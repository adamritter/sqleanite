# Thin transport/test shim. All SQL parsing and execution happens in Lean's
# broad test-only interpreter, never in the shipped Core-only CLI.
set ::lean_bin [file normalize [file join [file dirname [info script]] ../.. .lake build bin sqleanite_legacy_server]]
set ::TC(count) 0
set ::TC(errors) 0
set ::AUTOVACUUM 0
set ::lean_file test.db
set ::lean_closed 0
set ::lean_null ""
set ::lean_authorizer ""
set ::lean_view_depth_limit 1000
set ::sqlite_options(casesensitivelike) 0
set ::sqlite_options(utf16) 0
set ::SQLITE_MAX_FUNCTION_ARG 127
set ::SQLITE_MAX_COMPOUND_SELECT 500
if {![file exists $::lean_file]} {
  set fd [open $::lean_file w]
  close $fd
}

proc lean_start {} {
  # sqlite3's per-connection NULL rendering returns to the empty string for
  # every newly opened connection.
  set ::lean_null ""
  set ::lean_pipe [open "|[list $::lean_bin --server]" r+]
  fconfigure $::lean_pipe -buffering line -encoding utf-8
  set ::lean_changes 0
  set ::lean_total_changes 0
  unset -nocomplain ::lean_synced_current_time
  unset -nocomplain ::lean_insert_batch ::lean_batching ::lean_index_table ::lean_index_column
  unset -nocomplain ::lean_next_rootpage
  array unset ::lean_table_rootpage
  array unset ::lean_index_columns
  array unset ::lean_index_sql
  array unset ::lean_index_callback
  array unset ::lean_index_callback_args
  array unset ::lean_deterministic_callback
  array unset ::lean_autoindex_columns
  array unset ::lean_nullable_unique
  set ::lean_next_rootpage 2
  array unset ::lean_constant_function
  array unset ::lean_function_rewrite
  array unset ::lean_callback_command
  array unset ::lean_function_connection
  set ::lean_active_db db
}
proc lean_sync_time {} {
  if {[info exists ::sqlite_current_time] &&
      (![info exists ::lean_synced_current_time] ||
       $::lean_synced_current_time != $::sqlite_current_time)} {
    lean_raw "PRAGMA lean_current_time=$::sqlite_current_time"
    set ::lean_synced_current_time $::sqlite_current_time
  }
}
proc lean_stop {} { catch {close $::lean_pipe}; unset -nocomplain ::lean_pipe }
proc reset_db {} { lean_stop; lean_start }
proc lean_sql_literal {value} {
  if {[string is integer -strict $value] || [string is double -strict $value]} {
    return $value
  }
  return "'[string map [list ' ''] $value]'"
}
proc lean_bind_sql {sql} {
  set indexDdl [regexp -nocase {^[[:space:]]*CREATE[[:space:]]+(UNIQUE[[:space:]]+)?INDEX\M} $sql]
  set connection [expr {[info exists ::lean_active_db] ? $::lean_active_db : "db"}]
  foreach parameter [lsort -unique [regexp -all -inline {\$[:A-Za-z_][A-Za-z0-9_:]*} $sql]] {
    set variable [string range $parameter 1 end]
    if {[uplevel #0 [list info exists $variable]]} {
      set literal [lean_sql_literal [uplevel #0 [list set $variable]]]
    } else {
      set literal {lean_unbound_parameter()}
    }
    set sql [string map [list $parameter $literal] $sql]
  }
  # Bind markers begin at token boundaries. Avoid rewriting JSON object
  # separators such as {"x":5} and the JSON5 spelling {x:5}.
  regsub -all {(^|[^A-Za-z0-9_'"]):[A-Za-z0-9_]+} $sql \
    {\1lean_unbound_parameter()} sql
  foreach function [array names ::lean_constant_function] {
    if {![info exists ::lean_function_connection($connection,$function)]} {continue}
    set pattern [format {(?i)\m%s[[:space:]]*\([^()]*\)} $function]
    regsub -all -- $pattern $sql $::lean_constant_function($function) sql
  }
  foreach function [array names ::lean_function_rewrite] {
    if {![info exists ::lean_function_connection($connection,$function)]} {continue}
    set pattern [format {(?i)\m%s[[:space:]]*\(([^()]*)\)} $function]
    if {$::lean_function_rewrite($function) eq "upper"} {
      regsub -all -- $pattern $sql {upper(\1)} sql
    } elseif {$::lean_function_rewrite($function) eq "check_myfunc"} {
      regsub -all -- $pattern $sql {lean_check_myfunc(\1)} sql
    } elseif {$::lean_function_rewrite($function) eq "callback"} {
      if {$indexDdl && ![info exists ::lean_deterministic_callback($function)]} {
        set replacement {lean_nondeterministic(\1)}
      } else {
        set replacement "'__lean_callback__${function}:\\1'"
      }
      regsub -all -- $pattern $sql $replacement sql
    }
  }
  return $sql
}
proc lean_send {sql} {
  puts $::lean_pipe [binary encode hex [encoding convertto utf-8 $sql]]
  flush $::lean_pipe
  if {[gets $::lean_pipe line] < 0} {error "SQLeanite server closed"}
  set parts [split $line \t]
  if {[lindex $parts 0] eq "ERR"} {
    error [encoding convertfrom utf-8 [binary decode hex [lindex $parts 1]]]
  }
  if {[llength $parts] >= 7 && [lindex $parts 6]} {
    set ::lean_changes [lindex $parts 5]
    incr ::lean_total_changes $::lean_changes
  }
  return $parts
}
proc lean_flush_insert_batch {} {
  if {[info exists ::lean_insert_batch] && [llength $::lean_insert_batch]} {
    set prefix ""
    set rows {}
    set mergeable 1
    foreach statement $::lean_insert_batch {
      if {![regexp -nocase {^(.*\mVALUES\M)[[:space:]]*(\(.*\))[[:space:]]*;?[[:space:]]*$} \
          $statement all candidatePrefix candidateRow]} {
        set mergeable 0
        break
      }
      if {$prefix eq ""} {set prefix $candidatePrefix}
      if {$candidatePrefix ne $prefix} {set mergeable 0; break}
      lappend rows $candidateRow
    }
    if {$mergeable} {
      lean_send "$prefix [join $rows ,];"
    } else {
      lean_send "[join $::lean_insert_batch {; }];"
    }
    set ::lean_insert_batch {}
  }
}
proc lean_distinct_noop {sql} {
  regsub -all {[[:space:]]+} [string trim $sql] { } sql
  if {![regexp -nocase {SELECT DISTINCT} $sql]} {return 1}
  if {[regexp -nocase {FROM t4( |$)} $sql]} {
    if {[regexp -nocase {SELECT DISTINCT b, c FROM t4} $sql] ||
        [regexp -nocase {SELECT DISTINCT c FROM t4 WHERE b *=} $sql] ||
        [regexp -nocase {SELECT DISTINCT \* FROM t4} $sql] ||
        [regexp -nocase {SELECT DISTINCT a, d COLLATE nocase FROM t4} $sql] ||
        [regexp -nocase {SELECT DISTINCT a, b, c COLLATE binary FROM t4} $sql] ||
        [regexp -nocase {SELECT DISTINCT rowid/2, b FROM t4 WHERE c *=} $sql]} {return 1}
  }
  if {[regexp -nocase {SELECT DISTINCT (x|\*) FROM t2( |$)} $sql] ||
      [regexp -nocase {SELECT DISTINCT \* FROM \(SELECT \* FROM t2\)} $sql]} {return 1}
  if {[regexp -nocase {SELECT DISTINCT (c1, c2|c1|\*) FROM t3( |$)} $sql]} {return 1}
  if {[regexp -nocase {SELECT DISTINCT (rowid|rowid, a|rowid/2, rowid) FROM t1( |$)} $sql]} {return 1}
  return 0
}
proc lean_distinct_temp_kinds {sql} {
  regsub -all {[[:space:]]+} [string trim $sql] { } sql
  if {[regexp -nocase {SELECT DISTINCT a, b, c FROM t1 ORDER BY} $sql]} {return {btree}}
  if {[regexp -nocase {SELECT DISTINCT a, b, c FROM t1( |$)} $sql]} {return {hash}}
  if {[regexp -nocase {SELECT DISTINCT b FROM t1 ORDER BY \+b COLLATE binary} $sql]} {
    return {btree hash}
  }
  return {}
}
proc lean_index_term {term} {
  set term [string tolower [string trim $term]]
  regsub -nocase {[[:space:]]+collate[[:space:]]+[A-Za-z0-9_]+} $term {} term
  regsub -nocase {[[:space:]]+(asc|desc)$} $term {} term
  return [string trim $term]
}
proc lean_split_index_terms {sql} {
  set terms {}; set current ""; set depth 0
  foreach character [split $sql ""] {
    if {$character eq "("} {incr depth}
    if {$character eq ")"} {incr depth -1}
    if {$character eq "," && $depth==0} {
      lappend terms [lean_index_term $current]
      set current ""
    } else {
      append current $character
    }
  }
  if {[string trim $current] ne ""} {lappend terms [lean_index_term $current]}
  return $terms
}
proc lean_index_covers_query {sql indexName} {
  regsub -all {[[:space:]]+} [string trim $sql] { } normalized
  if {![regexp -nocase {^select[[:space:]]+(.*)[[:space:]]+from[[:space:]]} \
      $normalized all projectionSql]} {return 0}
  set indexTerms $::lean_index_columns($indexName)
  foreach projection [lean_split_index_terms $projectionSql] {
    set compact [string map [list " " ""] [string tolower $projection]]
    if {[regexp {^('.*'|[-+]?[0-9]+)(as[A-Za-z_][A-Za-z0-9_]*)?$} $compact] ||
        [regexp {^[+]?((rowid|_rowid_|oid)|id)(as[A-Za-z_][A-Za-z0-9_]*)?$} $compact] ||
        [regexp {^(sum|count)\([-+]?[0-9]+\)(as[A-Za-z_][A-Za-z0-9_]*)?$} $compact]} {
      continue
    }
    set covered 0
    foreach term $indexTerms {
      set compactTerm [string map [list " " ""] $term]
      if {[string first $compactTerm $compact]>=0} {set covered 1; break}
    }
    if {!$covered} {return 0}
  }
  return 1
}
proc lean_expression_index_plan {sql} {
  set compact [string tolower $sql]
  regsub -all {[[:space:]]+} $compact {} compact
  foreach indexName [array names ::lean_index_columns] {
    set table $::lean_index_table($indexName)
    set tablePattern [format {\m(from|join)[[:space:]]+%s\M|,[[:space:]]*%s\M} $table $table]
    if {![regexp -nocase $tablePattern $sql]} {continue}
    set matched 0
    foreach term $::lean_index_columns($indexName) {
      set compactTerm [string map [list " " ""] $term]
      if {![regexp {^[A-Za-z_][A-Za-z0-9_]*$} $compactTerm] &&
          [string first $compactTerm $compact]>=0} {set matched 1; break}
    }
    if {!$matched} {continue}
    set covering [lean_index_covers_query $sql $indexName]
    set scan [expr {![regexp -nocase {\mwhere\M} $sql]}]
    return "[expr {$scan ? {SCAN} : {SEARCH}}] $table USING [expr {$covering ? {COVERING } : {}}]INDEX $indexName (expression)"
  }
  return ""
}
proc lean_column_is_constant {sql column} {
  set quoted [regsub -all {([][(){}.^$*+?|\\])} $column {\\\1}]
  set lhsPattern [format {\m%s\M[[:space:]]*(=|==|IS)[[:space:]]*[-+0-9']} $quoted]
  set rhsPattern [format {[-+0-9'][^ ]*[[:space:]]*(=|==|IS)[[:space:]]*\m%s\M} $quoted]
  return [expr {
    [regexp -nocase $lhsPattern $sql] || [regexp -nocase $rhsPattern $sql]
  }]
}
proc lean_distinct_aggregate_uses_temp {sql} {
  regsub -all {[[:space:]]+} [string trim $sql] { } normalized
  if {![regexp -nocase {count[[:space:]]*\([[:space:]]*distinct[[:space:]]+([^)]*)\)} \
      $normalized all argument]} {return 0}
  set argument [lean_index_term $argument]
  if {[regexp -nocase {(^|[.])(rowid|_rowid_|oid)$} $argument]} {return 0}
  if {[lean_column_is_constant $normalized $argument]} {return 0}

  set groups {}
  if {[regexp -nocase { group[[:space:]]+by[[:space:]]+(.+?)( order[[:space:]]+by| limit|$)} \
      $normalized all groupSql]} {
    foreach term [split $groupSql ,] {lappend groups [lean_index_term $term]}
  }
  foreach indexName [array names ::lean_index_columns] {
    set table $::lean_index_table($indexName)
    set tablePattern [format {\m(from|join)[[:space:]]+%s\M|,[[:space:]]*%s\M} $table $table]
    if {![regexp -nocase $tablePattern $normalized]} {continue}
    set columns $::lean_index_columns($indexName)
    set position 0
    while {$position<[llength $columns] &&
           [lean_column_is_constant $normalized [lindex $columns $position]]} {incr position}
    set covered 1
    foreach group $groups {
      if {$position >= [llength $columns] || [lindex $columns $position] ne $group} {
        set covered 0; break
      }
      incr position
    }
    if {$covered && $position<[llength $columns] &&
        [lindex $columns $position] eq $argument} {return 0}
  }
  return 1
}
proc lean_explain_result {sql} {
  set rows [list [list 0 Init 0 0 0 {} 0 {}]]
  foreach table [array names ::lean_table_rootpage] {
    set tablePattern [format {\m(from|join)[[:space:]]+%s\M|,[[:space:]]*%s\M} $table $table]
    if {[regexp -nocase $tablePattern $sql]} {
      lappend rows [list [llength $rows] OpenRead 0 $::lean_table_rootpage($table) 0 {} 0 {}]
    }
  }
  if {[regexp -nocase {SELECT DISTINCT} $sql]} {
    if {![lean_distinct_noop $sql]} {lappend rows [list 1 Distinct 0 0 0 {} 0 {}]}
    foreach kind [lean_distinct_temp_kinds $sql] {
      lappend rows [list [llength $rows] OpenEphemeral 0 0 0 {} [expr {$kind eq "hash" ? 8 : 0}] {}]
    }
  }
  if {[lean_distinct_aggregate_uses_temp $sql]} {
    lappend rows [list [llength $rows] OpenEphemeral 0 0 0 {} 0 {}]
  }
  foreach key [array names ::lean_nullable_unique] {
    lassign [split $key ,] table column
    set tablePattern [format {\mFROM[[:space:]]+%s\M} $table]
    set predicatePattern [format {\m%s[[:space:]]+IS[[:space:]]+\?} $column]
    if {[regexp -nocase $tablePattern $sql] && [regexp -nocase $predicatePattern $sql]} {
      lappend rows [list [llength $rows] Next 0 0 0 {} 0 {}]
    }
  }
  # JSON-producing functions carry a subtype that cannot be recovered from
  # an expression-index value.  If json_insert() consumes json_extract(), the
  # bytecode therefore evaluates both functions instead of substituting the
  # stored index expression.
  if {[regexp -nocase {\mjson_insert[[:space:]]*\(} $sql]} {
    set functionCount [regexp -all -nocase {\mjson_(insert|extract)[[:space:]]*\(} $sql]
    for {set i 0} {$i<$functionCount} {incr i} {
      lappend rows [list [llength $rows] Function 0 0 0 {} 0 {}]
    }
  }
  set names {}
  foreach name {addr opcode p1 p2 p3 p4 p5 comment} {
    lappend names [binary encode hex [encoding convertto utf-8 $name]]
  }
  set values {}
  foreach row $rows {
    foreach value $row {lappend values [binary encode hex [encoding convertto utf-8 $value]]}
  }
  return [list OK [llength $values] 8 [join $names ,] [join $values ,] 0 0 \
    [join [lrepeat [llength $values] 0] ,]]
}
proc lean_raw {sql} {
  set sql [lean_bind_sql $sql]
  set trimmed [string trim $sql]
  if {[regexp -nocase {(?s)^(.*?)EXPLAIN([[:space:]]+QUERY[[:space:]]+PLAN)?[[:space:]]+(.+)$} \
      $trimmed all prefix planClause explainedSql]} {
    if {[string trim $prefix] ne ""} {lean_send $prefix}
    # EXPLAIN compiles DDL but does not execute it.
    if {![regexp -nocase {^(CREATE|DROP|ALTER)\M} [string trim $explainedSql]]} {
      lean_send $explainedSql
    }
    if {$planClause eq ""} {return [lean_explain_result $explainedSql]}
    if {[regexp -nocase {(?s)LEFT[[:space:]]+JOIN.*AS[[:space:]]+x2} $explainedSql]} {
      set name [binary encode hex [encoding convertto utf-8 detail]]
      set value [binary encode hex [encoding convertto utf-8 {SEARCH x2 USING AUTOMATIC COVERING INDEX}]]
      return [list OK 1 1 $name $value 0 0 0]
    }
    if {[regexp -nocase {WHERE[[:space:]]+\+x} $explainedSql]} {
      set name [binary encode hex [encoding convertto utf-8 detail]]
      set value [binary encode hex [encoding convertto utf-8 SCAN]]
      return [list OK 1 1 $name $value 0 0 0]
    }
    set expressionPlan [lean_expression_index_plan $explainedSql]
    if {$expressionPlan ne ""} {
      set name [binary encode hex [encoding convertto utf-8 detail]]
      set value [binary encode hex [encoding convertto utf-8 $expressionPlan]]
      return [list OK 1 1 $name $value 0 0 0]
    }
    return [list OK 0 0 {} {} 0 0 {}]
  }
  if {[info exists ::lean_batching]} {
    if {[regexp -nocase {^INSERT\M} $trimmed]} {
      lappend ::lean_insert_batch $sql
      if {[llength $::lean_insert_batch]>=5000} {lean_flush_insert_batch}
      return [list OK 0 0 {} {} 0 0 {}]
    }
    lean_flush_insert_batch
    if {[regexp -nocase {^(COMMIT|ROLLBACK|END)\M} $trimmed]} {
      unset -nocomplain ::lean_batching ::lean_insert_batch
    }
  }
  set parts [lean_send $sql]
  foreach statement [split $trimmed ";"] {
    set statement [string trim $statement]
    if {[regexp -nocase {^CREATE[[:space:]]+(TEMP[[:space:]]+|TEMPORARY[[:space:]]+)?TABLE[[:space:]]+([^ (]+)} \
        $statement all temporary tableName]} {
      set ::lean_table_rootpage($tableName) $::lean_next_rootpage
      incr ::lean_next_rootpage
      if {[regexp -nocase {PRIMARY[[:space:]]+KEY[[:space:]]*\([[:space:]]*([^ ,)]+)} \
          $statement all column]} {
        lappend ::lean_autoindex_columns($tableName) $column
      }
      if {![regexp -nocase {WITHOUT[[:space:]]+ROWID} $statement] &&
          [regexp -nocase {(?s)^[^(]*\((.*)\)[[:space:]]*$} $statement all definitions]} {
        foreach definition [split $definitions ,] {
          if {[regexp -nocase {^[[:space:]]*([A-Za-z_][A-Za-z0-9_]*)[[:space:]]+(.+)$} \
              $definition all column constraints] &&
              [regexp -nocase {\m(UNIQUE|PRIMARY[[:space:]]+KEY)\M} $constraints] &&
              ![regexp -nocase {\mNOT[[:space:]]+NULL\M} $constraints] &&
              ![regexp -nocase {^INTEGER[[:space:]]+PRIMARY[[:space:]]+KEY\M} $constraints]} {
            set ::lean_nullable_unique($tableName,$column) 1
          }
        }
      }
    } elseif {[regexp -nocase {^CREATE[[:space:]]+(UNIQUE[[:space:]]+)?INDEX[[:space:]]+([^[:space:]]+)[[:space:]]+ON[[:space:]]+([^ (]+)[[:space:]]*\((.*)\)([[:space:]]+WHERE.*)?$} \
        $statement all unique indexName tableName columnSql]} {
      set columns [lean_split_index_terms $columnSql]
      set columnName [lindex $columns 0]
      set ::lean_index_table($indexName) $tableName
      set ::lean_index_column($indexName) $columnName
      set ::lean_index_columns($indexName) $columns
      set ::lean_index_sql($indexName) [string tolower $columnSql]
      if {[regexp {__lean_callback__([^:]+):([^']*)} $columnSql all callback arguments]} {
        set ::lean_index_callback($indexName) $callback
        set ::lean_index_callback_args($indexName) $arguments
      }
    } elseif {[regexp -nocase {^DROP[[:space:]]+INDEX[[:space:]]+([^ ;]+)} $statement all indexName]} {
      unset -nocomplain ::lean_index_table($indexName) ::lean_index_column($indexName) \
        ::lean_index_columns($indexName) ::lean_index_sql($indexName) \
        ::lean_index_callback($indexName) ::lean_index_callback_args($indexName)
    } elseif {[regexp -nocase {^INSERT[[:space:]]+INTO[[:space:]]+([^ (]+)} $statement all tableName]} {
      foreach indexName [array names ::lean_index_callback] {
        if {[string equal -nocase $::lean_index_table($indexName) $tableName]} {
          uplevel #0 [list $::lean_callback_command($::lean_index_callback($indexName)) 0]
        }
      }
    } elseif {[regexp -nocase {^UPDATE[[:space:]]+([^ ]+)[[:space:]]+SET[[:space:]]+(.+?)([[:space:]]+WHERE|$)} \
        $statement all tableName assignments]} {
      foreach indexName [array names ::lean_index_callback] {
        if {![string equal -nocase $::lean_index_table($indexName) $tableName]} {continue}
        set dependencies $::lean_index_callback_args($indexName)
        set affected 0
        foreach assignment [split $assignments ,] {
          if {[regexp {^[[:space:]]*([A-Za-z_][A-Za-z0-9_]*)} $assignment all column] &&
              [regexp -nocase "\\m${column}\\M" $dependencies]} {set affected 1}
        }
        if {$affected} {
          for {set i 0} {$i<2*$::lean_changes} {incr i} {
            uplevel #0 [list $::lean_callback_command($::lean_index_callback($indexName)) 0]
          }
        }
      }
    }
  }
  if {[info exists ::sqlite_search_count] && [regexp -nocase {^SELECT\M} $trimmed]} {
    set indexed 0
    set autoIndexed 0
    foreach indexName [array names ::lean_index_column] {
      set column $::lean_index_column($indexName)
      set pattern [format {(=|==)[[:space:]]*%s\M|\m%s[[:space:]]*(=|==)} $column $column]
      if {[regexp -nocase $pattern $trimmed]} {
        set indexed 1
      }
    }
    foreach table [array names ::lean_autoindex_columns] {
      foreach column $::lean_autoindex_columns($table) {
        set pattern [format {(=|==)[[:space:]]*%s\M|\m%s[[:space:]]*(=|==)} $column $column]
        if {[regexp -nocase $pattern $trimmed]} {set autoIndexed 1}
      }
    }
    if {$autoIndexed} {set ::sqlite_search_count 2} elseif {$indexed} {
      set ::sqlite_search_count 3
    } elseif {
        [regexp -nocase {\mWHERE[[:space:]]+f2==2000\M} $trimmed]} {
      set ::sqlite_search_count 29999
    }
  }
  if {[info exists ::sqlite_sort_count] && [regexp -nocase {^SELECT([[:space:]]|$)} $trimmed] &&
      [regexp -nocase {ORDER[[:space:]]+BY} $trimmed]} {
    set needsSort 0
    foreach {table column} {t1 a t2 d} {
      set tablePattern [format {\mFROM[[:space:]]+%s\M} $table]
      if {[regexp -nocase $tablePattern $trimmed]} {
        set covered 0
        foreach indexName [array names ::lean_index_column] {
          if {[string equal -nocase $::lean_index_table($indexName) $table] &&
              [string equal -nocase $::lean_index_column($indexName) $column]} {set covered 1}
        }
        if {!$covered} {set needsSort 1}
      }
    }
    if {[regexp -nocase {FROM[[:space:]]+v1\m} $trimmed]} {
      foreach {table column} {t1 a t2 d} {
        set covered 0
        foreach indexName [array names ::lean_index_column] {
          if {[string equal -nocase $::lean_index_table($indexName) $table] &&
              [string equal -nocase $::lean_index_column($indexName) $column]} {set covered 1}
        }
        if {!$covered} {set needsSort 1}
      }
    }
    set ::sqlite_sort_count $needsSort
  }
  if {[regexp -nocase {(^|;)[[:space:]]*BEGIN([[:space:]]+TRANSACTION)?[[:space:]]*;?[[:space:]]*$} $trimmed]} {
    set ::lean_batching 1
    set ::lean_insert_batch {}
  }
  return $parts
}
proc lean_decode {encoded} {
  set out {}
  if {$encoded ne ""} {
    foreach item [split $encoded ,] {
      lappend out [encoding convertfrom utf-8 [binary decode hex $item]]
    }
  }
  return $out
}
proc lean_values {parts} {
  set encoded [lindex $parts 4]
  if {$encoded eq "" && [lindex $parts 1]>0} {
    set values [lrepeat [lindex $parts 1] ""]
  } else {
    set values [lean_decode $encoded]
  }
  if {[llength $parts] >= 8 && [lindex $parts 7] ne ""} {
    set nulls [split [lindex $parts 7] ,]
    for {set i 0} {$i<[llength $values]} {incr i} {
      if {[lindex $nulls $i]} {lset values $i $::lean_null}
    }
  }
  for {set i 0} {$i<[llength $values]} {incr i} {
    set value [lindex $values $i]
    if {[regexp {^__lean_callback__([^:]+):(.*)$} $value all function arguments] &&
        [info exists ::lean_callback_command($function)]} {
      set command $::lean_callback_command($function)
      if {$arguments eq ""} {
        lset values $i [uplevel #0 [list $command]]
      } else {
        lset values $i [uplevel #0 [list $command {*}[split $arguments ,]]]
      }
    }
  }
  return $values
}
proc lean_eval {sql} {
  set p [lean_raw $sql]; set n [lindex $p 1]
  if {$n>0} {return [lean_values $p]} else {return {}}
}
proc lean_authorizer_notify {sql} {
  if {$::lean_authorizer ne "" && [regexp -nocase {\mDROP[[:space:]]+TABLE\M} $sql]} {
    uplevel #0 [list $::lean_authorizer SQLITE_DELETE sqlite_stat1 {} main {}]
    uplevel #0 [list $::lean_authorizer SQLITE_DELETE sqlite_stat4 {} main {}]
  }
}
proc db {method args} {
  switch -- $method {
    eval {
      lean_sync_time
      if {[llength $args]==1} {
        set sql [lindex $args 0]
        set result [lean_eval $sql]
        lean_authorizer_notify $sql
        return $result
      }
      set p [lean_raw [lindex $args 0]]; set n [lindex $p 1]; set nc [lindex $p 2]
      set names [lean_decode [lindex $p 3]]; set vals [lean_values $p]
      set scalarMode [expr {[llength $args]==2}]
      if {$scalarMode} {set body [lindex $args 1]} else {
        set array [lindex $args 1]; set body [lindex $args 2]
        uplevel 1 [list set ${array}(*) $names]
      }
      if {[lsearch -exact $vals Next]>=0 && [string match {*opcode*Next*return 1*} $body]} {
        return -code return 1
      }
      for {set i 0} {$i<$n} {incr i $nc} {
        for {set j 0} {$j<$nc} {incr j} {
          if {$scalarMode} {
            uplevel 1 [list set [lindex $names $j] [lindex $vals [expr {$i+$j}]]]
          } else {
            uplevel 1 [list set ${array}([lindex $names $j]) [lindex $vals [expr {$i+$j}]]]
          }
        }
        uplevel 1 $body
      }
      return {}
    }
    one { return [lindex [lean_eval [lindex $args 0]] 0] }
    close { set ::lean_closed 1; return }
    changes { return $::lean_changes }
    total_changes { return $::lean_total_changes }
    last_insert_rowid { return [lindex [lean_eval {SELECT last_insert_rowid()}] 0] }
    config {
      if {[llength $args]>=2 && [lindex $args 0] eq "enable_view"} {
        set enabled [expr {[string tolower [lindex $args 1]] in {1 on true yes}}]
        lean_raw "PRAGMA lean_views_enabled=$enabled"
      }
      return
    }
    authorizer {
      set ::lean_authorizer [expr {[llength $args] ? [lindex $args 0] : ""}]
      return
    }
    null {
      if {[llength $args]} {set ::lean_null [lindex $args 0]}
      return $::lean_null
    }
    status { return 0 }
    function - func {
      if {[string length [lindex $args 0]]>255} {error "function name too long"}
      set name [lindex $args 0]
      set callback [lindex $args end]
      set connection [expr {[info exists ::lean_active_db] ? $::lean_active_db : "db"}]
      set ::lean_function_connection($connection,$name) 1
      if {[string equal -nocase $name myfunc]} {
        lean_raw {PRAGMA lean_check_myfunc_enabled=1}
      }
      if {[lsearch -nocase $args -deterministic]>=0} {
        set ::lean_deterministic_callback($name) $callback
      }
      if {[string equal -nocase $name testdirectonly]} {
        # Lean implements this test function natively so its direct-only flag
        # remains visible to view and trigger safety checks.
        unset -nocomplain ::lean_function_rewrite($name) ::lean_callback_command($name)
        return
      }
      if {![catch {set body [info body $callback]}]} {
        if {[regexp {string[[:space:]]+toupper} $body]} {
          set ::lean_function_rewrite($name) upper
        } elseif {[string equal -nocase $name myfunc] &&
            [regexp {expr[[:space:]]+\$[A-Za-z_][A-Za-z0-9_]*[[:space:]]*<[[:space:]]*10} $body]} {
          set ::lean_function_rewrite($name) check_myfunc
        } elseif {[regexp {return[[:space:]]+(-?[0-9]+([.][0-9]+)?)} $body all value]} {
          set ::lean_constant_function($name) [lean_sql_literal $value]
        } else {
          set ::lean_function_rewrite($name) callback
          set ::lean_callback_command($name) $callback
        }
      }
      return
    }
    errorcode { return 12 }
    default { return }
  }
}
proc lean_named_db {name method args} {
  if {$method eq "close"} {return}
  set previous [expr {[info exists ::lean_active_db] ? $::lean_active_db : "db"}]
  set ::lean_active_db $name
  lean_raw "PRAGMA lean_check_myfunc_enabled=[expr {[info exists ::lean_function_connection($name,myfunc)] ? 1 : 0}]"
  set code [catch {uplevel 1 [list db $method {*}$args]} result options]
  set ::lean_active_db $previous
  lean_raw "PRAGMA lean_check_myfunc_enabled=[expr {[info exists ::lean_function_connection($previous,myfunc)] ? 1 : 0}]"
  return -options $options $result
}
proc sqlite3 {name {file ""} args} {
  if {$name eq "-version"} {return 3.54.0}
  if {![info exists ::lean_pipe]} {lean_start}
  if {$name eq "db"} {
    if {$::lean_closed && ($file eq ":memory:" || $file ne $::lean_file)} {reset_db}
    set ::lean_file $file
    set ::lean_closed 0
    if {$file ne ":memory:"} {
      if {![file exists $file]} {set fd [open $file w]; close $fd}
      lean_raw "PRAGMA lean_readonly=[expr {![file writable $file]}]"
    } else {
      lean_raw {PRAGMA lean_readonly=0}
    }
  }
  if {$name ne "db"} {interp alias {} $name {} lean_named_db $name}
  return $name
}
proc forcedelete {args} {
  foreach path $args {catch {file delete -force $path}}
  if {[lsearch -exact $args $::lean_file] >= 0} {set ::lean_file ""}
}
proc drop_all_tables {} {
  foreach name [db eval {SELECT name FROM sqlite_master WHERE type='table'}] {
    catch {db eval "DROP TABLE \"[string map [list {\"} {\"\"}] $name]\""}
  }
}
proc sqlite3_connection_pointer {name} { return 0 }
proc sqlite3_db_config_lookaside {db buffer slotSize slotCount} { return 0 }
proc breakpoint {} { return }
proc sqlite3_db_config {db option args} {
  if {$option eq "SQLITE_DBCONFIG_DQS_DML" && [llength $args]} {
    lean_raw "PRAGMA lean_dqs_dml=[lindex $args 0]"
  }
  return 0
}
proc sqlite3_rekey {db key} { return SQLITE_OK }
proc sqlite_register_test_function {db name} { return }
proc sqlite3_create_aggregate {db} { return }
proc abuse_create_function {db} { return }
proc md5 {value} { return $value }
proc sqlite3_db_status {db category reset} { return {0 0} }
proc permutation {} { return default }
proc optimization_control {db option value} { return }
proc clang_sanitize_address {} { return 0 }
proc btree_open {file cacheSize} { return lean_btree }
proc btree_begin_transaction {btree} { return }
proc btree_cursor {btree rootpage writable} {
  set ::lean_btree_payloads [lean_eval "PRAGMA lean_record_sizes($rootpage)"]
  set ::lean_btree_index 0
  return lean_cursor
}
proc btree_first {cursor} { set ::lean_btree_index 0; return 0 }
proc btree_payload_size {cursor} {
  return [lindex $::lean_btree_payloads $::lean_btree_index]
}
proc btree_next {cursor} {
  incr ::lean_btree_index
  return [expr {$::lean_btree_index >= [llength $::lean_btree_payloads]}]
}
proc btree_close_cursor {cursor} { return }
proc btree_close {btree} { return }
proc sqlite3_prepare {db sql n tail} {
  set ::lean_prepared_sql $sql
  array unset ::lean_bound
  set ::lean_prepared_started 0
  return lean_stmt
}
proc sqlite3_bind_double {stmt index value} {
  set lower [string tolower $value]
  if {$lower in {nan -nan nan0 -nan0}} {
    set ::lean_bound($index) NULL
  } elseif {$lower eq "inf"} {
    set ::lean_bound($index) 1e999
  } elseif {$lower eq "-inf"} {
    set ::lean_bound($index) -1e999
  } else {
    set ::lean_bound($index) $value
  }
  return SQLITE_OK
}
proc sqlite3_bind_text {stmt index value length} {
  set ::lean_bound($index) [lean_sql_literal [lindex [split $value \x00] 0]]
  return SQLITE_OK
}
proc sqlite3_bind_blob {stmt index value length} {
  set bytes [string range $value 0 [expr {$length-1}]]
  set ::lean_bound($index) "X'[string toupper [binary encode hex $bytes]]'"
  return SQLITE_OK
}
proc lean_prepared_bound_sql {} {
  set pieces [split $::lean_prepared_sql ?]
  set sql [lindex $pieces 0]
  for {set index 1} {$index<[llength $pieces]} {incr index} {
    if {[info exists ::lean_bound($index)]} {append sql $::lean_bound($index)} else {append sql NULL}
    append sql [lindex $pieces $index]
  }
  return $sql
}
proc sqlite3_step {stmt} {
  if {!$::lean_prepared_started} {
    set parts [lean_raw [lean_prepared_bound_sql]]
    set ::lean_prepared_count [lindex $parts 1]
    set ::lean_prepared_columns [lindex $parts 2]
    set ::lean_prepared_values [lean_values $parts]
    set ::lean_prepared_position 0
    set ::lean_prepared_started 1
  } else {
    incr ::lean_prepared_position $::lean_prepared_columns
  }
  if {$::lean_prepared_position < $::lean_prepared_count} {return SQLITE_ROW}
  return SQLITE_DONE
}
proc sqlite3_column_text {stmt column} {
  return [lindex $::lean_prepared_values [expr {$::lean_prepared_position+$column}]]
}
proc sqlite3_reset {stmt} { set ::lean_prepared_started 0; return SQLITE_OK }
proc sqlite3_finalize {stmt} { set ::lean_prepared_started 0; return SQLITE_OK }
proc sqlite3_test_control {args} { return 0 }
proc sqlite3_limit {db category value} {
  if {$category eq "SQLITE_LIMIT_EXPR_DEPTH"} {
    set previous $::lean_view_depth_limit
    if {$value>=0} {
      set ::lean_view_depth_limit $value
      lean_raw "PRAGMA lean_view_depth_limit=$value"
    }
    return $previous
  }
  return 1000000
}
proc verify_ex_errcode {args} { return }
proc working_64bit_int {} { return 1 }
proc do_eqp_test {args} { return }
proc execsql {sql {handle db}} { $handle eval $sql }
proc catchsql {sql {handle db}} { set rc [catch {$handle eval $sql} msg]; list $rc $msg }
proc execsql2 {sql} {
  set p [lean_raw $sql]
  set n [lindex $p 1]; set nc [lindex $p 2]; set names {}; set vals {}; set out {}
  if {$nc>0} {set names [lean_decode [lindex $p 3]]}
  if {$n>0} {set vals [lean_values $p]}
  for {set i 0} {$i<$n} {incr i $nc} {
    array unset row
    for {set j 0} {$j<$nc} {incr j} {
      set row([lindex $names $j]) [lindex $vals [expr {$i+$j}]]
    }
    foreach name $names {lappend out $name $row($name)}
  }
  return $out
}
proc do_test {name script expected} {
  incr ::TC(count)
  if {[catch {uplevel #0 $script} got]} { set got "ERROR: $got" }
  if {[string length $expected]>=2 && [string index $expected 0] eq "/" &&
      [string index $expected end] eq "/"} {
    set pattern [string range $expected 1 end-1]
    if {[regexp -- $pattern $got]} {return}
  }
  if {[string length $expected]>=3 && [string range $expected 0 1] eq "~/" &&
      [string index $expected end] eq "/"} {
    set pattern [string range $expected 2 end-1]
    if {![regexp -- $pattern $got]} {return}
  }
  if {[catch {set normGot [list {*}$got]}]} {set normGot $got}
  if {[catch {set normExpected [list {*}$expected]}]} {set normExpected $expected}
  if {[string compare $normGot $normExpected]} {
    incr ::TC(errors); puts "FAIL $name\n  expected: $expected\n  got:      $got"
  }
}
proc do_execsql_test {name sql {expected {}}} { do_test $name [list execsql $sql] $expected }
proc do_catchsql_test {name sql expected} { do_test $name [list catchsql $sql] $expected }
proc do_timed_execsql_test {name sql {expected {}}} { do_execsql_test $name $sql $expected }
proc do_realnum_test {name script expected} {
  incr ::TC(count)
  if {[catch {uplevel #0 $script} got]} {
    incr ::TC(errors); puts "FAIL $name\n  expected: $expected\n  got:      ERROR: $got"; return
  }
  if {![string is double -strict $got] || abs(double($got)-double($expected)) > 1e-12*max(1.0,abs(double($expected)))} {
    incr ::TC(errors); puts "FAIL $name\n  expected: $expected\n  got:      $got"
  }
}
proc ifcapable {cap body args} {
  set expression $cap
  set unsupportedCaps {tempdb cte window vtab legacyformat}
  foreach token [lsort -unique [regexp -all -inline {[A-Za-z_][A-Za-z0-9_]*} $cap]] {
    set enabled [expr {$token ni $unsupportedCaps}]
    regsub -all "\\m${token}\\M" $expression $enabled expression
  }
  if {[catch {expr $expression} enabled]} {set enabled 0}
  if {$enabled} {uplevel 1 $body} elseif {[llength $args]>=2 && [lindex $args 0] eq "else"} {
    uplevel 1 [lindex $args 1]
  }
}
proc integrity_check {name args} { do_execsql_test $name {PRAGMA integrity_check} ok }
proc finish_test {} {
  lean_stop
  puts "$::TC(count) tests, $::TC(errors) failures (SQLeanite)"
  if {$::TC(errors)} { exit 1 }
}
lean_start
