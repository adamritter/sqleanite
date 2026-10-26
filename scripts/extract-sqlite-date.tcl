set path [lindex $argv 0]
set f [open $path r]
set input [read $f]
close $f
interp create -safe dateextract
proc capture {name sql} {
  puts "case\t[binary encode hex [encoding convertto utf-8 $name]]\t[binary encode hex [encoding convertto utf-8 $sql]]"
}
interp alias dateextract capture {} capture
interp limit dateextract command -value 1000000
interp eval dateextract {
  proc repeat {n text} {string repeat $text $n}
  proc datetest {name expression expected} {capture date-$name "SELECT coalesce($expression,'NULL');"}
  proc do_execsql_test {name sql expected} {capture $name $sql}
}
set command ""
set start 1
set line 0
foreach part [split $input \n] {
  incr line
  if {$command eq ""} {set start $line}
  append command $part \n
  if {![info complete $command]} {continue}
  set trim [string trimleft $command]
  if {[regexp {^(datetest|do_execsql_test)\s} $trim]} {
    if {[catch {interp eval dateextract $command} error]} {
      puts "failed\t$start\t[binary encode hex [encoding convertto utf-8 $error]]"
    }
  } elseif {$trim ne "" && ![string match #* $trim]} {
    puts "not-extracted\t$start\t[binary encode hex [encoding convertto utf-8 [lindex [split $trim \n] 0]]]"
  }
  set command ""
}
if {[string trim $command] ne ""} {error "incomplete trailing Tcl command"}
