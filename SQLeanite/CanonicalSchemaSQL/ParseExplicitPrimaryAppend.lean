import SQLeanite.CanonicalSchemaSQL.StripPrefixNotNullEnd

namespace SQLeanite.CanonicalSchemaSQL

theorem parseExplicitPrimary_append (policy : Core.NotNullConflict) (rest : List Char) :
    parseExplicitPrimary (explicitPrimaryChars policy ++ rest) = some (policy, rest) := by
  cases policy <;> simp [explicitPrimaryChars, parseExplicitPrimary, stripPrefix]

theorem parseNullPolicy_append (policy : Core.NotNullConflict) (rest : List Char)
    (separator : endsColumn rest = true) :
    parseNullPolicy (notNullConflictChars policy ++ rest) = (policy, rest) := by
  cases policy
  · cases rest with
    | nil => rfl
    | cons character tail =>
        have notSpace : character ≠ ' ' := by
          intro equal
          subst character
          simp [endsColumn] at separator
        simp [notNullConflictChars, parseNullPolicy, stripPrefix, Ne.symm notSpace]
  · simp [notNullConflictChars, parseNullPolicy, stripPrefix]
  · simp [notNullConflictChars, parseNullPolicy, stripPrefix]

theorem parseAutoBody_append (column : Core.Column) (rest : List Char)
    (automatic : column.autoIncrement = true)
    (consistent : column.integerPrimaryKey = true → column.notNull = true)
    (exclusive : column.integerPrimaryKey = true → column.textPrimaryKey = false)
    (noDefault : column.defaultValue = none)
    (separator : endsColumn rest = true) :
    parseAutoBody (autoBodyChars column ++ rest) = some (column, rest) := by
  have restored := fromAuto_inverse column automatic consistent exclusive noDefault
  simp only [autoBodyChars, quoteChars, List.cons_append, List.append_assoc, List.nil_append, parseAutoBody]
  rw [takeIdent_escape _ _ (by simp)]
  simp only [Option.bind_eq_bind, Option.bind, String.ofList_toList]
  rw [stripPrefix_append]
  simp only [Option.bind_eq_bind, Option.bind]
  rw [parseExplicitPrimary_append]
  simp only [Option.bind_eq_bind, Option.bind]
  rw [stripPrefix_append]
  simp only [Option.bind_eq_bind, Option.bind]
  cases hn : column.integerPrimaryNotNull
  · have plain : column.notNullConflict = .abort := by
      by_cases same : column.notNullConflict = .abort
      · exact same
      · have declared := (column.notNullConflictOnly same).2 (column.autoIncrementOnly automatic)
        simp_all
    simp only [hn, Bool.false_eq_true, ↓reduceIte]
    simp [hn, plain] at restored
    simp [stripPrefix, restored]
  · simp only [hn, ↓reduceIte, List.append_assoc]
    rw [stripPrefix_append]
    dsimp only
    rw [parseNullPolicy_append _ _ separator]
    simp [hn] at restored
    simp [restored]

theorem parseKeyColumn_any_append (column : Core.Column) (rest : List Char)
    (consistent : column.integerPrimaryKey = true → column.notNull = true)
    (exclusive : column.integerPrimaryKey = true → column.textPrimaryKey = false)
    (noDefault : column.defaultValue = none)
    (separator : endsColumn rest = true) :
    parseKeyColumn (keyColumnChars column ++ rest) = some (column, rest) := by
  cases automatic : column.autoIncrement
  · have noTag : stripPrefix "/*sqleanite-autoinc*/".toList
        (typedKeyColumnChars column ++ rest) = none := by
      cases declared : column.indexedType with
      | none =>
          simp only [typedKeyColumnChars, declared, legacyKeyColumnChars]
          split <;> simp [plainColumnChars, baseColumnChars, quoteChars, stripPrefix]
      | some typ => simp [typedKeyColumnChars, declared, stripPrefix]
    simp only [keyColumnChars, automatic, Bool.false_eq_true, ↓reduceIte, parseKeyColumn]
    rw [noTag]
    exact parseTypedKeyColumn_any_append column rest consistent exclusive noDefault automatic separator
  · simp only [keyColumnChars, automatic, ↓reduceIte, List.append_assoc, parseKeyColumn]
    rw [stripPrefix_append]
    exact parseAutoBody_append column rest automatic consistent exclusive noDefault separator

theorem keyColumnChars_noDefaultTag (column : Core.Column) (rest : List Char) :
    stripPrefix "/*sqleanite-default ".toList (keyColumnChars column ++ rest) = none := by
  cases automatic : column.autoIncrement
  · simpa [keyColumnChars, automatic] using typedKeyColumnChars_noDefaultTag column rest
  · simp [keyColumnChars, automatic, stripPrefix]

theorem takeQuotedNat_quote (number : Nat) (rest : List Char)
    (boundary : rest.head? ≠ some '"') :
    takeQuotedNat (quoteChars (toString number) ++ rest) = some (number, rest) := by
  unfold takeQuotedNat quoteChars
  simp only [List.cons_append, List.append_assoc, List.nil_append]
  rw [takeIdent_escape _ _ boundary]
  simp only [Option.bind_eq_bind, Option.bind, String.ofList_toList]
  change ((Nat.repr number).toNat?.bind (fun value => some (value, rest))) = _
  rw [Nat.toNat?_repr]
  rfl

theorem parseColumn_any_append (column : Core.Column) (rest : List Char)
    (consistent : column.integerPrimaryKey = true → column.notNull = true)
    (exclusive : column.integerPrimaryKey = true → column.textPrimaryKey = false)
    (separator : endsColumn rest = true) :
    parseColumn (columnChars column ++ rest) = some (column, rest) := by
  cases hd : column.defaultValue with
  | none =>
      have parsed := parseKeyColumn_any_append column rest consistent exclusive hd separator
      simp only [columnChars, hd, parseColumn]
      rw [keyColumnChars_noDefaultTag]
      exact parsed
  | some spec =>
      let base : Core.Column := { column with defaultValue := none }
      have parsed := parseKeyColumn_any_append base [] consistent exclusive rfl (by rfl)
      have restored : { base with defaultValue := some spec } = column := by cases column; simp_all [base]
      simp only [columnChars, hd, List.append_assoc, parseColumn, defaultHeader]
      rw [stripPrefix_append]
      simp only [Option.bind_eq_bind, Option.bind]
      rw [takeQuotedNat_quote _ _ (by simp)]
      simp only [Option.bind_eq_bind, Option.bind]
      rw [stripPrefix_append]
      simp only [Option.bind_eq_bind, Option.bind]
      rw [takeQuotedNat_quote _ _ (by simp)]
      simp only [Option.bind_eq_bind, Option.bind]
      rw [stripPrefix_append]
      simp only [Option.bind_eq_bind, Option.bind, List.take_left, List.drop_left]
      have p : parseKeyColumn (keyColumnChars base) = some (base, []) := by simpa using parsed
      rw [p]
      simp only [Option.bind_eq_bind, Option.bind]
      rw [stripPrefix_append]
      simp only [Option.bind_eq_bind, Option.bind, List.take_left, List.drop_left, String.ofList_toList]
      rw [ColumnDefault.fromSource_spec]
      simp [stripPrefix, restored]

theorem parseColumns_append : (columns : List Core.Column) → (fuel : Nat) →
    (suffix : List Char) →
    columns ≠ [] → columns.length ≤ fuel →
    (∀ c ∈ columns, c.integerPrimaryKey = true →
      c.notNull = true) →
    (∀ c ∈ columns, c.integerPrimaryKey = true → c.textPrimaryKey = false) →
    parseColumns fuel (columnsChars columns ++ ')' :: suffix) =
      some (columns, ')' :: suffix)
  | [], _, _, h, _, _, _ => absurd rfl h
  | [c], fuel + 1, suffix, _, _, cons, exclusive => by
      have : columnsChars [c] = columnChars c := rfl
      rw [this]
      have step := parseColumn_any_append c
        (')' :: suffix)
        (cons c (by simp)) (exclusive c (by simp)) rfl
      simp only [parseColumns]
      rw [step]
      rfl
  | c :: d :: cs, fuel + 1, suffix, _, bound, cons, exclusive => by
      have expand : columnsChars (c :: d :: cs)
          = columnChars c ++ ',' :: columnsChars (d :: cs) := rfl
      rw [expand, List.append_assoc]
      have step := parseColumn_any_append c
        (',' :: (columnsChars (d :: cs) ++ ')' :: suffix))
        (cons c (by simp)) (exclusive c (by simp)) rfl
      simp only [parseColumns]
      rw [show ',' :: columnsChars (d :: cs) ++ ')' :: suffix
            = ',' :: (columnsChars (d :: cs) ++ ')' :: suffix) from rfl] at *
      rw [step]
      have tail := parseColumns_append (d :: cs) fuel suffix (by simp)
        (by simp at bound ⊢; omega)
        (fun x m => cons x (by simp [m]))
        (fun x m => exclusive x (by simp [m]))
      simp [tail]

theorem legacyKeyColumnChars_length_ge (column : Core.Column) : 1 ≤ (legacyKeyColumnChars column).length := by
  have plain (column : Core.Column) : 1 ≤ (plainColumnChars column).length := by
    simp [plainColumnChars, baseColumnChars, quoteChars]
  unfold legacyKeyColumnChars
  split
  · exact plain column
  · have enough := plain (primaryBase column)
    simp only [List.length_append]
    omega

theorem typedKeyColumnChars_length_ge (column : Core.Column) : 1 ≤ (typedKeyColumnChars column).length := by
  cases h : column.indexedType with
  | none => simpa [typedKeyColumnChars, h] using legacyKeyColumnChars_length_ge column
  | some typ => simp [typedKeyColumnChars, h]

theorem keyColumnChars_length_ge (column : Core.Column) : 1 ≤ (keyColumnChars column).length := by
  unfold keyColumnChars
  split
  · simp
  · exact typedKeyColumnChars_length_ge column

theorem columnChars_length_ge (column : Core.Column) : 1 ≤ (columnChars column).length := by
  cases hd : column.defaultValue with
  | none => simpa [columnChars, hd] using keyColumnChars_length_ge column
  | some spec =>
      have enough := keyColumnChars_length_ge { column with defaultValue := none }
      simp only [columnChars, hd, List.length_append, List.length_singleton]
      omega

theorem columnsChars_length_ge : (columns : List Core.Column) →
    columns.length ≤ (columnsChars columns).length
  | [] => by simp [columnsChars]
  | [c] => by simpa [columnsChars] using columnChars_length_ge c
  | c :: d :: cs => by
      have ih := columnsChars_length_ge (d :: cs)
      have head := columnChars_length_ge c
      simp only [columnsChars, List.length_cons, List.length_append] at ih ⊢
      omega

theorem parseChars_tableChars (s : Core.Schema) (printable : Printable s) :
    parseChars (tableChars s) = some s := by
  have shape : tableChars s
      = "CREATE TABLE ".toList ++
        ('"' :: (escapeIdent s.name.toList ++ '"' ::
          ('(' :: (columnsChars s.catalogColumns ++ [')'])))) := by
    simp [tableChars, quoteChars]
  have body := parseColumns_append s.catalogColumns
    ((columnsChars s.catalogColumns ++ [')']).length + 1)
    []
    printable.nonempty
    (by have := columnsChars_length_ge s.columns; simp only [List.length_append,
          List.length_singleton];
        have catalog := columnsChars_length_ge s.catalogColumns
        omega)
    printable.primaryKeyNotNull
    (by
      intro column member integer
      have catalogShape := printable.catalogShape
      unfold Core.Schema.CatalogShape at catalogShape
      split at catalogShape
      · have noInteger := catalogShape.2.2.1
        rw [List.findIdx?_eq_none_iff] at noInteger
        have contradiction := noInteger column member
        rw [integer] at contradiction
        contradiction
      · have noText := catalogShape.2.2.2
        rw [List.findIdx?_eq_none_iff] at noText
        exact noText column member)
  simp only [List.length_append, List.length_singleton, List.length_nil,
    Nat.add_zero] at body
  have body' :
      parseColumns
        ((columnsChars s.catalogColumns).length + 1 + 1)
        (columnsChars s.catalogColumns ++ [')']) =
        some (s.catalogColumns, [')']) := by
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using body
  rw [shape]
  unfold parseChars
  rw [stripPrefix_append]
  simp only [Option.bind_eq_bind, Option.bind]
  rw [takeIdent_escape s.name.toList
    ('(' :: (columnsChars s.catalogColumns ++ [')'])) (by simp)]
  simp only [Option.bind_eq_bind, Option.bind]
  rw [show (columnsChars s.catalogColumns ++ [')']).length + 1 =
    (columnsChars s.catalogColumns).length + 1 + 1 by simp]
  rw [body']
  simp only [Option.bind_eq_bind, Option.bind]
  have catalogShape := printable.catalogShape
  unfold Core.Schema.CatalogShape at catalogShape
  split at catalogShape
  · rw [catalogShape.2.2.1]
    simp only
    simp only [String.ofList_toList]
    apply congrArg some
    congr
    · exact catalogShape.1.symm
    · exact catalogShape.2.1.symm
    · rw [catalogShape.2.2.2.2]
      have width : s.columns.length = s.catalogColumns.length + 1 := by
        rw [catalogShape.1]
        simp
      rw [width]
  · rw [catalogShape.2.2.1]
    simp only
    simp only [String.ofList_toList]
    apply congrArg some
    congr
    · exact catalogShape.1
    · exact catalogShape.2.1.symm

end SQLeanite.CanonicalSchemaSQL
