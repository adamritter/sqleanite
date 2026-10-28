import SQLeanite.CanonicalSchemaSQL.Printable

namespace SQLeanite.CanonicalSchemaSQL

private theorem stripPrefix_notNull_end (rest : List Char)
    (separator : endsBaseColumn rest = true) : stripPrefix " NOT NULL".toList rest = none := by
  rcases baseSeparator_cases rest separator with ordinary | ⟨tail, rfl⟩
  · cases rest with
    | nil => rfl
    | cons c tail =>
        have notSpace : c ≠ ' ' := by
          intro equal
          subst c
          simp [endsColumn] at ordinary
        simp [stripPrefix, Ne.symm notSpace]
  · rfl

theorem parseBaseColumn_append (columnName : String)
    (columnNotNull columnPrimary columnTextPrimary : Bool)
    (rest : List Char)
    (consistent : columnPrimary = true →
      columnNotNull = true)
    (exclusive : columnPrimary = true → columnTextPrimary = false)
    (separator : endsBaseColumn rest = true ∨ (columnNotNull = true ∧ columnPrimary = false)) :
    parseBaseColumn (baseColumnChars
      { name := columnName, notNull := columnNotNull, integerPrimaryKey := columnPrimary, textPrimaryKey := columnTextPrimary } ++ rest)
      = some
        ({ name := columnName, notNull := columnNotNull, integerPrimaryKey := columnPrimary, textPrimaryKey := columnTextPrimary }, rest) := by
  cases columnPrimary <;> cases columnTextPrimary <;> cases columnNotNull
  all_goals simp only [Bool.false_eq_true, Bool.true_eq_false, and_false, false_and, or_false] at separator
  · have shape : baseColumnChars
        ({ name := columnName, notNull := false, integerPrimaryKey := false, textPrimaryKey := false } : Core.Column) ++ rest
        = '"' :: (escapeIdent columnName.toList ++ '"' :: rest) := by
      simp [baseColumnChars, quoteChars, columnSuffix, columnTypeChars]
    rw [shape]; simp only [parseBaseColumn]; rw [takeIdent_escape _ _ (by
      intro leadingQuote
      cases rest with
      | nil => simp at leadingQuote
      | cons character rest =>
          have : character = '"' := by simpa using leadingQuote
          subst character
          simp [endsBaseColumn, endsColumn] at separator)]
    simp [separator]
  · have shape : baseColumnChars
        ({ name := columnName, notNull := true, integerPrimaryKey := false, textPrimaryKey := false } : Core.Column) ++ rest
        = '"' :: (escapeIdent columnName.toList ++ '"' :: (" NOT NULL".toList ++ rest)) := by
      simp [baseColumnChars, quoteChars, columnSuffix, columnTypeChars]
    rw [shape]; simp only [parseBaseColumn]; rw [takeIdent_escape _ _ (by simp)]
    simp [endsBaseColumn, endsColumn, stripPrefix]
  · have noNotNull := stripPrefix_notNull_end rest separator
    have shape : baseColumnChars
        ({ name := columnName, notNull := false, integerPrimaryKey := false, textPrimaryKey := true } : Core.Column) ++ rest
        = '"' :: (escapeIdent columnName.toList ++ '"' ::
          (" TEXT PRIMARY KEY".toList ++ rest)) := by
      simp [baseColumnChars, quoteChars, columnSuffix, columnTypeChars]
    rw [shape]; simp only [parseBaseColumn]; rw [takeIdent_escape _ _ (by simp)]
    simp [endsBaseColumn, endsColumn, stripPrefix] at noNotNull ⊢
    exact noNotNull ▸ rfl
  · have shape : baseColumnChars
        ({ name := columnName, notNull := true, integerPrimaryKey := false, textPrimaryKey := true } : Core.Column) ++ rest
        = '"' :: (escapeIdent columnName.toList ++ '"' ::
          (" TEXT PRIMARY KEY NOT NULL".toList ++ rest)) := by
      simp [baseColumnChars, quoteChars, columnSuffix, columnTypeChars]
    rw [shape]; simp only [parseBaseColumn]; rw [takeIdent_escape _ _ (by simp)]
    simp [endsBaseColumn, endsColumn, stripPrefix]
  · exact absurd (consistent rfl) (by simp)
  · have shape : baseColumnChars
        ({ name := columnName, notNull := true, integerPrimaryKey := true, textPrimaryKey := false } : Core.Column) ++ rest
        = '"' :: (escapeIdent columnName.toList ++ '"' :: (" INTEGER PRIMARY KEY".toList ++ rest)) := by
      simp [baseColumnChars, quoteChars, columnSuffix, columnTypeChars]
    rw [shape]; simp only [parseBaseColumn]; rw [takeIdent_escape _ _ (by simp)]
    have noNotNull := stripPrefix_notNull_end rest separator
    simp [endsBaseColumn, endsColumn, stripPrefix] at noNotNull ⊢
    exact noNotNull ▸ rfl
  · exact absurd (exclusive rfl) (by simp)
  · exact absurd (exclusive rfl) (by simp)

private theorem separator_not_quote {rest : List Char} (separator : endsBaseColumn rest = true) :
    rest.head? ≠ some '"' := by
  cases rest with
  | nil => simp
  | cons c rest =>
      intro equal
      have : c = '"' := by simpa using equal
      subst c
      simp [endsBaseColumn, endsColumn] at separator

private theorem typeCase_not_quote (name : String) (rest : List Char)
    (boundary : rest.head? ≠ some '"') :
    (typeCaseChars name ++ rest).head? ≠ some '"' := by
  unfold typeCaseChars
  split
  · simpa using boundary
  · split <;> simp_all

theorem parseBaseColumn_typed_append (name typeName : String) (notNull : Bool)
    (rest : List Char) (separator : endsBaseColumn rest = true ∨ notNull = true) :
    parseBaseColumn (baseColumnChars (Core.Column.typed name typeName notNull) ++ rest) =
      some (Core.Column.typed name typeName notNull, rest) := by
  cases notNull
  · have separator := separator.resolve_right (by decide)
    have shape : baseColumnChars (Core.Column.typed name typeName false) ++ rest =
        '"' :: (escapeIdent name.toList ++ '"' :: ' ' :: '"' ::
          (escapeIdent typeName.toList ++ '"' :: (typeCaseChars typeName ++ rest))) := by
      by_cases empty : typeName = ""
      · simp [Core.Column.typed, empty, baseColumnChars, columnTypeChars, columnSuffix, quoteChars, typeCaseChars]
      · have nonempty : typeName.isEmpty = false := by simpa using empty
        simp [Core.Column.typed, empty, baseColumnChars, columnTypeChars, nonempty, columnSuffix, quoteChars, List.append_assoc]
    rw [shape]
    simp only [parseBaseColumn]
    rw [takeIdent_escape _ _ (by simp)]
    change parseTypedColumn name.toList (escapeIdent typeName.toList ++ '"' :: (typeCaseChars typeName ++ rest)) = _
    unfold parseTypedColumn
    rw [takeIdent_escape _ _ (typeCase_not_quote _ _ (separator_not_quote separator))]
    simp only [Option.bind_eq_bind, Option.bind, String.ofList_toList]
    rw [stripPrefix_append]
    simp [separator, bind, Option.bind]
  · have shape : baseColumnChars (Core.Column.typed name typeName true) ++ rest =
        '"' :: (escapeIdent name.toList ++ '"' :: ' ' :: '"' ::
          (escapeIdent typeName.toList ++ '"' :: (typeCaseChars typeName ++ (" NOT NULL".toList ++ rest)))) := by
      by_cases empty : typeName = ""
      · simp [Core.Column.typed, empty, baseColumnChars, columnTypeChars, columnSuffix, quoteChars, typeCaseChars, List.append_assoc]
      · have nonempty : typeName.isEmpty = false := by simpa using empty
        simp [Core.Column.typed, empty, baseColumnChars, columnTypeChars, nonempty, columnSuffix, quoteChars, List.append_assoc]
    rw [shape]
    simp only [parseBaseColumn]
    rw [takeIdent_escape _ _ (by simp)]
    change parseTypedColumn name.toList
      (escapeIdent typeName.toList ++ '"' :: (typeCaseChars typeName ++ (" NOT NULL".toList ++ rest))) = _
    unfold parseTypedColumn
    rw [takeIdent_escape _ _ (typeCase_not_quote _ _ (by simp))]
    simp only [Option.bind_eq_bind, Option.bind, String.ofList_toList]
    rw [stripPrefix_append]
    simp [endsBaseColumn, endsColumn, stripPrefix, bind, Option.bind]

theorem parseBaseColumn_integerNotNull_append (name : String) (rest : List Char) :
    let column : Core.Column := { name, notNull := true, integerPrimaryKey := true, integerPrimaryNotNull := true }
    parseBaseColumn (baseColumnChars column ++ rest) = some (column, rest) := by
  dsimp only
  have shape : baseColumnChars
      ({ name, notNull := true, integerPrimaryKey := true, integerPrimaryNotNull := true } : Core.Column) ++ rest =
      '"' :: (escapeIdent name.toList ++ '"' :: (" INTEGER PRIMARY KEY NOT NULL".toList ++ rest)) := by
    simp [baseColumnChars, quoteChars, columnSuffix, columnTypeChars]
  rw [shape]
  simp only [parseBaseColumn]
  rw [takeIdent_escape _ _ (by simp)]
  simp [endsBaseColumn, endsColumn, stripPrefix]

theorem parseBaseColumn_any_append (column : Core.Column) (rest : List Char)
    (consistent : column.integerPrimaryKey = true → column.notNull = true)
    (exclusive : column.integerPrimaryKey = true → column.textPrimaryKey = false)
    (policy : column.notNullConflict = .abort)
    (primaryPolicy : column.primaryConflict = .abort)
    (noDefault : column.defaultValue = none)
    (noIndexed : column.indexedType = none)
    (noAuto : column.autoIncrement = false)
    (separator : endsBaseColumn rest = true ∨ (column.notNull = true ∧
      (column.integerPrimaryKey = false ∨ column.integerPrimaryNotNull = true))) :
    parseBaseColumn (baseColumnChars column ++ rest) = some (column, rest) := by
  by_cases explicitType : column.explicitEmptyType = true
  · have flags := column.explicitEmptyTypeOnly explicitType
    have noExplicitKey : column.integerPrimaryNotNull = false := by
      cases h : column.integerPrimaryNotNull
      · rfl
      · have key := column.integerPrimaryNotNullOnly h
        simp_all
    have equal : column = Core.Column.typed column.name "" column.notNull := by
      cases column
      simp_all [Core.Column.typed]
    have ending : endsBaseColumn rest = true ∨ column.notNull = true := by
      rcases separator with h | h
      · exact Or.inl h
      · exact Or.inr h.1
    rw [equal]
    exact parseBaseColumn_typed_append _ _ _ rest ending
  have notExplicitType : column.explicitEmptyType = false := Bool.eq_false_iff.mpr explicitType
  by_cases declared : column.integerPrimaryNotNull = true
  · have primary := column.integerPrimaryNotNullOnly declared
    have required := consistent primary
    have notText := exclusive primary
    have empty := column.primaryType (by simp [primary])
    have equal : column = { name := column.name, notNull := true, integerPrimaryKey := true, integerPrimaryNotNull := true } := by cases column; simp_all
    rw [equal]
    exact parseBaseColumn_integerNotNull_append _ rest
  · have undeclared : column.integerPrimaryNotNull = false := Bool.eq_false_iff.mpr declared
    by_cases empty : column.declaredType = ""
    · have equal : column = { name := column.name, notNull := column.notNull, integerPrimaryKey := column.integerPrimaryKey, textPrimaryKey := column.textPrimaryKey } := by cases column; simp_all
      rw [equal]
      exact parseBaseColumn_append _ _ _ _ rest consistent exclusive (by simpa [undeclared] using separator)
    · have notPrimary : column.integerPrimaryKey = false ∧ column.textPrimaryKey = false := by
        have h := column.primaryType
        cases hi : column.integerPrimaryKey <;> cases ht : column.textPrimaryKey <;> simp_all
      have equal : column = { name := column.name, notNull := column.notNull, declaredType := column.declaredType } := by cases column; simp_all
      rw [equal]
      simpa [Core.Column.typed, empty] using
        parseBaseColumn_typed_append column.name column.declaredType column.notNull rest
          (by rcases separator with h | h; exact Or.inl h; exact Or.inr h.1)

theorem parsePlainColumn_any_append (column : Core.Column) (rest : List Char)
    (consistent : column.integerPrimaryKey = true → column.notNull = true)
    (exclusive : column.integerPrimaryKey = true → column.textPrimaryKey = false)
    (primaryPolicy : column.primaryConflict = .abort)
    (noDefault : column.defaultValue = none)
    (noIndexed : column.indexedType = none)
    (noAuto : column.autoIncrement = false)
    (separator : endsBaseColumn rest = true) :
    parsePlainColumn (plainColumnChars column ++ rest) = some (column, rest) := by
  let base := column.withoutNotNullConflict
  have allowed : endsBaseColumn (notNullConflictChars column.notNullConflict ++ rest) = true ∨
      (base.notNull = true ∧ (base.integerPrimaryKey = false ∨ base.integerPrimaryNotNull = true)) := by
    by_cases plain : column.notNullConflict = .abort
    · exact .inl (by simpa [plain, notNullConflictChars] using separator)
    · have required := column.notNullConflictOnly plain
      apply Or.inr
      refine ⟨required.1, ?_⟩
      cases key : column.integerPrimaryKey with
      | false => exact Or.inl key
      | true => exact Or.inr (required.2 key)
  have parsed := parseBaseColumn_any_append base
    (notNullConflictChars column.notNullConflict ++ rest) consistent exclusive rfl primaryPolicy noDefault noIndexed noAuto allowed
  have restored := Core.Column.restoreNotNullConflict column
  change parsePlainColumn (baseColumnChars base ++ notNullConflictChars column.notNullConflict ++ rest) = _
  rw [List.append_assoc]
  unfold parsePlainColumn
  rw [parsed]
  simp only [Option.bind_eq_bind, Option.bind]
  cases policy : column.notNullConflict with
  | abort =>
      have same : base = column := by
        dsimp [base, Core.Column.withoutNotNullConflict]
        cases column
        simp_all
      rcases baseSeparator_cases rest separator with ordinary | ⟨tail, rfl⟩
      · cases rest with
        | nil => simp [notNullConflictChars, stripPrefix, same]
        | cons character tail =>
            have notSpace : character ≠ ' ' := by
              intro equal
              subst character
              simp [endsColumn] at ordinary
            simp [notNullConflictChars, stripPrefix, same, Ne.symm notSpace]
      · simp [notNullConflictChars, stripPrefix, same]
  | ignore =>
      rw [policy] at restored
      simp [notNullConflictChars, stripPrefix, bind, Option.bind, base, restored]
  | replace =>
      rw [policy] at restored
      simp [notNullConflictChars, stripPrefix, bind, Option.bind, base, restored]

theorem primaryFromBase_inverse (column : Core.Column)
    (primary : (column.integerPrimaryKey || column.textPrimaryKey) = true)
    (consistent : column.integerPrimaryKey = true → column.notNull = true)
    (exclusive : column.integerPrimaryKey = true → column.textPrimaryKey = false)
    (noDefault : column.defaultValue = none)
    (noIndexed : column.indexedType = none)
    (noAuto : column.autoIncrement = false) :
    primaryFromBase (primaryBase column) column.primaryConflict = some column := by
  have notExplicitType : column.explicitEmptyType = false := by
    cases declared : column.explicitEmptyType
    · rfl
    · have flags := column.explicitEmptyTypeOnly declared
      simp_all
  have explicitOnly := column.integerPrimaryNotNullOnly
  have empty := column.primaryType primary
  cases hi : column.integerPrimaryKey <;> cases ht : column.textPrimaryKey <;>
    cases hn : column.integerPrimaryNotNull <;> cases column <;> simp_all [primaryBase, primaryFromBase]

theorem parseLegacyKeyColumn_any_append (column : Core.Column) (rest : List Char)
    (consistent : column.integerPrimaryKey = true → column.notNull = true)
    (exclusive : column.integerPrimaryKey = true → column.textPrimaryKey = false)
    (noDefault : column.defaultValue = none)
    (noIndexed : column.indexedType = none)
    (noAuto : column.autoIncrement = false)
    (separator : endsColumn rest = true) :
    parseLegacyKeyColumn (legacyKeyColumnChars column ++ rest) = some (column, rest) := by
  by_cases plain : column.primaryConflict = .abort
  · have parsed := parsePlainColumn_any_append column rest consistent exclusive plain noDefault noIndexed noAuto
      (by simp [endsBaseColumn, separator])
    simp only [legacyKeyColumnChars, plain, if_pos, parseLegacyKeyColumn, parsed, Option.bind_eq_bind, Option.bind]
    cases rest with
    | nil => rfl
    | cons character tail =>
        have notSpace : character ≠ ' ' := by
          intro equal
          subst character
          simp [endsColumn] at separator
        simp [stripPrefix, Ne.symm notSpace]
  · have primary := column.primaryConflictOnly plain
    have restored := primaryFromBase_inverse column primary consistent exclusive noDefault noIndexed noAuto
    have baseConsistent : (primaryBase column).integerPrimaryKey = true → (primaryBase column).notNull = true := by
      simp [primaryBase]; split <;> simp
    have baseExclusive : (primaryBase column).integerPrimaryKey = true → (primaryBase column).textPrimaryKey = false := by
      simp [primaryBase]; split <;> simp
    have basePolicy : (primaryBase column).primaryConflict = .abort := by
      simp [primaryBase]; split <;> rfl
    have tail : endsBaseColumn (primaryConflictChars column.primaryConflict ++ rest) = true := by
      cases policy : column.primaryConflict <;> simp_all [primaryConflictChars, endsBaseColumn]
    have parsed := parsePlainColumn_any_append (primaryBase column)
      (primaryConflictChars column.primaryConflict ++ rest) baseConsistent baseExclusive basePolicy (by simp [primaryBase]; split <;> rfl) (by simp [primaryBase]; split <;> rfl) (by simp [primaryBase]; split <;> rfl) tail
    simp only [legacyKeyColumnChars, if_neg plain, List.append_assoc]
    unfold parseLegacyKeyColumn
    rw [parsed]
    simp only [Option.bind_eq_bind, Option.bind]
    cases policy : column.primaryConflict with
    | abort => contradiction
    | ignore =>
        rw [policy] at restored
        simp [primaryConflictChars, stripPrefix, bind, Option.bind, restored]
    | replace =>
        rw [policy] at restored
        simp [primaryConflictChars, stripPrefix, bind, Option.bind, restored]

private theorem parseIndexedType_absent (rest : List Char)
    (boundary : rest.take 2 ≠ [' ', '"']) :
    parseIndexedType rest = some ({ declaredType := "" }, rest) := by
  unfold parseIndexedType
  split <;> simp_all

theorem parseIndexedType_quoted (name : String) (rest : List Char) :
    parseIndexedType ((' ' :: (quoteChars name ++ "(0)".toList)) ++ rest) =
      some (typedIndexedType name, rest) := by
  simp only [quoteChars, List.cons_append, List.append_assoc, List.nil_append, parseIndexedType]
  rw [takeIdent_escape _ _ (by simp)]
  simp only [Option.bind_eq_bind, Option.bind, String.ofList_toList]
  rw [stripPrefix_append]
  rfl

theorem parseIndexedType_append (typ : Core.IndexedType) (rest : List Char)
    (boundary : rest.take 2 ≠ [' ', '"']) :
    parseIndexedType (indexedTypeChars typ ++ rest) = some (typ, rest) := by
  cases typ with
  | mk name explicit consistent =>
      cases explicit
      · by_cases empty : name = ""
        · subst name
          simpa [indexedTypeChars] using parseIndexedType_absent rest boundary
        · have nonempty : name.isEmpty = false := by simpa using empty
          simpa [indexedTypeChars, nonempty, typedIndexedType, empty] using
            parseIndexedType_quoted name rest
      · have empty := consistent rfl
        subst name
        simpa [indexedTypeChars, typedIndexedType] using parseIndexedType_quoted "" rest

theorem fromIndexed_inverse (column : Core.Column) (typ : Core.IndexedType)
    (declared : column.indexedType = some typ)
    (exclusive : column.integerPrimaryKey = true → column.textPrimaryKey = false)
    (noDefault : column.defaultValue = none) :
    fromIndexed column.name typ column.notNull column.notNullConflict column.primaryConflict = some column := by
  have textKey : column.textPrimaryKey = true := column.indexedTypeOnly (by simp [declared])
  have noInteger : column.integerPrimaryKey = false := by
    cases key : column.integerPrimaryKey
    · rfl
    · have notText := exclusive key
      simp_all
  have noAuto : column.autoIncrement = false := by
    cases h : column.autoIncrement
    · rfl
    · have key := column.autoIncrementOnly h
      simp_all
  have noIntegerNull : column.integerPrimaryNotNull = false := by
    cases h : column.integerPrimaryNotNull
    · rfl
    · have key := column.integerPrimaryNotNullOnly h
      simp_all
  have empty := column.primaryType (by simp [textKey])
  have notEmptyType : column.explicitEmptyType = false := by
    cases h : column.explicitEmptyType
    · rfl
    · have flags := column.explicitEmptyTypeOnly h
      simp_all
  unfold fromIndexed
  have equal : ({
      name := column.name
      notNull := column.notNull
      textPrimaryKey := true
      indexedType := some typ
      primaryConflict := column.primaryConflict
      primaryConflictOnly := by simp
      indexedTypeOnly := by simp } : Core.Column) =
      column.withoutNotNullConflict := by
    cases column
    simp_all [Core.Column.withoutNotNullConflict]
  rw [equal]
  exact Core.Column.restoreNotNullConflict column

theorem parseIndexedBody_append (column : Core.Column) (typ : Core.IndexedType) (rest : List Char)
    (declared : column.indexedType = some typ)
    (exclusive : column.integerPrimaryKey = true → column.textPrimaryKey = false)
    (noDefault : column.defaultValue = none) :
    parseIndexedBody (indexedBodyChars column typ ++ rest) = some (column, rest) := by
  have restored := fromIndexed_inverse column typ declared exclusive noDefault
  simp only [indexedBodyChars, quoteChars, List.cons_append, List.append_assoc, List.nil_append,
    parseIndexedBody]
  rw [takeIdent_escape _ _ (by
    unfold indexedTypeChars
    split <;> cases column.notNull <;> simp)]
  simp only [Option.bind_eq_bind, Option.bind]
  rw [parseIndexedType_append typ _ (by cases column.notNull <;> simp)]
  simp only [Option.bind_eq_bind, Option.bind, String.ofList_toList]
  cases hn : column.notNull <;> cases np : column.notNullConflict <;>
    cases pp : column.primaryConflict <;>
    simp_all [parseNullPolicy, parseExplicitPrimary, notNullConflictChars, explicitPrimaryChars,
      stripPrefix, Option.bind_eq_bind, Option.bind]

theorem parseTypedKeyColumn_any_append (column : Core.Column) (rest : List Char)
    (consistent : column.integerPrimaryKey = true → column.notNull = true)
    (exclusive : column.integerPrimaryKey = true → column.textPrimaryKey = false)
    (noDefault : column.defaultValue = none)
    (noAuto : column.autoIncrement = false)
    (separator : endsColumn rest = true) :
    parseTypedKeyColumn (typedKeyColumnChars column ++ rest) = some (column, rest) := by
  cases declared : column.indexedType with
  | none =>
      have parsed := parseLegacyKeyColumn_any_append column rest consistent exclusive noDefault declared noAuto separator
      have noTag : stripPrefix "/*sqleanite-key*/".toList (legacyKeyColumnChars column ++ rest) = none := by
        unfold legacyKeyColumnChars
        split <;> simp [plainColumnChars, baseColumnChars, quoteChars, stripPrefix]
      simp only [typedKeyColumnChars, declared, parseTypedKeyColumn]
      rw [noTag]
      exact parsed
  | some typ =>
      simp only [typedKeyColumnChars, declared, List.append_assoc, parseTypedKeyColumn]
      rw [stripPrefix_append]
      exact parseIndexedBody_append column typ rest declared exclusive noDefault

theorem typedKeyColumnChars_noDefaultTag (column : Core.Column) (rest : List Char) :
    stripPrefix "/*sqleanite-default ".toList (typedKeyColumnChars column ++ rest) = none := by
  cases declared : column.indexedType with
  | none =>
      simp only [typedKeyColumnChars, declared, legacyKeyColumnChars]
      split <;> simp [plainColumnChars, baseColumnChars, quoteChars, stripPrefix]
  | some typ => simp [typedKeyColumnChars, declared, stripPrefix]

theorem fromAuto_inverse (column : Core.Column)
    (automatic : column.autoIncrement = true)
    (consistent : column.integerPrimaryKey = true → column.notNull = true)
    (exclusive : column.integerPrimaryKey = true → column.textPrimaryKey = false)
    (noDefault : column.defaultValue = none) :
    fromAuto column.name column.integerPrimaryNotNull column.notNullConflict column.primaryConflict = some column := by
  have aliasKey := column.autoIncrementOnly automatic
  have required := consistent aliasKey
  have noText := exclusive aliasKey
  have empty := column.primaryType (by simp [aliasKey])
  have noIndexed : column.indexedType = none := by
    cases h : column.indexedType
    · rfl
    · have textKey := column.indexedTypeOnly (by simp [h])
      simp_all
  have noEmptyType : column.explicitEmptyType = false := by
    cases h : column.explicitEmptyType
    · rfl
    · have flags := column.explicitEmptyTypeOnly h
      simp_all
  unfold fromAuto
  have equal : ({
      name := column.name
      notNull := true
      integerPrimaryKey := true
      integerPrimaryNotNull := column.integerPrimaryNotNull
      primaryConflict := column.primaryConflict
      primaryConflictOnly := by simp
      autoIncrement := true
      autoIncrementOnly := by simp } : Core.Column) = column.withoutNotNullConflict := by
    cases column
    simp_all [Core.Column.withoutNotNullConflict]
  rw [equal]
  exact Core.Column.restoreNotNullConflict column

end SQLeanite.CanonicalSchemaSQL
