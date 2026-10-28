# Sourced by live-path-check.sh; shares its failure status and scratch files.

if rg -F -q 'unless SQLite.TextEncoding.supported header.textEncoding.val do' "$audit_sources/SQLeanite/CoreFileAdapter.lean" &&
   rg -F -q 'SQLite.TextEncoding.supported header.textEncoding.val' SQLeanite/CoreWALFileAdapter.lean &&
   rg -F -q 'unless utf8TextEncoding header.textEncoding.val do' "$audit_sources/SQLeanite/CoreFileAdapter.lean" &&
   rg -F -q 'CoreFileAdapter.utf8TextEncoding header.textEncoding.val' SQLeanite/CoreWALFileAdapter.lean &&
   rg -F -q 'CoreFileAdapter.utf8TextEncoding_iff' "$audit_sources/SQLeanite/ProofAxioms.lean"; then
  ok "zero cookies retain UTF-8 defaults; both readers admit explicit text encodings and writers keep their actual format guard"
else
  fail "text encoding read admission, zero-cookie default or write-format guard is disconnected"
fi

if rg -F -q 'CoreCheck.forUpdate table.schema assigned (← source.compiledChecks)' "$audit_sources/SQLeanite/Core.lean" &&
   rg -F -q 'table.requireChecks row' "$audit_sources/SQLeanite/Core.lean" &&
   rg -F -q 'table.requirePatchedChecks selected rows' "$audit_sources/SQLeanite/Core.lean" &&
   rg -F -q 'stored.checkFailure row' SQLeanite/CoreInsertIgnore.lean &&
   rg -F -q 'stored.checkFailure candidate' SQLeanite/CoreUpsertSQL.lean &&
   rg -F -q 'match executeBase state statement with' SQLeanite/CoreSourceSQL.lean &&
   rg -F -q 'Core.Table.createRow_checks' "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   rg -F -q 'CoreCatalogSQL.retain_compiledChecks' "$audit_sources/SQLeanite/ProofAxioms.lean"; then
  ok "retained CHECK programs reach inserts, updates, IGNORE and UPSERT with audited cache/row contracts"
else
  fail "CHECK preparation, constraint execution or cache/row contracts are disconnected"
fi

if rg -F -q 'if CoreViewSQL.uses query.compoundHeight state query || hasDerived query.compoundHeight query then insertSelect state' "$audit_sources/SQLeanite/CoreDerivedSQL.lean" &&
   rg -F -q 'executeConnectionStatement state (.insert table columns inputs' "$audit_sources/SQLeanite/CoreDerivedSQL.lean" &&
   rg -F -q 'CoreDerivedSQL.streamingValues_ordered' "$audit_sources/SQLeanite/ProofAxioms.lean"; then
  ok "derived INSERT inputs rejoin ordinary writes and ORDER BY excludes VALUES streaming"
else
  fail "derived INSERT routing or the streaming order guard is disconnected"
fi


if rg -F -q 'if stored.hasChecks then' "$audit_sources/SQLeanite/CoreSQL.lean" &&
   rg -F -q 'CoreUpdateRow.apply state stored' "$audit_sources/SQLeanite/CoreSQL.lean" &&
   rg -F -q 'CoreUpdateRow.apply state stored' SQLeanite/CoreUpsertSQL.lean &&
   rg -F -q 'stored.checkFailure row (some assigned)' SQLeanite/CoreUpdateRow.lean &&
   rg -F -q 'remaining.upsert row rowValid' SQLeanite/CoreUpdateRow.lean &&
   rg -F -q 'CoreUpdateRow.install_rows' "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   rg -F -q 'CoreCheck.forUpdate_member' "$audit_sources/SQLeanite/ProofAxioms.lean"; then
  ok "UPDATE CHECK dependencies retain SET columns and install rows through checked Core operations"
else
  fail "UPDATE CHECK dependency routing or row installation contract is disconnected"
fi

if rg -F -q 'captures expression.height (SQLite.Scalar.prepare expression)' SQLeanite/CoreScalarQuery.lean &&
   rg -F -q 'hasFunction_scalarSubquery' "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   rg -F -q 'hasFunction_existsSubquery' "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   rg -F -q 'mismatch "the captured IN subquery"' "$audit_sources/SQLeanite/CoreTokenGrammar.lean" &&
   rg -F -q 'mismatch "the captured EXISTS subquery"' "$audit_sources/SQLeanite/CoreTokenGrammar.lean"; then
  ok "parser-folded subqueries precede query preparation and IN/EXISTS tokens are replayed"
else
  fail "subquery preparation or independent captured-token replay is disconnected"
fi

if rg -F -q 'headerOrEmpty bytes.toList' "$audit_sources/SQLeanite/CoreFileAdapter.lean" &&
   rg -F -q 'CoreFileAdapter.headerOrEmpty first main.size' SQLeanite/CoreWALFileAdapter.lean &&
   rg -F -q 'empty WAL database requires exclusive initialization' SQLeanite/CoreWALFileAdapter.lean &&
   rg -F -q 'if first.size ≤ 1 && first.size == (← paths.main.metadata).byteSize.toNat then return true' SQLeanite/SQLite/WALShared.lean &&
   rg -F -q 'CoreFileAdapter.headerOrEmpty_short_nonempty' "$audit_sources/SQLeanite/ProofAxioms.lean"; then
  ok "zero-byte opens stay virtual and initial WAL publication requires the exclusive database lock"
else
  fail "zero-byte admission or exclusive WAL initialization is disconnected"
fi

if rg -F -q 'kind := .membership' "$audit_sources/SQLeanite/SQLite/Scalar.lean" &&
   rg -F -q 'SQLite.Scalar.membershipTyped collation affinity left typed' SQLeanite/CoreScalarQuery.lean &&
   rg -F -q 'executeWithSources compile preparing (request.kind == .exists)' SQLeanite/CoreScalarQuery.lean &&
   rg -F -q 'if limit.any (count ≥ ·) then break' SQLeanite/CoreScalarQuery.lean &&
   rg -F -q 'CoreScalarQuery.setTruth_empty' "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   rg -F -q 'CoreScalarQuery.scan_limit_zero' "$audit_sources/SQLeanite/ProofAxioms.lean"; then
  ok "IN/NOT IN set callbacks and EXISTS lazy scans reach audited empty-set and zero-limit contracts"
else
  fail "set-subquery callbacks or lazy scan contracts are disconnected"
fi

if rg -F -q 'parseInRhs (parseExprFuel fuel 0)' "$audit_sources/SQLeanite/Parser.lean" &&
   rg -F -q 'else matchInTable (significant tokens.toList)' "$audit_sources/SQLeanite/CoreTokenGrammar.lean" &&
   rg -F -q 'bindInputs (original.compoundHeight + 1)' SQLeanite/CoreScalarQuery.lean &&
   rg -F -q 'bindInputs fuel state parents arm' SQLeanite/CoreScalarQuery.lean &&
   rg -F -q 'CoreTokenGrammar.inTableNames?_where' "$audit_sources/SQLeanite/ProofAxioms.lean"; then
  ok "IN table names replay independently and compound arms retain lexical parent scopes"
else
  fail "IN table replay or correlated compound binding is disconnected"
fi

if rg -F -q 'else executeCheckedAdd state name definition' SQLeanite/CoreSourceSQL.lean &&
   rg -F -q 'oldChecks ++ (CoreCheck.collect #[definition] #[]).map' SQLeanite/CoreSourceSQL.lean &&
   rg -F -q 'CoreCollationSyntax.forTable tableName columns check.expression' SQLeanite/CoreSourceSQL.lean &&
   rg -F -q 'CoreCheck.requireRows after.schema checks after.rows' SQLeanite/CoreSourceSQL.lean &&
   rg -F -q 'CoreCheck.requireRows_checked' "$audit_sources/SQLeanite/ProofAxioms.lean"; then
  ok "ALTER ADD CHECK scans existing rows before retained catalog publication through the audited row contract"
else
  fail "ALTER ADD CHECK validation or retained-source routing is disconnected"
fi

if rg -F -q 'CoreForeignKey.requireTransition state next edges' "$audit_sources/SQLeanite/CoreDerivedSQL.lean" &&
   rg -F -q 'if !state.foreignKeys && preparation.isNone then return ← CoreConnectionSQL.executeStatement state sql source' "$audit_sources/SQLeanite/CoreDerivedSQL.lean" &&
   rg -F -q 'CoreSQL.executeInsertReturning state table columns (.inl rows)' "$audit_sources/SQLeanite/CoreDerivedSQL.lean" &&
   rg -F -q 'next.recordForeignWrite tableName row.rowid none' "$audit_sources/SQLeanite/CoreSQL.lean" &&
   rg -F -q 'outcome.1.recordForeignWrite tableName rowid' "$audit_sources/SQLeanite/CoreSQL.lean" &&
   rg -F -q 'next.recordForeignWrite stored.schema.name row.rowid' SQLeanite/CoreUpsertSQL.lean &&
   rg -F -q 'CoreCatalogSQL.retain_compiledForeignKeys' "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   rg -F -q 'CoreForeignKey.requireTransition_clause' "$audit_sources/SQLeanite/ProofAxioms.lean"; then
  ok "retained foreign keys and accepted INSERT/UPDATE/UPSERT effects reach the audited prepublication check"
else
  fail "foreign-key source, row-effect recording or prepublication validation is disconnected"
fi

if rg -F -q 'CoreForeignKeyData.checkRows schemaDatabase' SQLeanite/CoreSchemaPragma.lean &&
   rg -F -q 'CoreSchemaPragma.inspectionRows state.database schema' SQLeanite/CorePragmaTable.lean &&
   rg -F -q '"pragma_foreign_key_check" => some' SQLeanite/CorePragmaTable.lean &&
   rg -F -q '"pragma_foreign_key_list" => some' SQLeanite/CorePragmaTable.lean &&
   rg -F -q 'CoreForeignKeyData.referenceSatisfied_null' "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   rg -F -q 'let next := schemaTransition state next sql' "$audit_sources/SQLeanite/CoreDerivedSQL.lean" &&
   rg -F -q 'schemaHash := some state.schemaHashValue' "$audit_sources/SQLeanite/CoreDerivedSQL.lean" &&
   rg -F -q 'SQLite.SchemaHash.rollback_unchanged' "$audit_sources/SQLeanite/ProofAxioms.lean"; then
  ok "foreign-key inspection statements and table functions share retained programs and the audited NULL rule"
else
  fail "foreign-key inspection routing or NULL-reference contract is disconnected"
fi

if rg -F -q 'let next ← CoreForeignKeyRename.execute state next sql source' "$audit_sources/SQLeanite/CoreDerivedSQL.lean" &&
   rg -F -q 'current ← CoreSourceSQL.retain current child.schema.name sql' SQLeanite/CoreForeignKeyRename.lean &&
   rg -F -q 'SQLite.ForeignKeyCatalog.rewrite_no_targets' "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   rg -F -q 'CoreForeignKeyRename.execute_unrelated' "$audit_sources/SQLeanite/ProofAxioms.lean"; then
  ok "parent renames rewrite and independently validate retained child REFERENCES programs"
else
  fail "foreign-key rename propagation is disconnected"
fi

if rg -F -q 'CoreForeignKeySyntax.collect columns constraints' SQLeanite/CoreCatalogSQL.lean &&
   rg -F -q 'matchTableForeign constraint key' "$audit_sources/SQLeanite/CoreTokenGrammar.lean" &&
   rg -F -q 'constraint.check.isNone && constraint.references.isNone' SQLeanite/CoreSourceSQL.lean &&
   rg -F -q 'foreignChildReferences oldName 0 tokens' SQLeanite/SQLite/ColumnCatalog.lean &&
   rg -F -q 'CoreForeignKeySyntax.collect_no_tables' "$audit_sources/SQLeanite/ProofAxioms.lean"; then
  ok "table FOREIGN KEY programs retain certified child bindings, declaration order and source-aware construction"
else
  fail "table FOREIGN KEY metadata, certification or retained construction is disconnected"
fi

if rg -F -q 'CoreStrictSyntax.require table.schema.name columns row.values' "$audit_sources/SQLeanite/Core.lean" &&
   rg -F -q 'if strictColumns.isSome then executeCheckedAdd' SQLeanite/CoreSourceSQL.lean &&
   rg -F -q 'CoreStrictSyntax.lower name columns constraints' SQLeanite/CoreSourceSQL.lean &&
   rg -F -q 'CoreStrictSyntax.require_checked' "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   rg -F -q 'CoreCatalogSQL.retain_compiledStrictColumns' "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   rg -F -q '"pragma_table_list" => some' SQLeanite/CorePragmaTable.lean; then
  ok "STRICT retained type programs check row writes and ADD defaults while preserving ANY storage and public metadata"
else
  fail "STRICT typing, catalog retention, ADD validation or metadata is disconnected"
fi

if rg -F -q 'expectMainDeclaredName name' "$audit_sources/SQLeanite/CoreTokenGrammar.lean" &&
   rg -F -q 'schemaName.toLower == "main" then objectName' "$audit_sources/SQLeanite/Parser.lean" &&
   rg -F -q 'unknown database {token.render}' "$audit_sources/SQLeanite/CoreTokenGrammar.lean" &&
   rg -F -q 'CREATE main qualifiers preserve literal periods and certified target names' "$audit_sources/Tests.lean"; then
  ok "CREATE main qualifiers retain independently replayed object names and literal-period boundaries"
else
  fail "CREATE qualifier binding, token spelling or target regression is disconnected"
fi

# Generated source programs preserve typed registers before ordinary Core writes.
if rg -F -q 'CoreGeneratedSQL.statement state sql' "$audit_sources/SQLeanite/CoreDerivedSQL.lean" &&
   rg -F -q 'CoreGeneratedSQL.preparation state target' "$audit_sources/SQLeanite/CoreDerivedSQL.lean" &&
   rg -F -q 'source.compiledGeneratedColumns' SQLeanite/CoreGeneratedSQL.lean &&
   rg -F -q 'SQLite.Scalar.evalTypedWithBuiltin' SQLeanite/CoreGeneratedSQL.lean &&
   rg -F -q 'CoreGeneratedSyntax.affected generated direct' SQLeanite/CoreForeignKey.lean &&
   rg -F -q 'CoreGeneratedSQL.calculate_empty' "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   rg -F -q 'STORED generated programs preserve dependency order' "$audit_sources/Tests.lean"; then
  ok "STORED programs bind dependencies, retain typed registers and reach checked Core writes"
else
  fail "STORED program binding, row preparation, foreign-key footprint or runtime regression is disconnected"
fi

if rg -F -q 'executeGeneratedAdd state name definition strictColumns' SQLeanite/CoreSourceSQL.lean &&
   rg -F -q 'CoreSQL.prepareAddColumn state name definition' SQLeanite/CoreSourceSQL.lean &&
   rg -F -q 'requireStoredEmpty before' SQLeanite/CoreSourceSQL.lean &&
   rg -F -q 'must have at least one non-generated column' SQLeanite/CoreSourceSQL.lean &&
   rg -F -q 'CoreSourceSQL.requireStoredEmpty_rejects_nonempty' "$audit_sources/SQLeanite/ProofAxioms.lean"; then
  ok "generated ALTER validates declarations and rejects populated additions before row rebuilding"
else
  fail "generated ALTER validation, empty-table contract or last-ordinary-column guard is disconnected"
fi

if rg -F -q 'prepareInsertTargets columns source preparation' "$audit_sources/SQLeanite/CoreSQL.lean" &&
   rg -F -q 'CoreSQL.prepareInsertTargets columns inputSource preparation' SQLeanite/CoreUpsertSQL.lean &&
   rg -F -q 'CoreSQL.prepareInsertTargets columns (.inr query) preparation' "$audit_sources/SQLeanite/CoreDerivedSQL.lean" &&
   rg -F -q 'CoreSQL.prepareInsertTargets_ordinary' "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   rg -F -q 'Generated INSERT retains original target-list provenance' "$audit_sources/Tests.lean"; then
  ok "generated INSERT retains source target provenance through ordinary, derived, register and UPSERT inputs"
else
  fail "generated INSERT target provenance, shared arity checks or ordinary-target contract is disconnected"
fi

if rg -F -q 'CoreDeclaredCollationSQL.statement state sql' "$audit_sources/SQLeanite/CoreDerivedSQL.lean" &&
   rg -F -q 'CoreDeclaredCollationSQL.uses state select' SQLeanite/CoreFileEngine.lean &&
   rg -F -q 'CoreDeclaredCollationSQL.uses state select' SQLeanite/CoreWALFileEngine.lean &&
   rg -F -q 'CoreSchemaSQL.binaryCollations sql' SQLeanite/CoreLazyFileEngine.lean &&
   rg -F -q 'CoreSchemaSQL.binaryCollations sql' "$audit_sources/SQLeanite/CoreFileAdapter.lean" &&
   rg -F -q 'SQLite.ExprCollation.effectiveName term.expr' SQLeanite/CoreOrder.lean &&
   rg -F -q 'CoreCatalogSQL.retain_compiledCollations' "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   rg -F -q 'Declared column collations preserve explicit priority' "$audit_sources/Tests.lean"; then
  ok "declared column programs reach typed expressions and decline BINARY-only file read plans"
else
  fail "declared collation binding, priority, row/file guards or retained-program contract is disconnected"
fi

if rg -F -q 'defaultCollation := ExprCollation.effectiveName argument' "$audit_sources/SQLeanite/SQLite/Scalar.lean" &&
   rg -F -q 'membershipCollation request.collation entry.collation request.defaultCollation entry.defaultCollation' SQLeanite/CoreScalarQuery.lean &&
   rg -F -q 'let operand ← CoreSQL.compoundTailArm validated.inputState operand' SQLeanite/CoreScalarQuery.lean &&
   rg -F -q 'CoreScalarQuery.membershipCollation_explicit_right' "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   rg -F -q 'IN query collation distinguishes explicit operators' "$audit_sources/Tests.lean"; then
  ok "IN query operands preserve explicit-before-declared collation and scalar-result isolation"
else
  fail "IN query default metadata, comparison priority or scalar isolation regression is disconnected"
fi

if rg -F -q 'declaredResultCollationFuel select.compoundHeight select' "$audit_sources/SQLeanite/CoreSQL.lean" &&
   rg -F -q 'let operand := membershipOperand validated.inputQuery.compoundHeight validated.inputQuery' SQLeanite/CoreScalarQuery.lean &&
   rg -F -q 'CoreScalarQuery.membershipOperand_last' "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   rg -F -q 'CoreSQL.requiresCompoundCollation_no_compounds' "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   rg -F -q 'CoreSQLReadText.translatedCompound_declaredResultCollation_false' "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   rg -F -q 'Compound declared collations preserve set keys and IN operand metadata' "$audit_sources/Tests.lean"; then
  ok "compound result metadata selects collated set execution while IN uses its own bound operand"
else
  fail "compound declaration selection, IN operand binding or ordinary-query contract is disconnected"
fi

if rg -F -q 'CoreSourceSQL.retain next name (materializationSQL schema definitions)' "$audit_sources/SQLeanite/CoreDerivedSQL.lean" &&
   rg -F -q 'CoreSQL.baseResultCollations state { query with valueRows := none, compounds := #[] }' "$audit_sources/SQLeanite/CoreDerivedSQL.lean" &&
   rg -F -q 'executeWithSources compile true (kind == .exists)' SQLeanite/CoreScalarQuery.lean &&
   rg -F -q 'prepareWithSources parents mode fuel state bindings query' "$audit_sources/SQLeanite/CoreDerivedSQL.lean" &&
   rg -F -q 'let (seen, fresh) := enqueueCollated all kinds seen' "$audit_sources/SQLeanite/CoreDerivedSQL.lean" &&
   rg -F -q 'originalOperands := some (left,right)' "$audit_sources/SQLeanite/CoreSQL.lean" &&
   rg -F -q 'let kind ← SQLite.ExprCollation.require key.collation?' "$audit_sources/SQLeanite/CoreSQL.lean" &&
   rg -F -q 'matchStatement body false' "$audit_sources/SQLeanite/CoreTokenGrammar.lean" &&
   rg -F -q 'CoreDerivedSQL.enqueueCollated_duplicate' "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   rg -F -q 'CoreSQL.JoinSearchKey.collation_original' "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   rg -F -q 'Derived and CTE declarations preserve scopes, collation and private state' "$audit_sources/Tests.lean"; then
  ok "derived declarations, phase-separated scalar sources, recursive keys and original JOIN collation reach public Core execution"
else
  fail "derived metadata retention, scalar source phases, recursive queue or JOIN comparison provenance is disconnected"
fi

if rg -F -q 'CoreViewSQL.load { database := database, headers } header.schemaCookie.val records' SQLeanite/CoreFileEngine.lean &&
   rg -F -q 'CoreViewSQL.load { database := opened.1, headers := { main := opened.2 } } version records' SQLeanite/CoreWALFileEngine.lean &&
   rg -F -q 'CoreViewSQL.uses select.compoundHeight state select' SQLeanite/CoreFileEngine.lean &&
   rg -F -q 'CoreViewSQL.uses select.compoundHeight state select' SQLeanite/CoreWALFileEngine.lean &&
   rg -F -q 'CoreViewSQL.guard state sql' "$audit_sources/SQLeanite/CoreDerivedSQL.lean" &&
   rg -F -q 'CoreViewRename.execute state next sql source' "$audit_sources/SQLeanite/CoreDerivedSQL.lean" &&
   rg -F -q 'CoreTokenGrammar.references parsed.tokens parsed.statements' SQLeanite/CoreViewRename.lean &&
   rg -F -q 'CoreCatalogData.view text' SQLeanite/CoreViewRename.lean &&
   rg -F -q 'matchViewSelect query' "$audit_sources/SQLeanite/CoreTokenGrammar.lean" &&
   rg -F -q 'CoreViewSQL.orderDatabase next' "$audit_sources/SQLeanite/CoreDerivedSQL.lean" &&
   rg -F -q 'CoreCatalogImage.attachObjects checked objects' "$audit_sources/SQLeanite/CoreFileAdapter.lean" &&
   rg -F -q 'CoreFileAdapter.convertCatalogPageSize' SQLeanite/CoreFileEngine.lean &&
   rg -F -q 'CoreCatalogImage.objectRecordsMatch objects records' SQLeanite/CoreWALFileAdapter.lean &&
   rg -F -q 'catalog := persisted.catalog.acknowledge' SQLeanite/CoreFileEngine.lean &&
   rg -F -q 'catalog := next.catalog.acknowledge' SQLeanite/CoreWALFileEngine.lean &&
   rg -F -q 'CoreCatalogImage.attachObjects_matches' "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   rg -F -q 'CoreViewSQL.orderDatabase_tables_perm' "$audit_sources/SQLeanite/ProofAxioms.lean" &&
   rg -F -q 'Persistent VIEW sources, lexical isolation, ALTER and physical catalog evidence' "$audit_sources/Tests.lean"; then
  ok "persistent VIEW sources retain actual catalog identities, independent physical checks, lexical scopes and source-aware ALTER/publication"
else
  fail "persistent VIEW binding, catalog identity/physical validation, ALTER or public publication path is disconnected"
fi
