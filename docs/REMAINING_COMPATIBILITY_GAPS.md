# Remaining SQLite compatibility regressions — 2026-10-30

**246 named probes, 460 test cases: 331 failures and 129 passes.** Failures occur in 178 named probes. These are not 178 proven independent bugs, and the survey does not establish that every possible incompatibility has been found.

Reference: SQLite 3.53.4, source ID `bf7c7f30031888f4e796e429ab3978879485813aaca6f641c7b33e4e09459bcc`. Production code is unchanged from the WITHOUT ROWID reseek checkpoint.

The [machine-readable inventory](validation/sqlite-remaining-gaps-20261030.json) links compressed complete SQL, raw outputs/errors, independent persisted snapshots, build/audit receipts and both final seed runs. The final seeds are 2026103097 and 2026103099; both produce the same status for every named case.

## Run

Requires the built public and test executables and the pinned SQLite shell in `SQLITE3_BIN`. Python uses only its standard library. Its `sqlite3` import only splits complete statements; it is not the reference database engine.

```sh
python3 scripts/run-remaining-compatibility-gaps.py --seed 2026103097 --output /tmp/remaining.json
SQLEANITE_REMAINING_SEED=2026103097 python3 scripts/test_remaining_compatibility_gaps.py
python3 scripts/test_remaining_compatibility_gaps.py RemainingGaps.test_upsert_trigger_wal
python3 scripts/test_remaining_compatibility_gaps.py RemainingGaps.test_effects_insert_fail_transaction_api
```

The full test command intentionally exits 1 while these differences remain: 460 tests, 331 failures, zero skips/expected failures. Each named test runs only its own fixture. The report runner also exits 1 for differences and exits 2 for invalid reference probes. Its four-worker final surveys took approximately 3.6 seconds; sequential unittest took 12.3 seconds. These are local observations, not portable performance guarantees.

## What is compared

428 public file tests use independent copies of native-created databases, 214 per file mode. Every case compares exit status, exact stdout bytes, normalized diagnostic prefix, native-reopened catalog SQL, typed rows including observable rowids, table metadata, selected header settings, reserved bytes and integrity. Persisted snapshots compare row multisets; query output order is never normalized.

32 separate tests use the continuing Core API and a non-bailing native connection. They compare every output and error after FAIL/ROLLBACK/RAISE, transaction/savepoint boundaries, counters and visible rows. They are API tests, not disk durability tests.

WAL fixtures retain a native connection while copying committed, uncheckpointed main/WAL files. The actual WAL bytes/hash are recorded before either engine opens the copy. Dedicated WAL mode passes UTF-8 rowid/WITHOUT ROWID read/write probes; UTF-16 writes and UTF-16 WITHOUT ROWID reads still fail. Rollback-mode probes against WAL fixtures are listed separately.

## Findings

- **Silent SQL difference:** UPSERT DO UPDATE skips an AFTER UPDATE trigger, leaving its log empty. Both public file modes and the continuing API reproduce it.
- **Captured WITHOUT ROWID trigger bodies:** UPDATE/DELETE using scalar subqueries fail on a private `__sqleanite_rowid` lookup.
- **Schema/write gaps:** descending keys, virtual generated columns, declaration conflict policies, ALTER with retained indexes/triggers, compound/partial/expression/collated UPSERT, INSTEAD OF/temp triggers, composite/cascading/deferred foreign keys.
- **Query gaps:** three-table joins, declared-collation USING, aggregate/subquery combinations, named/RANGE/GROUPS/EXCLUDE windows, NTILE/NTH_VALUE, recursive queue ordering/limits, CTE-prefixed DML, row values, UPDATE FROM, index hints and correlated JSON table functions.
- **File/session gaps:** UTF-16 writes and WITHOUT ROWID acquisition, reserved-byte writes, PRAGMA/session commands, VACUUM/ANALYZE/REINDEX/ATTACH. Writes silently change selected input page sizes and auto-vacuum settings.
- **Connection effects:** FAIL/ROLLBACK/RAISE continuation, query_only enforcement, UPSERT update failure and deferred commit behavior.
- Passing controls remain in the suite: RIGHT/FULL/NATURAL JOIN, several aggregates and scalar functions, ordinary UTF-16 reads, baseline ABORT/IGNORE/REPLACE continuation and successful UTF-8 WAL acquisition.

## Validation and limits

Full build, all 414 existing Lean test groups, proof audit, live-path audit and module-boundary check pass. No production Lean source, native shim or existing test was changed. New failing cases are maintained Python unittest regressions exercising public executables, not new Lean proof claims.

The earlier discovery reports are retained, including six invalid probe/mode pairs. SOUNDEX and FTS5 are absent from the pinned reference and therefore not counted as port failures. The accidental UNIQUE update collision was corrected before final evaluation.

- This is a finite source-guided survey, not enumeration of all SQL programs or proof that all incompatibilities are found.
- Planner/cost/EXPLAIN equivalence and unspecified SELECT row order are not comprehensively tested; actual query stdout is compared verbatim.
- Arbitrary malformed pages, all WAL/SHM locking schedules, concurrent mixed-engine connections, power loss and every-syscall crash recovery are not exhaustively covered.
- Optional extensions absent from the pinned reference (SOUNDEX and FTS5) are excluded; RTREE is probed because this reference supports it.
- Date/time now tests check availability/type rather than equal wall-clock timestamps. Localtime/utc use the same inherited environment.
- Failure counts count probe/mode pairs, not independent defects; several share one missing parser/execution capability.
- The rollback reader is also deliberately tested against uncheckpointed WAL pairs. Those are separately named cross-mode admission failures, not failures of the dedicated WAL reader.
- Unchanged historical compatibility documents can contain stale unsupported labels; this report and exact checkpoint supersede them only for the named cases.

## Complete named inventory

`R` = rollback public file mode; `W` = WAL public file mode; `A` = continuing API. A dash means the mode does not apply. A pass covers this example only.

| Area / probe | R | W | A | Observed differences |
|---|---|---|---|---|
| effects / `effects_deferred_commit_failure` | — | — | fail | sql_errors, sql_output |
| effects / `effects_foreign_key_check` | — | — | pass | — |
| effects / `effects_insert_abort_autocommit` | — | — | pass | — |
| effects / `effects_insert_abort_savepoint` | — | — | pass | — |
| effects / `effects_insert_abort_transaction` | — | — | pass | — |
| effects / `effects_insert_fail_autocommit` | — | — | fail | sql_errors, sql_output |
| effects / `effects_insert_fail_savepoint` | — | — | fail | sql_errors, sql_output |
| effects / `effects_insert_fail_transaction` | — | — | fail | sql_errors, sql_output |
| effects / `effects_insert_ignore_autocommit` | — | — | pass | — |
| effects / `effects_insert_ignore_savepoint` | — | — | pass | — |
| effects / `effects_insert_ignore_transaction` | — | — | pass | — |
| effects / `effects_insert_replace_autocommit` | — | — | pass | — |
| effects / `effects_insert_replace_savepoint` | — | — | pass | — |
| effects / `effects_insert_replace_transaction` | — | — | pass | — |
| effects / `effects_insert_rollback_autocommit` | — | — | fail | sql_errors, sql_output |
| effects / `effects_insert_rollback_savepoint` | — | — | fail | sql_errors, sql_output |
| effects / `effects_insert_rollback_transaction` | — | — | fail | sql_errors, sql_output |
| effects / `effects_query_only` | — | — | fail | sql_errors, sql_output |
| effects / `effects_raise_abort` | — | — | pass | — |
| effects / `effects_raise_fail` | — | — | fail | sql_errors, sql_output |
| effects / `effects_raise_ignore` | — | — | fail | exit_status, sql_errors, sql_output |
| effects / `effects_raise_rollback` | — | — | fail | sql_errors, sql_output |
| effects / `effects_update_abort` | — | — | pass | — |
| effects / `effects_update_fail` | — | — | fail | sql_errors, sql_output |
| effects / `effects_update_ignore` | — | — | pass | — |
| effects / `effects_update_replace` | — | — | pass | — |
| effects / `effects_update_rollback` | — | — | fail | sql_errors, sql_output |
| effects / `effects_upsert_trigger` | — | — | fail | sql_output |
| effects / `effects_upsert_update_abort` | — | — | fail | sql_output |
| effects / `effects_wr_hidden__rowid_` | — | — | pass | — |
| effects / `effects_wr_hidden_oid` | — | — | pass | — |
| effects / `effects_wr_hidden_rowid` | — | — | pass | — |
| extended / `compound_foreign_key_parent` | fail | fail | — | exit_status, persisted_catalog, persisted_names, persisted_tables, sql_error, sql_output |
| extended / `declaration_stored_generated` | pass | pass | — | — |
| extended / `declaration_strict_any` | pass | pass | — | — |
| extended / `declaration_unique_desc` | fail | fail | — | exit_status, persisted_catalog, persisted_names, persisted_reserved_bytes, persisted_tables, sql_error, sql_output |
| extended / `declaration_unique_nocase` | fail | fail | — | exit_status, persisted_catalog, persisted_names, persisted_reserved_bytes, persisted_tables, sql_error, sql_output |
| extended / `index_create_compound_desc` | fail | fail | — | exit_status, persisted_catalog, persisted_tables, sql_error, sql_output |
| extended / `index_create_desc` | fail | fail | — | exit_status, persisted_catalog, persisted_tables, sql_error, sql_output |
| extended / `index_create_expression_desc` | fail | fail | — | exit_status, persisted_catalog, persisted_tables, sql_error, sql_output |
| extended / `index_create_unique_desc` | fail | fail | — | exit_status, persisted_catalog, persisted_tables, sql_error, sql_output |
| extended / `index_open_compound_desc` | fail | fail | — | exit_status, sql_error, sql_output |
| extended / `index_open_desc` | fail | fail | — | exit_status, sql_error, sql_output |
| extended / `index_open_expression_desc` | fail | fail | — | exit_status, sql_error, sql_output |
| extended / `index_open_unique_desc` | fail | fail | — | exit_status, sql_error, sql_output |
| extended / `limit_cte` | fail | fail | — | exit_status, sql_error, sql_output |
| extended / `limit_scalar_subquery` | fail | fail | — | exit_status, sql_error, sql_output |
| extended / `notnull_fail` | fail | fail | — | exit_status, persisted_catalog, persisted_names, persisted_tables, sql_error, sql_output |
| extended / `notnull_rollback` | fail | fail | — | exit_status, persisted_catalog, persisted_names, persisted_tables, sql_error, sql_output |
| extended / `recursive_multiple_arms` | pass | pass | — | — |
| extended / `scalar_current_date` | fail | fail | — | exit_status, sql_error, sql_output |
| extended / `scalar_current_time` | fail | fail | — | exit_status, sql_error, sql_output |
| extended / `scalar_current_timestamp` | fail | fail | — | exit_status, sql_error, sql_output |
| extended / `scalar_datetime_empty` | fail | fail | — | exit_status, sql_error, sql_output |
| extended / `scalar_datetime_localtime` | fail | fail | — | exit_status, sql_error, sql_output |
| extended / `scalar_datetime_now` | fail | fail | — | exit_status, sql_error, sql_output |
| extended / `scalar_datetime_utc` | fail | fail | — | exit_status, sql_error, sql_output |
| extended / `scalar_math_log` | pass | pass | — | — |
| extended / `scalar_math_pow` | pass | pass | — | — |
| extended / `scalar_math_sqrt` | pass | pass | — | — |
| extended / `scalar_math_trig` | pass | pass | — | — |
| extended / `scalar_random_capability` | fail | fail | — | exit_status, sql_error, sql_output |
| extended / `scalar_randomblob_capability` | fail | fail | — | exit_status, sql_error, sql_output |
| extended / `scalar_sqlite_compileoption` | fail | fail | — | exit_status, sql_error, sql_output |
| extended / `scalar_total_null` | pass | pass | — | — |
| extended / `scalar_zeroblob` | pass | pass | — | — |
| extended / `trigger_shadowed_rowids` | fail | fail | — | exit_status, persisted_tables, sql_error, sql_output |
| extended / `view_column_list` | pass | pass | — | — |
| extended / `virtual_rtree` | fail | fail | — | exit_status, persisted_catalog, persisted_names, persisted_tables, sql_error |
| extended / `wr_alter_add` | fail | fail | — | exit_status, persisted_catalog, persisted_tables, sql_error, sql_output |
| extended / `wr_alter_rename` | fail | fail | — | exit_status, persisted_catalog, persisted_tables, sql_error, sql_output |
| extended / `wr_covering_predicate` | pass | pass | — | — |
| extended / `wr_foreign_key_parent` | fail | fail | — | exit_status, persisted_tables, sql_error, sql_output |
| query / `aggregate_bare_group` | pass | pass | — | — |
| query / `aggregate_bare_max` | pass | pass | — | — |
| query / `aggregate_bare_min` | pass | pass | — | — |
| query / `aggregate_distinct` | pass | pass | — | — |
| query / `aggregate_filter` | pass | pass | — | — |
| query / `aggregate_having_subquery` | fail | fail | — | exit_status, sql_error, sql_output |
| query / `aggregate_order` | pass | pass | — | — |
| query / `aggregate_scalar_subquery` | fail | fail | — | exit_status, sql_error, sql_output |
| query / `blob_cast` | pass | pass | — | — |
| query / `collation_using` | fail | fail | — | exit_status, sql_error, sql_output |
| query / `correlated_compound` | pass | pass | — | — |
| query / `correlated_group` | pass | pass | — | — |
| query / `cte_delete` | fail | fail | — | exit_status, persisted_tables, sql_error, sql_output |
| query / `cte_insert` | fail | fail | — | exit_status, persisted_tables, sql_error, sql_output |
| query / `cte_materialized` | pass | pass | — | — |
| query / `cte_not_materialized` | pass | pass | — | — |
| query / `cte_update` | fail | fail | — | exit_status, persisted_tables, sql_error, sql_output |
| query / `format` | pass | pass | — | — |
| query / `index_hint` | fail | fail | — | exit_status, sql_error, sql_output |
| query / `join_full` | pass | pass | — | — |
| query / `join_natural` | pass | pass | — | — |
| query / `join_right` | pass | pass | — | — |
| query / `join_three` | fail | fail | — | exit_status, sql_error, sql_output |
| query / `json_each_lateral` | fail | fail | — | exit_status, sql_error, sql_output |
| query / `json_error_position` | pass | pass | — | — |
| query / `json_tree_lateral` | fail | fail | — | exit_status, sql_error, sql_output |
| query / `json_valid_flags` | pass | pass | — | — |
| query / `jsonb` | pass | pass | — | — |
| query / `jsonb_extract` | pass | pass | — | — |
| query / `like_escape` | pass | pass | — | — |
| query / `likely` | pass | pass | — | — |
| query / `not_indexed` | fail | fail | — | exit_status, sql_error, sql_output |
| query / `numeric_literals` | pass | pass | — | — |
| query / `octet_length` | pass | pass | — | — |
| query / `recursive_limit` | fail | fail | — | exit_status, sql_error, sql_output |
| query / `recursive_offset` | fail | fail | — | exit_status, sql_error, sql_output |
| query / `recursive_order` | fail | fail | — | exit_status, sql_error, sql_output |
| query / `row_value_equal` | fail | fail | — | exit_status, sql_error, sql_output |
| query / `row_value_in` | fail | fail | — | exit_status, sql_error, sql_output |
| query / `row_value_update` | fail | fail | — | exit_status, persisted_tables, sql_error, sql_output |
| query / `sort_nulls_first` | pass | pass | — | — |
| query / `sort_nulls_last` | pass | pass | — | — |
| query / `sqlite_offset` | fail | fail | — | exit_status, sql_error, sql_output |
| query / `string_concat` | pass | pass | — | — |
| query / `unhex` | pass | pass | — | — |
| query / `unistr` | pass | pass | — | — |
| query / `update_from` | fail | fail | — | exit_status, persisted_tables, sql_error, sql_output |
| query / `window_chained` | fail | fail | — | exit_status, sql_error, sql_output |
| query / `window_exclude_current` | fail | fail | — | exit_status, sql_error, sql_output |
| query / `window_exclude_ties` | fail | fail | — | exit_status, sql_error, sql_output |
| query / `window_filter` | pass | pass | — | — |
| query / `window_grouped` | fail | fail | — | exit_status, sql_error, sql_output |
| query / `window_groups` | fail | fail | — | exit_status, sql_error, sql_output |
| query / `window_join` | fail | fail | — | exit_status, sql_error, sql_output |
| query / `window_named` | fail | fail | — | exit_status, sql_error, sql_output |
| query / `window_nth` | fail | fail | — | exit_status, sql_error, sql_output |
| query / `window_ntile` | fail | fail | — | exit_status, sql_error, sql_output |
| query / `window_range` | fail | fail | — | exit_status, sql_error, sql_output |
| schema / `alter_compound_add` | fail | fail | — | exit_status, persisted_catalog, persisted_tables, sql_error |
| schema / `alter_compound_drop_unreferenced` | fail | fail | — | exit_status, persisted_catalog, persisted_tables, sql_error |
| schema / `alter_compound_rename_column` | fail | fail | — | exit_status, persisted_catalog, persisted_tables, sql_error |
| schema / `alter_compound_rename_table` | fail | fail | — | exit_status, persisted_catalog, persisted_names, persisted_tables, sql_error, sql_output |
| schema / `alter_expression_add` | fail | fail | — | exit_status, persisted_catalog, persisted_tables, sql_error |
| schema / `alter_expression_drop_unreferenced` | fail | fail | — | exit_status, persisted_catalog, persisted_tables, sql_error |
| schema / `alter_expression_rename_column` | fail | fail | — | exit_status, persisted_catalog, persisted_tables, sql_error |
| schema / `alter_expression_rename_table` | fail | fail | — | exit_status, persisted_catalog, persisted_names, persisted_tables, sql_error, sql_output |
| schema / `alter_partial_add` | fail | fail | — | exit_status, persisted_catalog, persisted_tables, sql_error |
| schema / `alter_partial_drop_unreferenced` | fail | fail | — | exit_status, persisted_catalog, persisted_tables, sql_error |
| schema / `alter_partial_rename_column` | fail | fail | — | exit_status, persisted_catalog, persisted_tables, sql_error |
| schema / `alter_partial_rename_table` | fail | fail | — | exit_status, persisted_catalog, persisted_names, persisted_tables, sql_error, sql_output |
| schema / `alter_trigger_add_column` | pass | pass | — | — |
| schema / `alter_trigger_drop_column` | fail | fail | — | exit_status, persisted_catalog, persisted_tables, sql_error, sql_output |
| schema / `alter_trigger_rename_column` | fail | fail | — | exit_status, persisted_catalog, persisted_tables, sql_error, sql_output |
| schema / `alter_trigger_rename_table` | fail | fail | — | exit_status, persisted_catalog, persisted_names, persisted_tables, sql_error, sql_output |
| schema / `alter_unique_add` | fail | fail | — | exit_status, persisted_catalog, persisted_tables, sql_error |
| schema / `alter_unique_drop_unreferenced` | fail | fail | — | exit_status, persisted_catalog, persisted_tables, sql_error |
| schema / `alter_unique_rename_column` | fail | fail | — | exit_status, persisted_catalog, persisted_tables, sql_error |
| schema / `alter_unique_rename_table` | fail | fail | — | exit_status, persisted_catalog, persisted_names, persisted_tables, sql_error, sql_output |
| schema / `ddl_composite_desc` | fail | fail | — | exit_status, persisted_catalog, persisted_names, persisted_reserved_bytes, persisted_tables, sql_error, sql_output |
| schema / `ddl_default_expression` | pass | pass | — | — |
| schema / `ddl_inline_asc_integer` | pass | pass | — | — |
| schema / `ddl_inline_desc_integer` | fail | fail | — | exit_status, persisted_catalog, persisted_names, persisted_reserved_bytes, persisted_tables, sql_error, sql_output |
| schema / `ddl_inline_desc_text` | fail | fail | — | exit_status, persisted_catalog, persisted_names, persisted_reserved_bytes, persisted_tables, sql_error, sql_output |
| schema / `ddl_named_column_constraint` | pass | pass | — | — |
| schema / `ddl_table_desc_text` | fail | fail | — | exit_status, persisted_catalog, persisted_names, persisted_reserved_bytes, persisted_tables, sql_error, sql_output |
| schema / `ddl_virtual_generated` | fail | fail | — | exit_status, persisted_catalog, persisted_names, persisted_reserved_bytes, persisted_tables, sql_error, sql_output |
| schema / `declared_unique_fail` | fail | fail | — | exit_status, persisted_catalog, persisted_names, persisted_reserved_bytes, persisted_tables, sql_error, sql_output |
| schema / `declared_unique_ignore` | fail | fail | — | exit_status, persisted_catalog, persisted_names, persisted_reserved_bytes, persisted_tables, sql_error, sql_output |
| schema / `declared_unique_replace` | fail | fail | — | exit_status, persisted_catalog, persisted_names, persisted_reserved_bytes, persisted_tables, sql_error, sql_output |
| schema / `declared_unique_rollback` | fail | fail | — | exit_status, persisted_catalog, persisted_names, persisted_reserved_bytes, persisted_tables, sql_error, sql_output |
| schema / `fk_cascade` | fail | fail | — | exit_status, persisted_catalog, persisted_names, persisted_tables, sql_error |
| schema / `fk_composite` | fail | fail | — | exit_status, persisted_catalog, persisted_names, persisted_tables, sql_error, sql_output |
| schema / `fk_defer_pragma` | fail | fail | — | exit_status, persisted_tables, sql_error, sql_output |
| schema / `fk_deferred` | fail | fail | — | exit_status, persisted_tables, sql_error, sql_output |
| schema / `fk_no_action` | pass | pass | — | — |
| schema / `fk_restrict` | fail | fail | — | exit_status, persisted_catalog, persisted_names, persisted_tables, sql_error, sql_output |
| schema / `fk_set_default` | fail | fail | — | exit_status, persisted_catalog, persisted_names, persisted_tables, sql_error, sql_output |
| schema / `fk_set_null` | fail | fail | — | exit_status, persisted_catalog, persisted_names, persisted_tables, sql_error, sql_output |
| schema / `insert_or_fail` | fail | fail | — | exit_status, persisted_tables, sql_error, sql_output |
| schema / `insert_or_rollback` | fail | fail | — | exit_status, persisted_tables, sql_error, sql_output |
| schema / `instead_of_insert` | fail | fail | — | exit_status, persisted_tables, sql_error, sql_output |
| schema / `instead_of_update` | fail | fail | — | exit_status, persisted_tables, sql_error, sql_output |
| schema / `recursive_replace_auxiliary` | fail | fail | — | exit_status, persisted_tables, sql_error, sql_output |
| schema / `temp_table` | fail | fail | — | exit_status, sql_error, sql_output |
| schema / `temp_trigger` | fail | fail | — | exit_status, persisted_tables, sql_error, sql_output |
| schema / `temp_view` | fail | fail | — | exit_status, sql_error, sql_output |
| schema / `update_or_fail` | fail | fail | — | exit_status, persisted_tables, sql_error, sql_output |
| schema / `update_or_rollback` | fail | fail | — | exit_status, persisted_tables, sql_error, sql_output |
| schema / `upsert_collated` | fail | fail | — | exit_status, persisted_tables, sql_error, sql_output |
| schema / `upsert_compound` | fail | fail | — | exit_status, persisted_tables, sql_error, sql_output |
| schema / `upsert_expression` | fail | fail | — | exit_status, persisted_tables, sql_error, sql_output |
| schema / `upsert_partial` | fail | fail | — | exit_status, persisted_tables, sql_error, sql_output |
| schema / `upsert_select` | pass | pass | — | — |
| schema / `upsert_trigger` | fail | fail | — | persisted_tables, sql_output |
| schema / `upsert_without_rowid` | fail | fail | — | exit_status, persisted_tables, sql_error, sql_output |
| schema / `wr_captured_trigger_delete` | fail | fail | — | exit_status, persisted_tables, sql_error, sql_output |
| schema / `wr_captured_trigger_update` | fail | fail | — | exit_status, persisted_tables, sql_error, sql_output |
| schema / `wr_primary_fail` | fail | fail | — | exit_status, persisted_catalog, persisted_names, persisted_reserved_bytes, persisted_tables, sql_error, sql_output |
| schema / `wr_primary_ignore` | fail | fail | — | exit_status, persisted_catalog, persisted_names, persisted_reserved_bytes, persisted_tables, sql_error, sql_output |
| schema / `wr_primary_replace` | fail | fail | — | exit_status, persisted_catalog, persisted_names, persisted_reserved_bytes, persisted_tables, sql_error, sql_output |
| schema / `wr_primary_rollback` | fail | fail | — | exit_status, persisted_catalog, persisted_names, persisted_reserved_bytes, persisted_tables, sql_error, sql_output |
| storage / `analyze` | fail | fail | — | exit_status, persisted_catalog, persisted_names, persisted_tables, sql_error, sql_output |
| storage / `attach` | fail | fail | — | exit_status, sql_error, sql_output |
| storage / `auto_vacuum_full` | fail | fail | — | persisted_headers |
| storage / `auto_vacuum_incremental` | fail | fail | — | persisted_headers |
| storage / `geometry_1024` | fail | pass | — | persisted_headers |
| storage / `geometry_512` | fail | pass | — | persisted_headers |
| storage / `geometry_65536` | fail | pass | — | persisted_headers |
| storage / `geometry_8192` | fail | pass | — | persisted_headers |
| storage / `pragma_application_id` | pass | pass | — | — |
| storage / `pragma_auto_vacuum` | fail | fail | — | exit_status, sql_error, sql_output |
| storage / `pragma_collation_list` | fail | fail | — | exit_status, sql_error, sql_output |
| storage / `pragma_database_list` | fail | fail | — | exit_status, sql_error, sql_output |
| storage / `pragma_encoding` | pass | pass | — | — |
| storage / `pragma_foreign_key_list` | pass | pass | — | — |
| storage / `pragma_freelist_count` | fail | fail | — | exit_status, sql_error, sql_output |
| storage / `pragma_function_list` | fail | fail | — | exit_status, sql_error, sql_output |
| storage / `pragma_page_count` | fail | fail | — | exit_status, sql_error, sql_output |
| storage / `pragma_page_size` | fail | fail | — | exit_status, sql_error, sql_output |
| storage / `pragma_query_only` | fail | fail | — | exit_status, sql_error, sql_output |
| storage / `pragma_read_uncommitted` | fail | fail | — | exit_status, sql_error, sql_output |
| storage / `pragma_reverse_unordered` | fail | fail | — | exit_status, sql_error, sql_output |
| storage / `pragma_schema_version` | fail | fail | — | exit_status, sql_error, sql_output |
| storage / `reindex` | fail | fail | — | exit_status, sql_error, sql_output |
| storage / `reserved_bytes_16` | fail | fail | — | exit_status, persisted_tables, sql_error, sql_output |
| storage / `reserved_bytes_32` | fail | fail | — | exit_status, persisted_tables, sql_error, sql_output |
| storage / `utf16be_create` | fail | fail | — | exit_status, persisted_catalog, persisted_headers, persisted_names, persisted_reserved_bytes, persisted_tables, sql_error, sql_output |
| storage / `utf16be_delete` | fail | fail | — | exit_status, persisted_tables, sql_error, sql_output |
| storage / `utf16be_insert` | fail | fail | — | exit_status, persisted_tables, sql_error, sql_output |
| storage / `utf16be_read` | pass | pass | — | — |
| storage / `utf16be_schema` | fail | fail | — | exit_status, persisted_catalog, persisted_tables, sql_error, sql_output |
| storage / `utf16be_update` | fail | fail | — | exit_status, persisted_tables, sql_error, sql_output |
| storage / `utf16be_wr_read` | fail | fail | — | exit_status, sql_error, sql_output |
| storage / `utf16le_create` | fail | fail | — | exit_status, persisted_catalog, persisted_headers, persisted_names, persisted_reserved_bytes, persisted_tables, sql_error, sql_output |
| storage / `utf16le_delete` | fail | fail | — | exit_status, persisted_tables, sql_error, sql_output |
| storage / `utf16le_insert` | fail | fail | — | exit_status, persisted_tables, sql_error, sql_output |
| storage / `utf16le_read` | pass | pass | — | — |
| storage / `utf16le_schema` | fail | fail | — | exit_status, persisted_catalog, persisted_tables, sql_error, sql_output |
| storage / `utf16le_update` | fail | fail | — | exit_status, persisted_tables, sql_error, sql_output |
| storage / `utf16le_wr_read` | fail | fail | — | exit_status, sql_error, sql_output |
| storage / `vacuum` | fail | fail | — | exit_status, sql_error, sql_output |
| storage / `wal_overlay_utf16be_rowid_read` | fail | pass | — | exit_status, sql_error, sql_output |
| storage / `wal_overlay_utf16be_rowid_update` | fail | fail | — | exit_status, persisted_tables, sql_error, sql_output |
| storage / `wal_overlay_utf16be_wr_read` | fail | fail | — | exit_status, sql_error, sql_output |
| storage / `wal_overlay_utf16be_wr_update` | fail | fail | — | exit_status, persisted_tables, sql_error, sql_output |
| storage / `wal_overlay_utf16le_rowid_read` | fail | pass | — | exit_status, sql_error, sql_output |
| storage / `wal_overlay_utf16le_rowid_update` | fail | fail | — | exit_status, persisted_tables, sql_error, sql_output |
| storage / `wal_overlay_utf16le_wr_read` | fail | fail | — | exit_status, sql_error, sql_output |
| storage / `wal_overlay_utf16le_wr_update` | fail | fail | — | exit_status, persisted_tables, sql_error, sql_output |
| storage / `wal_overlay_utf8_rowid_read` | fail | pass | — | exit_status, sql_error, sql_output |
| storage / `wal_overlay_utf8_rowid_update` | fail | pass | — | exit_status, persisted_tables, sql_error, sql_output |
| storage / `wal_overlay_utf8_wr_read` | fail | pass | — | exit_status, sql_error, sql_output |
| storage / `wal_overlay_utf8_wr_update` | fail | pass | — | exit_status, persisted_tables, sql_error, sql_output |
