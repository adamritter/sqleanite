#!/usr/bin/env python3
"""ALTER ADD COLUMN validates retained CHECK programs against existing rows."""
import os
import random
import re
import subprocess
import sqlite3
import tempfile
from pathlib import Path
import unittest
from test_pragma_tables import SQLITE, BINARY

class CheckAddColumn(unittest.TestCase):
    pass

def observe(path):
    def query(sql):
        result = subprocess.run([SQLITE, str(path), sql], text=True, capture_output=True, timeout=30)
        return result.returncode, result.stdout, result.stderr
    catalog = query("SELECT type,hex(name),hex(tbl_name),hex(sql) FROM sqlite_schema ORDER BY type,name;")
    names = query("SELECT hex(name) FROM sqlite_schema WHERE type='table' ORDER BY name;")
    rows = []
    for raw in names[1].splitlines():
        name = bytes.fromhex(raw).decode()
        quoted = '"' + name.replace('"', '""') + '"'
        rows.append((name, query('SELECT rowid,* FROM ' + quoted + ' ORDER BY rowid;')))
    # An existing CHECK program can itself raise an evaluator error. Keep that
    # diagnostic and return code as observed data, alongside catalog and rows.
    return catalog, names, query('PRAGMA integrity_check;'), rows


def statement_lines(sql):
    # The sqlite3 shell with -bail still executes later statements on the same
    # input line after an ALTER runtime error. Separate complete statements so
    # both drivers stop at the first failing SQL statement. Preserve all SQL.
    chunks = []
    current = ''
    for char in sql:
        current += char
        if char == ';' and sqlite3.complete_statement(current):
            chunks.append(current)
            current = ''
    if current:
        chunks.append(current)
    return '\n'.join(chunks) + '\n'


def case(sql, mode, setup):
    def test(self):
        with tempfile.TemporaryDirectory(prefix='sqleanite-check-add-') as directory:
            left = Path(directory) / 'lean.db'
            right = Path(directory) / 'sqlite.db'
            for path in (left, right):
                subprocess.run([SQLITE, str(path)], input=setup, text=True, check=True, capture_output=True)
            lean = subprocess.run([str(BINARY), mode, str(left)], input=statement_lines(sql), text=True, capture_output=True, timeout=30)
            reference = subprocess.run([SQLITE, '-batch', '-bail', str(right)], input=statement_lines(sql), text=True, capture_output=True, timeout=30)
            self.assertEqual(lean.returncode, reference.returncode, lean.stderr + ' / ' + reference.stderr)
            self.assertEqual(lean.stdout, reference.stdout, lean.stderr)
            if reference.returncode:
                def error(result):
                    line = result.stderr.splitlines()[0] if result.stderr else ''
                    return re.sub(r'^(?:Parse error|Runtime error|Error)(?: near line [0-9]+)?: ?', '', line)
                self.assertEqual(error(lean), error(reference))
            self.assertEqual(observe(left), observe(right))
    return test


SETUP = 'CREATE TABLE t(id INTEGER PRIMARY KEY,x INTEGER);INSERT INTO t VALUES(1,2),(2,4);'
QUERIES = {
    'valid': 'ALTER TABLE t ADD COLUMN y INTEGER DEFAULT 1 CHECK(y>0);SELECT * FROM t;INSERT INTO t VALUES(3,6,0);',
    'invalid': 'ALTER TABLE t ADD COLUMN y INTEGER DEFAULT 0 CHECK(y>0);',
    'null': 'ALTER TABLE t ADD COLUMN y CHECK(y>0);SELECT * FROM t;',
    'named': 'ALTER TABLE t ADD COLUMN y DEFAULT 0 CONSTRAINT positive CHECK(y>0);',
    'old_column_pass': 'ALTER TABLE t ADD COLUMN y DEFAULT 1 CHECK(x>0);SELECT * FROM t;',
    'old_column_fail': 'ALTER TABLE t ADD COLUMN y DEFAULT 1 CHECK(x<3);',
    'cross_column': 'ALTER TABLE t ADD COLUMN y DEFAULT 1 CHECK(x>y);SELECT * FROM t;',
    'cross_column_fail': 'ALTER TABLE t ADD COLUMN y DEFAULT 3 CHECK(x>y);',
    'multiple_first': 'ALTER TABLE t ADD COLUMN y DEFAULT 2 CHECK(y>2) CHECK(y<4);',
    'multiple_last': 'ALTER TABLE t ADD COLUMN y DEFAULT 4 CHECK(y>2) CHECK(y<4);',
    'unknown_column': 'ALTER TABLE t ADD COLUMN y CHECK(missing>0);',
    'subquery': 'ALTER TABLE t ADD COLUMN y CHECK((SELECT 1));',
    'aggregate': 'ALTER TABLE t ADD COLUMN y CHECK(sum(x)>0);',
    'unknown_function': 'ALTER TABLE t ADD COLUMN y CHECK(absent(y)>0);',
    'runtime': 'ALTER TABLE t ADD COLUMN y CHECK(abs(-9223372036854775808));',
    'lazy': 'ALTER TABLE t ADD COLUMN y CHECK(CASE WHEN x>0 THEN 1 ELSE abs(-9223372036854775808) END);SELECT * FROM t;',
    'folded': 'ALTER TABLE t ADD COLUMN y CHECK(0 AND missing);',
    'rowid': 'ALTER TABLE t ADD COLUMN y CHECK(rowid>0);SELECT * FROM t;',
    'affinity': "ALTER TABLE t ADD COLUMN y INTEGER DEFAULT '03' CHECK(typeof(y)='integer' AND y=3);SELECT y,typeof(y) FROM t;",
    'rollback': 'BEGIN;ALTER TABLE t ADD COLUMN y DEFAULT 1 CHECK(y>0);ROLLBACK;SELECT * FROM t;',
    'savepoint': 'SAVEPOINT s;ALTER TABLE t ADD COLUMN y DEFAULT 0 CHECK(y>0);',
    'duplicate': 'ALTER TABLE t ADD COLUMN x CHECK(missing);',
}
for name, sql in QUERIES.items():
    for suffix, mode in [('rollback', '--verified-file'), ('wal', '--verified-wal-file')]:
        setattr(CheckAddColumn, 'test_' + name + '_' + suffix, case(sql, mode, SETUP))
EXTRA = {
    'empty_unknown_function': ('CREATE TABLE t(x);', 'ALTER TABLE t ADD y CHECK(absent(y));'),
    'unknown_function_case': ('CREATE TABLE t(x);INSERT INTO t VALUES(1);', 'ALTER TABLE t ADD y CHECK(AbSeNt(y));'),
    'unknown_function_column': ('CREATE TABLE t(x);INSERT INTO t VALUES(1);', 'ALTER TABLE t ADD y CHECK(absent(missing));'),
    'arity': ('CREATE TABLE t(x);INSERT INTO t VALUES(1);', 'ALTER TABLE t ADD y CHECK(abs(1,2));'),
    'empty_arity': ('CREATE TABLE t(x);', 'ALTER TABLE t ADD y CHECK(abs(1,2));'),
    'old_violation_new_true': ('CREATE TABLE t(x CHECK(x>0));PRAGMA ignore_check_constraints=ON;INSERT INTO t VALUES(-1);', 'ALTER TABLE t ADD y CHECK(1);'),
    'old_named_violation': ('CREATE TABLE t(x CONSTRAINT old_positive CHECK(x>0));PRAGMA ignore_check_constraints=ON;INSERT INTO t VALUES(-1);', 'ALTER TABLE t ADD y CHECK(1);'),
    'no_new_check_runtime': ('CREATE TABLE t(x CHECK(abs(x)));PRAGMA ignore_check_constraints=ON;INSERT INTO t VALUES(-9223372036854775808);', 'ALTER TABLE t ADD y DEFAULT 1;'),
    'quoted_name': ('CREATE TABLE "odd table"("X X");INSERT INTO "odd table" VALUES(1);', 'ALTER TABLE "odd table" ADD "Y Y" DEFAULT 2 CHECK("Y Y">"X X");SELECT * FROM "odd table";'),
    'semicolon_default': ('CREATE TABLE t(x);INSERT INTO t VALUES(1);', "ALTER TABLE t ADD y TEXT DEFAULT ';' CHECK(length(y)=1);SELECT y FROM t;"),
    'line_comment': ('CREATE TABLE t(x);INSERT INTO t VALUES(1);', 'ALTER TABLE t ADD y DEFAULT 2 -- retained default comment\n CHECK(y>x);SELECT * FROM t;'),
    'repeated_default': ('CREATE TABLE t(x);INSERT INTO t VALUES(1);', 'ALTER TABLE t ADD y DEFAULT 9 DEFAULT 2 CHECK(y=2);SELECT * FROM t;'),
    'text_affinity': ('CREATE TABLE t(x);INSERT INTO t VALUES(1);', "ALTER TABLE t ADD y TEXT DEFAULT 2 CHECK(typeof(y)='text');SELECT y,typeof(y) FROM t;"),
    'collation': ('CREATE TABLE t(x);INSERT INTO t VALUES(1);', "ALTER TABLE t ADD y DEFAULT 'A' CHECK(y COLLATE NOCASE='a');SELECT y FROM t;"),
    'empty_false': ('CREATE TABLE t(x);', 'ALTER TABLE t ADD y DEFAULT 0 CHECK(y>0);SELECT * FROM t;INSERT INTO t(x) VALUES(1);'),
    'empty_runtime': ('CREATE TABLE t(x);', 'ALTER TABLE t ADD y CHECK(abs(-9223372036854775808));SELECT * FROM t;'),
    'empty_name': ('CREATE TABLE t(x);', 'ALTER TABLE t ADD y CHECK(missing);'),
    'hidden_rowid': ('CREATE TABLE t(x);INSERT INTO t(rowid,x) VALUES(4,1);', 'ALTER TABLE t ADD y CHECK(rowid=4);SELECT rowid,* FROM t;'),
    'negative_rowid': ('CREATE TABLE t(x);INSERT INTO t(rowid,x) VALUES(-1,1);', 'ALTER TABLE t ADD y CHECK(rowid>0);'),
    'old_bad_plain': ('CREATE TABLE t(x CHECK(x>0));PRAGMA ignore_check_constraints=ON;INSERT INTO t VALUES(-1);', 'ALTER TABLE t ADD y;'),
    'old_bad_new_check': ('CREATE TABLE t(x CHECK(x>0));PRAGMA ignore_check_constraints=ON;INSERT INTO t VALUES(-1);', 'ALTER TABLE t ADD y CHECK(y IS NULL);'),
    'old_bad_default': ('CREATE TABLE t(x CHECK(x>0));PRAGMA ignore_check_constraints=ON;INSERT INTO t VALUES(-1);', 'ALTER TABLE t ADD y DEFAULT 9;'),
    'old_valid': ('CREATE TABLE t(x CHECK(x>0));INSERT INTO t VALUES(1);', 'ALTER TABLE t ADD y CHECK(y IS NULL);SELECT * FROM t;INSERT INTO t VALUES(-1,NULL);'),
    'old_runtime': ('CREATE TABLE t(x CHECK(abs(x)));PRAGMA ignore_check_constraints=ON;INSERT INTO t VALUES(-9223372036854775808);', 'ALTER TABLE t ADD y;'),
    'old_folded': ('CREATE TABLE t(x CHECK(0 AND x));PRAGMA ignore_check_constraints=ON;INSERT INTO t VALUES(0);', 'ALTER TABLE t ADD y;'),
    'old_index': ('CREATE TABLE t(x UNIQUE CHECK(x>0));INSERT INTO t VALUES(1);', 'ALTER TABLE t ADD y DEFAULT 2 CHECK(x<y);SELECT * FROM t;'),
}
for name, (setup, sql) in EXTRA.items():
    for suffix, mode in [('rollback', '--verified-file'), ('wal', '--verified-wal-file')]:
        setattr(CheckAddColumn, 'test_' + name + '_' + suffix, case(sql, mode, setup))
rng = random.Random(int(os.environ.get('SQLEANITE_CHECK_ADD_SEED', '365501')))
for i in range(12):
    values = [rng.randrange(-20, 20) for _ in range(rng.randrange(1, 10))]
    default = rng.randrange(-20, 20)
    setup = 'CREATE TABLE t(x INTEGER);INSERT INTO t VALUES' + ','.join(f'({v})' for v in values) + ';'
    sql = f'ALTER TABLE t ADD y INTEGER DEFAULT {default} CHECK(y<=x);SELECT * FROM t;'
    for suffix, mode in [('rollback', '--verified-file'), ('wal', '--verified-wal-file')]:
        setattr(CheckAddColumn, f'test_fresh_{i}_{suffix}', case(sql, mode, setup))
if __name__ == '__main__':
    unittest.main()
