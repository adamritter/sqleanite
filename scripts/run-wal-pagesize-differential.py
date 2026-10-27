#!/usr/bin/env python3
"""All eight SQLite page sizes with live readers, overflow, indexes and schema trees.

Reference SQLite creates the input and a separate expected database. Every
mutation runs independently in Lean and SQLite; persisted values, index scans,
integrity and original page geometry are compared after each checkpoint.
"""
import argparse, hashlib, importlib.util, json, os, pathlib, random, struct, subprocess, tempfile

ROOT = pathlib.Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location('live_wal', ROOT / 'scripts/run-wal-live-differential.py')
live = importlib.util.module_from_spec(spec)
spec.loader.exec_module(live)

def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--lean', default=str(ROOT / '.lake/build/bin/sqleanite'))
    p.add_argument('--sqlite', default=os.environ['SQLITE3_BIN'])
    p.add_argument('--seed', type=int, default=356201)
    p.add_argument('--fixtures', type=int, default=1)
    p.add_argument('--sizes', type=int, nargs='+', default=[512 << i for i in range(8)])
    p.add_argument('--output', type=pathlib.Path, required=True)
    a = p.parse_args()
    rng = random.Random(a.seed)
    cases, failures = [], []

    def check(name, actual, expected):
        result = dict(name=name, actual=actual, expected=expected, matches=actual == expected)
        cases.append(result)
        if not result['matches']: failures.append(result)

    def lean(db, sql='', checkpoint=False):
        r = subprocess.run([a.lean, '--verified-wal-checkpoint' if checkpoint else '--verified-wal-file', str(db)],
                           input=sql, text=True, capture_output=True, timeout=180)
        return dict(code=r.returncode, stdout=r.stdout, stderr=r.stderr)

    def sha(text): return hashlib.sha256(text.encode()).hexdigest()

    with tempfile.TemporaryDirectory(prefix='sqleanite-wal-pagesize-') as tmp:
        for fixture in range(a.fixtures):
            for size in a.sizes:
                name = f'{fixture}-page{size}'
                db = pathlib.Path(tmp) / (name + '.db')
                ref = pathlib.Path(tmp) / (name + '-reference.db')
                owner, expected = live.SQLite(a.sqlite, db), live.SQLite(a.sqlite, ref)
                observer = None
                try:
                    n = rng.randint(48, 70)
                    ids = [-9223372036854775808, -129, -1, 0] + list(range(1, n)) + [9223372036854775807]
                    rng.shuffle(ids)
                    rows = []
                    for i, key in enumerate(ids):
                        width = [0, 1, size - 35, size - 34, 2 * size + 17, size // 6][i % 6]
                        blob = bytes(rng.randrange(256) for _ in range(width))
                        text = f'{rng.randrange(100000):05}-' + rng.choice(['a', 'Z', 'x']) * (size // 6 + i % 9)
                        rows.append(f"({key},'{text}',x'{blob.hex()}')")
                    # Large schema records force catalog overflow at small sizes.
                    column = 'column_' + 'q' * 700
                    sql = (f'PRAGMA page_size={size};PRAGMA journal_mode=WAL;PRAGMA wal_autocheckpoint=0;'
                           f'PRAGMA application_id={rng.randint(1, 2000000)};PRAGMA user_version={rng.randint(1, 2000000)};'
                           'CREATE TABLE t(id INTEGER PRIMARY KEY,k TEXT,b BLOB);'
                           'CREATE INDEX tk ON t(k);CREATE INDEX tb ON t(b);'
                           'CREATE TABLE names(k TEXT PRIMARY KEY,v);'
                           "INSERT INTO names VALUES('first',17),('second',29);"
                           'CREATE TABLE empty(id INTEGER PRIMARY KEY,v);'
                           f'CREATE TABLE wide(id INTEGER PRIMARY KEY,"{column}" TEXT);'
                           'BEGIN;INSERT INTO t VALUES' + ','.join(rows) + ';' +
                           ''.join(f'CREATE TABLE extra_{i}(id INTEGER PRIMARY KEY,v TEXT);' for i in range(18)) + 'COMMIT;')
                    owner.query(sql, timeout=120)
                    expected.query(sql, timeout=120)
                    observer = live.SQLite(a.sqlite, db, readonly=True)
                    query = 'SELECT id,quote(k),hex(b) FROM t ORDER BY id;'
                    old = observer.query('BEGIN;' + query)
                    check(name + '-initial', sha(old), sha(expected.query(query)))
                    wal, shm = pathlib.Path(str(db) + '-wal'), pathlib.Path(str(db) + '-shm')
                    old_index = shm.read_bytes()
                    frames = struct.unpack_from('=I', old_index, 16)[0]
                    end = 32 + frames * (size + 24)
                    prefix = wal.read_bytes()[:end]
                    inodes = [wal.stat().st_ino, shm.stat().st_ino]
                    mutation = "UPDATE t SET k=k||'-lean',b=b||x'0123456789ABCDEF' WHERE id%3=0;DELETE FROM t WHERE id=2;"
                    result = lean(db, mutation)
                    check(name + '-live-write', result, dict(code=0, stdout='', stderr=''))
                    expected.query(mutation)
                    latest = expected.query(query)
                    check(name + '-reader-snapshot', sha(observer.query(query)), sha(old))
                    check(name + '-prefix-retained', wal.read_bytes()[:end] == prefix, True)
                    check(name + '-inodes-retained', [wal.stat().st_ino, shm.stat().st_ino], inodes)
                    check(name + '-owner-new-data', sha(owner.query(query)), sha(latest))
                    read = lean(db, query)
                    check(name + '-lean-reopen-code', read['code'], 0)
                    check(name + '-lean-reopen-data', sha(read['stdout']), sha(latest))
                    frozen = [db.read_bytes(), wal.read_bytes()]
                    busy = lean(db, checkpoint=True)
                    check(name + '-checkpoint-busy', busy['code'] != 0 and 'database is locked' in busy['stderr'], True)
                    check(name + '-busy-unchanged', [db.read_bytes(), wal.read_bytes()] == frozen, True)
                    check(name + '-release-snapshot', sha(observer.query('COMMIT;' + query)), sha(latest))

                    def compare(stage):
                        queries = {
                            'rows': query,
                            'index-text': 'SELECT id,k FROM t INDEXED BY tk ORDER BY k,id;',
                            'index-blob': 'SELECT id,hex(b) FROM t INDEXED BY tb ORDER BY b,id;',
                            'schema': 'SELECT type,name,tbl_name,sql FROM sqlite_schema ORDER BY name;',
                            'primary': 'SELECT k,v FROM names ORDER BY k;',
                            'empty': 'SELECT * FROM empty;',
                            'metadata': 'PRAGMA application_id;PRAGMA user_version;PRAGMA page_size;',
                            'integrity': 'PRAGMA integrity_check;',
                        }
                        for label, q in queries.items():
                            actual, reference = owner.query(q), expected.query(q)
                            check(name + '-' + stage + '-' + label, actual if label == 'schema' else sha(actual), reference if label == 'schema' else sha(reference))
                        check(name + '-' + stage + '-wal-size', struct.unpack_from('>I', wal.read_bytes(), 8)[0], size)

                    compare('first')
                    cp = lean(db, checkpoint=True)
                    check(name + '-checkpoint-code', cp['code'], 0)
                    field = struct.unpack_from('>H', db.read_bytes(), 16)[0]
                    check(name + '-main-size', 65536 if field == 1 else field, size)
                    compare('checkpoint')
                    # SQLite can reset the WAL; Lean must keep its new header/salts.
                    sql = "INSERT INTO t VALUES(100000,'sqlite-after-checkpoint',x'0102');UPDATE names SET v=31 WHERE k='first';"
                    owner.query(sql); expected.query(sql)
                    sql = ("INSERT INTO t VALUES(100001,'lean-after-restart',x'AA00BB');"
                           'ALTER TABLE extra_1 ADD COLUMN added TEXT;DROP TABLE extra_2;'
                           "INSERT INTO names VALUES('third',41);PRAGMA user_version=123456;")
                    check(name + '-restart-write', lean(db, sql), dict(code=0, stdout='', stderr=''))
                    expected.query(sql)
                    compare('restart')
                    # Empty the table to cover 65536's zero content-offset sentinel.
                    sql = 'DELETE FROM t;'
                    check(name + '-empty-write', lean(db, sql), dict(code=0, stdout='', stderr=''))
                    expected.query(sql)
                    compare('empty')
                    check(name + '-empty-checkpoint', lean(db, checkpoint=True)['code'], 0)
                finally:
                    if observer is not None: observer.close()
                    owner.close(); expected.close()
                r = subprocess.run([a.sqlite, str(db), 'PRAGMA page_size;PRAGMA integrity_check;'], text=True, capture_output=True)
                check(name + '-after-close', dict(code=r.returncode, stdout=r.stdout, stderr=r.stderr),
                      dict(code=0, stdout=f'{size}\nok\n', stderr=''))
                # Last SQLite close removes WAL/SHM. Creating the next WAL
                # must derive its size from the main header, including 65536.
                check(name + '-new-log-write', lean(db, "INSERT INTO empty VALUES(7,'new-log');"),
                      dict(code=0, stdout='', stderr=''))
                check(name + '-new-log-size', struct.unpack_from('>I', pathlib.Path(str(db)+'-wal').read_bytes(), 8)[0], size)
                r = subprocess.run([a.sqlite, str(db), 'SELECT * FROM empty;PRAGMA page_size;PRAGMA integrity_check;'], text=True, capture_output=True)
                check(name + '-new-log-data', dict(code=r.returncode, stdout=r.stdout, stderr=r.stderr),
                      dict(code=0, stdout=f'7|new-log\n{size}\nok\n', stderr=''))
    report = dict(seed=a.seed, fixtures=a.fixtures, page_sizes=a.sizes, cases=cases, failures=failures,
                  executable_sha256=live.digest(pathlib.Path(a.lean)), native_sha256=live.digest(ROOT/'native/sqleanite_vfs.c'),
                  harness_sha256=live.digest(pathlib.Path(__file__)),
                  sqlite_identity=subprocess.check_output([a.sqlite, '--version'], text=True).strip())
    a.output.write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps(dict(cases=len(cases), failures=len(failures), output=str(a.output))), flush=True)
    return bool(failures)

if __name__ == '__main__': raise SystemExit(main())
