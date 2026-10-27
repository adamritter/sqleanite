#!/usr/bin/env python3
"""Regression for the former SQLite/SQLeanite simultaneous-reader corruption.

An idle SQLite connection retains its mapped wal-index while Lean grows the
database. Independent readers must see the committed result before and after
the observer closes. This checks one concrete interleaving, not all schedules.
"""
import argparse
import hashlib
import json
import os
import pathlib
import select
import subprocess
import tempfile

ROOT=pathlib.Path(__file__).resolve().parents[1]


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--lean',type=pathlib.Path,default=ROOT/'.lake/build/bin/sqleanite')
    p.add_argument('--sqlite',default=os.environ.get('SQLITE3_BIN','/usr/bin/sqlite3'))
    p.add_argument('--output',type=pathlib.Path)
    args=p.parse_args()
    with tempfile.TemporaryDirectory(prefix='sqleanite-wal-reader-') as tmp:
        d=pathlib.Path(tmp);db=d/'data.db';q=d/'query.sql'
        def write(sql):
            q.write_text(sql)
            r=subprocess.run([str(args.lean),'--verified-wal-file',str(db),str(q)],text=True,capture_output=True,timeout=180)
            assert r.returncode==0,r.stderr
        def read():
            r=subprocess.run([args.sqlite,'-readonly',str(db),'SELECT count(*),sum(length(p)) FROM t; PRAGMA integrity_check;'],text=True,capture_output=True,timeout=180)
            return dict(code=r.returncode,stdout=r.stdout,stderr=r.stderr)
        write('CREATE TABLE t(id INTEGER PRIMARY KEY,p BLOB);BEGIN;'+''.join(f"INSERT INTO t VALUES({i},'x');" for i in range(1,201))+'COMMIT;')
        observer=subprocess.Popen([args.sqlite,'-batch','-readonly','-cmd',
            'SELECT count(*),sum(length(p)) FROM t;',str(db)],stdin=subprocess.PIPE,
            stdout=subprocess.PIPE,stderr=subprocess.PIPE,text=True,bufsize=1)
        try:
            assert select.select([observer.stdout],[],[],10)[0], 'observer did not become ready'
            before=observer.stdout.readline().strip()
            assert before=='200|200',before
            write('UPDATE t SET p=zeroblob(700);')
            with_open_observer=read()
        finally:
            observer.stdin.close()
            observer.wait(timeout=10)
        after_close=read()
    digest=hashlib.sha256()
    for path in sorted((ROOT/'SQLeanite').rglob('*.lean'))+[ROOT/'Main.lean']:
        digest.update(str(path.relative_to(ROOT)).encode()+b'\0'+path.read_bytes())
    expected='200|140000\nok\n'
    report=dict(purpose=__doc__.strip(),before=before,expected_after=expected,
        with_open_observer=with_open_observer,after_observer_closed=after_close,
        matches_with_observer=with_open_observer['code']==0 and with_open_observer['stdout']==expected,
        matches_after_close=after_close['code']==0 and after_close['stdout']==expected,
        observer_sqlite_version=subprocess.check_output([args.sqlite,'--version'],text=True).strip(),
        oracle_sqlite_version=subprocess.check_output([args.sqlite,'--version'],text=True).strip(),
        implementation_sha256=digest.hexdigest(),harness_sha256=hashlib.sha256(pathlib.Path(__file__).read_bytes()).hexdigest(),
        status='Concrete idle-observer regression; broader live schedules are tested separately.')
    report['cases']=[dict(observer='open',matches=report['matches_with_observer']),dict(observer='closed',matches=report['matches_after_close'])]
    report['failures']=sum(not case['matches'] for case in report['cases'])
    if args.output: args.output.write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2))
    return bool(report['failures'])


if __name__=='__main__': raise SystemExit(main())
