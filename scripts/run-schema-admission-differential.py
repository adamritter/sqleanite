#!/usr/bin/env python3
"""Check ordinary table/index creation names and IF NOT EXISTS with SQLite.

Every case starts independently using implicit-rowid tables. Compare acceptance and complete table/index
catalog identity plus independent SQLite integrity. Errors and no-ops preserve
the original main/WAL bytes. Table constraints and qualified schema names are
outside this focused corpus and are not inferred to be compatible.
"""
import argparse
import contextlib
import hashlib
import json
import os
import pathlib
import random
import shutil
import sqlite3
import subprocess
import tempfile

ROOT=pathlib.Path(__file__).resolve().parents[1]


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--lean',type=pathlib.Path,default=ROOT/'.lake/build/bin/sqleanite')
    p.add_argument('--sqlite',default=os.environ.get('SQLITE3_BIN','/usr/bin/sqlite3'))
    p.add_argument('--seed',type=int,default=353610)
    p.add_argument('--random-cases',type=int,default=80)
    p.add_argument('--output',type=pathlib.Path)
    args=p.parse_args();rng=random.Random(args.seed);failures=[];phases=[]
    setup="CREATE TABLE t(id INTEGER,v);INSERT INTO t VALUES(1,'a');CREATE INDEX ix ON t(v);CREATE TABLE other(id INTEGER,v);CREATE TABLE shadow(rowid,oid,_rowid_);"
    queries=[
        'CREATE TABLE IF NOT EXISTS t(v);','CREATE TABLE t(v);',
        'CREATE TABLE IF NOT EXISTS ix(v);','CREATE TABLE ix(v);',
        'CREATE INDEX t ON t(v);','CREATE INDEX IF NOT EXISTS t ON t(v);',
        'CREATE INDEX ix ON other(v);','CREATE INDEX IF NOT EXISTS ix ON other(v);',
        'CREATE UNIQUE INDEX IF NOT EXISTS ix ON t(missing);',
        'CREATE INDEX IF NOT EXISTS ix ON missing(v);',
        'CREATE INDEX IF NOT EXISTS ix ON t(unknown_function(v));',
        'CREATE INDEX IF NOT EXISTS ix ON t(v) WHERE missing;',
        'CREATE INDEX ir ON t(rowid);','CREATE INDEX ir ON t(oid);','CREATE INDEX ir ON t(_rowid_);',
        'CREATE INDEX iq ON t(t.v);','CREATE INDEX iq ON t(wrong.v);',
        'CREATE INDEX ir ON shadow(rowid);','CREATE UNIQUE INDEX ir ON shadow(oid);',
        'CREATE TABLE sqlite_x(a);','CREATE TABLE IF NOT EXISTS sqlite_x(a);',
        'CREATE INDEX sqlite_x ON t(v);','CREATE INDEX IF NOT EXISTS sqlite_x ON t(v);',
        'CREATE TABLE fresh(a);','CREATE UNIQUE INDEX fresh ON other(v);',
        'BEGIN;CREATE TABLE IF NOT EXISTS t(v);ROLLBACK;']
    for _ in range(args.random_cases):
        name=rng.choice(['t','other','ix','fresh'+str(rng.randrange(99)),'sqlite_'+str(rng.randrange(99))])
        optional=rng.choice(['','IF NOT EXISTS '])
        if rng.randrange(2):queries.append(f'CREATE TABLE {optional}{name}(v INTEGER);')
        else:
            table=rng.choice(['t','other','missing','shadow']);column=rng.choice(['v','rowid','id','missing'])
            unique=rng.choice(['','UNIQUE ']);queries.append(f'CREATE {unique}INDEX {optional}{name} ON {table}({column});')
    with tempfile.TemporaryDirectory(prefix='sqleanite-schema-') as tmp:
        for mode in ['--verified-file','--verified-wal-file']:
            d=pathlib.Path(tmp)/mode;d.mkdir()
            def sqlite(db,sql):return subprocess.run([args.sqlite,'-batch','-bail',str(db)],input=sql,text=True,capture_output=True,timeout=120)
            def lean(db,sql):
                q=d/'query.sql';q.write_text(sql)
                return subprocess.run([str(args.lean),mode,str(db),str(q)],text=True,capture_output=True,timeout=120)
            def copy(source,target):
                shutil.copyfile(source,target)
                if pathlib.Path(str(source)+'-wal').exists():shutil.copyfile(str(source)+'-wal',str(target)+'-wal')
            def observe(db):
                with contextlib.closing(sqlite3.connect(db)) as c:
                    assert c.execute('PRAGMA integrity_check').fetchall()==[('ok',)]
                    # SQL spelling is canonicalized by Lean; compare object identity and metadata.
                    objects=c.execute("SELECT type,name,tbl_name FROM sqlite_schema ORDER BY type,name").fetchall()
                    details={name:c.execute('PRAGMA table_info("'+name.replace('"','""')+'")').fetchall() for kind,name,_ in objects if kind=='table'}
                    indexes={name:sorted([r[1:] for r in c.execute('PRAGMA index_list("'+name.replace('"','""')+'")')]) for kind,name,_ in objects if kind=='table'}
                    return dict(objects=objects,columns=details,indexes=indexes)
            a_base=d/'a.db';b_base=d/'b.db';a=lean(a_base,setup);b=sqlite(b_base,setup);assert a.returncode==b.returncode==0,(a.stderr,b.stderr)
            matching_errors=0;noops=0;passed=0
            for i,sql in enumerate(queries):
                case=d/str(i);case.mkdir();a_db=case/'a.db';b_db=case/'b.db';copy(a_base,a_db);copy(b_base,b_db)
                files=[a_db,pathlib.Path(str(a_db)+'-wal')];before={str(f):f.read_bytes() for f in files if f.exists()};old=observe(b_db)
                a=lean(a_db,sql);b=sqlite(b_db,sql)
                if (a.returncode==0)!=(b.returncode==0):
                    failures.append(dict(mode=mode,sql=sql,kind='acceptance',lean=dict(code=a.returncode,stderr=a.stderr),sqlite=dict(code=b.returncode,stderr=b.stderr)));continue
                if a.returncode:matching_errors+=1
                inspector=case/'inspect.db';copy(a_db,inspector)
                try:actual=observe(inspector);expected=observe(b_db)
                except sqlite3.DatabaseError as e:failures.append(dict(mode=mode,sql=sql,kind='SQLite reader',error=str(e)));continue
                if actual!=expected:
                    failures.append(dict(mode=mode,sql=sql,kind='schema',lean=actual,sqlite=expected));continue
                if a.returncode or expected['objects']==old['objects']:
                    after={str(f):f.read_bytes() for f in files if f.exists()}
                    if before!=after:failures.append(dict(mode=mode,sql=sql,kind='error/no-op changed image'));continue
                    if not a.returncode:noops+=1
                passed+=1
            phases.append(dict(mode=mode,cases=len(queries),passed=passed,matching_errors=matching_errors,noops=noops))
    digest=hashlib.sha256()
    for path in sorted((ROOT/'SQLeanite').rglob('*.lean'))+[ROOT/'Main.lean']:
        digest.update(str(path.relative_to(ROOT)).encode()+b'\0'+path.read_bytes())
    report=dict(seed=args.seed,random_cases=args.random_cases,phases=phases,failures=failures,
        implementation_sha256=digest.hexdigest(),executable_sha256=hashlib.sha256(args.lean.read_bytes()).hexdigest(),
        harness_sha256=hashlib.sha256(pathlib.Path(__file__).read_bytes()).hexdigest(),
        sqlite_version=subprocess.check_output([args.sqlite,'--version'],text=True).strip(),comparison=__doc__.strip())
    if args.output:args.output.write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2));return bool(failures)


if __name__=='__main__':raise SystemExit(main())
