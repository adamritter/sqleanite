#!/usr/bin/env python3
"""CREATE INDEX catalog spelling and transaction lifetime, compared with SQLite.

Scope: supported single-column named indexes in WAL mode. The report retains
execution results, exact C-observed catalog text, rows and integrity. It is not
a claim about partial/expression indexes, ALTER rewriting, or the rollback path.
"""
import argparse, hashlib, json, os, pathlib, random, subprocess, tempfile
ROOT=pathlib.Path(__file__).resolve().parents[1]

def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--seed',type=int,required=True)
    p.add_argument('--count',type=int,default=16)
    p.add_argument('--output',type=pathlib.Path,required=True)
    a=p.parse_args();rng=random.Random(a.seed);sqlite=os.environ['SQLITE3_BIN'];exe=ROOT/'.lake/build/bin/sqleanite'
    def run(argv,sql):
        r=subprocess.run(argv,input=sql,text=True,capture_output=True,timeout=30)
        return dict(code=r.returncode,stdout=r.stdout,stderr=r.stderr)
    def c(db,sql):return run([sqlite,'-batch','-bail',str(db)],sql)
    query="SELECT type,hex(name),hex(tbl_name),hex(sql) FROM sqlite_schema ORDER BY type,name;SELECT id,typeof(v),quote(v) FROM t ORDER BY id;PRAGMA integrity_check;"
    cases=[]
    forms=[
        'CREATE INDEX ix ON t(v);',
        'create unique index ix on t ( v );',
        'CrEaTe INDEX IF NOT EXISTS main.ix ON t(v);',
        'CREATE /*one*/ INDEX /*two*/ "ix" /*three*/ ON "t"( "v" );',
        'CREATE UNIQUE INDEX [ix] ON [t]([v]);',
        'CREATE INDEX `ix` ON `t`(`v`);',
        'CREATE INDEX ix ON t(v) /* trailing */ ;',
        'CREATE INDEX ix ON t(v) -- trailing line\n;',
        'CREATE INDEX ix\nON t(\nv\n);',
        'CREATE INDEX ix ON t(v)\n\t  ',
    ]
    with tempfile.TemporaryDirectory(prefix='sqleanite-index-source-') as tmp:
        for i in range(a.count):
            name='index_'+str(rng.randrange(10000000))
            create=forms[i%len(forms)].replace('ix',name)
            alternate=f'CREATE INDEX "{name}" ON "t"( "v" );'
            setup=("PRAGMA journal_mode=WAL;CREATE TABLE t(id INTEGER PRIMARY KEY,v);"
                   f"INSERT INTO t VALUES(1,'a{rng.randrange(1000000)}'),(2,'b{rng.randrange(1000000)}');")
            variants={
                'autocommit':create,
                'transaction':'BEGIN;'+create+'COMMIT;',
                'rollback':'BEGIN;'+create+'ROLLBACK;'+alternate,
                'savepoint':'SAVEPOINT outer_mark;'+create+'SAVEPOINT inner_mark;DROP INDEX '+name+';'+alternate+'ROLLBACK TO inner_mark;RELEASE inner_mark;RELEASE outer_mark;',
                'rollback-savepoint':'BEGIN;SAVEPOINT s;'+create+'ROLLBACK TO s;RELEASE s;COMMIT;'+alternate,
                'same-name-savepoint':'SAVEPOINT s;'+create+'SAVEPOINT s;DROP INDEX '+name+';'+alternate+'ROLLBACK TO s;RELEASE s;RELEASE s;',
                'no-op':create+f'CREATE UNIQUE INDEX IF NOT EXISTS "{name}" ON t(id);',
                'type-change':create+'UPDATE t SET v=id;DELETE FROM t;',
                'recreate':create+'DROP INDEX '+name+';'+alternate,
            }
            for variant,sql in variants.items():
                left=pathlib.Path(tmp)/f'{i}-{variant}-lean.db';right=pathlib.Path(tmp)/f'{i}-{variant}-sqlite.db'
                assert c(left,setup)['code']==0 and c(right,setup)['code']==0
                lean=run([str(exe),'--verified-wal-file',str(left)],sql);reference=c(right,sql)
                actual,expected=c(left,query),c(right,query)
                match=lean['code']==reference['code']==0 and lean['stdout']==reference['stdout'] and actual==expected and actual['code']==0 and actual['stdout'].endswith('ok\n')
                cases.append(dict(name=f'{i}-{variant}',setup=setup,sql=sql,lean=lean,sqlite=reference,actual=actual,expected=expected,matches=match))
    h=hashlib.sha256()
    for f in sorted((ROOT/'SQLeanite').rglob('*.lean'))+[ROOT/'Main.lean']:
        h.update(str(f.relative_to(ROOT)).encode()+b'\0'+f.read_bytes())
    report=dict(seed=a.seed,count=a.count,scope=__doc__.strip(),cases=cases,failures=[c for c in cases if not c['matches']],source_sha256=h.hexdigest(),executable_sha256=hashlib.sha256(exe.read_bytes()).hexdigest(),native_sha256=hashlib.sha256((ROOT/'native/sqleanite_vfs.c').read_bytes()).hexdigest(),harness_sha256=hashlib.sha256(pathlib.Path(__file__).read_bytes()).hexdigest(),sqlite_identity=subprocess.check_output([sqlite,'--version'],text=True).strip())
    a.output.write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(dict(cases=len(cases),failures=len(report['failures']))))
    return bool(report['failures'])
if __name__=='__main__':raise SystemExit(main())
