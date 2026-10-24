#!/usr/bin/env python3
"""Quoted function names and the pinned function-argument limit through both
production file modes. Exact CLI bytes/rejection status are compared with pinned
SQLite; read-only queries must preserve existing main/WAL bytes.
"""
import argparse
import hashlib
import json
import os
import pathlib
import random
import subprocess
import tempfile

ROOT=pathlib.Path(__file__).resolve().parents[1]


def quoted(name, style):
    if style=='bare':return name
    if style=='double':return '"'+name.replace('"','""')+'"'
    if style=='bracket':return '['+name+']'
    if style=='backtick':return '`'+name.replace('`','``')+'`'
    return "'"+name.replace("'","''")+"'"


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--seed',type=int,default=353720)
    p.add_argument('--random-cases',type=int,default=200)
    p.add_argument('--sqlite',default=os.environ.get('SQLITE3_BIN','/usr/bin/sqlite3'))
    p.add_argument('--output',type=pathlib.Path,required=True)
    args=p.parse_args();rng=random.Random(args.seed)
    executable=ROOT/'.lake/build/bin/sqleanite'
    functions=[('abs','-3'),('length',"'árvíz🙂'"),('octet_length',"'árvíz🙂'"),('hex',"X'00FF80'"),
               ('unhex',"'00 ff',' '"),('upper',"'abcá'"),('lower',"X'FF41'"),('substr',"'abcdef',-3,2"),
               ('substring',"'abcdef',2,3"),('instr',"'árvíz','ví'"),('trim',"' xyx ',' x'"),
               ('ltrim',"' a '"),('rtrim',"' a '"),('replace',"'abcabc','ab','X'"),
               ('char','65,128578'),('unicode',"'🙂'"),('quote',"'a''b'"),('zeroblob','7'),
               ('typeof','1.0'),('round','1.2345,2'),('sign',"'-3.5'"),('min','1.0,1'),
               ('max','1,1.0'),('coalesce',"NULL,'x'"),('ifnull','NULL,7'),('nullif','1,1.0'),
               ('iif','1,2,3'),('concat',"'a',NULL,'b'"),('concat_ws',"'-','a','','b'")]
    queries=[]
    for name,arguments in functions:
        for style in ['bare','double','bracket','backtick','single']:
            call=quoted(name,style)+'('+arguments+')'
            queries.append(f'SELECT {call};')
            queries.append(f'SELECT {call} FROM t WHERE id=1;')
            queries.append(f'SELECT {quoted(name,style)}(DISTINCT {arguments});')
    for name in ['sum','avg','total','count','min','max']:
        for style in ['double','bracket','backtick']:
            fun=quoted(name,style)
            queries.extend([f'SELECT {fun}(v) FROM t;',f'SELECT {fun}(DISTINCT v) FROM t;',
                            f'SELECT {fun}(ALL v) FROM t;'])
    for style in ['bare','double','bracket','backtick']:
        fun=quoted('count',style)
        queries.extend([f'SELECT {fun}(*) FROM t;',f'SELECT {fun}(*) FROM t WHERE 0;'])
        for n in [999,1000,1001]:
            for name in ['char','concat']:
                call=quoted(name,style)+'('+','.join(['65' if name=='char' else "'a'"]*n)+')'
                queries.append(f'SELECT length({call});')
    for _ in range(args.random_cases):
        name,arguments=rng.choice(functions)
        name=''.join(c.upper() if rng.randrange(2) else c for c in name)
        fun=quoted(name,rng.choice(['double','bracket','backtick']))
        queries.append(f'SELECT {fun}({arguments}) FROM t WHERE id={rng.randrange(1,7)};')
    queries+=['SELECT "abs"(v),[abs](v),`abs`(v) FROM t ORDER BY id;',
              'SELECT "abs"(-3) AS x FROM t ORDER BY "abs"(v),id;',
              'SELECT 0 AND "abs"(-9223372036854775808);',
              'SELECT 0 AND "unknown_function"();',
              'SELECT "unknown_function"(1);','SELECT "cast"(1);',
              'SELECT "true"();','SELECT "lean_dqs"(\'lean_dqs\');',
              'SELECT "__sqlean_boolean_true"();','SELECT "sum"(v) OVER () FROM t;',
              'SELECT "abs"();','SELECT "abs"(1,2);','SELECT "abs"(DISTINCT 1);']
    for name in ['cast_integer','CAST_INTEGER','Cast_Text','lean_distinct_aggregate_abs','LEAN_DISTINCT_AGGREGATE_ABS','lean_dqs','__sqlean_boolean_true']:
        for style in ['bare','double','bracket','backtick']:
            for modifier in ['', 'DISTINCT ']:
                queries.append(f'SELECT {quoted(name,style)}({modifier}1);')
    setup='CREATE TABLE t(id INTEGER PRIMARY KEY,v,"abs"); INSERT INTO t VALUES(1,-3,99),(2,1.5,88),(3,NULL,77),(4,0,66),(5,\'2\',55),(6,-1,44);'
    failures,phases=[],[]
    with tempfile.TemporaryDirectory(prefix='sqleanite-quoted-function-') as tmp:
        for mode in ['--verified-file','--verified-wal-file']:
            folder=pathlib.Path(tmp)/mode;folder.mkdir()
            def run(sql,destination=folder):
                destination.mkdir(exist_ok=True)
                q=destination/'query.sql';q.write_text(sql)
                a=subprocess.run([str(executable),mode,str(destination/'lean.db'),str(q)],capture_output=True,timeout=120)
                b=subprocess.run([args.sqlite,'-batch','-bail',str(destination/'sqlite.db')],input=sql.encode(),capture_output=True,timeout=120)
                return a,b
            a,b=run(setup);assert a.returncode==b.returncode==0,(a.stderr,b.stderr)
            files=[folder/n for n in ['lean.db','lean.db-wal','sqlite.db','sqlite.db-wal']]
            def snapshot():return {f.name:f.read_bytes() for f in files if f.exists()}
            before=snapshot();errors=0
            def compare(sql,a,b):
                same=(a.returncode==b.returncode==0 and a.stdout==b.stdout) or (a.returncode>0 and b.returncode>0)
                if not same:
                    def out(r):return dict(code=r.returncode,stdout=r.stdout.decode('latin-1'),stderr=r.stderr.decode('latin-1'))
                    failures.append(dict(mode=mode,sql=sql,lean=out(a),sqlite=out(b)))
                return same
            for sql in queries:
                a,b=run(sql)
                if compare(sql,a,b) and a.returncode:errors+=1
            assert before==snapshot(),'read query changed main/WAL bytes'
            writes=['INSERT INTO t VALUES(7,"abs"(-17),`length`(\'hello\'));',
                    'UPDATE t SET v="abs"(v),"abs"=`length`(v) WHERE [abs](v)>1;',
                    'DELETE FROM t WHERE "abs"(v)>1;']
            for i,write in enumerate(writes):
                sql=setup+write+'SELECT id,v,"abs" FROM t ORDER BY id;'
                a,b=run(sql,folder/f'write-{i}');compare(sql,a,b)
            phases.append(dict(mode=mode,read_queries=len(queries),matching_read_errors=errors,writes=len(writes)))
    digest=hashlib.sha256()
    for path in sorted((ROOT/'SQLeanite').rglob('*.lean'))+[ROOT/'Main.lean']:
        digest.update(str(path.relative_to(ROOT)).encode()+b'\0'+path.read_bytes())
    report=dict(seed=args.seed,random_cases=args.random_cases,phases=phases,failures=failures,implementation_sha256=digest.hexdigest(),
                executable_sha256=hashlib.sha256(executable.read_bytes()).hexdigest(),harness_sha256=hashlib.sha256(pathlib.Path(__file__).read_bytes()).hexdigest(),
                sqlite_version=subprocess.check_output([args.sqlite,'--version'],text=True).strip(),comparison=__doc__.strip())
    args.output.write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(dict(queries=sum(p['read_queries']+p['writes'] for p in phases),failures=len(failures))))
    return bool(failures)

if __name__=='__main__':raise SystemExit(main())
