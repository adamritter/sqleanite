#!/usr/bin/env python3
"""Compare UNISTR and UNISTR_QUOTE using pinned SQLite and both Core file modes.

Successful queries compare type and hex output, including complete invalid UTF-8
and NUL-containing results. Errors compare positive exit status only, not SQLite
error codes or diagnostic wording. Read-only queries preserve main/WAL bytes.
Six subsequent write scenarios compare typed hex readback, including failed writes.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import random
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]


def literal(text):
    return "'"+text.replace("'", "''")+"'"


def corpus(seed,count):
    rng=random.Random(seed)
    texts=['', 'plain', "a'b", '\\', '\\\\', '\\n', '\\t', '\\u0041', '\\0041',
        '\\+01F600', '\\U0001F600', '\\uD800', '\\uDC00', '\\uD800\\uDC00',
        '\\U00110000', '\\UFFFFFFFF', '\\U00200000', '\\U80000000',
        '\\u0000\\0041', 'a\\0000z', '\\u12', '\\+12345', '\\U1234567',
        '\\123x', '\\q', 'árvíz\\u0041', '\\u0041\\\\u0042', "a\n\\'\t"]
    for _ in range(count):
        parts=[]
        for _ in range(rng.randrange(1,6)):
            choice=rng.randrange(7)
            if choice<4:
                width,prefix=[(4,'\\'),(4,'\\u'),(6,'\\+'),(8,'\\U')][choice]
                number=rng.randrange(16**width)
                parts.append(prefix+format(number,'0'+str(width)+rng.choice(['x','X'])))
            elif choice==4:parts.append(rng.choice(['\\\\','\\q','\\u123','\\+0000x0','\\']))
            else:parts.append(rng.choice(['abc',"'",'\n','\x1b','árvíz','𝄞']))
        texts.append(''.join(parts))
    bytevalues=[b'',b'\0\\q',b'\xff\x80',b'\\u0041\0\\q',b'\x01\x1f\\\x7f',b"'\\\n",
        b'\\u00\x0001',b'\xef\xbb\xbf',b'\0\x01',bytes(range(1,32))]
    bytevalues += [bytes(rng.randrange(256) for _ in range(rng.randrange(1,25))) for _ in range(count//5)]
    values=['NULL','0','-1','1.25','-0.0','1e999','-1e999','1e-300']+[literal(t) for t in texts]
    values += [f"{cast}(X'{b.hex()}'{tail}" for b in bytevalues for cast,tail in [('',')'),('CAST',' AS TEXT)')]]
    # The first form above is a parenthesized BLOB literal, the second TEXT.
    setup='CREATE TABLE t(id INTEGER PRIMARY KEY,v);CREATE TABLE e(id INTEGER PRIMARY KEY,v);'
    for i,v in enumerate(values[:40],1):setup+=f'INSERT INTO t VALUES({i},{v});'
    queries=[]
    for value in values:
        for function in ['unistr','unistr_quote']:
            expression=f'{function}({value})'
            queries.append(f'SELECT typeof({expression}),hex({expression});')
    queries += [
        'SELECT id,typeof(unistr(v)),hex(unistr(v)) FROM t WHERE id<12 ORDER BY id;',
        'SELECT id,hex(unistr_quote(v)) FROM t ORDER BY id DESC LIMIT 10;',
        'SELECT hex(group_concat(unistr_quote(v))) FROM t;',
        'SELECT unistr(v) FROM e;', 'SELECT unistr_quote(v) FROM e;',
        "SELECT unistr('\\q') FROM e;", "SELECT unistr('\\q') LIMIT 0;",
        "SELECT unistr('\\q') LIMIT 1 OFFSET 1;", "SELECT coalesce('x',unistr('\\q'));",
        "SELECT CASE WHEN 0 THEN unistr('\\q') ELSE 7 END;",
        "SELECT unistr_quote('\\q');", "SELECT unistr(DISTINCT '\\u0041');",
        "SELECT unistr_quote(DISTINCT 'x');", "SELECT 'unistr'('\\0041');",
        'SELECT unistr();','SELECT unistr(1,2);','SELECT unistr_quote();','SELECT unistr_quote(1,2);',
        'SELECT unistr(*) FROM e LIMIT 0;', 'SELECT unistr(missing) FROM e LIMIT 0;',
        'SELECT unistr_quote(missing) FROM e LIMIT 0;',
    ]
    return setup,queries

def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--seed',type=int,default=353860)
    p.add_argument('--random-cases',type=int,default=100)
    p.add_argument('--sqlite',default=os.environ.get('SQLITE3_BIN','/usr/bin/sqlite3'))
    p.add_argument('--output',type=Path,required=True)
    args=p.parse_args(); setup,queries=corpus(args.seed,args.random_cases)
    failures=[];phases=[]
    with tempfile.TemporaryDirectory(prefix='sqleanite-unicode-escape-') as tmp:
        for mode in ['--verified-file','--verified-wal-file']:
            folder=Path(tmp)/mode;folder.mkdir()
            def run(sql):
                q=folder/'query.sql';q.write_text(sql)
                l=subprocess.run([str(ROOT/'.lake/build/bin/sqleanite'),mode,str(folder/'lean.db'),str(q)],capture_output=True,timeout=120)
                r=subprocess.run([args.sqlite,'-batch','-bail',str(folder/'sqlite.db')],input=sql.encode(),capture_output=True,timeout=120)
                return l,r
            l,r=run(setup);assert l.returncode==r.returncode==0,(l.stderr,r.stderr)
            def snapshot():return {f.name:f.read_bytes() for f in folder.iterdir() if f.name in ['lean.db','lean.db-wal','sqlite.db','sqlite.db-wal']}
            before=snapshot();errors=0
            for sql in queries:
                l,r=run(sql);same=(l.returncode==r.returncode==0 and l.stdout==r.stdout) or (l.returncode>0 and r.returncode>0)
                if not same:
                    def out(x):return dict(code=x.returncode,stdout=x.stdout.decode('latin1'),stderr=x.stderr.decode('latin1'))
                    failures.append(dict(mode=mode,sql=sql,lean=out(l),sqlite=out(r)))
                elif l.returncode:errors+=1
            assert before==snapshot(),'aggregate read changed input bytes'
            writes=[
                'CREATE TABLE u(id INTEGER PRIMARY KEY,v);',
                "INSERT INTO u VALUES(1,unistr(X'5C7544383030')),(2,unistr(X'5C75303030305C7530303431')),(3,unistr(X'FF805C7530303431'));",
                "INSERT INTO u VALUES(4,unistr_quote(CAST(X'1B5C270A' AS TEXT))),(5,unistr_quote(X'00FF')),(6,unistr(NULL));",
                "UPDATE u SET v=unistr_quote(v) WHERE id<4;",
                "UPDATE u SET v=unistr(X'5C71') WHERE id=6;",
                "INSERT INTO u VALUES(7,unistr(X'5C71'));",
            ]
            write_errors=0
            for sql in writes:
                l,r=run(sql)
                if not ((l.returncode==r.returncode==0 and l.stdout==r.stdout) or (l.returncode>0 and r.returncode>0)):
                    failures.append(dict(mode=mode,sql=sql,kind='write',lean=dict(code=l.returncode,stderr=l.stderr.decode('latin1')),sqlite=dict(code=r.returncode,stderr=r.stderr.decode('latin1'))))
                elif l.returncode:write_errors+=1
                l,r=run('SELECT id,typeof(v),hex(v) FROM u ORDER BY id;')
                if not (l.returncode==r.returncode==0 and l.stdout==r.stdout):
                    failures.append(dict(mode=mode,sql=sql,kind='write-readback',lean=dict(code=l.returncode,stdout=l.stdout.decode('latin1')),sqlite=dict(code=r.returncode,stdout=r.stdout.decode('latin1'))))
            phases.append(dict(mode=mode,queries=len(queries),matching_errors=errors,writes=len(writes),matching_write_errors=write_errors))
    d=hashlib.sha256()
    for path in sorted((ROOT/'SQLeanite').rglob('*.lean'))+[ROOT/'Main.lean']:d.update(str(path.relative_to(ROOT)).encode()+b'\0'+path.read_bytes())
    report=dict(seed=args.seed,random_cases=args.random_cases,phases=phases,failures=failures,implementation_sha256=d.hexdigest(),executable_sha256=hashlib.sha256((ROOT/'.lake/build/bin/sqleanite').read_bytes()).hexdigest(),harness_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),sqlite_version=subprocess.check_output([args.sqlite,'--version'],text=True).strip(),comparison=__doc__.strip())
    args.output.write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(dict(queries=sum(p['queries'] for p in phases),failures=len(failures))))
    return bool(failures)

if __name__=='__main__':raise SystemExit(main())
