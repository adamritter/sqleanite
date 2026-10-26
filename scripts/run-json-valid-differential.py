#!/usr/bin/env python3
"""SQLite json_valid() text/JSON5/JSONB differential through both public file modes.

Fixed grammar and binary-header controls are mixed with independently seeded
values and mutations. Every mask 1..15 and the default are compared together;
bad/coerced masks and callback error prefixes are separate cases. Error messages
are compared after removing the CLI prefix and C caret/source display lines. C-generated
JSONB is fixture data only. Compare complete stdout/status, immutable main/WAL
bytes, C integrity and typed-row observations. Preserve all failures.
"""
import argparse, hashlib, json, os, random, re, shutil, subprocess, tempfile
from pathlib import Path
ROOT = Path(__file__).resolve().parents[1]
def digest(root):
    result = hashlib.sha256()
    for p in sorted((root/'SQLeanite').rglob('*.lean'))+[root/'Main.lean']:
        result.update(str(p.relative_to(root)).encode()+b'\0'+p.read_bytes())
    return result.hexdigest()
def text_expr(data):
    if isinstance(data,str):data=data.encode()
    return "CAST(X'"+data.hex()+"' AS TEXT)"
def blob_expr(data):return "X'"+data.hex()+"'"
def node(kind,data,width=None):
    n=len(data)
    if width is None:width=0 if n<12 else 1 if n<256 else 2 if n<65536 else 4
    return bytes([(n if width==0 else {1:12,2:13,4:14,8:15}[width])*16+kind])+(n.to_bytes(width,'big') if width else b'')+data
def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--seed',type=int,default=354750);p.add_argument('--fixtures',type=int,default=2)
    p.add_argument('--random-cases',type=int,default=64);p.add_argument('--implementation-root',type=Path,default=ROOT)
    p.add_argument('--output',type=Path,required=True);a=p.parse_args();rng=random.Random(a.seed)
    root=a.implementation_root.resolve();binary=root/'.lake/build/bin/sqleanite'
    sqlite=os.environ.get('SQLITE3_BIN','sqlite3');source=digest(root);executable=hashlib.sha256(binary.read_bytes()).hexdigest()
    def run(argv,sql):
        r=subprocess.run(argv,input=sql.encode(),capture_output=True,timeout=120)
        return dict(code=r.returncode,stdout=r.stdout.decode('latin1'),stderr=r.stderr.decode('latin1'))
    def csql(path,sql):return run([sqlite,'-batch','-bail',str(path)],sql)
    def error_message(result):
        if not result['code']:return ''
        first=result['stderr'].splitlines()[0] if result['stderr'] else ''
        return re.sub(r'^(?:Parse error|Runtime error|Error)(?: near line [0-9]+)?: ?', '', first)
    def snapshot(path):
        return {s:hashlib.sha256(Path(str(path)+s).read_bytes()).hexdigest() for s in ['','-wal'] if Path(str(path)+s).exists()}
    values=[]
    def add(group,expression):values.append(dict(group=group,expression=expression))
    strict=['null','true','false','0','-0','1','-1','123456789012345678901234567890','1.0','0.1','1e1','1E+1','-1e-1','1e9999',
            '""','"a"','"\\u0000"','"\\ud800"','"\\udfff"','"\\ud800\\udfff"','[]','{}','[null,true,false,1,"a"]','{"a":1,"a":2}',
            ' [1, {"x":[false]}] \r\n','"é中😀"']
    extensions=["'a'",'{a:1}','$','{_a:1,$b:2}','{é:1}','{\\u0061:1}','{\\u0030:1}',
        '{true:1}','{false:1}','{null:1}','{null$:1}','{null_:1}','{TRUE:1}','{trueX:1}','{NaN:1}','{Infinity:1}',
        '{a:1,}','[1,]','+1','.1','1.','1.e1','+.1','-.1','0x1','0Xabcdef','-0x1','+0x1',
        'Inf','Infinity','iNf','-Infinity','+Inf','NaN','qNaN','sNaN','+NaN','-NaN',
        '//x\n1','/*x*/1','1//x','1/*x*/','/*x*/[/*x*/1,/*x*/]/*x*/',
        "'\\''",'"\\\'"','"\\x41"','"\\v"','"\\0"','"\\01"','"\\a"','"\\\nq"','"\\\r\nq"','"\\\u2028q"','"a\nb"','"a\tb"']
    bad=['',' ','tru','True','falsex','nully','nul','NaNx','infinite','00','01','-01','0x','0xg','+','-','.','+.','1e','1e+','1e-',
         '.e1','1..0','1e1.0','1 2','{}[]','[','{','[1','[1,,2]','[,1]','{,}','{a}','{a:}','{a:1,,}','{1:2}',
         '"','"x','"\\','"\\u"','"\\u000"','"\\uXXXX"','"\\x0"','/*x','//','/*/1','1/*','"a\x00b"']
    for group,items in [('strict-text',strict),('json5-text',extensions),('invalid-text',bad)]:
        for s in items:add(group,text_expr(s));add(group+'-blob',blob_expr(s.encode()))
    spaces=['\t','\n','\r',' ','\v','\f','\u0085','\u00a0','\u1680']+[chr(x) for x in range(0x2000,0x200c)]+['\u2028','\u2029','\u202f','\u205f','\u3000','\ufeff']
    for s in spaces:
        for value in [s+'1'+s,'['+s+'1'+s+']','{'+s+'x:1'+s+'}']:add('whitespace',text_expr(value))
    for data in [b'1\0junk',b'null\0x',b'[]\0[]',b'\0null',b'"\xff"',b'\xff',b'{\xff:1}',b'"\xc0\x80"',b'"\xed\xa0\x80"']:
        add('raw-bytes-text',text_expr(data));add('raw-bytes-blob',blob_expr(data))
    for i in range(32):
        add('raw-control',text_expr(b'"a'+bytes([i])+b'b"'))
    for kind in range(16):
        for data in [b'',b'0',b'1',b'-0',b'00',b'01',b'1.0',b'1e1',b'e1',b'0x1',b'a',b'"',b'\\n',b'\0']:
            add('jsonb-kinds',blob_expr(node(kind,data)))
    for kind,data in [(0,b''),(1,b''),(2,b''),(3,b'00'),(5,b'e1'),(7,b'x'),(8,b'\\u0000'),(9,b'\\xZZ'),(10,b'\0'),(11,b'\x00'),(12,b'\x17a\x00')]:
        for width in [1,2,4,8]:add('jsonb-nonminimal',blob_expr(node(kind,data,width)))
    for kind in [7,8,9,10]:
        for data in [b'\\',b'\\a',b'\\0',b'\\01',b'\\x',b'\\x00',b'\\xGG',b'\\u0000',b'\\uGGGG',b'\\v',b"\\'",b'\\\n',b'\\\r\n',b'\\\n\\a',b'\\\n\\xZZ',b'\\\n\xff']:
            add('jsonb-string',blob_expr(node(kind,data)))
    for data in [b'\xc0',b'\xc0\0',b'\xd0\0\0',b'\xf0\0\0\0\1\0\0\0\0',b'\xcb\x01',b'\xcb\x02\x00',
                 b'\x1b\x00',b'\x2b\x00\x01',b'\x1c\x00',b'\x3c\x17a\x00',b'\x3c\x13a\x00',b'\x2c\x17a',b'\x4c\x17a\x00\x00',
                 b'\x0b\x00',b'\x0f',b'1234',b'12345',b'[1234]',b'{"a":1}']:
        add('jsonb-structure',blob_expr(data))
    for depth in [1,2,10,999,1000,1001]:
        add('text-depth',text_expr('['*depth+'0'+']'*depth))
        data=b'\x13\x30'
        for _ in range(depth):data=node(11,data)
        add('jsonb-depth',blob_expr(data))
    for literal in ['NULL','0','1','-1','1.5','1e99','-1e999','9223372036854775807']:
        add('sql-storage-type',literal)
    generated=[]
    def random_value(depth=0):
        choices=[None,True,False,rng.randrange(-10**18,10**18),rng.random()*1e12,
                 ''.join(rng.choice('abcé中😀\\\n\t"0123') for _ in range(rng.randrange(20)))]
        if depth<3:
            choices += [[random_value(depth+1) for _ in range(rng.randrange(4))],
                        {str(rng.randrange(10)):random_value(depth+1) for _ in range(rng.randrange(4))}]
        return rng.choice(choices)
    for _ in range(a.random_cases):
        s=json.dumps(random_value(),ensure_ascii=bool(rng.randrange(2)),separators=(',',':'))
        response=csql(':memory:',f'SELECT hex(jsonb({text_expr(s)}));')
        assert response['code']==0,response
        data=bytes.fromhex(response['stdout'].strip())
        generated.append(dict(text=s,jsonb_hex=data.hex(),oracle=response))
        add('seeded-text',text_expr(s));add('seeded-jsonb',blob_expr(data))
        raw=bytearray(s.encode())
        for _ in range(rng.randrange(1,4)):
            op=rng.randrange(3);pos=rng.randrange(len(raw)+1)
            if op==0:raw[pos:pos]=bytes([rng.randrange(256)])
            elif op==1 and pos<len(raw):del raw[pos]
            elif pos<len(raw):raw[pos]=rng.randrange(256)
        add('seeded-text-mutation',text_expr(bytes(raw)))
        raw=bytearray(data);pos=rng.randrange(len(raw)+1);op=rng.randrange(3)
        if op==0:raw[pos:pos]=bytes([rng.randrange(256)])
        elif op==1 and pos<len(raw):del raw[pos]
        elif pos<len(raw):raw[pos]=rng.randrange(256)
        add('seeded-jsonb-mutation',blob_expr(bytes(raw)))
        add('seeded-binary',blob_expr(bytes(rng.randrange(256) for _ in range(rng.randrange(25)))))
    cases=[];fixtures=[]
    flags=['NULL','0','-1','16','255','9223372036854775807','-9223372036854775808',
           '1.9','2.9','15.9','16.0',"'2x'","'2e0'","'0x2'","'  +8x'", "X'32'","''","'bad'"]
    with tempfile.TemporaryDirectory(prefix='sqleanite-json-valid-') as tmp:
        for fixture in range(a.fixtures):
            folder=Path(tmp)/str(fixture);folder.mkdir();base=folder/'base.db';page=512<<(fixture%8)
            setup=f'PRAGMA page_size={page};CREATE TABLE t(id INTEGER PRIMARY KEY,v);'
            setup+=''.join(f"INSERT INTO t VALUES({i+1},{v['expression']});" for i,v in enumerate(values))
            created=csql(base,setup);assert created['code']==0,created
            queries=[dict(group=v['group'],input=i+1,sql='SELECT '+','.join(['json_valid(v)']+[f'json_valid(v,{mask})' for mask in range(1,16)])+f' FROM t WHERE id={i+1};') for i,v in enumerate(values)]
            queries += [dict(group='mask-coercion',sql=f'SELECT json_valid({value},{mask});') for mask in flags for value in ['NULL',"'1'","X'00'"]]
            queries += [dict(group='arity',sql=q) for q in ['SELECT json_valid();','SELECT json_valid(1,2,3);',
                'SELECT json_valid() LIMIT 0;','SELECT CASE WHEN 0 THEN json_valid() ELSE 1 END;',
                'SELECT json_valid() FROM t WHERE 0;','SELECT json_valid(1,2,3) FROM t LIMIT 0;']]
            queries += [dict(group='arity-spelling-context',sql=sql) for sql in ['SELECT JSON_VALID();', 'SELECT "JSON_VALID"();', 'SELECT JsOn_VaLiD(1,2,3);', 'SELECT json_valid(*);', 'SELECT JSON_VALID(DISTINCT 1,2,3);', 'SELECT 0 AND json_valid();', 'SELECT json_valid() AND 0;', 'SELECT 1 OR json_valid();', 'SELECT iif(0,json_valid(),1);', 'SELECT CASE WHEN 0 THEN JSON_VALID() ELSE 1 END;', 'SELECT JSON_VALID() FROM t LIMIT 0;', 'SELECT id FROM t WHERE 0 AND JSON_VALID();', 'SELECT sum(JSON_VALID()) FROM t;', 'SELECT count(*) FILTER(WHERE JSON_VALID()) FROM t;', 'SELECT JSON_VALID() FROM t a JOIN t b USING(id);', 'SELECT JSON_VALID() FROM t a JOIN t b USING(id) LIMIT 0;', 'SELECT count(*) FROM t ORDER BY JSON_VALID();', 'SELECT json_valid(DISTINCT 1,2);', 'SELECT json_valid(abs(-9223372036854775808),0);']]
            queries += [dict(group='arity-rewritten-in',sql=sql) for sql in ['SELECT 1 IN (JSON_VALID());', 'SELECT 1 NOT IN (JSON_VALID());', 'SELECT id FROM t WHERE id IN (JSON_VALID());']]
            queries += [dict(group='arity-limit',sql='SELECT json_valid('+','.join(['1']*count)+');') for count in [1000,1001]]
            queries += [dict(group='callback-prefix',sql=f'SELECT id,json_valid(v,{mask}) FROM t WHERE id<5 ORDER BY id;') for mask in ['id','id+12','4-id','CASE WHEN id=3 THEN 0 ELSE 1 END']]
            for mode in ['--verified-file','--verified-wal-file']:
                left=folder/(mode+'-lean.db');right=folder/(mode+'-c.db');shutil.copyfile(base,left);shutil.copyfile(base,right)
                bl,br=snapshot(left),snapshot(right)
                for q in queries:
                    l=run([str(binary),mode,str(left)],q['sql']);c=csql(right,q['sql'])
                    cases.append(dict(q,fixture=fixture,page_size=page,mode=mode,lean=l,sqlite=c,lean_error=error_message(l),sqlite_error=error_message(c),matched=bool(l['code'])==bool(c['code']) and l['stdout']==c['stdout'] and error_message(l)==error_message(c)))
                observe='PRAGMA integrity_check;SELECT id,typeof(v),hex(v) FROM t ORDER BY id;'
                lo,co=csql(left,observe),csql(right,observe)
                fixtures.append(dict(fixture=fixture,mode=mode,page_size=page,setup=setup,lean_unchanged=bl==snapshot(left),sqlite_unchanged=br==snapshot(right),
                    observation_lean=lo,observation_sqlite=co,matched=bl==snapshot(left) and br==snapshot(right) and lo['code']==co['code']==0 and lo['stdout']==co['stdout'] and lo['stdout'].startswith('ok\n')))
    assert source==digest(root) and executable==hashlib.sha256(binary.read_bytes()).hexdigest(),'Implementation changed during evaluation'
    failures=sum(not c['matched'] for c in cases)+sum(not f['matched'] for f in fixtures)
    report=dict(seed=a.seed,random_cases=a.random_cases,values=values,generated_jsonb=generated,cases=cases,fixtures=fixtures,failures=failures,
        implementation_sha256=source,executable_sha256=executable,harness_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        sqlite_version=subprocess.check_output([sqlite,'--version'],text=True).strip(),comparison=__doc__.strip())
    a.output.write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(dict(values=len(values),cases=len(cases),failures=failures)));return bool(failures)
if __name__=='__main__':raise SystemExit(main())
