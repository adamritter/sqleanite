#!/usr/bin/env python3
"""Native UTF-16 provenance through expression and source boundaries.
All known differences are normal failing unittests; no skips or oracle routes.
"""
import os,random,re,shutil,subprocess,tempfile,unittest
from pathlib import Path
from test_check_add_column import statement_lines,SQLITE,BINARY
class UTF16Provenance(unittest.TestCase):pass
READS={
 'identity':'SELECT hex(v),octet_length(v),hex(CAST(v AS BLOB)) FROM t;',
 'case':"SELECT hex(CASE WHEN id=1 THEN v ELSE 'x' END) FROM t;",
 'coalesce':"SELECT hex(coalesce(v,'x')),hex(iif(id=1,v,'x')) FROM t;",
 'scalar':'SELECT hex((SELECT v FROM t WHERE id=1));',
 'correlated':'SELECT id,hex((SELECT v FROM t b WHERE b.id=a.id)) FROM t a;',
 'derived':'SELECT hex(v) FROM (SELECT id,v FROM t);',
 'cte':'WITH c AS MATERIALIZED(SELECT id,v FROM t) SELECT hex(v) FROM c;',
 'view':'SELECT hex(v) FROM q;',
 'join':'SELECT hex(a.v),hex(b.v) FROM t a JOIN t b ON a.id=b.id;',
 'window':'SELECT hex(v),row_number() OVER(ORDER BY id) FROM t;',
 'aggregate':'SELECT hex(min(v)),hex(max(v)) FROM t;',
 'concat':"SELECT hex(v||'x'),hex('x'||v),hex(v||v) FROM t;",
 'functions':'SELECT hex(lower(v)),hex(upper(v)),hex(substr(v,1)),hex(replace(v,\'x\',\'y\')) FROM t;',
 'value_compare':"SELECT v=CAST(X'{equivalent}' AS TEXT),v<CAST(X'{equivalent}' AS TEXT) FROM t;",
}

def case(encoding,payload,equivalent,sql,mode,two_rows=False,setup_suffix="",expected_error=False):
 def test(self):
  with tempfile.TemporaryDirectory(prefix='sqleanite-utf16-origin-') as folder:
   base=Path(folder)/'base.db';left=Path(folder)/'lean.db';right=Path(folder)/'sqlite.db'
   setup=f"PRAGMA encoding='{encoding}';CREATE TABLE t(id INTEGER PRIMARY KEY,v TEXT);INSERT INTO t VALUES(1,CAST(X'{payload}' AS TEXT));CREATE VIEW q AS SELECT id,v FROM t;"
   if two_rows:setup+=f"INSERT INTO t VALUES(2,CAST(X'{equivalent}' AS TEXT));"
   setup+=setup_suffix
   subprocess.run([SQLITE,str(base)],input=setup.encode(),capture_output=True,check=True)
   shutil.copyfile(base,left);shutil.copyfile(base,right);before=left.read_bytes()
   query=statement_lines(sql.format(equivalent=equivalent)).encode()
   lean=subprocess.run([str(BINARY),mode,str(left)],input=query,capture_output=True,timeout=30)
   ref=subprocess.run([SQLITE,'-batch','-bail',str(right)],input=query,capture_output=True,timeout=30)
   self.assertEqual(bool(ref.returncode),expected_error,ref.stderr)
   self.assertEqual(lean.returncode,ref.returncode,lean.stderr)
   self.assertEqual(lean.stdout,ref.stdout)
   if expected_error:
    def diagnostic(result):
     line=result.stderr.decode('utf-8').splitlines()[0] if result.stderr else ''
     return re.sub(r'^(?:Parse error|Runtime error|Error)(?: near line [0-9]+)?: ?','',line)
    self.assertEqual(diagnostic(lean),diagnostic(ref))
   self.assertEqual(left.read_bytes(),before,'read changed physical bytes')
   self.assertEqual(subprocess.check_output([SQLITE,str(left),'PRAGMA integrity_check;']),b'ok\n')
 return test
rng=random.Random(int(os.environ.get('SQLEANITE_UTF16_PROVENANCE_SEED','611731')))
for enc,pairs in [
 ('UTF-16le',[('00D84100','00D841DC'),('00D8','FDFF'),('FEFF','FDFF'),('4100','4100')]),
 ('UTF-16be',[('D8000041','D800DC41'),('D800','FFFD'),('FFFE','FFFD'),('0041','0041')])]:
 # Fresh malformed pair plus an independent valid supplementary-plane
 # control. Canonical bytes follow the explicit UTF-16 code-unit definition;
 # every observable expectation still comes from the ordinary SQLite process.
 high=rng.randrange(0xD800,0xDC00);following=rng.randrange(0x0041,0x05FF)
 canonical=(high,0xDC00+(following&0x3FF))
 endian='little' if enc.endswith('le') else 'big'
 encode=lambda units:b''.join(word.to_bytes(2,endian) for word in units).hex().upper()
 pairs += [(encode((high,following)),encode(canonical)),(encode(canonical),encode(canonical))]
 for index,(payload,equivalent) in enumerate(pairs):
  for name,sql in READS.items():
   for suffix,mode in [('rollback','--verified-file'),('wal','--verified-wal-file')]:
    setattr(UTF16Provenance,f'test_{enc.replace("-","_")}_{index}_{name}_{suffix}',case(enc,payload,equivalent,sql,mode))
  for name,sql in {
   'multi_native_extrema':'SELECT hex(min(v)),hex(max(v)) FROM t;',
   'multi_join_rows':'SELECT a.id,b.id,hex(a.v),hex(b.v) FROM t a JOIN t b ON a.id!=b.id ORDER BY a.id,b.id;',
   'multi_scalar_extrema':"SELECT id,hex(min(v,CAST(X'{equivalent}' AS TEXT))),hex(max(v,CAST(X'{equivalent}' AS TEXT))),hex(nullif(v,CAST(X'{equivalent}' AS TEXT))) FROM t ORDER BY id;",
  }.items():
   for suffix,mode in [('rollback','--verified-file'),('wal','--verified-wal-file')]:
    setattr(UTF16Provenance,f'test_{enc.replace("-","_")}_{index}_{name}_{suffix}',case(enc,payload,equivalent,sql,mode,True))
if __name__=='__main__':unittest.main()
