#!/usr/bin/env python3
"""Native UTF-16 comparison at predicate and correlated-capture boundaries."""
import os,random,unittest
from test_utf16_provenance import case
class UTF16Predicates(unittest.TestCase):pass
READS={
 'case_value':"SELECT CASE v WHEN CAST(X'{equivalent}' AS TEXT) THEN 1 ELSE 0 END FROM t;",
 'between_value':"SELECT v BETWEEN CAST(X'{equivalent}' AS TEXT) AND CAST(X'{equivalent}' AS TEXT) FROM t;",
 'between_where':"SELECT id FROM t WHERE v BETWEEN CAST(X'{equivalent}' AS TEXT) AND CAST(X'{equivalent}' AS TEXT);",
 'in_single':"SELECT v IN(CAST(X'{equivalent}' AS TEXT)) FROM t;",
 'in_three':"SELECT v IN(CAST(X'{equivalent}' AS TEXT),'x','y') FROM t;",
 'in_subquery':"SELECT v IN(SELECT CAST(X'{equivalent}' AS TEXT)) FROM t;",
 'outer_scalar':'SELECT hex((SELECT a.v)) FROM t a;',
 'between_where_short':"SELECT id FROM t WHERE v BETWEEN CAST(X'FFFF' AS TEXT) AND abs(-9223372036854775808);",
 'binary_where':"SELECT id FROM t WHERE v=CAST(X'{equivalent}' AS TEXT);",
 'in_where':"SELECT id FROM t WHERE v IN(CAST(X'{equivalent}' AS TEXT),'x','y');",
 'filter_native':"SELECT count(*) FILTER(WHERE v=CAST(X'{equivalent}' AS TEXT)) FROM t;",
 'having_native':"SELECT count(*) FROM t HAVING min(v)=CAST(X'{equivalent}' AS TEXT);",
 'outer_hex':'SELECT (SELECT hex(a.v)) FROM t a;',
}
rng=random.Random(int(os.environ.get('SQLEANITE_UTF16_PREDICATE_SEED','821701')))
for enc,pairs in [
 ('UTF-16le',[('00D84100','00D841DC'),('00D8','FDFF'),('FEFF','FDFF'),('4100','4100')]),
 ('UTF-16be',[('D8000041','D800DC41'),('D800','FFFD'),('FFFE','FFFD'),('0041','0041')])]:
 high=rng.randrange(0xD800,0xDC00);following=rng.randrange(0x0041,0x05FF)
 endian='little' if enc.endswith('le') else 'big'
 encode=lambda units:b''.join(word.to_bytes(2,endian) for word in units).hex().upper()
 canonical=(high,0xDC00+(following&0x3FF))
 pairs += [(encode((high,following)),encode(canonical)),(encode(canonical),encode(canonical))]
 for index,(payload,equivalent) in enumerate(pairs):
  for name,sql in READS.items():
   for suffix,mode in [('rollback','--verified-file'),('wal','--verified-wal-file')]:
    setattr(UTF16Predicates,f'test_{enc.replace("-","_")}_{index}_{name}_{suffix}',case(enc,payload,equivalent,sql,mode))
  for suffix,mode in [('rollback','--verified-file'),('wal','--verified-wal-file')]:
   sql="SELECT v BETWEEN CAST(X'FFFF' AS TEXT) AND abs(-9223372036854775808) FROM t;"
   setattr(UTF16Predicates,f'test_{enc.replace("-","_")}_{index}_between_value_eager_{suffix}',case(enc,payload,equivalent,sql,mode,expected_error=True))
 # C creates an odd-length stored TEXT by native concatenation. A captured
 # source value must preserve this representation; a public CAST truncates it.
 payload,equivalent=pairs[0]
 for name,sql in READS.items():
  for suffix,mode in [('rollback','--verified-file'),('wal','--verified-wal-file')]:
   setattr(UTF16Predicates,f'test_{enc.replace("-","_")}_odd_{name}_{suffix}',case(enc,payload,equivalent,sql,mode,setup_suffix="UPDATE t SET v=v||X'41';"))
 for suffix,mode in [('rollback','--verified-file'),('wal','--verified-wal-file')]:
  sql="SELECT v BETWEEN CAST(X'FFFF' AS TEXT) AND abs(-9223372036854775808) FROM t;"
  setattr(UTF16Predicates,f'test_{enc.replace("-","_")}_odd_between_value_eager_{suffix}',case(enc,payload,equivalent,sql,mode,setup_suffix="UPDATE t SET v=v||X'41';",expected_error=True))
if __name__=='__main__':unittest.main()
