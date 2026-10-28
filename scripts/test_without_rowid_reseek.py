#!/usr/bin/env python3
"""Actual primary-key reseek after BEFORE programs delete/reinsert rows."""
import os,random,unittest
from test_without_rowid import case
class WithoutRowidReseek(unittest.TestCase):pass
BASE="CREATE TABLE w(k TEXT PRIMARY KEY,v TEXT,n) WITHOUT ROWID;INSERT INTO w VALUES('a','aye',1),('b','bee',2);"
AFTER='SELECT * FROM w ORDER BY k;SELECT changes(),total_changes(),last_insert_rowid();'
Q={
 'update_same':"CREATE TRIGGER b BEFORE UPDATE ON w WHEN old.k='a' BEGIN DELETE FROM w WHERE k=old.k;INSERT INTO w VALUES(old.k,'replacement',20);END;UPDATE w SET n=n+10 WHERE k='a';",
 'delete_same':"CREATE TRIGGER b BEFORE DELETE ON w WHEN old.k='a' BEGIN DELETE FROM w WHERE k=old.k;INSERT INTO w VALUES(old.k,'replacement',20);END;DELETE FROM w WHERE k='a';",
 'later_update':"CREATE TRIGGER b BEFORE UPDATE ON w WHEN old.k='a' BEGIN DELETE FROM w WHERE k='b';INSERT INTO w VALUES('b','replacement',20);END;UPDATE w SET n=n+10;",
 'later_delete':"CREATE TRIGGER b BEFORE DELETE ON w WHEN old.k='a' BEGIN DELETE FROM w WHERE k='b';INSERT INTO w VALUES('b','replacement',20);END;DELETE FROM w;",
 'update_changed_key':"CREATE TRIGGER b BEFORE UPDATE ON w WHEN old.k='a' BEGIN UPDATE w SET k='c' WHERE k=old.k;END;UPDATE w SET n=n+10 WHERE k='a';",
 'delete_changed_key':"CREATE TRIGGER b BEFORE DELETE ON w WHEN old.k='a' BEGIN UPDATE w SET k='c' WHERE k=old.k;END;DELETE FROM w WHERE k='a';",
}
rng=random.Random(int(os.environ.get('SQLEANITE_WITHOUT_ROWID_RESEEK_SEED','1891001')))
nonce=rng.randrange(1000,999999);delta=rng.randrange(20,900)
BASE=BASE.replace("'a'",f"'a{nonce}'").replace("'b'",f"'b{nonce}'")
Q={name:sql.replace("'a'",f"'a{nonce}'").replace("'b'",f"'b{nonce}'").replace('n=n+10',f'n=n+{delta}') for name,sql in Q.items()}
for name,sql in Q.items():
 for suffix,mode in [('rollback','--verified-file'),('wal','--verified-wal-file')]:setattr(WithoutRowidReseek,'test_'+name+'_'+suffix,case(BASE,sql+AFTER,mode))
if __name__=='__main__':unittest.main()
