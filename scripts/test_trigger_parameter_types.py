#!/usr/bin/env python3
"""Trigger Param registers carry values/collation/subtype, not column affinity."""
import unittest
from test_check_add_column import case
from test_trigger_execution import SETUP,TAIL
class ParameterTypes(unittest.TestCase):pass
EXPRESSIONS={
 'new_integer_text':"new.n='03'",
 'old_integer_text':"old.n='02'",
 'new_text_integer':"new.v=23",
 'old_text_integer':"old.v=23",
 'explicit_cast':"CAST(new.n AS INTEGER)='03'",
 'numeric_values':"new.n=3",
 'single_in':"new.n IN('03')",
 'multiple_in':"new.n IN('03','3')",
 'case_base':"CASE new.n WHEN '03' THEN 1 ELSE 0 END",
 'scalar_select':"(SELECT new.n)='03'",
 'between':"new.n BETWEEN '02' AND '04'",
 'typeof_value':"typeof(new.n)='integer'",
}
for timing in ['BEFORE','AFTER']:
 for name,expression in EXPRESSIONS.items():
  sql=f"CREATE TRIGGER tr {timing} UPDATE ON t BEGIN UPDATE log SET n=({expression}),v=typeof(new.n)||'/'||typeof(new.v);END;UPDATE t SET n='03',v=23 WHERE id=2;"+TAIL
  for suffix,mode in [('rollback','--verified-file'),('wal','--verified-wal-file')]:
   setattr(ParameterTypes,'test_'+timing.lower()+'_'+name+'_'+suffix,case(sql,mode,SETUP))
for timing,event,action in [('BEFORE','UPDATE','UPDATE t SET n=n+1;'),('AFTER','UPDATE','UPDATE t SET n=n+1;'),('BEFORE','DELETE','DELETE FROM t WHERE 0;')]:
 sql=f'CREATE TRIGGER tr {timing} {event} ON t BEGIN SELECT n;END;'+action
 for suffix,mode in [('rollback','--verified-file'),('wal','--verified-wal-file')]:
  setattr(ParameterTypes,'test_unqualified_'+timing.lower()+'_'+event.lower()+'_'+suffix,case(sql,mode,SETUP))
if __name__=='__main__':unittest.main()
