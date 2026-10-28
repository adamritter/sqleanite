#!/usr/bin/env python3
"""Independent selectable SELECT-input regressions; remaining gaps fail normally."""
import unittest
from test_error_effects import case,REGISTER_SETUP,REGISTER_TAIL
class SelectInputGaps(unittest.TestCase):pass
QUERIES={
 'table_counter':'SELECT NULL,last_insert_rowid() FROM src',
 'table_later_error':'SELECT id+10,CASE WHEN n=2 THEN abs(-9223372036854775808) ELSE n END FROM src',
 'where_counter':'SELECT NULL,n FROM src WHERE last_insert_rowid()<12',
 'rowid_order_counter':'SELECT NULL,last_insert_rowid() FROM src ORDER BY id',
 'sort_counter':'SELECT NULL,last_insert_rowid() FROM src ORDER BY n DESC',
 'sort_error':'SELECT id+10,CASE WHEN n=2 THEN abs(-9223372036854775808) ELSE n END FROM src ORDER BY n DESC',
 'self_counter':'SELECT NULL,last_insert_rowid() FROM dst',
 'limit_counter':'SELECT NULL,last_insert_rowid() FROM src LIMIT 2 OFFSET 1',
 'distinct_counter':'SELECT DISTINCT NULL,last_insert_rowid() FROM src',
 'union_counter':'SELECT NULL,last_insert_rowid() UNION ALL SELECT NULL,last_insert_rowid()',
 'values_counter':'SELECT NULL,column1 FROM(VALUES(last_insert_rowid()),(last_insert_rowid()))',
 'subquery_counter':'SELECT NULL,last_insert_rowid() FROM(SELECT * FROM src)',
}
for name,query in QUERIES.items():setattr(SelectInputGaps,'test_'+name,case(REGISTER_SETUP+'INSERT INTO dst '+query+';'+REGISTER_TAIL))
if __name__=='__main__':unittest.main()
