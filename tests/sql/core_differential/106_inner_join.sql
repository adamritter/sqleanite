CREATE TABLE items(id INTEGER PRIMARY KEY,first,second);
INSERT INTO items VALUES(1,'one','group'),(2,'two','group'),(3,'three','other');
SELECT a.id,b.id,a.first FROM items AS a INNER JOIN items AS b
  ON a.second=b.second WHERE a.id<b.id ORDER BY a.id,b.id;
