CREATE TABLE items(id INTEGER PRIMARY KEY,first,second);
INSERT INTO items VALUES(3,'three',NULL),(1,'one','a'),(2,'two','b');
SELECT second,id FROM items WHERE id>=2 ORDER BY second DESC,first LIMIT 2;
