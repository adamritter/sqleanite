CREATE TABLE items(id INTEGER PRIMARY KEY,first,second);
INSERT INTO items VALUES(1,NULL,'x'),(2,'value',NULL),(3,NULL,NULL);
SELECT id FROM items WHERE first IS NULL AND NOT second IS NULL ORDER BY id;
SELECT id FROM items WHERE first=NULL OR second='x' ORDER BY id;
