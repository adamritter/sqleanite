CREATE TABLE items(id INTEGER PRIMARY KEY,first,second);
INSERT INTO items VALUES(3,'three',NULL),(1,'one',NULL),(2,'two',NULL);
DELETE FROM items WHERE id=2;
SELECT * FROM items ORDER BY id;
