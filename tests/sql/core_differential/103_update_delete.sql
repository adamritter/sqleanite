CREATE TABLE items(id INTEGER PRIMARY KEY,first,second);
INSERT INTO items VALUES(1,'one','keep'),(2,'two','drop'),(3,'three','keep');
UPDATE items SET first='changed' WHERE second='keep';
DELETE FROM items WHERE first!='changed';
SELECT id,first,second FROM items ORDER BY id;
