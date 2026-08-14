CREATE TABLE items(id INTEGER PRIMARY KEY,first,second);
INSERT INTO items VALUES(1,'old','payload');
INSERT OR REPLACE INTO items VALUES(1,'new',NULL);
SELECT * FROM items;
