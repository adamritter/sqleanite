CREATE TABLE widget(sku INTEGER PRIMARY KEY,label,note);
INSERT INTO widget VALUES(4,'delta','d');
INSERT INTO widget VALUES(2,'beta','b');
INSERT INTO widget VALUES(9,'iota',NULL);
SELECT sku,label,note FROM widget WHERE sku>=2 ORDER BY sku DESC LIMIT 2;
UPDATE widget SET note='updated' WHERE sku=2;
SELECT sku,note FROM widget WHERE sku=2;
DELETE FROM widget WHERE sku=4;
SELECT sku FROM widget;
