BEGIN;
UPDATE orders SET status='held' WHERE id=7;
SELECT status FROM orders WHERE id=7;
COMMIT;
SELECT status FROM orders WHERE id=7;
