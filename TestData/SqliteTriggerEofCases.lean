import Init

namespace SQLeanite.TestData

def sqliteTriggerEofCases : List (String × String) := [
  ("CREATE TRIGGER truncated_0 AFTER UPDATE ON t BEGIN ", "incomplete input"),
  ("CREATE TRIGGER truncated_1 AFTER UPDATE ON t BEGIN SELECT 1;", "incomplete input"),
  ("CREATE TRIGGER truncated_2 AFTER UPDATE ON t BEGIN UPDATE t SET n=1;", "incomplete input"),
  ("CREATE TRIGGER truncated_3 AFTER UPDATE ON t BEGIN unexpected token", "near \"unexpected\": syntax error"),
  ("CREATE TRIGGER truncated_4 AFTER UPDATE ON t BEGIN SELECT 1; unexpected token", "near \"unexpected\": syntax error"),
  ("CREATE TRIGGER truncated_5 AFTER UPDATE ON t BEGIN DELETE FROM t;", "incomplete input"),
  ("CREATE TRIGGER truncated_6 AFTER UPDATE ON t BEGIN ", "incomplete input"),
  ("CREATE TRIGGER truncated_7 AFTER UPDATE ON t BEGIN SELECT 1;", "incomplete input"),
  ("CREATE TRIGGER truncated_8 AFTER UPDATE ON t BEGIN UPDATE t SET n=1;", "incomplete input"),
  ("CREATE TRIGGER truncated_9 AFTER UPDATE ON t BEGIN unexpected token", "near \"unexpected\": syntax error"),
  ("CREATE TRIGGER truncated_10 AFTER UPDATE ON t BEGIN SELECT 1; unexpected token", "near \"unexpected\": syntax error"),
  ("CREATE TRIGGER truncated_11 AFTER UPDATE ON t BEGIN DELETE FROM t;", "incomplete input")]

end SQLeanite.TestData
