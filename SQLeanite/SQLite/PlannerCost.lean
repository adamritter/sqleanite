import SQLeanite.Core

/-! Default single-column index size and LogEst arithmetic from SQLite 3.53.4
util.c/build.c. This is statistics-free planning; STAT1/STAT4 are separate work. -/
namespace SQLeanite.SQLite.PlannerCost

def logEst (value : Nat) : Int :=
  if value < 2 then 0 else
    let bits := value.log2
    let leading := if bits ≥ 3 then value >>> (bits - 3) else value <<< (3 - bits)
    Int.ofNat (bits * 10 + ([0, 2, 3, 5, 6, 7, 8, 9] : List Nat)[leading % 8]!)

def add (left right : Int) : Int :=
  let larger := max left right
  let gap := (larger - min left right).toNat
  larger + if gap > 49 then 0 else if gap > 31 then 1 else
    Int.ofNat (([10,10,9,9,8,8,7,7,7,6,6,6,5,5,5,4,4,4,4,3,3,3,3,3,3,2,2,2,2,2,2,2] : List Nat)[gap]!)

/-- Column.szEst is measured in units of roughly four bytes. Empty declared
names retain the no-type size, unlike an explicit BLOB declaration. -/
def columnWeight (column : Core.Column) : Nat :=
  if column.integerPrimaryKey then 1
  else if column.textPrimaryKey then 5
  else if column.declaredType.isEmpty then 1
  else if [.integer, .real, .numeric].contains column.affinity then 1
  else
    let name := column.declaredType.toLower
    let tail := if (name.splitOn "char").length > 1 then (name.splitOn "char").getLast?
      else if (name.splitOn "blob(").length > 1 then (name.splitOn "blob(").getLast? else none
    match tail with
    | none => 5
    | some tail =>
        let digits := tail.toList.dropWhile (fun c => !c.isDigit) |>.takeWhile Char.isDigit
        min 255 (((String.ofList digits).toNat?.getD 0) / 4 + 1)

def tableWidth (schema : Core.Schema) : Int :=
  logEst (4 * ((schema.catalogColumns.map columnWeight).sum + if schema.hasHiddenRowid then 1 else 0))

def indexWidth (schema : Core.Schema) (column : Nat) : Int :=
  logEst (4 * ((schema.columns[column]?.map columnWeight |>.getD 1) + 1))

/-- where.c's index seek/scan estimate and optional table lookup cost. -/
def scan (schema : Core.Schema) (column : Nat) (rows : Int) (covering : Bool) : Int :=
  let seek := logEst 200 - 33
  let rowid := column == schema.primaryKey
  let step := if rowid then rows + 16 else rows + 1 + 15 * indexWidth schema column / tableWidth schema
  let cost := add seek step
  if rowid || covering then cost else add cost (rows + 16)

theorem add_comm (left right : Int) : add left right = add right left := by
  simp [add, Int.max_comm, Int.min_comm]

end SQLeanite.SQLite.PlannerCost
