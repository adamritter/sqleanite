import SQLeanite.CoreEngine
import SQLeanite.PhysicalQuery
import SQLeanite.SQLite.Collation

namespace SQLeanite
namespace QuerySemantics

/-- Rows in the denotational semantics retain join structure. This makes the
scope of a predicate explicit and prevents an outer-side predicate from being
silently treated as an inner-side predicate. -/
inductive Row where
  | values (cells : List Core.Value)
  | joined (left right : Row)
  deriving Inhabited, BEq, DecidableEq

inductive ColumnPath where
  | cell (index : Nat)
  | left (path : ColumnPath)
  | right (path : ColumnPath)
  deriving Repr, DecidableEq

def Row.lookup : Row → ColumnPath → Core.Value
  | .values cells, .cell index => cells[index]?.getD .null
  | .joined left _, .left path => left.lookup path
  | .joined _ right, .right path => right.lookup path
  | _, _ => .null

def sqlEquals (left right : Core.Value) : Truth :=
  PhysicalQuery.sqlEquals left right

/-- SQL truth conversion shared with executable joined predicates, including
numeric prefixes in stored TEXT/BLOB values. -/
def valueTruth (value : Core.Value) : Truth := SQLite.PhysicalAffinity.truth value

/-- A comparison operand in the denotational language. Unlike the original
single-table predicate constructors, this form can name both sides of a join.
Keeping literals here as well gives the live join bridge one exact target for
all of `CoreJoin.Operand`. -/
inductive Operand where
  | column (path : ColumnPath)
  | coercedColumn (affinity : SQLite.Affinity) (path : ColumnPath)
  | literal (value : Core.Value)

def Operand.value : Operand → Row → Core.Value
  | .column path, row => row.lookup path
  | .coercedColumn affinity path, row =>
      SQLite.PhysicalAffinity.comparison affinity (row.lookup path)
  | .literal value, _ => value

inductive Predicate where
  | constant (truth : Truth)
  | truthy (column : ColumnPath)
  | equals (column : ColumnPath) (value : Core.Value)
  | notEquals (column : ColumnPath) (value : Core.Value)
  | compare (operation : PhysicalQuery.Comparison) (column : ColumnPath)
      (value : Core.Value)
  | operandsEqual (left right : Operand)
  | operandsNotEqual (left right : Operand)
  | operandsCompare (operation : PhysicalQuery.Comparison) (left right : Operand)
  | operandTruthy (operand : Operand)
  | operandsEqualCollated (kind : SQLite.Collation.Kind) (left right : Operand)
  | operandsCompareCollated (kind : SQLite.Collation.Kind) (operation : PhysicalQuery.Comparison) (left right : Operand)
  | operandIsNull (operand : Operand)
  | isNull (column : ColumnPath)
  | not (predicate : Predicate)
  | and (left right : Predicate)
  | or (left right : Predicate)
  | onLeft (predicate : Predicate)
  | onRight (predicate : Predicate)

def Predicate.eval : Predicate → Row → Truth
  | .operandsEqualCollated kind left right, row =>
      SQLite.Collation.sqlEquals kind (left.value row) (right.value row)
  | .operandsCompareCollated kind operation left right, row =>
      SQLite.Collation.sqlCompare kind operation (left.value row) (right.value row)
  | .constant truth, _ => truth
  | .truthy column, row => valueTruth (row.lookup column)
  | .equals column value, row => sqlEquals (row.lookup column) value
  | .notEquals column value, row => Truth.not (sqlEquals (row.lookup column) value)
  | .compare operation column value, row =>
      PhysicalQuery.sqlCompare operation (row.lookup column) value
  | .operandsEqual left right, row => sqlEquals (left.value row) (right.value row)
  | .operandsNotEqual left right, row =>
      Truth.not (sqlEquals (left.value row) (right.value row))
  | .operandsCompare operation left right, row =>
      PhysicalQuery.sqlCompare operation (left.value row) (right.value row)
  | .operandTruthy operand, row => valueTruth (operand.value row)
  | .operandIsNull operand, row => if operand.value row = .null then .true else .false
  | .isNull column, row => if row.lookup column = .null then .true else .false
  | .not predicate, row => Truth.not (predicate.eval row)
  | .and left right, row => Truth.and (left.eval row) (right.eval row)
  | .or left right, row => Truth.or (left.eval row) (right.eval row)
  | .onLeft predicate, .joined left _ => predicate.eval left
  | .onRight predicate, .joined _ right => predicate.eval right
  | .onLeft _, _ | .onRight _, _ => .unknown

def whereRows (predicate : Predicate) (rows : List Row) : List Row :=
  rows.filter fun row => predicate.eval row == .true

def joinRows (left right : List Row) : List Row :=
  left.flatMap fun leftRow => right.map fun rightRow => .joined leftRow rightRow

/-- Denotation of a left outer cross join. An empty right input contributes one
NULL-shaped placeholder row. Full outer-join column widths are outside the MVP;
the constructor is present to state the 3VL counterexample precisely. -/
def leftJoinRows (left right : List Row) : List Row :=
  if right.isEmpty then left.map fun leftRow => .joined leftRow (.values [])
  else joinRows left right

def leftOuterForRowsWith (predicate : Predicate) (nullRight left : Row)
    (right : List Row) : List Row :=
  let matchingRows := (right.map fun row => .joined left row).filter
    (fun row => predicate.eval row == .true)
  if matchingRows.isEmpty then [.joined left nullRight] else matchingRows

def leftOuterForRows (predicate : Predicate) (left : Row)
    (right : List Row) : List Row :=
  leftOuterForRowsWith predicate (.values []) left right

def leftOuterOnRowsWith (predicate : Predicate) (nullRight : Row)
    (left right : List Row) : List Row :=
  left.flatMap fun row => leftOuterForRowsWith predicate nullRight row right

def leftOuterOnRows (predicate : Predicate) (left right : List Row) : List Row :=
  leftOuterOnRowsWith predicate (.values []) left right

/-- COUNT aggregation represented as a multiplicity-valued grouped bag: the
group key occurs once for every contributing input occurrence. -/
def groupCountRows (key : Row → Row) (rows : List Row) : List Row :=
  rows.map key

/-- Natural-weight SUM aggregation represented in the same grouped-bag form:
the multiplicity of a group key is the sum of the input measures. -/
def groupSumRows (key : Row → Row) (measure : Row → Nat)
    (rows : List Row) : List Row :=
  rows.flatMap fun row => List.replicate (measure row) (key row)

/-- Duplicate-preserving `INTERSECT ALL`: each right occurrence can match one
left occurrence. -/
def bagIntersect [DecidableEq α] : List α → List α → List α
  | [], _ => []
  | value :: values, right =>
      if value ∈ right then value :: bagIntersect values (right.erase value)
      else bagIntersect values right

/-- Duplicate-preserving `EXCEPT ALL`: right occurrences cancel left
occurrences one-for-one. -/
def bagExcept [DecidableEq α] : List α → List α → List α
  | [], _ => []
  | value :: values, right =>
      if value ∈ right then bagExcept values (right.erase value)
      else value :: bagExcept values right

inductive Projection where
  | identity
  | left
  | right
  deriving Repr, DecidableEq

def Projection.apply : Projection → Row → Row
  | .identity, row => row
  | .left, .joined leftRow _ => leftRow
  | .right, .joined _ rightRow => rightRow
  | _, row => row

inductive Plan where
  | table (name : String)
  | rows (rows : List Row)
  | unionAll (left right : Plan)
  | intersectAll (left right : Plan)
  | exceptAll (left right : Plan)
  | distinct (input : Plan)
  | filter (predicate : Predicate) (input : Plan)
  | project (projection : Projection) (input : Plan)
  | innerJoin (left right : Plan)
  | leftOuterJoin (left right : Plan)
  | leftOuterOn (predicate : Predicate) (left right : Plan)
  | leftOuterOnWith (predicate : Predicate) (nullRight : Row) (left right : Plan)
  | groupCount (key : Row → Row) (input : Plan)
  | groupSum (key : Row → Row) (measure : Row → Nat) (input : Plan)

/-- Rows of a named table, embedded into the denotational row type.

Stated over `Core.Database`, the database the verified engine actually
executes. It previously used the legacy interpreter's `Database`, so the
optimizer soundness theorems were about a structure the Core path never
touches -- the same defect as proving P2 only for `Engine.evalIndex`. -/
def tableRows (database : Core.Database) (name : String) : List Row :=
  match database.findTable? name with
  | none => []
  | some table => table.rows.map fun row => .values row.values

def evalPlan (database : Core.Database) : Plan → List Row
  | .table name => tableRows database name
  | .rows rows => rows
  | .unionAll left right => evalPlan database left ++ evalPlan database right
  | .intersectAll left right =>
      bagIntersect (evalPlan database left) (evalPlan database right)
  | .exceptAll left right =>
      bagExcept (evalPlan database left) (evalPlan database right)
  | .distinct input => Core.deduplicate (evalPlan database input)
  | .filter predicate input => whereRows predicate (evalPlan database input)
  | .project projection input => (evalPlan database input).map projection.apply
  | .innerJoin left right => joinRows (evalPlan database left) (evalPlan database right)
  | .leftOuterJoin left right =>
      leftJoinRows (evalPlan database left) (evalPlan database right)
  | .leftOuterOn predicate left right =>
      leftOuterOnRows predicate (evalPlan database left) (evalPlan database right)
  | .leftOuterOnWith predicate nullRight left right =>
      leftOuterOnRowsWith predicate nullRight
        (evalPlan database left) (evalPlan database right)
  | .groupCount key input => groupCountRows key (evalPlan database input)
  | .groupSum key measure input =>
      groupSumRows key measure (evalPlan database input)

/-- An ORDER BY term is a path into the denotational row. -/
structure OrderTerm where
  column : ColumnPath
  descending : Bool := false
  deriving Repr, DecidableEq

private def compareRows : List OrderTerm → Row → Row → Ordering
  | [], _, _ => .eq
  | term :: terms, left, right =>
      let order := PhysicalQuery.compareValue
        (left.lookup term.column) (right.lookup term.column)
      let order := if term.descending then order.swap else order
      if order == .eq then compareRows terms left right else order

private def insertOrdered (terms : List OrderTerm) (row : Row) : List Row → List Row
  | [] => [row]
  | candidate :: rows =>
      if compareRows terms row candidate == .lt then row :: candidate :: rows
      else candidate :: insertOrdered terms row rows

private def orderRows (terms : List OrderTerm) (rows : List Row) : List Row :=
  rows.foldl (fun ordered row => insertOrdered terms row ordered) []

structure Select where
  plan : Plan
  orderBy : List OrderTerm := []
  limit : Option Nat := none

def eval (database : Core.Database) (query : Select) : List Row :=
  let rows := evalPlan database query.plan
  let rows := if query.orderBy.isEmpty then rows else orderRows query.orderBy rows
  match query.limit with
  | none => rows
  | some limit => rows.take limit

def BagEq (left right : List Row) : Prop := left.Perm right

end QuerySemantics
end SQLeanite
