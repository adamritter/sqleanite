import SQLeanite.Value

namespace SQLeanite
namespace KRelation

/-!
# Multiplicity-valued SQL bag semantics

A relation maps each row to its natural-number multiplicity. This makes SQL
duplicate behavior algebraic rather than encoding it through list order.
Finite `domain` lists are supplied only where projection or aggregation must
sum over source rows.
-/

abbrev Relation (Row : Type) := Row → Nat

def empty : Relation Row := fun _ => 0
def unionAll (left right : Relation Row) : Relation Row :=
  fun row => left row + right row
def intersect (left right : Relation Row) : Relation Row :=
  fun row => min (left row) (right row)
def except (left right : Relation Row) : Relation Row :=
  fun row => left row - right row
def distinct (relation : Relation Row) : Relation Row :=
  fun row => if relation row = 0 then 0 else 1

/-- WHERE retains exactly TRUE; FALSE and UNKNOWN both contribute zero
multiplicity. -/
def select (predicate : Row → Truth) (relation : Relation Row) : Relation Row :=
  fun row => if predicate row = .true then relation row else 0

def join (left : Relation Left) (right : Relation Right) :
    Relation (Left × Right) :=
  fun row => left row.1 * right row.2

def swap (relation : Relation (Left × Right)) : Relation (Right × Left) :=
  fun row => relation (row.2, row.1)

def projectSum [DecidableEq Output] (projection : Input → Output)
    (relation : Relation Input) (output : Output) : List Input → Nat
  | [] => 0
  | input :: inputs =>
      (if projection input = output then relation input else 0) +
        projectSum projection relation output inputs

def project [DecidableEq Output] (domain : List Input) (projection : Input → Output)
    (relation : Relation Input) : Relation Output :=
  fun output => projectSum projection relation output domain

def groupCount [DecidableEq Group] (domain : List Row) (key : Row → Group)
    (relation : Relation Row) : Relation Group :=
  project domain key relation

def groupSumRows [DecidableEq Group] (key : Row → Group)
    (measure : Row → Nat) (relation : Relation Row) (group : Group) :
    List Row → Nat
  | [] => 0
  | row :: rows =>
      (if key row = group then relation row * measure row else 0) +
        groupSumRows key measure relation group rows

def groupSum [DecidableEq Group] (domain : List Row) (key : Row → Group)
    (measure : Row → Nat) (relation : Relation Row) : Relation Group :=
  fun group => groupSumRows key measure relation group domain

@[ext] theorem Relation.ext {left right : Relation Row}
    (pointwise : ∀ row, left row = right row) : left = right := by
  funext row
  exact pointwise row

theorem unionAll_comm (left right : Relation Row) :
    unionAll left right = unionAll right left := by
  apply Relation.ext
  intro row
  exact Nat.add_comm _ _

theorem unionAll_assoc (first second third : Relation Row) :
    unionAll (unionAll first second) third =
      unionAll first (unionAll second third) := by
  apply Relation.ext
  intro row
  exact Nat.add_assoc _ _ _

theorem intersect_comm (left right : Relation Row) :
    intersect left right = intersect right left := by
  apply Relation.ext
  intro row
  exact Nat.min_comm _ _

theorem except_self (relation : Relation Row) :
    except relation relation = empty := by
  apply Relation.ext
  intro row
  exact Nat.sub_self _

theorem distinct_idempotent (relation : Relation Row) :
    distinct (distinct relation) = distinct relation := by
  apply Relation.ext
  intro row
  by_cases zero : relation row = 0 <;> simp [distinct, zero]

theorem select_unionAll (predicate : Row → Truth)
    (left right : Relation Row) :
    select predicate (unionAll left right) =
      unionAll (select predicate left) (select predicate right) := by
  apply Relation.ext
  intro row
  by_cases passes : predicate row = .true <;>
    simp [select, unionAll, passes]

theorem select_unknown (relation : Relation Row) :
    select (fun _ => .unknown) relation = empty := by
  apply Relation.ext
  intro row
  rfl

theorem join_unionAll_left (first second : Relation Left)
    (right : Relation Right) :
    join (unionAll first second) right =
      unionAll (join first right) (join second right) := by
  apply Relation.ext
  intro row
  exact Nat.add_mul _ _ _

theorem join_unionAll_right (left : Relation Left)
    (first second : Relation Right) :
    join left (unionAll first second) =
      unionAll (join left first) (join left second) := by
  apply Relation.ext
  intro row
  exact Nat.mul_add _ _ _

theorem swap_join (left : Relation Left) (right : Relation Right) :
    swap (join left right) = join right left := by
  apply Relation.ext
  intro row
  exact Nat.mul_comm _ _

theorem project_unionAll [DecidableEq Output] (domain : List Input)
    (projection : Input → Output) (left right : Relation Input) :
    project domain projection (unionAll left right) =
      unionAll (project domain projection left)
        (project domain projection right) := by
  apply Relation.ext
  intro output
  induction domain with
  | nil => rfl
  | cons input inputs induction =>
      by_cases selected : projection input = output
      · simp [project, projectSum, selected, unionAll] at induction ⊢
        omega
      · simp [project, projectSum, selected, unionAll] at induction ⊢
        exact induction

theorem groupCount_unionAll [DecidableEq Group] (domain : List Row)
    (key : Row → Group) (left right : Relation Row) :
    groupCount domain key (unionAll left right) =
      unionAll (groupCount domain key left) (groupCount domain key right) :=
  project_unionAll domain key left right

theorem groupSum_unionAll [DecidableEq Group] (domain : List Row)
    (key : Row → Group) (measure : Row → Nat)
    (left right : Relation Row) :
    groupSum domain key measure (unionAll left right) =
      unionAll (groupSum domain key measure left)
        (groupSum domain key measure right) := by
  apply Relation.ext
  intro group
  induction domain with
  | nil => rfl
  | cons row rows induction =>
      by_cases selected : key row = group
      · simp [groupSum, groupSumRows, selected, unionAll] at induction ⊢
        rw [Nat.add_mul]
        rw [induction]
        omega
      · simp [groupSum, groupSumRows, selected, unionAll] at induction ⊢
        exact induction

end KRelation
end SQLeanite
