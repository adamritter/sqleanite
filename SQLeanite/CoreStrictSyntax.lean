import SQLeanite.PhysicalCodec.PageSize
import SQLeanite.SQLite.ColumnType
import SQLeanite.Syntax.TableConstraintDef

/-! STRICT is a retained type program. ANY lowers to the Core's ordinary
no-affinity storage column; its public declared name remains in the program. -/
namespace SQLeanite.CoreStrictSyntax

abbrev Spec := String × String

def typeName (table : String) (column : ColumnDef) : Except String String :=
  match SQLite.ColumnType.standard column.declaredType with
  | some name => pure name
  | none => if column.declaredType.isEmpty then .error s!"missing datatype for {table}.{column.name}"
    else .error s!"unknown datatype for {table}.{column.name}: \"{SQLite.ColumnType.name column.declaredType}\""

def specs (table : String) (columns : Array ColumnDef) : Except String (List Spec) :=
  columns.toList.mapM fun column => do return (column.name, ← typeName table column)

def lowerColumn (table : String) (constraints : Array TableConstraintDef) (column : ColumnDef) : Except String ColumnDef := do
  let typ ← typeName table column
  let primary := column.primaryKey || constraints.any (fun constraint =>
    constraint.primaryKey && constraint.columns.any (fun name => name.toLower == column.name.toLower))
  let compound := constraints.any (fun constraint => constraint.primaryKey && constraint.columns.size > 1 &&
    constraint.columns.any (fun name => name.toLower == column.name.toLower))
  return { column with
    declaredType := if typ == "ANY" then "" else column.declaredType
    notNull := column.notNull || (primary && (typ != "INTEGER" || compound)) }

theorem lowerColumn_any (table : String) (constraints : Array TableConstraintDef) (column : ColumnDef)
    (typed : typeName table column = .ok "ANY") :
    (lowerColumn table constraints column).map (·.declaredType) = .ok "" := by
  simp [lowerColumn, typed, bind, Except.bind, Except.map, pure, Except.pure]

def lower (table : String) (columns : Array ColumnDef) (constraints : Array TableConstraintDef) : Except String (Array ColumnDef) :=
  columns.mapM (lowerColumn table constraints)

def accepts (name : String) (value : PhysicalCodec.Value) : Bool :=
  match value with
  | .null => true
  | _ => match name, value with
    | "ANY", _ | "INT", .integer _ | "INTEGER", .integer _ | "REAL", .realBits _ |
        "TEXT", .text _ | "BLOB", .blob _ => true
    | _, _ => false

def storageClass : PhysicalCodec.Value → String
  | .null => "NULL" | .integer _ => "INT" | .realBits _ => "REAL" | .text _ => "TEXT" | .blob _ => "BLOB"

def valid (columns : List Spec) (values : List PhysicalCodec.Value) : Bool :=
  (columns.zip values).all fun (spec, value) => accepts spec.2 value

def require (table : String) (columns : List Spec) (values : List PhysicalCodec.Value) : Except String Unit :=
  match (columns.zip values).find? (fun (spec, value) => !accepts spec.2 value) with
  | none => pure ()
  | some (spec, value) => .error s!"cannot store {storageClass value} value in {spec.2} column {table}.{spec.1}"

theorem accepts_any (value : PhysicalCodec.Value) : accepts "ANY" value = true := by
  cases value <;> rfl

theorem require_checked {table : String} {columns : List Spec} {values : List PhysicalCodec.Value}
    (success : require table columns values = .ok ()) : valid columns values = true := by
  unfold require at success
  split at success
  · next absent =>
      unfold valid
      rw [List.all_eq_true]
      intro pair member
      have kept := List.find?_eq_none.mp absent pair member
      simpa using kept
  · contradiction

end SQLeanite.CoreStrictSyntax
