import SQLeanite.SQLite.ColumnType
import SQLeanite.SQLite.Type

/-! CAST uses parse.y typetoken and expr.c/sqlite3Dequote, independently of
column metadata normalization. In particular, an empty CAST type is NUMERIC,
and quoting ends the effective name at the first closing quote. -/
namespace SQLeanite.SQLite.CastType

def name (source : String) : String :=
  match lex source with
  | .ok tokens => match (ColumnType.significant tokens.toList).head? with
      | some (.quotedIdent name _) | some (.string name) => name
      | _ => source
  | .error _ => source

def check (source : String) : Except String String :=
  if ColumnType.valid source then .ok (name source) else .error "invalid CAST type syntax"

def affinity (name : String) : Affinity :=
  if name.isEmpty then .numeric else typeAffinity name

theorem check_valid (source result : String) (accepted : check source = .ok result) :
    ColumnType.valid source = true := by
  unfold check at accepted
  split at accepted
  · assumption
  · contradiction

theorem check_name (source result : String) (accepted : check source = .ok result) :
    result = name source := by
  unfold check at accepted
  split at accepted
  · cases accepted; rfl
  · contradiction

theorem affinity_empty : affinity "" = .numeric := rfl

theorem affinity_nonempty (name : String) (nonempty : name.isEmpty = false) :
    affinity name = typeAffinity name := by simp [affinity, nonempty]

end SQLeanite.SQLite.CastType
