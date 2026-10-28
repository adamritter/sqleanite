import SQLeanite.Core.Table

namespace SQLeanite.CoreAutomaticIndex

/-- The table's retained declaration, rather than the index-name prefix alone,
identifies automatic UNIQUE and non-rowid PRIMARY KEY indexes. -/
def find (table : Core.Table) (name : String) : Option Core.Index :=
  (CoreSchemaSQL.automaticIndexes table.schema table.catalogSQL).bind fun indexes =>
    indexes.find? (fun index => index.name == name)

def contains (table : Core.Table) (index : Core.Index) : Bool :=
  index.isImplicitPrimary table.schema || find table index.name == some index

def primary (table : Core.Table) (index : Core.Index) : Bool :=
  contains table index && !index.unique && table.schema.hasHiddenRowid &&
    index.column == table.schema.declaredPrimaryKey

theorem contains_implicit (table : Core.Table) (index : Core.Index)
    (implicit : index.isImplicitPrimary table.schema = true) : contains table index = true := by
  simp [contains, implicit]

theorem contains_declared (table : Core.Table) (index : Core.Index)
    (ordinary : index.isImplicitPrimary table.schema = false) :
    contains table index = true ↔ find table index.name = some index := by
  simp [contains, ordinary]

end SQLeanite.CoreAutomaticIndex
