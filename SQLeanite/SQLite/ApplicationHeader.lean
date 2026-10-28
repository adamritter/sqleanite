import SQLeanite.FileFormat.U16Value

/-! Application-owned SQLite header words, separate from table contents.
`pragma.c` uses `sqlite3Atoi`, whose signed-prefix conversion differs from SQL
CAST: no leading whitespace, bounded decimal, and unsigned-prefix hex only. -/
namespace SQLeanite.SQLite.ApplicationHeader

structure Metadata where
  applicationId : FileFormat.U32Value := ⟨0, by omega⟩
  userVersion : FileFormat.U32Value := ⟨0, by omega⟩
  deriving DecidableEq, BEq

structure Schemas where
  main : Metadata := {}
  temporary : Metadata := {}
  deriving DecidableEq, BEq

def supported (name : String) : Bool :=
  name.toLower == "user_version" || name.toLower == "application_id"

def signed (word : FileFormat.U32Value) : Int :=
  if word.val < 2147483648 then Int.ofNat word.val else Int.ofNat word.val - 4294967296

def word (value : Int) : FileFormat.U32Value :=
  ⟨(value % 4294967296).toNat, by
    have nonnegative := Int.emod_nonneg value (by decide : (4294967296 : Int) ≠ 0)
    have bound := Int.emod_lt_of_pos value (by decide : (0 : Int) < 4294967296)
    omega⟩

def decimalDigit (c : Char) : Bool := '0' ≤ c && c ≤ '9'
def hexDigit (c : Char) : Option Nat :=
  if decimalDigit c then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else if 'A' ≤ c && c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
  else none

def decimal (negative : Bool) (chars : List Char) : Int :=
  let digits := chars.takeWhile decimalDigit
  let magnitude := digits.foldl (fun n c => n * 10 + c.toNat - '0'.toNat) 0
  if magnitude ≤ (if negative then 2147483648 else 2147483647) then
    if negative then -(Int.ofNat magnitude) else Int.ofNat magnitude
  else 0

def atoi (source : String) : Int :=
  match source.toList with
  | '-' :: rest => decimal true rest
  | '+' :: rest => decimal false rest
  | '0' :: x :: rest =>
      if (x == 'x' || x == 'X') && (rest.head?.bind hexDigit).isSome then
        let digits := rest.takeWhile (fun c => (hexDigit c).isSome)
        let magnitude := digits.foldl (fun n c => n * 16 + (hexDigit c).getD 0) 0
        if magnitude ≤ 2147483647 then Int.ofNat magnitude else 0
      else decimal false source.toList
  | chars => decimal false chars

def Metadata.get (metadata : Metadata) (name : String) : FileFormat.U32Value :=
  if name.toLower == "user_version" then metadata.userVersion else metadata.applicationId

def Metadata.set (metadata : Metadata) (name : String) (value : FileFormat.U32Value) : Metadata :=
  if name.toLower == "user_version" then { metadata with userVersion := value }
  else { metadata with applicationId := value }

def Schemas.get (schemas : Schemas) (temporary : Bool) : Metadata :=
  if temporary then schemas.temporary else schemas.main

def Schemas.set (schemas : Schemas) (temporary : Bool) (metadata : Metadata) : Schemas :=
  if temporary then { schemas with temporary := metadata } else { schemas with main := metadata }

theorem signed_bounds (value : FileFormat.U32Value) :
    -2147483648 ≤ signed value ∧ signed value ≤ 2147483647 := by
  have bound := value.isLt
  change -2147483648 ≤ (if value.val < 2147483648 then (value.val : Int) else (value.val : Int) - 4294967296) ∧
    (if value.val < 2147483648 then (value.val : Int) else (value.val : Int) - 4294967296) ≤ 2147483647
  split <;> omega

theorem Metadata.get_set (metadata : Metadata) (name : String) (value : FileFormat.U32Value) :
    (metadata.set name value).get name = value := by
  unfold Metadata.set Metadata.get
  split <;> rfl

theorem Schemas.temporary_preserves_main (schemas : Schemas) (metadata : Metadata) :
    (schemas.set true metadata).main = schemas.main := rfl

end SQLeanite.SQLite.ApplicationHeader
