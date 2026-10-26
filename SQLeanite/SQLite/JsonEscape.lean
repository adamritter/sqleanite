import SQLeanite.SQLite.Text

/-! Byte-level SQLite JSON escape decoding, shared by validity and navigation. -/
namespace SQLeanite.SQLite.JsonEscape

def byte (input : Array UInt8) (index : Nat) : Nat := (input[index]?.getD 0).toNat
def digit (c : Nat) : Bool := 48 ≤ c && c ≤ 57
def lineSeparator (input : Array UInt8) (pos : Nat) : Bool :=
  byte input pos == 226 && byte input (pos+1) == 128 &&
    (byte input (pos+2) == 168 || byte input (pos+2) == 169)

def hexInt (c : Nat) : Nat := (c + 9*((c/64)%2)) % 16
def hex4 (input : Array UInt8) (pos : Nat) : Nat :=
  (List.range 4).foldl (fun n i => n*16 + hexInt (byte input (pos+i))) 0

/-- utf.c:sqlite3Utf8ReadLimited decodes at most four bytes without scalar
validation. This differs intentionally from SQL unicode(). -/
def utf8 (input : Array UInt8) (pos finish : Nat) : Nat × Nat := Id.run do
  if pos ≥ finish then return (0, pos)
  let c := byte input pos
  if c < 192 then return (c, pos+1)
  let mut value := if c < 224 then c%32 else if c < 240 then c%16
    else if c < 248 then c%8 else if c < 252 then c%4 else if c < 254 then c%2 else 0
  let mut next := pos+1
  for _ in [0:3] do
    if next < finish && byte input next / 64 == 2 then
      value := value*64 + byte input next % 64
      next := next+1
    else break
  return (value, next)

def continuationEnd (input : Array UInt8) (finish : Nat) : Nat → Nat → Nat
  | 0, pos => pos
  | fuel+1, pos =>
      if pos+1 ≥ finish || byte input pos != 92 then pos
      else if byte input (pos+1) == 10 then continuationEnd input finish fuel (pos+2)
      else if byte input (pos+1) == 13 then
        continuationEnd input finish fuel (pos + if pos+2 < finish && byte input (pos+2) == 10 then 3 else 2)
      else if pos+4 ≤ finish && lineSeparator input (pos+1) then continuationEnd input finish fuel (pos+4)
      else pos

def unescape (input : Array UInt8) (finish : Nat) : Nat → Nat → Nat × Nat
  | 0, _ => (629145, finish)
  | fuel+1, pos =>
      if pos+1 ≥ finish then (629145, finish) else
      let c := byte input (pos+1)
      if c == 117 then
        if pos+6 > finish then (629145, finish) else
        let value := hex4 input (pos+2)
        let low := hex4 input (pos+8)
        if value / 1024 == 54 && pos+12 ≤ finish && byte input (pos+6) == 92 &&
            byte input (pos+7) == 117 && low / 1024 == 55 then
          ((value%1024)*1024 + low%1024 + 65536, pos+12)
        else (value, pos+6)
      else if c == 120 then
        if pos+4 > finish then (629145, finish)
        else (hexInt (byte input (pos+2))*16 + hexInt (byte input (pos+3)), pos+4)
      else if c == 48 then
        (if pos+2 < finish && digit (byte input (pos+2)) then 629145 else 0, pos+2)
      else if [34,39,47,92].contains c then (c, pos+2)
      else match [(98,8),(102,12),(110,10),(114,13),(116,9),(118,11)].find? (fun p => p.1 == c) with
        | some p => (p.2, pos+2)
        | none =>
            let next := continuationEnd input finish (input.size+1) pos
            if next == pos then (629145, pos+2)
            else if next ≥ finish then (0, next)
            else if byte input next == 92 then unescape input finish fuel next
            else utf8 input next finish

theorem unescape_short (input : Array UInt8) (finish fuel pos : Nat)
    (short : finish ≤ pos+1) : unescape input finish (fuel+1) pos = (629145, finish) := by
  simp [unescape, short]

end SQLeanite.SQLite.JsonEscape
