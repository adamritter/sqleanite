import Std

/-! SQLite 3.53.4 QRF's default list-mode byte display. This is a client
formatting boundary, not a change to SQL values or stored TEXT/BLOB bytes. -/
namespace SQLeanite.SQLite.CLI

/-- Stop at NUL and display C0 controls as ^X, except TAB, LF and CR-LF.
Bytes above the ASCII control range pass through without UTF-8 decoding. -/
def listTextBytes : List UInt8 → List UInt8
  | [] => []
  | byte :: rest =>
      if byte == 0 then []
      else if byte ≤ 31 && byte != 9 && byte != 10 &&
          !(byte == 13 && rest.head? == some 10) then
        94 :: (byte + 64) :: listTextBytes rest
      else byte :: listTextBytes rest

theorem listTextBytes_nul (rest : List UInt8) : listTextBytes (0 :: rest) = [] := rfl

theorem listTextBytes_length_le (input : List UInt8) :
    (listTextBytes input).length ≤ 2 * input.length := by
  induction input with
  | nil => simp [listTextBytes]
  | cons byte rest ih =>
      simp only [listTextBytes]
      split
      · simp
      · split <;> simp only [List.length_cons] <;> omega

end SQLeanite.SQLite.CLI
