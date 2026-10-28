
/-! Preserve source text while separating the admitted SQL statements. Quoted
text and comments protect their semicolons; each resulting statement must still
pass the independent certified lexer/parser before it can execute. -/
namespace SQLeanite.SQLite.Script

inductive Mode where
  | plain | dash | slash | single | double | bracket | backtick | line | block | star
  deriving DecidableEq, Repr

/-- The eight-state completion grammar from the pinned complete.c. Whitespace
is ignored; a trigger ends only at the SEMI END SEMI token sequence. -/
inductive Phase where
  | invalid | start | normal | explain | create | trigger | bodySemi | triggerEnd
  deriving DecidableEq, Repr

inductive CompletionToken where
  | semi | other | explain | create | temp | trigger | end_
  deriving DecidableEq, Repr

def advancePhase : Phase → CompletionToken → Phase
  | .invalid, token | .start, token => match token with
      | .semi => .start | .explain => .explain | .create => .create | _ => .normal
  | .normal, .semi => .start
  | .normal, _ => .normal
  | .explain, .semi => .start
  | .explain, .other => .explain
  | .explain, .create => .create
  | .explain, _ => .normal
  | .create, .semi => .start
  | .create, .temp => .create
  | .create, .trigger => .trigger
  | .create, _ => .normal
  | .trigger, .semi => .bodySemi
  | .trigger, _ => .trigger
  | .bodySemi, .semi => .bodySemi
  | .bodySemi, .end_ => .triggerEnd
  | .bodySemi, _ => .trigger
  | .triggerEnd, .semi => .start
  | .triggerEnd, _ => .trigger

structure Completion where
  phase : Phase := .invalid
  word : List Char := []

def wordToken (word : List Char) : CompletionToken :=
  match (String.ofList word.reverse).toLower with
  | "explain" => .explain | "create" => .create
  | "temp" | "temporary" => .temp | "trigger" => .trigger | "end" => .end_
  | _ => .other

def Completion.flush (completion : Completion) : Completion :=
  if completion.word.isEmpty then completion
  else { phase := advancePhase completion.phase (wordToken completion.word) }

def wordChar (char : Char) : Bool :=
  char.isAlphanum || char == '_' || char == '$' || char.toNat ≥ 128

def Completion.ordinary (completion : Completion) (char : Char) : Completion :=
  if wordChar char then { completion with word := char :: completion.word }
  else
    let completion := completion.flush
    if char.isWhitespace || char == '-' || char == '/' then completion
    else { phase := advancePhase completion.phase (if char == ';' then .semi else .other) }

/-- Delay '-' and '/' until their next byte distinguishes a comment from an
operator. Quotes contribute OTHER once; their contents never become keywords. -/
def Completion.observe (completion : Completion) (mode : Mode) (char : Char) : Completion :=
  match mode with
  | .plain => completion.ordinary char
  | .dash => if char == '-' then completion else
      ({ completion with phase := advancePhase completion.phase .other }).ordinary char
  | .slash => if char == '*' then completion else
      ({ completion with phase := advancePhase completion.phase .other }).ordinary char
  | _ => completion

theorem trigger_body_semicolon : advancePhase .trigger .semi = .bodySemi := rfl

theorem trigger_final_semicolon : advancePhase .triggerEnd .semi = .start := rfl

structure Scanner where
  mode : Mode := .plain
  completion : Completion := {}
  reversed : List Char := []
  completed : List (List Char) := []

def ordinary (char : Char) : Mode :=
  if char == '-' then .dash else if char == '/' then .slash
  else if char == '\'' then .single else if char == '"' then .double
  else if char == '[' then .bracket else if char == '`' then .backtick else .plain

def transition (mode : Mode) (char : Char) : Mode :=
  match mode with
  | .plain => ordinary char
  | .dash => if char == '-' then .line else ordinary char
  | .slash => if char == '*' then .block else ordinary char
  | .single => if char == '\'' then .plain else .single
  | .double => if char == '"' then .plain else .double
  | .bracket => if char == ']' then .plain else .bracket
  | .backtick => if char == '`' then .plain else .backtick
  | .line => if char == '\n' then .plain else .line
  | .block => if char == '*' then .star else .block
  | .star => if char == '/' then .plain else if char == '*' then .star else .block

def step (scanner : Scanner) (char : Char) : Scanner :=
  let reversed := char :: scanner.reversed
  let completion := scanner.completion.observe scanner.mode char
  if (scanner.mode == .plain || scanner.mode == .dash || scanner.mode == .slash) && char == ';' &&
      completion.phase == .start then
    { completed := reversed.reverse :: scanner.completed }
  else { scanner with mode := transition scanner.mode char, completion, reversed }

def contents (scanner : Scanner) : List Char :=
  scanner.completed.reverse.flatten ++ scanner.reversed.reverse

theorem step_contents (scanner : Scanner) (char : Char) :
    contents (step scanner char) = contents scanner ++ [char] := by
  unfold step
  dsimp only
  split <;> simp [contents, List.reverse_cons, List.append_assoc]

theorem contents_scan (input : List Char) (scanner : Scanner) :
    contents (input.foldl step scanner) = contents scanner ++ input := by
  induction input generalizing scanner with
  | nil => simp
  | cons char rest ih =>
      simp only [List.foldl_cons, ih, step_contents]
      simp [List.append_assoc]

def splitChars (input : List Char) : List (List Char) :=
  let finalState := input.foldl step {}
  finalState.completed.reverse ++ [finalState.reversed.reverse]

theorem splitChars_flatten (input : List Char) : (splitChars input).flatten = input := by
  simp only [splitChars, List.flatten_append, List.flatten_singleton]
  change contents (input.foldl step {}) = input
  rw [contents_scan]
  rfl

def split (sql : String) : List String := (splitChars sql.toList).map String.ofList

theorem split_preserves_source (sql : String) :
    ((split sql).map String.toList).flatten = sql.toList := by
  simp [split, List.map_map, splitChars_flatten]

theorem semicolon_in_group (scanner : Scanner)
    (grouped : scanner.mode = .single ∨ scanner.mode = .double ∨ scanner.mode = .bracket ∨
      scanner.mode = .backtick ∨ scanner.mode = .line ∨ scanner.mode = .block ∨ scanner.mode = .star) :
    (step scanner ';').completed = scanner.completed := by
  rcases grouped with same | same | same | same | same | same | same <;> simp [step, same]

end SQLeanite.SQLite.Script
