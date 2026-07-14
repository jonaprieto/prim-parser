import PrimParser.Run

/-!
# Error positions and labels

`Error` is a bare `String`, but `Failure` already records `restSize`, so the
failure offset is recoverable: `pos = |input| - restSize`. `parse` surfaces it,
and `label` / `<?>` attach an "expected ..." message the way megaparsec's `<?>`
does (only when the branch failed *without consuming*, so deeper errors survive).
-/

namespace Parser

variable {α : Type} {ge gc : Necessity}

/-- A parse error over the half-open span `pos..endPos` (character offsets), with
1-based `line`/`col` of `pos` and a message. `token`/`satisfy` fail without
consuming, so `pos` is exactly the offending character; the span covers it (or is
empty at end of input). -/
structure ParseError where
  pos : Nat
  endPos : Nat
  line : Nat
  col : Nat
  msg : String
  deriving Repr, BEq

/-- Run `p` on a `String`, reporting the failure span, line and column on error. -/
def parse (p : Parser Error ⟨ge, gc⟩ α) (s : String) : Except ParseError α :=
  let len := s.toList.length
  (p.run (ofString s)).handle
    (fun _ f =>
      let pos := len - f.restSize
      let before := s.toList.take pos
      .error { pos := pos
               endPos := min (pos + 1) len
               line := (before.count '\n') + 1
               col := (before.reverse.takeWhile (· != '\n')).length + 1
               msg := f.error })
    (fun _ r => .ok r.result)

/-- Render a parse error as `line:col: msg`, the offending source line, and a caret
under the failing span. -/
def ParseError.pretty (e : ParseError) (src : String) : String :=
  let srcLine := (src.splitOn "\n").getD (e.line - 1) ""
  let width := max 1 (e.endPos - e.pos)
  let caret := String.ofList (List.replicate (e.col - 1) ' ') ++ String.ofList (List.replicate width '^')
  s!"{e.line}:{e.col}: {e.msg}\n{srcLine}\n{caret}"

/-- Replace `p`'s error message with `expected <name>`. Unconditional (fits the
default full-backtracking `<|>`); use for turning primitive failures into
readable expectations. -/
def label (name : String) (p : Parser Error ⟨ge, gc⟩ α) : Parser Error ⟨ge, gc⟩ α where
  run t := (p.run t).handle
    (fun h f => Outcome.throwFailure (h := h) { f with error := "expected " ++ name })
    (fun h r => Outcome.ofSuccess (c := h) r)

infixl:10 " <?> " => fun p name => label name p

private def errIs (e : Except ParseError α) (p : Nat) (m : String) : Bool :=
  match e with | .error err => err.pos == p && err.msg == m | .ok _ => false

/-- 1-based line/col of a parse error, or none on success. -/
private def lineCol (e : Except ParseError α) : Option (Nat × Nat) :=
  match e with | .error err => some (err.line, err.col) | .ok _ => none

#guard errIs (nat.parse "abc") 0 "fail"
#guard errIs ((nat <?> "number").parse "abc") 0 "expected number"
#guard (nat.parse "42").toOption == some 42
#guard errIs ((gdo let a ← nat; char 'x'; return a).parse "12!") 2 "fail"
-- line/col: fail at the 'x' on line 3, column 2 (after two lines and a leading digit)
#guard lineCol ((gdo skipMany (satisfy (· != 'x')); char '!').parse "ab\ncd\n1x") == some (3, 2)
#guard lineCol (nat.parse "abc") == some (1, 1)
-- expected-set: <||> merges both branches' messages
#guard errIs (((char 'a' <?> "a") <||> (char 'b' <?> "b")).parse "c") 0 "expected a or expected b"

-- pretty: line:col + source line + caret under the offending span
private def prettyOf (e : Except ParseError α) (src : String) : String :=
  match e with | .error err => err.pretty src | .ok _ => "ok"
#guard prettyOf ((gdo let a ← nat; char 'x'; return a).parse "12!") "12!" == "1:3: fail\n12!\n  ^"

end Parser
