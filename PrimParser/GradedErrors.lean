import PrimParser.Graded
import PrimParser.Errors

/-!
# Positional error reporting for the deep backend

The shallow `Parser` reconstructs errors from the parse *witness* (`restSize`), at
zero happy-path cost. The deep fuel interpreter already tracks the analogous datum:
`Res.err` carries the **furthest byte position** reached (`alt` keeps the max). So
the deep backend gets the *same* positional `Parser.ParseError` — line/col + caret —
by post-processing that position, again paying nothing on the success path.

Parity note: this matches the shallow backend's *positional* reporting (offset →
line/col → pretty caret). Message-level features (`label`/`<?>`, expected-set
merging) would need `Res.err` to carry a message and a `label` GADT node; not done
here. -/

namespace Graded
open Parser

/-- 1-based line/column of a byte offset within `bytes`. -/
def byteLineCol (bytes : ByteArray) (pos : Nat) : Nat × Nat :=
  let before := bytes.toList.take pos
  ((before.filter (· == 10)).length + 1,
   (before.reverse.takeWhile (· != 10)).length + 1)

/-- Run a deep grammar on a `String`, reporting a `Parser.ParseError` (identical in
shape to `Parser.parse`) built from the furthest byte position on failure. -/
def parseLoc (top : G Nat conditional Nat) (s : String) : Except ParseError Nat :=
  let bytes := s.toUTF8
  let mk (e : Nat) (msg : String) : ParseError :=
    let (line, col) := byteLineCol bytes e
    { pos := e, endPos := min (e + 1) bytes.size, line, col, msg }
  match G.run bytes top (bytes.size * 64 + 64) top 0 with
  | .ok v pos => if pos ≥ bytes.size then .ok v else .error (mk pos "unexpected trailing input")
  | .err e    => .error (mk e "parse error")

/-- `parse` then render the error the same way the shallow backend does. -/
def parsePretty (top : G Nat conditional Nat) (s : String) : Except String Nat :=
  (parseLoc top s).mapError (·.pretty s)

/-- Grammar `'\n'` then a number: fails on line 2 when the number is missing. -/
private def eolNat : G Nat conditional Nat := .seqR (.lit (ch '\n')) .nat

-- deep backend reconstructs line/col + caret, matching `Parser.parse`:
#guard (parseLoc gnat "abc").toOption == none
#guard (match parseLoc gnat "abc"   with | .error e => (e.line, e.col) | _ => (0, 0)) == (1, 1)
#guard (match parseLoc eolNat "\nab" with | .error e => (e.line, e.col) | _ => (0, 0)) == (2, 1)
#guard (match parsePretty gnat "abc" with | .error s => s | .ok _ => "") == "1:1: parse error\nabc\n^"
#guard (parseLoc gnat "42").toOption == some 42

end Graded
