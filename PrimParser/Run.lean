import PrimParser.Basic

/-!
# Ergonomic entry points

Running a parser directly needs a length-indexed `Text n`, built via `ofString`.
These wrappers take a plain `String`.
-/

namespace Parser

variable {α ε : Type} {ge gc : Necessity}

/-- Run `p` on a `String`, returning the parsed value on success. -/
def parse? (p : Parser ε ⟨ge, gc⟩ α) (s : String) : Option α :=
  p.runResult? (ofString s)

/-- Run `p` on a `String`, returning the value and the unconsumed suffix. -/
def parsePrefix? (p : Parser ε ⟨ge, gc⟩ α) (s : String) : Option (α × String) :=
  (p.runOption (ofString s)).map fun r => (r.result, String.ofList r.restText.toList)

/-- Run `p` and require it to consume the whole input (`p` then `eof`). -/
def parseAll? (p : Parser Error ⟨ge, gc⟩ α) (s : String) : Option α :=
  (gdo let a ← p; eof; return a).parse? s

#guard nat.parse? "123" == some 123
#guard nat.parsePrefix? "123abc" == some (123, "abc")
#guard nat.parseAll? "123abc" == none      -- trailing input rejected
#guard nat.parseAll? "123" == some 123

end Parser

