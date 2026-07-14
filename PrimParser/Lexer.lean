import PrimParser.Run

/-!
# Lexer combinators

Common lexing pieces missing from the core: `symbol`, `signed`, character and
string literals with escapes, and line / block comment skippers. Built on the
existing combinators; no new primitives.
-/

namespace Parser

/-- Parse an exact string and skip trailing whitespace. -/
def symbol (s : String) : Parser Error conditional PUnit := lexeme (string s)

/-- Optional leading `-`, then `p`, as a signed integer. -/
def signed (p : Parser Error conditional Nat) : Parser Error conditional Int := gdo
  let neg ← optional (char '-')
  let n ← p
  return if neg.isSome then -(n : Int) else (n : Int)
  grade_by by simp

/-- Map an escape letter to its character (`\n`, `\t`, `\r`, `\0`, else itself). -/
def escapee : Char → Char
  | 'n' => '\n' | 't' => '\t' | 'r' => '\r' | '0' => '\x00' | c => c

/-- One character, honouring a leading backslash escape. -/
def charLiteral : Parser Error conditional Char :=
  anyChar >>=ᵍ fun c =>
    if c == '\\' then (escapee <$>ᵍ anyChar).relax
    else (ok c : Parser Error fallible Char)

/-- A double-quoted string with backslash escapes. -/
def stringLiteral : Parser Error conditional String := gdo
  dquote
  let cs ← manyTill charLiteral dquote
  return String.ofList cs

/-- Skip `//`-style line comment: the prefix, then everything up to (not incl.) newline. -/
def skipLineComment (pre : String) : Parser Error conditional PUnit := gdo
  string pre
  skipWhile (· != '\n')

/-- Skip a block comment delimited by `opn` and `cls`. -/
def skipBlockComment (opn cls : String) : Parser Error conditional PUnit := gdo
  string opn
  skipUntil (string cls) anyChar

#guard (symbol "let").parsePrefix? "let  x" == some ((), "x")
#guard (signed nat).parse? "-42" == some (-42)
#guard (signed nat).parse? "42" == some 42
#guard stringLiteral.parse? "\"ab\\nc\"" == some "ab\nc"
#guard (gdo skipLineComment "//"; nat).parse? "// hi\n" == none  -- newline left, nat fails
#guard (gdo skipLineComment "//"; anyChar).parse? "//hi\nX" == some '\n'
#guard (gdo skipBlockComment "/*" "*/"; nat).parse? "/* c */7" == some 7

end Parser
