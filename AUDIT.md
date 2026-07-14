# prim-parser audit

Scope: the `PrimParser/` library (core + combinators + proofs). Method: automated
escape-hatch and axiom sweeps, plus manual review of runtime safety, the grade
discipline, and behaviour on untrusted input. Commit: branch
`feature/generic-tokens-and-perf`.

## Soundness — clean

- No `sorry`, `axiom`, `unsafe`, `native_decide`, `panic`, or `get!` anywhere in
  `PrimParser/`. The only `partial` is `expandGDoBlock`, the `gdo` **macro**
  (compile-time syntax, not a parser).
- Every public definition depends only on the mathlib-baseline axioms
  (`propext`, `Classical.choice`, `Quot.sound`); some (`token`, `anyToken`) need
  even fewer. No `sorryAx`, no `Lean.ofReduceBool`.
- **The grade discipline is enforced, not asserted.** `Success`/`Failure` carry a
  `witness` (a proof that the remaining size satisfies the consumption grade), and
  the `Outcome` type only exposes a `Failure` branch when the error grade allows it.
  A parser therefore cannot claim a grade its runtime behaviour violates — it would
  fail to construct the witness. `impossible = ⟨never-fail, always-consume⟩` is
  proved uninhabited. The lawful graded-monad instances are machine-proved.

Conclusion: totality and the grade/error contracts hold. No unsoundness found.

## Findings

### 1. DoS: stack overflow on deep/long untrusted input — HIGH (untrusted) / LOW (trusted)
`fix.go` and `many.go` are not tail-recursive; recursion depth equals nesting depth
(`fix`) or element count (`many`). Confirmed: `100000`-deep `((...))` overflows the
stack (backtrace: `Parser.fix.go` ~8000+ frames); the broadened benchmark aborts on
flat inputs past ~50-100k elements. A parser fed untrusted input (network, files)
can be crashed. Mitigation: enforce a depth/size bound before parsing, or move to a
CPS/iterative core. For trusted input (DSLs, proof pipelines) the risk is low.

### 2. Left recursion is silently wrong — MEDIUM (correctness footgun)
A left-recursive body typechecks at grade `conditional`, `fix` accepts it, the
result is total, but it returns wrong answers (proved in `Productivity.lean`,
`fix_not_productive`). The `⟨_, always⟩` type reads like it enforces guardedness but
does not. Documented by the author; the fix is to write the iterative form
(`chainl1`). A size-indexed guarded `fix` (agdarsec-style) would make it a type
error.

### 3. Performance — LOW (not a correctness issue)
Against a same-family baseline — `fgdorais/lean4-parser`, another pure monadic
combinator library — prim-parser is ~1.5-3x slower on integers/csv/sexp/lambda and
~9x on JSON. The totality and proof machinery cost a modest constant factor against
a peer; the earlier 12-33x figures were against `Std.Internal.Parsec`, an imperative
(mutable-iterator) parser, which is not the same family. Structural cost: every
token boxes an `Outcome` through `gbind`.

The JSON 9x is the grammar, not the library. On the same `[1,2,...]` input, the
`Examples/Json.json` grammar runs at 39 ms, a flat `[nat,...]` prim parser (no
`oneOf`, no AST) at 7.1 ms (≈ the integer parser, ~1.6x lean4-parser). So JSON's 9x
decomposes as ~1.6x library + ~5.5x grammar: the six-way `oneOf` per token, building
the full `Json` AST, and a `lexeme` whitespace parse per comma. A first-char
dispatch would recover most of it.

A per-commit sweep over the token-parameterized range (`3493016..HEAD`, clean
rebuild each) shows the five grammar timings flat within noise — no regression from
any commit.

### 4. Parser semantics diverge from parsec — INFO
- Default `<|>` is full PEG backtracking (no commit, no memoization) → potential
  exponential backtracking; `committedChoice` is the LL(1) opt-in.
- `string` is atomic (fails without consuming on a partial match); parsec consumes.
- `many`/`takeWhile` stop silently on a partial match; callers must add `eof` to
  reject trailing garbage.

### 5. Diagnostics — LOW
Error payload is a bare `String`. Structured line/col, a position range, a caret
pretty-printer, and an expected-set merge (`<||>`) were added, but `<?>` relabels
unconditionally (can clobber a deeper inner error), and there is no expected-set
type carried through `choice`.

## Non-findings (checked, safe)

- Array reads use proof-carried indexing (`arr[off]'h`) — no out-of-bounds panic.
- All positions/counters are `Nat` (arbitrary precision) — no integer overflow.
- `parse` / line-col / `pretty` use bounded `getD`/`take` (`pos ≤ len` from the
  `Failure` witness) — no panic.
- No FFI / `@[extern]` / `unsafe`.
