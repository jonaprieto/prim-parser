import PrimParser.Graded
import PrimParser.Byte

/-!
# Compiling the deep backend to the fast byte backend

`Graded.G` and `Byte.BParser` are **both** `ByteArray`-based, so a reified grammar
compiles straight into the compiled byte combinators — no byte/`Char` bridge, unlike
the shallow denotation. Each `G` node maps to its `Byte` combinator, and grades line
up (both use the same `Grade` algebra). `recur` maps to `self`; a grammar ties the
knot with a memoized `partial def` (`compiled := G.compile compiled top`), so the
grammar structure is walked **once** at compile time and the run is pure closure
calls — deep grammars execute at byte-combinator speed instead of paying the fuel
interpreter's per-node dispatch.
-/

namespace Graded
open Byte

/-- Compile a reified grammar into the compiled byte backend. `self` denotes the
fixpoint node `recur`. -/
def G.compile {ρ : Type} (self : BParser conditional ρ) :
    {g : Grade} → {α : Type} → G ρ g α → BParser g α
  | _, _, .pure a       => Byte.pure a
  | _, _, .fail         => Byte.fail
  | _, _, .byte f       => Byte.satisfy f
  | _, _, .lit c        => Byte.byte c
  | _, _, .chars1 f     => Byte.map (fun _ => (⟨⟩ : PUnit)) (Byte.takeWhile1 f)
  | _, _, .chars0 f     => Byte.map (fun _ => (⟨⟩ : PUnit)) (Byte.takeWhile f)
  | _, _, .nat          => Byte.nat
  | _, _, .takeN n      => Byte.takeN n
  | _, _, .map f a      => Byte.map f (G.compile self a)
  | _, _, .map2 f a b   => Byte.map2 f (G.compile self a) (G.compile self b)
  | _, _, .seqR a b     => Byte.seqR (G.compile self a) (G.compile self b)
  | _, _, .seqL a b     => Byte.seqL (G.compile self a) (G.compile self b)
  | _, _, .alt a b      => Byte.alt (G.compile self a) (G.compile self b)
  | _, _, .star a       => Byte.many (G.compile self a)
  | _, _, .starFold f acc a => Byte.foldMany f acc (G.compile self a)
  | _, _, .bind m k     => Byte.bind (G.compile self m) (fun a => G.compile self (k a))
  | _, _, .recur        => self

end Graded
