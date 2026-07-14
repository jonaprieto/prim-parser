#!/usr/bin/env bash
# End-to-end (process launch + parse canada.json + exit) comparison via hyperfine.
# Run from the repo root. Builds all single-parse binaries, then benchmarks.
set -e
export PATH="$HOME/.elan/bin:$HOME/.opam/default/bin:$HOME/.cargo/bin:$PATH"
lake build jcanada jcanada-shallow
(cd bench/ocaml-canada && eval "$(opam env)" && dune build)
(cd bench/hs-canada && cabal build)
LEAN=.lake/build/bin/jcanada
LEAN_SHALLOW=.lake/build/bin/jcanada-shallow
OCAML=$(find bench/ocaml-canada/_build -name 'canada.exe' | head -1)
HS=$(find bench/hs-canada/dist-newstyle -type f -name 'hs-canada' -perm +111 | head -1)
# graded-lean-deep parses ByteArray (like angstrom/megaparsec); graded-lean-shallow
# parses Text Char (String decoded to a boxed Array Char) — the decode tax is the point.
hyperfine -N --warmup 3 \
  -n "graded-lean-deep"    "$LEAN" \
  -n "graded-lean-shallow" "$LEAN_SHALLOW" \
  -n "angstrom-ocaml"      "$OCAML" \
  -n "megaparsec-hs"       "$HS"
