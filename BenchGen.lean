/-!
Shared benchmark scaffolding: input generators, robust timing stats, and file I/O.
Imports no parser library, so both the prim-parser and lean4-parser benchmark
executables can share it (the two libraries both define `_root_.Parser` and cannot
be imported into the same module).
-/

/- ===================== generators ===================== -/

def genInts (n : Nat) : String := String.intercalate "," ((List.range n).map toString)

def genSexp (w : Nat) : Nat → String
  | 0     => "a"
  | d + 1 => "(" ++ String.intercalate " " (List.replicate w (genSexp w d)) ++ ")"

def genCsv (rows cols : Nat) : String :=
  String.intercalate "\n" ((List.range rows).map fun _ =>
    String.intercalate "," ((List.range cols).map toString))

def genJson (n : Nat) : String := "[" ++ String.intercalate "," ((List.range n).map toString) ++ "]"

def genLambda (n : Nat) : String := String.join (List.replicate n "\\a. ") ++ "x"

/- ===================== stats ===================== -/

structure Stats where
  minMs : Float
  medMs : Float
  meanMs : Float
  sdMs : Float
  mbps : Float

def r2 (x : Float) : Float := (x * 100.0).round / 100.0

def statsOf (ns : Array Nat) (bytes : Nat) : Stats :=
  let sorted := ns.qsort Nat.blt
  let k := sorted.size
  let ms (x : Nat) : Float := Float.ofNat x / 1.0e6
  let mn := ms (sorted.getD 0 0)
  let med := ms (sorted.getD (k / 2) 0)
  let mean := (Float.ofNat (ns.foldl (· + ·) 0) / Float.ofNat k) / 1.0e6
  let var := (ns.foldl (fun a x => a + (ms x - mean) * (ms x - mean)) 0.0) / Float.ofNat k
  { minMs := mn, medMs := med, meanMs := mean, sdMs := Float.sqrt var,
    mbps := (Float.ofNat bytes / 1.0e6) / (mn / 1000.0) }

/-- Time `reps` parses of `act`; return its checksum and per-rep nanoseconds.
`IO.lazyPure` forces each parse (a pure `act ()` would be hoisted/CSE'd). Fails
loudly if the checksum is not stable across reps. -/
def bench (reps : Nat) (act : Unit → Nat) : IO (Nat × Array Nat) := do
  let chk ← IO.lazyPure act
  let mut arr := Array.mkEmpty reps
  for _ in [0:reps] do
    let t0 ← IO.monoNanosNow
    let r ← IO.lazyPure act
    let t1 ← IO.monoNanosNow
    if r != chk then throw (IO.userError "nondeterministic checksum")
    arr := arr.push (t1 - t0)
  pure (chk, arr)

/-- Write `content` to `bench-data/<name>.txt`, then read it back. -/
def prep (name content : String) : IO String := do
  IO.FS.createDirAll "bench-data"
  let path := s!"bench-data/{name}.txt"
  IO.FS.writeFile path content
  IO.FS.readFile path

/-- Measure one grammar, print a line, and return `(name, min-ms, MB/s)`. -/
def benchOne (name input : String) (reps : Nat) (act : Unit → Nat) : IO (String × Float × Float) := do
  let (chk, ns) ← bench reps act
  let s := statsOf ns input.length
  IO.println s!"  {name} ({input.length}B, chk {chk}): min {r2 s.minMs} / med {r2 s.medMs} ± {r2 s.sdMs} ms  ({r2 s.mbps} MB/s)"
  pure (name, s.minMs, s.mbps)

/-- Write `(name, min-ms, MB/s)` rows as a TSV for later merging. -/
def writeTsv (path : String) (rows : Array (String × Float × Float)) : IO Unit :=
  IO.FS.writeFile path (String.intercalate "\n" (rows.toList.map fun (n, mn, mb) => s!"{n}\t{mn}\t{mb}") ++ "\n")
