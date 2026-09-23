import Carmichael.Smallest

open Nat

/-- Measure time for repeated evaluations to avoid lazy evaluation and zero measurements. -/
def timeIterated (iters : Nat) (f : Unit → Bool) : IO (Bool × Float) := do
  let t0 ← IO.monoNanosNow
  let mut res := false
  for _ in [0:iters] do
    res := f ()
  let t1 ← IO.monoNanosNow
  let totalUs := (t1 - t0).toFloat / 1000.0
  let avgUs := totalUs / iters.toFloat
  return (res, avgUs)

/-- Measure time for repeated evaluations returning a list of candidates. -/
def timeIteratedList (iters : Nat) (f : Unit → List Nat) : IO (List Nat × Float) := do
  let t0 ← IO.monoNanosNow
  let mut res : List Nat := []
  for _ in [0:iters] do
    res := f ()
  let t1 ← IO.monoNanosNow
  let totalUs := (t1 - t0).toFloat / 1000.0
  let avgUs := totalUs / iters.toFloat
  return (res, avgUs)

def main : IO Unit := do
  IO.println "================================================================================="
  IO.println "  Empirical Scaling Benchmark: Carmichael Modular Funnel Pipeline"
  IO.println "================================================================================="
  IO.println ""
  IO.println "### Suite 1: checkCarmichaelBound N (Refutation Verifier Early-Exit)"
  IO.println "| Bound N | Result | Runtime (us) | Runtime (ms) | Kernel #time (ms) | Status |"
  IO.println "|:---:|:---:|:---:|:---:|:---:|:---|"

  -- Measured via `by decide` in Lean 4 kernel with maxRecDepth 10000 & exp threshold 1000:
  let kernelTimes : List (Nat × Nat) :=
    [(100, 116), (200, 238), (561, 715), (1000, 739), (2000, 772), (5000, 808)]
  let bounds := [100, 200, 561, 1000, 2000, 5000]

  for N in bounds do
    let ktime := (kernelTimes.find? (fun p => p.1 == N)).map (·.2) |>.getD 0
    let iters := if N ≤ 561 then 50 else 100
    let (res, us) ← timeIterated iters (fun () => checkCarmichaelBound N)
    let ms := us / 1000.0
    let status := if res then "Soundness Active (< 561, All Refuted)"
      else "Witness Halt at 561 (First Carmichael)"
    IO.println s!"| {N} | {res} | {us} | {ms} | {ktime} | {status} |"

  IO.println ""
  IO.println "### Suite 2: Full Funnel Scan (Unconstrained Filter over [0, N))"
  IO.println "| Bound N | Total | Identified | Scan (us) | Scan (ms) | Extracted Candidates |"
  IO.println "|:---:|:---:|:---:|:---:|:---:|:---|"

  for N in bounds do
    let iters := if N ≤ 1000 then 20 else 5
    let (cands, us) ← timeIteratedList iters
      (fun () => (List.range N).filter isCarmichaelCandidate)
    let ms := us / 1000.0
    IO.println s!"| {N} | {N} | {cands.length} | {us} | {ms} | {cands} |"

  IO.println ""
  IO.println "================================================================================="
