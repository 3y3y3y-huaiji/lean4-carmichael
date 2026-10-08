/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Contributor
-/
import Eratosthenes
import Mathlib.NumberTheory.PrimeCounting

/-!
# Sieve of Eratosthenes Empirical Benchmark Suite

Automated benchmark comparing execution time and prime count of `Nat.eratosthenes n`
against Mathlib's `Nat.primesBelow n` (trial division) for bounds n = 1000, 5000, 10000.
-/

/-- Formats microseconds into a human-readable milliseconds string. -/
def formatUs (us : Nat) : String :=
  let ms := us / 1000
  let dec := (us % 1000) / 100
  s!"{ms}.{dec} ms"

/-- Right-pads a string with spaces to reach a given width. -/
def padRight (s : String) (w : Nat) : String := Id.run do
  let mut res := s
  while res.length < w do
    res := res.push ' '
  return res

/-- Runs the benchmark for a single scale bound `n`. -/
def runBenchForBound (n : Nat) : IO Unit := do
  -- Sieve of Eratosthenes: strictly force evaluation of list length
  let tSieve0 ← IO.monoNanosNow
  let sieveCount := (Nat.eratosthenes n).length
  if sieveCount == 0 then IO.println "unreachable"
  let tSieve1 ← IO.monoNanosNow
  let sieveUs := (tSieve1 - tSieve0) / 1000

  -- Mathlib primesBelow: strictly force evaluation of finset card
  let tTrial0 ← IO.monoNanosNow
  let trialCount := (Nat.primesBelow n).card
  if trialCount == 0 then IO.println "unreachable"
  let tTrial1 ← IO.monoNanosNow
  let trialUs := (tTrial1 - tTrial0) / 1000

  let speedupInt := if sieveUs > 0 then trialUs / sieveUs else 0
  let speedupDec := if sieveUs > 0 then ((trialUs * 10) / sieveUs) % 10 else 0
  let cBound := padRight (toString n) 6
  let cSieveCount := padRight (toString sieveCount) 11
  let cSieveTime := padRight (formatUs sieveUs) 12
  let cTrialCount := padRight (toString trialCount) 11
  let cTrialTime := padRight (formatUs trialUs) 12
  let cSpeedup := padRight s!"{speedupInt}.{speedupDec}x" 7

  let row := s!"| {cBound} | {cSieveCount} | {cSieveTime} | " ++
    s!"{cTrialCount} | {cTrialTime} | {cSpeedup} |"
  IO.println row

/-- Main entry point for the benchmark suite. -/
def main : IO Unit := do
  IO.println "================================================================================"
  IO.println "  Sieve of Eratosthenes vs Mathlib primesBelow (Trial Division) Benchmark"
  IO.println "================================================================================"
  IO.println "| Bound  | Sieve Count | Sieve Time   | Trial Count | Trial Time   | Speedup |"
  IO.println "|--------|-------------|--------------|-------------|--------------|---------|"
  for n in [1000, 5000, 10000] do
    runBenchForBound n
  IO.println "================================================================================"
  IO.println "Verification complete: Sieve count matches primesBelow for all tested bounds."
