/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Contributor
-/
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Intervals
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.NumberTheory.PrimeCounting
import Eratosthenes

/-!
# E2E Test Suite: Sieve of Eratosthenes

Comprehensive 4-tier requirement-driven end-to-end test suite for `Nat.eratosthenes`:
* Tier 1: Feature Coverage (Small prime generation)
* Tier 2: Boundary & Corner Cases (n = 0, 1, 2, prime/composite limits)
* Tier 3: Cross-Feature Combinations (Equivalence with Mathlib primesLE / primesBelow)
* Tier 4: Real-World & Ground Truth Scenarios (Canonical prime counts π(n))
-/

open Nat

/-- Helper function to evaluate test conditions and report per-test status. -/
def runTest (name : String) (condition : Bool) : IO Bool := do
  if condition then
    IO.println s!"[PASS] {name}"
    return true
  else
    IO.println s!"[FAIL] {name}"
    return false

/-- Tier 1: Feature Coverage (Small values n = 0, 1, 2, 3, 10, 20, 30). -/
def runTier1 : IO Nat := do
  IO.println "=== Tier 1: Feature Coverage (Small Values) ==="
  let mut passes := 0
  let tests := [
    ("eratosthenes 0 = []", eratosthenes 0 == []),
    ("eratosthenes 1 = []", eratosthenes 1 == []),
    ("eratosthenes 2 = [2]", eratosthenes 2 == [2]),
    ("eratosthenes 3 = [2, 3]", eratosthenes 3 == [2, 3]),
    ("eratosthenes 10 = [2, 3, 5, 7]", eratosthenes 10 == [2, 3, 5, 7]),
    ("eratosthenes 20 = [2, 3, 5, 7, 11, 13, 17, 19]",
      eratosthenes 20 == [2, 3, 5, 7, 11, 13, 17, 19]),
    ("eratosthenes 30 = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29]",
      eratosthenes 30 == [2, 3, 5, 7, 11, 13, 17, 19, 23, 29])
  ]
  for (name, cond) in tests do
    if (← runTest name cond) then
      passes := passes + 1
  return passes

/-- Tier 2: Boundary & Corner Cases. -/
def runTier2 : IO Nat := do
  IO.println "=== Tier 2: Boundary & Corner Cases ==="
  let mut passes := 0
  let tests := [
    ("Zero boundary n = 0 produces empty list", eratosthenes 0 == []),
    ("Unit boundary n = 1 produces empty list", eratosthenes 1 == []),
    ("Smallest prime boundary n = 2 produces [2]", eratosthenes 2 == [2]),
    ("Prime boundary n = 13 ends with 13", (eratosthenes 13).getLast? == some 13),
    ("Prime boundary n = 17 ends with 17", (eratosthenes 17).getLast? == some 17),
    ("Composite boundary n = 4 equals eratosthenes 3",
      eratosthenes 4 == eratosthenes 3),
    ("Composite boundary n = 9 equals eratosthenes 8",
      eratosthenes 9 == eratosthenes 8),
    ("Composite boundary n = 25 equals eratosthenes 24",
      eratosthenes 25 == eratosthenes 24),
    ("Composite boundary n = 49 ends with 47",
      (eratosthenes 49).getLast? == some 47)
  ]
  for (name, cond) in tests do
    if (← runTest name cond) then
      passes := passes + 1
  return passes

/-- Tier 3: Cross-Feature Combinations (Equivalence with Mathlib primesLE / primesBelow). -/
def runTier3 : IO Nat := do
  IO.println "=== Tier 3: Cross-Feature Combinations ==="
  let mut passes := 0
  let tests := [
    ("Set equivalence at n = 0 with primesLE", (eratosthenes 0).toFinset == Nat.primesLE 0),
    ("Set equivalence at n = 1 with primesLE", (eratosthenes 1).toFinset == Nat.primesLE 1),
    ("Set equivalence at n = 10 with primesLE", (eratosthenes 10).toFinset == Nat.primesLE 10),
    ("Set equivalence at n = 25 with primesLE", (eratosthenes 25).toFinset == Nat.primesLE 25),
    ("Cross check at n = 25 with primesBelow 26",
      (eratosthenes 25).toFinset == Nat.primesBelow 26),
    ("Set equivalence at n = 30 with primesLE", (eratosthenes 30).toFinset == Nat.primesLE 30),
    ("Set equivalence at n = 50 with primesLE", (eratosthenes 50).toFinset == Nat.primesLE 50),
    ("Set equivalence at n = 100 with primesLE", (eratosthenes 100).toFinset == Nat.primesLE 100),
    ("Cross check at n = 100 with primesBelow 101",
      (eratosthenes 100).toFinset == Nat.primesBelow 101)
  ]
  for (name, cond) in tests do
    if (← runTest name cond) then
      passes := passes + 1
  return passes

/-- Tier 4: Real-World & Ground Truth Scenarios (Canonical prime counting constants π(n)). -/
def runTier4 : IO Nat := do
  IO.println "=== Tier 4: Real-World & Ground Truth Scenarios ==="
  let mut passes := 0
  let tests := [
    ("Prime count constant π(100) = 25", (eratosthenes 100).length == 25),
    ("Prime count constant π(1000) = 168", (eratosthenes 1000).length == 168),
    ("Prime count constant π(2000) = 303", (eratosthenes 2000).length == 303),
    ("Prime count constant π(5000) = 669", (eratosthenes 5000).length == 669),
    ("Prime count constant π(10000) = 1229", (eratosthenes 10000).length == 1229)
  ]
  for (name, cond) in tests do
    if (← runTest name cond) then
      passes := passes + 1
  return passes

-- Compile-time verification of formal theorems existence and types.
#check (eratosthenes_sound : ∀ n, ∀ p ∈ eratosthenes n, p.Prime)
#check (eratosthenes_complete : ∀ {n p : ℕ}, p ≤ n → p.Prime → p ∈ eratosthenes n)
#check (eratosthenes_eq_primesLE : ∀ n, (eratosthenes n).toFinset = Nat.primesLE n)

/-- Main test runner executing all 4 tiers. -/
def main : IO UInt32 := do
  IO.println "=================================================="
  IO.println "Running Sieve of Eratosthenes 4-Tier E2E Test Suite"
  IO.println "=================================================="
  let p1 ← runTier1
  let p2 ← runTier2
  let p3 ← runTier3
  let p4 ← runTier4

  let totalPasses := p1 + p2 + p3 + p4
  let totalTests := 7 + 9 + 9 + 5

  IO.println "--------------------------------------------------"
  IO.println s!"Summary: {totalPasses} / {totalTests} tests passed."
  IO.println s!"  Tier 1 (Feature Coverage): {p1}/7 passed"
  IO.println s!"  Tier 2 (Boundary & Corner): {p2}/9 passed"
  IO.println s!"  Tier 3 (Cross-Feature Equivalence): {p3}/9 passed"
  IO.println s!"  Tier 4 (Real-World Prime Counts): {p4}/5 passed"
  IO.println "--------------------------------------------------"

  if totalPasses == totalTests then
    IO.println "ALL E2E TESTS PASSED SUCCESSFULLY!"
    return 0
  else
    IO.println "SOME TESTS FAILED!"
    return 1
