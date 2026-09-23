import Carmichael.Smallest

open Nat

/-- Local Eratosthenes sieve for benchmark comparison. -/
def eratosthenesSieve (n : Nat) : Array Bool := Id.run do
  let mut isPrime := Array.replicate (n + 1) true
  if n ≥ 0 then isPrime := isPrime.set! 0 false
  if n ≥ 1 then isPrime := isPrime.set! 1 false
  let mut p := 2
  while p * p ≤ n do
    if isPrime[p]! then
      let mut multiple := p * p
      while multiple ≤ n do
        isPrime := isPrime.set! multiple false
        multiple := multiple + p
    p := p + 1
  return isPrime

def timeAction {α : Type} (act : IO α) : IO (α × Nat) := do
  let t0 ← IO.monoNanosNow
  let a ← act
  let t1 ← IO.monoNanosNow
  return (a, t1 - t0)

def main : IO Unit := do
  IO.println "=========================================================================="
  IO.println "  LEAN 4 Strict Evaluation Benchmark (Carmichael Reflection & Sieve)"
  IO.println "=========================================================================="
  IO.println ""
  IO.println " [1] Strict Check for 561 Minimality (checkCarmichaelBound 561):"
  let (res, nanos561) ← timeAction (pure (checkCarmichaelBound 561))
  let us561 := nanos561 / 1000
  IO.println s!"     * Result           : {res}"
  IO.println s!"     * Computation Time : {us561} us"
  IO.println ""

  IO.println " [2] Strict Sieve of Eratosthenes Construction & Array Traversal:"
  let testScales := [1000, 5000, 10000, 50000, 100000]
  for scale in testScales do
    let (primeCount, nanos) ← timeAction do
      let sieve := eratosthenesSieve scale
      let mut count : Nat := 0
      for i in [2:scale + 1] do
        if sieve[i]! then count := count + 1
      return count

    let us := nanos / 1000
    IO.println s!"     * N = {scale} | Filtered: {primeCount} primes | Time: {us} us"
  IO.println ""
  IO.println "=========================================================================="