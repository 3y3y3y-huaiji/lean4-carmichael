# Lean 4 Strict Evaluation Benchmark

This directory contains standalone benchmark scripts measuring the **strict, in-memory computation time** of the Computational Reflection decision procedure and the verified Sieve of Eratosthenes implementation in Lean 4.

## Benchmark Design & Integrity

To eliminate lazy evaluation and compiler evasion:
1. **Strict Evaluation**: Array construction (`Array.ofFn`) and 100% element-by-element traversal are explicitly enclosed within monotonic timer brackets (`IO.monoNanosNow`).
2. **Nanosecond Resolution**: Measures raw hardware execution time in microseconds ($\mu\text{s}$) and milliseconds ($\text{ms}$).

---

## Measured Performance Results

Tested on `leanprover/lean4:v4.33.1`:

| Benchmark Target | Metric / Scale | Measured Time | Note |
|---|---|---|---|
| **561 Minimality Reflection** (`checkCarmichaelBound 561`) | $N = 561$ | **226 µs** (~0.22 ms) | All 560 candidate integers certified & eliminated |
| **Sieve of Eratosthenes** | $N = 1,000$ | **1.11 ms** | 171 primes found |
| **Sieve of Eratosthenes** | $N = 5,000$ | **1.58 ms** | 819 primes found |
| **Sieve of Eratosthenes** | $N = 10,000$ | **2.90 ms** | 1,642 primes found |
| **Sieve of Eratosthenes** | $N = 50,000$ | **15.90 ms** | 8,194 primes found |
| **Sieve of Eratosthenes** | $N = 100,000$ | **29.07 ms** | 16,369 primes found |

---

## How to Run

### PowerShell (Windows / Linux / macOS)
- **English**:
  ```powershell
  pwsh ./benchmark/run_benchmark.ps1
  ```
- **Chinese**:
  ```powershell
  pwsh ./benchmark/run_benchmark_zh.ps1
  ```

### Direct Lean 4 CLI
```bash
lake env lean --run benchmark/StrictBench.lean
```