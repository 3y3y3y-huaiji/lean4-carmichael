/-
Copyright (c) 2026 Su MingKai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Su MingKai
-/
import Carmichael.Korselt
import Carmichael.Smallest
import Carmichael.Poulet
import Carmichael.StrongPsp
import Carmichael.StrongPspMulti

/-!
# Formalized Pseudoprimes & Computational Reflection Suite in Lean 4

This library provides a comprehensive formalization of pseudoprimes, computational reflection,
and deterministic primality testing in Lean 4 with Mathlib4.

## Submodules

- `Carmichael.Korselt`: Korselt's criterion (1899) with out-of-the-box computation and equivalence.
- `Carmichael.Smallest`: Proof that 561 is the strictly smallest Carmichael number
  (resolving Mathlib TODO).
- `Carmichael.Poulet`: 341 is the strictly smallest Poulet number (base-2 Fermat pseudoprime).
- `Carmichael.StrongPsp`: 2047 is the strictly smallest base-2 strong pseudoprime (Miller-Rabin),
  with constructive 2-adic decomposition and hierarchy bridge `IsStrongPsp 2 n → IsPoulet n`.
- `Carmichael.StrongPspMulti`: Pomerance-Selfridge-Wagstaff (PSW) theorem for bases {2, 3}
  (1,373,653), 100% deterministic primality testing for n < 1,373,653, and 64-bit industrial
  primality testing interface.
-/

