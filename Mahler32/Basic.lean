import Mathlib

/-!
# The Mahler `3/2` recursion `a(n+1) = a n + ⌈a n / 2⌉`

`a` is OEIS A061419 (`a 0 = 1`).  This file records the exact arithmetic skeleton of the parity
problem `a n % 2`; every statement is a closed-form local law, proved with `omega` alone.

* `step_eq` : the ceiling-free form `step x = (3 * x + x % 2) / 2`;
* `step_parity` : `step x % 2 = x / 2 % 2`, i.e. the parity of the next term is the *second
  binary digit* of the current term.  This is the sharp reason why a base-`6` window propagates
  and a base-`3` window does not;
* `step_mod_three` : `step x % 3 = 2 * (x % 2)`, so the last ternary digit is `2 * (x % 2)` and
  is never `1`;
* `a_mod_six` : the last base-`6` digit is a bijective encoding of the pair of consecutive
  parities `(a (n+1) % 2, a n % 2)`, so it only takes the values `0, 2, 3, 5`;
* `step_parity_hex` : the base-`6` two-digit local law `b 0' = (t 0 + b 1) % 2`;
* `step_injective` : `step` is injective, so no information is lost;
* `step_shift` / `step_pow_shift` : adding a multiple of `2 ^ (j+1)` changes `step` by a multiple
  of `2 ^ j`, iterated `k` times with increment `2 ^ (m - k)` — the "one binary digit per step"
  law in exact form;
* `parity_window` / `parity_window_hex` / `a_parity_window` : `m` binary (equivalently `m`
  base-`6`) digits determine the next `m` parities;
* `cliff_sharp` : the window is sharp — `0` and `6 ^ m` agree on `m` base-`6` digits yet differ
  in parity at step `m`.
* `run_spec` / `ternary_machine` : the base-`3` two-state machine (append `x % 2`, then divide by
  `2` digit by digit with a carry in `{0, 1}`) computes `step x`.
-/

namespace Mahler32

/-- `a n` is A061419: `a 0 = 1` and `a (n+1) = a n + ⌈a n / 2⌉`. -/
def a : ℕ → ℕ
  | 0 => 1
  | n + 1 => a n + (a n + 1) / 2

/-- The step map `x ↦ x + ⌈x / 2⌉` of the recursion. -/
def step (x : ℕ) : ℕ := x + (x + 1) / 2

@[simp] lemma a_zero : a 0 = 1 := rfl

lemma step_eq_a (n : ℕ) : step (a n) = a (n + 1) := rfl

/-- The orbit is the orbit of `step`. -/
lemma a_add (n k : ℕ) : a (n + k) = step^[k] (a n) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.add_succ, ← step_eq_a, ih, Function.iterate_succ_apply']

/-- Splitting a natural number by parity. -/
lemma two_cases (n : ℕ) : (∃ k, n = 2 * k) ∨ (∃ k, n = 2 * k + 1) := by
  rcases Nat.even_or_odd n with h | h
  · obtain ⟨k, rfl⟩ := h
    exact Or.inl ⟨k, by ring⟩
  · obtain ⟨k, rfl⟩ := h
    exact Or.inr ⟨k, by ring⟩

/-- Ceiling-free form: `step x = ⌈3 * x / 2⌉ = (3 * x + x % 2) / 2`. -/
lemma step_eq (x : ℕ) : step x = (3 * x + x % 2) / 2 := by
  obtain ⟨k, rfl⟩ | ⟨k, rfl⟩ := two_cases x <;> unfold step <;> omega

/-- The parity of the next term is the second binary digit of the current one. -/
theorem step_parity (x : ℕ) : step x % 2 = x / 2 % 2 := by
  obtain ⟨k, rfl⟩ | ⟨k, rfl⟩ := two_cases x <;> unfold step <;> omega

/-- Doubling clears the ceiling: `2 * step z = 3 * z + z % 2`. -/
lemma two_mul_step (z : ℕ) : 2 * step z = 3 * z + z % 2 := by
  obtain ⟨k, rfl⟩ | ⟨k, rfl⟩ := two_cases z <;> unfold step <;> omega

/-- The last ternary digit of the next term is `2 * (x % 2)`. -/
theorem step_mod_three (x : ℕ) : step x % 3 = 2 * (x % 2) := by
  obtain ⟨k, rfl⟩ | ⟨k, rfl⟩ := two_cases x <;> unfold step <;> omega

/-- The base-`6` two-digit parity law: with `b j = d j % 2` and `t j = d j / 2`, the new least
significant bit is `(t 0 + b 1) % 2`. -/
theorem step_parity_hex (x : ℕ) : step x % 2 = ((x % 6) / 2 + x / 6 % 2) % 2 := by
  obtain ⟨k, rfl⟩ | ⟨k, rfl⟩ := two_cases x <;> unfold step <;> omega

lemma a_succ_eq (n : ℕ) : a (n + 1) = (3 * a n + a n % 2) / 2 := step_eq (a n)

lemma a_succ_mod_three (n : ℕ) : a (n + 1) % 3 = 2 * (a n % 2) := step_mod_three (a n)

/-- The parity of `a (n+1)` is the second binary digit of `a n`. -/
theorem a_succ_parity (n : ℕ) : a (n + 1) % 2 = a n / 2 % 2 := step_parity (a n)

/-- No term with index `≥ 1` is `≡ 1 (mod 3)`. -/
theorem a_mod_three_ne_one {n : ℕ} (hn : 1 ≤ n) : a n % 3 ≠ 1 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [a_succ_mod_three]
  omega

/-- Every term is positive. -/
lemma a_pos (n : ℕ) : 0 < a n := by
  induction n with
  | zero => decide
  | succ n ih => rw [show a (n + 1) = step (a n) from rfl, step_eq]; omega

/-- The sequence is strictly increasing. -/
lemma a_lt_succ (n : ℕ) : a n < a (n + 1) := by
  have := a_pos n
  rw [show a (n + 1) = step (a n) from rfl, step_eq]
  omega

lemma a_mono : StrictMono a := strictMono_nat_of_lt_succ a_lt_succ

/-- The last base-`6` digit of `a (n+1)` is a bijective encoding of the pair of consecutive
parities `(a (n+1) % 2, a n % 2)`. -/
theorem a_mod_six (n : ℕ) : a (n + 1) % 6 = 3 * (a (n + 1) % 2) + 2 * (a n % 2) := by
  have h3 := a_succ_mod_three n
  have h2 : a (n + 1) % 6 % 2 = a (n + 1) % 2 := by omega
  have h1 : a (n + 1) % 6 % 3 = a (n + 1) % 3 := by omega
  omega

/-- Hence the last base-`6` digit never equals `1` or `4`. -/
theorem a_mod_six_mem (n : ℕ) : a (n + 1) % 6 = 0 ∨ a (n + 1) % 6 = 2 ∨
    a (n + 1) % 6 = 3 ∨ a (n + 1) % 6 = 5 := by
  have h := a_mod_six n
  have hp : a (n + 1) % 2 = 0 ∨ a (n + 1) % 2 = 1 := by omega
  have hq : a n % 2 = 0 ∨ a n % 2 = 1 := by omega
  rcases hp with hp | hp <;> rcases hq with hq | hq <;> omega

/-- The step map is injective: the recursion is reversible. -/
theorem step_injective {x y : ℕ} (h : step x = step y) : x = y := by
  obtain ⟨k, rfl⟩ | ⟨k, rfl⟩ := two_cases x <;>
    obtain ⟨l, rfl⟩ | ⟨l, rfl⟩ := two_cases y <;> unfold step at h <;> omega

/-! ### The ternary two-state machine

Read the base-`3` digits of `x` most significant first, append `w = x % 2`, and divide by `2`
digit by digit with a carry in `{0, 1}`:

`val = 3 * carry + d`, output `val / 2`, new carry `val % 2`.

This is exactly the transducer of the problem statement; `ternary_machine` says it computes
`step x`.  Note that no bound on the digits is needed — the invariant is pure algebra. -/

/-- Value of a most-significant-digit-first digit list in base `3`. -/
def val : List ℕ → ℕ
  | [] => 0
  | d :: ds => d * 3 ^ ds.length + val ds

@[simp] lemma val_nil : val [] = 0 := rfl

lemma val_cons (d : ℕ) (ds : List ℕ) : val (d :: ds) = d * 3 ^ ds.length + val ds := rfl

lemma val_append_singleton (L : List ℕ) (d : ℕ) : val (L ++ [d]) = val L * 3 + d := by
  induction L with
  | nil => simp [val]
  | cons e es ih =>
    rw [List.cons_append, val_cons, ih, val_cons]
    have h : 3 ^ (es ++ [d]).length = 3 ^ es.length * 3 := by
      rw [List.length_append, List.length_singleton, pow_succ]
    rw [h]
    ring

lemma val_reverse_eq_ofDigits (L : List ℕ) : val L.reverse = Nat.ofDigits 3 L := by
  induction L with
  | nil => simp
  | cons d ds ih =>
    rw [List.reverse_cons, val_append_singleton, ih, Nat.ofDigits_cons]
    omega

/-- The MSB-first digit list of `x` evaluates back to `x`. -/
lemma val_digits (x : ℕ) : val (Nat.digits 3 x).reverse = x := by
  rw [val_reverse_eq_ofDigits, Nat.ofDigits_digits]

/-- Quotient digits produced by the scan. -/
def runOut : List ℕ → ℕ → List ℕ
  | [], _ => []
  | d :: ds, r => (3 * r + d) / 2 :: runOut ds ((3 * r + d) % 2)

/-- Final carry of the scan. -/
def runRem : List ℕ → ℕ → ℕ
  | [], r => r
  | d :: ds, r => runRem ds ((3 * r + d) % 2)

lemma runOut_length (L : List ℕ) (r : ℕ) : (runOut L r).length = L.length := by
  induction L generalizing r with
  | nil => rfl
  | cons d ds ih => simp [runOut, ih]

lemma runRem_lt_two (L : List ℕ) (r : ℕ) (hr : r < 2) : runRem L r < 2 := by
  induction L generalizing r with
  | nil => simpa [runRem] using hr
  | cons d ds ih =>
    simp only [runRem]
    exact ih _ (by omega)

/-- Long-division invariant: the emitted digits and the final carry reconstruct `3 ^ |L| * r +
val L`. -/
theorem run_spec (L : List ℕ) (r : ℕ) :
    2 * val (runOut L r) + runRem L r = r * 3 ^ L.length + val L := by
  induction L generalizing r with
  | nil => simp [runOut, runRem, val]
  | cons d ds ih =>
    have h2 : 2 * ((3 * r + d) / 2) + (3 * r + d) % 2 = 3 * r + d := by omega
    calc 2 * val (runOut (d :: ds) r) + runRem (d :: ds) r
        = 2 * (((3 * r + d) / 2) * 3 ^ ds.length + val (runOut ds ((3 * r + d) % 2)))
            + runRem ds ((3 * r + d) % 2) := by
          simp only [runOut, runRem, val_cons, runOut_length]
      _ = 2 * ((3 * r + d) / 2) * 3 ^ ds.length
            + (2 * val (runOut ds ((3 * r + d) % 2)) + runRem ds ((3 * r + d) % 2)) := by
          ring
      _ = 2 * ((3 * r + d) / 2) * 3 ^ ds.length
            + ((3 * r + d) % 2 * 3 ^ ds.length + val ds) := by
          rw [ih]
      _ = (2 * ((3 * r + d) / 2) + (3 * r + d) % 2) * 3 ^ ds.length + val ds := by
          ring
      _ = (3 * r + d) * 3 ^ ds.length + val ds := by rw [h2]
      _ = r * 3 ^ (d :: ds).length + val (d :: ds) := by
          rw [val_cons, List.length_cons, pow_succ]
          ring

/-- **The two-state machine computes `step`.**  Appending the parity digit and running the
divide-by-`2` scan over the base-`3` digits reproduces `⌈3x/2⌉`. -/
theorem ternary_machine (x : ℕ) :
    val (runOut ((Nat.digits 3 x).reverse ++ [x % 2]) 0) = step x := by
  have hspec := run_spec ((Nat.digits 3 x).reverse ++ [x % 2]) 0
  have hval : val ((Nat.digits 3 x).reverse ++ [x % 2]) = 3 * x + x % 2 := by
    rw [val_append_singleton, val_digits]
    omega
  have hrem := runRem_lt_two ((Nat.digits 3 x).reverse ++ [x % 2]) 0 (by norm_num)
  have hstep := two_mul_step x
  rw [hval, Nat.zero_mul, Nat.zero_add] at hspec
  omega

/-! ### The information window (the "cliff")

Each iteration spends exactly one binary digit: `step x` is determined modulo `2 ^ j` by `x`
modulo `2 ^ (j+1)`, so `m` binary digits buy exactly `m` future parities and not one more.
The two theorems `parity_window_hex` and `cliff_sharp` are the two halves of that statement. -/

/-- Adding a multiple of `2 ^ (j+1)` changes `step` by a multiple of `2 ^ j`, explicitly. -/
theorem step_shift (j t x : ℕ) :
    step (x + 2 ^ (j + 1) * t) = step x + 2 ^ j * (3 * t) := by
  have h2 : (x + 2 ^ (j + 1) * t) % 2 = x % 2 := by
    obtain ⟨s, hs⟩ : ∃ s, 2 ^ (j + 1) * t = 2 * s := ⟨2 ^ j * t, by rw [pow_succ]; ring⟩
    rw [hs]
    omega
  have key : 2 * step (x + 2 ^ (j + 1) * t) = 2 * (step x + 2 ^ j * (3 * t)) := by
    have hexp : 2 * (step x + 2 ^ j * (3 * t)) = 2 * step x + 2 * (2 ^ j * (3 * t)) := by
      ring
    rw [hexp, two_mul_step, two_mul_step, h2]
    simp only [pow_succ]
    ring
  exact Nat.mul_left_cancel (n := 2) (by norm_num) key

/-- Iterated form: after `k` steps the increment is `2 ^ (m - k)` times an integer. -/
theorem step_pow_shift (m k : ℕ) (hk : k ≤ m) (t x : ℕ) :
    step^[k] (x + 2 ^ m * t) = step^[k] x + 2 ^ (m - k) * (3 ^ k * t) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hk' : k ≤ m := by omega
    have hlt : k < m := by omega
    rw [Function.iterate_succ_apply', ih hk', Function.iterate_succ_apply']
    have hshift := step_shift (m - k - 1) (3 ^ k * t) (step^[k] x)
    rw [show m - k - 1 + 1 = m - k from by omega] at hshift
    rw [hshift, show m - k - 1 = m - (k + 1) from by omega, pow_succ]
    ring

/-- `m` binary digits determine the next `m` parities. -/
theorem parity_window (m k t x : ℕ) (hk : k < m) :
    (step^[k] (x + 2 ^ m * t)) % 2 = (step^[k] x) % 2 := by
  rw [step_pow_shift m k (by omega) t x]
  obtain ⟨d, hd⟩ : ∃ d, m - k = d + 1 := ⟨m - k - 1, by omega⟩
  have hcomm : 2 ^ (m - k) * (3 ^ k * t) = (2 ^ d * (3 ^ k * t)) * 2 := by
    rw [hd, pow_succ]
    ring
  rw [hcomm, Nat.add_mul_mod_self_right]

/-- `m` base-`6` digits determine the next `m` parities (one digit carries one binary digit). -/
theorem parity_window_hex (m k t x : ℕ) (hk : k < m) :
    (step^[k] (x + 6 ^ m * t)) % 2 = (step^[k] x) % 2 := by
  have h : 6 ^ m * t = 2 ^ m * (3 ^ m * t) := by
    rw [show (6 : ℕ) = 2 * 3 from by norm_num, mul_pow]
    ring
  rw [h]
  exact parity_window m k (3 ^ m * t) x hk

/-- Sequence form: any number congruent to `a n` modulo `6 ^ m` produces the same next `m`
parities as the true orbit does. -/
theorem a_parity_window (m k t n : ℕ) (hk : k < m) :
    a (n + k) % 2 = (step^[k] (a n + 6 ^ m * t)) % 2 := by
  rw [a_add, parity_window_hex m k t (a n) hk]

lemma step_two_pow_mul (j c : ℕ) : step (2 ^ (j + 1) * c) = 3 * (2 ^ j * c) := by
  have h : 2 ^ (j + 1) * c = 2 * (2 ^ j * c) := by rw [pow_succ]; ring
  rw [h]
  unfold step
  have hdiv : (2 * (2 ^ j * c) + 1) / 2 = 2 ^ j * c := by omega
  rw [hdiv]
  ring

/-- The orbit of `6 ^ m` sits exactly on the boundary: after `m` exact halvings it is the odd
number `3 ^ m * 3 ^ m`. -/
theorem step_pow_six (m k : ℕ) (hk : k ≤ m) :
    step^[k] (6 ^ m) = 3 ^ k * (2 ^ (m - k) * 3 ^ m) := by
  induction k with
  | zero =>
    rw [Function.iterate_zero_apply, pow_zero, one_mul, Nat.sub_zero]
    rw [show (6 : ℕ) = 2 * 3 from by norm_num, mul_pow]
  | succ k ih =>
    have hk' : k ≤ m := by omega
    have hlt : k < m := by omega
    rw [Function.iterate_succ_apply', ih hk']
    obtain ⟨d, hd⟩ : ∃ d, m - k = d + 1 := ⟨m - k - 1, by omega⟩
    have hsplit : 3 ^ k * (2 ^ (m - k) * 3 ^ m) = 2 ^ (d + 1) * (3 ^ k * 3 ^ m) := by
      rw [← hd]
      ring
    rw [hsplit, step_two_pow_mul, show d = m - (k + 1) from by omega, pow_succ]
    ring

/-- Powers of `3` are odd. -/
lemma three_pow_mod_two (k : ℕ) : (3 : ℕ) ^ k % 2 = 1 := by
  induction k with
  | zero => norm_num
  | succ k ih => rw [pow_succ, Nat.mul_mod, ih]

/-- The window is sharp: two numbers agreeing on `m` base-`6` digits can still differ in parity
at step `m` (`0` versus `6 ^ m`). -/
theorem cliff_sharp (m : ℕ) :
    ∃ x y : ℕ, x % 6 ^ m = y % 6 ^ m ∧ (step^[m] x) % 2 ≠ (step^[m] y) % 2 := by
  refine ⟨0, 6 ^ m, by simp, ?_⟩
  have hzero : step^[m] 0 = 0 := by
    induction m with
    | zero => simp
    | succ m ih => rw [Function.iterate_succ_apply', ih]; simp [step]
  have hsix := step_pow_six m m le_rfl
  have h3 := three_pow_mod_two m
  rw [hzero, hsix, show m - m = 0 from by omega, pow_zero, one_mul, Nat.mul_mod, h3]
  norm_num

/-! ### Period doubling

Scanning a block `B` twice, the carry after the first copy is `r + ones B` (mod `2`): the parity
of the number of odd digits is exactly the affine part of the state map.  So

* odd `ones B`  : the carry flips, the two output blocks differ, and `|B|` is **not** a period
  of the two-block output — the period strictly doubles to `2 * |B|`;
* even `ones B` : the carry returns, the two output blocks coincide, so `|B|` survives.
-/

/-- Number of odd digits of a digit list. -/
def ones (L : List ℕ) : ℕ := (L.map (fun d => d % 2)).sum

@[simp] lemma ones_nil : ones [] = 0 := rfl

lemma ones_cons (d : ℕ) (ds : List ℕ) : ones (d :: ds) = d % 2 + ones ds := rfl

/-- **One-period state transition**: the carry after a block is `r + ones B` mod `2`. -/
theorem runRem_eq (L : List ℕ) (r : ℕ) (hr : r < 2) : runRem L r = (r + ones L) % 2 := by
  induction L generalizing r with
  | nil => simp [runRem, ones]; omega
  | cons d ds ih =>
    rw [runRem, ones_cons, ih ((3 * r + d) % 2) (by omega)]
    have hstep : (3 * r + d) % 2 = (r + d % 2) % 2 := by omega
    rw [hstep]
    omega

/-- The scan is a monoid homomorphism on concatenation, with the carry threaded through. -/
theorem runOut_append (L₁ L₂ : List ℕ) (r : ℕ) :
    runOut (L₁ ++ L₂) r = runOut L₁ r ++ runOut L₂ (runRem L₁ r) := by
  induction L₁ generalizing r with
  | nil => simp [runOut, runRem]
  | cons d ds ih => simp only [List.cons_append, runOut, runRem, ih]

/-- Two copies of a block: the second copy starts from the carry `(r + ones B) % 2`. -/
theorem runOut_two_blocks (B : List ℕ) (r : ℕ) (hr : r < 2) :
    runOut (B ++ B) r = runOut B r ++ runOut B ((r + ones B) % 2) := by
  rw [runOut_append, runRem_eq B r hr]

/-- Odd number of odd digits: the carry flips. -/
theorem runOut_two_blocks_odd (B : List ℕ) (hodd : ones B % 2 = 1) (r : ℕ) (hr : r < 2) :
    runOut (B ++ B) r = runOut B r ++ runOut B (1 - r) := by
  rw [runOut_two_blocks B r hr]
  have h : (r + ones B) % 2 = 1 - r := by omega
  rw [h]

/-- Even number of odd digits: the carry returns, so the block repeats. -/
theorem runOut_two_blocks_even (B : List ℕ) (heven : ones B % 2 = 0) (r : ℕ) (hr : r < 2) :
    runOut (B ++ B) r = runOut B r ++ runOut B r := by
  rw [runOut_two_blocks B r hr]
  have h : (r + ones B) % 2 = r := by omega
  rw [h]

/-- The two output blocks differ in their first digit, because the incoming carries differ. -/
theorem runOut_blocks_ne (B : List ℕ) (hd : ∀ d ∈ B, d < 3) (hB : B ≠ []) (r : ℕ) (hr : r < 2) :
    runOut B r ≠ runOut B (1 - r) := by
  obtain ⟨d, ds, rfl⟩ : ∃ d ds, B = d :: ds := by
    cases B with
    | nil => exact absurd rfl hB
    | cons d ds => exact ⟨d, ds, rfl⟩
  have hd3 : d < 3 := hd d (by simp)
  simp only [runOut]
  intro hcons
  have := List.cons.inj hcons
  omega

/-- **Period doubling (odd case).**  For a block with an odd number of odd digits, the scan of
`B ++ B` has the two halves different, i.e. `|B|` is not a period: the period doubles. -/
theorem period_doubling (B : List ℕ) (hd : ∀ d ∈ B, d < 3) (hB : B ≠ [])
    (hodd : ones B % 2 = 1) (r : ℕ) (hr : r < 2) :
    (runOut (B ++ B) r).take B.length ≠ (runOut (B ++ B) r).drop B.length := by
  rw [runOut_two_blocks_odd B hodd r hr, ← runOut_length B r, List.take_left, List.drop_left]
  exact runOut_blocks_ne B hd hB r hr

/-- **No doubling (even case).**  For a block with an even number of odd digits, the two halves
of the scan of `B ++ B` coincide, so `|B|` remains a period. -/
theorem period_persists (B : List ℕ) (heven : ones B % 2 = 0) (r : ℕ) (hr : r < 2) :
    (runOut (B ++ B) r).take B.length = (runOut (B ++ B) r).drop B.length := by
  rw [runOut_two_blocks_even B heven r hr, ← runOut_length B r, List.take_left, List.drop_left]


/-! ### The inverse branch and legal predecessors

`bstep y = (2y - 2y % 3) / 3` undoes one step: it is the base-`3` "shift the digits right" rule,
defined exactly when `y ≢ 1 (mod 3)`.  Being a *local* rule, it contracts `3`-adically, so the
`k`-fold predecessors of a point form `2 ^ k` residue classes modulo `3 ^ k` — one per history of
parity digits. -/

/-- Inverse branch of `step`: undo one base-`3` digit. -/
def bstep (y : ℕ) : ℕ := (2 * y - 2 * y % 3) / 3

/-- Clearing the division: `3 * bstep y + 2y % 3 = 2y`. -/
lemma bstep_mul (y : ℕ) : 3 * bstep y + 2 * y % 3 = 2 * y := by
  have hmod : (2 * y - 2 * y % 3) % 3 = 0 := by omega
  have hd := Nat.div_add_mod (2 * y - 2 * y % 3) 3
  rw [hmod, Nat.add_zero] at hd
  unfold bstep
  omega

/-- The digit emitted by the inverse branch is `2y % 3`, and it is `0` or `1`. -/
lemma bstep_parity (y : ℕ) (h : y % 3 ≠ 1) : bstep y % 2 = 2 * y % 3 := by
  have hc : 2 * y % 3 < 2 := by omega
  have hm := bstep_mul y
  omega

/-- The inverse branch and the step map are mutually inverse (where defined). -/
theorem step_bstep (y : ℕ) (h : y % 3 ≠ 1) : step (bstep y) = y := by
  have hc : 2 * y % 3 < 2 := by omega
  have hm := bstep_mul y
  rw [step_eq]
  omega

/-- One step followed by one inverse step returns. -/
theorem bstep_step (x : ℕ) : bstep (step x) = x := by
  have hstep := two_mul_step x
  have hpar : 2 * step x % 3 = x % 2 := by omega
  have hm := bstep_mul (step x)
  rw [hpar] at hm
  omega

/-- `k` inverse steps undo `k` steps. -/
theorem bstep_pow_step (k : ℕ) (x : ℕ) : bstep^[k] (step^[k] x) = x := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply', bstep_step]
    exact ih

/-- The legality predicate: the first `k` inverse steps never hit `≡ 1 (mod 3)`. -/
def good (k y : ℕ) : Prop := ∀ j, j < k → (bstep^[j] y) % 3 ≠ 1

lemma good.zero (y : ℕ) : good 0 y := fun j hj => absurd hj (Nat.not_lt_zero j)

lemma good.succ {k y : ℕ} (h : good (k + 1) y) : y % 3 ≠ 1 ∧ good k (bstep y) := by
  refine ⟨h 0 (by omega), fun j hj => ?_⟩
  have := h (j + 1) (by omega)
  rwa [Function.iterate_succ_apply] at this

/-- `k` inverse steps invert `k` steps, provided the path stays legal. -/
theorem step_pow_bstep : ∀ k y : ℕ, good k y → step^[k] (bstep^[k] y) = y
  | 0, y, _ => by simp
  | k + 1, y, h => by
    obtain ⟨h0, hk⟩ := good.succ h
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply,
      step_pow_bstep k (bstep y) hk, step_bstep y h0]


end Mahler32
