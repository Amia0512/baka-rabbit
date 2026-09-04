import Mathlib

open scoped BigOperators

set_option maxHeartbeats 0

/-!
# q=6 all-root decomposition: geometric-term lemmas for step13

This file proves, for the order-13 palindromic recurrence `step13` of the q=6
quadrangle sequence (same definition as in `q6_allroot_decomp1.lean`):

1. every geometric term `n ↦ c * z^n` with `char13 z = 0` satisfies the
   recurrence `x (n+13) = step13 x n` (`geom_satisfies_step13`), where
   `char13` is the order-13 characteristic polynomial (the reverse of the
   denominator `Q(x) = 1 - 375 x + 31905 x^2 - ... - x^13` of the q=6
   generating function);
2. the constant sequence satisfies the recurrence (`const_satisfies_step13`),
   since `z = 1` is a characteristic root (`char13_one`);
3. (pure-ring bridge) `char13` factors as `(z - 1) * g1 z * g2 z * g3 z * g4 z`
   over the four reversed cubics `g_j(z) = z^3 * f_j(1/z)` (`char13_factor`),
   so every root of the certificate cubics `f1..f4` of
   `q6_allroot_cert.py` is a characteristic root (`char13_of_g1..g4`).

No `Q6D` data is copied here; the recurrence coefficients are taken verbatim
from `Q6D.D_recur_13` (also used by `q6_allroot_decomp1.lean`).
-/

namespace Q6AllRootDecomp

/-- The order-13 recurrence step for the q=6 quadrangle sequence
    (coefficients of `Q6D.D_recur_13`). -/
def step13 (x : ℕ → ℝ) (n : ℕ) : ℝ :=
  (375 : ℝ) * x (n + 12) - (31905 : ℝ) * x (n + 11) + (940863 : ℝ) * x (n + 10)
    - (11023137 : ℝ) * x (n + 9) + (55190391 : ℝ) * x (n + 8) - (123722817 : ℝ) * x (n + 7)
    + (123722817 : ℝ) * x (n + 6) - (55190391 : ℝ) * x (n + 5) + (11023137 : ℝ) * x (n + 4)
    - (940863 : ℝ) * x (n + 3) + (31905 : ℝ) * x (n + 2) - (375 : ℝ) * x (n + 1) + x n

/-- Order-13 characteristic polynomial: `z^13 = 375 z^12 - 31905 z^11 + ... - 375 z + 1`
    is equivalent to `char13 z = 0`.  It is the reciprocal of the denominator
    polynomial `Q(x) = 1 - 375 x + 31905 x^2 - ... - x^13`. -/
def char13 (z : ℝ) : ℝ :=
  z ^ 13 - (375 : ℝ) * z ^ 12 + (31905 : ℝ) * z ^ 11 - (940863 : ℝ) * z ^ 10
    + (11023137 : ℝ) * z ^ 9 - (55190391 : ℝ) * z ^ 8 + (123722817 : ℝ) * z ^ 7
    - (123722817 : ℝ) * z ^ 6 + (55190391 : ℝ) * z ^ 5 - (11023137 : ℝ) * z ^ 4
    + (940863 : ℝ) * z ^ 3 - (31905 : ℝ) * z ^ 2 + (375 : ℝ) * z - 1

/-- Reversed cubics `g_j(z) = z^3 * f_j(1/z)` for the four cubics `f_j` of the
    certificate `q6_allroot_cert.py`:
    `f1 = x^3 - 269 x^2 + 66 x - 1`, `f2 = x^3 - 66 x^2 + 269 x - 1`,
    `f3 = x^3 - 26 x^2 + 13 x - 1`, `f4 = x^3 - 13 x^2 + 26 x - 1`. -/
def g1 (z : ℝ) : ℝ := 1 - (269 : ℝ) * z + (66 : ℝ) * z ^ 2 - z ^ 3
def g2 (z : ℝ) : ℝ := 1 - (66 : ℝ) * z + (269 : ℝ) * z ^ 2 - z ^ 3
def g3 (z : ℝ) : ℝ := 1 - (26 : ℝ) * z + (13 : ℝ) * z ^ 2 - z ^ 3
def g4 (z : ℝ) : ℝ := 1 - (13 : ℝ) * z + (26 : ℝ) * z ^ 2 - z ^ 3

/-- `char13 z = (z - 1) * g1 z * g2 z * g3 z * g4 z` (pure ring identity,
    verified independently in exact rational arithmetic). -/
theorem char13_factor (z : ℝ) :
    char13 z = (z - 1) * g1 z * g2 z * g3 z * g4 z := by
  unfold char13 g1 g2 g3 g4
  ring

/-- `z = 1` is a characteristic root. -/
theorem char13_one : char13 (1 : ℝ) = 0 := by
  unfold char13
  norm_num

/-- Roots of the reversed cubic `g1` are characteristic roots. -/
theorem char13_of_g1 (z : ℝ) (hz : g1 z = 0) : char13 z = 0 := by
  rw [char13_factor, hz]
  ring

/-- Roots of the reversed cubic `g2` are characteristic roots. -/
theorem char13_of_g2 (z : ℝ) (hz : g2 z = 0) : char13 z = 0 := by
  rw [char13_factor, hz]
  ring

/-- Roots of the reversed cubic `g3` are characteristic roots. -/
theorem char13_of_g3 (z : ℝ) (hz : g3 z = 0) : char13 z = 0 := by
  rw [char13_factor, hz]
  ring

/-- Roots of the reversed cubic `g4` are characteristic roots. -/
theorem char13_of_g4 (z : ℝ) (hz : g4 z = 0) : char13 z = 0 := by
  rw [char13_factor, hz]
  ring

/-- Palindromic symmetry: `char13 (z⁻¹) = -char13 z / z^13` for `z ≠ 0`.
    (The coefficients are anti-palindromic: `a_k = -a_{13-k}`.) -/
theorem char13_inv (z : ℝ) (hz0 : z ≠ 0) : char13 (z⁻¹) = -char13 z / z ^ 13 := by
  unfold char13
  field_simp [hz0]
  ring_nf

/-- A nonzero characteristic root stays a characteristic root under
    reciprocation (used to pass from a certificate root `r` to the geometric
    base `r⁻¹` of the decomposition). -/
theorem char13_inv_of_root (z : ℝ) (hz0 : z ≠ 0) (hz : char13 z = 0) :
    char13 (z⁻¹) = 0 := by
  rw [char13_inv z hz0, hz]
  ring

/-- Shift lemma: `z^(n+k) = z^k * z^n`. -/
private lemma pow_shift (z : ℝ) (n k : ℕ) : z ^ (n + k) = z ^ k * z ^ n := by
  rw [pow_add]
  ring

/-- The bracket appearing when `step13` is applied to a geometric term:
    `step13 (n ↦ c * z^n) n = c * z^n * bracket13 z`. -/
def bracket13 (z : ℝ) : ℝ :=
  (375 : ℝ) * z ^ 12 - (31905 : ℝ) * z ^ 11 + (940863 : ℝ) * z ^ 10
    - (11023137 : ℝ) * z ^ 9 + (55190391 : ℝ) * z ^ 8 - (123722817 : ℝ) * z ^ 7
    + (123722817 : ℝ) * z ^ 6 - (55190391 : ℝ) * z ^ 5 + (11023137 : ℝ) * z ^ 4
    - (940863 : ℝ) * z ^ 3 + (31905 : ℝ) * z ^ 2 - (375 : ℝ) * z + 1

private lemma step13_geom (z c : ℝ) (n : ℕ) :
    step13 (fun k : ℕ => c * z ^ k) n = c * z ^ n * bracket13 z := by
  unfold step13 bracket13
  simp only [pow_shift z n 12, pow_shift z n 11, pow_shift z n 10, pow_shift z n 9,
      pow_shift z n 8, pow_shift z n 7, pow_shift z n 6, pow_shift z n 5,
      pow_shift z n 4, pow_shift z n 3, pow_shift z n 2, pow_shift z n 1]
  ring

private lemma bracket13_eq_char13 (z : ℝ) : bracket13 z = z ^ 13 - char13 z := by
  unfold bracket13 char13
  ring

/-- Main geometric-term lemma: if `z` is a root of the order-13 characteristic
    polynomial, then every geometric term `n ↦ c * z^n` satisfies the q=6
    order-13 recurrence `x (n+13) = step13 x n`. -/
theorem geom_satisfies_step13 (z : ℝ) (hz : char13 z = 0) (c : ℝ) (n : ℕ) :
    (fun k : ℕ => c * z ^ k) (n + 13) = step13 (fun k : ℕ => c * z ^ k) n := by
  change c * z ^ (n + 13) = step13 (fun k : ℕ => c * z ^ k) n
  rw [step13_geom]
  rw [pow_shift z n 13]
  rw [bracket13_eq_char13 z]
  rw [hz]
  ring

/-- The constant sequence satisfies the q=6 order-13 recurrence
    (the `z = 1` case). -/
theorem const_satisfies_step13 (n : ℕ) :
    (fun _ : ℕ => (1 : ℝ)) (n + 13) = step13 (fun _ : ℕ => (1 : ℝ)) n := by
  unfold step13
  norm_num

/-- Candidate all-root right-hand side, summed form (one term per certificate
    root).  Shape matches the hypothesis `hD` of
    `Q6AllRootPositive.int_pos_of_all_roots_positive`. -/
noncomputable def rhs (r β : Fin 12 → ℝ) (n : ℕ) : ℝ :=
  (49 : ℝ) / 169 + ∑ i : Fin 12, β i * (r i)⁻¹ ^ (n + 1)

/-- The homogeneous order-13 difference operator:
    `lin x n = x (n+13) - step13 x n`.  A sequence satisfies the recurrence
    iff `lin` vanishes on it. -/
def lin (x : ℕ → ℝ) (n : ℕ) : ℝ := x (n + 13) - step13 x n

/-- Exponent reshaping: the `k ↦ β * b⁻¹ ^ (k+1)` term is a geometric term
    with base `b⁻¹` and coefficient `β * b⁻¹`. -/
private theorem geom_shift (b β : ℝ) (hb0 : b ≠ 0) (hroot : char13 b = 0) (n : ℕ) :
    (fun k : ℕ => β * b⁻¹ ^ (k + 1)) (n + 13) = step13 (fun k : ℕ => β * b⁻¹ ^ (k + 1)) n := by
  convert geom_satisfies_step13 (b⁻¹) (char13_inv_of_root b hb0 hroot)
      (β * b⁻¹) n using 2 <;> ring

/-- Linearity of `lin` under addition. -/
private theorem lin_add (x y : ℕ → ℝ) (n : ℕ) : lin (fun k => x k + y k) n = lin x n + lin y n := by
  unfold lin step13
  ring

/-- Linearity of `lin` under scalar multiplication. -/
private theorem lin_smul (c : ℝ) (x : ℕ → ℝ) (n : ℕ) :
    lin (fun k => c * x k) n = c * lin x n := by
  unfold lin step13
  ring

/-- The constant sequence is in the kernel of `lin`. -/
private theorem lin_const (n : ℕ) : lin (fun _ : ℕ => (1 : ℝ)) n = 0 := by
  unfold lin
  rw [const_satisfies_step13]
  ring

/-- Any geometric term `k ↦ c * z^k` with `char13 z = 0` is in the kernel
    of `lin` (restatement of `geom_satisfies_step13` in operator form). -/
private theorem lin_geom (z : ℝ) (hz : char13 z = 0) (c : ℝ) (n : ℕ) :
    lin (fun k : ℕ => c * z ^ k) n = 0 := by
  unfold lin
  rw [geom_satisfies_step13 z hz c n]
  ring

end Q6AllRootDecomp

#print axioms Q6AllRootDecomp.geom_satisfies_step13
#print axioms Q6AllRootDecomp.const_satisfies_step13
#print axioms Q6AllRootDecomp.char13_factor
#print axioms Q6AllRootDecomp.char13_of_g1
