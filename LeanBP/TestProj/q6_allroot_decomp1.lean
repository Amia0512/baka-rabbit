import Mathlib

set_option maxHeartbeats 0

/-!
# q=6 all-root decomposition: order-13 recurrence uniqueness (generic bridge)

Generic reusable lemma for the q=6 candidate decomposition.  If two real
sequences satisfy the same order-13 palindromic recurrence (the one proved
for `Q6D.D` in `q6_drecur13_v2.lean`) and agree on the first 13 terms, then
they agree everywhere.  This reduces the "all n" decomposition identity to:

  (1) the candidate RHS satisfies the order-13 recurrence, and
  (2) it matches the 13 initial values D(0)..D(12).

No `Q6D` definitions are copied here; the recurrence coefficients are taken
verbatim from `Q6D.D_recur_13`.
-/

namespace Q6AllRootDecomp

/-- The order-13 recurrence step for the q=6 quadrangle sequence
    (coefficients of `Q6D.D_recur_13`). -/
def step13 (x : ℕ → ℝ) (n : ℕ) : ℝ :=
  (375 : ℝ) * x (n + 12) - (31905 : ℝ) * x (n + 11) + (940863 : ℝ) * x (n + 10)
    - (11023137 : ℝ) * x (n + 9) + (55190391 : ℝ) * x (n + 8) - (123722817 : ℝ) * x (n + 7)
    + (123722817 : ℝ) * x (n + 6) - (55190391 : ℝ) * x (n + 5) + (11023137 : ℝ) * x (n + 4)
    - (940863 : ℝ) * x (n + 3) + (31905 : ℝ) * x (n + 2) - (375 : ℝ) * x (n + 1) + x n

/-- Two sequences satisfying the q=6 order-13 recurrence with the same first
    13 terms coincide everywhere. -/
theorem seq_eq_of_rec13 {a b : ℕ → ℝ}
    (ha : ∀ n, a (n + 13) = step13 a n)
    (hb : ∀ n, b (n + 13) = step13 b n)
    (hinit : ∀ k < 13, a k = b k) :
    ∀ n, a n = b n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      match n with
      | 0 => exact hinit 0 (by norm_num)
      | 1 => exact hinit 1 (by norm_num)
      | 2 => exact hinit 2 (by norm_num)
      | 3 => exact hinit 3 (by norm_num)
      | 4 => exact hinit 4 (by norm_num)
      | 5 => exact hinit 5 (by norm_num)
      | 6 => exact hinit 6 (by norm_num)
      | 7 => exact hinit 7 (by norm_num)
      | 8 => exact hinit 8 (by norm_num)
      | 9 => exact hinit 9 (by norm_num)
      | 10 => exact hinit 10 (by norm_num)
      | 11 => exact hinit 11 (by norm_num)
      | 12 => exact hinit 12 (by norm_num)
      | m + 13 =>
          rw [ha m, hb m]
          unfold step13
          have ih12 : a (m + 12) = b (m + 12) := ih (m + 12) (by omega)
          have ih11 : a (m + 11) = b (m + 11) := ih (m + 11) (by omega)
          have ih10 : a (m + 10) = b (m + 10) := ih (m + 10) (by omega)
          have ih9 : a (m + 9) = b (m + 9) := ih (m + 9) (by omega)
          have ih8 : a (m + 8) = b (m + 8) := ih (m + 8) (by omega)
          have ih7 : a (m + 7) = b (m + 7) := ih (m + 7) (by omega)
          have ih6 : a (m + 6) = b (m + 6) := ih (m + 6) (by omega)
          have ih5 : a (m + 5) = b (m + 5) := ih (m + 5) (by omega)
          have ih4 : a (m + 4) = b (m + 4) := ih (m + 4) (by omega)
          have ih3 : a (m + 3) = b (m + 3) := ih (m + 3) (by omega)
          have ih2 : a (m + 2) = b (m + 2) := ih (m + 2) (by omega)
          have ih1 : a (m + 1) = b (m + 1) := ih (m + 1) (by omega)
          have ih0 : a m = b m := ih m (by omega)
          rw [ih12, ih11, ih10, ih9, ih8, ih7, ih6, ih5, ih4, ih3, ih2, ih1, ih0]

end Q6AllRootDecomp

#print axioms Q6AllRootDecomp.seq_eq_of_rec13
