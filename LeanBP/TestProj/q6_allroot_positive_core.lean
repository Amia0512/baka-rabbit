import Mathlib

open scoped BigOperators

namespace Q6AllRootPositive

theorem int_pos_of_all_roots_positive {d : ℤ} {n : ℕ}
    {r β : Fin 12 → ℝ}
    (hr : ∀ i, 0 < r i)
    (hβ : ∀ i, 0 < β i)
    (hD : (d : ℝ) = (49 : ℝ) / 169 + ∑ i, β i * (r i)⁻¹ ^ (n + 1)) :
    0 < d := by
  have hsum : 0 ≤ ∑ i, β i * (r i)⁻¹ ^ (n + 1) := by
    apply Finset.sum_nonneg
    intro i hi
    exact mul_nonneg (hβ i).le (pow_nonneg (inv_pos.mpr (hr i)).le (n + 1))
  have hdReal : (0 : ℝ) < d := by
    rw [hD]
    nlinarith [show (0 : ℝ) < 49 / 169 by norm_num]
  exact_mod_cast hdReal

end Q6AllRootPositive

#print axioms Q6AllRootPositive.int_pos_of_all_roots_positive
