import Mathlib
import TestProj.q6_drecur13_v2
import TestProj.q6_allroot_decomp2
import TestProj.q6_allroot_positive_core

open scoped BigOperators
set_option maxHeartbeats 0

namespace Q6AllRootAssemble

open Q6AllRootDecomp

noncomputable def rhs (r β : Fin 12 → ℝ) (n : ℕ) : ℝ :=
  49 / 169 + ∑ i : Fin 12, β i * (r i)⁻¹ ^ (n + 1)

private lemma pow_shift (z : ℝ) (n k : ℕ) : z ^ (n + k) = z ^ k * z ^ n := by
  rw [pow_add]
  ring

/-- A shifted geometric term with a characteristic base satisfies the order-13 step. -/
theorem geom_term_step (r β : ℝ) (hroot : char13 (r⁻¹) = 0) (n : ℕ) :
    (fun k : ℕ => β * r⁻¹ ^ (k + 1)) (n + 13) =
      step13 (fun k : ℕ => β * r⁻¹ ^ (k + 1)) n := by
  convert Q6AllRootDecomp.geom_satisfies_step13 (r⁻¹) hroot
      (β * r⁻¹) n using 2 <;> ring

private lemma step_add (x y : ℕ → ℝ) (n : ℕ) :
    step13 (fun k => x k + y k) n = step13 x n + step13 y n := by
  unfold step13
  ring

private lemma step_const (n : ℕ) : step13 (fun _ : ℕ => (1 : ℝ)) n = 1 := by
  unfold step13
  norm_num

/-- Parameterized recurrence lemma for the complete candidate right-hand side. -/
theorem rhs_step13 {r β : Fin 12 → ℝ}
    (hroot : ∀ i, char13 ((r i)⁻¹) = 0) (n : ℕ) :
    rhs r β (n + 13) = step13 (rhs r β) n := by
  have hsum_step :
      step13 (fun k => ∑ i, β i * (r i)⁻¹ ^ (k + 1)) n =
        ∑ i, step13 (fun k => β i * (r i)⁻¹ ^ (k + 1)) n := by
    unfold step13
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
    repeat' rw [Finset.sum_mul]
    repeat' rw [Finset.mul_sum]
  have hconst : step13 (fun _ : ℕ => (49 / 169 : ℝ)) n = 49 / 169 := by
    unfold step13
    norm_num
  calc
    rhs r β (n + 13) = 49 / 169 +
        ∑ i, (fun k : ℕ => β i * (r i)⁻¹ ^ (k + 1)) (n + 13) := by
          rfl
    _ = 49 / 169 +
        ∑ i, step13 (fun k => β i * (r i)⁻¹ ^ (k + 1)) n := by
          congr 1
          apply Finset.sum_congr rfl
          intro i hi
          exact geom_term_step (r i) (β i) (hroot i) n
    _ = step13 (fun _ : ℕ => (49 / 169 : ℝ)) n +
        step13 (fun k => ∑ i, β i * (r i)⁻¹ ^ (k + 1)) n := by
          rw [hconst, hsum_step]
    _ = step13 (rhs r β) n := by
          change step13 (fun _ : ℕ => (49 / 169 : ℝ)) n +
              step13 (fun k => ∑ i, β i * (r i)⁻¹ ^ (k + 1)) n =
            step13 (fun k => 49 / 169 + ∑ i, β i * (r i)⁻¹ ^ (k + 1)) n
          rw [step_add]

/-- Two sequences satisfying the q=6 order-13 recurrence with the same first
    13 terms coincide everywhere. -/
private theorem seq_eq_of_rec13 {a b : ℕ → ℝ}
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

/-- Minimal bridge: the genuine `D` recurrence and the 13 initial matches imply
     the all-n decomposition by the order-13 uniqueness lemma. -/
theorem D_eq_rhs_of_initial
    {r β : Fin 12 → ℝ}
    (hroot : ∀ i, char13 ((r i)⁻¹) = 0)
    (hinit : ∀ k < 13, (Q6D.D k : ℝ) = rhs r β k) :
    ∀ n, (Q6D.D n : ℝ) = rhs r β n := by
  have hDrec : ∀ n, (Q6D.D (n + 13) : ℝ) =
      step13 (fun k => (Q6D.D k : ℝ)) n := by
    intro n
    have h := Q6D.D_recur_13 n
    change (Q6D.D (n + 13) : ℝ) =
      (375 : ℝ) * Q6D.D (n + 12) - 31905 * Q6D.D (n + 11) +
        940863 * Q6D.D (n + 10) - 11023137 * Q6D.D (n + 9) +
        55190391 * Q6D.D (n + 8) - 123722817 * Q6D.D (n + 7) +
        123722817 * Q6D.D (n + 6) - 55190391 * Q6D.D (n + 5) +
        11023137 * Q6D.D (n + 4) - 940863 * Q6D.D (n + 3) +
        31905 * Q6D.D (n + 2) - 375 * Q6D.D (n + 1) + Q6D.D n
    exact_mod_cast h
  exact seq_eq_of_rec13 hDrec (rhs_step13 hroot) hinit

/-- Positivity entry point once the root and weight inequalities and the
    preceding decomposition bridge have been supplied. -/
theorem D_pos_of_initial
    {d : ℤ} {n : ℕ} {r β : Fin 12 → ℝ}
    (hd : d = Q6D.D n)
    (hr : ∀ i, 0 < r i) (hβ : ∀ i, 0 < β i)
    (hroot : ∀ i, char13 ((r i)⁻¹) = 0)
    (hinit : ∀ k < 13, (Q6D.D k : ℝ) = rhs r β k)
    (hdecomp : ∀ m, (Q6D.D m : ℝ) = rhs r β m) : 0 < d := by
  have hD : (d : ℝ) = rhs r β n := by
    rw [show (d : ℝ) = (Q6D.D n : ℝ) by exact_mod_cast hd]
    exact hdecomp n
  exact Q6AllRootPositive.int_pos_of_all_roots_positive hr hβ hD

end Q6AllRootAssemble

#print axioms Q6AllRootAssemble.rhs_step13
#print axioms Q6AllRootAssemble.D_eq_rhs_of_initial
