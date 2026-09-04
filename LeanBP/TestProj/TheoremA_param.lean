import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

set_option maxHeartbeats 0
set_option linter.unusedVariables false

/-!
# Theorem A: equal-height two-block shifted regions are strictly beaten by the rectangle.

Formalized algebraic core (2026-08-24, compile-clean 2026-08-24).  The equal-height
overlap term satisfies

  G_b = Σ_{P∈Ωₛ} μₚ·(μₚ − μ_{P−s}) ,   Ωₛ = nonempty subsets of the overlap.

Write aᵢ = μ_{Pᵢ} and bᵢ = μ_{Pᵢ−s}.  The column-reflection isometry gives
Σ bᵢ² = Σ aᵢ² (renumbering via P ↦ φ(P−s)), encoded as hypothesis hA.  Then

  2·G_b = (Σ aᵢ² + Σ bᵢ²) − 2·Σ aᵢ·bᵢ = Σ (aᵢ − bᵢ)² ≥ 0.

No monotonicity, no PF, no sign-stability: only the reflection isometry and
squares are used.  This file proves the parametric inequality  A − C ≥ 0
given A = B (the reflection isometry) via the explicit square identity.

Statements match the paper symbols:  A = Σ μₚ²,  C = Σ μₚ·μ_{P−s},  G_b = A − C.
-/

namespace TheoremA

/- Pointwise identity used inside sums: (a − b)² = a² + b² − 2ab. -/
lemma sq_sub (a b : ℝ) : (a - b)^2 = a^2 + b^2 - 2 * a * b := by
  ring

/- Helper:  Σᵢ (aᵢ² + bᵢ² − 2aᵢbᵢ) = (Σ aᵢ²) + (Σ bᵢ²) − 2·(Σ aᵢbᵢ). -/
lemma sum_sq_minus_2ab (ι : Type) [Fintype ι] (a b : ι → ℝ) :
    (Finset.univ : Finset ι).sum (fun x => (a x)^2 + (b x)^2 - 2 * a x * b x)
    = (Finset.univ : Finset ι).sum (fun x => (a x)^2)
      + (Finset.univ : Finset ι).sum (fun x => (b x)^2)
      - 2 * (Finset.univ : Finset ι).sum (fun x => a x * b x) := by
  rw [Finset.sum_sub_distrib]
  rw [Finset.sum_add_distrib]
  have h2 : (Finset.univ : Finset ι).sum (fun x => 2 * a x * b x)
            = 2 * (Finset.univ : Finset ι).sum (fun x => a x * b x) := by
    have h3 : (Finset.univ : Finset ι).sum (fun x => 2 * a x * b x)
              = (Finset.univ : Finset ι).sum (fun x => 2 * (a x * b x)) := by
      apply Finset.sum_congr rfl
      intro x hx
      ring
    rw [h3]
    rw [Finset.mul_sum]
  rw [h2]

/- The algebraic core (Theorem A, parametric):  given the reflection isometry
   Σ bᵢ² = Σ aᵢ²  (hypothesis hA), we have  A − C = (1/2)·Σ (aᵢ − bᵢ)² ≥ 0
   where A = Σ aᵢ² and C = Σ aᵢ·bᵢ.  In paper notation:  G_b = A − C ≥ 0. -/
theorem twoBlock_Gb_nonneg (ι : Type) [Fintype ι]
    (a b : ι → ℝ)
    (hA : (Finset.univ : Finset ι).sum (fun x => (a x)^2)
          = (Finset.univ : Finset ι).sum (fun x => (b x)^2)) :
    0 ≤ (Finset.univ : Finset ι).sum (fun x => (a x)^2)
      - (Finset.univ : Finset ι).sum (fun x => a x * b x) := by
  have hcore : (Finset.univ : Finset ι).sum (fun x => (a x - b x)^2)
               = 2 * ((Finset.univ : Finset ι).sum (fun x => (a x)^2)
                      - (Finset.univ : Finset ι).sum (fun x => a x * b x)) := by
    calc
      (Finset.univ : Finset ι).sum (fun x => (a x - b x)^2)
          = (Finset.univ : Finset ι).sum (fun x => (a x)^2 + (b x)^2 - 2 * a x * b x) := by
            apply Finset.sum_congr rfl
            intro x hx
            exact sq_sub (a x) (b x)
      _ = (Finset.univ : Finset ι).sum (fun x => (a x)^2)
          + (Finset.univ : Finset ι).sum (fun x => (b x)^2)
          - 2 * (Finset.univ : Finset ι).sum (fun x => a x * b x) := by
            exact sum_sq_minus_2ab ι a b
      _ = 2 * ((Finset.univ : Finset ι).sum (fun x => (a x)^2)
               - (Finset.univ : Finset ι).sum (fun x => a x * b x)) := by
            rw [hA]
            ring
  have hideq : (Finset.univ : Finset ι).sum (fun x => (a x)^2)
               - (Finset.univ : Finset ι).sum (fun x => a x * b x)
               = (1/2) * (Finset.univ : Finset ι).sum (fun x => (a x - b x)^2) := by
    rw [hcore]
    ring
  have hnonneg : 0 ≤ (Finset.univ : Finset ι).sum (fun x => (a x - b x)^2) := by
    exact Finset.sum_nonneg (fun x hx => sq_nonneg (a x - b x))
  rw [hideq]
  exact mul_nonneg (by positivity : 0 ≤ (1/2 : ℝ)) hnonneg

end TheoremA