import Mathlib

open scoped Topology
open Set

set_option maxHeartbeats 0

namespace Q6AllRoot

abbrev R := Real

def f1o1 (x : R) : R := x^3 - 269*x^2 + 66*x - 1
def N1o1 (x : R) : R := -17*x^2 + 3443*x - 374
def fp1o1 (x : R) : R := 3*x^2 - 538*x + 66

noncomputable def p_f1o1 : Polynomial R := Polynomial.X ^ 3 - 269*Polynomial.X ^ 2 + 66*Polynomial.X - 1
lemma poly_eval_f1o1 (x : R) : Polynomial.eval x p_f1o1 = f1o1 x := by
  unfold f1o1 p_f1o1
  simp [Polynomial.eval]

lemma cont_f1o1 (lo hi : R) : ContinuousOn f1o1 (Set.Icc lo hi) := by
  rw [show f1o1 = fun x : R => Polynomial.eval x p_f1o1 by
    funext x
    simp [f1o1, poly_eval_f1o1]]
  exact Polynomial.continuousOn p_f1o1

lemma root_f1o1 : ∃ p : R, p ∈ Set.Icc (537/2 : R) (269 : R) ∧ f1o1 p = 0 := by
  have hmem : (0 : R) ∈ Set.Icc (f1o1 (537/2 : R)) (f1o1 (269 : R)) := by
    constructor <;> unfold f1o1 <;> norm_num
  have hpre : (0 : R) ∈ f1o1 '' (Set.Icc (537/2 : R) (269 : R)) :=
    intermediate_value_Icc (by norm_num : (537/2 : R) ≤ (269 : R)) (cont_f1o1 (537/2 : R) (269 : R)) hmem
  rcases hpre with ⟨p, hpI, hp⟩
  exact ⟨p, hpI, hp⟩

lemma N1o1_mono : AntitoneOn N1o1 (Set.Icc (537/2 : R) (269 : R)) := by
  intro x hx y hy hxy
  have hcalc : N1o1 y - N1o1 x = (y - x) * (-17 * (x + y) + 3443) := by
    unfold N1o1; ring_nf
  have hbound : -17 * (x + y) + 3443 <= 0 := by nlinarith [hx.1, hx.2, hy.1, hy.2]
  have hneg : N1o1 y - N1o1 x <= 0 := by
    rw [hcalc]
    exact mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hxy) hbound
  exact sub_nonpos.mp hneg

lemma fp1o1_mono : MonotoneOn fp1o1 (Set.Icc (537/2 : R) (269 : R)) := by
  intro x hx y hy hxy
  have hcalc : fp1o1 y - fp1o1 x = (y - x) * (3 * (x + y) + -538) := by
    unfold fp1o1; ring_nf
  have hbound : 0 <= 3 * (x + y) + -538 := by nlinarith [hx.1, hx.2, hy.1, hy.2]
  have hsub : 0 <= fp1o1 y - fp1o1 x := by
    rw [hcalc]
    exact mul_nonneg (sub_nonneg.mpr hxy) hbound
  exact sub_nonneg.mp hsub

lemma N1o1_lo : N1o1 (537/2 : R) < 0 := by unfold N1o1; norm_num
lemma fp1o1_lo : 0 < fp1o1 (537/2 : R) := by unfold fp1o1; norm_num

theorem cert_f1o1 : ∃ p : R, p ∈ Set.Icc (537/2 : R) (269 : R) ∧ f1o1 p = 0 ∧ N1o1 p < 0 ∧ 0 < fp1o1 p := by
  rcases root_f1o1 with ⟨p, hpI, hp0⟩
  refine ⟨p, hpI, hp0, ?_, ?_⟩
  · have hN : N1o1 p ≤ N1o1 (537/2 : R) := N1o1_mono (by norm_num : (537/2 : R) ∈ Set.Icc (537/2 : R) (269 : R)) hpI (by simpa using hpI.1)
    have hz : N1o1 (537/2 : R) < 0 := N1o1_lo
    exact lt_of_le_of_lt hN hz
  · have hF : fp1o1 (537/2 : R) ≤ fp1o1 p := fp1o1_mono (by norm_num : (537/2 : R) ∈ Set.Icc (537/2 : R) (269 : R)) hpI (by simpa using hpI.1)
    have hz : 0 < fp1o1 (537/2 : R) := fp1o1_lo
    exact lt_of_lt_of_le hz hF

def f2o1 (x : R) : R := x^3 - 66*x^2 + 269*x - 1
def N2o1 (x : R) : R := -17*x^2 + 748*x - 1130
def fp2o1 (x : R) : R := 3*x^2 - 132*x + 269

noncomputable def p_f2o1 : Polynomial R := Polynomial.X ^ 3 - 66*Polynomial.X ^ 2 + 269*Polynomial.X - 1
lemma poly_eval_f2o1 (x : R) : Polynomial.eval x p_f2o1 = f2o1 x := by
  unfold f2o1 p_f2o1
  simp [Polynomial.eval]

lemma cont_f2o1 (lo hi : R) : ContinuousOn f2o1 (Set.Icc lo hi) := by
  rw [show f2o1 = fun x : R => Polynomial.eval x p_f2o1 by
    funext x
    simp [f2o1, poly_eval_f2o1]]
  exact Polynomial.continuousOn p_f2o1

lemma root_f2o1 : ∃ p : R, p ∈ Set.Icc (4 : R) (9/2 : R) ∧ f2o1 p = 0 := by
  let g := fun x : R => -f2o1 x
  have hcontg : ContinuousOn g (Set.Icc (4 : R) (9/2 : R)) := by
    exact (cont_f2o1 (4 : R) (9/2 : R)).neg
  have hmem : (0 : R) ∈ Set.Icc (g (4 : R)) (g (9/2 : R)) := by
    constructor <;> unfold g f2o1 <;> norm_num
  have hpre : (0 : R) ∈ g '' (Set.Icc (4 : R) (9/2 : R)) :=
    intermediate_value_Icc (by norm_num : (4 : R) ≤ (9/2 : R)) hcontg hmem
  rcases hpre with ⟨p, hpI, hp⟩
  use p, hpI
  unfold g at hp
  linarith

lemma N2o1_mono : MonotoneOn N2o1 (Set.Icc (4 : R) (9/2 : R)) := by
  intro x hx y hy hxy
  have hcalc : N2o1 y - N2o1 x = (y - x) * (-17 * (x + y) + 748) := by
    unfold N2o1; ring_nf
  have hbound : 0 <= -17 * (x + y) + 748 := by nlinarith [hx.1, hx.2, hy.1, hy.2]
  have hsub : 0 <= N2o1 y - N2o1 x := by
    rw [hcalc]
    exact mul_nonneg (sub_nonneg.mpr hxy) hbound
  exact sub_nonneg.mp hsub

lemma fp2o1_mono : AntitoneOn fp2o1 (Set.Icc (4 : R) (9/2 : R)) := by
  intro x hx y hy hxy
  have hcalc : fp2o1 y - fp2o1 x = (y - x) * (3 * (x + y) + -132) := by
    unfold fp2o1; ring_nf
  have hbound : 3 * (x + y) + -132 <= 0 := by nlinarith [hx.1, hx.2, hy.1, hy.2]
  have hneg : fp2o1 y - fp2o1 x <= 0 := by
    rw [hcalc]
    exact mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hxy) hbound
  exact sub_nonpos.mp hneg

lemma N2o1_lo : 0 < N2o1 (4 : R) := by unfold N2o1; norm_num
lemma fp2o1_lo : fp2o1 (4 : R) < 0 := by unfold fp2o1; norm_num

theorem cert_f2o1 : ∃ p : R, p ∈ Set.Icc (4 : R) (9/2 : R) ∧ f2o1 p = 0 ∧ 0 < N2o1 p ∧ fp2o1 p < 0 := by
  rcases root_f2o1 with ⟨p, hpI, hp0⟩
  refine ⟨p, hpI, hp0, ?_, ?_⟩
  · have hN : N2o1 (4 : R) ≤ N2o1 p := N2o1_mono (by norm_num : (4 : R) ∈ Set.Icc (4 : R) (9/2 : R)) hpI (by simpa using hpI.1)
    have hz : 0 < N2o1 (4 : R) := N2o1_lo
    exact lt_of_lt_of_le hz hN
  · have hF : fp2o1 p ≤ fp2o1 (4 : R) := fp2o1_mono (by norm_num : (4 : R) ∈ Set.Icc (4 : R) (9/2 : R)) hpI (by simpa using hpI.1)
    have hz : fp2o1 (4 : R) < 0 := fp2o1_lo
    exact lt_of_le_of_lt hF hz

def f2o2 (x : R) : R := x^3 - 66*x^2 + 269*x - 1
def N2o2 (x : R) : R := -17*x^2 + 748*x - 1130
def fp2o2 (x : R) : R := 3*x^2 - 132*x + 269

noncomputable def p_f2o2 : Polynomial R := Polynomial.X ^ 3 - 66*Polynomial.X ^ 2 + 269*Polynomial.X - 1
lemma poly_eval_f2o2 (x : R) : Polynomial.eval x p_f2o2 = f2o2 x := by
  unfold f2o2 p_f2o2
  simp [Polynomial.eval]

lemma cont_f2o2 (lo hi : R) : ContinuousOn f2o2 (Set.Icc lo hi) := by
  rw [show f2o2 = fun x : R => Polynomial.eval x p_f2o2 by
    funext x
    simp [f2o2, poly_eval_f2o2]]
  exact Polynomial.continuousOn p_f2o2

lemma root_f2o2 : ∃ p : R, p ∈ Set.Icc (123/2 : R) (62 : R) ∧ f2o2 p = 0 := by
  have hmem : (0 : R) ∈ Set.Icc (f2o2 (123/2 : R)) (f2o2 (62 : R)) := by
    constructor <;> unfold f2o2 <;> norm_num
  have hpre : (0 : R) ∈ f2o2 '' (Set.Icc (123/2 : R) (62 : R)) :=
    intermediate_value_Icc (by norm_num : (123/2 : R) ≤ (62 : R)) (cont_f2o2 (123/2 : R) (62 : R)) hmem
  rcases hpre with ⟨p, hpI, hp⟩
  exact ⟨p, hpI, hp⟩

lemma N2o2_mono : AntitoneOn N2o2 (Set.Icc (123/2 : R) (62 : R)) := by
  intro x hx y hy hxy
  have hcalc : N2o2 y - N2o2 x = (y - x) * (-17 * (x + y) + 748) := by
    unfold N2o2; ring_nf
  have hbound : -17 * (x + y) + 748 <= 0 := by nlinarith [hx.1, hx.2, hy.1, hy.2]
  have hneg : N2o2 y - N2o2 x <= 0 := by
    rw [hcalc]
    exact mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hxy) hbound
  exact sub_nonpos.mp hneg

lemma fp2o2_mono : MonotoneOn fp2o2 (Set.Icc (123/2 : R) (62 : R)) := by
  intro x hx y hy hxy
  have hcalc : fp2o2 y - fp2o2 x = (y - x) * (3 * (x + y) + -132) := by
    unfold fp2o2; ring_nf
  have hbound : 0 <= 3 * (x + y) + -132 := by nlinarith [hx.1, hx.2, hy.1, hy.2]
  have hsub : 0 <= fp2o2 y - fp2o2 x := by
    rw [hcalc]
    exact mul_nonneg (sub_nonneg.mpr hxy) hbound
  exact sub_nonneg.mp hsub

lemma N2o2_lo : N2o2 (123/2 : R) < 0 := by unfold N2o2; norm_num
lemma fp2o2_lo : 0 < fp2o2 (123/2 : R) := by unfold fp2o2; norm_num

theorem cert_f2o2 : ∃ p : R, p ∈ Set.Icc (123/2 : R) (62 : R) ∧ f2o2 p = 0 ∧ N2o2 p < 0 ∧ 0 < fp2o2 p := by
  rcases root_f2o2 with ⟨p, hpI, hp0⟩
  refine ⟨p, hpI, hp0, ?_, ?_⟩
  · have hN : N2o2 p ≤ N2o2 (123/2 : R) := N2o2_mono (by norm_num : (123/2 : R) ∈ Set.Icc (123/2 : R) (62 : R)) hpI (by simpa using hpI.1)
    have hz : N2o2 (123/2 : R) < 0 := N2o2_lo
    exact lt_of_le_of_lt hN hz
  · have hF : fp2o2 (123/2 : R) ≤ fp2o2 p := fp2o2_mono (by norm_num : (123/2 : R) ∈ Set.Icc (123/2 : R) (62 : R)) hpI (by simpa using hpI.1)
    have hz : 0 < fp2o2 (123/2 : R) := fp2o2_lo
    exact lt_of_lt_of_le hz hF

def f3o1 (x : R) : R := x^3 - 26*x^2 + 13*x - 1
def N3o1 (x : R) : R := -43*x^2 + 827*x - 184
def fp3o1 (x : R) : R := 3*x^2 - 52*x + 13

noncomputable def p_f3o1 : Polynomial R := Polynomial.X ^ 3 - 26*Polynomial.X ^ 2 + 13*Polynomial.X - 1
lemma poly_eval_f3o1 (x : R) : Polynomial.eval x p_f3o1 = f3o1 x := by
  unfold f3o1 p_f3o1
  simp [Polynomial.eval]

lemma cont_f3o1 (lo hi : R) : ContinuousOn f3o1 (Set.Icc lo hi) := by
  rw [show f3o1 = fun x : R => Polynomial.eval x p_f3o1 by
    funext x
    simp [f3o1, poly_eval_f3o1]]
  exact Polynomial.continuousOn p_f3o1

lemma root_f3o1 : ∃ p : R, p ∈ Set.Icc (25 : R) (51/2 : R) ∧ f3o1 p = 0 := by
  have hmem : (0 : R) ∈ Set.Icc (f3o1 (25 : R)) (f3o1 (51/2 : R)) := by
    constructor <;> unfold f3o1 <;> norm_num
  have hpre : (0 : R) ∈ f3o1 '' (Set.Icc (25 : R) (51/2 : R)) :=
    intermediate_value_Icc (by norm_num : (25 : R) ≤ (51/2 : R)) (cont_f3o1 (25 : R) (51/2 : R)) hmem
  rcases hpre with ⟨p, hpI, hp⟩
  exact ⟨p, hpI, hp⟩

lemma N3o1_mono : AntitoneOn N3o1 (Set.Icc (25 : R) (51/2 : R)) := by
  intro x hx y hy hxy
  have hcalc : N3o1 y - N3o1 x = (y - x) * (-43 * (x + y) + 827) := by
    unfold N3o1; ring_nf
  have hbound : -43 * (x + y) + 827 <= 0 := by nlinarith [hx.1, hx.2, hy.1, hy.2]
  have hneg : N3o1 y - N3o1 x <= 0 := by
    rw [hcalc]
    exact mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hxy) hbound
  exact sub_nonpos.mp hneg

lemma fp3o1_mono : MonotoneOn fp3o1 (Set.Icc (25 : R) (51/2 : R)) := by
  intro x hx y hy hxy
  have hcalc : fp3o1 y - fp3o1 x = (y - x) * (3 * (x + y) + -52) := by
    unfold fp3o1; ring_nf
  have hbound : 0 <= 3 * (x + y) + -52 := by nlinarith [hx.1, hx.2, hy.1, hy.2]
  have hsub : 0 <= fp3o1 y - fp3o1 x := by
    rw [hcalc]
    exact mul_nonneg (sub_nonneg.mpr hxy) hbound
  exact sub_nonneg.mp hsub

lemma N3o1_lo : N3o1 (25 : R) < 0 := by unfold N3o1; norm_num
lemma fp3o1_lo : 0 < fp3o1 (25 : R) := by unfold fp3o1; norm_num

theorem cert_f3o1 : ∃ p : R, p ∈ Set.Icc (25 : R) (51/2 : R) ∧ f3o1 p = 0 ∧ N3o1 p < 0 ∧ 0 < fp3o1 p := by
  rcases root_f3o1 with ⟨p, hpI, hp0⟩
  refine ⟨p, hpI, hp0, ?_, ?_⟩
  · have hN : N3o1 p ≤ N3o1 (25 : R) := N3o1_mono (by norm_num : (25 : R) ∈ Set.Icc (25 : R) (51/2 : R)) hpI (by simpa using hpI.1)
    have hz : N3o1 (25 : R) < 0 := N3o1_lo
    exact lt_of_le_of_lt hN hz
  · have hF : fp3o1 (25 : R) ≤ fp3o1 p := fp3o1_mono (by norm_num : (25 : R) ∈ Set.Icc (25 : R) (51/2 : R)) hpI (by simpa using hpI.1)
    have hz : 0 < fp3o1 (25 : R) := fp3o1_lo
    exact lt_of_lt_of_le hz hF

def f4o1 (x : R) : R := x^3 - 13*x^2 + 26*x - 1
def N4o1 (x : R) : R := -43*x^2 + 375*x - 291
def fp4o1 (x : R) : R := 3*x^2 - 26*x + 26

noncomputable def p_f4o1 : Polynomial R := Polynomial.X ^ 3 - 13*Polynomial.X ^ 2 + 26*Polynomial.X - 1
lemma poly_eval_f4o1 (x : R) : Polynomial.eval x p_f4o1 = f4o1 x := by
  unfold f4o1 p_f4o1
  simp [Polynomial.eval]

lemma cont_f4o1 (lo hi : R) : ContinuousOn f4o1 (Set.Icc lo hi) := by
  rw [show f4o1 = fun x : R => Polynomial.eval x p_f4o1 by
    funext x
    simp [f4o1, poly_eval_f4o1]]
  exact Polynomial.continuousOn p_f4o1

lemma root_f4o1 : ∃ p : R, p ∈ Set.Icc (2 : R) (5/2 : R) ∧ f4o1 p = 0 := by
  let g := fun x : R => -f4o1 x
  have hcontg : ContinuousOn g (Set.Icc (2 : R) (5/2 : R)) := by
    exact (cont_f4o1 (2 : R) (5/2 : R)).neg
  have hmem : (0 : R) ∈ Set.Icc (g (2 : R)) (g (5/2 : R)) := by
    constructor <;> unfold g f4o1 <;> norm_num
  have hpre : (0 : R) ∈ g '' (Set.Icc (2 : R) (5/2 : R)) :=
    intermediate_value_Icc (by norm_num : (2 : R) ≤ (5/2 : R)) hcontg hmem
  rcases hpre with ⟨p, hpI, hp⟩
  use p, hpI
  unfold g at hp
  linarith

lemma N4o1_mono : MonotoneOn N4o1 (Set.Icc (2 : R) (5/2 : R)) := by
  intro x hx y hy hxy
  have hcalc : N4o1 y - N4o1 x = (y - x) * (-43 * (x + y) + 375) := by
    unfold N4o1; ring_nf
  have hbound : 0 <= -43 * (x + y) + 375 := by nlinarith [hx.1, hx.2, hy.1, hy.2]
  have hsub : 0 <= N4o1 y - N4o1 x := by
    rw [hcalc]
    exact mul_nonneg (sub_nonneg.mpr hxy) hbound
  exact sub_nonneg.mp hsub

lemma fp4o1_mono : AntitoneOn fp4o1 (Set.Icc (2 : R) (5/2 : R)) := by
  intro x hx y hy hxy
  have hcalc : fp4o1 y - fp4o1 x = (y - x) * (3 * (x + y) + -26) := by
    unfold fp4o1; ring_nf
  have hbound : 3 * (x + y) + -26 <= 0 := by nlinarith [hx.1, hx.2, hy.1, hy.2]
  have hneg : fp4o1 y - fp4o1 x <= 0 := by
    rw [hcalc]
    exact mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hxy) hbound
  exact sub_nonpos.mp hneg

lemma N4o1_lo : 0 < N4o1 (2 : R) := by unfold N4o1; norm_num
lemma fp4o1_lo : fp4o1 (2 : R) < 0 := by unfold fp4o1; norm_num

theorem cert_f4o1 : ∃ p : R, p ∈ Set.Icc (2 : R) (5/2 : R) ∧ f4o1 p = 0 ∧ 0 < N4o1 p ∧ fp4o1 p < 0 := by
  rcases root_f4o1 with ⟨p, hpI, hp0⟩
  refine ⟨p, hpI, hp0, ?_, ?_⟩
  · have hN : N4o1 (2 : R) ≤ N4o1 p := N4o1_mono (by norm_num : (2 : R) ∈ Set.Icc (2 : R) (5/2 : R)) hpI (by simpa using hpI.1)
    have hz : 0 < N4o1 (2 : R) := N4o1_lo
    exact lt_of_lt_of_le hz hN
  · have hF : fp4o1 p ≤ fp4o1 (2 : R) := fp4o1_mono (by norm_num : (2 : R) ∈ Set.Icc (2 : R) (5/2 : R)) hpI (by simpa using hpI.1)
    have hz : fp4o1 (2 : R) < 0 := fp4o1_lo
    exact lt_of_le_of_lt hF hz

def f4o2 (x : R) : R := x^3 - 13*x^2 + 26*x - 1
def N4o2 (x : R) : R := -43*x^2 + 375*x - 291
def fp4o2 (x : R) : R := 3*x^2 - 26*x + 26

noncomputable def p_f4o2 : Polynomial R := Polynomial.X ^ 3 - 13*Polynomial.X ^ 2 + 26*Polynomial.X - 1
lemma poly_eval_f4o2 (x : R) : Polynomial.eval x p_f4o2 = f4o2 x := by
  unfold f4o2 p_f4o2
  simp [Polynomial.eval]

lemma cont_f4o2 (lo hi : R) : ContinuousOn f4o2 (Set.Icc lo hi) := by
  rw [show f4o2 = fun x : R => Polynomial.eval x p_f4o2 by
    funext x
    simp [f4o2, poly_eval_f4o2]]
  exact Polynomial.continuousOn p_f4o2

lemma root_f4o2 : ∃ p : R, p ∈ Set.Icc (21/2 : R) (11 : R) ∧ f4o2 p = 0 := by
  have hmem : (0 : R) ∈ Set.Icc (f4o2 (21/2 : R)) (f4o2 (11 : R)) := by
    constructor <;> unfold f4o2 <;> norm_num
  have hpre : (0 : R) ∈ f4o2 '' (Set.Icc (21/2 : R) (11 : R)) :=
    intermediate_value_Icc (by norm_num : (21/2 : R) ≤ (11 : R)) (cont_f4o2 (21/2 : R) (11 : R)) hmem
  rcases hpre with ⟨p, hpI, hp⟩
  exact ⟨p, hpI, hp⟩

lemma N4o2_mono : AntitoneOn N4o2 (Set.Icc (21/2 : R) (11 : R)) := by
  intro x hx y hy hxy
  have hcalc : N4o2 y - N4o2 x = (y - x) * (-43 * (x + y) + 375) := by
    unfold N4o2; ring_nf
  have hbound : -43 * (x + y) + 375 <= 0 := by nlinarith [hx.1, hx.2, hy.1, hy.2]
  have hneg : N4o2 y - N4o2 x <= 0 := by
    rw [hcalc]
    exact mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hxy) hbound
  exact sub_nonpos.mp hneg

lemma fp4o2_mono : MonotoneOn fp4o2 (Set.Icc (21/2 : R) (11 : R)) := by
  intro x hx y hy hxy
  have hcalc : fp4o2 y - fp4o2 x = (y - x) * (3 * (x + y) + -26) := by
    unfold fp4o2; ring_nf
  have hbound : 0 <= 3 * (x + y) + -26 := by nlinarith [hx.1, hx.2, hy.1, hy.2]
  have hsub : 0 <= fp4o2 y - fp4o2 x := by
    rw [hcalc]
    exact mul_nonneg (sub_nonneg.mpr hxy) hbound
  exact sub_nonneg.mp hsub

lemma N4o2_lo : N4o2 (21/2 : R) < 0 := by unfold N4o2; norm_num
lemma fp4o2_lo : 0 < fp4o2 (21/2 : R) := by unfold fp4o2; norm_num

theorem cert_f4o2 : ∃ p : R, p ∈ Set.Icc (21/2 : R) (11 : R) ∧ f4o2 p = 0 ∧ N4o2 p < 0 ∧ 0 < fp4o2 p := by
  rcases root_f4o2 with ⟨p, hpI, hp0⟩
  refine ⟨p, hpI, hp0, ?_, ?_⟩
  · have hN : N4o2 p ≤ N4o2 (21/2 : R) := N4o2_mono (by norm_num : (21/2 : R) ∈ Set.Icc (21/2 : R) (11 : R)) hpI (by simpa using hpI.1)
    have hz : N4o2 (21/2 : R) < 0 := N4o2_lo
    exact lt_of_le_of_lt hN hz
  · have hF : fp4o2 (21/2 : R) ≤ fp4o2 p := fp4o2_mono (by norm_num : (21/2 : R) ∈ Set.Icc (21/2 : R) (11 : R)) hpI (by simpa using hpI.1)
    have hz : 0 < fp4o2 (21/2 : R) := fp4o2_lo
    exact lt_of_lt_of_le hz hF

/-! 汇总：六个外部根证书（根存在 + N 与 fp 符号），beta>0 条件成立。
   内部六个根（0<r<1）证书在 q6_sign_cert.lean 的 Q6D 命名空间（six_branches，
   全局名 cert_a1..cert_d1），二者共同给出 q=6 全部 12 个实根的
   -N_j(r)/(169 f_j'(r)) > 0。 -/
theorem outer_six_prop :
    (∃ p : R, p ∈ Set.Icc (537/2 : R) (269 : R) ∧ f1o1 p = 0 ∧ N1o1 p < 0 ∧ 0 < fp1o1 p) ∧
    (∃ p : R, p ∈ Set.Icc (4 : R) (9/2 : R) ∧ f2o1 p = 0 ∧ 0 < N2o1 p ∧ fp2o1 p < 0) ∧
    (∃ p : R, p ∈ Set.Icc (123/2 : R) (62 : R) ∧ f2o2 p = 0 ∧ N2o2 p < 0 ∧ 0 < fp2o2 p) ∧
    (∃ p : R, p ∈ Set.Icc (25 : R) (51/2 : R) ∧ f3o1 p = 0 ∧ N3o1 p < 0 ∧ 0 < fp3o1 p) ∧
    (∃ p : R, p ∈ Set.Icc (2 : R) (5/2 : R) ∧ f4o1 p = 0 ∧ 0 < N4o1 p ∧ fp4o1 p < 0) ∧
    (∃ p : R, p ∈ Set.Icc (21/2 : R) (11 : R) ∧ f4o2 p = 0 ∧ N4o2 p < 0 ∧ 0 < fp4o2 p) := by
  constructor
  · exact cert_f1o1
  · constructor
    · exact cert_f2o1
    · constructor
      · exact cert_f2o2
      · constructor
        · exact cert_f3o1
        · constructor
          · exact cert_f4o1
          · exact cert_f4o2

end Q6AllRoot


