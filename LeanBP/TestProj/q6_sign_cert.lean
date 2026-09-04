import Mathlib
open scoped Topology
open Set

abbrev R := Real

noncomputable def pa1 : Polynomial R := Polynomial.X ^ 3 - 269 * Polynomial.X ^ 2 + 66 * Polynomial.X - 1
def fa1 (x : R) : R := x ^ 3 - 269 * x ^ 2 + 66 * x - 1
def fpa1 (x : R) : R := 3 * x ^ 2 - 538 * x + 66
def Na1 (x : R) : R := -17 * x ^ 2 + 3443 * x - 374

lemma poly_eval_a1 (x : R) : Polynomial.eval x pa1 = x ^ 3 - 269 * x ^ 2 + 66 * x - 1 := by
  unfold pa1
  simp [Polynomial.eval]

lemma cont_a1 (lo hi : R) : ContinuousOn fa1 (Set.Icc lo hi) := by
  rw [show fa1 = fun x : R => Polynomial.eval x pa1 by
    funext x
    simp [fa1, poly_eval_a1]]
  exact Polynomial.continuousOn pa1

lemma mono_Na1 : MonotoneOn Na1 (Set.Icc (0 : R) 1) := by
  intro x hx y hy hxy
  have hbound : 0 <= 3443 + -17 * (x + y) := by
    nlinarith [hx.1, hx.2, hy.1, hy.2]
  have hcalc : Na1 y - Na1 x = (y - x) * (3443 + -17 * (x + y)) := by
    unfold Na1; ring
  have hsub : 0 <= Na1 y - Na1 x := by
    rw [hcalc]
    exact mul_nonneg (sub_nonneg.mpr hxy) hbound
  exact sub_nonneg.mp hsub

lemma antitone_fpa1 : AntitoneOn fpa1 (Set.Icc (0 : R) 1) := by
  intro x hx y hy hxy
  have hbound : 3 * (x + y) + -538 <= 0 := by
    nlinarith [hx.1, hx.2, hy.1, hy.2]
  have hcalc : fpa1 y - fpa1 x = (y - x) * (3 * (x + y) + -538) := by
    unfold fpa1; ring
  have hneg : 0 <= - (fpa1 y - fpa1 x) := by
    rw [hcalc]
    nlinarith
  exact sub_nonneg.mp (by simpa [sub_eq_add_neg] using hneg)

lemma Na1_hi_neg : Na1 (1/50 : R) < 0 := by unfold Na1; norm_num
lemma fpa1_hi_pos : 0 < fpa1 (1/50 : R) := by unfold fpa1; norm_num
lemma fa1_lo_lt : fa1 (1/100 : R) < 0 := by unfold fa1; norm_num
lemma fa1_hi_pos : 0 < fa1 (1/50 : R) := by unfold fa1; norm_num

lemma root_a1 : exists p : R, p ∈ Set.Icc (1/100 : R) (1/50 : R) ∧ fa1 p = 0 := by
  have hcont : ContinuousOn fa1 (Set.Icc (1/100 : R) (1/50 : R)) := cont_a1 (1/100 : R) (1/50 : R)
  have hmem : (0 : R) ∈ Set.Icc (fa1 (1/100 : R)) (fa1 (1/50 : R)) := by
    exact ⟨le_of_lt fa1_lo_lt, le_of_lt fa1_hi_pos⟩
  have hpre : (0 : R) ∈ fa1 '' (Set.Icc (1/100 : R) (1/50 : R)) :=
    intermediate_value_Icc (by norm_num : (1/100 : R) ≤ (1/50 : R)) hcont hmem
  rcases hpre with ⟨p, hpI, hp⟩
  exact ⟨p, hpI, hp⟩

theorem cert_a1 : exists p : R, p ∈ Set.Icc (1/100 : R) (1/50 : R) ∧ fa1 p = 0 ∧ Na1 p < 0 ∧ 0 < fpa1 p := by
  rcases root_a1 with ⟨p, hpI, hp0⟩
  have h0 : (0 : R) ≤ (1/100 : R) := by norm_num
  have h1 : (1/50 : R) ≤ (1 : R) := by norm_num
  have hp01 : p ∈ Set.Icc (0 : R) 1 := by
    constructor <;> nlinarith [hpI.1, hpI.2, h0, h1]
  have hh : (1/50 : R) ∈ Set.Icc (0 : R) 1 := by norm_num
  refine ⟨p, hpI, hp0, ?_, ?_⟩
  · have hpN : Na1 p ≤ Na1 (1/50 : R) := mono_Na1 hp01 hh (by simpa using hpI.2)
    have : Na1 (1/50 : R) < 0 := Na1_hi_neg
    exact lt_of_le_of_lt hpN this
  · have hpp : fpa1 (1/50 : R) ≤ fpa1 p := antitone_fpa1 hp01 hh (by simpa using hpI.2)
    have : 0 < fpa1 (1/50 : R) := fpa1_hi_pos
    exact lt_of_lt_of_le this hpp

noncomputable def pb1 : Polynomial R := Polynomial.X ^ 3 - 66 * Polynomial.X ^ 2 + 269 * Polynomial.X - 1
def fb1 (x : R) : R := x ^ 3 - 66 * x ^ 2 + 269 * x - 1
def fpb1 (x : R) : R := 3 * x ^ 2 - 132 * x + 269
def Nb1 (x : R) : R := -17 * x ^ 2 + 748 * x - 1130

lemma poly_eval_b1 (x : R) : Polynomial.eval x pb1 = x ^ 3 - 66 * x ^ 2 + 269 * x - 1 := by
  unfold pb1
  simp [Polynomial.eval]

lemma cont_b1 (lo hi : R) : ContinuousOn fb1 (Set.Icc lo hi) := by
  rw [show fb1 = fun x : R => Polynomial.eval x pb1 by
    funext x
    simp [fb1, poly_eval_b1]]
  exact Polynomial.continuousOn pb1

lemma mono_Nb1 : MonotoneOn Nb1 (Set.Icc (0 : R) 1) := by
  intro x hx y hy hxy
  have hbound : 0 <= 748 + -17 * (x + y) := by
    nlinarith [hx.1, hx.2, hy.1, hy.2]
  have hcalc : Nb1 y - Nb1 x = (y - x) * (748 + -17 * (x + y)) := by
    unfold Nb1; ring
  have hsub : 0 <= Nb1 y - Nb1 x := by
    rw [hcalc]
    exact mul_nonneg (sub_nonneg.mpr hxy) hbound
  exact sub_nonneg.mp hsub

lemma antitone_fpb1 : AntitoneOn fpb1 (Set.Icc (0 : R) 1) := by
  intro x hx y hy hxy
  have hbound : 3 * (x + y) + -132 <= 0 := by
    nlinarith [hx.1, hx.2, hy.1, hy.2]
  have hcalc : fpb1 y - fpb1 x = (y - x) * (3 * (x + y) + -132) := by
    unfold fpb1; ring
  have hneg : 0 <= - (fpb1 y - fpb1 x) := by
    rw [hcalc]
    nlinarith
  exact sub_nonneg.mp (by simpa [sub_eq_add_neg] using hneg)

lemma Nb1_hi_neg : Nb1 (1/250 : R) < 0 := by unfold Nb1; norm_num
lemma fpb1_hi_pos : 0 < fpb1 (1/250 : R) := by unfold fpb1; norm_num
lemma fb1_lo_lt : fb1 (1/500 : R) < 0 := by unfold fb1; norm_num
lemma fb1_hi_pos : 0 < fb1 (1/250 : R) := by unfold fb1; norm_num

lemma root_b1 : exists p : R, p ∈ Set.Icc (1/500 : R) (1/250 : R) ∧ fb1 p = 0 := by
  have hcont : ContinuousOn fb1 (Set.Icc (1/500 : R) (1/250 : R)) := cont_b1 (1/500 : R) (1/250 : R)
  have hmem : (0 : R) ∈ Set.Icc (fb1 (1/500 : R)) (fb1 (1/250 : R)) := by
    exact ⟨le_of_lt fb1_lo_lt, le_of_lt fb1_hi_pos⟩
  have hpre : (0 : R) ∈ Set.image fb1 (Set.Icc (1/500 : R) (1/250 : R)) :=
    intermediate_value_Icc (by norm_num : (1/500 : R) ≤ (1/250 : R)) hcont hmem
  rcases hpre with ⟨p, hpI, hp⟩
  exact ⟨p, hpI, hp⟩

theorem cert_b1 : exists p : R, p ∈ Set.Icc (1/500 : R) (1/250 : R) ∧ fb1 p = 0 ∧ Nb1 p < 0 ∧ 0 < fpb1 p := by
  rcases root_b1 with ⟨p, hpI, hp0⟩
  have h0 : (0 : R) ≤ (1/500 : R) := by norm_num
  have h1 : (1/250 : R) ≤ (1 : R) := by norm_num
  have hp01 : p ∈ Set.Icc (0 : R) 1 := by
    constructor <;> nlinarith [hpI.1, hpI.2, h0, h1]
  have hh : (1/250 : R) ∈ Set.Icc (0 : R) 1 := by norm_num
  refine ⟨p, hpI, hp0, ?_, ?_⟩
  · have hpN : Nb1 p ≤ Nb1 (1/250 : R) := mono_Nb1 hp01 hh (by simpa using hpI.2)
    have : Nb1 (1/250 : R) < 0 := Nb1_hi_neg
    exact lt_of_le_of_lt hpN this
  · have hpp : fpb1 (1/250 : R) ≤ fpb1 p := antitone_fpb1 hp01 hh (by simpa using hpI.2)
    have : 0 < fpb1 (1/250 : R) := fpb1_hi_pos
    exact lt_of_lt_of_le this hpp

noncomputable def pc1 : Polynomial R := Polynomial.X ^ 3 - 26 * Polynomial.X ^ 2 + 13 * Polynomial.X - 1
def fc1 (x : R) : R := x ^ 3 - 26 * x ^ 2 + 13 * x - 1
def fpc1 (x : R) : R := 3 * x ^ 2 - 52 * x + 13
def Nc1 (x : R) : R := -43 * x ^ 2 + 827 * x - 184

lemma poly_eval_c1 (x : R) : Polynomial.eval x pc1 = x ^ 3 - 26 * x ^ 2 + 13 * x - 1 := by
  unfold pc1
  simp [Polynomial.eval]

lemma cont_c1 (lo hi : R) : ContinuousOn fc1 (Set.Icc lo hi) := by
  rw [show fc1 = fun x : R => Polynomial.eval x pc1 by
    funext x
    simp [fc1, poly_eval_c1]]
  exact Polynomial.continuousOn pc1

lemma mono_Nc1 : MonotoneOn Nc1 (Set.Icc (0 : R) 1) := by
  intro x hx y hy hxy
  have hbound : 0 <= 827 + -43 * (x + y) := by
    nlinarith [hx.1, hx.2, hy.1, hy.2]
  have hcalc : Nc1 y - Nc1 x = (y - x) * (827 + -43 * (x + y)) := by
    unfold Nc1; ring
  have hsub : 0 <= Nc1 y - Nc1 x := by
    rw [hcalc]
    exact mul_nonneg (sub_nonneg.mpr hxy) hbound
  exact sub_nonneg.mp hsub

lemma antitone_fpc1 : AntitoneOn fpc1 (Set.Icc (0 : R) 1) := by
  intro x hx y hy hxy
  have hbound : 3 * (x + y) + -52 <= 0 := by
    nlinarith [hx.1, hx.2, hy.1, hy.2]
  have hcalc : fpc1 y - fpc1 x = (y - x) * (3 * (x + y) + -52) := by
    unfold fpc1; ring
  have hneg : 0 <= - (fpc1 y - fpc1 x) := by
    rw [hcalc]
    nlinarith
  exact sub_nonneg.mp (by simpa [sub_eq_add_neg] using hneg)

lemma Nc1_hi_neg : Nc1 (1/10 : R) < 0 := by unfold Nc1; norm_num
lemma fpc1_hi_pos : 0 < fpc1 (1/10 : R) := by unfold fpc1; norm_num
lemma fc1_lo_lt : fc1 (2/25 : R) < 0 := by unfold fc1; norm_num
lemma fc1_hi_pos : 0 < fc1 (1/10 : R) := by unfold fc1; norm_num

lemma root_c1 : exists p : R, p ∈ Set.Icc (2/25 : R) (1/10 : R) ∧ fc1 p = 0 := by
  have hcont : ContinuousOn fc1 (Set.Icc (2/25 : R) (1/10 : R)) := cont_c1 (2/25 : R) (1/10 : R)
  have hmem : (0 : R) ∈ Set.Icc (fc1 (2/25 : R)) (fc1 (1/10 : R)) := by
    exact ⟨le_of_lt fc1_lo_lt, le_of_lt fc1_hi_pos⟩
  have hpre : (0 : R) ∈ Set.image fc1 (Set.Icc (2/25 : R) (1/10 : R)) :=
    intermediate_value_Icc (by norm_num : (2/25 : R) ≤ (1/10 : R)) hcont hmem
  rcases hpre with ⟨p, hpI, hp⟩
  exact ⟨p, hpI, hp⟩

theorem cert_c1 : exists p : R, p ∈ Set.Icc (2/25 : R) (1/10 : R) ∧ fc1 p = 0 ∧ Nc1 p < 0 ∧ 0 < fpc1 p := by
  rcases root_c1 with ⟨p, hpI, hp0⟩
  have h0 : (0 : R) ≤ (2/25 : R) := by norm_num
  have h1 : (1/10 : R) ≤ (1 : R) := by norm_num
  have hp01 : p ∈ Set.Icc (0 : R) 1 := by
    constructor <;> nlinarith [hpI.1, hpI.2, h0, h1]
  have hh : (1/10 : R) ∈ Set.Icc (0 : R) 1 := by norm_num
  refine ⟨p, hpI, hp0, ?_, ?_⟩
  · have hpN : Nc1 p ≤ Nc1 (1/10 : R) := mono_Nc1 hp01 hh (by simpa using hpI.2)
    have : Nc1 (1/10 : R) < 0 := Nc1_hi_neg
    exact lt_of_le_of_lt hpN this
  · have hpp : fpc1 (1/10 : R) ≤ fpc1 p := antitone_fpc1 hp01 hh (by simpa using hpI.2)
    have : 0 < fpc1 (1/10 : R) := fpc1_hi_pos
    exact lt_of_lt_of_le this hpp

noncomputable def pd1 : Polynomial R := Polynomial.X ^ 3 - 13 * Polynomial.X ^ 2 + 26 * Polynomial.X - 1
def fd1 (x : R) : R := x ^ 3 - 13 * x ^ 2 + 26 * x - 1
def fpd1 (x : R) : R := 3 * x ^ 2 - 26 * x + 26
def Nd1 (x : R) : R := -43 * x ^ 2 + 375 * x - 291

lemma poly_eval_d1 (x : R) : Polynomial.eval x pd1 = x ^ 3 - 13 * x ^ 2 + 26 * x - 1 := by
  unfold pd1
  simp [Polynomial.eval]

lemma cont_d1 (lo hi : R) : ContinuousOn fd1 (Set.Icc lo hi) := by
  rw [show fd1 = fun x : R => Polynomial.eval x pd1 by
    funext x
    simp [fd1, poly_eval_d1]]
  exact Polynomial.continuousOn pd1

lemma mono_Nd1 : MonotoneOn Nd1 (Set.Icc (0 : R) 1) := by
  intro x hx y hy hxy
  have hbound : 0 <= 375 + -43 * (x + y) := by
    nlinarith [hx.1, hx.2, hy.1, hy.2]
  have hcalc : Nd1 y - Nd1 x = (y - x) * (375 + -43 * (x + y)) := by
    unfold Nd1; ring
  have hsub : 0 <= Nd1 y - Nd1 x := by
    rw [hcalc]
    exact mul_nonneg (sub_nonneg.mpr hxy) hbound
  exact sub_nonneg.mp hsub

lemma antitone_fpd1 : AntitoneOn fpd1 (Set.Icc (0 : R) 1) := by
  intro x hx y hy hxy
  have hbound : 3 * (x + y) + -26 <= 0 := by
    nlinarith [hx.1, hx.2, hy.1, hy.2]
  have hcalc : fpd1 y - fpd1 x = (y - x) * (3 * (x + y) + -26) := by
    unfold fpd1; ring
  have hneg : 0 <= - (fpd1 y - fpd1 x) := by
    rw [hcalc]
    nlinarith
  exact sub_nonneg.mp (by simpa [sub_eq_add_neg] using hneg)

lemma Nd1_hi_neg : Nd1 (1/25 : R) < 0 := by unfold Nd1; norm_num
lemma fpd1_hi_pos : 0 < fpd1 (1/25 : R) := by unfold fpd1; norm_num
lemma fd1_lo_lt : fd1 (1/50 : R) < 0 := by unfold fd1; norm_num
lemma fd1_hi_pos : 0 < fd1 (1/25 : R) := by unfold fd1; norm_num

lemma root_d1 : exists p : R, p ∈ Set.Icc (1/50 : R) (1/25 : R) ∧ fd1 p = 0 := by
  have hcont : ContinuousOn fd1 (Set.Icc (1/50 : R) (1/25 : R)) := cont_d1 (1/50 : R) (1/25 : R)
  have hmem : (0 : R) ∈ Set.Icc (fd1 (1/50 : R)) (fd1 (1/25 : R)) := by
    exact ⟨le_of_lt fd1_lo_lt, le_of_lt fd1_hi_pos⟩
  have hpre : (0 : R) ∈ Set.image fd1 (Set.Icc (1/50 : R) (1/25 : R)) :=
    intermediate_value_Icc (by norm_num : (1/50 : R) ≤ (1/25 : R)) hcont hmem
  rcases hpre with ⟨p, hpI, hp⟩
  exact ⟨p, hpI, hp⟩

theorem cert_d1 : exists p : R, p ∈ Set.Icc (1/50 : R) (1/25 : R) ∧ fd1 p = 0 ∧ Nd1 p < 0 ∧ 0 < fpd1 p := by
  rcases root_d1 with ⟨p, hpI, hp0⟩
  have h0 : (0 : R) ≤ (1/50 : R) := by norm_num
  have h1 : (1/25 : R) ≤ (1 : R) := by norm_num
  have hp01 : p ∈ Set.Icc (0 : R) 1 := by
    constructor <;> nlinarith [hpI.1, hpI.2, h0, h1]
  have hh : (1/25 : R) ∈ Set.Icc (0 : R) 1 := by norm_num
  refine ⟨p, hpI, hp0, ?_, ?_⟩
  · have hpN : Nd1 p ≤ Nd1 (1/25 : R) := mono_Nd1 hp01 hh (by simpa using hpI.2)
    have : Nd1 (1/25 : R) < 0 := Nd1_hi_neg
    exact lt_of_le_of_lt hpN this
  · have hpp : fpd1 (1/25 : R) ≤ fpd1 p := antitone_fpd1 hp01 hh (by simpa using hpI.2)
    have : 0 < fpd1 (1/25 : R) := fpd1_hi_pos
    exact lt_of_lt_of_le this hpp

noncomputable def pa2 : Polynomial R := Polynomial.X ^ 3 - 269 * Polynomial.X ^ 2 + 66 * Polynomial.X - 1
def fa2 (x : R) : R := x ^ 3 - 269 * x ^ 2 + 66 * x - 1
def fpa2 (x : R) : R := 3 * x ^ 2 - 538 * x + 66
def Na2 (x : R) : R := -17 * x ^ 2 + 3443 * x - 374

lemma poly_eval_a2 (x : R) : Polynomial.eval x pa2 = x ^ 3 - 269 * x ^ 2 + 66 * x - 1 := by
  unfold pa2
  simp [Polynomial.eval]

lemma cont_a2 (lo hi : R) : ContinuousOn fa2 (Set.Icc lo hi) := by
  rw [show fa2 = fun x : R => Polynomial.eval x pa2 by
    funext x
    simp [fa2, poly_eval_a2]]
  exact Polynomial.continuousOn pa2

lemma mono_Na2 : MonotoneOn Na2 (Set.Icc (0 : R) 1) := by
  intro x hx y hy hxy
  have hbound : 0 <= 3443 + -17 * (x + y) := by
    nlinarith [hx.1, hx.2, hy.1, hy.2]
  have hcalc : Na2 y - Na2 x = (y - x) * (3443 + -17 * (x + y)) := by
    unfold Na2; ring
  have hsub : 0 <= Na2 y - Na2 x := by
    rw [hcalc]
    exact mul_nonneg (sub_nonneg.mpr hxy) hbound
  exact sub_nonneg.mp hsub

lemma antitone_fpa2 : AntitoneOn fpa2 (Set.Icc (0 : R) 1) := by
  intro x hx y hy hxy
  have hbound : 3 * (x + y) + -538 <= 0 := by
    nlinarith [hx.1, hx.2, hy.1, hy.2]
  have hcalc : fpa2 y - fpa2 x = (y - x) * (3 * (x + y) + -538) := by
    unfold fpa2; ring
  have hneg : 0 <= - (fpa2 y - fpa2 x) := by
    rw [hcalc]
    nlinarith
  exact sub_nonneg.mp (by simpa [sub_eq_add_neg] using hneg)

lemma Na2_lo_pos : 0 < Na2 (1/5 : R) := by unfold Na2; norm_num
lemma fpa2_lo_neg : fpa2 (1/5 : R) < 0 := by unfold fpa2; norm_num
lemma fa2_lo_pos : 0 < fa2 (1/5 : R) := by unfold fa2; norm_num
lemma fa2_hi_lt : fa2 (6/25 : R) < 0 := by unfold fa2; norm_num

lemma root_a2 : exists p : R, p ∈ Set.Icc (1/5 : R) (6/25 : R) ∧ fa2 p = 0 := by
  have hcont : ContinuousOn (fun x : R => -fa2 x) (Set.Icc (1/5 : R) (6/25 : R)) := by
    exact (cont_a2 (1/5 : R) (6/25 : R)).neg
  have hmem : (0 : R) ∈ Set.Icc (-fa2 (1/5 : R)) (-fa2 (6/25 : R)) := by
    exact ⟨by linarith [fa2_lo_pos], by linarith [fa2_hi_lt]⟩
  have hpre : (0 : R) ∈ Set.image (fun x : R => -fa2 x) (Set.Icc (1/5 : R) (6/25 : R)) :=
    intermediate_value_Icc (by norm_num : (1/5 : R) ≤ (6/25 : R)) hcont hmem
  rcases hpre with ⟨p, hpI, hp⟩
  exact ⟨p, hpI, by linarith⟩

theorem cert_a2 : exists p : R, p ∈ Set.Icc (1/5 : R) (6/25 : R) ∧ fa2 p = 0 ∧ 0 < Na2 p ∧ fpa2 p < 0 := by
  rcases root_a2 with ⟨p, hpI, hp0⟩
  have h0 : (0 : R) ≤ (1/5 : R) := by norm_num
  have h1 : (6/25 : R) ≤ (1 : R) := by norm_num
  have hp01 : p ∈ Set.Icc (0 : R) 1 := by
    constructor <;> nlinarith [hpI.1, hpI.2, h0, h1]
  have hl : (1/5 : R) ∈ Set.Icc (0 : R) 1 := by norm_num
  have hh : (6/25 : R) ∈ Set.Icc (0 : R) 1 := by norm_num
  refine ⟨p, hpI, hp0, ?_, ?_⟩
  · have hpN : Na2 (1/5 : R) ≤ Na2 p := mono_Na2 hl hp01 (by simpa using hpI.1)
    have : 0 < Na2 (1/5 : R) := Na2_lo_pos
    exact lt_of_lt_of_le this hpN
  · have hpp : fpa2 p ≤ fpa2 (1/5 : R) := antitone_fpa2 hl hp01 (by simpa using hpI.1)
    have : fpa2 (1/5 : R) < 0 := fpa2_lo_neg
    exact lt_of_le_of_lt hpp this

noncomputable def pc2 : Polynomial R := Polynomial.X ^ 3 - 26 * Polynomial.X ^ 2 + 13 * Polynomial.X - 1
def fc2 (x : R) : R := x ^ 3 - 26 * x ^ 2 + 13 * x - 1
def fpc2 (x : R) : R := 3 * x ^ 2 - 52 * x + 13
def Nc2 (x : R) : R := -43 * x ^ 2 + 827 * x - 184

lemma poly_eval_c2 (x : R) : Polynomial.eval x pc2 = x ^ 3 - 26 * x ^ 2 + 13 * x - 1 := by
  unfold pc2
  simp [Polynomial.eval]

lemma cont_c2 (lo hi : R) : ContinuousOn fc2 (Set.Icc lo hi) := by
  rw [show fc2 = fun x : R => Polynomial.eval x pc2 by
    funext x
    simp [fc2, poly_eval_c2]]
  exact Polynomial.continuousOn pc2

lemma mono_Nc2 : MonotoneOn Nc2 (Set.Icc (0 : R) 1) := by
  intro x hx y hy hxy
  have hbound : 0 <= 827 + -43 * (x + y) := by
    nlinarith [hx.1, hx.2, hy.1, hy.2]
  have hcalc : Nc2 y - Nc2 x = (y - x) * (827 + -43 * (x + y)) := by
    unfold Nc2; ring
  have hsub : 0 <= Nc2 y - Nc2 x := by
    rw [hcalc]
    exact mul_nonneg (sub_nonneg.mpr hxy) hbound
  exact sub_nonneg.mp hsub

lemma antitone_fpc2 : AntitoneOn fpc2 (Set.Icc (0 : R) 1) := by
  intro x hx y hy hxy
  have hbound : 3 * (x + y) + -52 <= 0 := by
    nlinarith [hx.1, hx.2, hy.1, hy.2]
  have hcalc : fpc2 y - fpc2 x = (y - x) * (3 * (x + y) + -52) := by
    unfold fpc2; ring
  have hneg : 0 <= - (fpc2 y - fpc2 x) := by
    rw [hcalc]
    nlinarith
  exact sub_nonneg.mp (by simpa [sub_eq_add_neg] using hneg)

lemma Nc2_lo_pos : 0 < Nc2 (2/5 : R) := by unfold Nc2; norm_num
lemma fpc2_lo_neg : fpc2 (2/5 : R) < 0 := by unfold fpc2; norm_num
lemma fc2_lo_pos : 0 < fc2 (2/5 : R) := by unfold fc2; norm_num
lemma fc2_hi_lt : fc2 (11/25 : R) < 0 := by unfold fc2; norm_num

lemma root_c2 : exists p : R, p ∈ Set.Icc (2/5 : R) (11/25 : R) ∧ fc2 p = 0 := by
  have hcont : ContinuousOn (fun x : R => -fc2 x) (Set.Icc (2/5 : R) (11/25 : R)) := by
    exact (cont_c2 (2/5 : R) (11/25 : R)).neg
  have hmem : (0 : R) ∈ Set.Icc (-fc2 (2/5 : R)) (-fc2 (11/25 : R)) := by
    exact ⟨by linarith [fc2_lo_pos], by linarith [fc2_hi_lt]⟩
  have hpre : (0 : R) ∈ Set.image (fun x : R => -fc2 x) (Set.Icc (2/5 : R) (11/25 : R)) :=
    intermediate_value_Icc (by norm_num : (2/5 : R) ≤ (11/25 : R)) hcont hmem
  rcases hpre with ⟨p, hpI, hp⟩
  exact ⟨p, hpI, by linarith⟩

theorem cert_c2 : exists p : R, p ∈ Set.Icc (2/5 : R) (11/25 : R) ∧ fc2 p = 0 ∧ 0 < Nc2 p ∧ fpc2 p < 0 := by
  rcases root_c2 with ⟨p, hpI, hp0⟩
  have h0 : (0 : R) ≤ (2/5 : R) := by norm_num
  have h1 : (11/25 : R) ≤ (1 : R) := by norm_num
  have hp01 : p ∈ Set.Icc (0 : R) 1 := by
    constructor <;> nlinarith [hpI.1, hpI.2, h0, h1]
  have hl : (2/5 : R) ∈ Set.Icc (0 : R) 1 := by norm_num
  have hh : (11/25 : R) ∈ Set.Icc (0 : R) 1 := by norm_num
  refine ⟨p, hpI, hp0, ?_, ?_⟩
  · have hpN : Nc2 (2/5 : R) ≤ Nc2 p := mono_Nc2 hl hp01 (by simpa using hpI.1)
    have : 0 < Nc2 (2/5 : R) := Nc2_lo_pos
    exact lt_of_lt_of_le this hpN
  · have hpp : fpc2 p ≤ fpc2 (2/5 : R) := antitone_fpc2 hl hp01 (by simpa using hpI.1)
    have : fpc2 (2/5 : R) < 0 := fpc2_lo_neg
    exact lt_of_le_of_lt hpp this


/- 汇总：六个分支的存在性与符号，等价于 N(p)*f'(p)<0 的完整证书 -/
theorem six_branches :
    (∃ p : R, p ∈ Set.Icc (1/100 : R) (1/50) ∧ fa1 p = 0 ∧ Na1 p < 0 ∧ 0 < fpa1 p) ∧
    (∃ p : R, p ∈ Set.Icc (1/5 : R) (6/25) ∧ fa2 p = 0 ∧ 0 < Na2 p ∧ fpa2 p < 0) ∧
    (∃ p : R, p ∈ Set.Icc (1/500 : R) (1/250) ∧ fb1 p = 0 ∧ Nb1 p < 0 ∧ 0 < fpb1 p) ∧
    (∃ p : R, p ∈ Set.Icc (2/25 : R) (1/10) ∧ fc1 p = 0 ∧ Nc1 p < 0 ∧ 0 < fpc1 p) ∧
    (∃ p : R, p ∈ Set.Icc (2/5 : R) (11/25) ∧ fc2 p = 0 ∧ 0 < Nc2 p ∧ fpc2 p < 0) ∧
    (∃ p : R, p ∈ Set.Icc (1/50 : R) (1/25) ∧ fd1 p = 0 ∧ Nd1 p < 0 ∧ 0 < fpd1 p) := by
  exact ⟨cert_a1, ⟨cert_a2, ⟨cert_b1, ⟨cert_c1, ⟨cert_c2, cert_d1⟩⟩⟩⟩⟩

/- 核心引申：alpha = -N(p)*lambda/(169*f'(p)) > 0 的代数内容。
   对任一分支，f(p)=0 且 N(p)*f'(p)<0 时，-N(p)*f'(p) > 0（即 N(p)*f'(p)<0 取反）。
   乘以正数 lambda>0 与 169>0 不改变正性；six_branches 给出逐支 N(p)*f'(p)<0 的形式化证书，
   故每个增长分支 alpha_lambda > 0。 -/
theorem alpha_pos_core (Nc fpv : R) (hN : Nc < 0) (hf : 0 < fpv) : 0 < - (Nc * fpv) := by
  nlinarith [hN, hf]

