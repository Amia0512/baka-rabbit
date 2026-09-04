import Mathlib
import TestProj.q6_sign_cert
import TestProj.q6_allroot_outer

open scoped BigOperators
open Set

set_option maxHeartbeats 0

namespace Q6AllRootParam

abbrev R := ℝ

noncomputable def p1 : R := Classical.choose cert_a1
noncomputable def p2 : R := Classical.choose cert_a2
noncomputable def p3 : R := Classical.choose cert_b1
noncomputable def p4 : R := Classical.choose cert_c1
noncomputable def p5 : R := Classical.choose cert_c2
noncomputable def p6 : R := Classical.choose cert_d1
noncomputable def p7 : R := Classical.choose Q6AllRoot.cert_f1o1
noncomputable def p8 : R := Classical.choose Q6AllRoot.cert_f2o1
noncomputable def p9 : R := Classical.choose Q6AllRoot.cert_f2o2
noncomputable def p10 : R := Classical.choose Q6AllRoot.cert_f3o1
noncomputable def p11 : R := Classical.choose Q6AllRoot.cert_f4o1
noncomputable def p12 : R := Classical.choose Q6AllRoot.cert_f4o2

noncomputable def roots : Fin 12 → R
  | ⟨0, _⟩ => p1
  | ⟨1, _⟩ => p2
  | ⟨2, _⟩ => p3
  | ⟨3, _⟩ => p4
  | ⟨4, _⟩ => p5
  | ⟨5, _⟩ => p6
  | ⟨6, _⟩ => p7
  | ⟨7, _⟩ => p8
  | ⟨8, _⟩ => p9
  | ⟨9, _⟩ => p10
  | ⟨10, _⟩ => p11
  | ⟨11, _⟩ => p12

lemma roots_pos (i : Fin 12) : 0 < roots i := by
  fin_cases i
  · exact lt_of_lt_of_le (by norm_num) (Classical.choose_spec cert_a1).1.1
  · exact lt_of_lt_of_le (by norm_num) (Classical.choose_spec cert_a2).1.1
  · exact lt_of_lt_of_le (by norm_num) (Classical.choose_spec cert_b1).1.1
  · exact lt_of_lt_of_le (by norm_num) (Classical.choose_spec cert_c1).1.1
  · exact lt_of_lt_of_le (by norm_num) (Classical.choose_spec cert_c2).1.1
  · exact lt_of_lt_of_le (by norm_num) (Classical.choose_spec cert_d1).1.1
  · exact lt_of_lt_of_le (by norm_num) (Classical.choose_spec Q6AllRoot.cert_f1o1).1.1
  · exact lt_of_lt_of_le (by norm_num) (Classical.choose_spec Q6AllRoot.cert_f2o1).1.1
  · exact lt_of_lt_of_le (by norm_num) (Classical.choose_spec Q6AllRoot.cert_f2o2).1.1
  · exact lt_of_lt_of_le (by norm_num) (Classical.choose_spec Q6AllRoot.cert_f3o1).1.1
  · exact lt_of_lt_of_le (by norm_num) (Classical.choose_spec Q6AllRoot.cert_f4o1).1.1
  · exact lt_of_lt_of_le (by norm_num) (Classical.choose_spec Q6AllRoot.cert_f4o2).1.1

noncomputable def beta : Fin 12 → R
  | ⟨0, _⟩ => -Na1 p1 / (169 * fpa1 p1)
  | ⟨1, _⟩ => -Na2 p2 / (169 * fpa2 p2)
  | ⟨2, _⟩ => -Nb1 p3 / (169 * fpb1 p3)
  | ⟨3, _⟩ => -Nc1 p4 / (169 * fpc1 p4)
  | ⟨4, _⟩ => -Nc2 p5 / (169 * fpc2 p5)
  | ⟨5, _⟩ => -Nd1 p6 / (169 * fpd1 p6)
  | ⟨6, _⟩ => -Q6AllRoot.N1o1 p7 / (169 * Q6AllRoot.fp1o1 p7)
  | ⟨7, _⟩ => -Q6AllRoot.N2o1 p8 / (169 * Q6AllRoot.fp2o1 p8)
  | ⟨8, _⟩ => -Q6AllRoot.N2o2 p9 / (169 * Q6AllRoot.fp2o2 p9)
  | ⟨9, _⟩ => -Q6AllRoot.N3o1 p10 / (169 * Q6AllRoot.fp3o1 p10)
  | ⟨10, _⟩ => -Q6AllRoot.N4o1 p11 / (169 * Q6AllRoot.fp4o1 p11)
  | ⟨11, _⟩ => -Q6AllRoot.N4o2 p12 / (169 * Q6AllRoot.fp4o2 p12)

lemma beta_pos (i : Fin 12) : 0 < beta i := by
  fin_cases i
  · unfold beta p1
    have h := Classical.choose_spec cert_a1
    apply (div_pos_iff).2
    left
    constructor
    · nlinarith [h.2.2.1]
    · exact mul_pos (by norm_num) h.2.2.2
  · unfold beta p2
    have h := Classical.choose_spec cert_a2
    apply (div_pos_iff).2
    right
    constructor
    · nlinarith [h.2.2.1]
    · exact mul_neg_of_pos_of_neg (by norm_num) h.2.2.2
  · unfold beta p3
    have h := Classical.choose_spec cert_b1
    apply (div_pos_iff).2
    left
    constructor
    · nlinarith [h.2.2.1]
    · exact mul_pos (by norm_num) h.2.2.2
  · unfold beta p4
    have h := Classical.choose_spec cert_c1
    apply (div_pos_iff).2
    left
    constructor
    · nlinarith [h.2.2.1]
    · exact mul_pos (by norm_num) h.2.2.2
  · unfold beta p5
    have h := Classical.choose_spec cert_c2
    apply (div_pos_iff).2
    right
    constructor
    · nlinarith [h.2.2.1]
    · exact mul_neg_of_pos_of_neg (by norm_num) h.2.2.2
  · unfold beta p6
    have h := Classical.choose_spec cert_d1
    apply (div_pos_iff).2
    left
    constructor
    · nlinarith [h.2.2.1]
    · exact mul_pos (by norm_num) h.2.2.2
  · unfold beta p7
    have h := Classical.choose_spec Q6AllRoot.cert_f1o1
    apply (div_pos_iff).2
    left
    constructor
    · nlinarith [h.2.2.1]
    · exact mul_pos (by norm_num) h.2.2.2
  · unfold beta p8
    have h := Classical.choose_spec Q6AllRoot.cert_f2o1
    apply (div_pos_iff).2
    right
    constructor
    · nlinarith [h.2.2.1]
    · exact mul_neg_of_pos_of_neg (by norm_num) h.2.2.2
  · unfold beta p9
    have h := Classical.choose_spec Q6AllRoot.cert_f2o2
    apply (div_pos_iff).2
    left
    constructor
    · nlinarith [h.2.2.1]
    · exact mul_pos (by norm_num) h.2.2.2
  · unfold beta p10
    have h := Classical.choose_spec Q6AllRoot.cert_f3o1
    apply (div_pos_iff).2
    left
    constructor
    · nlinarith [h.2.2.1]
    · exact mul_pos (by norm_num) h.2.2.2
  · unfold beta p11
    have h := Classical.choose_spec Q6AllRoot.cert_f4o1
    apply (div_pos_iff).2
    right
    constructor
    · nlinarith [h.2.2.1]
    · exact mul_neg_of_pos_of_neg (by norm_num) h.2.2.2
  · unfold beta p12
    have h := Classical.choose_spec Q6AllRoot.cert_f4o2
    apply (div_pos_iff).2
    left
    constructor
    · nlinarith [h.2.2.1]
    · exact mul_pos (by norm_num) h.2.2.2

#print axioms Q6AllRootParam.roots_pos
#print axioms Q6AllRootParam.beta_pos

end Q6AllRootParam
