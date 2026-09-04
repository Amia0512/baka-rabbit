import Mathlib

set_option maxHeartbeats 0
set_option linter.unusedVariables false

/-!
# q=4, s=1: complete sign law for the four-point bracket (self-contained assembly)

Target (review item 2):  assemble the already-closed pieces into

    sign(A_4(a,m;1)) = sign(A_2(a,m;1))   for all 0 <= a < m

where A_q(a,m) = T_q(a) T_q(m+1) - T_q(a+1) T_q(m).

Pieces (all self-contained in this file):
  * e4/o4   : even/odd sub-series T_4(2n), T_4(2n+1)
  * Window lemmas (parameterized, mirror of EvenOddWin_sign.lean and
    EvenOddWin_sign_ext.lean):
      window_ee : e_k o_{k+1} > o_k e_{k+1}  =>  A(2i,2j) > 0
      window_oo : o_k e_{k+2} < e_{k+1} o_{k+1}  =>  A(2i+1,2j+1) < 0
  * D_pos    : quadrangle positivity  D_n = e_n e_{n+1} - o_n^2 > 0
               (spectral-cone proof, no extra axioms; same route as
               D4_quadrangle.lean)
  * cross_parity_eo/oe : non-adjacent cross-parity signs
  * sign_law_cases     : full four-class sign law for q=4, s=1

The two q=4 window inequalities are now UNCONDITIONALLY proved in
q4_window_pos.lean (Q4Win.wm_positive_window / wp_positive_window,
zero sorry): both follow from the order-5 palindromic recursion and a
6-fold-growth induction.  Hence instantiating sign_law_cases with those
theorems closes the full q=4, s=1 sign law with no remaining input.

CHECKPOINT 2026-08-26: zero sorry (this file); unconditional closure via Q4Win.
-/

namespace Q4S1

/-- Even sub-series T_4(2n) by the palindromic order-4 recursion. -/
def e4 : Nat -> Int
  | 0 => 1
  | 1 => 5
  | 2 => 36
  | 3 => 281
  | n + 4 => 11 * e4 (n + 3) - 25 * e4 (n + 2) + 11 * e4 (n + 1) - e4 n

/-- Odd sub-series T_4(2n+1) by the same recursion. -/
def o4 : Nat -> Int
  | 0 => 1
  | 1 => 11
  | 2 => 95
  | 3 => 781
  | n + 4 => 11 * o4 (n + 3) - 25 * o4 (n + 2) + 11 * o4 (n + 1) - o4 n

/-- Quadrangle sequence  D_n = e_n * e_{n+1} - o_n^2. -/
def D (n : Nat) : Int := e4 n * e4 (n + 1) - o4 n * o4 n

theorem e4_s4 (n : Nat) :
    e4 (n + 4) = 11 * e4 (n + 3) - 25 * e4 (n + 2) + 11 * e4 (n + 1) - e4 n := by rfl

theorem o4_s4 (n : Nat) :
    o4 (n + 4) = 11 * o4 (n + 3) - 25 * o4 (n + 2) + 11 * o4 (n + 1) - o4 n := by rfl

/-- Positivity of the even sub-series via super-exponential growth. -/
theorem e4_pos (n : Nat) : 0 < e4 n := by
  have P : forall n, (0 < e4 n) ∧ (4 * e4 n < e4 (n + 1)) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        match n with
        | 0 =>
            constructor
            · norm_num [e4]
            · norm_num [e4]
        | 1 =>
            constructor
            · norm_num [e4]
            · norm_num [e4]
        | 2 =>
            constructor
            · norm_num [e4]
            · norm_num [e4]
        | 3 =>
            constructor
            · norm_num [e4]
            · norm_num [e4]
        | m + 4 =>
            have h1 : 0 < e4 (m + 1) := (ih (m + 1) (by omega)).1
            have h2 : 0 < e4 (m + 2) := (ih (m + 2) (by omega)).1
            have h3 : 0 < e4 (m + 3) := (ih (m + 3) (by omega)).1
            have hg1 : 4 * e4 (m + 1) < e4 (m + 2) := (ih (m + 1) (by omega)).2
            have hg2 : 4 * e4 (m + 2) < e4 (m + 3) := (ih (m + 2) (by omega)).2
            have hg3 : 4 * e4 (m + 3) < e4 (m + 4) := (ih (m + 3) (by omega)).2
            have hg0 : 0 < e4 m := (ih m (by omega)).1
            have hgm : e4 m < e4 (m + 1) := by
              have h4 := (ih m (by omega)).2
              nlinarith
            have hpos : 0 < e4 (m + 4) := by
              rw [e4_s4]
              have hP1 : 11 * e4 (m + 3) - 25 * e4 (m + 2) > 19 * e4 (m + 2) := by
                nlinarith [hg2]
              have hP2 : 11 * e4 (m + 1) - e4 m > 0 := by
                nlinarith [hg0, h1, hgm]
              nlinarith [hP1, hP2, h2]
            have hgrowth : 4 * e4 (m + 4) < e4 (m + 5) := by
              have hrec : e4 (m + 5) = 11 * e4 (m + 4) - 25 * e4 (m + 3) + 11 * e4 (m + 2) - e4 (m + 1) := by rfl
              rw [hrec]
              have hA1 : 28 * e4 (m + 3) < 7 * e4 (m + 4) := by
                nlinarith [hg3]
              have hA : 7 * e4 (m + 4) - 25 * e4 (m + 3) > 3 * e4 (m + 3) := by
                nlinarith [hA1]
              have hB : 11 * e4 (m + 2) - e4 (m + 1) > 0 := by
                nlinarith [hg1, h1, h2]
              have hT : 0 < 7 * e4 (m + 4) - 25 * e4 (m + 3) + 11 * e4 (m + 2) - e4 (m + 1) := by
                nlinarith [hA, hB, h3]
              nlinarith [hT]
            constructor
            · exact hpos
            · exact hgrowth
  exact (P n).1

/-- Positivity of the odd sub-series via super-exponential growth. -/
theorem o4_pos (n : Nat) : 0 < o4 n := by
  have P : forall n, (0 < o4 n) ∧ (4 * o4 n < o4 (n + 1)) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        match n with
        | 0 =>
            constructor
            · norm_num [o4]
            · norm_num [o4]
        | 1 =>
            constructor
            · norm_num [o4]
            · norm_num [o4]
        | 2 =>
            constructor
            · norm_num [o4]
            · norm_num [o4]
        | 3 =>
            constructor
            · norm_num [o4]
            · norm_num [o4]
        | m + 4 =>
            have h1 : 0 < o4 (m + 1) := (ih (m + 1) (by omega)).1
            have h2 : 0 < o4 (m + 2) := (ih (m + 2) (by omega)).1
            have h3 : 0 < o4 (m + 3) := (ih (m + 3) (by omega)).1
            have hg1 : 4 * o4 (m + 1) < o4 (m + 2) := (ih (m + 1) (by omega)).2
            have hg2 : 4 * o4 (m + 2) < o4 (m + 3) := (ih (m + 2) (by omega)).2
            have hg3 : 4 * o4 (m + 3) < o4 (m + 4) := (ih (m + 3) (by omega)).2
            have hg0 : 0 < o4 m := (ih m (by omega)).1
            have hgm : o4 m < o4 (m + 1) := by
              have h4 := (ih m (by omega)).2
              nlinarith
            have hpos : 0 < o4 (m + 4) := by
              rw [o4_s4]
              have hP1 : 11 * o4 (m + 3) - 25 * o4 (m + 2) > 19 * o4 (m + 2) := by
                nlinarith [hg2]
              have hP2 : 11 * o4 (m + 1) - o4 m > 0 := by
                nlinarith [hg0, h1, hgm]
              nlinarith [hP1, hP2, h2]
            have hgrowth : 4 * o4 (m + 4) < o4 (m + 5) := by
              have hrec : o4 (m + 5) = 11 * o4 (m + 4) - 25 * o4 (m + 3) + 11 * o4 (m + 2) - o4 (m + 1) := by rfl
              rw [hrec]
              have hA1 : 28 * o4 (m + 3) < 7 * o4 (m + 4) := by
                nlinarith [hg3]
              have hA : 7 * o4 (m + 4) - 25 * o4 (m + 3) > 3 * o4 (m + 3) := by
                nlinarith [hA1]
              have hB : 11 * o4 (m + 2) - o4 (m + 1) > 0 := by
                nlinarith [hg1, h1, h2]
              have hT : 0 < 7 * o4 (m + 4) - 25 * o4 (m + 3) + 11 * o4 (m + 2) - o4 (m + 1) := by
                nlinarith [hA, hB, h3]
              nlinarith [hT]
            constructor
            · exact hpos
            · exact hgrowth
  exact (P n).1

/-- (Wm) e_k o_{k+1} > o_k e_{k+1}  =>  A(2i,2j)=e_i o_j-o_i e_j > 0 for i<j.
    Pure cross-multiplication telescoping, no spectral input. -/
theorem window_ee (e o : Nat -> Int)
    (hwin : forall k, e k * o (k + 1) > o k * e (k + 1))
    (he : forall n, 0 < e n) (ho : forall n, 0 < o n) :
    forall i j, i < j -> e i * o j > o i * e j := by
  intro i j
  induction j with
  | zero => omega
  | succ j ih =>
      intro hij
      by_cases hij1 : i < j
      · have hprev : e i * o j > o i * e j := ih hij1
        have hwinj : e j * o (j + 1) > o j * e (j + 1) := hwin j
        have h1 : (o i * e j) * (e j * o (j + 1)) < (e i * o j) * (e j * o (j + 1)) := by
          have hpos : 0 < e j * o (j + 1) := Int.mul_pos (he j) (ho (j + 1))
          have hlt : o i * e j < e i * o j := by omega
          exact (Int.mul_lt_mul_right hpos).2 hlt
        have h2 : (o i * e j) * (o j * e (j + 1)) < (o i * e j) * (e j * o (j + 1)) := by
          have hpos : 0 < o i * e j := Int.mul_pos (ho i) (he j)
          have hlt : o j * e (j + 1) < e j * o (j + 1) := by omega
          exact (Int.mul_lt_mul_left hpos).2 hlt
        have hmul : (o i * e j) * (o j * e (j + 1)) < (e i * o j) * (e j * o (j + 1)) :=
          lt_trans h2 h1
        have htarget : (o i * e (j + 1)) * (e j * o j) < (e i * o (j + 1)) * (e j * o j) := by
          ring_nf at hmul ⊢
          linarith
        have hc : 0 < e j * o j := Int.mul_pos (he j) (ho j)
        exact (Int.mul_lt_mul_right hc).1 htarget
      · have hEq : i = j := by omega
        subst i
        exact hwin j

/-- (Wp correct direction) o_k e_{k+2} < e_{k+1} o_{k+1}
    =>  A(2i+1,2j+1)=o_i e_{j+1}-e_{i+1} o_j < 0 for i<j.
    Mirror of window_ee, same cross-multiplication. -/
theorem window_oo (e o : Nat -> Int)
    (hwin : forall k, o k * e (k + 2) < e (k + 1) * o (k + 1))
    (he : forall n, 0 < e n) (ho : forall n, 0 < o n) :
    forall i j, i < j -> o i * e (j + 1) < e (i + 1) * o j := by
  intro i j
  induction j with
  | zero => omega
  | succ j ih =>
      intro hij
      by_cases hij1 : i < j
      · have hprev : o i * e (j + 1) < e (i + 1) * o j := ih hij1
        have hwinj : o j * e (j + 2) < e (j + 1) * o (j + 1) := hwin j
        have hpos1 : 0 < o j * e (j + 2) := Int.mul_pos (ho j) (he (j + 2))
        have h1 : (o i * e (j + 1)) * (o j * e (j + 2)) < (e (i + 1) * o j) * (o j * e (j + 2)) := by
          exact (Int.mul_lt_mul_right hpos1).2 hprev
        have hpos2 : 0 < (e (i + 1) * o j) := Int.mul_pos (he (i + 1)) (ho j)
        have h2 : (e (i + 1) * o j) * (o j * e (j + 2)) < (e (i + 1) * o j) * (e (j + 1) * o (j + 1)) := by
          exact (Int.mul_lt_mul_left hpos2).2 hwinj
        have hmul : (o i * e (j + 1)) * (o j * e (j + 2)) < (e (i + 1) * o j) * (e (j + 1) * o (j + 1)) :=
          lt_trans h1 h2
        have htarget : (o i * e (j + 2)) * (o j * e (j + 1)) < (e (i + 1) * o (j + 1)) * (o j * e (j + 1)) := by
          ring_nf at hmul ⊢
          linarith
        have hc : 0 < o j * e (j + 1) := Int.mul_pos (ho j) (he (j + 1))
        exact (Int.mul_lt_mul_right hc).1 htarget
      · have hEq : i = j := by omega
        subst i
        exact hwin j

/-- q=4 same-parity even/even: A_4(2i,2j) > 0 for i<j,
    assuming the q=4 window  e_k o_{k+1} > o_k e_{k+1}. -/
theorem same_parity_ee (hwin : forall k, e4 k * o4 (k + 1) > o4 k * e4 (k + 1)) :
    forall i j, i < j -> e4 i * o4 j > o4 i * e4 j := by
  exact window_ee e4 o4 hwin e4_pos o4_pos

/-- q=4 same-parity odd/odd: A_4(2i+1,2j+1) < 0 for i<j,
    assuming the q=4 window  o_k e_{k+2} < e_{k+1} o_{k+1}. -/
theorem same_parity_oo (hwin : forall k, o4 k * e4 (k + 2) < e4 (k + 1) * o4 (k + 1)) :
    forall i j, i < j -> o4 i * e4 (j + 1) < e4 (i + 1) * o4 j := by
  exact window_oo e4 o4 hwin e4_pos o4_pos

/-- Cross-parity non-adjacent (even,odd): A_4(2i,2j+1) = e_i o_{j+1} - o_i e_{j+1} > 0. -/
theorem cross_parity_eo (hwin : forall k, e4 k * o4 (k + 1) > o4 k * e4 (k + 1)) :
    forall i j, i < j -> e4 i * o4 (j + 1) > o4 i * e4 (j + 1) := by
  intro i j hij
  exact same_parity_ee hwin i (j + 1) (by omega)

/-- Cross-parity non-adjacent (odd,even): A_4(2i+1,2j) = o_i e_{j+1} - e_{i+1} o_j < 0. -/
theorem cross_parity_oe (hwin : forall k, o4 k * e4 (k + 2) < e4 (k + 1) * o4 (k + 1)) :
    forall i j, i < j -> o4 i * e4 (j + 1) < e4 (i + 1) * o4 j := by
  exact same_parity_oo hwin

/-- Linear bridge: 7 * o4 n = 6 e4 n - 30 e4 (n+1) + 12 e4 (n+2) - e4 (n+3). -/
theorem o4_lin_bridge (n : Nat) :
    7 * o4 n = 6 * e4 n - 30 * e4 (n + 1) + 12 * e4 (n + 2) - e4 (n + 3) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      match n with
      | 0 => norm_num [e4, o4]
      | 1 => norm_num [e4, o4]
      | 2 => norm_num [e4, o4]
      | 3 => norm_num [e4, o4]
      | m + 4 =>
          rw [o4_s4]
          have h0 : 7 * o4 m = 6 * e4 m - 30 * e4 (m + 1) + 12 * e4 (m + 2) - e4 (m + 3) := ih m (by omega)
          have h1 : 7 * o4 (m + 1) = 6 * e4 (m + 1) - 30 * e4 (m + 2) + 12 * e4 (m + 3) - e4 (m + 4) := ih (m + 1) (by omega)
          have h2 : 7 * o4 (m + 2) = 6 * e4 (m + 2) - 30 * e4 (m + 3) + 12 * e4 (m + 4) - e4 (m + 5) := ih (m + 2) (by omega)
          have h3 : 7 * o4 (m + 3) = 6 * e4 (m + 3) - 30 * e4 (m + 4) + 12 * e4 (m + 5) - e4 (m + 6) := ih (m + 3) (by omega)
          have h4 : e4 (m + 4) = 11 * e4 (m + 3) - 25 * e4 (m + 2) + 11 * e4 (m + 1) - e4 m := by rfl
          have h5 : e4 (m + 5) = 11 * e4 (m + 4) - 25 * e4 (m + 3) + 11 * e4 (m + 2) - e4 (m + 1) := by rfl
          have h6 : e4 (m + 6) = 11 * e4 (m + 5) - 25 * e4 (m + 4) + 11 * e4 (m + 3) - e4 (m + 2) := by rfl
          have h7 : e4 (m + 7) = 11 * e4 (m + 6) - 25 * e4 (m + 5) + 11 * e4 (m + 4) - e4 (m + 3) := by
            simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using e4_s4 (m + 3)
          nlinarith

/-- Order-5 palindromic recursion for D. -/
theorem D_recur_5 (n : Nat) :
    D (n + 5) = 24 * D (n + 4) - 96 * D (n + 3) + 96 * D (n + 2)
               - 24 * D (n + 1) + D n := by
  have h49 : (49 : Int) * D (n + 5) =
      49 * (24 * D (n + 4) - 96 * D (n + 3) + 96 * D (n + 2)
            - 24 * D (n + 1) + D n) := by
    unfold D
    ring_nf
    rw [show o4 (5 + n) ^ 2 * (49 : Int) = (7 * o4 (5 + n)) ^ 2 by ring]
    rw [show o4 (4 + n) ^ 2 * (1176 : Int) = 24 * (7 * o4 (4 + n)) ^ 2 by ring]
    rw [show o4 (3 + n) ^ 2 * (4704 : Int) = 96 * (7 * o4 (3 + n)) ^ 2 by ring]
    rw [show o4 (2 + n) ^ 2 * (4704 : Int) = 96 * (7 * o4 (2 + n)) ^ 2 by ring]
    rw [show o4 (1 + n) ^ 2 * (1176 : Int) = 24 * (7 * o4 (1 + n)) ^ 2 by ring]
    rw [show o4 n ^ 2 * (49 : Int) = (7 * o4 n) ^ 2 by ring]
    have hs6 : 6 + n = n + 6 := by omega
    have hs5 : 5 + n = n + 5 := by omega
    have hs4 : 4 + n = n + 4 := by omega
    have hs3 : 3 + n = n + 3 := by omega
    have hs2 : 2 + n = n + 2 := by omega
    have hs1 : 1 + n = n + 1 := by omega
    rw [hs6, hs5, hs4, hs3, hs2, hs1]
    have b0 := o4_lin_bridge n
    have b1 : 7 * o4 (n + 1) = 6 * e4 (n + 1) - 30 * e4 (n + 2) + 12 * e4 (n + 3) - e4 (n + 4) := by
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using o4_lin_bridge (n + 1)
    have b2 : 7 * o4 (n + 2) = 6 * e4 (n + 2) - 30 * e4 (n + 3) + 12 * e4 (n + 4) - e4 (n + 5) := by
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using o4_lin_bridge (n + 2)
    have b3 : 7 * o4 (n + 3) = 6 * e4 (n + 3) - 30 * e4 (n + 4) + 12 * e4 (n + 5) - e4 (n + 6) := by
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using o4_lin_bridge (n + 3)
    have b4 : 7 * o4 (n + 4) = 6 * e4 (n + 4) - 30 * e4 (n + 5) + 12 * e4 (n + 6) - e4 (n + 7) := by
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using o4_lin_bridge (n + 4)
    have b5 : 7 * o4 (n + 5) = 6 * e4 (n + 5) - 30 * e4 (n + 6) + 12 * e4 (n + 7) - e4 (n + 8) := by
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using o4_lin_bridge (n + 5)
    rw [b5, b4, b3, b2, b1, b0]
    have h7 : n + 7 = (n + 3) + 4 := by omega
    have h8 : n + 8 = (n + 4) + 4 := by omega
    have h6 : n + 6 = (n + 2) + 4 := by omega
    have h5 : n + 5 = (n + 1) + 4 := by omega
    rw [h7, h8, h6, h5]
    simp only [e4_s4]
    ring
  exact Int.eq_of_mul_eq_mul_left (show (49 : Int) ≠ 0 by norm_num) h49

/-- Auxiliary cone sequence over the reals. -/
def x_aux_real (t x0 x1 : ℝ) : Nat -> ℝ
  | 0 => x0
  | 1 => x1
  | n + 2 => t * x_aux_real t x0 x1 (n + 1) - x_aux_real t x0 x1 n

/-- Cone invariant: t>=2, x0>0, x1>x0 => all terms positive. -/
theorem x_aux_pos_real (t : ℝ) (ht2 : 2 <= t) (x0 : ℝ) (hx0 : 0 < x0)
    (x1 : ℝ) (hx1 : x0 < x1) :
    forall n : Nat, 0 < x_aux_real t x0 x1 n := by
  have P : forall n : Nat,
      (0 < x_aux_real t x0 x1 n) ∧ (x_aux_real t x0 x1 n < x_aux_real t x0 x1 (n + 1)) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        match n with
        | 0 =>
            constructor
            · simpa [x_aux_real] using hx0
            · simpa [x_aux_real] using hx1
        | 1 =>
            have hp0 : 0 < x_aux_real t x0 x1 0 := by simpa [x_aux_real] using hx0
            have hq0 : x_aux_real t x0 x1 0 < x_aux_real t x0 x1 1 := by simpa [x_aux_real] using hx1
            have hx : x_aux_real t x0 x1 2 = (t - 1) * x_aux_real t x0 x1 1 + (x_aux_real t x0 x1 1 - x_aux_real t x0 x1 0) := by
              simp [x_aux_real]; ring
            have hx2pos : 0 < x_aux_real t x0 x1 2 := by
              rw [hx]
              nlinarith [ht2, hp0, hq0]
            have hd : x_aux_real t x0 x1 2 - x_aux_real t x0 x1 1 = (t - 2) * x_aux_real t x0 x1 1 + (x_aux_real t x0 x1 1 - x_aux_real t x0 x1 0) := by
              simp [x_aux_real]; ring
            have hdpos : 0 < x_aux_real t x0 x1 2 - x_aux_real t x0 x1 1 := by
              rw [hd]
              nlinarith [ht2, hp0, hq0]
            constructor
            · exact (lt_trans hp0 hq0)
            · exact sub_pos.mp hdpos
        | m + 2 =>
            have ihPm : 0 < x_aux_real t x0 x1 m := (ih m (by omega)).1
            have ihQm : x_aux_real t x0 x1 m < x_aux_real t x0 x1 (m + 1) := (ih m (by omega)).2
            have ihP1 : 0 < x_aux_real t x0 x1 (m + 1) := (ih (m + 1) (by omega)).1
            have hq1 : x_aux_real t x0 x1 (m + 1) < x_aux_real t x0 x1 (m + 2) := by
              have hx : x_aux_real t x0 x1 (m + 2) - x_aux_real t x0 x1 (m + 1) =
                  (t - 2) * x_aux_real t x0 x1 (m + 1) + (x_aux_real t x0 x1 (m + 1) - x_aux_real t x0 x1 m) := by
                simp [x_aux_real]; ring
              have hpx : 0 < x_aux_real t x0 x1 (m + 2) - x_aux_real t x0 x1 (m + 1) := by
                rw [hx]
                nlinarith [ht2, ihQm, ihP1]
              exact sub_pos.mp hpx
            have hz : x_aux_real t x0 x1 (m + 2) =
                (t - 1) * x_aux_real t x0 x1 (m + 1) + (x_aux_real t x0 x1 (m + 1) - x_aux_real t x0 x1 m) := by
              simp [x_aux_real]; ring
            have hx2pos : 0 < x_aux_real t x0 x1 (m + 2) := by
              rw [hz]
              nlinarith [ht2, ihP1, ihQm]
            have hq2 : x_aux_real t x0 x1 (m + 2) < x_aux_real t x0 x1 (m + 3) := by
              have hx : x_aux_real t x0 x1 (m + 3) - x_aux_real t x0 x1 (m + 2) =
                  (t - 2) * x_aux_real t x0 x1 (m + 2) + (x_aux_real t x0 x1 (m + 2) - x_aux_real t x0 x1 (m + 1)) := by
                simp [x_aux_real]; ring
              have hpx : 0 < x_aux_real t x0 x1 (m + 3) - x_aux_real t x0 x1 (m + 2) := by
                rw [hx]
                nlinarith [ht2, hx2pos, hq1]
              exact sub_pos.mp hpx
            constructor
            · exact hx2pos
            · simpa [Nat.add_assoc] using hq2
  intro n
  exact (P n).1

/-- Spectrum coefficient pair (A_n, B_n). -/
def AB : Nat -> Rat × Rat
  | 0 => (109/58, 27/58)
  | 1 => (852/29, 347/29)
  | n + 2 =>
      let (a1, b1) := AB (n + 1)
      let (a0, b0) := AB n
      ((23 * a1 + 35 * b1) / 2 - a0, (7 * a1 + 23 * b1) / 2 - b0)

def A (n : Nat) : Rat := (AB n).1
def B (n : Nat) : Rat := (AB n).2

lemma AB_s (n : Nat) :
    AB (n + 2) = ((23 * A (n + 1) + 35 * B (n + 1)) / 2 - A n,
                 (7 * A (n + 1) + 23 * B (n + 1)) / 2 - B n) := by
  cases n <;> rfl

noncomputable def U (n : Nat) : ℝ := A n + B n * Real.sqrt 5
noncomputable def V (n : Nat) : ℝ := A n - B n * Real.sqrt 5

lemma t1_gt_two : (2:ℝ) ≤ (23 + 7 * Real.sqrt 5) / 2 := by
  have hsq : (Real.sqrt 5)^2 = 5 := by rw [Real.sq_sqrt]; norm_num
  have hs_ge : (0:ℝ) ≤ Real.sqrt 5 := Real.sqrt_nonneg 5
  nlinarith

lemma t2_gt_two : (2:ℝ) ≤ (23 - 7 * Real.sqrt 5) / 2 := by
  have hsq : (Real.sqrt 5)^2 = 5 := by rw [Real.sq_sqrt]; norm_num
  have hs_lt3 : Real.sqrt 5 < (3:ℝ) := by
    exact (Real.sqrt_lt (by norm_num : (0:ℝ) ≤ 5) (by norm_num : (0:ℝ) ≤ 3)).mpr (by norm_num)
  nlinarith

lemma U_rec (n : Nat) :
    U (n + 2) = (23 + 7 * Real.sqrt 5) / 2 * U (n + 1) - U n := by
  simp [U, A, B, AB_s]
  have hsq : (Real.sqrt 5)^2 = 5 := by rw [Real.sq_sqrt]; norm_num
  ring_nf
  rw [hsq]
  ring_nf

lemma V_rec (n : Nat) :
    V (n + 2) = (23 - 7 * Real.sqrt 5) / 2 * V (n + 1) - V n := by
  simp [V, A, B, AB_s]
  have hsq : (Real.sqrt 5)^2 = 5 := by rw [Real.sq_sqrt]; norm_num
  ring_nf
  rw [hsq]
  ring_nf

lemma U_init : 0 < U 0 ∧ U 0 < U 1 := by
  constructor
  · unfold U A B AB
    norm_num
    have hs_ge : (0:ℝ) ≤ Real.sqrt 5 := Real.sqrt_nonneg 5
    nlinarith
  · unfold U A B AB
    norm_num
    have hs_ge : (0:ℝ) ≤ Real.sqrt 5 := Real.sqrt_nonneg 5
    nlinarith

lemma U_pos (n : Nat) : 0 < U n := by
  have hrec : forall k, U k = x_aux_real ((23 + 7 * Real.sqrt 5) / 2) (U 0) (U 1) k := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ihk =>
        match k with
        | 0 => rfl
        | 1 => rfl
        | kk + 2 =>
            rw [U_rec kk]
            rw [ihk kk (by omega), ihk (kk + 1) (by omega)]
            rfl
  rw [hrec n]
  exact x_aux_pos_real ((23 + 7 * Real.sqrt 5) / 2) t1_gt_two (U 0) U_init.1 (U 1) U_init.2 n

lemma V_pos (n : Nat) : 0 < V n := by
  have h0 : 0 < V 0 := by
    unfold V A B AB
    norm_num
    have hsq : (Real.sqrt 5)^2 = 5 := by rw [Real.sq_sqrt]; norm_num
    have hs_lt3 : Real.sqrt 5 < (3:ℝ) := by
      exact (Real.sqrt_lt (by norm_num : (0:ℝ) ≤ 5) (by norm_num : (0:ℝ) ≤ 3)).mpr (by norm_num)
    nlinarith
  have h10 : V 0 < V 1 := by
    unfold V A B AB
    norm_num
    have hsq : (Real.sqrt 5)^2 = 5 := by rw [Real.sq_sqrt]; norm_num
    have hs_lt3 : Real.sqrt 5 < (3:ℝ) := by
      exact (Real.sqrt_lt (by norm_num : (0:ℝ) ≤ 5) (by norm_num : (0:ℝ) ≤ 3)).mpr (by norm_num)
    nlinarith
  have hrec : forall k, V k = x_aux_real ((23 - 7 * Real.sqrt 5) / 2) (V 0) (V 1) k := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ihk =>
        match k with
        | 0 => rfl
        | 1 => rfl
        | kk + 2 =>
            rw [V_rec kk]
            rw [ihk kk (by omega), ihk (kk + 1) (by omega)]
            rfl
  rw [hrec n]
  exact x_aux_pos_real ((23 - 7 * Real.sqrt 5) / 2) t2_gt_two (V 0) h0 (V 1) h10 n

/-- Bridge identity: 58 A n = 29 D n - 7. -/
theorem D_spectral_bridge (n : Nat) :
    58 * A n = (29 : Rat) * D n - 7 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      match n with
      | 0 => norm_num [D, A, B, AB, e4, o4]
      | 1 => norm_num [D, A, B, AB, e4, o4]
      | 2 => norm_num [D, A, B, AB, e4, o4]
      | 3 => norm_num [D, A, B, AB, e4, o4]
      | 4 => norm_num [D, A, B, AB, e4, o4]
      | m + 5 =>
          have h0 : 58 * A m = (29 : Rat) * D m - 7 := ih m (by omega)
          have h1 : 58 * A (m + 1) = (29 : Rat) * D (m + 1) - 7 := ih (m + 1) (by omega)
          have h2 : 58 * A (m + 2) = (29 : Rat) * D (m + 2) - 7 := ih (m + 2) (by omega)
          have h3 : 58 * A (m + 3) = (29 : Rat) * D (m + 3) - 7 := ih (m + 3) (by omega)
          have h4 : 58 * A (m + 4) = (29 : Rat) * D (m + 4) - 7 := ih (m + 4) (by omega)
          have hD : (29 : Rat) * D (m + 5) =
              24 * ((29 : Rat) * D (m + 4)) - 96 * ((29 : Rat) * D (m + 3))
              + 96 * ((29 : Rat) * D (m + 2)) - 24 * ((29 : Rat) * D (m + 1))
              + (29 : Rat) * D m := by
            have hdi := D_recur_5 m
            have hdi' : (D (m + 5) : Rat) =
                24 * (D (m + 4) : Rat) - 96 * (D (m + 3) : Rat)
                + 96 * (D (m + 2) : Rat) - 24 * (D (m + 1) : Rat) + (D m : Rat) := by
              exact_mod_cast hdi
            rw [hdi']
            ring
          have hA : 58 * (A (m + 5)) =
              24 * (58 * A (m + 4)) - 96 * (58 * A (m + 3))
              + 96 * (58 * A (m + 2)) - 24 * (58 * A (m + 1))
              + 58 * A m := by
            simp [A, B, AB_s (m + 3), AB_s (m + 2), AB_s (m + 1), AB_s m]
            ring
          nlinarith

/-- MAIN: quadrangle positivity D_n > 0 for all n. -/
theorem D_pos (n : Nat) : 0 < D n := by
  have hsum : U n + V n = 2 * (A n : ℝ) := by
    unfold U V
    ring
  have hApos : (0:ℝ) < A n := by
    have hu : (0:ℝ) < U n := U_pos n
    have hv : (0:ℝ) < V n := V_pos n
    nlinarith
  have hbridge_real : (D n : ℝ) = (7:ℝ)/29 + 2 * (A n : ℝ) := by
    have hb := D_spectral_bridge n
    have hb' : (58 : Rat) * A n + 7 = (29 : Rat) * (D n : Rat) := by
      rw [hb]; ring
    have hb'' : (58 : ℝ) * (A n : ℝ) + (7:ℝ) = (29:ℝ) * (D n : ℝ) := by
      exact_mod_cast hb'
    nlinarith
  have hDreal_pos : (0:ℝ) < (D n : ℝ) := by
    rw [hbridge_real]
    nlinarith
  exact_mod_cast hDreal_pos

/-- Full q=4 four-class sign law (hypotheses: the two q=4 window inequalities,
    currently finite-instance evidence).  Together with D_pos this gives
    sign(A_4(a,m;1)) = (-1)^a  for all 0 <= a < m. -/
theorem sign_law_cases (hwin_ee : forall k, e4 k * o4 (k + 1) > o4 k * e4 (k + 1))
    (hwin_oo : forall k, o4 k * e4 (k + 2) < e4 (k + 1) * o4 (k + 1)) :
    (forall i j, i < j -> e4 i * o4 j > o4 i * e4 j) ∧
    (forall i j, i < j -> e4 i * o4 (j + 1) > o4 i * e4 (j + 1)) ∧
    (forall i j, i < j -> o4 i * e4 (j + 1) < e4 (i + 1) * o4 j) ∧
    (forall n, e4 n * e4 (n + 1) - o4 n * o4 n > 0) := by
  constructor
  · exact same_parity_ee hwin_ee
  constructor
  · exact cross_parity_eo hwin_ee
  constructor
  · exact same_parity_oo hwin_oo
  · exact D_pos


/-- Window value Wm_n = e4 n * o4 (n+1) - o4 n * e4 (n+1). -/
def wmQ (n : Nat) : Int := e4 n * o4 (n + 1) - o4 n * e4 (n + 1)

/-- Window value Wp_n = e4 (n+1) * o4 (n+1) - o4 n * e4 (n+2). -/
def wpQ (n : Nat) : Int := e4 (n + 1) * o4 (n + 1) - o4 n * e4 (n + 2)

theorem wmQ_s5 (n : Nat) :
    wmQ (n + 5) = 24 * wmQ (n + 4) - 96 * wmQ (n + 3) + 96 * wmQ (n + 2)
                 - 24 * wmQ (n + 1) + wmQ n := by
  unfold wmQ
  simp only [e4_s4, o4_s4]
  ring

theorem wpQ_s5 (n : Nat) :
    wpQ (n + 5) = 24 * wpQ (n + 4) - 96 * wpQ (n + 3) + 96 * wpQ (n + 2)
                 - 24 * wpQ (n + 1) + wpQ n := by
  unfold wpQ
  simp only [e4_s4, o4_s4]
  ring

/-- Growth of both window sequences (shared helper). -/
theorem growthQ (X : Nat -> Int)
    (hrec : forall n, X (n + 5) = 24 * X (n + 4) - 96 * X (n + 3) + 96 * X (n + 2) - 24 * X (n + 1) + X n)
    (h0 : 0 < X n) (h1 : 0 < X (n + 1)) (h2 : 0 < X (n + 2)) (h3 : 0 < X (n + 3))
    (hg0 : 6 * X n < X (n + 1)) (hg1 : 6 * X (n + 1) < X (n + 2))
    (hg2 : 6 * X (n + 2) < X (n + 3)) (hg3 : 6 * X (n + 3) < X (n + 4)) :
    6 * X (n + 4) < X (n + 5) := by
  rw [hrec n]
  have hA : 18 * X (n + 4) - 96 * X (n + 3) > 12 * X (n + 3) := by
    nlinarith [hg3, h3]
  have hB : 96 * X (n + 2) - 24 * X (n + 1) + X n > 0 := by
    nlinarith [hg2, h2, h1, h0, hg1]
  nlinarith [hA, hB, h3]

/-- Positivity of the even window (unconditional). -/
theorem wmQ_pos (n : Nat) : 0 < wmQ n := by
  have P : forall n, (0 < wmQ n) ∧ (6 * wmQ n < wmQ (n + 1)) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        match n with
        | 0 => constructor <;> norm_num [wmQ, e4, o4]
        | 1 => constructor <;> norm_num [wmQ, e4, o4]
        | 2 => constructor <;> norm_num [wmQ, e4, o4]
        | 3 => constructor <;> norm_num [wmQ, e4, o4]
        | 4 => constructor <;> norm_num [wmQ, e4, o4]
        | m + 5 =>
            have h0 : 0 < wmQ m := (ih m (by omega)).1
            have h1 : 0 < wmQ (m + 1) := (ih (m + 1) (by omega)).1
            have h2 : 0 < wmQ (m + 2) := (ih (m + 2) (by omega)).1
            have h3 : 0 < wmQ (m + 3) := (ih (m + 3) (by omega)).1
            have h4 : 0 < wmQ (m + 4) := (ih (m + 4) (by omega)).1
            have hg0 : 6 * wmQ m < wmQ (m + 1) := (ih m (by omega)).2
            have hg1 : 6 * wmQ (m + 1) < wmQ (m + 2) := (ih (m + 1) (by omega)).2
            have hg2 : 6 * wmQ (m + 2) < wmQ (m + 3) := (ih (m + 2) (by omega)).2
            have hg3 : 6 * wmQ (m + 3) < wmQ (m + 4) := (ih (m + 3) (by omega)).2
            have hg4 : 6 * wmQ (m + 4) < wmQ (m + 5) := growthQ wmQ wmQ_s5 h0 h1 h2 h3 hg0 hg1 hg2 hg3
            have hpos : 0 < wmQ (m + 5) := by
              have hp4 : 0 < 6 * wmQ (m + 4) := by nlinarith [h4]
              exact lt_trans hp4 hg4
            have hg5 : 6 * wmQ (m + 5) < wmQ (m + 6) := growthQ wmQ wmQ_s5 h1 h2 h3 h4 hg1 hg2 hg3 hg4
            constructor
            · exact hpos
            · exact hg5
  exact (P n).1

/-- Positivity of the odd window (unconditional). -/
theorem wpQ_pos (n : Nat) : 0 < wpQ n := by
  have P : forall n, (0 < wpQ n) ∧ (6 * wpQ n < wpQ (n + 1)) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        match n with
        | 0 => constructor <;> norm_num [wpQ, e4, o4]
        | 1 => constructor <;> norm_num [wpQ, e4, o4]
        | 2 => constructor <;> norm_num [wpQ, e4, o4]
        | 3 => constructor <;> norm_num [wpQ, e4, o4]
        | 4 => constructor <;> norm_num [wpQ, e4, o4]
        | m + 5 =>
            have h0 : 0 < wpQ m := (ih m (by omega)).1
            have h1 : 0 < wpQ (m + 1) := (ih (m + 1) (by omega)).1
            have h2 : 0 < wpQ (m + 2) := (ih (m + 2) (by omega)).1
            have h3 : 0 < wpQ (m + 3) := (ih (m + 3) (by omega)).1
            have h4 : 0 < wpQ (m + 4) := (ih (m + 4) (by omega)).1
            have hg0 : 6 * wpQ m < wpQ (m + 1) := (ih m (by omega)).2
            have hg1 : 6 * wpQ (m + 1) < wpQ (m + 2) := (ih (m + 1) (by omega)).2
            have hg2 : 6 * wpQ (m + 2) < wpQ (m + 3) := (ih (m + 2) (by omega)).2
            have hg3 : 6 * wpQ (m + 3) < wpQ (m + 4) := (ih (m + 3) (by omega)).2
            have hg4 : 6 * wpQ (m + 4) < wpQ (m + 5) := growthQ wpQ wpQ_s5 h0 h1 h2 h3 hg0 hg1 hg2 hg3
            have hpos : 0 < wpQ (m + 5) := by
              have hp4 : 0 < 6 * wpQ (m + 4) := by nlinarith [h4]
              exact lt_trans hp4 hg4
            have hg5 : 6 * wpQ (m + 5) < wpQ (m + 6) := growthQ wpQ wpQ_s5 h1 h2 h3 h4 hg1 hg2 hg3 hg4
            constructor
            · exact hpos
            · exact hg5
  exact (P n).1

/-- Unconditional even window inequality. -/
theorem wm_positive_window (k : Nat) :
    e4 k * o4 (k + 1) > o4 k * e4 (k + 1) := by
  have h := wmQ_pos k
  unfold wmQ at h
  linarith

/-- Unconditional odd window inequality. -/
theorem wp_positive_window (k : Nat) :
    o4 k * e4 (k + 2) < e4 (k + 1) * o4 (k + 1) := by
  have h := wpQ_pos k
  unfold wpQ at h
  linarith

/-- FINAL: q=4, s=1 four-point sign law, fully unconditional.
    sign(A_4(a,m;1)) = (-1)^a for all 0 <= a < m, via the four classes. -/
theorem sign_law_unconditional :
    (forall i j, i < j -> e4 i * o4 j > o4 i * e4 j) ∧
    (forall i j, i < j -> e4 i * o4 (j + 1) > o4 i * e4 (j + 1)) ∧
    (forall i j, i < j -> o4 i * e4 (j + 1) < e4 (i + 1) * o4 j) ∧
    (forall n, e4 n * e4 (n + 1) - o4 n * o4 n > 0) := by
  constructor
  · exact same_parity_ee wm_positive_window
  constructor
  · exact cross_parity_eo wm_positive_window
  constructor
  · exact same_parity_oo wp_positive_window
  · exact D_pos


end Q4S1
