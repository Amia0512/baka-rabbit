import Mathlib

set_option maxHeartbeats 0
set_option linter.unusedVariables false

/-!
# q = 4 quadrangle sequence  D_n = e_n * e_{n+1} - o_n^2
Status: 2026-08-26  D_pos CLOSED (official theorem, no sorry/axiom).

Definitions, finite checks, the order-5 recursion (D_recur_5) and the
spectral-cone proof of positivity are all verified in Lean.

Key lemmas:
  * linear bridge      7 o4(n) = 6 e4(n) - 30 e4(n+1) + 12 e4(n+2) - e4(n+3)
                        (strong induction; both series share order-4 recursion)
  * order-5 recursion  D_{n+5} = 24 D_{n+4} - 96 D_{n+3} + 96 D_{n+2} - 24 D_{n+1} + D_n
  * cone invariant     x_aux_pos: for any t >= 2, x0 > 0, x1 > x0, the sequence
                        x_{n+2} = t x_{n+1} - x_n is strictly positive.
  * spectral bridge    D_n = 7/29 + U_n + V_n, where
                        U_n = A_n + B_n sqrt5,  V_n = A_n - B_n sqrt5,
                        A_n,B_n rational sequences (pair AB), and
                        58 A_n = 29 D_n - 7  (D_spectral_bridge).
  * MAIN THEOREM       D_pos : forall n, 0 < D n.
                        U,V are each >= 2-eigenvalue positive cones (U_pos,V_pos),
                        so D_n = 7/29 + U_n + V_n > 0.

Spectrum (exact, all positive roots):
  characteristic (x-1)(x^2 - t1 x + 1)(x^2 - t2 x + 1),
  t1 = (23+7 sqrt5)/2 ~ 19.326, t2 = (23-7 sqrt5)/2 ~ 3.674  (t1+t2 = 23, t1 t2 = 71)
  initial values u0,v0 from (109 pm 27 sqrt5)/58,  u1,v1 from (852 pm 347 sqrt5)/29.

Compile:  set ELAN_HOME=D:/smartrabbit/elan && cd D:\smartrabbit\LeanBP\TestProj && lake env lean D4_quadrangle.lean
-/

namespace D4Q

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

-- Definitional shift lemmas (rfl).
theorem e4_s4 (n : Nat) :
    e4 (n + 4) = 11 * e4 (n + 3) - 25 * e4 (n + 2) + 11 * e4 (n + 1) - e4 n := by rfl

theorem o4_s4 (n : Nat) :
    o4 (n + 4) = 11 * o4 (n + 3) - 25 * o4 (n + 2) + 11 * o4 (n + 1) - o4 n := by rfl

theorem e4_s5 (n : Nat) :
    e4 (n + 5) = 11 * e4 (n + 4) - 25 * e4 (n + 3) + 11 * e4 (n + 2) - e4 (n + 1) := by rfl

theorem o4_s5 (n : Nat) :
    o4 (n + 5) = 11 * o4 (n + 4) - 25 * o4 (n + 3) + 11 * o4 (n + 2) - o4 (n + 1) := by rfl

theorem e4_s6 (n : Nat) :
    e4 (n + 6) = 11 * e4 (n + 5) - 25 * e4 (n + 4) + 11 * e4 (n + 3) - e4 (n + 2) := by rfl

theorem o4_s6 (n : Nat) :
    o4 (n + 6) = 11 * o4 (n + 5) - 25 * o4 (n + 4) + 11 * o4 (n + 3) - o4 (n + 2) := by rfl

-- Initial values (finite check).
example : D 0 = 4 := by native_decide
example : D 1 = 59 := by native_decide
example : D 2 = 1091 := by native_decide
example : D 3 = 20884 := by native_decide
example : D 4 = 402049 := by native_decide
example : D 5 = 7747636 := by native_decide
example : D 6 = 149325299 := by native_decide
example : D 7 = 2878130699 := by native_decide
example : D 8 = 55474052836 := by native_decide
example : D 9 = 1069226408449 := by native_decide
example : D 10 = 20608649218084 := by native_decide
example : D 11 = 397218429283691 := by native_decide

/-- Linear bridge between the odd and even sub-series:
    7 * o4(n) = 6*e4(n) - 30*e4(n+1) + 12*e4(n+2) - e4(n+3). -/
theorem o4_lin (n : Nat) :
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
          have he4 : e4 (m + 4) = 11 * e4 (m + 3) - 25 * e4 (m + 2) + 11 * e4 (m + 1) - e4 m := e4_s4 m
          have he5 : e4 (m + 5) = 11 * e4 (m + 4) - 25 * e4 (m + 3) + 11 * e4 (m + 2) - e4 (m + 1) := e4_s5 m
          have he6 : e4 (m + 6) = 11 * e4 (m + 5) - 25 * e4 (m + 4) + 11 * e4 (m + 3) - e4 (m + 2) := e4_s6 m
          have he7 : e4 (m + 7) = 11 * e4 (m + 6) - 25 * e4 (m + 5) + 11 * e4 (m + 4) - e4 (m + 3) := by
            simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using e4_s4 (m + 3)
          nlinarith

theorem o4_lin1 (n : Nat) :
    7 * o4 (n + 1) = 6 * e4 (n + 1) - 30 * e4 (n + 2) + 12 * e4 (n + 3) - e4 (n + 4) := by
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using o4_lin (n + 1)

theorem o4_lin2 (n : Nat) :
    7 * o4 (n + 2) = 6 * e4 (n + 2) - 30 * e4 (n + 3) + 12 * e4 (n + 4) - e4 (n + 5) := by
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using o4_lin (n + 2)

theorem o4_lin3 (n : Nat) :
    7 * o4 (n + 3) = 6 * e4 (n + 3) - 30 * e4 (n + 4) + 12 * e4 (n + 5) - e4 (n + 6) := by
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using o4_lin (n + 3)

theorem o4_lin4 (n : Nat) :
    7 * o4 (n + 4) = 6 * e4 (n + 4) - 30 * e4 (n + 5) + 12 * e4 (n + 6) - e4 (n + 7) := by
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using o4_lin (n + 4)

theorem o4_lin5 (n : Nat) :
    7 * o4 (n + 5) = 6 * e4 (n + 5) - 30 * e4 (n + 6) + 12 * e4 (n + 7) - e4 (n + 8) := by
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using o4_lin (n + 5)

-- Initial values (finite check) for the closed recursion.
example : D 12 = 7656129213946259 := by native_decide

/-- Order-5 palindromic recursion for D:
    D_{n+5} = 24 D_{n+4} - 96 D_{n+3} + 96 D_{n+2} - 24 D_{n+1} + D_n. -/
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
    rw [o4_lin5 n, o4_lin4 n, o4_lin3 n, o4_lin2 n, o4_lin1 n, o4_lin n]
    have h7 : n + 7 = (n + 3) + 4 := by omega
    have h8 : n + 8 = (n + 4) + 4 := by omega
    have h6 : n + 6 = (n + 2) + 4 := by omega
    have h5 : n + 5 = (n + 1) + 4 := by omega
    rw [h7, h8, h6, h5]
    simp only [e4_s4]
    ring
  exact Int.eq_of_mul_eq_mul_left (show (49 : Int) ≠ 0 by norm_num) h49

end D4Q

open D4Q

/-- Spectrum coefficient pair (A_n, B_n):  U_n = A_n + B_n*sqrt 5,
    V_n = A_n - B_n*sqrt 5.  Branches satisfy x_{n+2} = t_i x_{n+1} - x_n,
    t1 = (23+7*sqrt 5)/2,  t2 = (23-7*sqrt 5)/2. -/
def AB : Nat -> Rat × Rat
  | 0 => (109/58, 27/58)
  | 1 => (852/29, 347/29)
  | n + 2 =>
      let (a1, b1) := AB (n + 1)
      let (a0, b0) := AB n
      ((23 * a1 + 35 * b1) / 2 - a0, (7 * a1 + 23 * b1) / 2 - b0)

def A (n : Nat) : Rat := (AB n).1
def B (n : Nat) : Rat := (AB n).2

/-- Two-step recursion of AB (definitional). -/
lemma AB_s (n : Nat) :
    AB (n + 2) = ((23 * A (n + 1) + 35 * B (n + 1)) / 2 - A n,
                 (7 * A (n + 1) + 23 * B (n + 1)) / 2 - B n) := by
  cases n <;> rfl

/-- Real version of the aux sequence. -/
def x_aux_real (t x0 x1 : ℝ) : Nat -> ℝ
  | 0 => x0
  | 1 => x1
  | n + 2 => t * x_aux_real t x0 x1 (n + 1) - x_aux_real t x0 x1 n

/-- Cone-invariance in ℝ:  t >= 2, x0 > 0, x1 > x0  =>  all terms > 0. -/
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

/-- Spectral branches on the reals. -/
noncomputable def U (n : Nat) : ℝ := A n + B n * Real.sqrt 5
noncomputable def V (n : Nat) : ℝ := A n - B n * Real.sqrt 5

/-- t1 = (23 + 7 sqrt5)/2 > 2. -/
lemma t1_gt_two : (2:ℝ) ≤ (23 + 7 * Real.sqrt 5) / 2 := by
  have hsq : (Real.sqrt 5)^2 = 5 := by rw [Real.sq_sqrt]; norm_num
  have hs_ge : (0:ℝ) ≤ Real.sqrt 5 := Real.sqrt_nonneg 5
  nlinarith

/-- t2 = (23 - 7 sqrt5)/2 > 2  (uses sqrt5 < 3). -/
lemma t2_gt_two : (2:ℝ) ≤ (23 - 7 * Real.sqrt 5) / 2 := by
  have hsq : (Real.sqrt 5)^2 = 5 := by rw [Real.sq_sqrt]; norm_num
  have hs_lt3 : Real.sqrt 5 < (3:ℝ) := by
    exact (Real.sqrt_lt (by norm_num : (0:ℝ) ≤ 5) (by norm_num : (0:ℝ) ≤ 3)).mpr (by norm_num)
  nlinarith

/-- U satisfies the t1 recursion. -/
lemma U_rec (n : Nat) :
    U (n + 2) = (23 + 7 * Real.sqrt 5) / 2 * U (n + 1) - U n := by
  simp [U, A, B, AB_s]
  have hsq : (Real.sqrt 5)^2 = 5 := by rw [Real.sq_sqrt]; norm_num
  ring_nf
  rw [hsq]
  ring_nf

/-- V satisfies the t2 recursion. -/
lemma V_rec (n : Nat) :
    V (n + 2) = (23 - 7 * Real.sqrt 5) / 2 * V (n + 1) - V n := by
  simp [V, A, B, AB_s]
  have hsq : (Real.sqrt 5)^2 = 5 := by rw [Real.sq_sqrt]; norm_num
  ring_nf
  rw [hsq]
  ring_nf

/-- Initial values for U. -/
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

/-- U_n > 0 for all n. -/
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

/-- V_n > 0 for all n. -/
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

/-- Bridge identity:  58 * A_n = 29 * D_n - 7, i.e.  D_n = 7/29 + 2 A_n. -/
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

/-- MAIN RESULT:  D_n > 0 for all n.
    Proof:  D_n = 7/29 + 2 A_n  (bridge), and 2 A_n = U_n + V_n with
    both U_n, V_n > 0 by the cone-invariance argument. -/
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
    -- 58 A n = 29 D n - 7  =>  D n = 7/29 + 2 A n
    have hb' : (58 : Rat) * A n + 7 = (29 : Rat) * (D n : Rat) := by
      rw [hb]; ring
    -- cast to real and linear arithmetic
    have hb'' : (58 : ℝ) * (A n : ℝ) + (7:ℝ) = (29:ℝ) * (D n : ℝ) := by
      exact_mod_cast hb'
    nlinarith
  have hDreal_pos : (0:ℝ) < (D n : ℝ) := by
    rw [hbridge_real]
    nlinarith
  exact_mod_cast hDreal_pos
