import Mathlib

set_option maxHeartbeats 0
set_option linter.unusedVariables false

/-!
# q=4 window positivity: Wm_n>0 and Wp_n>0 for all n (self-contained)

Wm_n = e_n o_{n+1} - o_n e_{n+1}       (even window, e_k o_{k+1} > o_k e_{k+1})
Wp_n = e_{n+1} o_{n+1} - o_n e_{n+2}   (odd window, o_k e_{k+2} < e_{k+1} o_{k+1})

Strategy:
  1. define e4/o4 by the order-4 palindromic recursion (true T_4 sub-series);
  2. define wm/wp as the exact window values;
  3. prove the order-5 palindromic recursion for wm/wp (bridge_rec / bridge_rec_p,
     algebraic consequence of the order-4 recursions);
  4. prove 6-fold growth (6X_n < X_{n+1}) by strong induction => 0 < wm/wp.

This makes the two q=4 window inequalities UNCONDITIONAL theorems, closing
the only remaining input of Q4S1 (q4_s1_signlaw.lean).

CHECKPOINT 2026-08-26: zero sorry.
-/

namespace Q4Win

/-- Even sub-series T_4(2n). -/
def e4 : Nat -> Int
  | 0 => 1
  | 1 => 5
  | 2 => 36
  | 3 => 281
  | n + 4 => 11 * e4 (n + 3) - 25 * e4 (n + 2) + 11 * e4 (n + 1) - e4 n

/-- Odd sub-series T_4(2n+1). -/
def o4 : Nat -> Int
  | 0 => 1
  | 1 => 11
  | 2 => 95
  | 3 => 781
  | n + 4 => 11 * o4 (n + 3) - 25 * o4 (n + 2) + 11 * o4 (n + 1) - o4 n

theorem e4_s4 (n : Nat) :
    e4 (n + 4) = 11 * e4 (n + 3) - 25 * e4 (n + 2) + 11 * e4 (n + 1) - e4 n := by rfl

theorem o4_s4 (n : Nat) :
    o4 (n + 4) = 11 * o4 (n + 3) - 25 * o4 (n + 2) + 11 * o4 (n + 1) - o4 n := by rfl

/-- Even window value (true quadratic form). -/
def wm (n : Nat) : Int := e4 n * o4 (n + 1) - o4 n * e4 (n + 1)

/-- Odd window value (true quadratic form). -/
def wp (n : Nat) : Int := e4 (n + 1) * o4 (n + 1) - o4 n * e4 (n + 2)

/-- Wm satisfies the order-5 palindromic recursion (algebraic identity). -/
theorem wm_s5 (n : Nat) :
    wm (n + 5) = 24 * wm (n + 4) - 96 * wm (n + 3) + 96 * wm (n + 2) - 24 * wm (n + 1) + wm n := by
  unfold wm
  simp only [e4_s4, o4_s4]
  ring

/-- Wp satisfies the order-5 palindromic recursion (algebraic identity). -/
theorem wp_s5 (n : Nat) :
    wp (n + 5) = 24 * wp (n + 4) - 96 * wp (n + 3) + 96 * wp (n + 2) - 24 * wp (n + 1) + wp n := by
  unfold wp
  simp only [e4_s4, o4_s4]
  ring

/-- Initial values. -/
theorem wm_init : wm 0 = 6 ∧ wm 1 = 79 ∧ wm 2 = 1421 ∧ wm 3 = 27071 ∧ wm 4 = 520729 := by
  norm_num [wm, e4, o4]

theorem wp_init : wp 0 = 19 ∧ wp 1 = 329 ∧ wp 2 = 6186 ∧ wp 3 = 118679 ∧ wp 4 = 2285569 := by
  norm_num [wp, e4, o4]

/-- Growth step: 6X_n < X_{n+1} for n..n+3 and positivity imply 6X_{n+4} < X_{n+5}. -/
theorem growth_5 (X : Nat -> Int)
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

/-- Positivity of the even window by strong induction. -/
theorem wm_pos (n : Nat) : 0 < wm n := by
  have P : forall n, (0 < wm n) ∧ (6 * wm n < wm (n + 1)) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        match n with
        | 0 => constructor <;> norm_num [wm, e4, o4]
        | 1 => constructor <;> norm_num [wm, e4, o4]
        | 2 => constructor <;> norm_num [wm, e4, o4]
        | 3 => constructor <;> norm_num [wm, e4, o4]
        | 4 => constructor <;> norm_num [wm, e4, o4]
        | m + 5 =>
            have h0 : 0 < wm m := (ih m (by omega)).1
            have h1 : 0 < wm (m + 1) := (ih (m + 1) (by omega)).1
            have h2 : 0 < wm (m + 2) := (ih (m + 2) (by omega)).1
            have h3 : 0 < wm (m + 3) := (ih (m + 3) (by omega)).1
            have h4 : 0 < wm (m + 4) := (ih (m + 4) (by omega)).1
            have hg0 : 6 * wm m < wm (m + 1) := (ih m (by omega)).2
            have hg1 : 6 * wm (m + 1) < wm (m + 2) := (ih (m + 1) (by omega)).2
            have hg2 : 6 * wm (m + 2) < wm (m + 3) := (ih (m + 2) (by omega)).2
            have hg3 : 6 * wm (m + 3) < wm (m + 4) := (ih (m + 3) (by omega)).2
            have hg4 : 6 * wm (m + 4) < wm (m + 5) := growth_5 wm wm_s5 h0 h1 h2 h3 hg0 hg1 hg2 hg3
            have hpos : 0 < wm (m + 5) := by
              have hp4 : 0 < 6 * wm (m + 4) := by nlinarith [h4]
              exact lt_trans hp4 hg4
            have hg5 : 6 * wm (m + 5) < wm (m + 6) := growth_5 wm wm_s5 h1 h2 h3 h4 hg1 hg2 hg3 hg4
            constructor
            · exact hpos
            · exact hg5
  exact (P n).1

/-- Positivity of the odd window by strong induction. -/
theorem wp_pos (n : Nat) : 0 < wp n := by
  have P : forall n, (0 < wp n) ∧ (6 * wp n < wp (n + 1)) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        match n with
        | 0 => constructor <;> norm_num [wp, e4, o4]
        | 1 => constructor <;> norm_num [wp, e4, o4]
        | 2 => constructor <;> norm_num [wp, e4, o4]
        | 3 => constructor <;> norm_num [wp, e4, o4]
        | 4 => constructor <;> norm_num [wp, e4, o4]
        | m + 5 =>
            have h0 : 0 < wp m := (ih m (by omega)).1
            have h1 : 0 < wp (m + 1) := (ih (m + 1) (by omega)).1
            have h2 : 0 < wp (m + 2) := (ih (m + 2) (by omega)).1
            have h3 : 0 < wp (m + 3) := (ih (m + 3) (by omega)).1
            have h4 : 0 < wp (m + 4) := (ih (m + 4) (by omega)).1
            have hg0 : 6 * wp m < wp (m + 1) := (ih m (by omega)).2
            have hg1 : 6 * wp (m + 1) < wp (m + 2) := (ih (m + 1) (by omega)).2
            have hg2 : 6 * wp (m + 2) < wp (m + 3) := (ih (m + 2) (by omega)).2
            have hg3 : 6 * wp (m + 3) < wp (m + 4) := (ih (m + 3) (by omega)).2
            have hg4 : 6 * wp (m + 4) < wp (m + 5) := growth_5 wp wp_s5 h0 h1 h2 h3 hg0 hg1 hg2 hg3
            have hpos : 0 < wp (m + 5) := by
              have hp4 : 0 < 6 * wp (m + 4) := by nlinarith [h4]
              exact lt_trans hp4 hg4
            have hg5 : 6 * wp (m + 5) < wp (m + 6) := growth_5 wp wp_s5 h1 h2 h3 h4 hg1 hg2 hg3 hg4
            constructor
            · exact hpos
            · exact hg5
  exact (P n).1

/-- MAIN: even window, unconditional:  e_k o_{k+1} > o_k e_{k+1}. -/
theorem wm_positive_window (k : Nat) :
    e4 k * o4 (k + 1) > o4 k * e4 (k + 1) := by
  have h := wm_pos k
  unfold wm at h
  linarith

/-- MAIN: odd window, unconditional:  o_k e_{k+2} < e_{k+1} o_{k+1}. -/
theorem wp_positive_window (k : Nat) :
    o4 k * e4 (k + 2) < e4 (k + 1) * o4 (k + 1) := by
  have h := wp_pos k
  unfold wp at h
  linarith

end Q4Win
