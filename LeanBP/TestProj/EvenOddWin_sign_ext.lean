import Mathlib.Data.Int.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

set_option maxHeartbeats 0
set_option linter.unusedVariables false

/-!
# Even-q, s=1: same-parity four-point signs via window cross-multiplication (extended)

This file provides the direction-correct version of the odd/odd window lemma:

    oo_neg : (forall k, o k * e (k+2) < e (k+1) * o (k+1))
             -> forall i j, i < j -> o i * e (j+1) < e (i+1) * o j

The original EvenOddWin.oo_pos assumed the opposite window direction
(o k * e (k+2) > e (k+1) * o (k+1)) and proved >, which does NOT match the
q=2,4,6,... empirical sign table (e.g. q=4: o_0 e_2 = 36 < 55 = e_1 o_1).
For the even-q s=1 sign law the correct same-parity odd/odd sign is

    A(2i+1,2j+1) = o_i e_{j+1} - e_{i+1} o_j < 0   (i < j),

which is exactly the conclusion of oo_neg below.  The proof is the exact
mirror of oo_pos: pure cross-multiplication telescoping, no spectral input.

CHECKPOINT 2026-08-26: zero sorry, parameterized over e,o : Nat -> Int.
-/


namespace EvenOddWin

/-- (W+ reversed, correct direction): v_k = e_{k+1}/o_k strictly DECREASING
    (i.e. o_k * e_{k+2} < e_{k+1} * o_{k+1}) implies
    o_i * e_{j+1} < e_{i+1} * o_j for i<j. -/
theorem oo_neg (e o : Nat -> Int)
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
        -- combine: (o_i e_{j+1}) * (o_j e_{j+2}) < (e_{i+1} o_j) * (e_{j+1} o_{j+1})
        have hpos1 : 0 < o j * e (j + 2) := Int.mul_pos (ho j) (he (j + 2))
        have h1 : (o i * e (j + 1)) * (o j * e (j + 2)) < (e (i + 1) * o j) * (o j * e (j + 2)) := by
          exact (Int.mul_lt_mul_right hpos1).2 hprev
        have hpos2 : 0 < (e (i + 1) * o j) := Int.mul_pos (he (i + 1)) (ho j)
        have h2 : (e (i + 1) * o j) * (o j * e (j + 2)) < (e (i + 1) * o j) * (e (j + 1) * o (j + 1)) := by
          exact (Int.mul_lt_mul_left hpos2).2 hwinj
        have hmul : (o i * e (j + 1)) * (o j * e (j + 2)) < (e (i + 1) * o j) * (e (j + 1) * o (j + 1)) :=
          lt_trans h1 h2
        -- goal: o_i e_{j+2} < e_{i+1} o_{j+1}.  rewrite both sides by ring to expose common o_j e_{j+1}
        have htarget : (o i * e (j + 2)) * (o j * e (j + 1)) < (e (i + 1) * o (j + 1)) * (o j * e (j + 1)) := by
          ring_nf at hmul ⊢
          linarith
        have hc : 0 < o j * e (j + 1) := Int.mul_pos (ho j) (he (j + 1))
        exact (Int.mul_lt_mul_right hc).1 htarget
      · have hEq : i = j := by omega
        subst i
        exact hwin j
end EvenOddWin
