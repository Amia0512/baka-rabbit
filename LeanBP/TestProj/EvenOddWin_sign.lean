import Mathlib.Data.Int.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

set_option maxHeartbeats 0
set_option linter.unusedVariables false

/-!
# Even-q, s=1: same-parity four-point signs via window cross-multiplication

For even height q write e_n = T_q(2n), o_n = T_q(2n+1) (positive integers).
The window inequalities are
    Wm_k = o_k*e_{k+1} - e_k*o_{k+1} < 0      (i.e. e_k*o_{k+1} > o_k*e_{k+1})        (W-)
    Wp_k = e_{k+1}*o_{k+1} - o_k*e_{k+2} > 0  (i.e. o_k*e_{k+2} < e_{k+1}*o_{k+1})    (W+)
which mean the ratios u_k = e_k/o_k and v_k = e_{k+1}/o_k are respectively
strictly decreasing and strictly increasing.

For the four-point bracket A(a,m)=T(a)T(m+1)-T(a+1)T(m) the same-parity
cases (i<j) are
    A(2i,2j)     = e_i*o_j - o_i*e_j           (even/even)
    A(2i+1,2j+1) = o_i*e_{j+1} - e_{i+1}*o_j   (odd/odd)
and the windows imply both > 0 by pure cross-multiplication telescoping
(no spectral input, no TP2):

    e_i*o_j / (o_i*e_j)   = prod_{k=i}^{j-1} [ e_k*o_{k+1} / (o_k*e_{k+1}) ]           > 1
    o_i*e_{j+1} / (e_{i+1}*o_j) = prod_{k=i}^{j-1} [ o_k*e_{k+2} / (e_{k+1}*o_{k+1}) ] > 1

This file proves both implications over an abstract positive integer
sequence: the same-parity part of the s=1 sign law for every even q.

CHECKPOINT 2026-08-25: zero sorry, parameterized over e,o : Nat -> Int.
-/

namespace EvenOddWin

/-- (W-): u_k = e_k/o_k strictly decreasing => e_i*o_j > o_i*e_j for i<j. -/
theorem ee_pos (e o : Nat -> Int)
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
        -- Step 1: (o_i*e_j)*(e_j*o_{j+1}) < (e_i*o_j)*(e_j*o_{j+1})
        have h1 : (o i * e j) * (e j * o (j + 1)) < (e i * o j) * (e j * o (j + 1)) := by
          have hpos : 0 < e j * o (j + 1) := Int.mul_pos (he j) (ho (j + 1))
          have hlt : o i * e j < e i * o j := by omega
          exact (Int.mul_lt_mul_right hpos).2 hlt
        -- Step 2: (o_i*e_j)*(o_j*e_{j+1}) < (o_i*e_j)*(e_j*o_{j+1})
        have h2 : (o i * e j) * (o j * e (j + 1)) < (o i * e j) * (e j * o (j + 1)) := by
          have hpos : 0 < o i * e j := Int.mul_pos (ho i) (he j)
          have hlt : o j * e (j + 1) < e j * o (j + 1) := by omega
          exact (Int.mul_lt_mul_left hpos).2 hlt
        -- Chain: (o_i*e_j)*(o_j*e_{j+1}) < (e_i*o_j)*(e_j*o_{j+1})
        have hmul : (o i * e j) * (o j * e (j + 1)) < (e i * o j) * (e j * o (j + 1)) :=
          lt_trans h2 h1
        -- Restate with the common factor e_j*o_j
        have htarget : (o i * e (j + 1)) * (e j * o j) < (e i * o (j + 1)) * (e j * o j) := by
          ring_nf at hmul ⊢
          linarith
        have hc : 0 < e j * o j := Int.mul_pos (he j) (ho j)
        exact (Int.mul_lt_mul_right hc).1 htarget
      · have hEq : i = j := by omega
        subst i
        exact hwin j

/-- (W+): v_k = e_{k+1}/o_k strictly increasing => o_i*e_{j+1} > e_{i+1}*o_j for i<j. -/
theorem oo_pos (e o : Nat -> Int)
    (hwin : forall k, o k * e (k + 2) > e (k + 1) * o (k + 1))
    (he : forall n, 0 < e n) (ho : forall n, 0 < o n) :
    forall i j, i < j -> o i * e (j + 1) > e (i + 1) * o j := by
  intro i j
  induction j with
  | zero => omega
  | succ j ih =>
      intro hij
      by_cases hij1 : i < j
      · have hprev : o i * e (j + 1) > e (i + 1) * o j := ih hij1
        have hwinj : o j * e (j + 2) > e (j + 1) * o (j + 1) := hwin j
        -- Step 1: (e_{i+1}*o_j)*(o_j*e_{j+2}) < (o_i*e_{j+1})*(o_j*e_{j+2})
        have h1 : (e (i + 1) * o j) * (o j * e (j + 2)) < (o i * e (j + 1)) * (o j * e (j + 2)) := by
          have hpos : 0 < o j * e (j + 2) := Int.mul_pos (ho j) (he (j + 2))
          have hlt : e (i + 1) * o j < o i * e (j + 1) := by omega
          exact (Int.mul_lt_mul_right hpos).2 hlt
        -- Step 2: (e_{i+1}*o_j)*(e_{j+1}*o_{j+1}) < (e_{i+1}*o_j)*(o_j*e_{j+2})
        have h2 : (e (i + 1) * o j) * (e (j + 1) * o (j + 1)) < (e (i + 1) * o j) * (o j * e (j + 2)) := by
          have hpos : 0 < e (i + 1) * o j := Int.mul_pos (he (i + 1)) (ho j)
          have hlt : e (j + 1) * o (j + 1) < o j * e (j + 2) := by omega
          exact (Int.mul_lt_mul_left hpos).2 hlt
        have hmul : (e (i + 1) * o j) * (e (j + 1) * o (j + 1)) < (o i * e (j + 1)) * (o j * e (j + 2)) :=
          lt_trans h2 h1
        have htarget : (e (i + 1) * o (j + 1)) * (e (j + 1) * o j) < (o i * e (j + 2)) * (e (j + 1) * o j) := by
          ring_nf at hmul ⊢
          linarith
        have hc : 0 < e (j + 1) * o j := Int.mul_pos (he (j + 1)) (ho j)
        exact (Int.mul_lt_mul_right hc).1 htarget
      · have hEq : i = j := by omega
        subst i
        exact hwin j

end EvenOddWin