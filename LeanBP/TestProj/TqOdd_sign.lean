import Mathlib.Data.Int.Fib.Basic
import Mathlib.Data.Int.Fib.Lemmas
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

set_option maxHeartbeats 0
set_option linter.unusedVariables false

/-!
# Odd-q, s=1: four-point sign via area parity

For height q ODD the strip q x L is tileable iff L is even:
  * L odd  : q*L odd, no tiling, so T_q(L) = 0;
  * L even : q*L even and the all-horizontal tiling exists, so 0 < T_q(L).

For the shift s = 1 the A-level quantity is
    A_q(a, m) = T_q(a) T_q(m+1) - T_q(a+1) T_q(m).
The parity profile above forces, for a < m:
  * if a and m have the same parity then A_q = 0 (side vanishes);
  * if they have opposite parity then sign(A_q) = (-1)^a, matching A_2.
Equivalently:  0 ≤ (-1)^a * A_q(a, m)   for all a < m.
-/

namespace TqOdd

open Int

/-- (-1)^(2n) = 1. -/
lemma pow_neg_one_even (n : Nat) : (-1 : Int) ^ (2 * n) = 1 := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      rw [Nat.mul_succ]
      rw [pow_succ, pow_succ]
      rw [ih]
      norm_num

/-- (-1)^(2n+1) = -1. -/
lemma pow_neg_one_odd (n : Nat) : (-1 : Int) ^ (2 * n + 1) = -1 := by
  rw [pow_succ]
  rw [pow_neg_one_even n]
  norm_num

/-- Parity profile of T at a pair of adjacent widths: one slot vanishes,
    the other is positive, together with the sign of (-1)^a. -/
lemma pair_case (T : Nat → Int)
    (hEven : ∀ n, 0 < T (2 * n)) (hOdd : ∀ n, T (2 * n + 1) = 0) (a : Nat) :
    (T a = 0 ∧ 0 < T (a + 1) ∧ (-1 : Int) ^ a = -1) ∨
    (0 < T a ∧ T (a + 1) = 0 ∧ (-1 : Int) ^ a = 1) := by
  by_cases haOdd : Odd a
  · left
    rcases haOdd with ⟨n, hn⟩
    have hpow : (-1 : Int) ^ a = -1 := by
      rw [hn]
      exact pow_neg_one_odd n
    constructor
    · rw [hn]; exact hOdd n
    constructor
    · have hnext : a + 1 = 2 * (n + 1) := by omega
      rw [hnext]; exact hEven (n + 1)
    · exact hpow
  · right
    have hev : Even a := (Nat.even_or_odd a).resolve_right haOdd
    constructor
    · rcases hev with ⟨n, hn⟩
      have h2 : a = 2 * n := by omega
      rw [h2]
      have hc : 2 * n = n * 2 := by omega
      rw [hc]
      simpa [mul_comm] using hEven n
    constructor
    · rcases hev with ⟨n, hn⟩
      have hnext : a + 1 = 2 * n + 1 := by omega
      rw [hnext]; exact hOdd n
    · rcases hev with ⟨n, hn⟩
      have h2 : a = 2 * n := by omega
      rw [h2]
      exact pow_neg_one_even n

/-- The four-point bridge for odd q, s = 1: for a < m,
      0 ≤ (-1)^a * A_q(a, m). -/
theorem E_sign_via_parity (T : Nat → Int)
    (hEven : ∀ n, 0 < T (2 * n)) (hOdd : ∀ n, T (2 * n + 1) = 0)
    (a m : Nat) (ham : a < m) :
    0 ≤ (-1 : Int) ^ a * (T a * T (m + 1) - T (a + 1) * T m) := by
  have hp := pair_case T hEven hOdd a
  have hq := pair_case T hEven hOdd m
  rcases hp with hpaL | hpaR
  · rcases hq with hpmL | hpmR
    · -- a odd, m odd: both T(a)=0, T(m)=0
      rw [hpaL.1, hpmL.1, hpaL.2.2]
      norm_num
    · -- a odd, m even: T(a)=0, T(m+1)=0
      rw [hpaL.1, hpmR.2.1, hpaL.2.2]
      have hpos1 : 0 < T (a + 1) := hpaL.2.1
      have hpos2 : 0 < T m := hpmR.1
      nlinarith [hpos1, hpos2]
  · rcases hq with hpmL | hpmR
    · -- a even, m odd: T(a+1)=0, T(m)=0
      rw [hpaR.2.1, hpmL.1, hpaR.2.2]
      have hpos1 : 0 < T a := hpaR.1
      have hpos2 : 0 < T (m + 1) := hpmL.2.1
      nlinarith [hpos1, hpos2]
    · -- a even, m even: T(a+1)=0, T(m+1)=0
      rw [hpaR.2.1, hpmR.2.1, hpaR.2.2]
      norm_num

end TqOdd