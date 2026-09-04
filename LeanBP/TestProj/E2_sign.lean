import Mathlib.Data.Int.Fib.Basic
import Mathlib.Data.Int.Fib.Lemmas
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

set_option maxHeartbeats 0
set_option linter.unusedVariables false

/-!
# E_2 sign law for s = 1 (q = 2 closure, self-contained)

In the A-level four-point reduction the quantity for height 2 is
    A_2(l, r; s) = F(l+1)F(r+1) - F(l-s+1)F(r+s+1).
For s = 1 and the slice l = a+1, m = r+1 the associated four-point
difference is
    E_2(a, m) = F(a+1)F(m+2) - F(a+2)F(m+1).
The d'Ocagne closed form (proved here, same argument as
A2_dOcagne_sign.lean but self-contained) gives for a ≤ m:

    E_2(a, m) = (-1)^a * F(m-a)

where F denotes the integer Fibonacci sequence.  This closes the q = 2,
s = 1 instance of the four-point sign identity sign(A_q) = sign(A_2).

CHECKPOINT 2026-08-25 (compile-clean, zero sorry):
  theorem E2_s1_closed (a m : ℕ) (hm : a ≤ m) :
      fib (↑a + 1) * fib (↑m + 2) - fib (↑a + 2) * fib (↑m + 1)
        = (-1 : ℤ) ^ a * fib (↑(m - a))
-/

namespace E2S1

open Int

/-- Cassini bracket (natural index, integers):
    fib(a)^2 - fib(a+1)*fib(a-1) = (-1)^(a+1). -/
theorem fib_cassini_bracket (a : ℕ) :
    (fib (↑a : ℤ)) ^ 2 - fib (↑a + 1) * fib (↑a - 1) = (-1 : ℤ) ^ (a + 1) := by
  have h := Int.fib_succ_mul_fib_pred_sub_fib_sq (↑a : ℤ)
  have hnat : ((↑a : ℤ).natAbs) = a := by exact Int.natAbs_natCast a
  have h' : fib (↑a + 1) * fib (↑a - 1) - (fib (↑a : ℤ)) ^ 2 = (-1 : ℤ) ^ a := by
    rwa [hnat] at h
  have hnegs : -((-1 : ℤ) ^ a) = (-1 : ℤ) ^ (a + 1) := by
    rw [pow_succ]
    ring
  omega

/-- d'Ocagne closed form:
    fib(a)*fib(m+1) - fib(a+1)*fib(m) = (-1)^(a+1) fib(m-a)  for a ≤ m. -/
theorem dOcagne_closed (a m : ℕ) (hm : a ≤ m) :
    fib (↑a) * fib (↑m + 1) - fib (↑a + 1) * fib (↑m)
      = (-1 : ℤ) ^ (a + 1) * fib (↑(m - a)) := by
  have hsum : (↑a : ℤ) + ↑(m - a) = ↑m := by omega
  have hfm : fib (↑m) = fib (↑a - 1) * fib (↑(m - a)) + fib (↑a) * fib (↑(m - a) + 1) := by
    have h := Int.fib_add (↑a : ℤ) (↑(m - a))
    rw [hsum] at h
    exact h
  have hfm1 : fib (↑m + 1) = fib (↑a) * fib (↑(m - a)) + fib (↑a + 1) * fib (↑(m - a) + 1) := by
    have h := Int.fib_add (↑a + 1 : ℤ) (↑(m - a))
    have hc : ((↑a : ℤ) + 1) - 1 = ↑a := by ring
    have hsum1 : ((↑a : ℤ) + 1) + ↑(m - a) = ↑m + 1 := by omega
    rw [hsum1] at h
    rw [hc] at h
    exact h
  have hcass := fib_cassini_bracket a
  rw [hfm1, hfm]
  have hcancel :
      fib (↑a) * (fib (↑a) * fib (↑(m - a)) + fib (↑a + 1) * fib (↑(m - a) + 1))
        - fib (↑a + 1) * (fib (↑a - 1) * fib (↑(m - a)) + fib (↑a) * fib (↑(m - a) + 1))
      = fib (↑(m - a)) * (fib (↑a) ^ 2 - fib (↑a + 1) * fib (↑a - 1)) := by
          ring
  rw [hcancel]
  rw [hcass]
  ring

/-- E_2 sign law, s = 1 (the q = 2 four-point closure):
    E_2(a,m) = F(a+1)F(m+2) - F(a+2)F(m+1) = (-1)^a F(m-a)  for a ≤ m. -/
theorem E2_s1_closed (a m : ℕ) (hm : a ≤ m) :
    fib (↑a + 1) * fib (↑m + 2) - fib (↑a + 2) * fib (↑m + 1)
      = (-1 : ℤ) ^ a * fib (↑(m - a)) := by
  have hc := dOcagne_closed (a + 1) (m + 1) (by omega)
  -- 目标左侧与 hc 左侧 cast 对齐
  have hleft_eq : fib (↑a + 1) * fib (↑m + 2) - fib (↑a + 2) * fib (↑m + 1)
                = fib (↑(a + 1)) * fib (↑(m + 1) + 1) - fib (↑(a + 1) + 1) * fib (↑(m + 1)) := by
    push_cast
    ring
  rw [hleft_eq]
  rw [hc]
  have hpow : (-1 : ℤ) ^ ((a + 1) + 1) = (-1 : ℤ) ^ a := by
    rw [pow_succ]
    ring
  have hind_nat : (m + 1) - (a + 1) = m - a := by omega
  rw [hpow, hind_nat]

end E2S1
