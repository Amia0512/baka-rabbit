import Mathlib.Data.Nat.Basic

/-
目标：证明 2×k 长条区域的骨牌平铺数 = fib(k+1)。
-/

def fib : Nat -> Nat
  | 0 => 0
  | 1 => 1
  | n + 2 => fib (n + 1) + fib n

def T : Nat -> Nat
  | 0 => 1
  | 1 => 1
  | k + 2 => T (k + 1) + T k

-- 核心定理：T(k) = fib(k+1)（强归纳）
theorem T_eq_fib_succ (k : Nat) : T k = fib (k + 1) := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
      cases k with
      | zero => simp [T, fib]
      | succ m =>
          cases m with
          | zero => simp [T, fib]
          | succ n =>
              have h1 : T (n + 1) = fib (n + 2) := ih (n + 1) (by omega)
              have h2 : T n = fib (n + 1) := ih n (by omega)
              rw [T]
              rw [h1, h2]
              simp [fib]

example : T 7 = 21 := by native_decide
#eval T 10