import Mathlib

set_option maxHeartbeats 0
set_option linter.unusedVariables false

/-!
# q=6 quadrangle sequence  D_n = e_n * e_{n+1} - o_n^2

Even/odd sub-series T_6(2n), T_6(2n+1).
* e6: order-7 palindromic recursion (verified).
* o6: order-6 palindrome recursion (verified).
* bridge: 377 * o6(n) = -257 e6(n) + 5201 e6(n+1) - 14637 e6(n+2) + 13879 e6(n+3)
                        - 4616 e6(n+4) + 441 e6(n+5) - 11 e6(n+6)
  proved via B(n) := 377 o6(n) - bridgeRHS(n), which satisfies the same order-7
  recursion as the e-span and has zero initial values (strong induction).
-/

namespace Q6D

/-- Even sub-series T_6(2n). -/
def e6 : Nat -> Int
  | 0 => 1
  | 1 => 13
  | 2 => 281
  | 3 => 6728
  | 4 => 167089
  | 5 => 4213133
  | 6 => 106912793
  | n + 7 => 40 * e6 (n + 6) - 416 * e6 (n + 5) + 1224 * e6 (n + 4)
             - 1224 * e6 (n + 3) + 416 * e6 (n + 2) - 40 * e6 (n + 1) + e6 n

/-- Odd sub-series T_6(2n+1). -/
def o6 : Nat -> Int
  | 0 => 1
  | 1 => 41
  | 2 => 1183
  | 3 => 31529
  | 4 => 817991
  | 5 => 21001799
  | n + 6 => 39 * o6 (n + 5) - 377 * o6 (n + 4) + 847 * o6 (n + 3)
             - 377 * o6 (n + 2) + 39 * o6 (n + 1) - o6 n

/-- Bridge remainder:  B(n) = 377 o6(n) - bridge RHS. -/
def B (n : Nat) : Int :=
  377 * o6 n - (-257 * e6 n + 5201 * e6 (n + 1) - 14637 * e6 (n + 2)
                + 13879 * e6 (n + 3) - 4616 * e6 (n + 4) + 441 * e6 (n + 5)
                - 11 * e6 (n + 6))

/-- Quadrangle sequence  D_n = e_n * e_{n+1} - o_n^2. -/
def D (n : Nat) : Int := e6 n * e6 (n + 1) - o6 n * o6 n

theorem e6_s7 (n : Nat) :
    e6 (n + 7) = 40 * e6 (n + 6) - 416 * e6 (n + 5) + 1224 * e6 (n + 4)
                - 1224 * e6 (n + 3) + 416 * e6 (n + 2) - 40 * e6 (n + 1) + e6 n := by rfl

theorem o6_s6 (n : Nat) :
    o6 (n + 6) = 39 * o6 (n + 5) - 377 * o6 (n + 4) + 847 * o6 (n + 3)
                - 377 * o6 (n + 2) + 39 * o6 (n + 1) - o6 n := by rfl

/-- B satisfies the order-7 palindromic recursion (rings of the e/o recursions). -/
theorem B_rec (n : Nat) :
    B (n + 7) = 40 * B (n + 6) - 416 * B (n + 5) + 1224 * B (n + 4) - 1224 * B (n + 3)
                + 416 * B (n + 2) - 40 * B (n + 1) + B n := by
  unfold B
  simp only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
  simp [e6, o6]
  ring_nf

/-- Zero initial values of B. -/
theorem B_init0 : B 0 = 0 := by unfold B; norm_num [e6, o6]
theorem B_init1 : B 1 = 0 := by unfold B; norm_num [e6, o6]
theorem B_init2 : B 2 = 0 := by unfold B; norm_num [e6, o6]
theorem B_init3 : B 3 = 0 := by unfold B; norm_num [e6, o6]
theorem B_init4 : B 4 = 0 := by unfold B; norm_num [e6, o6]
theorem B_init5 : B 5 = 0 := by unfold B; norm_num [e6, o6]
theorem B_init6 : B 6 = 0 := by unfold B; norm_num [e6, o6]

/-- Linear bridge between odd and even sub-series via strong induction on B. -/
theorem o6_lin (n : Nat) :
    377 * o6 n = -257 * e6 n + 5201 * e6 (n + 1) - 14637 * e6 (n + 2)
                 + 13879 * e6 (n + 3) - 4616 * e6 (n + 4) + 441 * e6 (n + 5)
                 - 11 * e6 (n + 6) := by
  have hBz : ∀ n, B n = 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        match n with
        | 0 => exact B_init0
        | 1 => exact B_init1
        | 2 => exact B_init2
        | 3 => exact B_init3
        | 4 => exact B_init4
        | 5 => exact B_init5
        | 6 => exact B_init6
        | m + 7 =>
            have h_rec := B_rec m
            have h6 : B (m + 6) = 0 := ih (m + 6) (by omega)
            have h5 : B (m + 5) = 0 := ih (m + 5) (by omega)
            have h4 : B (m + 4) = 0 := ih (m + 4) (by omega)
            have h3 : B (m + 3) = 0 := ih (m + 3) (by omega)
            have h2 : B (m + 2) = 0 := ih (m + 2) (by omega)
            have h1 : B (m + 1) = 0 := ih (m + 1) (by omega)
            have h0 : B m = 0 := ih m (by omega)
            rw [h_rec, h6, h5, h4, h3, h2, h1, h0]
            ring
  have hz := hBz n
  unfold B at hz
  omega

-- initial D values (finite checks)
example : D 0 = 12 := by native_decide
example : D 1 = 1972 := by native_decide
example : D 2 = 491079 := by native_decide
