import Mathlib

set_option maxHeartbeats 0
set_option linter.unusedVariables false

/-!
# q=6 quadrangle sequence  D_n = e_n * e_{n+1} - o_n^2

Order-13 palindromic recursion for D:
D(n+13) = 375 D(n+12) - 31905 D(n+11) + 940863 D(n+10) - 11023137 D(n+9)
        + 55190391 D(n+8) - 123722817 D(n+7) + 123722817 D(n+6)
        - 55190391 D(n+5) + 11023137 D(n+4) - 940863 D(n+3)
        + 31905 D(n+2) - 375 D(n+1) + D n
Proved by multiplying with 377^2, eliminating o via the o6_lin bridge,
normalizing indices, folding v19..v7 via he, then ring.
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

/-- Quadrangle sequence  D_n = e_n * e_{n+1} - o_n^2. -/
def D (n : Nat) : Int := e6 n * e6 (n + 1) - o6 n * o6 n

theorem e6_s7 (n : Nat) :
    e6 (n + 7) = 40 * e6 (n + 6) - 416 * e6 (n + 5) + 1224 * e6 (n + 4)
                - 1224 * e6 (n + 3) + 416 * e6 (n + 2) - 40 * e6 (n + 1) + e6 n := by rfl

/-- Bridge remainder:  B(n) = 377 o6(n) - bridge RHS. -/
def B (n : Nat) : Int :=
  377 * o6 n - (-257 * e6 n + 5201 * e6 (n + 1) - 14637 * e6 (n + 2)
                + 13879 * e6 (n + 3) - 4616 * e6 (n + 4) + 441 * e6 (n + 5)
                - 11 * e6 (n + 6))

theorem B_rec (n : Nat) :
    B (n + 7) = 40 * B (n + 6) - 416 * B (n + 5) + 1224 * B (n + 4) - 1224 * B (n + 3)
                + 416 * B (n + 2) - 40 * B (n + 1) + B n := by
  unfold B
  simp only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
  simp [e6, o6]
  ring_nf

theorem B_init0 : B 0 = 0 := by unfold B; norm_num [e6, o6]
theorem B_init1 : B 1 = 0 := by unfold B; norm_num [e6, o6]
theorem B_init2 : B 2 = 0 := by unfold B; norm_num [e6, o6]
theorem B_init3 : B 3 = 0 := by unfold B; norm_num [e6, o6]
theorem B_init4 : B 4 = 0 := by unfold B; norm_num [e6, o6]
theorem B_init5 : B 5 = 0 := by unfold B; norm_num [e6, o6]
theorem B_init6 : B 6 = 0 := by unfold B; norm_num [e6, o6]

/-- Linear bridge between odd and even sub-series. -/
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

/-- e6 recursion with normalized indices n + j. -/
theorem he7 (n : Nat) :
    e6 (n + 7) = 40 * e6 (n + 6) - 416 * e6 (n + 5) + 1224 * e6 (n + 4)
                  - 1224 * e6 (n + 3) + 416 * e6 (n + 2) - 40 * e6 (n + 1)
                  + e6 n := by
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, Nat.add_zero] using e6_s7 (n + 0)

theorem he8 (n : Nat) :
    e6 (n + 8) = 40 * e6 (n + 7) - 416 * e6 (n + 6) + 1224 * e6 (n + 5)
                  - 1224 * e6 (n + 4) + 416 * e6 (n + 3) - 40 * e6 (n + 2)
                  + e6 (n + 1) := by
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, Nat.add_zero] using e6_s7 (n + 1)

theorem he9 (n : Nat) :
    e6 (n + 9) = 40 * e6 (n + 8) - 416 * e6 (n + 7) + 1224 * e6 (n + 6)
                  - 1224 * e6 (n + 5) + 416 * e6 (n + 4) - 40 * e6 (n + 3)
                  + e6 (n + 2) := by
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, Nat.add_zero] using e6_s7 (n + 2)

theorem he10 (n : Nat) :
    e6 (n + 10) = 40 * e6 (n + 9) - 416 * e6 (n + 8) + 1224 * e6 (n + 7)
                  - 1224 * e6 (n + 6) + 416 * e6 (n + 5) - 40 * e6 (n + 4)
                  + e6 (n + 3) := by
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, Nat.add_zero] using e6_s7 (n + 3)

theorem he11 (n : Nat) :
    e6 (n + 11) = 40 * e6 (n + 10) - 416 * e6 (n + 9) + 1224 * e6 (n + 8)
                  - 1224 * e6 (n + 7) + 416 * e6 (n + 6) - 40 * e6 (n + 5)
                  + e6 (n + 4) := by
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, Nat.add_zero] using e6_s7 (n + 4)

theorem he12 (n : Nat) :
    e6 (n + 12) = 40 * e6 (n + 11) - 416 * e6 (n + 10) + 1224 * e6 (n + 9)
                  - 1224 * e6 (n + 8) + 416 * e6 (n + 7) - 40 * e6 (n + 6)
                  + e6 (n + 5) := by
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, Nat.add_zero] using e6_s7 (n + 5)

theorem he13 (n : Nat) :
    e6 (n + 13) = 40 * e6 (n + 12) - 416 * e6 (n + 11) + 1224 * e6 (n + 10)
                  - 1224 * e6 (n + 9) + 416 * e6 (n + 8) - 40 * e6 (n + 7)
                  + e6 (n + 6) := by
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, Nat.add_zero] using e6_s7 (n + 6)

theorem he14 (n : Nat) :
    e6 (n + 14) = 40 * e6 (n + 13) - 416 * e6 (n + 12) + 1224 * e6 (n + 11)
                  - 1224 * e6 (n + 10) + 416 * e6 (n + 9) - 40 * e6 (n + 8)
                  + e6 (n + 7) := by
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, Nat.add_zero] using e6_s7 (n + 7)

theorem he15 (n : Nat) :
    e6 (n + 15) = 40 * e6 (n + 14) - 416 * e6 (n + 13) + 1224 * e6 (n + 12)
                  - 1224 * e6 (n + 11) + 416 * e6 (n + 10) - 40 * e6 (n + 9)
                  + e6 (n + 8) := by
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, Nat.add_zero] using e6_s7 (n + 8)

theorem he16 (n : Nat) :
    e6 (n + 16) = 40 * e6 (n + 15) - 416 * e6 (n + 14) + 1224 * e6 (n + 13)
                  - 1224 * e6 (n + 12) + 416 * e6 (n + 11) - 40 * e6 (n + 10)
                  + e6 (n + 9) := by
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, Nat.add_zero] using e6_s7 (n + 9)

theorem he17 (n : Nat) :
    e6 (n + 17) = 40 * e6 (n + 16) - 416 * e6 (n + 15) + 1224 * e6 (n + 14)
                  - 1224 * e6 (n + 13) + 416 * e6 (n + 12) - 40 * e6 (n + 11)
                  + e6 (n + 10) := by
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, Nat.add_zero] using e6_s7 (n + 10)

theorem he18 (n : Nat) :
    e6 (n + 18) = 40 * e6 (n + 17) - 416 * e6 (n + 16) + 1224 * e6 (n + 15)
                  - 1224 * e6 (n + 14) + 416 * e6 (n + 13) - 40 * e6 (n + 12)
                  + e6 (n + 11) := by
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, Nat.add_zero] using e6_s7 (n + 11)

theorem he19 (n : Nat) :
    e6 (n + 19) = 40 * e6 (n + 18) - 416 * e6 (n + 17) + 1224 * e6 (n + 16)
                  - 1224 * e6 (n + 15) + 416 * e6 (n + 14) - 40 * e6 (n + 13)
                  + e6 (n + 12) := by
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, Nat.add_zero] using e6_s7 (n + 12)

-- initial D values (finite check)
example : D 0 = 12 := by native_decide
example : D 1 = 1972 := by native_decide
example : D 2 = 491079 := by native_decide

/-- Order-13 palindromic recursion for D (generated proof). -/
theorem D_recur_13 (n : Nat) :
    D (n + 13) = 375 * D (n + 12) - 31905 * D (n + 11) + 940863 * D (n + 10)
      - 11023137 * D (n + 9) + 55190391 * D (n + 8) - 123722817 * D (n + 7)
      + 123722817 * D (n + 6) - 55190391 * D (n + 5) + 11023137 * D (n + 4)
      - 940863 * D (n + 3) + 31905 * D (n + 2) - 375 * D (n + 1) + D n := by
  have h142 : (142129 : Int) * D (n + 13) =
      (142129 : Int) * (375 * D (n + 12) - 31905 * D (n + 11) + 940863 * D (n + 10)
        - 11023137 * D (n + 9) + 55190391 * D (n + 8) - 123722817 * D (n + 7)
        + 123722817 * D (n + 6) - 55190391 * D (n + 5) + 11023137 * D (n + 4)
        - 940863 * D (n + 3) + 31905 * D (n + 2) - 375 * D (n + 1) + D n) := by
    unfold D
    ring_nf
    rw [show o6 (13 + n) ^ 2 * (142129 : Int) = (377 * o6 (13 + n)) ^ 2 by ring]
    rw [show o6 (12 + n) ^ 2 * (53298375 : Int) = (375 * (377 * o6 (12 + n)) ^ 2) by ring]
    rw [show o6 (11 + n) ^ 2 * (4534625745 : Int) = (31905 * (377 * o6 (11 + n)) ^ 2) by ring]
    rw [show o6 (10 + n) ^ 2 * (133723917327 : Int) = (940863 * (377 * o6 (10 + n)) ^ 2) by ring]
    rw [show o6 (9 + n) ^ 2 * (1566707438673 : Int) = (11023137 * (377 * o6 (9 + n)) ^ 2) by ring]
    rw [show o6 (8 + n) ^ 2 * (7844155082439 : Int) = (55190391 * (377 * o6 (8 + n)) ^ 2) by ring]
    rw [show o6 (7 + n) ^ 2 * (17584600257393 : Int) = (123722817 * (377 * o6 (7 + n)) ^ 2) by ring]
    rw [show o6 (6 + n) ^ 2 * (17584600257393 : Int) = (123722817 * (377 * o6 (6 + n)) ^ 2) by ring]
    rw [show o6 (5 + n) ^ 2 * (7844155082439 : Int) = (55190391 * (377 * o6 (5 + n)) ^ 2) by ring]
    rw [show o6 (4 + n) ^ 2 * (1566707438673 : Int) = (11023137 * (377 * o6 (4 + n)) ^ 2) by ring]
    rw [show o6 (3 + n) ^ 2 * (133723917327 : Int) = (940863 * (377 * o6 (3 + n)) ^ 2) by ring]
    rw [show o6 (2 + n) ^ 2 * (4534625745 : Int) = (31905 * (377 * o6 (2 + n)) ^ 2) by ring]
    rw [show o6 (1 + n) ^ 2 * (53298375 : Int) = (375 * (377 * o6 (1 + n)) ^ 2) by ring]
    rw [show o6 (n) ^ 2 * (142129 : Int) = (377 * o6 (n)) ^ 2 by ring]

    -- normalize k + n to n + k
    have hs1 : 1 + n = n + 1 := by omega
    have hs2 : 2 + n = n + 2 := by omega
    have hs3 : 3 + n = n + 3 := by omega
    have hs4 : 4 + n = n + 4 := by omega
    have hs5 : 5 + n = n + 5 := by omega
    have hs6 : 6 + n = n + 6 := by omega
    have hs7 : 7 + n = n + 7 := by omega
    have hs8 : 8 + n = n + 8 := by omega
    have hs9 : 9 + n = n + 9 := by omega
    have hs10 : 10 + n = n + 10 := by omega
    have hs11 : 11 + n = n + 11 := by omega
    have hs12 : 12 + n = n + 12 := by omega
    have hs13 : 13 + n = n + 13 := by omega
    rw [hs13, hs12, hs11, hs10, hs9, hs8, hs7, hs6, hs5, hs4, hs3, hs2, hs1]

    -- bridge: eliminate all o terms via o6_lin (small indices first)
    rw [o6_lin n, o6_lin (n + 1), o6_lin (n + 2), o6_lin (n + 3), o6_lin (n + 4), o6_lin (n + 5), o6_lin (n + 6), o6_lin (n + 7), o6_lin (n + 8), o6_lin (n + 9), o6_lin (n + 10), o6_lin (n + 11), o6_lin (n + 12), o6_lin (n + 13)]

    -- normalize every index to n + j (variable first, digits evaluated)
    simp only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, Nat.add_zero]
    norm_num

    -- local variables v_j := e6 (n + j)
    set v0 : Int := e6 n
    set v1 : Int := e6 (n + 1)
    set v2 : Int := e6 (n + 2)
    set v3 : Int := e6 (n + 3)
    set v4 : Int := e6 (n + 4)
    set v5 : Int := e6 (n + 5)
    set v6 : Int := e6 (n + 6)
    set v7 : Int := e6 (n + 7)
    set v8 : Int := e6 (n + 8)
    set v9 : Int := e6 (n + 9)
    set v10 : Int := e6 (n + 10)
    set v11 : Int := e6 (n + 11)
    set v12 : Int := e6 (n + 12)
    set v13 : Int := e6 (n + 13)
    set v14 : Int := e6 (n + 14)
    set v15 : Int := e6 (n + 15)
    set v16 : Int := e6 (n + 16)
    set v17 : Int := e6 (n + 17)
    set v18 : Int := e6 (n + 18)
    set v19 : Int := e6 (n + 19)

    -- fold v19..v7 down to v0..v6 via the recursion
    have h19 : v19 = 40 * v18 - 416 * v17 + 1224 * v16 - 1224 * v15
        + 416 * v14 - 40 * v13 + v12 := by
      dsimp [v19, v18, v17, v16, v15, v14, v13, v12]
      simpa [Nat.add_zero] using he19 n
    have h18 : v18 = 40 * v17 - 416 * v16 + 1224 * v15 - 1224 * v14
        + 416 * v13 - 40 * v12 + v11 := by
      dsimp [v18, v17, v16, v15, v14, v13, v12, v11]
      simpa [Nat.add_zero] using he18 n
    have h17 : v17 = 40 * v16 - 416 * v15 + 1224 * v14 - 1224 * v13
        + 416 * v12 - 40 * v11 + v10 := by
      dsimp [v17, v16, v15, v14, v13, v12, v11, v10]
      simpa [Nat.add_zero] using he17 n
    have h16 : v16 = 40 * v15 - 416 * v14 + 1224 * v13 - 1224 * v12
        + 416 * v11 - 40 * v10 + v9 := by
      dsimp [v16, v15, v14, v13, v12, v11, v10, v9]
      simpa [Nat.add_zero] using he16 n
    have h15 : v15 = 40 * v14 - 416 * v13 + 1224 * v12 - 1224 * v11
        + 416 * v10 - 40 * v9 + v8 := by
      dsimp [v15, v14, v13, v12, v11, v10, v9, v8]
      simpa [Nat.add_zero] using he15 n
    have h14 : v14 = 40 * v13 - 416 * v12 + 1224 * v11 - 1224 * v10
        + 416 * v9 - 40 * v8 + v7 := by
      dsimp [v14, v13, v12, v11, v10, v9, v8, v7]
      simpa [Nat.add_zero] using he14 n
    have h13 : v13 = 40 * v12 - 416 * v11 + 1224 * v10 - 1224 * v9
        + 416 * v8 - 40 * v7 + v6 := by
      dsimp [v13, v12, v11, v10, v9, v8, v7, v6]
      simpa [Nat.add_zero] using he13 n
    have h12 : v12 = 40 * v11 - 416 * v10 + 1224 * v9 - 1224 * v8
        + 416 * v7 - 40 * v6 + v5 := by
      dsimp [v12, v11, v10, v9, v8, v7, v6, v5]
      simpa [Nat.add_zero] using he12 n
    have h11 : v11 = 40 * v10 - 416 * v9 + 1224 * v8 - 1224 * v7
        + 416 * v6 - 40 * v5 + v4 := by
      dsimp [v11, v10, v9, v8, v7, v6, v5, v4]
      simpa [Nat.add_zero] using he11 n
    have h10 : v10 = 40 * v9 - 416 * v8 + 1224 * v7 - 1224 * v6
        + 416 * v5 - 40 * v4 + v3 := by
      dsimp [v10, v9, v8, v7, v6, v5, v4, v3]
      simpa [Nat.add_zero] using he10 n
    have h9 : v9 = 40 * v8 - 416 * v7 + 1224 * v6 - 1224 * v5
        + 416 * v4 - 40 * v3 + v2 := by
      dsimp [v9, v8, v7, v6, v5, v4, v3, v2]
      simpa [Nat.add_zero] using he9 n
    have h8 : v8 = 40 * v7 - 416 * v6 + 1224 * v5 - 1224 * v4
        + 416 * v3 - 40 * v2 + v1 := by
      dsimp [v8, v7, v6, v5, v4, v3, v2, v1]
      simpa [Nat.add_zero] using he8 n
    have h7 : v7 = 40 * v6 - 416 * v5 + 1224 * v4 - 1224 * v3
        + 416 * v2 - 40 * v1 + v0 := by
      dsimp [v7, v6, v5, v4, v3, v2, v1, v0]
      simpa [Nat.add_zero] using he7 n
    rw [h19, h18, h17, h16, h15, h14, h13, h12, h11, h10, h9, h8, h7]
    ring
  exact Int.eq_of_mul_eq_mul_left (show (142129 : Int) ≠ 0 by norm_num) h142

end Q6D

#print axioms Q6D.D_recur_13

