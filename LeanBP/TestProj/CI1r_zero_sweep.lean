import Mathlib.Data.Nat.Basic
import Mathlib.Data.Int.Basic
import Mathlib.Data.List.Basic

set_option maxHeartbeats 0
set_option linter.unusedVariables false

/-!
# q = 1: CI(1,r) ≥ 0 — machine-verified same-sign structure (s > 0)

Theorem 3.2c (corrected 2026-08-24): the SYM identity gives
CI(1,r) = ½·Σ_P Δ_1(P)·Δ_r(P).  Numerically Δ_1(P) and Δ_r(P) have the
same sign for every P ⊆ [s,w) and every r ≥ 1 (Δ_1·Δ_r ≥ 0 termwise), so
CI(1,r) ≥ 0.  This file machine-checks the termwise same-sign inequality
on finite concrete instances with native_decide; the parametric statement
is Theorem 3.2c in the paper.  s < 0 reduces to s > 0 by the mirror
isomorphism preserving tiling counts.
-/

abbrev Cell := Int × Int

def adj (a b : Cell) : Bool :=
  (a.1 + 1 = b.1 && a.2 = b.2) || (a.1 = b.1 + 1 && a.2 = b.2) ||
  (a.1 = b.1 && a.2 + 1 = b.2) || (a.1 = b.1 && a.2 = b.2 + 1)

partial def tilingCount (all : List Cell) (state : List Cell) (acc : Nat) : Nat :=
  if all.all (fun x => state.contains x) then acc + 1
  else
    match all.find? (fun x => !state.contains x) with
    | none => acc
    | some first =>
        (all.filter (fun v => v != first && !state.contains v && adj first v)).foldl
          (fun a v => tilingCount all (state ++ [first, v]) a) acc

def tilings (s : List Cell) : Nat := tilingCount s [] 0

-- full h x w board (rows 0..h-1, cols 0..w-1)
def rectCells (h w : Nat) : List Cell :=
  (List.range h).flatMap (fun i => (List.range w).map (fun j => ((i : Int), (j : Int))))

-- board with the columns of `removed` deleted
def delCols (h w : Nat) (removed : List Int) : List Cell :=
  ((rectCells h w).filter (fun c => !removed.contains c.2))

-- Rov reflection on a width-w board with shift s: R(c) = w-1+s-c
def rov (w : Nat) (s : Int) (c : Int) : Int :=
  ((w : Int) - 1 + s) - c

-- u_h(P): tiling count of h x w board after deleting P
def u (h w : Nat) (P : List Int) : Nat := tilings (delCols h w P)

-- Δ_h(P) := u_h(P) - u_h(R(P))  (Nat subtraction in Lean; same-sign via product sign)
-- We verify: not ((Δ_1 < Δ_1_target) etc.) -- instead verify the boolean:
-- sign-compare via (u1(P) < u1(RP)) == (u_r(P) < u_r(RP)) ??  simpler: verify
-- Δ_1 != 0 -> (Δ_1 > 0) == (Δ_r > 0) is equivalent to (Δ_1*Δ_r >= 0) for Int.
-- Use Int to allow negative deltas:
def intSub (a b : Nat) : Int := (a : Int) - (b : Int)

-- w=2, s=1, P={1}, R(P)={1}
example : (intSub (u 1 2 ([1] : List Int)) (u 1 2 ([1] : List Int)) = 0)
          ∨ ((intSub (u 1 2 ([1] : List Int)) (u 1 2 ([1] : List Int)) > 0) ↔
             (intSub (u 1 2 ([1] : List Int)) (u 1 2 ([1] : List Int)) > 0)) := by
  native_decide

example : (intSub (u 1 2 ([1] : List Int)) (u 1 2 ([1] : List Int)) = 0)
          ∨ ((intSub (u 1 2 ([1] : List Int)) (u 1 2 ([1] : List Int)) > 0) ↔
             (intSub (u 2 2 ([1] : List Int)) (u 2 2 ([1] : List Int)) > 0)) := by
  native_decide

example : (intSub (u 1 2 ([1] : List Int)) (u 1 2 ([1] : List Int)) = 0)
          ∨ ((intSub (u 1 2 ([1] : List Int)) (u 1 2 ([1] : List Int)) > 0) ↔
             (intSub (u 3 2 ([1] : List Int)) (u 3 2 ([1] : List Int)) > 0)) := by
  native_decide

-- w=3, s=1, P={1}, R(P)={2}
example : (intSub (u 1 3 ([1] : List Int)) (u 1 3 ([2] : List Int)) = 0)
          ∨ ((intSub (u 1 3 ([1] : List Int)) (u 1 3 ([2] : List Int)) > 0) ↔
             (intSub (u 1 3 ([1] : List Int)) (u 1 3 ([2] : List Int)) > 0)) := by
  native_decide

example : (intSub (u 1 3 ([1] : List Int)) (u 1 3 ([2] : List Int)) = 0)
          ∨ ((intSub (u 1 3 ([1] : List Int)) (u 1 3 ([2] : List Int)) > 0) ↔
             (intSub (u 2 3 ([1] : List Int)) (u 2 3 ([2] : List Int)) > 0)) := by
  native_decide

example : (intSub (u 1 3 ([1] : List Int)) (u 1 3 ([2] : List Int)) = 0)
          ∨ ((intSub (u 1 3 ([1] : List Int)) (u 1 3 ([2] : List Int)) > 0) ↔
             (intSub (u 3 3 ([1] : List Int)) (u 3 3 ([2] : List Int)) > 0)) := by
  native_decide

-- w=3, s=1, P={2}, R(P)={1}
example : (intSub (u 1 3 ([2] : List Int)) (u 1 3 ([1] : List Int)) = 0)
          ∨ ((intSub (u 1 3 ([2] : List Int)) (u 1 3 ([1] : List Int)) > 0) ↔
             (intSub (u 1 3 ([2] : List Int)) (u 1 3 ([1] : List Int)) > 0)) := by
  native_decide

example : (intSub (u 1 3 ([2] : List Int)) (u 1 3 ([1] : List Int)) = 0)
          ∨ ((intSub (u 1 3 ([2] : List Int)) (u 1 3 ([1] : List Int)) > 0) ↔
             (intSub (u 2 3 ([2] : List Int)) (u 2 3 ([1] : List Int)) > 0)) := by
  native_decide

example : (intSub (u 1 3 ([2] : List Int)) (u 1 3 ([1] : List Int)) = 0)
          ∨ ((intSub (u 1 3 ([2] : List Int)) (u 1 3 ([1] : List Int)) > 0) ↔
             (intSub (u 3 3 ([2] : List Int)) (u 3 3 ([1] : List Int)) > 0)) := by
  native_decide

-- w=3, s=1, P={1, 2}, R(P)={2, 1}
example : (intSub (u 1 3 ([1, 2] : List Int)) (u 1 3 ([2, 1] : List Int)) = 0)
          ∨ ((intSub (u 1 3 ([1, 2] : List Int)) (u 1 3 ([2, 1] : List Int)) > 0) ↔
             (intSub (u 1 3 ([1, 2] : List Int)) (u 1 3 ([2, 1] : List Int)) > 0)) := by
  native_decide

example : (intSub (u 1 3 ([1, 2] : List Int)) (u 1 3 ([2, 1] : List Int)) = 0)
          ∨ ((intSub (u 1 3 ([1, 2] : List Int)) (u 1 3 ([2, 1] : List Int)) > 0) ↔
             (intSub (u 2 3 ([1, 2] : List Int)) (u 2 3 ([2, 1] : List Int)) > 0)) := by
  native_decide

example : (intSub (u 1 3 ([1, 2] : List Int)) (u 1 3 ([2, 1] : List Int)) = 0)
          ∨ ((intSub (u 1 3 ([1, 2] : List Int)) (u 1 3 ([2, 1] : List Int)) > 0) ↔
             (intSub (u 3 3 ([1, 2] : List Int)) (u 3 3 ([2, 1] : List Int)) > 0)) := by
  native_decide

-- w=3, s=2, P={2}, R(P)={2}
example : (intSub (u 1 3 ([2] : List Int)) (u 1 3 ([2] : List Int)) = 0)
          ∨ ((intSub (u 1 3 ([2] : List Int)) (u 1 3 ([2] : List Int)) > 0) ↔
             (intSub (u 1 3 ([2] : List Int)) (u 1 3 ([2] : List Int)) > 0)) := by
  native_decide

example : (intSub (u 1 3 ([2] : List Int)) (u 1 3 ([2] : List Int)) = 0)
          ∨ ((intSub (u 1 3 ([2] : List Int)) (u 1 3 ([2] : List Int)) > 0) ↔
             (intSub (u 2 3 ([2] : List Int)) (u 2 3 ([2] : List Int)) > 0)) := by
  native_decide

example : (intSub (u 1 3 ([2] : List Int)) (u 1 3 ([2] : List Int)) = 0)
          ∨ ((intSub (u 1 3 ([2] : List Int)) (u 1 3 ([2] : List Int)) > 0) ↔
             (intSub (u 3 3 ([2] : List Int)) (u 3 3 ([2] : List Int)) > 0)) := by
  native_decide

-- w=4, s=1, P={1}, R(P)={3}
example : (intSub (u 1 4 ([1] : List Int)) (u 1 4 ([3] : List Int)) = 0)
          ∨ ((intSub (u 1 4 ([1] : List Int)) (u 1 4 ([3] : List Int)) > 0) ↔
             (intSub (u 1 4 ([1] : List Int)) (u 1 4 ([3] : List Int)) > 0)) := by
  native_decide

example : (intSub (u 1 4 ([1] : List Int)) (u 1 4 ([3] : List Int)) = 0)
          ∨ ((intSub (u 1 4 ([1] : List Int)) (u 1 4 ([3] : List Int)) > 0) ↔
             (intSub (u 2 4 ([1] : List Int)) (u 2 4 ([3] : List Int)) > 0)) := by
  native_decide

example : (intSub (u 1 4 ([1] : List Int)) (u 1 4 ([3] : List Int)) = 0)
          ∨ ((intSub (u 1 4 ([1] : List Int)) (u 1 4 ([3] : List Int)) > 0) ↔
             (intSub (u 3 4 ([1] : List Int)) (u 3 4 ([3] : List Int)) > 0)) := by
  native_decide

-- w=4, s=1, P={2}, R(P)={2}
example : (intSub (u 1 4 ([2] : List Int)) (u 1 4 ([2] : List Int)) = 0)
          ∨ ((intSub (u 1 4 ([2] : List Int)) (u 1 4 ([2] : List Int)) > 0) ↔
             (intSub (u 1 4 ([2] : List Int)) (u 1 4 ([2] : List Int)) > 0)) := by
  native_decide

example : (intSub (u 1 4 ([2] : List Int)) (u 1 4 ([2] : List Int)) = 0)
          ∨ ((intSub (u 1 4 ([2] : List Int)) (u 1 4 ([2] : List Int)) > 0) ↔
             (intSub (u 2 4 ([2] : List Int)) (u 2 4 ([2] : List Int)) > 0)) := by
  native_decide

example : (intSub (u 1 4 ([2] : List Int)) (u 1 4 ([2] : List Int)) = 0)
          ∨ ((intSub (u 1 4 ([2] : List Int)) (u 1 4 ([2] : List Int)) > 0) ↔
             (intSub (u 3 4 ([2] : List Int)) (u 3 4 ([2] : List Int)) > 0)) := by
  native_decide

-- w=4, s=1, P={3}, R(P)={1}
example : (intSub (u 1 4 ([3] : List Int)) (u 1 4 ([1] : List Int)) = 0)
          ∨ ((intSub (u 1 4 ([3] : List Int)) (u 1 4 ([1] : List Int)) > 0) ↔
             (intSub (u 1 4 ([3] : List Int)) (u 1 4 ([1] : List Int)) > 0)) := by
  native_decide

example : (intSub (u 1 4 ([3] : List Int)) (u 1 4 ([1] : List Int)) = 0)
          ∨ ((intSub (u 1 4 ([3] : List Int)) (u 1 4 ([1] : List Int)) > 0) ↔
             (intSub (u 2 4 ([3] : List Int)) (u 2 4 ([1] : List Int)) > 0)) := by
  native_decide

example : (intSub (u 1 4 ([3] : List Int)) (u 1 4 ([1] : List Int)) = 0)
          ∨ ((intSub (u 1 4 ([3] : List Int)) (u 1 4 ([1] : List Int)) > 0) ↔
             (intSub (u 3 4 ([3] : List Int)) (u 3 4 ([1] : List Int)) > 0)) := by
  native_decide

-- w=4, s=1, P={1, 2}, R(P)={3, 2}
example : (intSub (u 1 4 ([1, 2] : List Int)) (u 1 4 ([3, 2] : List Int)) = 0)
          ∨ ((intSub (u 1 4 ([1, 2] : List Int)) (u 1 4 ([3, 2] : List Int)) > 0) ↔
             (intSub (u 1 4 ([1, 2] : List Int)) (u 1 4 ([3, 2] : List Int)) > 0)) := by
  native_decide

example : (intSub (u 1 4 ([1, 2] : List Int)) (u 1 4 ([3, 2] : List Int)) = 0)
          ∨ ((intSub (u 1 4 ([1, 2] : List Int)) (u 1 4 ([3, 2] : List Int)) > 0) ↔
             (intSub (u 2 4 ([1, 2] : List Int)) (u 2 4 ([3, 2] : List Int)) > 0)) := by
  native_decide

example : (intSub (u 1 4 ([1, 2] : List Int)) (u 1 4 ([3, 2] : List Int)) = 0)
          ∨ ((intSub (u 1 4 ([1, 2] : List Int)) (u 1 4 ([3, 2] : List Int)) > 0) ↔
             (intSub (u 3 4 ([1, 2] : List Int)) (u 3 4 ([3, 2] : List Int)) > 0)) := by
  native_decide

-- w=4, s=1, P={1, 3}, R(P)={3, 1}
example : (intSub (u 1 4 ([1, 3] : List Int)) (u 1 4 ([3, 1] : List Int)) = 0)
          ∨ ((intSub (u 1 4 ([1, 3] : List Int)) (u 1 4 ([3, 1] : List Int)) > 0) ↔
             (intSub (u 1 4 ([1, 3] : List Int)) (u 1 4 ([3, 1] : List Int)) > 0)) := by
  native_decide

example : (intSub (u 1 4 ([1, 3] : List Int)) (u 1 4 ([3, 1] : List Int)) = 0)
          ∨ ((intSub (u 1 4 ([1, 3] : List Int)) (u 1 4 ([3, 1] : List Int)) > 0) ↔
             (intSub (u 2 4 ([1, 3] : List Int)) (u 2 4 ([3, 1] : List Int)) > 0)) := by
  native_decide

example : (intSub (u 1 4 ([1, 3] : List Int)) (u 1 4 ([3, 1] : List Int)) = 0)
          ∨ ((intSub (u 1 4 ([1, 3] : List Int)) (u 1 4 ([3, 1] : List Int)) > 0) ↔
             (intSub (u 3 4 ([1, 3] : List Int)) (u 3 4 ([3, 1] : List Int)) > 0)) := by
  native_decide

-- w=4, s=1, P={2, 3}, R(P)={2, 1}
example : (intSub (u 1 4 ([2, 3] : List Int)) (u 1 4 ([2, 1] : List Int)) = 0)
          ∨ ((intSub (u 1 4 ([2, 3] : List Int)) (u 1 4 ([2, 1] : List Int)) > 0) ↔
             (intSub (u 1 4 ([2, 3] : List Int)) (u 1 4 ([2, 1] : List Int)) > 0)) := by
  native_decide

example : (intSub (u 1 4 ([2, 3] : List Int)) (u 1 4 ([2, 1] : List Int)) = 0)
          ∨ ((intSub (u 1 4 ([2, 3] : List Int)) (u 1 4 ([2, 1] : List Int)) > 0) ↔
             (intSub (u 2 4 ([2, 3] : List Int)) (u 2 4 ([2, 1] : List Int)) > 0)) := by
  native_decide

example : (intSub (u 1 4 ([2, 3] : List Int)) (u 1 4 ([2, 1] : List Int)) = 0)
          ∨ ((intSub (u 1 4 ([2, 3] : List Int)) (u 1 4 ([2, 1] : List Int)) > 0) ↔
             (intSub (u 3 4 ([2, 3] : List Int)) (u 3 4 ([2, 1] : List Int)) > 0)) := by
  native_decide

-- w=4, s=1, P={1, 2, 3}, R(P)={3, 2, 1}
example : (intSub (u 1 4 ([1, 2, 3] : List Int)) (u 1 4 ([3, 2, 1] : List Int)) = 0)
          ∨ ((intSub (u 1 4 ([1, 2, 3] : List Int)) (u 1 4 ([3, 2, 1] : List Int)) > 0) ↔
             (intSub (u 1 4 ([1, 2, 3] : List Int)) (u 1 4 ([3, 2, 1] : List Int)) > 0)) := by
  native_decide

example : (intSub (u 1 4 ([1, 2, 3] : List Int)) (u 1 4 ([3, 2, 1] : List Int)) = 0)
          ∨ ((intSub (u 1 4 ([1, 2, 3] : List Int)) (u 1 4 ([3, 2, 1] : List Int)) > 0) ↔
             (intSub (u 2 4 ([1, 2, 3] : List Int)) (u 2 4 ([3, 2, 1] : List Int)) > 0)) := by
  native_decide

example : (intSub (u 1 4 ([1, 2, 3] : List Int)) (u 1 4 ([3, 2, 1] : List Int)) = 0)
          ∨ ((intSub (u 1 4 ([1, 2, 3] : List Int)) (u 1 4 ([3, 2, 1] : List Int)) > 0) ↔
             (intSub (u 3 4 ([1, 2, 3] : List Int)) (u 3 4 ([3, 2, 1] : List Int)) > 0)) := by
  native_decide

-- w=4, s=2, P={2}, R(P)={3}
example : (intSub (u 1 4 ([2] : List Int)) (u 1 4 ([3] : List Int)) = 0)
          ∨ ((intSub (u 1 4 ([2] : List Int)) (u 1 4 ([3] : List Int)) > 0) ↔
             (intSub (u 1 4 ([2] : List Int)) (u 1 4 ([3] : List Int)) > 0)) := by
  native_decide

example : (intSub (u 1 4 ([2] : List Int)) (u 1 4 ([3] : List Int)) = 0)
          ∨ ((intSub (u 1 4 ([2] : List Int)) (u 1 4 ([3] : List Int)) > 0) ↔
             (intSub (u 2 4 ([2] : List Int)) (u 2 4 ([3] : List Int)) > 0)) := by
  native_decide

example : (intSub (u 1 4 ([2] : List Int)) (u 1 4 ([3] : List Int)) = 0)
          ∨ ((intSub (u 1 4 ([2] : List Int)) (u 1 4 ([3] : List Int)) > 0) ↔
             (intSub (u 3 4 ([2] : List Int)) (u 3 4 ([3] : List Int)) > 0)) := by
  native_decide

-- w=4, s=2, P={3}, R(P)={2}
example : (intSub (u 1 4 ([3] : List Int)) (u 1 4 ([2] : List Int)) = 0)
          ∨ ((intSub (u 1 4 ([3] : List Int)) (u 1 4 ([2] : List Int)) > 0) ↔
             (intSub (u 1 4 ([3] : List Int)) (u 1 4 ([2] : List Int)) > 0)) := by
  native_decide

example : (intSub (u 1 4 ([3] : List Int)) (u 1 4 ([2] : List Int)) = 0)
          ∨ ((intSub (u 1 4 ([3] : List Int)) (u 1 4 ([2] : List Int)) > 0) ↔
             (intSub (u 2 4 ([3] : List Int)) (u 2 4 ([2] : List Int)) > 0)) := by
  native_decide

example : (intSub (u 1 4 ([3] : List Int)) (u 1 4 ([2] : List Int)) = 0)
          ∨ ((intSub (u 1 4 ([3] : List Int)) (u 1 4 ([2] : List Int)) > 0) ↔
             (intSub (u 3 4 ([3] : List Int)) (u 3 4 ([2] : List Int)) > 0)) := by
  native_decide

-- w=4, s=2, P={2, 3}, R(P)={3, 2}
example : (intSub (u 1 4 ([2, 3] : List Int)) (u 1 4 ([3, 2] : List Int)) = 0)
          ∨ ((intSub (u 1 4 ([2, 3] : List Int)) (u 1 4 ([3, 2] : List Int)) > 0) ↔
             (intSub (u 1 4 ([2, 3] : List Int)) (u 1 4 ([3, 2] : List Int)) > 0)) := by
  native_decide

example : (intSub (u 1 4 ([2, 3] : List Int)) (u 1 4 ([3, 2] : List Int)) = 0)
          ∨ ((intSub (u 1 4 ([2, 3] : List Int)) (u 1 4 ([3, 2] : List Int)) > 0) ↔
             (intSub (u 2 4 ([2, 3] : List Int)) (u 2 4 ([3, 2] : List Int)) > 0)) := by
  native_decide

example : (intSub (u 1 4 ([2, 3] : List Int)) (u 1 4 ([3, 2] : List Int)) = 0)
          ∨ ((intSub (u 1 4 ([2, 3] : List Int)) (u 1 4 ([3, 2] : List Int)) > 0) ↔
             (intSub (u 3 4 ([2, 3] : List Int)) (u 3 4 ([3, 2] : List Int)) > 0)) := by
  native_decide

-- w=4, s=3, P={3}, R(P)={3}
example : (intSub (u 1 4 ([3] : List Int)) (u 1 4 ([3] : List Int)) = 0)
          ∨ ((intSub (u 1 4 ([3] : List Int)) (u 1 4 ([3] : List Int)) > 0) ↔
             (intSub (u 1 4 ([3] : List Int)) (u 1 4 ([3] : List Int)) > 0)) := by
  native_decide

example : (intSub (u 1 4 ([3] : List Int)) (u 1 4 ([3] : List Int)) = 0)
          ∨ ((intSub (u 1 4 ([3] : List Int)) (u 1 4 ([3] : List Int)) > 0) ↔
             (intSub (u 2 4 ([3] : List Int)) (u 2 4 ([3] : List Int)) > 0)) := by
  native_decide

example : (intSub (u 1 4 ([3] : List Int)) (u 1 4 ([3] : List Int)) = 0)
          ∨ ((intSub (u 1 4 ([3] : List Int)) (u 1 4 ([3] : List Int)) > 0) ↔
             (intSub (u 3 4 ([3] : List Int)) (u 3 4 ([3] : List Int)) > 0)) := by
  native_decide

-- w=5, s=1, P={1}, R(P)={4}
example : (intSub (u 1 5 ([1] : List Int)) (u 1 5 ([4] : List Int)) = 0)
          ∨ ((intSub (u 1 5 ([1] : List Int)) (u 1 5 ([4] : List Int)) > 0) ↔
             (intSub (u 1 5 ([1] : List Int)) (u 1 5 ([4] : List Int)) > 0)) := by
  native_decide

example : (intSub (u 1 5 ([1] : List Int)) (u 1 5 ([4] : List Int)) = 0)
          ∨ ((intSub (u 1 5 ([1] : List Int)) (u 1 5 ([4] : List Int)) > 0) ↔
             (intSub (u 2 5 ([1] : List Int)) (u 2 5 ([4] : List Int)) > 0)) := by
  native_decide

example : (intSub (u 1 5 ([1] : List Int)) (u 1 5 ([4] : List Int)) = 0)
          ∨ ((intSub (u 1 5 ([1] : List Int)) (u 1 5 ([4] : List Int)) > 0) ↔
             (intSub (u 3 5 ([1] : List Int)) (u 3 5 ([4] : List Int)) > 0)) := by
  native_decide

-- w=5, s=1, P={2}, R(P)={3}
example : (intSub (u 1 5 ([2] : List Int)) (u 1 5 ([3] : List Int)) = 0)
          ∨ ((intSub (u 1 5 ([2] : List Int)) (u 1 5 ([3] : List Int)) > 0) ↔
             (intSub (u 1 5 ([2] : List Int)) (u 1 5 ([3] : List Int)) > 0)) := by
  native_decide

example : (intSub (u 1 5 ([2] : List Int)) (u 1 5 ([3] : List Int)) = 0)
          ∨ ((intSub (u 1 5 ([2] : List Int)) (u 1 5 ([3] : List Int)) > 0) ↔
             (intSub (u 2 5 ([2] : List Int)) (u 2 5 ([3] : List Int)) > 0)) := by
  native_decide

example : (intSub (u 1 5 ([2] : List Int)) (u 1 5 ([3] : List Int)) = 0)
          ∨ ((intSub (u 1 5 ([2] : List Int)) (u 1 5 ([3] : List Int)) > 0) ↔
             (intSub (u 3 5 ([2] : List Int)) (u 3 5 ([3] : List Int)) > 0)) := by
  native_decide

-- w=5, s=1, P={3}, R(P)={2}
example : (intSub (u 1 5 ([3] : List Int)) (u 1 5 ([2] : List Int)) = 0)
          ∨ ((intSub (u 1 5 ([3] : List Int)) (u 1 5 ([2] : List Int)) > 0) ↔
             (intSub (u 1 5 ([3] : List Int)) (u 1 5 ([2] : List Int)) > 0)) := by
  native_decide

example : (intSub (u 1 5 ([3] : List Int)) (u 1 5 ([2] : List Int)) = 0)
          ∨ ((intSub (u 1 5 ([3] : List Int)) (u 1 5 ([2] : List Int)) > 0) ↔
             (intSub (u 2 5 ([3] : List Int)) (u 2 5 ([2] : List Int)) > 0)) := by
  native_decide

example : (intSub (u 1 5 ([3] : List Int)) (u 1 5 ([2] : List Int)) = 0)
          ∨ ((intSub (u 1 5 ([3] : List Int)) (u 1 5 ([2] : List Int)) > 0) ↔
             (intSub (u 3 5 ([3] : List Int)) (u 3 5 ([2] : List Int)) > 0)) := by
  native_decide

-- w=5, s=1, P={1, 2}, R(P)={4, 3}
example : (intSub (u 1 5 ([1, 2] : List Int)) (u 1 5 ([4, 3] : List Int)) = 0)
          ∨ ((intSub (u 1 5 ([1, 2] : List Int)) (u 1 5 ([4, 3] : List Int)) > 0) ↔
             (intSub (u 1 5 ([1, 2] : List Int)) (u 1 5 ([4, 3] : List Int)) > 0)) := by
  native_decide

example : (intSub (u 1 5 ([1, 2] : List Int)) (u 1 5 ([4, 3] : List Int)) = 0)
          ∨ ((intSub (u 1 5 ([1, 2] : List Int)) (u 1 5 ([4, 3] : List Int)) > 0) ↔
             (intSub (u 2 5 ([1, 2] : List Int)) (u 2 5 ([4, 3] : List Int)) > 0)) := by
  native_decide

example : (intSub (u 1 5 ([1, 2] : List Int)) (u 1 5 ([4, 3] : List Int)) = 0)
          ∨ ((intSub (u 1 5 ([1, 2] : List Int)) (u 1 5 ([4, 3] : List Int)) > 0) ↔
             (intSub (u 3 5 ([1, 2] : List Int)) (u 3 5 ([4, 3] : List Int)) > 0)) := by
  native_decide

-- w=5, s=1, P={1, 4}, R(P)={4, 1}
example : (intSub (u 1 5 ([1, 4] : List Int)) (u 1 5 ([4, 1] : List Int)) = 0)
          ∨ ((intSub (u 1 5 ([1, 4] : List Int)) (u 1 5 ([4, 1] : List Int)) > 0) ↔
             (intSub (u 1 5 ([1, 4] : List Int)) (u 1 5 ([4, 1] : List Int)) > 0)) := by
  native_decide

example : (intSub (u 1 5 ([1, 4] : List Int)) (u 1 5 ([4, 1] : List Int)) = 0)
          ∨ ((intSub (u 1 5 ([1, 4] : List Int)) (u 1 5 ([4, 1] : List Int)) > 0) ↔
             (intSub (u 2 5 ([1, 4] : List Int)) (u 2 5 ([4, 1] : List Int)) > 0)) := by
  native_decide

example : (intSub (u 1 5 ([1, 4] : List Int)) (u 1 5 ([4, 1] : List Int)) = 0)
          ∨ ((intSub (u 1 5 ([1, 4] : List Int)) (u 1 5 ([4, 1] : List Int)) > 0) ↔
             (intSub (u 3 5 ([1, 4] : List Int)) (u 3 5 ([4, 1] : List Int)) > 0)) := by
  native_decide

-- w=5, s=1, P={2, 4}, R(P)={3, 1}
example : (intSub (u 1 5 ([2, 4] : List Int)) (u 1 5 ([3, 1] : List Int)) = 0)
          ∨ ((intSub (u 1 5 ([2, 4] : List Int)) (u 1 5 ([3, 1] : List Int)) > 0) ↔
             (intSub (u 1 5 ([2, 4] : List Int)) (u 1 5 ([3, 1] : List Int)) > 0)) := by
  native_decide

example : (intSub (u 1 5 ([2, 4] : List Int)) (u 1 5 ([3, 1] : List Int)) = 0)
          ∨ ((intSub (u 1 5 ([2, 4] : List Int)) (u 1 5 ([3, 1] : List Int)) > 0) ↔
             (intSub (u 2 5 ([2, 4] : List Int)) (u 2 5 ([3, 1] : List Int)) > 0)) := by
  native_decide

example : (intSub (u 1 5 ([2, 4] : List Int)) (u 1 5 ([3, 1] : List Int)) = 0)
          ∨ ((intSub (u 1 5 ([2, 4] : List Int)) (u 1 5 ([3, 1] : List Int)) > 0) ↔
             (intSub (u 3 5 ([2, 4] : List Int)) (u 3 5 ([3, 1] : List Int)) > 0)) := by
  native_decide

-- w=5, s=1, P={1, 2, 3}, R(P)={4, 3, 2}
example : (intSub (u 1 5 ([1, 2, 3] : List Int)) (u 1 5 ([4, 3, 2] : List Int)) = 0)
          ∨ ((intSub (u 1 5 ([1, 2, 3] : List Int)) (u 1 5 ([4, 3, 2] : List Int)) > 0) ↔
             (intSub (u 1 5 ([1, 2, 3] : List Int)) (u 1 5 ([4, 3, 2] : List Int)) > 0)) := by
  native_decide

example : (intSub (u 1 5 ([1, 2, 3] : List Int)) (u 1 5 ([4, 3, 2] : List Int)) = 0)
          ∨ ((intSub (u 1 5 ([1, 2, 3] : List Int)) (u 1 5 ([4, 3, 2] : List Int)) > 0) ↔
             (intSub (u 2 5 ([1, 2, 3] : List Int)) (u 2 5 ([4, 3, 2] : List Int)) > 0)) := by
  native_decide

example : (intSub (u 1 5 ([1, 2, 3] : List Int)) (u 1 5 ([4, 3, 2] : List Int)) = 0)
          ∨ ((intSub (u 1 5 ([1, 2, 3] : List Int)) (u 1 5 ([4, 3, 2] : List Int)) > 0) ↔
             (intSub (u 3 5 ([1, 2, 3] : List Int)) (u 3 5 ([4, 3, 2] : List Int)) > 0)) := by
  native_decide

-- w=5, s=1, P={1, 2, 4}, R(P)={4, 3, 1}
example : (intSub (u 1 5 ([1, 2, 4] : List Int)) (u 1 5 ([4, 3, 1] : List Int)) = 0)
          ∨ ((intSub (u 1 5 ([1, 2, 4] : List Int)) (u 1 5 ([4, 3, 1] : List Int)) > 0) ↔
             (intSub (u 1 5 ([1, 2, 4] : List Int)) (u 1 5 ([4, 3, 1] : List Int)) > 0)) := by
  native_decide

example : (intSub (u 1 5 ([1, 2, 4] : List Int)) (u 1 5 ([4, 3, 1] : List Int)) = 0)
          ∨ ((intSub (u 1 5 ([1, 2, 4] : List Int)) (u 1 5 ([4, 3, 1] : List Int)) > 0) ↔
             (intSub (u 2 5 ([1, 2, 4] : List Int)) (u 2 5 ([4, 3, 1] : List Int)) > 0)) := by
  native_decide

example : (intSub (u 1 5 ([1, 2, 4] : List Int)) (u 1 5 ([4, 3, 1] : List Int)) = 0)
          ∨ ((intSub (u 1 5 ([1, 2, 4] : List Int)) (u 1 5 ([4, 3, 1] : List Int)) > 0) ↔
             (intSub (u 3 5 ([1, 2, 4] : List Int)) (u 3 5 ([4, 3, 1] : List Int)) > 0)) := by
  native_decide

-- w=5, s=1, P={1, 3, 4}, R(P)={4, 2, 1}
example : (intSub (u 1 5 ([1, 3, 4] : List Int)) (u 1 5 ([4, 2, 1] : List Int)) = 0)
          ∨ ((intSub (u 1 5 ([1, 3, 4] : List Int)) (u 1 5 ([4, 2, 1] : List Int)) > 0) ↔
             (intSub (u 1 5 ([1, 3, 4] : List Int)) (u 1 5 ([4, 2, 1] : List Int)) > 0)) := by
  native_decide

example : (intSub (u 1 5 ([1, 3, 4] : List Int)) (u 1 5 ([4, 2, 1] : List Int)) = 0)
          ∨ ((intSub (u 1 5 ([1, 3, 4] : List Int)) (u 1 5 ([4, 2, 1] : List Int)) > 0) ↔
             (intSub (u 2 5 ([1, 3, 4] : List Int)) (u 2 5 ([4, 2, 1] : List Int)) > 0)) := by
  native_decide

example : (intSub (u 1 5 ([1, 3, 4] : List Int)) (u 1 5 ([4, 2, 1] : List Int)) = 0)
          ∨ ((intSub (u 1 5 ([1, 3, 4] : List Int)) (u 1 5 ([4, 2, 1] : List Int)) > 0) ↔
             (intSub (u 3 5 ([1, 3, 4] : List Int)) (u 3 5 ([4, 2, 1] : List Int)) > 0)) := by
  native_decide

-- w=5, s=1, P={1, 2, 3, 4}, R(P)={4, 3, 2, 1}
example : (intSub (u 1 5 ([1, 2, 3, 4] : List Int)) (u 1 5 ([4, 3, 2, 1] : List Int)) = 0)
          ∨ ((intSub (u 1 5 ([1, 2, 3, 4] : List Int)) (u 1 5 ([4, 3, 2, 1] : List Int)) > 0) ↔
             (intSub (u 1 5 ([1, 2, 3, 4] : List Int)) (u 1 5 ([4, 3, 2, 1] : List Int)) > 0)) := by
  native_decide

example : (intSub (u 1 5 ([1, 2, 3, 4] : List Int)) (u 1 5 ([4, 3, 2, 1] : List Int)) = 0)
          ∨ ((intSub (u 1 5 ([1, 2, 3, 4] : List Int)) (u 1 5 ([4, 3, 2, 1] : List Int)) > 0) ↔
             (intSub (u 2 5 ([1, 2, 3, 4] : List Int)) (u 2 5 ([4, 3, 2, 1] : List Int)) > 0)) := by
  native_decide

example : (intSub (u 1 5 ([1, 2, 3, 4] : List Int)) (u 1 5 ([4, 3, 2, 1] : List Int)) = 0)
          ∨ ((intSub (u 1 5 ([1, 2, 3, 4] : List Int)) (u 1 5 ([4, 3, 2, 1] : List Int)) > 0) ↔
             (intSub (u 3 5 ([1, 2, 3, 4] : List Int)) (u 3 5 ([4, 3, 2, 1] : List Int)) > 0)) := by
  native_decide

-- w=5, s=2, P={2}, R(P)={4}
example : (intSub (u 1 5 ([2] : List Int)) (u 1 5 ([4] : List Int)) = 0)
          ∨ ((intSub (u 1 5 ([2] : List Int)) (u 1 5 ([4] : List Int)) > 0) ↔
             (intSub (u 1 5 ([2] : List Int)) (u 1 5 ([4] : List Int)) > 0)) := by
  native_decide

example : (intSub (u 1 5 ([2] : List Int)) (u 1 5 ([4] : List Int)) = 0)
          ∨ ((intSub (u 1 5 ([2] : List Int)) (u 1 5 ([4] : List Int)) > 0) ↔
             (intSub (u 2 5 ([2] : List Int)) (u 2 5 ([4] : List Int)) > 0)) := by
  native_decide

example : (intSub (u 1 5 ([2] : List Int)) (u 1 5 ([4] : List Int)) = 0)
          ∨ ((intSub (u 1 5 ([2] : List Int)) (u 1 5 ([4] : List Int)) > 0) ↔
             (intSub (u 3 5 ([2] : List Int)) (u 3 5 ([4] : List Int)) > 0)) := by
  native_decide

-- w=5, s=2, P={3}, R(P)={3}
example : (intSub (u 1 5 ([3] : List Int)) (u 1 5 ([3] : List Int)) = 0)
          ∨ ((intSub (u 1 5 ([3] : List Int)) (u 1 5 ([3] : List Int)) > 0) ↔
             (intSub (u 1 5 ([3] : List Int)) (u 1 5 ([3] : List Int)) > 0)) := by
  native_decide

example : (intSub (u 1 5 ([3] : List Int)) (u 1 5 ([3] : List Int)) = 0)
          ∨ ((intSub (u 1 5 ([3] : List Int)) (u 1 5 ([3] : List Int)) > 0) ↔
             (intSub (u 2 5 ([3] : List Int)) (u 2 5 ([3] : List Int)) > 0)) := by
  native_decide

example : (intSub (u 1 5 ([3] : List Int)) (u 1 5 ([3] : List Int)) = 0)
          ∨ ((intSub (u 1 5 ([3] : List Int)) (u 1 5 ([3] : List Int)) > 0) ↔
             (intSub (u 3 5 ([3] : List Int)) (u 3 5 ([3] : List Int)) > 0)) := by
  native_decide

-- w=5, s=2, P={4}, R(P)={2}
example : (intSub (u 1 5 ([4] : List Int)) (u 1 5 ([2] : List Int)) = 0)
          ∨ ((intSub (u 1 5 ([4] : List Int)) (u 1 5 ([2] : List Int)) > 0) ↔
             (intSub (u 1 5 ([4] : List Int)) (u 1 5 ([2] : List Int)) > 0)) := by
  native_decide

example : (intSub (u 1 5 ([4] : List Int)) (u 1 5 ([2] : List Int)) = 0)
          ∨ ((intSub (u 1 5 ([4] : List Int)) (u 1 5 ([2] : List Int)) > 0) ↔
             (intSub (u 2 5 ([4] : List Int)) (u 2 5 ([2] : List Int)) > 0)) := by
  native_decide

example : (intSub (u 1 5 ([4] : List Int)) (u 1 5 ([2] : List Int)) = 0)
          ∨ ((intSub (u 1 5 ([4] : List Int)) (u 1 5 ([2] : List Int)) > 0) ↔
             (intSub (u 3 5 ([4] : List Int)) (u 3 5 ([2] : List Int)) > 0)) := by
  native_decide

-- w=5, s=2, P={2, 3}, R(P)={4, 3}
example : (intSub (u 1 5 ([2, 3] : List Int)) (u 1 5 ([4, 3] : List Int)) = 0)
          ∨ ((intSub (u 1 5 ([2, 3] : List Int)) (u 1 5 ([4, 3] : List Int)) > 0) ↔
             (intSub (u 1 5 ([2, 3] : List Int)) (u 1 5 ([4, 3] : List Int)) > 0)) := by
  native_decide

example : (intSub (u 1 5 ([2, 3] : List Int)) (u 1 5 ([4, 3] : List Int)) = 0)
          ∨ ((intSub (u 1 5 ([2, 3] : List Int)) (u 1 5 ([4, 3] : List Int)) > 0) ↔
             (intSub (u 2 5 ([2, 3] : List Int)) (u 2 5 ([4, 3] : List Int)) > 0)) := by
  native_decide

example : (intSub (u 1 5 ([2, 3] : List Int)) (u 1 5 ([4, 3] : List Int)) = 0)
          ∨ ((intSub (u 1 5 ([2, 3] : List Int)) (u 1 5 ([4, 3] : List Int)) > 0) ↔
             (intSub (u 3 5 ([2, 3] : List Int)) (u 3 5 ([4, 3] : List Int)) > 0)) := by
  native_decide

-- w=5, s=2, P={2, 4}, R(P)={4, 2}
example : (intSub (u 1 5 ([2, 4] : List Int)) (u 1 5 ([4, 2] : List Int)) = 0)
          ∨ ((intSub (u 1 5 ([2, 4] : List Int)) (u 1 5 ([4, 2] : List Int)) > 0) ↔
             (intSub (u 1 5 ([2, 4] : List Int)) (u 1 5 ([4, 2] : List Int)) > 0)) := by
  native_decide

example : (intSub (u 1 5 ([2, 4] : List Int)) (u 1 5 ([4, 2] : List Int)) = 0)
          ∨ ((intSub (u 1 5 ([2, 4] : List Int)) (u 1 5 ([4, 2] : List Int)) > 0) ↔
             (intSub (u 2 5 ([2, 4] : List Int)) (u 2 5 ([4, 2] : List Int)) > 0)) := by
  native_decide

example : (intSub (u 1 5 ([2, 4] : List Int)) (u 1 5 ([4, 2] : List Int)) = 0)
          ∨ ((intSub (u 1 5 ([2, 4] : List Int)) (u 1 5 ([4, 2] : List Int)) > 0) ↔
             (intSub (u 3 5 ([2, 4] : List Int)) (u 3 5 ([4, 2] : List Int)) > 0)) := by
  native_decide

-- w=5, s=2, P={3, 4}, R(P)={3, 2}
example : (intSub (u 1 5 ([3, 4] : List Int)) (u 1 5 ([3, 2] : List Int)) = 0)
          ∨ ((intSub (u 1 5 ([3, 4] : List Int)) (u 1 5 ([3, 2] : List Int)) > 0) ↔
             (intSub (u 1 5 ([3, 4] : List Int)) (u 1 5 ([3, 2] : List Int)) > 0)) := by
  native_decide

example : (intSub (u 1 5 ([3, 4] : List Int)) (u 1 5 ([3, 2] : List Int)) = 0)
          ∨ ((intSub (u 1 5 ([3, 4] : List Int)) (u 1 5 ([3, 2] : List Int)) > 0) ↔
             (intSub (u 2 5 ([3, 4] : List Int)) (u 2 5 ([3, 2] : List Int)) > 0)) := by
  native_decide

example : (intSub (u 1 5 ([3, 4] : List Int)) (u 1 5 ([3, 2] : List Int)) = 0)
          ∨ ((intSub (u 1 5 ([3, 4] : List Int)) (u 1 5 ([3, 2] : List Int)) > 0) ↔
             (intSub (u 3 5 ([3, 4] : List Int)) (u 3 5 ([3, 2] : List Int)) > 0)) := by
  native_decide

-- w=5, s=2, P={2, 3, 4}, R(P)={4, 3, 2}
example : (intSub (u 1 5 ([2, 3, 4] : List Int)) (u 1 5 ([4, 3, 2] : List Int)) = 0)
          ∨ ((intSub (u 1 5 ([2, 3, 4] : List Int)) (u 1 5 ([4, 3, 2] : List Int)) > 0) ↔
             (intSub (u 1 5 ([2, 3, 4] : List Int)) (u 1 5 ([4, 3, 2] : List Int)) > 0)) := by
  native_decide

example : (intSub (u 1 5 ([2, 3, 4] : List Int)) (u 1 5 ([4, 3, 2] : List Int)) = 0)
          ∨ ((intSub (u 1 5 ([2, 3, 4] : List Int)) (u 1 5 ([4, 3, 2] : List Int)) > 0) ↔
             (intSub (u 2 5 ([2, 3, 4] : List Int)) (u 2 5 ([4, 3, 2] : List Int)) > 0)) := by
  native_decide

example : (intSub (u 1 5 ([2, 3, 4] : List Int)) (u 1 5 ([4, 3, 2] : List Int)) = 0)
          ∨ ((intSub (u 1 5 ([2, 3, 4] : List Int)) (u 1 5 ([4, 3, 2] : List Int)) > 0) ↔
             (intSub (u 3 5 ([2, 3, 4] : List Int)) (u 3 5 ([4, 3, 2] : List Int)) > 0)) := by
  native_decide

-- w=5, s=3, P={3}, R(P)={4}
example : (intSub (u 1 5 ([3] : List Int)) (u 1 5 ([4] : List Int)) = 0)
          ∨ ((intSub (u 1 5 ([3] : List Int)) (u 1 5 ([4] : List Int)) > 0) ↔
             (intSub (u 1 5 ([3] : List Int)) (u 1 5 ([4] : List Int)) > 0)) := by
  native_decide

example : (intSub (u 1 5 ([3] : List Int)) (u 1 5 ([4] : List Int)) = 0)
          ∨ ((intSub (u 1 5 ([3] : List Int)) (u 1 5 ([4] : List Int)) > 0) ↔
             (intSub (u 2 5 ([3] : List Int)) (u 2 5 ([4] : List Int)) > 0)) := by
  native_decide

example : (intSub (u 1 5 ([3] : List Int)) (u 1 5 ([4] : List Int)) = 0)
          ∨ ((intSub (u 1 5 ([3] : List Int)) (u 1 5 ([4] : List Int)) > 0) ↔
             (intSub (u 3 5 ([3] : List Int)) (u 3 5 ([4] : List Int)) > 0)) := by
  native_decide

-- w=5, s=3, P={4}, R(P)={3}
example : (intSub (u 1 5 ([4] : List Int)) (u 1 5 ([3] : List Int)) = 0)
          ∨ ((intSub (u 1 5 ([4] : List Int)) (u 1 5 ([3] : List Int)) > 0) ↔
             (intSub (u 1 5 ([4] : List Int)) (u 1 5 ([3] : List Int)) > 0)) := by
  native_decide

example : (intSub (u 1 5 ([4] : List Int)) (u 1 5 ([3] : List Int)) = 0)
          ∨ ((intSub (u 1 5 ([4] : List Int)) (u 1 5 ([3] : List Int)) > 0) ↔
             (intSub (u 2 5 ([4] : List Int)) (u 2 5 ([3] : List Int)) > 0)) := by
  native_decide

example : (intSub (u 1 5 ([4] : List Int)) (u 1 5 ([3] : List Int)) = 0)
          ∨ ((intSub (u 1 5 ([4] : List Int)) (u 1 5 ([3] : List Int)) > 0) ↔
             (intSub (u 3 5 ([4] : List Int)) (u 3 5 ([3] : List Int)) > 0)) := by
  native_decide

-- w=5, s=3, P={3, 4}, R(P)={4, 3}
example : (intSub (u 1 5 ([3, 4] : List Int)) (u 1 5 ([4, 3] : List Int)) = 0)
          ∨ ((intSub (u 1 5 ([3, 4] : List Int)) (u 1 5 ([4, 3] : List Int)) > 0) ↔
             (intSub (u 1 5 ([3, 4] : List Int)) (u 1 5 ([4, 3] : List Int)) > 0)) := by
  native_decide

example : (intSub (u 1 5 ([3, 4] : List Int)) (u 1 5 ([4, 3] : List Int)) = 0)
          ∨ ((intSub (u 1 5 ([3, 4] : List Int)) (u 1 5 ([4, 3] : List Int)) > 0) ↔
             (intSub (u 2 5 ([3, 4] : List Int)) (u 2 5 ([4, 3] : List Int)) > 0)) := by
  native_decide

example : (intSub (u 1 5 ([3, 4] : List Int)) (u 1 5 ([4, 3] : List Int)) = 0)
          ∨ ((intSub (u 1 5 ([3, 4] : List Int)) (u 1 5 ([4, 3] : List Int)) > 0) ↔
             (intSub (u 3 5 ([3, 4] : List Int)) (u 3 5 ([4, 3] : List Int)) > 0)) := by
  native_decide

-- w=5, s=4, P={4}, R(P)={4}
example : (intSub (u 1 5 ([4] : List Int)) (u 1 5 ([4] : List Int)) = 0)
          ∨ ((intSub (u 1 5 ([4] : List Int)) (u 1 5 ([4] : List Int)) > 0) ↔
             (intSub (u 1 5 ([4] : List Int)) (u 1 5 ([4] : List Int)) > 0)) := by
  native_decide

example : (intSub (u 1 5 ([4] : List Int)) (u 1 5 ([4] : List Int)) = 0)
          ∨ ((intSub (u 1 5 ([4] : List Int)) (u 1 5 ([4] : List Int)) > 0) ↔
             (intSub (u 2 5 ([4] : List Int)) (u 2 5 ([4] : List Int)) > 0)) := by
  native_decide

example : (intSub (u 1 5 ([4] : List Int)) (u 1 5 ([4] : List Int)) = 0)
          ∨ ((intSub (u 1 5 ([4] : List Int)) (u 1 5 ([4] : List Int)) > 0) ↔
             (intSub (u 3 5 ([4] : List Int)) (u 3 5 ([4] : List Int)) > 0)) := by
  native_decide

-- w=6, s=1, P={1}, R(P)={5}
example : (intSub (u 1 6 ([1] : List Int)) (u 1 6 ([5] : List Int)) = 0)
          ∨ ((intSub (u 1 6 ([1] : List Int)) (u 1 6 ([5] : List Int)) > 0) ↔
             (intSub (u 1 6 ([1] : List Int)) (u 1 6 ([5] : List Int)) > 0)) := by
  native_decide

example : (intSub (u 1 6 ([1] : List Int)) (u 1 6 ([5] : List Int)) = 0)
          ∨ ((intSub (u 1 6 ([1] : List Int)) (u 1 6 ([5] : List Int)) > 0) ↔
             (intSub (u 2 6 ([1] : List Int)) (u 2 6 ([5] : List Int)) > 0)) := by
  native_decide

example : (intSub (u 1 6 ([1] : List Int)) (u 1 6 ([5] : List Int)) = 0)
          ∨ ((intSub (u 1 6 ([1] : List Int)) (u 1 6 ([5] : List Int)) > 0) ↔
             (intSub (u 3 6 ([1] : List Int)) (u 3 6 ([5] : List Int)) > 0)) := by
  native_decide

-- w=6, s=1, P={2}, R(P)={4}
example : (intSub (u 1 6 ([2] : List Int)) (u 1 6 ([4] : List Int)) = 0)
          ∨ ((intSub (u 1 6 ([2] : List Int)) (u 1 6 ([4] : List Int)) > 0) ↔
             (intSub (u 1 6 ([2] : List Int)) (u 1 6 ([4] : List Int)) > 0)) := by
  native_decide

example : (intSub (u 1 6 ([2] : List Int)) (u 1 6 ([4] : List Int)) = 0)
          ∨ ((intSub (u 1 6 ([2] : List Int)) (u 1 6 ([4] : List Int)) > 0) ↔
             (intSub (u 2 6 ([2] : List Int)) (u 2 6 ([4] : List Int)) > 0)) := by
  native_decide

example : (intSub (u 1 6 ([2] : List Int)) (u 1 6 ([4] : List Int)) = 0)
          ∨ ((intSub (u 1 6 ([2] : List Int)) (u 1 6 ([4] : List Int)) > 0) ↔
             (intSub (u 3 6 ([2] : List Int)) (u 3 6 ([4] : List Int)) > 0)) := by
  native_decide

-- w=6, s=1, P={3}, R(P)={3}
example : (intSub (u 1 6 ([3] : List Int)) (u 1 6 ([3] : List Int)) = 0)
          ∨ ((intSub (u 1 6 ([3] : List Int)) (u 1 6 ([3] : List Int)) > 0) ↔
             (intSub (u 1 6 ([3] : List Int)) (u 1 6 ([3] : List Int)) > 0)) := by
  native_decide

example : (intSub (u 1 6 ([3] : List Int)) (u 1 6 ([3] : List Int)) = 0)
          ∨ ((intSub (u 1 6 ([3] : List Int)) (u 1 6 ([3] : List Int)) > 0) ↔
             (intSub (u 2 6 ([3] : List Int)) (u 2 6 ([3] : List Int)) > 0)) := by
  native_decide

example : (intSub (u 1 6 ([3] : List Int)) (u 1 6 ([3] : List Int)) = 0)
          ∨ ((intSub (u 1 6 ([3] : List Int)) (u 1 6 ([3] : List Int)) > 0) ↔
             (intSub (u 3 6 ([3] : List Int)) (u 3 6 ([3] : List Int)) > 0)) := by
  native_decide

-- w=6, s=1, P={1, 2}, R(P)={5, 4}
example : (intSub (u 1 6 ([1, 2] : List Int)) (u 1 6 ([5, 4] : List Int)) = 0)
          ∨ ((intSub (u 1 6 ([1, 2] : List Int)) (u 1 6 ([5, 4] : List Int)) > 0) ↔
             (intSub (u 1 6 ([1, 2] : List Int)) (u 1 6 ([5, 4] : List Int)) > 0)) := by
  native_decide

example : (intSub (u 1 6 ([1, 2] : List Int)) (u 1 6 ([5, 4] : List Int)) = 0)
          ∨ ((intSub (u 1 6 ([1, 2] : List Int)) (u 1 6 ([5, 4] : List Int)) > 0) ↔
             (intSub (u 2 6 ([1, 2] : List Int)) (u 2 6 ([5, 4] : List Int)) > 0)) := by
  native_decide

example : (intSub (u 1 6 ([1, 2] : List Int)) (u 1 6 ([5, 4] : List Int)) = 0)
          ∨ ((intSub (u 1 6 ([1, 2] : List Int)) (u 1 6 ([5, 4] : List Int)) > 0) ↔
             (intSub (u 3 6 ([1, 2] : List Int)) (u 3 6 ([5, 4] : List Int)) > 0)) := by
  native_decide

-- w=6, s=1, P={1, 5}, R(P)={5, 1}
example : (intSub (u 1 6 ([1, 5] : List Int)) (u 1 6 ([5, 1] : List Int)) = 0)
          ∨ ((intSub (u 1 6 ([1, 5] : List Int)) (u 1 6 ([5, 1] : List Int)) > 0) ↔
             (intSub (u 1 6 ([1, 5] : List Int)) (u 1 6 ([5, 1] : List Int)) > 0)) := by
  native_decide

example : (intSub (u 1 6 ([1, 5] : List Int)) (u 1 6 ([5, 1] : List Int)) = 0)
          ∨ ((intSub (u 1 6 ([1, 5] : List Int)) (u 1 6 ([5, 1] : List Int)) > 0) ↔
             (intSub (u 2 6 ([1, 5] : List Int)) (u 2 6 ([5, 1] : List Int)) > 0)) := by
  native_decide

example : (intSub (u 1 6 ([1, 5] : List Int)) (u 1 6 ([5, 1] : List Int)) = 0)
          ∨ ((intSub (u 1 6 ([1, 5] : List Int)) (u 1 6 ([5, 1] : List Int)) > 0) ↔
             (intSub (u 3 6 ([1, 5] : List Int)) (u 3 6 ([5, 1] : List Int)) > 0)) := by
  native_decide

-- w=6, s=1, P={2, 5}, R(P)={4, 1}
example : (intSub (u 1 6 ([2, 5] : List Int)) (u 1 6 ([4, 1] : List Int)) = 0)
          ∨ ((intSub (u 1 6 ([2, 5] : List Int)) (u 1 6 ([4, 1] : List Int)) > 0) ↔
             (intSub (u 1 6 ([2, 5] : List Int)) (u 1 6 ([4, 1] : List Int)) > 0)) := by
  native_decide

example : (intSub (u 1 6 ([2, 5] : List Int)) (u 1 6 ([4, 1] : List Int)) = 0)
          ∨ ((intSub (u 1 6 ([2, 5] : List Int)) (u 1 6 ([4, 1] : List Int)) > 0) ↔
             (intSub (u 2 6 ([2, 5] : List Int)) (u 2 6 ([4, 1] : List Int)) > 0)) := by
  native_decide

example : (intSub (u 1 6 ([2, 5] : List Int)) (u 1 6 ([4, 1] : List Int)) = 0)
          ∨ ((intSub (u 1 6 ([2, 5] : List Int)) (u 1 6 ([4, 1] : List Int)) > 0) ↔
             (intSub (u 3 6 ([2, 5] : List Int)) (u 3 6 ([4, 1] : List Int)) > 0)) := by
  native_decide

-- w=6, s=1, P={1, 2, 3}, R(P)={5, 4, 3}
example : (intSub (u 1 6 ([1, 2, 3] : List Int)) (u 1 6 ([5, 4, 3] : List Int)) = 0)
          ∨ ((intSub (u 1 6 ([1, 2, 3] : List Int)) (u 1 6 ([5, 4, 3] : List Int)) > 0) ↔
             (intSub (u 1 6 ([1, 2, 3] : List Int)) (u 1 6 ([5, 4, 3] : List Int)) > 0)) := by
  native_decide

example : (intSub (u 1 6 ([1, 2, 3] : List Int)) (u 1 6 ([5, 4, 3] : List Int)) = 0)
          ∨ ((intSub (u 1 6 ([1, 2, 3] : List Int)) (u 1 6 ([5, 4, 3] : List Int)) > 0) ↔
             (intSub (u 2 6 ([1, 2, 3] : List Int)) (u 2 6 ([5, 4, 3] : List Int)) > 0)) := by
  native_decide

example : (intSub (u 1 6 ([1, 2, 3] : List Int)) (u 1 6 ([5, 4, 3] : List Int)) = 0)
          ∨ ((intSub (u 1 6 ([1, 2, 3] : List Int)) (u 1 6 ([5, 4, 3] : List Int)) > 0) ↔
             (intSub (u 3 6 ([1, 2, 3] : List Int)) (u 3 6 ([5, 4, 3] : List Int)) > 0)) := by
  native_decide

-- w=6, s=1, P={1, 3, 4}, R(P)={5, 3, 2}
example : (intSub (u 1 6 ([1, 3, 4] : List Int)) (u 1 6 ([5, 3, 2] : List Int)) = 0)
          ∨ ((intSub (u 1 6 ([1, 3, 4] : List Int)) (u 1 6 ([5, 3, 2] : List Int)) > 0) ↔
             (intSub (u 1 6 ([1, 3, 4] : List Int)) (u 1 6 ([5, 3, 2] : List Int)) > 0)) := by
  native_decide

example : (intSub (u 1 6 ([1, 3, 4] : List Int)) (u 1 6 ([5, 3, 2] : List Int)) = 0)
          ∨ ((intSub (u 1 6 ([1, 3, 4] : List Int)) (u 1 6 ([5, 3, 2] : List Int)) > 0) ↔
             (intSub (u 2 6 ([1, 3, 4] : List Int)) (u 2 6 ([5, 3, 2] : List Int)) > 0)) := by
  native_decide

example : (intSub (u 1 6 ([1, 3, 4] : List Int)) (u 1 6 ([5, 3, 2] : List Int)) = 0)
          ∨ ((intSub (u 1 6 ([1, 3, 4] : List Int)) (u 1 6 ([5, 3, 2] : List Int)) > 0) ↔
             (intSub (u 3 6 ([1, 3, 4] : List Int)) (u 3 6 ([5, 3, 2] : List Int)) > 0)) := by
  native_decide

-- w=6, s=1, P={2, 3, 4}, R(P)={4, 3, 2}
example : (intSub (u 1 6 ([2, 3, 4] : List Int)) (u 1 6 ([4, 3, 2] : List Int)) = 0)
          ∨ ((intSub (u 1 6 ([2, 3, 4] : List Int)) (u 1 6 ([4, 3, 2] : List Int)) > 0) ↔
             (intSub (u 1 6 ([2, 3, 4] : List Int)) (u 1 6 ([4, 3, 2] : List Int)) > 0)) := by
  native_decide

example : (intSub (u 1 6 ([2, 3, 4] : List Int)) (u 1 6 ([4, 3, 2] : List Int)) = 0)
          ∨ ((intSub (u 1 6 ([2, 3, 4] : List Int)) (u 1 6 ([4, 3, 2] : List Int)) > 0) ↔
             (intSub (u 2 6 ([2, 3, 4] : List Int)) (u 2 6 ([4, 3, 2] : List Int)) > 0)) := by
  native_decide

example : (intSub (u 1 6 ([2, 3, 4] : List Int)) (u 1 6 ([4, 3, 2] : List Int)) = 0)
          ∨ ((intSub (u 1 6 ([2, 3, 4] : List Int)) (u 1 6 ([4, 3, 2] : List Int)) > 0) ↔
             (intSub (u 3 6 ([2, 3, 4] : List Int)) (u 3 6 ([4, 3, 2] : List Int)) > 0)) := by
  native_decide

-- w=6, s=1, P={1, 2, 3, 4}, R(P)={5, 4, 3, 2}
example : (intSub (u 1 6 ([1, 2, 3, 4] : List Int)) (u 1 6 ([5, 4, 3, 2] : List Int)) = 0)
          ∨ ((intSub (u 1 6 ([1, 2, 3, 4] : List Int)) (u 1 6 ([5, 4, 3, 2] : List Int)) > 0) ↔
             (intSub (u 1 6 ([1, 2, 3, 4] : List Int)) (u 1 6 ([5, 4, 3, 2] : List Int)) > 0)) := by
  native_decide

example : (intSub (u 1 6 ([1, 2, 3, 4] : List Int)) (u 1 6 ([5, 4, 3, 2] : List Int)) = 0)
          ∨ ((intSub (u 1 6 ([1, 2, 3, 4] : List Int)) (u 1 6 ([5, 4, 3, 2] : List Int)) > 0) ↔
             (intSub (u 2 6 ([1, 2, 3, 4] : List Int)) (u 2 6 ([5, 4, 3, 2] : List Int)) > 0)) := by
  native_decide

example : (intSub (u 1 6 ([1, 2, 3, 4] : List Int)) (u 1 6 ([5, 4, 3, 2] : List Int)) = 0)
          ∨ ((intSub (u 1 6 ([1, 2, 3, 4] : List Int)) (u 1 6 ([5, 4, 3, 2] : List Int)) > 0) ↔
             (intSub (u 3 6 ([1, 2, 3, 4] : List Int)) (u 3 6 ([5, 4, 3, 2] : List Int)) > 0)) := by
  native_decide

-- w=6, s=1, P={1, 2, 3, 5}, R(P)={5, 4, 3, 1}
example : (intSub (u 1 6 ([1, 2, 3, 5] : List Int)) (u 1 6 ([5, 4, 3, 1] : List Int)) = 0)
          ∨ ((intSub (u 1 6 ([1, 2, 3, 5] : List Int)) (u 1 6 ([5, 4, 3, 1] : List Int)) > 0) ↔
             (intSub (u 1 6 ([1, 2, 3, 5] : List Int)) (u 1 6 ([5, 4, 3, 1] : List Int)) > 0)) := by
  native_decide

example : (intSub (u 1 6 ([1, 2, 3, 5] : List Int)) (u 1 6 ([5, 4, 3, 1] : List Int)) = 0)
          ∨ ((intSub (u 1 6 ([1, 2, 3, 5] : List Int)) (u 1 6 ([5, 4, 3, 1] : List Int)) > 0) ↔
             (intSub (u 2 6 ([1, 2, 3, 5] : List Int)) (u 2 6 ([5, 4, 3, 1] : List Int)) > 0)) := by
  native_decide

example : (intSub (u 1 6 ([1, 2, 3, 5] : List Int)) (u 1 6 ([5, 4, 3, 1] : List Int)) = 0)
          ∨ ((intSub (u 1 6 ([1, 2, 3, 5] : List Int)) (u 1 6 ([5, 4, 3, 1] : List Int)) > 0) ↔
             (intSub (u 3 6 ([1, 2, 3, 5] : List Int)) (u 3 6 ([5, 4, 3, 1] : List Int)) > 0)) := by
  native_decide

-- w=6, s=1, P={1, 2, 4, 5}, R(P)={5, 4, 2, 1}
example : (intSub (u 1 6 ([1, 2, 4, 5] : List Int)) (u 1 6 ([5, 4, 2, 1] : List Int)) = 0)
          ∨ ((intSub (u 1 6 ([1, 2, 4, 5] : List Int)) (u 1 6 ([5, 4, 2, 1] : List Int)) > 0) ↔
             (intSub (u 1 6 ([1, 2, 4, 5] : List Int)) (u 1 6 ([5, 4, 2, 1] : List Int)) > 0)) := by
  native_decide

example : (intSub (u 1 6 ([1, 2, 4, 5] : List Int)) (u 1 6 ([5, 4, 2, 1] : List Int)) = 0)
          ∨ ((intSub (u 1 6 ([1, 2, 4, 5] : List Int)) (u 1 6 ([5, 4, 2, 1] : List Int)) > 0) ↔
             (intSub (u 2 6 ([1, 2, 4, 5] : List Int)) (u 2 6 ([5, 4, 2, 1] : List Int)) > 0)) := by
  native_decide

example : (intSub (u 1 6 ([1, 2, 4, 5] : List Int)) (u 1 6 ([5, 4, 2, 1] : List Int)) = 0)
          ∨ ((intSub (u 1 6 ([1, 2, 4, 5] : List Int)) (u 1 6 ([5, 4, 2, 1] : List Int)) > 0) ↔
             (intSub (u 3 6 ([1, 2, 4, 5] : List Int)) (u 3 6 ([5, 4, 2, 1] : List Int)) > 0)) := by
  native_decide

-- w=6, s=2, P={2}, R(P)={5}
example : (intSub (u 1 6 ([2] : List Int)) (u 1 6 ([5] : List Int)) = 0)
          ∨ ((intSub (u 1 6 ([2] : List Int)) (u 1 6 ([5] : List Int)) > 0) ↔
             (intSub (u 1 6 ([2] : List Int)) (u 1 6 ([5] : List Int)) > 0)) := by
  native_decide

example : (intSub (u 1 6 ([2] : List Int)) (u 1 6 ([5] : List Int)) = 0)
          ∨ ((intSub (u 1 6 ([2] : List Int)) (u 1 6 ([5] : List Int)) > 0) ↔
             (intSub (u 2 6 ([2] : List Int)) (u 2 6 ([5] : List Int)) > 0)) := by
  native_decide

example : (intSub (u 1 6 ([2] : List Int)) (u 1 6 ([5] : List Int)) = 0)
          ∨ ((intSub (u 1 6 ([2] : List Int)) (u 1 6 ([5] : List Int)) > 0) ↔
             (intSub (u 3 6 ([2] : List Int)) (u 3 6 ([5] : List Int)) > 0)) := by
  native_decide

-- w=6, s=2, P={3}, R(P)={4}
example : (intSub (u 1 6 ([3] : List Int)) (u 1 6 ([4] : List Int)) = 0)
          ∨ ((intSub (u 1 6 ([3] : List Int)) (u 1 6 ([4] : List Int)) > 0) ↔
             (intSub (u 1 6 ([3] : List Int)) (u 1 6 ([4] : List Int)) > 0)) := by
  native_decide

example : (intSub (u 1 6 ([3] : List Int)) (u 1 6 ([4] : List Int)) = 0)
          ∨ ((intSub (u 1 6 ([3] : List Int)) (u 1 6 ([4] : List Int)) > 0) ↔
             (intSub (u 2 6 ([3] : List Int)) (u 2 6 ([4] : List Int)) > 0)) := by
  native_decide

example : (intSub (u 1 6 ([3] : List Int)) (u 1 6 ([4] : List Int)) = 0)
          ∨ ((intSub (u 1 6 ([3] : List Int)) (u 1 6 ([4] : List Int)) > 0) ↔
             (intSub (u 3 6 ([3] : List Int)) (u 3 6 ([4] : List Int)) > 0)) := by
  native_decide

-- w=6, s=2, P={4}, R(P)={3}
example : (intSub (u 1 6 ([4] : List Int)) (u 1 6 ([3] : List Int)) = 0)
          ∨ ((intSub (u 1 6 ([4] : List Int)) (u 1 6 ([3] : List Int)) > 0) ↔
             (intSub (u 1 6 ([4] : List Int)) (u 1 6 ([3] : List Int)) > 0)) := by
  native_decide

example : (intSub (u 1 6 ([4] : List Int)) (u 1 6 ([3] : List Int)) = 0)
          ∨ ((intSub (u 1 6 ([4] : List Int)) (u 1 6 ([3] : List Int)) > 0) ↔
             (intSub (u 2 6 ([4] : List Int)) (u 2 6 ([3] : List Int)) > 0)) := by
  native_decide

example : (intSub (u 1 6 ([4] : List Int)) (u 1 6 ([3] : List Int)) = 0)
          ∨ ((intSub (u 1 6 ([4] : List Int)) (u 1 6 ([3] : List Int)) > 0) ↔
             (intSub (u 3 6 ([4] : List Int)) (u 3 6 ([3] : List Int)) > 0)) := by
  native_decide

-- w=6, s=2, P={2, 3}, R(P)={5, 4}
example : (intSub (u 1 6 ([2, 3] : List Int)) (u 1 6 ([5, 4] : List Int)) = 0)
          ∨ ((intSub (u 1 6 ([2, 3] : List Int)) (u 1 6 ([5, 4] : List Int)) > 0) ↔
             (intSub (u 1 6 ([2, 3] : List Int)) (u 1 6 ([5, 4] : List Int)) > 0)) := by
  native_decide

example : (intSub (u 1 6 ([2, 3] : List Int)) (u 1 6 ([5, 4] : List Int)) = 0)
          ∨ ((intSub (u 1 6 ([2, 3] : List Int)) (u 1 6 ([5, 4] : List Int)) > 0) ↔
             (intSub (u 2 6 ([2, 3] : List Int)) (u 2 6 ([5, 4] : List Int)) > 0)) := by
  native_decide

example : (intSub (u 1 6 ([2, 3] : List Int)) (u 1 6 ([5, 4] : List Int)) = 0)
          ∨ ((intSub (u 1 6 ([2, 3] : List Int)) (u 1 6 ([5, 4] : List Int)) > 0) ↔
             (intSub (u 3 6 ([2, 3] : List Int)) (u 3 6 ([5, 4] : List Int)) > 0)) := by
  native_decide

-- w=6, s=2, P={2, 5}, R(P)={5, 2}
example : (intSub (u 1 6 ([2, 5] : List Int)) (u 1 6 ([5, 2] : List Int)) = 0)
          ∨ ((intSub (u 1 6 ([2, 5] : List Int)) (u 1 6 ([5, 2] : List Int)) > 0) ↔
             (intSub (u 1 6 ([2, 5] : List Int)) (u 1 6 ([5, 2] : List Int)) > 0)) := by
  native_decide

example : (intSub (u 1 6 ([2, 5] : List Int)) (u 1 6 ([5, 2] : List Int)) = 0)
          ∨ ((intSub (u 1 6 ([2, 5] : List Int)) (u 1 6 ([5, 2] : List Int)) > 0) ↔
             (intSub (u 2 6 ([2, 5] : List Int)) (u 2 6 ([5, 2] : List Int)) > 0)) := by
  native_decide

example : (intSub (u 1 6 ([2, 5] : List Int)) (u 1 6 ([5, 2] : List Int)) = 0)
          ∨ ((intSub (u 1 6 ([2, 5] : List Int)) (u 1 6 ([5, 2] : List Int)) > 0) ↔
             (intSub (u 3 6 ([2, 5] : List Int)) (u 3 6 ([5, 2] : List Int)) > 0)) := by
  native_decide

-- w=6, s=2, P={3, 5}, R(P)={4, 2}
example : (intSub (u 1 6 ([3, 5] : List Int)) (u 1 6 ([4, 2] : List Int)) = 0)
          ∨ ((intSub (u 1 6 ([3, 5] : List Int)) (u 1 6 ([4, 2] : List Int)) > 0) ↔
             (intSub (u 1 6 ([3, 5] : List Int)) (u 1 6 ([4, 2] : List Int)) > 0)) := by
  native_decide

example : (intSub (u 1 6 ([3, 5] : List Int)) (u 1 6 ([4, 2] : List Int)) = 0)
          ∨ ((intSub (u 1 6 ([3, 5] : List Int)) (u 1 6 ([4, 2] : List Int)) > 0) ↔
             (intSub (u 2 6 ([3, 5] : List Int)) (u 2 6 ([4, 2] : List Int)) > 0)) := by
  native_decide

example : (intSub (u 1 6 ([3, 5] : List Int)) (u 1 6 ([4, 2] : List Int)) = 0)
          ∨ ((intSub (u 1 6 ([3, 5] : List Int)) (u 1 6 ([4, 2] : List Int)) > 0) ↔
             (intSub (u 3 6 ([3, 5] : List Int)) (u 3 6 ([4, 2] : List Int)) > 0)) := by
  native_decide

-- w=6, s=2, P={2, 3, 4}, R(P)={5, 4, 3}
example : (intSub (u 1 6 ([2, 3, 4] : List Int)) (u 1 6 ([5, 4, 3] : List Int)) = 0)
          ∨ ((intSub (u 1 6 ([2, 3, 4] : List Int)) (u 1 6 ([5, 4, 3] : List Int)) > 0) ↔
             (intSub (u 1 6 ([2, 3, 4] : List Int)) (u 1 6 ([5, 4, 3] : List Int)) > 0)) := by
  native_decide

example : (intSub (u 1 6 ([2, 3, 4] : List Int)) (u 1 6 ([5, 4, 3] : List Int)) = 0)
          ∨ ((intSub (u 1 6 ([2, 3, 4] : List Int)) (u 1 6 ([5, 4, 3] : List Int)) > 0) ↔
             (intSub (u 2 6 ([2, 3, 4] : List Int)) (u 2 6 ([5, 4, 3] : List Int)) > 0)) := by
  native_decide

example : (intSub (u 1 6 ([2, 3, 4] : List Int)) (u 1 6 ([5, 4, 3] : List Int)) = 0)
          ∨ ((intSub (u 1 6 ([2, 3, 4] : List Int)) (u 1 6 ([5, 4, 3] : List Int)) > 0) ↔
             (intSub (u 3 6 ([2, 3, 4] : List Int)) (u 3 6 ([5, 4, 3] : List Int)) > 0)) := by
  native_decide

-- w=6, s=2, P={2, 3, 5}, R(P)={5, 4, 2}
example : (intSub (u 1 6 ([2, 3, 5] : List Int)) (u 1 6 ([5, 4, 2] : List Int)) = 0)
          ∨ ((intSub (u 1 6 ([2, 3, 5] : List Int)) (u 1 6 ([5, 4, 2] : List Int)) > 0) ↔
             (intSub (u 1 6 ([2, 3, 5] : List Int)) (u 1 6 ([5, 4, 2] : List Int)) > 0)) := by
  native_decide

example : (intSub (u 1 6 ([2, 3, 5] : List Int)) (u 1 6 ([5, 4, 2] : List Int)) = 0)
          ∨ ((intSub (u 1 6 ([2, 3, 5] : List Int)) (u 1 6 ([5, 4, 2] : List Int)) > 0) ↔
             (intSub (u 2 6 ([2, 3, 5] : List Int)) (u 2 6 ([5, 4, 2] : List Int)) > 0)) := by
  native_decide

example : (intSub (u 1 6 ([2, 3, 5] : List Int)) (u 1 6 ([5, 4, 2] : List Int)) = 0)
          ∨ ((intSub (u 1 6 ([2, 3, 5] : List Int)) (u 1 6 ([5, 4, 2] : List Int)) > 0) ↔
             (intSub (u 3 6 ([2, 3, 5] : List Int)) (u 3 6 ([5, 4, 2] : List Int)) > 0)) := by
  native_decide

-- w=6, s=2, P={2, 4, 5}, R(P)={5, 3, 2}
example : (intSub (u 1 6 ([2, 4, 5] : List Int)) (u 1 6 ([5, 3, 2] : List Int)) = 0)
          ∨ ((intSub (u 1 6 ([2, 4, 5] : List Int)) (u 1 6 ([5, 3, 2] : List Int)) > 0) ↔
             (intSub (u 1 6 ([2, 4, 5] : List Int)) (u 1 6 ([5, 3, 2] : List Int)) > 0)) := by
  native_decide

example : (intSub (u 1 6 ([2, 4, 5] : List Int)) (u 1 6 ([5, 3, 2] : List Int)) = 0)
          ∨ ((intSub (u 1 6 ([2, 4, 5] : List Int)) (u 1 6 ([5, 3, 2] : List Int)) > 0) ↔
             (intSub (u 2 6 ([2, 4, 5] : List Int)) (u 2 6 ([5, 3, 2] : List Int)) > 0)) := by
  native_decide

example : (intSub (u 1 6 ([2, 4, 5] : List Int)) (u 1 6 ([5, 3, 2] : List Int)) = 0)
          ∨ ((intSub (u 1 6 ([2, 4, 5] : List Int)) (u 1 6 ([5, 3, 2] : List Int)) > 0) ↔
             (intSub (u 3 6 ([2, 4, 5] : List Int)) (u 3 6 ([5, 3, 2] : List Int)) > 0)) := by
  native_decide

-- w=6, s=2, P={2, 3, 4, 5}, R(P)={5, 4, 3, 2}
example : (intSub (u 1 6 ([2, 3, 4, 5] : List Int)) (u 1 6 ([5, 4, 3, 2] : List Int)) = 0)
          ∨ ((intSub (u 1 6 ([2, 3, 4, 5] : List Int)) (u 1 6 ([5, 4, 3, 2] : List Int)) > 0) ↔
             (intSub (u 1 6 ([2, 3, 4, 5] : List Int)) (u 1 6 ([5, 4, 3, 2] : List Int)) > 0)) := by
  native_decide

example : (intSub (u 1 6 ([2, 3, 4, 5] : List Int)) (u 1 6 ([5, 4, 3, 2] : List Int)) = 0)
          ∨ ((intSub (u 1 6 ([2, 3, 4, 5] : List Int)) (u 1 6 ([5, 4, 3, 2] : List Int)) > 0) ↔
             (intSub (u 2 6 ([2, 3, 4, 5] : List Int)) (u 2 6 ([5, 4, 3, 2] : List Int)) > 0)) := by
  native_decide

example : (intSub (u 1 6 ([2, 3, 4, 5] : List Int)) (u 1 6 ([5, 4, 3, 2] : List Int)) = 0)
          ∨ ((intSub (u 1 6 ([2, 3, 4, 5] : List Int)) (u 1 6 ([5, 4, 3, 2] : List Int)) > 0) ↔
             (intSub (u 3 6 ([2, 3, 4, 5] : List Int)) (u 3 6 ([5, 4, 3, 2] : List Int)) > 0)) := by
  native_decide

-- w=6, s=3, P={3}, R(P)={5}
example : (intSub (u 1 6 ([3] : List Int)) (u 1 6 ([5] : List Int)) = 0)
          ∨ ((intSub (u 1 6 ([3] : List Int)) (u 1 6 ([5] : List Int)) > 0) ↔
             (intSub (u 1 6 ([3] : List Int)) (u 1 6 ([5] : List Int)) > 0)) := by
  native_decide

example : (intSub (u 1 6 ([3] : List Int)) (u 1 6 ([5] : List Int)) = 0)
          ∨ ((intSub (u 1 6 ([3] : List Int)) (u 1 6 ([5] : List Int)) > 0) ↔
             (intSub (u 2 6 ([3] : List Int)) (u 2 6 ([5] : List Int)) > 0)) := by
  native_decide

example : (intSub (u 1 6 ([3] : List Int)) (u 1 6 ([5] : List Int)) = 0)
          ∨ ((intSub (u 1 6 ([3] : List Int)) (u 1 6 ([5] : List Int)) > 0) ↔
             (intSub (u 3 6 ([3] : List Int)) (u 3 6 ([5] : List Int)) > 0)) := by
  native_decide

