import Mathlib.Data.Nat.Basic
import Mathlib.Data.Int.Basic
import Mathlib.Data.List.Basic

set_option maxHeartbeats 0
set_option linter.unusedVariables false

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

def rectCells (h w : Nat) : List Cell :=
  (List.range h).flatMap (fun i => (List.range w).map (fun j => ((i : Int), (j : Int))))

-- Theorem A machine-certified finite sweep (equal-height two-block < rectangle).
-- w <= 6, q <= 3 (h <= 6) to keep native_decide fast; s ranges over all 0<|s|<w.

-- (w=2, q=1, s=-1) area=4
example : tilings [((0 : Int), (0 : Int)), ((0 : Int), (1 : Int)), ((1 : Int), (-1 : Int)), ((1 : Int), (0 : Int))] < tilings (rectCells (2) 2) := by
  native_decide

-- (w=2, q=1, s=1) area=4
example : tilings [((0 : Int), (0 : Int)), ((0 : Int), (1 : Int)), ((1 : Int), (1 : Int)), ((1 : Int), (2 : Int))] < tilings (rectCells (2) 2) := by
  native_decide

-- (w=2, q=2, s=-1) area=8
example : tilings [((0 : Int), (0 : Int)), ((0 : Int), (1 : Int)), ((1 : Int), (0 : Int)), ((1 : Int), (1 : Int)), ((2 : Int), (-1 : Int)), ((2 : Int), (0 : Int)), ((3 : Int), (-1 : Int)), ((3 : Int), (0 : Int))] < tilings (rectCells (4) 2) := by
  native_decide

-- (w=2, q=2, s=1) area=8
example : tilings [((0 : Int), (0 : Int)), ((0 : Int), (1 : Int)), ((1 : Int), (0 : Int)), ((1 : Int), (1 : Int)), ((2 : Int), (1 : Int)), ((2 : Int), (2 : Int)), ((3 : Int), (1 : Int)), ((3 : Int), (2 : Int))] < tilings (rectCells (4) 2) := by
  native_decide

-- (w=2, q=3, s=-1) area=12
example : tilings [((0 : Int), (0 : Int)), ((0 : Int), (1 : Int)), ((1 : Int), (0 : Int)), ((1 : Int), (1 : Int)), ((2 : Int), (0 : Int)), ((2 : Int), (1 : Int)), ((3 : Int), (-1 : Int)), ((3 : Int), (0 : Int)), ((4 : Int), (-1 : Int)), ((4 : Int), (0 : Int)), ((5 : Int), (-1 : Int)), ((5 : Int), (0 : Int))] < tilings (rectCells (6) 2) := by
  native_decide

-- (w=2, q=3, s=1) area=12
example : tilings [((0 : Int), (0 : Int)), ((0 : Int), (1 : Int)), ((1 : Int), (0 : Int)), ((1 : Int), (1 : Int)), ((2 : Int), (0 : Int)), ((2 : Int), (1 : Int)), ((3 : Int), (1 : Int)), ((3 : Int), (2 : Int)), ((4 : Int), (1 : Int)), ((4 : Int), (2 : Int)), ((5 : Int), (1 : Int)), ((5 : Int), (2 : Int))] < tilings (rectCells (6) 2) := by
  native_decide

-- (w=3, q=1, s=-2) area=6
example : tilings [((0 : Int), (0 : Int)), ((0 : Int), (1 : Int)), ((0 : Int), (2 : Int)), ((1 : Int), (-2 : Int)), ((1 : Int), (-1 : Int)), ((1 : Int), (0 : Int))] < tilings (rectCells (2) 3) := by
  native_decide

-- (w=3, q=1, s=-1) area=6
example : tilings [((0 : Int), (0 : Int)), ((0 : Int), (1 : Int)), ((0 : Int), (2 : Int)), ((1 : Int), (-1 : Int)), ((1 : Int), (0 : Int)), ((1 : Int), (1 : Int))] < tilings (rectCells (2) 3) := by
  native_decide

-- (w=3, q=1, s=1) area=6
example : tilings [((0 : Int), (0 : Int)), ((0 : Int), (1 : Int)), ((0 : Int), (2 : Int)), ((1 : Int), (1 : Int)), ((1 : Int), (2 : Int)), ((1 : Int), (3 : Int))] < tilings (rectCells (2) 3) := by
  native_decide

-- (w=3, q=1, s=2) area=6
example : tilings [((0 : Int), (0 : Int)), ((0 : Int), (1 : Int)), ((0 : Int), (2 : Int)), ((1 : Int), (2 : Int)), ((1 : Int), (3 : Int)), ((1 : Int), (4 : Int))] < tilings (rectCells (2) 3) := by
  native_decide

-- (w=3, q=2, s=-2) area=12
example : tilings [((0 : Int), (0 : Int)), ((0 : Int), (1 : Int)), ((0 : Int), (2 : Int)), ((1 : Int), (0 : Int)), ((1 : Int), (1 : Int)), ((1 : Int), (2 : Int)), ((2 : Int), (-2 : Int)), ((2 : Int), (-1 : Int)), ((2 : Int), (0 : Int)), ((3 : Int), (-2 : Int)), ((3 : Int), (-1 : Int)), ((3 : Int), (0 : Int))] < tilings (rectCells (4) 3) := by
  native_decide

-- (w=3, q=2, s=-1) area=12
example : tilings [((0 : Int), (0 : Int)), ((0 : Int), (1 : Int)), ((0 : Int), (2 : Int)), ((1 : Int), (0 : Int)), ((1 : Int), (1 : Int)), ((1 : Int), (2 : Int)), ((2 : Int), (-1 : Int)), ((2 : Int), (0 : Int)), ((2 : Int), (1 : Int)), ((3 : Int), (-1 : Int)), ((3 : Int), (0 : Int)), ((3 : Int), (1 : Int))] < tilings (rectCells (4) 3) := by
  native_decide

-- (w=3, q=2, s=1) area=12
example : tilings [((0 : Int), (0 : Int)), ((0 : Int), (1 : Int)), ((0 : Int), (2 : Int)), ((1 : Int), (0 : Int)), ((1 : Int), (1 : Int)), ((1 : Int), (2 : Int)), ((2 : Int), (1 : Int)), ((2 : Int), (2 : Int)), ((2 : Int), (3 : Int)), ((3 : Int), (1 : Int)), ((3 : Int), (2 : Int)), ((3 : Int), (3 : Int))] < tilings (rectCells (4) 3) := by
  native_decide

-- (w=3, q=2, s=2) area=12
example : tilings [((0 : Int), (0 : Int)), ((0 : Int), (1 : Int)), ((0 : Int), (2 : Int)), ((1 : Int), (0 : Int)), ((1 : Int), (1 : Int)), ((1 : Int), (2 : Int)), ((2 : Int), (2 : Int)), ((2 : Int), (3 : Int)), ((2 : Int), (4 : Int)), ((3 : Int), (2 : Int)), ((3 : Int), (3 : Int)), ((3 : Int), (4 : Int))] < tilings (rectCells (4) 3) := by
  native_decide

-- (w=3, q=3, s=-2) area=18
example : tilings [((0 : Int), (0 : Int)), ((0 : Int), (1 : Int)), ((0 : Int), (2 : Int)), ((1 : Int), (0 : Int)), ((1 : Int), (1 : Int)), ((1 : Int), (2 : Int)), ((2 : Int), (0 : Int)), ((2 : Int), (1 : Int)), ((2 : Int), (2 : Int)), ((3 : Int), (-2 : Int)), ((3 : Int), (-1 : Int)), ((3 : Int), (0 : Int)), ((4 : Int), (-2 : Int)), ((4 : Int), (-1 : Int)), ((4 : Int), (0 : Int)), ((5 : Int), (-2 : Int)), ((5 : Int), (-1 : Int)), ((5 : Int), (0 : Int))] < tilings (rectCells (6) 3) := by
  native_decide

-- (w=3, q=3, s=-1) area=18
example : tilings [((0 : Int), (0 : Int)), ((0 : Int), (1 : Int)), ((0 : Int), (2 : Int)), ((1 : Int), (0 : Int)), ((1 : Int), (1 : Int)), ((1 : Int), (2 : Int)), ((2 : Int), (0 : Int)), ((2 : Int), (1 : Int)), ((2 : Int), (2 : Int)), ((3 : Int), (-1 : Int)), ((3 : Int), (0 : Int)), ((3 : Int), (1 : Int)), ((4 : Int), (-1 : Int)), ((4 : Int), (0 : Int)), ((4 : Int), (1 : Int)), ((5 : Int), (-1 : Int)), ((5 : Int), (0 : Int)), ((5 : Int), (1 : Int))] < tilings (rectCells (6) 3) := by
  native_decide

-- (w=3, q=3, s=1) area=18
example : tilings [((0 : Int), (0 : Int)), ((0 : Int), (1 : Int)), ((0 : Int), (2 : Int)), ((1 : Int), (0 : Int)), ((1 : Int), (1 : Int)), ((1 : Int), (2 : Int)), ((2 : Int), (0 : Int)), ((2 : Int), (1 : Int)), ((2 : Int), (2 : Int)), ((3 : Int), (1 : Int)), ((3 : Int), (2 : Int)), ((3 : Int), (3 : Int)), ((4 : Int), (1 : Int)), ((4 : Int), (2 : Int)), ((4 : Int), (3 : Int)), ((5 : Int), (1 : Int)), ((5 : Int), (2 : Int)), ((5 : Int), (3 : Int))] < tilings (rectCells (6) 3) := by
  native_decide

-- (w=3, q=3, s=2) area=18
example : tilings [((0 : Int), (0 : Int)), ((0 : Int), (1 : Int)), ((0 : Int), (2 : Int)), ((1 : Int), (0 : Int)), ((1 : Int), (1 : Int)), ((1 : Int), (2 : Int)), ((2 : Int), (0 : Int)), ((2 : Int), (1 : Int)), ((2 : Int), (2 : Int)), ((3 : Int), (2 : Int)), ((3 : Int), (3 : Int)), ((3 : Int), (4 : Int)), ((4 : Int), (2 : Int)), ((4 : Int), (3 : Int)), ((4 : Int), (4 : Int)), ((5 : Int), (2 : Int)), ((5 : Int), (3 : Int)), ((5 : Int), (4 : Int))] < tilings (rectCells (6) 3) := by
  native_decide

-- (w=4, q=1, s=-3) area=8
example : tilings [((0 : Int), (0 : Int)), ((0 : Int), (1 : Int)), ((0 : Int), (2 : Int)), ((0 : Int), (3 : Int)), ((1 : Int), (-3 : Int)), ((1 : Int), (-2 : Int)), ((1 : Int), (-1 : Int)), ((1 : Int), (0 : Int))] < tilings (rectCells (2) 4) := by
  native_decide

-- (w=4, q=1, s=-2) area=8
example : tilings [((0 : Int), (0 : Int)), ((0 : Int), (1 : Int)), ((0 : Int), (2 : Int)), ((0 : Int), (3 : Int)), ((1 : Int), (-2 : Int)), ((1 : Int), (-1 : Int)), ((1 : Int), (0 : Int)), ((1 : Int), (1 : Int))] < tilings (rectCells (2) 4) := by
  native_decide

-- (w=4, q=1, s=-1) area=8
example : tilings [((0 : Int), (0 : Int)), ((0 : Int), (1 : Int)), ((0 : Int), (2 : Int)), ((0 : Int), (3 : Int)), ((1 : Int), (-1 : Int)), ((1 : Int), (0 : Int)), ((1 : Int), (1 : Int)), ((1 : Int), (2 : Int))] < tilings (rectCells (2) 4) := by
  native_decide

-- (w=4, q=1, s=1) area=8
example : tilings [((0 : Int), (0 : Int)), ((0 : Int), (1 : Int)), ((0 : Int), (2 : Int)), ((0 : Int), (3 : Int)), ((1 : Int), (1 : Int)), ((1 : Int), (2 : Int)), ((1 : Int), (3 : Int)), ((1 : Int), (4 : Int))] < tilings (rectCells (2) 4) := by
  native_decide

-- (w=4, q=1, s=2) area=8
example : tilings [((0 : Int), (0 : Int)), ((0 : Int), (1 : Int)), ((0 : Int), (2 : Int)), ((0 : Int), (3 : Int)), ((1 : Int), (2 : Int)), ((1 : Int), (3 : Int)), ((1 : Int), (4 : Int)), ((1 : Int), (5 : Int))] < tilings (rectCells (2) 4) := by
  native_decide

-- (w=4, q=1, s=3) area=8
example : tilings [((0 : Int), (0 : Int)), ((0 : Int), (1 : Int)), ((0 : Int), (2 : Int)), ((0 : Int), (3 : Int)), ((1 : Int), (3 : Int)), ((1 : Int), (4 : Int)), ((1 : Int), (5 : Int)), ((1 : Int), (6 : Int))] < tilings (rectCells (2) 4) := by
  native_decide

-- (w=4, q=2, s=-3) area=16
example : tilings [((0 : Int), (0 : Int)), ((0 : Int), (1 : Int)), ((0 : Int), (2 : Int)), ((0 : Int), (3 : Int)), ((1 : Int), (0 : Int)), ((1 : Int), (1 : Int)), ((1 : Int), (2 : Int)), ((1 : Int), (3 : Int)), ((2 : Int), (-3 : Int)), ((2 : Int), (-2 : Int)), ((2 : Int), (-1 : Int)), ((2 : Int), (0 : Int)), ((3 : Int), (-3 : Int)), ((3 : Int), (-2 : Int)), ((3 : Int), (-1 : Int)), ((3 : Int), (0 : Int))] < tilings (rectCells (4) 4) := by
  native_decide

-- (w=4, q=2, s=-2) area=16
example : tilings [((0 : Int), (0 : Int)), ((0 : Int), (1 : Int)), ((0 : Int), (2 : Int)), ((0 : Int), (3 : Int)), ((1 : Int), (0 : Int)), ((1 : Int), (1 : Int)), ((1 : Int), (2 : Int)), ((1 : Int), (3 : Int)), ((2 : Int), (-2 : Int)), ((2 : Int), (-1 : Int)), ((2 : Int), (0 : Int)), ((2 : Int), (1 : Int)), ((3 : Int), (-2 : Int)), ((3 : Int), (-1 : Int)), ((3 : Int), (0 : Int)), ((3 : Int), (1 : Int))] < tilings (rectCells (4) 4) := by
  native_decide

-- (w=4, q=2, s=-1) area=16
example : tilings [((0 : Int), (0 : Int)), ((0 : Int), (1 : Int)), ((0 : Int), (2 : Int)), ((0 : Int), (3 : Int)), ((1 : Int), (0 : Int)), ((1 : Int), (1 : Int)), ((1 : Int), (2 : Int)), ((1 : Int), (3 : Int)), ((2 : Int), (-1 : Int)), ((2 : Int), (0 : Int)), ((2 : Int), (1 : Int)), ((2 : Int), (2 : Int)), ((3 : Int), (-1 : Int)), ((3 : Int), (0 : Int)), ((3 : Int), (1 : Int)), ((3 : Int), (2 : Int))] < tilings (rectCells (4) 4) := by
  native_decide

-- (w=4, q=2, s=1) area=16
example : tilings [((0 : Int), (0 : Int)), ((0 : Int), (1 : Int)), ((0 : Int), (2 : Int)), ((0 : Int), (3 : Int)), ((1 : Int), (0 : Int)), ((1 : Int), (1 : Int)), ((1 : Int), (2 : Int)), ((1 : Int), (3 : Int)), ((2 : Int), (1 : Int)), ((2 : Int), (2 : Int)), ((2 : Int), (3 : Int)), ((2 : Int), (4 : Int)), ((3 : Int), (1 : Int)), ((3 : Int), (2 : Int)), ((3 : Int), (3 : Int)), ((3 : Int), (4 : Int))] < tilings (rectCells (4) 4) := by
  native_decide

-- (w=4, q=2, s=2) area=16
example : tilings [((0 : Int), (0 : Int)), ((0 : Int), (1 : Int)), ((0 : Int), (2 : Int)), ((0 : Int), (3 : Int)), ((1 : Int), (0 : Int)), ((1 : Int), (1 : Int)), ((1 : Int), (2 : Int)), ((1 : Int), (3 : Int)), ((2 : Int), (2 : Int)), ((2 : Int), (3 : Int)), ((2 : Int), (4 : Int)), ((2 : Int), (5 : Int)), ((3 : Int), (2 : Int)), ((3 : Int), (3 : Int)), ((3 : Int), (4 : Int)), ((3 : Int), (5 : Int))] < tilings (rectCells (4) 4) := by
  native_decide

-- (w=4, q=2, s=3) area=16
example : tilings [((0 : Int), (0 : Int)), ((0 : Int), (1 : Int)), ((0 : Int), (2 : Int)), ((0 : Int), (3 : Int)), ((1 : Int), (0 : Int)), ((1 : Int), (1 : Int)), ((1 : Int), (2 : Int)), ((1 : Int), (3 : Int)), ((2 : Int), (3 : Int)), ((2 : Int), (4 : Int)), ((2 : Int), (5 : Int)), ((2 : Int), (6 : Int)), ((3 : Int), (3 : Int)), ((3 : Int), (4 : Int)), ((3 : Int), (5 : Int)), ((3 : Int), (6 : Int))] < tilings (rectCells (4) 4) := by
  native_decide

-- (w=4, q=3, s=-3) area=24
example : tilings [((0 : Int), (0 : Int)), ((0 : Int), (1 : Int)), ((0 : Int), (2 : Int)), ((0 : Int), (3 : Int)), ((1 : Int), (0 : Int)), ((1 : Int), (1 : Int)), ((1 : Int), (2 : Int)), ((1 : Int), (3 : Int)), ((2 : Int), (0 : Int)), ((2 : Int), (1 : Int)), ((2 : Int), (2 : Int)), ((2 : Int), (3 : Int)), ((3 : Int), (-3 : Int)), ((3 : Int), (-2 : Int)), ((3 : Int), (-1 : Int)), ((3 : Int), (0 : Int)), ((4 : Int), (-3 : Int)), ((4 : Int), (-2 : Int)), ((4 : Int), (-1 : Int)), ((4 : Int), (0 : Int)), ((5 : Int), (-3 : Int)), ((5 : Int), (-2 : Int)), ((5 : Int), (-1 : Int)), ((5 : Int), (0 : Int))] < tilings (rectCells (6) 4) := by
  native_decide

-- (w=4, q=3, s=-2) area=24
example : tilings [((0 : Int), (0 : Int)), ((0 : Int), (1 : Int)), ((0 : Int), (2 : Int)), ((0 : Int), (3 : Int)), ((1 : Int), (0 : Int)), ((1 : Int), (1 : Int)), ((1 : Int), (2 : Int)), ((1 : Int), (3 : Int)), ((2 : Int), (0 : Int)), ((2 : Int), (1 : Int)), ((2 : Int), (2 : Int)), ((2 : Int), (3 : Int)), ((3 : Int), (-2 : Int)), ((3 : Int), (-1 : Int)), ((3 : Int), (0 : Int)), ((3 : Int), (1 : Int)), ((4 : Int), (-2 : Int)), ((4 : Int), (-1 : Int)), ((4 : Int), (0 : Int)), ((4 : Int), (1 : Int)), ((5 : Int), (-2 : Int)), ((5 : Int), (-1 : Int)), ((5 : Int), (0 : Int)), ((5 : Int), (1 : Int))] < tilings (rectCells (6) 4) := by
  native_decide

-- (w=4, q=3, s=-1) area=24
example : tilings [((0 : Int), (0 : Int)), ((0 : Int), (1 : Int)), ((0 : Int), (2 : Int)), ((0 : Int), (3 : Int)), ((1 : Int), (0 : Int)), ((1 : Int), (1 : Int)), ((1 : Int), (2 : Int)), ((1 : Int), (3 : Int)), ((2 : Int), (0 : Int)), ((2 : Int), (1 : Int)), ((2 : Int), (2 : Int)), ((2 : Int), (3 : Int)), ((3 : Int), (-1 : Int)), ((3 : Int), (0 : Int)), ((3 : Int), (1 : Int)), ((3 : Int), (2 : Int)), ((4 : Int), (-1 : Int)), ((4 : Int), (0 : Int)), ((4 : Int), (1 : Int)), ((4 : Int), (2 : Int)), ((5 : Int), (-1 : Int)), ((5 : Int), (0 : Int)), ((5 : Int), (1 : Int)), ((5 : Int), (2 : Int))] < tilings (rectCells (6) 4) := by
  native_decide

-- (w=4, q=3, s=1) area=24
example : tilings [((0 : Int), (0 : Int)), ((0 : Int), (1 : Int)), ((0 : Int), (2 : Int)), ((0 : Int), (3 : Int)), ((1 : Int), (0 : Int)), ((1 : Int), (1 : Int)), ((1 : Int), (2 : Int)), ((1 : Int), (3 : Int)), ((2 : Int), (0 : Int)), ((2 : Int), (1 : Int)), ((2 : Int), (2 : Int)), ((2 : Int), (3 : Int)), ((3 : Int), (1 : Int)), ((3 : Int), (2 : Int)), ((3 : Int), (3 : Int)), ((3 : Int), (4 : Int)), ((4 : Int), (1 : Int)), ((4 : Int), (2 : Int)), ((4 : Int), (3 : Int)), ((4 : Int), (4 : Int)), ((5 : Int), (1 : Int)), ((5 : Int), (2 : Int)), ((5 : Int), (3 : Int)), ((5 : Int), (4 : Int))] < tilings (rectCells (6) 4) := by
  native_decide

-- (w=4, q=3, s=2) area=24
example : tilings [((0 : Int), (0 : Int)), ((0 : Int), (1 : Int)), ((0 : Int), (2 : Int)), ((0 : Int), (3 : Int)), ((1 : Int), (0 : Int)), ((1 : Int), (1 : Int)), ((1 : Int), (2 : Int)), ((1 : Int), (3 : Int)), ((2 : Int), (0 : Int)), ((2 : Int), (1 : Int)), ((2 : Int), (2 : Int)), ((2 : Int), (3 : Int)), ((3 : Int), (2 : Int)), ((3 : Int), (3 : Int)), ((3 : Int), (4 : Int)), ((3 : Int), (5 : Int)), ((4 : Int), (2 : Int)), ((4 : Int), (3 : Int)), ((4 : Int), (4 : Int)), ((4 : Int), (5 : Int)), ((5 : Int), (2 : Int)), ((5 : Int), (3 : Int)), ((5 : Int), (4 : Int)), ((5 : Int), (5 : Int))] < tilings (rectCells (6) 4) := by
  native_decide

-- (w=4, q=3, s=3) area=24
example : tilings [((0 : Int), (0 : Int)), ((0 : Int), (1 : Int)), ((0 : Int), (2 : Int)), ((0 : Int), (3 : Int)), ((1 : Int), (0 : Int)), ((1 : Int), (1 : Int)), ((1 : Int), (2 : Int)), ((1 : Int), (3 : Int)), ((2 : Int), (0 : Int)), ((2 : Int), (1 : Int)), ((2 : Int), (2 : Int)), ((2 : Int), (3 : Int)), ((3 : Int), (3 : Int)), ((3 : Int), (4 : Int)), ((3 : Int), (5 : Int)), ((3 : Int), (6 : Int)), ((4 : Int), (3 : Int)), ((4 : Int), (4 : Int)), ((4 : Int), (5 : Int)), ((4 : Int), (6 : Int)), ((5 : Int), (3 : Int)), ((5 : Int), (4 : Int)), ((5 : Int), (5 : Int)), ((5 : Int), (6 : Int))] < tilings (rectCells (6) 4) := by
  native_decide

-- (w=5, q=1, s=-4) area=10
example : tilings [((0 : Int), (0 : Int)), ((0 : Int), (1 : Int)), ((0 : Int), (2 : Int)), ((0 : Int), (3 : Int)), ((0 : Int), (4 : Int)), ((1 : Int), (-4 : Int)), ((1 : Int), (-3 : Int)), ((1 : Int), (-2 : Int)), ((1 : Int), (-1 : Int)), ((1 : Int), (0 : Int))] < tilings (rectCells (2) 5) := by
  native_decide

-- (w=5, q=1, s=-3) area=10
example : tilings [((0 : Int), (0 : Int)), ((0 : Int), (1 : Int)), ((0 : Int), (2 : Int)), ((0 : Int), (3 : Int)), ((0 : Int), (4 : Int)), ((1 : Int), (-3 : Int)), ((1 : Int), (-2 : Int)), ((1 : Int), (-1 : Int)), ((1 : Int), (0 : Int)), ((1 : Int), (1 : Int))] < tilings (rectCells (2) 5) := by
  native_decide

-- (w=5, q=1, s=-2) area=10
example : tilings [((0 : Int), (0 : Int)), ((0 : Int), (1 : Int)), ((0 : Int), (2 : Int)), ((0 : Int), (3 : Int)), ((0 : Int), (4 : Int)), ((1 : Int), (-2 : Int)), ((1 : Int), (-1 : Int)), ((1 : Int), (0 : Int)), ((1 : Int), (1 : Int)), ((1 : Int), (2 : Int))] < tilings (rectCells (2) 5) := by
  native_decide

-- (w=5, q=1, s=-1) area=10
example : tilings [((0 : Int), (0 : Int)), ((0 : Int), (1 : Int)), ((0 : Int), (2 : Int)), ((0 : Int), (3 : Int)), ((0 : Int), (4 : Int)), ((1 : Int), (-1 : Int)), ((1 : Int), (0 : Int)), ((1 : Int), (1 : Int)), ((1 : Int), (2 : Int)), ((1 : Int), (3 : Int))] < tilings (rectCells (2) 5) := by
  native_decide

-- (w=5, q=1, s=1) area=10
example : tilings [((0 : Int), (0 : Int)), ((0 : Int), (1 : Int)), ((0 : Int), (2 : Int)), ((0 : Int), (3 : Int)), ((0 : Int), (4 : Int)), ((1 : Int), (1 : Int)), ((1 : Int), (2 : Int)), ((1 : Int), (3 : Int)), ((1 : Int), (4 : Int)), ((1 : Int), (5 : Int))] < tilings (rectCells (2) 5) := by
  native_decide

-- (w=5, q=1, s=2) area=10
example : tilings [((0 : Int), (0 : Int)), ((0 : Int), (1 : Int)), ((0 : Int), (2 : Int)), ((0 : Int), (3 : Int)), ((0 : Int), (4 : Int)), ((1 : Int), (2 : Int)), ((1 : Int), (3 : Int)), ((1 : Int), (4 : Int)), ((1 : Int), (5 : Int)), ((1 : Int), (6 : Int))] < tilings (rectCells (2) 5) := by
  native_decide

-- (w=5, q=1, s=3) area=10
example : tilings [((0 : Int), (0 : Int)), ((0 : Int), (1 : Int)), ((0 : Int), (2 : Int)), ((0 : Int), (3 : Int)), ((0 : Int), (4 : Int)), ((1 : Int), (3 : Int)), ((1 : Int), (4 : Int)), ((1 : Int), (5 : Int)), ((1 : Int), (6 : Int)), ((1 : Int), (7 : Int))] < tilings (rectCells (2) 5) := by
  native_decide

-- (w=5, q=1, s=4) area=10
example : tilings [((0 : Int), (0 : Int)), ((0 : Int), (1 : Int)), ((0 : Int), (2 : Int)), ((0 : Int), (3 : Int)), ((0 : Int), (4 : Int)), ((1 : Int), (4 : Int)), ((1 : Int), (5 : Int)), ((1 : Int), (6 : Int)), ((1 : Int), (7 : Int)), ((1 : Int), (8 : Int))] < tilings (rectCells (2) 5) := by
  native_decide

-- (w=5, q=2, s=-4) area=20
example : tilings [((0 : Int), (0 : Int)), ((0 : Int), (1 : Int)), ((0 : Int), (2 : Int)), ((0 : Int), (3 : Int)), ((0 : Int), (4 : Int)), ((1 : Int), (0 : Int)), ((1 : Int), (1 : Int)), ((1 : Int), (2 : Int)), ((1 : Int), (3 : Int)), ((1 : Int), (4 : Int)), ((2 : Int), (-4 : Int)), ((2 : Int), (-3 : Int)), ((2 : Int), (-2 : Int)), ((2 : Int), (-1 : Int)), ((2 : Int), (0 : Int)), ((3 : Int), (-4 : Int)), ((3 : Int), (-3 : Int)), ((3 : Int), (-2 : Int)), ((3 : Int), (-1 : Int)), ((3 : Int), (0 : Int))] < tilings (rectCells (4) 5) := by
  native_decide

-- (w=5, q=2, s=-3) area=20
example : tilings [((0 : Int), (0 : Int)), ((0 : Int), (1 : Int)), ((0 : Int), (2 : Int)), ((0 : Int), (3 : Int)), ((0 : Int), (4 : Int)), ((1 : Int), (0 : Int)), ((1 : Int), (1 : Int)), ((1 : Int), (2 : Int)), ((1 : Int), (3 : Int)), ((1 : Int), (4 : Int)), ((2 : Int), (-3 : Int)), ((2 : Int), (-2 : Int)), ((2 : Int), (-1 : Int)), ((2 : Int), (0 : Int)), ((2 : Int), (1 : Int)), ((3 : Int), (-3 : Int)), ((3 : Int), (-2 : Int)), ((3 : Int), (-1 : Int)), ((3 : Int), (0 : Int)), ((3 : Int), (1 : Int))] < tilings (rectCells (4) 5) := by
  native_decide

-- (w=5, q=2, s=-2) area=20
example : tilings [((0 : Int), (0 : Int)), ((0 : Int), (1 : Int)), ((0 : Int), (2 : Int)), ((0 : Int), (3 : Int)), ((0 : Int), (4 : Int)), ((1 : Int), (0 : Int)), ((1 : Int), (1 : Int)), ((1 : Int), (2 : Int)), ((1 : Int), (3 : Int)), ((1 : Int), (4 : Int)), ((2 : Int), (-2 : Int)), ((2 : Int), (-1 : Int)), ((2 : Int), (0 : Int)), ((2 : Int), (1 : Int)), ((2 : Int), (2 : Int)), ((3 : Int), (-2 : Int)), ((3 : Int), (-1 : Int)), ((3 : Int), (0 : Int)), ((3 : Int), (1 : Int)), ((3 : Int), (2 : Int))] < tilings (rectCells (4) 5) := by
  native_decide

-- (w=5, q=2, s=-1) area=20
example : tilings [((0 : Int), (0 : Int)), ((0 : Int), (1 : Int)), ((0 : Int), (2 : Int)), ((0 : Int), (3 : Int)), ((0 : Int), (4 : Int)), ((1 : Int), (0 : Int)), ((1 : Int), (1 : Int)), ((1 : Int), (2 : Int)), ((1 : Int), (3 : Int)), ((1 : Int), (4 : Int)), ((2 : Int), (-1 : Int)), ((2 : Int), (0 : Int)), ((2 : Int), (1 : Int)), ((2 : Int), (2 : Int)), ((2 : Int), (3 : Int)), ((3 : Int), (-1 : Int)), ((3 : Int), (0 : Int)), ((3 : Int), (1 : Int)), ((3 : Int), (2 : Int)), ((3 : Int), (3 : Int))] < tilings (rectCells (4) 5) := by
  native_decide

-- (w=5, q=2, s=1) area=20
example : tilings [((0 : Int), (0 : Int)), ((0 : Int), (1 : Int)), ((0 : Int), (2 : Int)), ((0 : Int), (3 : Int)), ((0 : Int), (4 : Int)), ((1 : Int), (0 : Int)), ((1 : Int), (1 : Int)), ((1 : Int), (2 : Int)), ((1 : Int), (3 : Int)), ((1 : Int), (4 : Int)), ((2 : Int), (1 : Int)), ((2 : Int), (2 : Int)), ((2 : Int), (3 : Int)), ((2 : Int), (4 : Int)), ((2 : Int), (5 : Int)), ((3 : Int), (1 : Int)), ((3 : Int), (2 : Int)), ((3 : Int), (3 : Int)), ((3 : Int), (4 : Int)), ((3 : Int), (5 : Int))] < tilings (rectCells (4) 5) := by
  native_decide

-- (w=5, q=2, s=2) area=20
example : tilings [((0 : Int), (0 : Int)), ((0 : Int), (1 : Int)), ((0 : Int), (2 : Int)), ((0 : Int), (3 : Int)), ((0 : Int), (4 : Int)), ((1 : Int), (0 : Int)), ((1 : Int), (1 : Int)), ((1 : Int), (2 : Int)), ((1 : Int), (3 : Int)), ((1 : Int), (4 : Int)), ((2 : Int), (2 : Int)), ((2 : Int), (3 : Int)), ((2 : Int), (4 : Int)), ((2 : Int), (5 : Int)), ((2 : Int), (6 : Int)), ((3 : Int), (2 : Int)), ((3 : Int), (3 : Int)), ((3 : Int), (4 : Int)), ((3 : Int), (5 : Int)), ((3 : Int), (6 : Int))] < tilings (rectCells (4) 5) := by
  native_decide

-- (w=5, q=2, s=3) area=20
example : tilings [((0 : Int), (0 : Int)), ((0 : Int), (1 : Int)), ((0 : Int), (2 : Int)), ((0 : Int), (3 : Int)), ((0 : Int), (4 : Int)), ((1 : Int), (0 : Int)), ((1 : Int), (1 : Int)), ((1 : Int), (2 : Int)), ((1 : Int), (3 : Int)), ((1 : Int), (4 : Int)), ((2 : Int), (3 : Int)), ((2 : Int), (4 : Int)), ((2 : Int), (5 : Int)), ((2 : Int), (6 : Int)), ((2 : Int), (7 : Int)), ((3 : Int), (3 : Int)), ((3 : Int), (4 : Int)), ((3 : Int), (5 : Int)), ((3 : Int), (6 : Int)), ((3 : Int), (7 : Int))] < tilings (rectCells (4) 5) := by
  native_decide

-- (w=5, q=2, s=4) area=20
example : tilings [((0 : Int), (0 : Int)), ((0 : Int), (1 : Int)), ((0 : Int), (2 : Int)), ((0 : Int), (3 : Int)), ((0 : Int), (4 : Int)), ((1 : Int), (0 : Int)), ((1 : Int), (1 : Int)), ((1 : Int), (2 : Int)), ((1 : Int), (3 : Int)), ((1 : Int), (4 : Int)), ((2 : Int), (4 : Int)), ((2 : Int), (5 : Int)), ((2 : Int), (6 : Int)), ((2 : Int), (7 : Int)), ((2 : Int), (8 : Int)), ((3 : Int), (4 : Int)), ((3 : Int), (5 : Int)), ((3 : Int), (6 : Int)), ((3 : Int), (7 : Int)), ((3 : Int), (8 : Int))] < tilings (rectCells (4) 5) := by
  native_decide

-- (w=5, q=3, s=-4) area=30
example : tilings [((0 : Int), (0 : Int)), ((0 : Int), (1 : Int)), ((0 : Int), (2 : Int)), ((0 : Int), (3 : Int)), ((0 : Int), (4 : Int)), ((1 : Int), (0 : Int)), ((1 : Int), (1 : Int)), ((1 : Int), (2 : Int)), ((1 : Int), (3 : Int)), ((1 : Int), (4 : Int)), ((2 : Int), (0 : Int)), ((2 : Int), (1 : Int)), ((2 : Int), (2 : Int)), ((2 : Int), (3 : Int)), ((2 : Int), (4 : Int)), ((3 : Int), (-4 : Int)), ((3 : Int), (-3 : Int)), ((3 : Int), (-2 : Int)), ((3 : Int), (-1 : Int)), ((3 : Int), (0 : Int)), ((4 : Int), (-4 : Int)), ((4 : Int), (-3 : Int)), ((4 : Int), (-2 : Int)), ((4 : Int), (-1 : Int)), ((4 : Int), (0 : Int)), ((5 : Int), (-4 : Int)), ((5 : Int), (-3 : Int)), ((5 : Int), (-2 : Int)), ((5 : Int), (-1 : Int)), ((5 : Int), (0 : Int))] < tilings (rectCells (6) 5) := by
  native_decide

-- (w=5, q=3, s=-3) area=30
example : tilings [((0 : Int), (0 : Int)), ((0 : Int), (1 : Int)), ((0 : Int), (2 : Int)), ((0 : Int), (3 : Int)), ((0 : Int), (4 : Int)), ((1 : Int), (0 : Int)), ((1 : Int), (1 : Int)), ((1 : Int), (2 : Int)), ((1 : Int), (3 : Int)), ((1 : Int), (4 : Int)), ((2 : Int), (0 : Int)), ((2 : Int), (1 : Int)), ((2 : Int), (2 : Int)), ((2 : Int), (3 : Int)), ((2 : Int), (4 : Int)), ((3 : Int), (-3 : Int)), ((3 : Int), (-2 : Int)), ((3 : Int), (-1 : Int)), ((3 : Int), (0 : Int)), ((3 : Int), (1 : Int)), ((4 : Int), (-3 : Int)), ((4 : Int), (-2 : Int)), ((4 : Int), (-1 : Int)), ((4 : Int), (0 : Int)), ((4 : Int), (1 : Int)), ((5 : Int), (-3 : Int)), ((5 : Int), (-2 : Int)), ((5 : Int), (-1 : Int)), ((5 : Int), (0 : Int)), ((5 : Int), (1 : Int))] < tilings (rectCells (6) 5) := by
  native_decide

-- (w=5, q=3, s=-2) area=30
example : tilings [((0 : Int), (0 : Int)), ((0 : Int), (1 : Int)), ((0 : Int), (2 : Int)), ((0 : Int), (3 : Int)), ((0 : Int), (4 : Int)), ((1 : Int), (0 : Int)), ((1 : Int), (1 : Int)), ((1 : Int), (2 : Int)), ((1 : Int), (3 : Int)), ((1 : Int), (4 : Int)), ((2 : Int), (0 : Int)), ((2 : Int), (1 : Int)), ((2 : Int), (2 : Int)), ((2 : Int), (3 : Int)), ((2 : Int), (4 : Int)), ((3 : Int), (-2 : Int)), ((3 : Int), (-1 : Int)), ((3 : Int), (0 : Int)), ((3 : Int), (1 : Int)), ((3 : Int), (2 : Int)), ((4 : Int), (-2 : Int)), ((4 : Int), (-1 : Int)), ((4 : Int), (0 : Int)), ((4 : Int), (1 : Int)), ((4 : Int), (2 : Int)), ((5 : Int), (-2 : Int)), ((5 : Int), (-1 : Int)), ((5 : Int), (0 : Int)), ((5 : Int), (1 : Int)), ((5 : Int), (2 : Int))] < tilings (rectCells (6) 5) := by
  native_decide

-- (w=5, q=3, s=-1) area=30
example : tilings [((0 : Int), (0 : Int)), ((0 : Int), (1 : Int)), ((0 : Int), (2 : Int)), ((0 : Int), (3 : Int)), ((0 : Int), (4 : Int)), ((1 : Int), (0 : Int)), ((1 : Int), (1 : Int)), ((1 : Int), (2 : Int)), ((1 : Int), (3 : Int)), ((1 : Int), (4 : Int)), ((2 : Int), (0 : Int)), ((2 : Int), (1 : Int)), ((2 : Int), (2 : Int)), ((2 : Int), (3 : Int)), ((2 : Int), (4 : Int)), ((3 : Int), (-1 : Int)), ((3 : Int), (0 : Int)), ((3 : Int), (1 : Int)), ((3 : Int), (2 : Int)), ((3 : Int), (3 : Int)), ((4 : Int), (-1 : Int)), ((4 : Int), (0 : Int)), ((4 : Int), (1 : Int)), ((4 : Int), (2 : Int)), ((4 : Int), (3 : Int)), ((5 : Int), (-1 : Int)), ((5 : Int), (0 : Int)), ((5 : Int), (1 : Int)), ((5 : Int), (2 : Int)), ((5 : Int), (3 : Int))] < tilings (rectCells (6) 5) := by
  native_decide

-- (w=5, q=3, s=1) area=30
example : tilings [((0 : Int), (0 : Int)), ((0 : Int), (1 : Int)), ((0 : Int), (2 : Int)), ((0 : Int), (3 : Int)), ((0 : Int), (4 : Int)), ((1 : Int), (0 : Int)), ((1 : Int), (1 : Int)), ((1 : Int), (2 : Int)), ((1 : Int), (3 : Int)), ((1 : Int), (4 : Int)), ((2 : Int), (0 : Int)), ((2 : Int), (1 : Int)), ((2 : Int), (2 : Int)), ((2 : Int), (3 : Int)), ((2 : Int), (4 : Int)), ((3 : Int), (1 : Int)), ((3 : Int), (2 : Int)), ((3 : Int), (3 : Int)), ((3 : Int), (4 : Int)), ((3 : Int), (5 : Int)), ((4 : Int), (1 : Int)), ((4 : Int), (2 : Int)), ((4 : Int), (3 : Int)), ((4 : Int), (4 : Int)), ((4 : Int), (5 : Int)), ((5 : Int), (1 : Int)), ((5 : Int), (2 : Int)), ((5 : Int), (3 : Int)), ((5 : Int), (4 : Int)), ((5 : Int), (5 : Int))] < tilings (rectCells (6) 5) := by
  native_decide

-- (w=5, q=3, s=2) area=30
example : tilings [((0 : Int), (0 : Int)), ((0 : Int), (1 : Int)), ((0 : Int), (2 : Int)), ((0 : Int), (3 : Int)), ((0 : Int), (4 : Int)), ((1 : Int), (0 : Int)), ((1 : Int), (1 : Int)), ((1 : Int), (2 : Int)), ((1 : Int), (3 : Int)), ((1 : Int), (4 : Int)), ((2 : Int), (0 : Int)), ((2 : Int), (1 : Int)), ((2 : Int), (2 : Int)), ((2 : Int), (3 : Int)), ((2 : Int), (4 : Int)), ((3 : Int), (2 : Int)), ((3 : Int), (3 : Int)), ((3 : Int), (4 : Int)), ((3 : Int), (5 : Int)), ((3 : Int), (6 : Int)), ((4 : Int), (2 : Int)), ((4 : Int), (3 : Int)), ((4 : Int), (4 : Int)), ((4 : Int), (5 : Int)), ((4 : Int), (6 : Int)), ((5 : Int), (2 : Int)), ((5 : Int), (3 : Int)), ((5 : Int), (4 : Int)), ((5 : Int), (5 : Int)), ((5 : Int), (6 : Int))] < tilings (rectCells (6) 5) := by
  native_decide

-- (w=5, q=3, s=3) area=30
example : tilings [((0 : Int), (0 : Int)), ((0 : Int), (1 : Int)), ((0 : Int), (2 : Int)), ((0 : Int), (3 : Int)), ((0 : Int), (4 : Int)), ((1 : Int), (0 : Int)), ((1 : Int), (1 : Int)), ((1 : Int), (2 : Int)), ((1 : Int), (3 : Int)), ((1 : Int), (4 : Int)), ((2 : Int), (0 : Int)), ((2 : Int), (1 : Int)), ((2 : Int), (2 : Int)), ((2 : Int), (3 : Int)), ((2 : Int), (4 : Int)), ((3 : Int), (3 : Int)), ((3 : Int), (4 : Int)), ((3 : Int), (5 : Int)), ((3 : Int), (6 : Int)), ((3 : Int), (7 : Int)), ((4 : Int), (3 : Int)), ((4 : Int), (4 : Int)), ((4 : Int), (5 : Int)), ((4 : Int), (6 : Int)), ((4 : Int), (7 : Int)), ((5 : Int), (3 : Int)), ((5 : Int), (4 : Int)), ((5 : Int), (5 : Int)), ((5 : Int), (6 : Int)), ((5 : Int), (7 : Int))] < tilings (rectCells (6) 5) := by
  native_decide

-- (w=5, q=3, s=4) area=30
example : tilings [((0 : Int), (0 : Int)), ((0 : Int), (1 : Int)), ((0 : Int), (2 : Int)), ((0 : Int), (3 : Int)), ((0 : Int), (4 : Int)), ((1 : Int), (0 : Int)), ((1 : Int), (1 : Int)), ((1 : Int), (2 : Int)), ((1 : Int), (3 : Int)), ((1 : Int), (4 : Int)), ((2 : Int), (0 : Int)), ((2 : Int), (1 : Int)), ((2 : Int), (2 : Int)), ((2 : Int), (3 : Int)), ((2 : Int), (4 : Int)), ((3 : Int), (4 : Int)), ((3 : Int), (5 : Int)), ((3 : Int), (6 : Int)), ((3 : Int), (7 : Int)), ((3 : Int), (8 : Int)), ((4 : Int), (4 : Int)), ((4 : Int), (5 : Int)), ((4 : Int), (6 : Int)), ((4 : Int), (7 : Int)), ((4 : Int), (8 : Int)), ((5 : Int), (4 : Int)), ((5 : Int), (5 : Int)), ((5 : Int), (6 : Int)), ((5 : Int), (7 : Int)), ((5 : Int), (8 : Int))] < tilings (rectCells (6) 5) := by
  native_decide

-- (w=6, q=1, s=-5) area=12
example : tilings [((0 : Int), (0 : Int)), ((0 : Int), (1 : Int)), ((0 : Int), (2 : Int)), ((0 : Int), (3 : Int)), ((0 : Int), (4 : Int)), ((0 : Int), (5 : Int)), ((1 : Int), (-5 : Int)), ((1 : Int), (-4 : Int)), ((1 : Int), (-3 : Int)), ((1 : Int), (-2 : Int)), ((1 : Int), (-1 : Int)), ((1 : Int), (0 : Int))] < tilings (rectCells (2) 6) := by
  native_decide

-- (w=6, q=1, s=-4) area=12
example : tilings [((0 : Int), (0 : Int)), ((0 : Int), (1 : Int)), ((0 : Int), (2 : Int)), ((0 : Int), (3 : Int)), ((0 : Int), (4 : Int)), ((0 : Int), (5 : Int)), ((1 : Int), (-4 : Int)), ((1 : Int), (-3 : Int)), ((1 : Int), (-2 : Int)), ((1 : Int), (-1 : Int)), ((1 : Int), (0 : Int)), ((1 : Int), (1 : Int))] < tilings (rectCells (2) 6) := by
  native_decide

-- (w=6, q=1, s=-3) area=12
example : tilings [((0 : Int), (0 : Int)), ((0 : Int), (1 : Int)), ((0 : Int), (2 : Int)), ((0 : Int), (3 : Int)), ((0 : Int), (4 : Int)), ((0 : Int), (5 : Int)), ((1 : Int), (-3 : Int)), ((1 : Int), (-2 : Int)), ((1 : Int), (-1 : Int)), ((1 : Int), (0 : Int)), ((1 : Int), (1 : Int)), ((1 : Int), (2 : Int))] < tilings (rectCells (2) 6) := by
  native_decide

-- (w=6, q=1, s=-2) area=12
example : tilings [((0 : Int), (0 : Int)), ((0 : Int), (1 : Int)), ((0 : Int), (2 : Int)), ((0 : Int), (3 : Int)), ((0 : Int), (4 : Int)), ((0 : Int), (5 : Int)), ((1 : Int), (-2 : Int)), ((1 : Int), (-1 : Int)), ((1 : Int), (0 : Int)), ((1 : Int), (1 : Int)), ((1 : Int), (2 : Int)), ((1 : Int), (3 : Int))] < tilings (rectCells (2) 6) := by
  native_decide

-- (w=6, q=1, s=-1) area=12
example : tilings [((0 : Int), (0 : Int)), ((0 : Int), (1 : Int)), ((0 : Int), (2 : Int)), ((0 : Int), (3 : Int)), ((0 : Int), (4 : Int)), ((0 : Int), (5 : Int)), ((1 : Int), (-1 : Int)), ((1 : Int), (0 : Int)), ((1 : Int), (1 : Int)), ((1 : Int), (2 : Int)), ((1 : Int), (3 : Int)), ((1 : Int), (4 : Int))] < tilings (rectCells (2) 6) := by
  native_decide

-- (w=6, q=1, s=1) area=12
example : tilings [((0 : Int), (0 : Int)), ((0 : Int), (1 : Int)), ((0 : Int), (2 : Int)), ((0 : Int), (3 : Int)), ((0 : Int), (4 : Int)), ((0 : Int), (5 : Int)), ((1 : Int), (1 : Int)), ((1 : Int), (2 : Int)), ((1 : Int), (3 : Int)), ((1 : Int), (4 : Int)), ((1 : Int), (5 : Int)), ((1 : Int), (6 : Int))] < tilings (rectCells (2) 6) := by
  native_decide

-- (w=6, q=1, s=2) area=12
example : tilings [((0 : Int), (0 : Int)), ((0 : Int), (1 : Int)), ((0 : Int), (2 : Int)), ((0 : Int), (3 : Int)), ((0 : Int), (4 : Int)), ((0 : Int), (5 : Int)), ((1 : Int), (2 : Int)), ((1 : Int), (3 : Int)), ((1 : Int), (4 : Int)), ((1 : Int), (5 : Int)), ((1 : Int), (6 : Int)), ((1 : Int), (7 : Int))] < tilings (rectCells (2) 6) := by
  native_decide

-- (w=6, q=1, s=3) area=12
example : tilings [((0 : Int), (0 : Int)), ((0 : Int), (1 : Int)), ((0 : Int), (2 : Int)), ((0 : Int), (3 : Int)), ((0 : Int), (4 : Int)), ((0 : Int), (5 : Int)), ((1 : Int), (3 : Int)), ((1 : Int), (4 : Int)), ((1 : Int), (5 : Int)), ((1 : Int), (6 : Int)), ((1 : Int), (7 : Int)), ((1 : Int), (8 : Int))] < tilings (rectCells (2) 6) := by
  native_decide

-- (w=6, q=1, s=4) area=12
example : tilings [((0 : Int), (0 : Int)), ((0 : Int), (1 : Int)), ((0 : Int), (2 : Int)), ((0 : Int), (3 : Int)), ((0 : Int), (4 : Int)), ((0 : Int), (5 : Int)), ((1 : Int), (4 : Int)), ((1 : Int), (5 : Int)), ((1 : Int), (6 : Int)), ((1 : Int), (7 : Int)), ((1 : Int), (8 : Int)), ((1 : Int), (9 : Int))] < tilings (rectCells (2) 6) := by
  native_decide

-- (w=6, q=1, s=5) area=12
example : tilings [((0 : Int), (0 : Int)), ((0 : Int), (1 : Int)), ((0 : Int), (2 : Int)), ((0 : Int), (3 : Int)), ((0 : Int), (4 : Int)), ((0 : Int), (5 : Int)), ((1 : Int), (5 : Int)), ((1 : Int), (6 : Int)), ((1 : Int), (7 : Int)), ((1 : Int), (8 : Int)), ((1 : Int), (9 : Int)), ((1 : Int), (10 : Int))] < tilings (rectCells (2) 6) := by
  native_decide

-- (w=6, q=2, s=-5) area=24
example : tilings [((0 : Int), (0 : Int)), ((0 : Int), (1 : Int)), ((0 : Int), (2 : Int)), ((0 : Int), (3 : Int)), ((0 : Int), (4 : Int)), ((0 : Int), (5 : Int)), ((1 : Int), (0 : Int)), ((1 : Int), (1 : Int)), ((1 : Int), (2 : Int)), ((1 : Int), (3 : Int)), ((1 : Int), (4 : Int)), ((1 : Int), (5 : Int)), ((2 : Int), (-5 : Int)), ((2 : Int), (-4 : Int)), ((2 : Int), (-3 : Int)), ((2 : Int), (-2 : Int)), ((2 : Int), (-1 : Int)), ((2 : Int), (0 : Int)), ((3 : Int), (-5 : Int)), ((3 : Int), (-4 : Int)), ((3 : Int), (-3 : Int)), ((3 : Int), (-2 : Int)), ((3 : Int), (-1 : Int)), ((3 : Int), (0 : Int))] < tilings (rectCells (4) 6) := by
  native_decide

-- (w=6, q=2, s=-4) area=24
example : tilings [((0 : Int), (0 : Int)), ((0 : Int), (1 : Int)), ((0 : Int), (2 : Int)), ((0 : Int), (3 : Int)), ((0 : Int), (4 : Int)), ((0 : Int), (5 : Int)), ((1 : Int), (0 : Int)), ((1 : Int), (1 : Int)), ((1 : Int), (2 : Int)), ((1 : Int), (3 : Int)), ((1 : Int), (4 : Int)), ((1 : Int), (5 : Int)), ((2 : Int), (-4 : Int)), ((2 : Int), (-3 : Int)), ((2 : Int), (-2 : Int)), ((2 : Int), (-1 : Int)), ((2 : Int), (0 : Int)), ((2 : Int), (1 : Int)), ((3 : Int), (-4 : Int)), ((3 : Int), (-3 : Int)), ((3 : Int), (-2 : Int)), ((3 : Int), (-1 : Int)), ((3 : Int), (0 : Int)), ((3 : Int), (1 : Int))] < tilings (rectCells (4) 6) := by
  native_decide

-- (w=6, q=2, s=-3) area=24
example : tilings [((0 : Int), (0 : Int)), ((0 : Int), (1 : Int)), ((0 : Int), (2 : Int)), ((0 : Int), (3 : Int)), ((0 : Int), (4 : Int)), ((0 : Int), (5 : Int)), ((1 : Int), (0 : Int)), ((1 : Int), (1 : Int)), ((1 : Int), (2 : Int)), ((1 : Int), (3 : Int)), ((1 : Int), (4 : Int)), ((1 : Int), (5 : Int)), ((2 : Int), (-3 : Int)), ((2 : Int), (-2 : Int)), ((2 : Int), (-1 : Int)), ((2 : Int), (0 : Int)), ((2 : Int), (1 : Int)), ((2 : Int), (2 : Int)), ((3 : Int), (-3 : Int)), ((3 : Int), (-2 : Int)), ((3 : Int), (-1 : Int)), ((3 : Int), (0 : Int)), ((3 : Int), (1 : Int)), ((3 : Int), (2 : Int))] < tilings (rectCells (4) 6) := by
  native_decide

-- (w=6, q=2, s=-2) area=24
example : tilings [((0 : Int), (0 : Int)), ((0 : Int), (1 : Int)), ((0 : Int), (2 : Int)), ((0 : Int), (3 : Int)), ((0 : Int), (4 : Int)), ((0 : Int), (5 : Int)), ((1 : Int), (0 : Int)), ((1 : Int), (1 : Int)), ((1 : Int), (2 : Int)), ((1 : Int), (3 : Int)), ((1 : Int), (4 : Int)), ((1 : Int), (5 : Int)), ((2 : Int), (-2 : Int)), ((2 : Int), (-1 : Int)), ((2 : Int), (0 : Int)), ((2 : Int), (1 : Int)), ((2 : Int), (2 : Int)), ((2 : Int), (3 : Int)), ((3 : Int), (-2 : Int)), ((3 : Int), (-1 : Int)), ((3 : Int), (0 : Int)), ((3 : Int), (1 : Int)), ((3 : Int), (2 : Int)), ((3 : Int), (3 : Int))] < tilings (rectCells (4) 6) := by
  native_decide

-- (w=6, q=2, s=-1) area=24
example : tilings [((0 : Int), (0 : Int)), ((0 : Int), (1 : Int)), ((0 : Int), (2 : Int)), ((0 : Int), (3 : Int)), ((0 : Int), (4 : Int)), ((0 : Int), (5 : Int)), ((1 : Int), (0 : Int)), ((1 : Int), (1 : Int)), ((1 : Int), (2 : Int)), ((1 : Int), (3 : Int)), ((1 : Int), (4 : Int)), ((1 : Int), (5 : Int)), ((2 : Int), (-1 : Int)), ((2 : Int), (0 : Int)), ((2 : Int), (1 : Int)), ((2 : Int), (2 : Int)), ((2 : Int), (3 : Int)), ((2 : Int), (4 : Int)), ((3 : Int), (-1 : Int)), ((3 : Int), (0 : Int)), ((3 : Int), (1 : Int)), ((3 : Int), (2 : Int)), ((3 : Int), (3 : Int)), ((3 : Int), (4 : Int))] < tilings (rectCells (4) 6) := by
  native_decide

-- (w=6, q=2, s=1) area=24
example : tilings [((0 : Int), (0 : Int)), ((0 : Int), (1 : Int)), ((0 : Int), (2 : Int)), ((0 : Int), (3 : Int)), ((0 : Int), (4 : Int)), ((0 : Int), (5 : Int)), ((1 : Int), (0 : Int)), ((1 : Int), (1 : Int)), ((1 : Int), (2 : Int)), ((1 : Int), (3 : Int)), ((1 : Int), (4 : Int)), ((1 : Int), (5 : Int)), ((2 : Int), (1 : Int)), ((2 : Int), (2 : Int)), ((2 : Int), (3 : Int)), ((2 : Int), (4 : Int)), ((2 : Int), (5 : Int)), ((2 : Int), (6 : Int)), ((3 : Int), (1 : Int)), ((3 : Int), (2 : Int)), ((3 : Int), (3 : Int)), ((3 : Int), (4 : Int)), ((3 : Int), (5 : Int)), ((3 : Int), (6 : Int))] < tilings (rectCells (4) 6) := by
  native_decide

-- (w=6, q=2, s=2) area=24
example : tilings [((0 : Int), (0 : Int)), ((0 : Int), (1 : Int)), ((0 : Int), (2 : Int)), ((0 : Int), (3 : Int)), ((0 : Int), (4 : Int)), ((0 : Int), (5 : Int)), ((1 : Int), (0 : Int)), ((1 : Int), (1 : Int)), ((1 : Int), (2 : Int)), ((1 : Int), (3 : Int)), ((1 : Int), (4 : Int)), ((1 : Int), (5 : Int)), ((2 : Int), (2 : Int)), ((2 : Int), (3 : Int)), ((2 : Int), (4 : Int)), ((2 : Int), (5 : Int)), ((2 : Int), (6 : Int)), ((2 : Int), (7 : Int)), ((3 : Int), (2 : Int)), ((3 : Int), (3 : Int)), ((3 : Int), (4 : Int)), ((3 : Int), (5 : Int)), ((3 : Int), (6 : Int)), ((3 : Int), (7 : Int))] < tilings (rectCells (4) 6) := by
  native_decide

-- (w=6, q=2, s=3) area=24
example : tilings [((0 : Int), (0 : Int)), ((0 : Int), (1 : Int)), ((0 : Int), (2 : Int)), ((0 : Int), (3 : Int)), ((0 : Int), (4 : Int)), ((0 : Int), (5 : Int)), ((1 : Int), (0 : Int)), ((1 : Int), (1 : Int)), ((1 : Int), (2 : Int)), ((1 : Int), (3 : Int)), ((1 : Int), (4 : Int)), ((1 : Int), (5 : Int)), ((2 : Int), (3 : Int)), ((2 : Int), (4 : Int)), ((2 : Int), (5 : Int)), ((2 : Int), (6 : Int)), ((2 : Int), (7 : Int)), ((2 : Int), (8 : Int)), ((3 : Int), (3 : Int)), ((3 : Int), (4 : Int)), ((3 : Int), (5 : Int)), ((3 : Int), (6 : Int)), ((3 : Int), (7 : Int)), ((3 : Int), (8 : Int))] < tilings (rectCells (4) 6) := by
  native_decide

-- (w=6, q=2, s=4) area=24
example : tilings [((0 : Int), (0 : Int)), ((0 : Int), (1 : Int)), ((0 : Int), (2 : Int)), ((0 : Int), (3 : Int)), ((0 : Int), (4 : Int)), ((0 : Int), (5 : Int)), ((1 : Int), (0 : Int)), ((1 : Int), (1 : Int)), ((1 : Int), (2 : Int)), ((1 : Int), (3 : Int)), ((1 : Int), (4 : Int)), ((1 : Int), (5 : Int)), ((2 : Int), (4 : Int)), ((2 : Int), (5 : Int)), ((2 : Int), (6 : Int)), ((2 : Int), (7 : Int)), ((2 : Int), (8 : Int)), ((2 : Int), (9 : Int)), ((3 : Int), (4 : Int)), ((3 : Int), (5 : Int)), ((3 : Int), (6 : Int)), ((3 : Int), (7 : Int)), ((3 : Int), (8 : Int)), ((3 : Int), (9 : Int))] < tilings (rectCells (4) 6) := by
  native_decide

-- (w=6, q=2, s=5) area=24
example : tilings [((0 : Int), (0 : Int)), ((0 : Int), (1 : Int)), ((0 : Int), (2 : Int)), ((0 : Int), (3 : Int)), ((0 : Int), (4 : Int)), ((0 : Int), (5 : Int)), ((1 : Int), (0 : Int)), ((1 : Int), (1 : Int)), ((1 : Int), (2 : Int)), ((1 : Int), (3 : Int)), ((1 : Int), (4 : Int)), ((1 : Int), (5 : Int)), ((2 : Int), (5 : Int)), ((2 : Int), (6 : Int)), ((2 : Int), (7 : Int)), ((2 : Int), (8 : Int)), ((2 : Int), (9 : Int)), ((2 : Int), (10 : Int)), ((3 : Int), (5 : Int)), ((3 : Int), (6 : Int)), ((3 : Int), (7 : Int)), ((3 : Int), (8 : Int)), ((3 : Int), (9 : Int)), ((3 : Int), (10 : Int))] < tilings (rectCells (4) 6) := by
  native_decide

-- (w=6, q=3, s=-5) area=36
example : tilings [((0 : Int), (0 : Int)), ((0 : Int), (1 : Int)), ((0 : Int), (2 : Int)), ((0 : Int), (3 : Int)), ((0 : Int), (4 : Int)), ((0 : Int), (5 : Int)), ((1 : Int), (0 : Int)), ((1 : Int), (1 : Int)), ((1 : Int), (2 : Int)), ((1 : Int), (3 : Int)), ((1 : Int), (4 : Int)), ((1 : Int), (5 : Int)), ((2 : Int), (0 : Int)), ((2 : Int), (1 : Int)), ((2 : Int), (2 : Int)), ((2 : Int), (3 : Int)), ((2 : Int), (4 : Int)), ((2 : Int), (5 : Int)), ((3 : Int), (-5 : Int)), ((3 : Int), (-4 : Int)), ((3 : Int), (-3 : Int)), ((3 : Int), (-2 : Int)), ((3 : Int), (-1 : Int)), ((3 : Int), (0 : Int)), ((4 : Int), (-5 : Int)), ((4 : Int), (-4 : Int)), ((4 : Int), (-3 : Int)), ((4 : Int), (-2 : Int)), ((4 : Int), (-1 : Int)), ((4 : Int), (0 : Int)), ((5 : Int), (-5 : Int)), ((5 : Int), (-4 : Int)), ((5 : Int), (-3 : Int)), ((5 : Int), (-2 : Int)), ((5 : Int), (-1 : Int)), ((5 : Int), (0 : Int))] < tilings (rectCells (6) 6) := by
  native_decide

-- (w=6, q=3, s=-4) area=36
example : tilings [((0 : Int), (0 : Int)), ((0 : Int), (1 : Int)), ((0 : Int), (2 : Int)), ((0 : Int), (3 : Int)), ((0 : Int), (4 : Int)), ((0 : Int), (5 : Int)), ((1 : Int), (0 : Int)), ((1 : Int), (1 : Int)), ((1 : Int), (2 : Int)), ((1 : Int), (3 : Int)), ((1 : Int), (4 : Int)), ((1 : Int), (5 : Int)), ((2 : Int), (0 : Int)), ((2 : Int), (1 : Int)), ((2 : Int), (2 : Int)), ((2 : Int), (3 : Int)), ((2 : Int), (4 : Int)), ((2 : Int), (5 : Int)), ((3 : Int), (-4 : Int)), ((3 : Int), (-3 : Int)), ((3 : Int), (-2 : Int)), ((3 : Int), (-1 : Int)), ((3 : Int), (0 : Int)), ((3 : Int), (1 : Int)), ((4 : Int), (-4 : Int)), ((4 : Int), (-3 : Int)), ((4 : Int), (-2 : Int)), ((4 : Int), (-1 : Int)), ((4 : Int), (0 : Int)), ((4 : Int), (1 : Int)), ((5 : Int), (-4 : Int)), ((5 : Int), (-3 : Int)), ((5 : Int), (-2 : Int)), ((5 : Int), (-1 : Int)), ((5 : Int), (0 : Int)), ((5 : Int), (1 : Int))] < tilings (rectCells (6) 6) := by
  native_decide

-- (w=6, q=3, s=-3) area=36
example : tilings [((0 : Int), (0 : Int)), ((0 : Int), (1 : Int)), ((0 : Int), (2 : Int)), ((0 : Int), (3 : Int)), ((0 : Int), (4 : Int)), ((0 : Int), (5 : Int)), ((1 : Int), (0 : Int)), ((1 : Int), (1 : Int)), ((1 : Int), (2 : Int)), ((1 : Int), (3 : Int)), ((1 : Int), (4 : Int)), ((1 : Int), (5 : Int)), ((2 : Int), (0 : Int)), ((2 : Int), (1 : Int)), ((2 : Int), (2 : Int)), ((2 : Int), (3 : Int)), ((2 : Int), (4 : Int)), ((2 : Int), (5 : Int)), ((3 : Int), (-3 : Int)), ((3 : Int), (-2 : Int)), ((3 : Int), (-1 : Int)), ((3 : Int), (0 : Int)), ((3 : Int), (1 : Int)), ((3 : Int), (2 : Int)), ((4 : Int), (-3 : Int)), ((4 : Int), (-2 : Int)), ((4 : Int), (-1 : Int)), ((4 : Int), (0 : Int)), ((4 : Int), (1 : Int)), ((4 : Int), (2 : Int)), ((5 : Int), (-3 : Int)), ((5 : Int), (-2 : Int)), ((5 : Int), (-1 : Int)), ((5 : Int), (0 : Int)), ((5 : Int), (1 : Int)), ((5 : Int), (2 : Int))] < tilings (rectCells (6) 6) := by
  native_decide

-- (w=6, q=3, s=-2) area=36
example : tilings [((0 : Int), (0 : Int)), ((0 : Int), (1 : Int)), ((0 : Int), (2 : Int)), ((0 : Int), (3 : Int)), ((0 : Int), (4 : Int)), ((0 : Int), (5 : Int)), ((1 : Int), (0 : Int)), ((1 : Int), (1 : Int)), ((1 : Int), (2 : Int)), ((1 : Int), (3 : Int)), ((1 : Int), (4 : Int)), ((1 : Int), (5 : Int)), ((2 : Int), (0 : Int)), ((2 : Int), (1 : Int)), ((2 : Int), (2 : Int)), ((2 : Int), (3 : Int)), ((2 : Int), (4 : Int)), ((2 : Int), (5 : Int)), ((3 : Int), (-2 : Int)), ((3 : Int), (-1 : Int)), ((3 : Int), (0 : Int)), ((3 : Int), (1 : Int)), ((3 : Int), (2 : Int)), ((3 : Int), (3 : Int)), ((4 : Int), (-2 : Int)), ((4 : Int), (-1 : Int)), ((4 : Int), (0 : Int)), ((4 : Int), (1 : Int)), ((4 : Int), (2 : Int)), ((4 : Int), (3 : Int)), ((5 : Int), (-2 : Int)), ((5 : Int), (-1 : Int)), ((5 : Int), (0 : Int)), ((5 : Int), (1 : Int)), ((5 : Int), (2 : Int)), ((5 : Int), (3 : Int))] < tilings (rectCells (6) 6) := by
  native_decide

-- (w=6, q=3, s=-1) area=36
example : tilings [((0 : Int), (0 : Int)), ((0 : Int), (1 : Int)), ((0 : Int), (2 : Int)), ((0 : Int), (3 : Int)), ((0 : Int), (4 : Int)), ((0 : Int), (5 : Int)), ((1 : Int), (0 : Int)), ((1 : Int), (1 : Int)), ((1 : Int), (2 : Int)), ((1 : Int), (3 : Int)), ((1 : Int), (4 : Int)), ((1 : Int), (5 : Int)), ((2 : Int), (0 : Int)), ((2 : Int), (1 : Int)), ((2 : Int), (2 : Int)), ((2 : Int), (3 : Int)), ((2 : Int), (4 : Int)), ((2 : Int), (5 : Int)), ((3 : Int), (-1 : Int)), ((3 : Int), (0 : Int)), ((3 : Int), (1 : Int)), ((3 : Int), (2 : Int)), ((3 : Int), (3 : Int)), ((3 : Int), (4 : Int)), ((4 : Int), (-1 : Int)), ((4 : Int), (0 : Int)), ((4 : Int), (1 : Int)), ((4 : Int), (2 : Int)), ((4 : Int), (3 : Int)), ((4 : Int), (4 : Int)), ((5 : Int), (-1 : Int)), ((5 : Int), (0 : Int)), ((5 : Int), (1 : Int)), ((5 : Int), (2 : Int)), ((5 : Int), (3 : Int)), ((5 : Int), (4 : Int))] < tilings (rectCells (6) 6) := by
  native_decide

-- (w=6, q=3, s=1) area=36
example : tilings [((0 : Int), (0 : Int)), ((0 : Int), (1 : Int)), ((0 : Int), (2 : Int)), ((0 : Int), (3 : Int)), ((0 : Int), (4 : Int)), ((0 : Int), (5 : Int)), ((1 : Int), (0 : Int)), ((1 : Int), (1 : Int)), ((1 : Int), (2 : Int)), ((1 : Int), (3 : Int)), ((1 : Int), (4 : Int)), ((1 : Int), (5 : Int)), ((2 : Int), (0 : Int)), ((2 : Int), (1 : Int)), ((2 : Int), (2 : Int)), ((2 : Int), (3 : Int)), ((2 : Int), (4 : Int)), ((2 : Int), (5 : Int)), ((3 : Int), (1 : Int)), ((3 : Int), (2 : Int)), ((3 : Int), (3 : Int)), ((3 : Int), (4 : Int)), ((3 : Int), (5 : Int)), ((3 : Int), (6 : Int)), ((4 : Int), (1 : Int)), ((4 : Int), (2 : Int)), ((4 : Int), (3 : Int)), ((4 : Int), (4 : Int)), ((4 : Int), (5 : Int)), ((4 : Int), (6 : Int)), ((5 : Int), (1 : Int)), ((5 : Int), (2 : Int)), ((5 : Int), (3 : Int)), ((5 : Int), (4 : Int)), ((5 : Int), (5 : Int)), ((5 : Int), (6 : Int))] < tilings (rectCells (6) 6) := by
  native_decide

-- (w=6, q=3, s=2) area=36
example : tilings [((0 : Int), (0 : Int)), ((0 : Int), (1 : Int)), ((0 : Int), (2 : Int)), ((0 : Int), (3 : Int)), ((0 : Int), (4 : Int)), ((0 : Int), (5 : Int)), ((1 : Int), (0 : Int)), ((1 : Int), (1 : Int)), ((1 : Int), (2 : Int)), ((1 : Int), (3 : Int)), ((1 : Int), (4 : Int)), ((1 : Int), (5 : Int)), ((2 : Int), (0 : Int)), ((2 : Int), (1 : Int)), ((2 : Int), (2 : Int)), ((2 : Int), (3 : Int)), ((2 : Int), (4 : Int)), ((2 : Int), (5 : Int)), ((3 : Int), (2 : Int)), ((3 : Int), (3 : Int)), ((3 : Int), (4 : Int)), ((3 : Int), (5 : Int)), ((3 : Int), (6 : Int)), ((3 : Int), (7 : Int)), ((4 : Int), (2 : Int)), ((4 : Int), (3 : Int)), ((4 : Int), (4 : Int)), ((4 : Int), (5 : Int)), ((4 : Int), (6 : Int)), ((4 : Int), (7 : Int)), ((5 : Int), (2 : Int)), ((5 : Int), (3 : Int)), ((5 : Int), (4 : Int)), ((5 : Int), (5 : Int)), ((5 : Int), (6 : Int)), ((5 : Int), (7 : Int))] < tilings (rectCells (6) 6) := by
  native_decide

-- (w=6, q=3, s=3) area=36
example : tilings [((0 : Int), (0 : Int)), ((0 : Int), (1 : Int)), ((0 : Int), (2 : Int)), ((0 : Int), (3 : Int)), ((0 : Int), (4 : Int)), ((0 : Int), (5 : Int)), ((1 : Int), (0 : Int)), ((1 : Int), (1 : Int)), ((1 : Int), (2 : Int)), ((1 : Int), (3 : Int)), ((1 : Int), (4 : Int)), ((1 : Int), (5 : Int)), ((2 : Int), (0 : Int)), ((2 : Int), (1 : Int)), ((2 : Int), (2 : Int)), ((2 : Int), (3 : Int)), ((2 : Int), (4 : Int)), ((2 : Int), (5 : Int)), ((3 : Int), (3 : Int)), ((3 : Int), (4 : Int)), ((3 : Int), (5 : Int)), ((3 : Int), (6 : Int)), ((3 : Int), (7 : Int)), ((3 : Int), (8 : Int)), ((4 : Int), (3 : Int)), ((4 : Int), (4 : Int)), ((4 : Int), (5 : Int)), ((4 : Int), (6 : Int)), ((4 : Int), (7 : Int)), ((4 : Int), (8 : Int)), ((5 : Int), (3 : Int)), ((5 : Int), (4 : Int)), ((5 : Int), (5 : Int)), ((5 : Int), (6 : Int)), ((5 : Int), (7 : Int)), ((5 : Int), (8 : Int))] < tilings (rectCells (6) 6) := by
  native_decide

-- (w=6, q=3, s=4) area=36
example : tilings [((0 : Int), (0 : Int)), ((0 : Int), (1 : Int)), ((0 : Int), (2 : Int)), ((0 : Int), (3 : Int)), ((0 : Int), (4 : Int)), ((0 : Int), (5 : Int)), ((1 : Int), (0 : Int)), ((1 : Int), (1 : Int)), ((1 : Int), (2 : Int)), ((1 : Int), (3 : Int)), ((1 : Int), (4 : Int)), ((1 : Int), (5 : Int)), ((2 : Int), (0 : Int)), ((2 : Int), (1 : Int)), ((2 : Int), (2 : Int)), ((2 : Int), (3 : Int)), ((2 : Int), (4 : Int)), ((2 : Int), (5 : Int)), ((3 : Int), (4 : Int)), ((3 : Int), (5 : Int)), ((3 : Int), (6 : Int)), ((3 : Int), (7 : Int)), ((3 : Int), (8 : Int)), ((3 : Int), (9 : Int)), ((4 : Int), (4 : Int)), ((4 : Int), (5 : Int)), ((4 : Int), (6 : Int)), ((4 : Int), (7 : Int)), ((4 : Int), (8 : Int)), ((4 : Int), (9 : Int)), ((5 : Int), (4 : Int)), ((5 : Int), (5 : Int)), ((5 : Int), (6 : Int)), ((5 : Int), (7 : Int)), ((5 : Int), (8 : Int)), ((5 : Int), (9 : Int))] < tilings (rectCells (6) 6) := by
  native_decide

-- (w=6, q=3, s=5) area=36
example : tilings [((0 : Int), (0 : Int)), ((0 : Int), (1 : Int)), ((0 : Int), (2 : Int)), ((0 : Int), (3 : Int)), ((0 : Int), (4 : Int)), ((0 : Int), (5 : Int)), ((1 : Int), (0 : Int)), ((1 : Int), (1 : Int)), ((1 : Int), (2 : Int)), ((1 : Int), (3 : Int)), ((1 : Int), (4 : Int)), ((1 : Int), (5 : Int)), ((2 : Int), (0 : Int)), ((2 : Int), (1 : Int)), ((2 : Int), (2 : Int)), ((2 : Int), (3 : Int)), ((2 : Int), (4 : Int)), ((2 : Int), (5 : Int)), ((3 : Int), (5 : Int)), ((3 : Int), (6 : Int)), ((3 : Int), (7 : Int)), ((3 : Int), (8 : Int)), ((3 : Int), (9 : Int)), ((3 : Int), (10 : Int)), ((4 : Int), (5 : Int)), ((4 : Int), (6 : Int)), ((4 : Int), (7 : Int)), ((4 : Int), (8 : Int)), ((4 : Int), (9 : Int)), ((4 : Int), (10 : Int)), ((5 : Int), (5 : Int)), ((5 : Int), (6 : Int)), ((5 : Int), (7 : Int)), ((5 : Int), (8 : Int)), ((5 : Int), (9 : Int)), ((5 : Int), (10 : Int))] < tilings (rectCells (6) 6) := by
  native_decide
