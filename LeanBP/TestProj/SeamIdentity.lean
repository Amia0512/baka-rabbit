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

def rowCells (r w : Nat) : List Cell :=
  match w with
  | 0 => []
  | c+1 => ((r : Int), (c : Int)) :: rowCells r c

def grid (h w : Nat) : List Cell :=
  match h with
  | 0 => []
  | r+1 => grid r w ++ rowCells r w

def myFilter (f : Cell -> Bool) (xs : List Cell) : List Cell :=
  match xs with
  | [] => []
  | x :: rest => if f x then x :: myFilter f rest else myFilter f rest

-- 上条带 w×q 挖 (q-1, P 绝对列)  [上块列 0..w-1]
def upCells (w q : Nat) (P : List Nat) : List Cell :=
  myFilter (fun cc => ! (cc.1 = ((q : Int) - 1) && P.any (fun c => cc.2 = (c : Int)))) (grid q w)

-- 矩形下条带 w×hp 挖 (0, P) [列 0..w-1]
def dnCells (w hp : Nat) (P : List Nat) : List Cell :=
  myFilter (fun cc => ! (cc.1 = 0 && P.any (fun c => cc.2 = (c : Int)))) (grid hp w)

-- 两块下块 w×hp 列偏移 s 挖 (0, P 绝对列) [列 s..s+w-1]
def dnCellsShifted (w hp : Nat) (s : Int) (P : List Nat) : List Cell :=
  myFilter (fun cc => ! (cc.1 = 0 && P.any (fun c => cc.2 = (c : Int))))
    ((List.range hp).flatMap (fun r => (List.range w).map (fun c => ((r : Int), (c : Int) + s))))

-- overlap = [max(0,s), min(w,w+s))
def loOv (s w : Int) : Int := if s >= 0 then s else 0
def hiOv (s w : Int) : Int := if s >= 0 then w else s + w

def inOverlap (s w : Int) (P : List Nat) : Bool :=
  P.all (fun c => loOv s w <= (c : Int) && (c : Int) < hiOv s w)

def hasNonOv (s w : Int) (P : List Nat) : Bool :=
  P.any (fun c => ! (loOv s w <= (c : Int) && (c : Int) < hiOv s w))

def sublists : List Nat -> List (List Nat)
  | [] => [[]]
  | x :: xs => (sublists xs).map (fun t => x :: t) ++ sublists xs

-- Σ_{P⊆[0,w)} U_P·W_P(0) 矩形全分解
def sumAll (Ps : List (List Nat)) (w q hp : Nat) : Nat :=
  match Ps with
  | [] => 0
  | P :: rest => tilings (upCells w q P) * tilings (dnCells w hp P) + sumAll rest w q hp

-- Σ_{P⊆overlap} U_P·W_P(s) 两块(有缝)
def sumR (Ps : List (List Nat)) (w q hp : Nat) (s : Int) : Nat :=
  match Ps with
  | [] => 0
  | P :: rest =>
      let term := if inOverlap s (w : Int) P then tilings (upCells w q P) * tilings (dnCellsShifted w hp s P) else 0
      term + sumR rest w q hp s

-- G = Σ_{P⊄overlap} U_P·W_P(0) (矩形独有项)
def sumG (Ps : List (List Nat)) (w q hp : Nat) (s : Int) : Nat :=
  match Ps with
  | [] => 0
  | P :: rest =>
      let term := if hasNonOv s (w : Int) P then tilings (upCells w q P) * tilings (dnCells w hp P) else 0
      term + sumG rest w q hp s

-- h=2 w=2 q=1 s=1
example : tilings (rectCells 2 2) = sumAll (sublists (List.range 2)) 2 1 1 := by
  native_decide

example : tilings [((0 : Int), (0 : Int)), ((0 : Int), (1 : Int)), ((1 : Int), (1 : Int)), ((1 : Int), (2 : Int))] = sumR (sublists (List.range 2)) 2 1 1 (1 : Int) := by
  native_decide

example : 0 < sumG (sublists (List.range 2)) 2 1 1 (1 : Int) := by
  native_decide

-- h=2 w=2 q=1 s=-1
example : tilings (rectCells 2 2) = sumAll (sublists (List.range 2)) 2 1 1 := by
  native_decide

example : tilings [((0 : Int), (1 : Int)), ((0 : Int), (2 : Int)), ((1 : Int), (0 : Int)), ((1 : Int), (1 : Int))] = sumR (sublists (List.range 2)) 2 1 1 (-1 : Int) := by
  native_decide

example : 0 < sumG (sublists (List.range 2)) 2 1 1 (-1 : Int) := by
  native_decide

-- h=2 w=3 q=1 s=1
example : tilings (rectCells 2 3) = sumAll (sublists (List.range 3)) 3 1 1 := by
  native_decide

example : tilings [((0 : Int), (0 : Int)), ((0 : Int), (1 : Int)), ((0 : Int), (2 : Int)), ((1 : Int), (1 : Int)), ((1 : Int), (2 : Int)), ((1 : Int), (3 : Int))] = sumR (sublists (List.range 3)) 3 1 1 (1 : Int) := by
  native_decide

example : 0 < sumG (sublists (List.range 3)) 3 1 1 (1 : Int) := by
  native_decide

-- h=2 w=3 q=1 s=-1
example : tilings (rectCells 2 3) = sumAll (sublists (List.range 3)) 3 1 1 := by
  native_decide

example : tilings [((0 : Int), (1 : Int)), ((0 : Int), (2 : Int)), ((0 : Int), (3 : Int)), ((1 : Int), (0 : Int)), ((1 : Int), (1 : Int)), ((1 : Int), (2 : Int))] = sumR (sublists (List.range 3)) 3 1 1 (-1 : Int) := by
  native_decide

example : 0 < sumG (sublists (List.range 3)) 3 1 1 (-1 : Int) := by
  native_decide

-- h=3 w=2 q=1 s=1
example : tilings (rectCells 3 2) = sumAll (sublists (List.range 2)) 2 1 2 := by
  native_decide

example : tilings [((0 : Int), (0 : Int)), ((0 : Int), (1 : Int)), ((1 : Int), (1 : Int)), ((1 : Int), (2 : Int)), ((2 : Int), (1 : Int)), ((2 : Int), (2 : Int))] = sumR (sublists (List.range 2)) 2 1 2 (1 : Int) := by
  native_decide

example : 0 < sumG (sublists (List.range 2)) 2 1 2 (1 : Int) := by
  native_decide

-- h=3 w=2 q=2 s=1
example : tilings (rectCells 3 2) = sumAll (sublists (List.range 2)) 2 2 1 := by
  native_decide

example : tilings [((0 : Int), (0 : Int)), ((0 : Int), (1 : Int)), ((1 : Int), (0 : Int)), ((1 : Int), (1 : Int)), ((2 : Int), (1 : Int)), ((2 : Int), (2 : Int))] = sumR (sublists (List.range 2)) 2 2 1 (1 : Int) := by
  native_decide

example : 0 < sumG (sublists (List.range 2)) 2 2 1 (1 : Int) := by
  native_decide

-- h=3 w=4 q=1 s=1
example : tilings (rectCells 3 4) = sumAll (sublists (List.range 4)) 4 1 2 := by
  native_decide

example : tilings [((0 : Int), (0 : Int)), ((0 : Int), (1 : Int)), ((0 : Int), (2 : Int)), ((0 : Int), (3 : Int)), ((1 : Int), (1 : Int)), ((1 : Int), (2 : Int)), ((1 : Int), (3 : Int)), ((1 : Int), (4 : Int)), ((2 : Int), (1 : Int)), ((2 : Int), (2 : Int)), ((2 : Int), (3 : Int)), ((2 : Int), (4 : Int))] = sumR (sublists (List.range 4)) 4 1 2 (1 : Int) := by
  native_decide

example : 0 < sumG (sublists (List.range 4)) 4 1 2 (1 : Int) := by
  native_decide

-- h=3 w=4 q=2 s=1
example : tilings (rectCells 3 4) = sumAll (sublists (List.range 4)) 4 2 1 := by
  native_decide

example : tilings [((0 : Int), (0 : Int)), ((0 : Int), (1 : Int)), ((0 : Int), (2 : Int)), ((0 : Int), (3 : Int)), ((1 : Int), (0 : Int)), ((1 : Int), (1 : Int)), ((1 : Int), (2 : Int)), ((1 : Int), (3 : Int)), ((2 : Int), (1 : Int)), ((2 : Int), (2 : Int)), ((2 : Int), (3 : Int)), ((2 : Int), (4 : Int))] = sumR (sublists (List.range 4)) 4 2 1 (1 : Int) := by
  native_decide

example : 0 < sumG (sublists (List.range 4)) 4 2 1 (1 : Int) := by
  native_decide

-- h=3 w=4 q=2 s=-2
example : tilings (rectCells 3 4) = sumAll (sublists (List.range 4)) 4 2 1 := by
  native_decide

example : tilings [((0 : Int), (2 : Int)), ((0 : Int), (3 : Int)), ((0 : Int), (4 : Int)), ((0 : Int), (5 : Int)), ((1 : Int), (2 : Int)), ((1 : Int), (3 : Int)), ((1 : Int), (4 : Int)), ((1 : Int), (5 : Int)), ((2 : Int), (0 : Int)), ((2 : Int), (1 : Int)), ((2 : Int), (2 : Int)), ((2 : Int), (3 : Int))] = sumR (sublists (List.range 4)) 4 2 1 (-2 : Int) := by
  native_decide

example : 0 < sumG (sublists (List.range 4)) 4 2 1 (-2 : Int) := by
  native_decide

-- h=4 w=3 q=1 s=1
example : tilings (rectCells 4 3) = sumAll (sublists (List.range 3)) 3 1 3 := by
  native_decide

example : tilings [((0 : Int), (0 : Int)), ((0 : Int), (1 : Int)), ((0 : Int), (2 : Int)), ((1 : Int), (1 : Int)), ((1 : Int), (2 : Int)), ((1 : Int), (3 : Int)), ((2 : Int), (1 : Int)), ((2 : Int), (2 : Int)), ((2 : Int), (3 : Int)), ((3 : Int), (1 : Int)), ((3 : Int), (2 : Int)), ((3 : Int), (3 : Int))] = sumR (sublists (List.range 3)) 3 1 3 (1 : Int) := by
  native_decide

example : 0 < sumG (sublists (List.range 3)) 3 1 3 (1 : Int) := by
  native_decide

-- h=4 w=3 q=2 s=1
example : tilings (rectCells 4 3) = sumAll (sublists (List.range 3)) 3 2 2 := by
  native_decide

example : tilings [((0 : Int), (0 : Int)), ((0 : Int), (1 : Int)), ((0 : Int), (2 : Int)), ((1 : Int), (0 : Int)), ((1 : Int), (1 : Int)), ((1 : Int), (2 : Int)), ((2 : Int), (1 : Int)), ((2 : Int), (2 : Int)), ((2 : Int), (3 : Int)), ((3 : Int), (1 : Int)), ((3 : Int), (2 : Int)), ((3 : Int), (3 : Int))] = sumR (sublists (List.range 3)) 3 2 2 (1 : Int) := by
  native_decide

example : 0 < sumG (sublists (List.range 3)) 3 2 2 (1 : Int) := by
  native_decide

-- h=4 w=3 q=2 s=-2
example : tilings (rectCells 4 3) = sumAll (sublists (List.range 3)) 3 2 2 := by
  native_decide

example : tilings [((0 : Int), (2 : Int)), ((0 : Int), (3 : Int)), ((0 : Int), (4 : Int)), ((1 : Int), (2 : Int)), ((1 : Int), (3 : Int)), ((1 : Int), (4 : Int)), ((2 : Int), (0 : Int)), ((2 : Int), (1 : Int)), ((2 : Int), (2 : Int)), ((3 : Int), (0 : Int)), ((3 : Int), (1 : Int)), ((3 : Int), (2 : Int))] = sumR (sublists (List.range 3)) 3 2 2 (-2 : Int) := by
  native_decide

example : 0 < sumG (sublists (List.range 3)) 3 2 2 (-2 : Int) := by
  native_decide

-- h=4 w=3 q=3 s=1
example : tilings (rectCells 4 3) = sumAll (sublists (List.range 3)) 3 3 1 := by
  native_decide

example : tilings [((0 : Int), (0 : Int)), ((0 : Int), (1 : Int)), ((0 : Int), (2 : Int)), ((1 : Int), (0 : Int)), ((1 : Int), (1 : Int)), ((1 : Int), (2 : Int)), ((2 : Int), (0 : Int)), ((2 : Int), (1 : Int)), ((2 : Int), (2 : Int)), ((3 : Int), (1 : Int)), ((3 : Int), (2 : Int)), ((3 : Int), (3 : Int))] = sumR (sublists (List.range 3)) 3 3 1 (1 : Int) := by
  native_decide

example : 0 < sumG (sublists (List.range 3)) 3 3 1 (1 : Int) := by
  native_decide

-- h=4 w=4 q=1 s=1
example : tilings (rectCells 4 4) = sumAll (sublists (List.range 4)) 4 1 3 := by
  native_decide

example : tilings [((0 : Int), (0 : Int)), ((0 : Int), (1 : Int)), ((0 : Int), (2 : Int)), ((0 : Int), (3 : Int)), ((1 : Int), (1 : Int)), ((1 : Int), (2 : Int)), ((1 : Int), (3 : Int)), ((1 : Int), (4 : Int)), ((2 : Int), (1 : Int)), ((2 : Int), (2 : Int)), ((2 : Int), (3 : Int)), ((2 : Int), (4 : Int)), ((3 : Int), (1 : Int)), ((3 : Int), (2 : Int)), ((3 : Int), (3 : Int)), ((3 : Int), (4 : Int))] = sumR (sublists (List.range 4)) 4 1 3 (1 : Int) := by
  native_decide

example : 0 < sumG (sublists (List.range 4)) 4 1 3 (1 : Int) := by
  native_decide

-- h=4 w=4 q=2 s=1
example : tilings (rectCells 4 4) = sumAll (sublists (List.range 4)) 4 2 2 := by
  native_decide

example : tilings [((0 : Int), (0 : Int)), ((0 : Int), (1 : Int)), ((0 : Int), (2 : Int)), ((0 : Int), (3 : Int)), ((1 : Int), (0 : Int)), ((1 : Int), (1 : Int)), ((1 : Int), (2 : Int)), ((1 : Int), (3 : Int)), ((2 : Int), (1 : Int)), ((2 : Int), (2 : Int)), ((2 : Int), (3 : Int)), ((2 : Int), (4 : Int)), ((3 : Int), (1 : Int)), ((3 : Int), (2 : Int)), ((3 : Int), (3 : Int)), ((3 : Int), (4 : Int))] = sumR (sublists (List.range 4)) 4 2 2 (1 : Int) := by
  native_decide

example : 0 < sumG (sublists (List.range 4)) 4 2 2 (1 : Int) := by
  native_decide

-- h=4 w=4 q=2 s=-1
example : tilings (rectCells 4 4) = sumAll (sublists (List.range 4)) 4 2 2 := by
  native_decide

example : tilings [((0 : Int), (1 : Int)), ((0 : Int), (2 : Int)), ((0 : Int), (3 : Int)), ((0 : Int), (4 : Int)), ((1 : Int), (1 : Int)), ((1 : Int), (2 : Int)), ((1 : Int), (3 : Int)), ((1 : Int), (4 : Int)), ((2 : Int), (0 : Int)), ((2 : Int), (1 : Int)), ((2 : Int), (2 : Int)), ((2 : Int), (3 : Int)), ((3 : Int), (0 : Int)), ((3 : Int), (1 : Int)), ((3 : Int), (2 : Int)), ((3 : Int), (3 : Int))] = sumR (sublists (List.range 4)) 4 2 2 (-1 : Int) := by
  native_decide

example : 0 < sumG (sublists (List.range 4)) 4 2 2 (-1 : Int) := by
  native_decide

-- h=4 w=4 q=3 s=2
example : tilings (rectCells 4 4) = sumAll (sublists (List.range 4)) 4 3 1 := by
  native_decide

example : tilings [((0 : Int), (0 : Int)), ((0 : Int), (1 : Int)), ((0 : Int), (2 : Int)), ((0 : Int), (3 : Int)), ((1 : Int), (0 : Int)), ((1 : Int), (1 : Int)), ((1 : Int), (2 : Int)), ((1 : Int), (3 : Int)), ((2 : Int), (0 : Int)), ((2 : Int), (1 : Int)), ((2 : Int), (2 : Int)), ((2 : Int), (3 : Int)), ((3 : Int), (2 : Int)), ((3 : Int), (3 : Int)), ((3 : Int), (4 : Int)), ((3 : Int), (5 : Int))] = sumR (sublists (List.range 4)) 4 3 1 (2 : Int) := by
  native_decide

example : 0 < sumG (sublists (List.range 4)) 4 3 1 (2 : Int) := by
  native_decide

-- h=2 w=4 q=1 s=1
example : tilings (rectCells 2 4) = sumAll (sublists (List.range 4)) 4 1 1 := by
  native_decide

example : tilings [((0 : Int), (0 : Int)), ((0 : Int), (1 : Int)), ((0 : Int), (2 : Int)), ((0 : Int), (3 : Int)), ((1 : Int), (1 : Int)), ((1 : Int), (2 : Int)), ((1 : Int), (3 : Int)), ((1 : Int), (4 : Int))] = sumR (sublists (List.range 4)) 4 1 1 (1 : Int) := by
  native_decide

example : 0 < sumG (sublists (List.range 4)) 4 1 1 (1 : Int) := by
  native_decide

-- h=2 w=4 q=1 s=-2
example : tilings (rectCells 2 4) = sumAll (sublists (List.range 4)) 4 1 1 := by
  native_decide

example : tilings [((0 : Int), (2 : Int)), ((0 : Int), (3 : Int)), ((0 : Int), (4 : Int)), ((0 : Int), (5 : Int)), ((1 : Int), (0 : Int)), ((1 : Int), (1 : Int)), ((1 : Int), (2 : Int)), ((1 : Int), (3 : Int))] = sumR (sublists (List.range 4)) 4 1 1 (-2 : Int) := by
  native_decide

example : 0 < sumG (sublists (List.range 4)) 4 1 1 (-2 : Int) := by
  native_decide

-- h=4 w=2 q=1 s=1
example : tilings (rectCells 4 2) = sumAll (sublists (List.range 2)) 2 1 3 := by
  native_decide

example : tilings [((0 : Int), (0 : Int)), ((0 : Int), (1 : Int)), ((1 : Int), (1 : Int)), ((1 : Int), (2 : Int)), ((2 : Int), (1 : Int)), ((2 : Int), (2 : Int)), ((3 : Int), (1 : Int)), ((3 : Int), (2 : Int))] = sumR (sublists (List.range 2)) 2 1 3 (1 : Int) := by
  native_decide

example : 0 < sumG (sublists (List.range 2)) 2 1 3 (1 : Int) := by
  native_decide

-- h=4 w=2 q=2 s=-1
example : tilings (rectCells 4 2) = sumAll (sublists (List.range 2)) 2 2 2 := by
  native_decide

example : tilings [((0 : Int), (1 : Int)), ((0 : Int), (2 : Int)), ((1 : Int), (1 : Int)), ((1 : Int), (2 : Int)), ((2 : Int), (0 : Int)), ((2 : Int), (1 : Int)), ((3 : Int), (0 : Int)), ((3 : Int), (1 : Int))] = sumR (sublists (List.range 2)) 2 2 2 (-1 : Int) := by
  native_decide

example : 0 < sumG (sublists (List.range 2)) 2 2 2 (-1 : Int) := by
  native_decide

-- h=4 w=2 q=3 s=1
example : tilings (rectCells 4 2) = sumAll (sublists (List.range 2)) 2 3 1 := by
  native_decide

example : tilings [((0 : Int), (0 : Int)), ((0 : Int), (1 : Int)), ((1 : Int), (0 : Int)), ((1 : Int), (1 : Int)), ((2 : Int), (0 : Int)), ((2 : Int), (1 : Int)), ((3 : Int), (1 : Int)), ((3 : Int), (2 : Int))] = sumR (sublists (List.range 2)) 2 3 1 (1 : Int) := by
  native_decide

example : 0 < sumG (sublists (List.range 2)) 2 3 1 (1 : Int) := by
  native_decide
