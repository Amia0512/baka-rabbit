import Mathlib

set_option maxHeartbeats 0

namespace Q6AllRootPF

noncomputable section

open Polynomial

private def X : Polynomial ℚ := Polynomial.X

def f1 : Polynomial ℚ := X ^ 3 - 269 * X ^ 2 + 66 * X - 1
def f2 : Polynomial ℚ := X ^ 3 - 66 * X ^ 2 + 269 * X - 1
def f3 : Polynomial ℚ := X ^ 3 - 26 * X ^ 2 + 13 * X - 1
def f4 : Polynomial ℚ := X ^ 3 - 13 * X ^ 2 + 26 * X - 1

def n1 : Polynomial ℚ := -17 * X ^ 2 + 3443 * X - 374
def n2 : Polynomial ℚ := -17 * X ^ 2 + 748 * X - 1130
def n3 : Polynomial ℚ := -43 * X ^ 2 + 827 * X - 184
def n4 : Polynomial ℚ := -43 * X ^ 2 + 375 * X - 291

def p : Polynomial ℚ :=
  X ^ 12 - 363 * X ^ 11 + 29377 * X ^ 10 - 806424 * X ^ 9 +
    8591767 * X ^ 8 - 37871957 * X ^ 7 + 70390335 * X ^ 6 -
    53332482 * X ^ 5 + 17318434 * X ^ 4 - 2431370 * X ^ 3 +
    134439 * X ^ 2 - 2528 * X + 12

def q : Polynomial ℚ := -(X - 1) * f1 * f2 * f3 * f4

theorem partial_fraction_identity :
    -169 * p = -49 * f1 * f2 * f3 * f4 +
      (X - 1) * (n1 * f2 * f3 * f4 + n2 * f1 * f3 * f4 +
        n3 * f1 * f2 * f4 + n4 * f1 * f2 * f3) := by
  unfold p f1 f2 f3 f4 n1 n2 n3 n4 X
  ring

theorem denominator_factor :
    q = -(X - 1) * f1 * f2 * f3 * f4 := by
  rfl

end

#print axioms Q6AllRootPF.partial_fraction_identity
#print axioms Q6AllRootPF.denominator_factor

end Q6AllRootPF
