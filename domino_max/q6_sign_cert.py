# -*- coding: utf-8 -*-
"""q=6 spectral-weight exact sign certificate (pure rational, no floats).

This script proves, for each of the six growing branches lambda>1 of the q=6
quadrangle generating function, the exact sign identity

    alpha_lambda = -N(p) * lambda / (169 * f'(p)) > 0,   p = 1/lambda in (0,1),

where f is the corresponding cubic factor and N the exact numerator of the
partial-fraction decomposition G(x) = -49/169/(x-1)
  - (17x^2-3443x+374)/169/(x^3-269x^2+66x-1)
  - (17x^2-748x+1130)/169/(x^3-66x^2+269x-1)
  - (43x^2-827x+184)/169/(x^3-26x^2+13x-1)
  - (43x^2-375x+291)/169/(x^3-13x^2+26x-1).

All computations are exact rational arithmetic:
  * root isolation via sympy Poly.intervals() (rational endpoints);
  * adaptive rational bisection until f(lo) and f(hi) have opposite signs;
  * uniqueness via Poly.count_roots(lo, hi) == 1 on the enclosing interval;
  * N(p)*f'(p) < 0 via exact endpoint/vertex sign checks (both are quadratics).
No float(), no nroots, no sp.N is used anywhere.
"""
from fractions import Fraction
import sympy as sp

X = sp.symbols('x')

TERMS = [
    # (branch, f(x), N(x), enclosing intervals for p in (0,1))
    ('A1', X**3 - 269*X**2 + 66*X - 1,
     -(17*X**2 - 3443*X + 374), ((1, 100), (1, 50))),
    ('A2', X**3 - 269*X**2 + 66*X - 1,
     -(17*X**2 - 3443*X + 374), ((1, 5), (6, 25))),
    ('B',  X**3 - 66*X**2 + 269*X - 1,
     -(17*X**2 - 748*X + 1130), ((1, 500), (1, 250))),
    ('C1', X**3 - 26*X**2 + 13*X - 1,
     -(43*X**2 - 827*X + 184), ((2, 25), (1, 10))),
    ('C2', X**3 - 26*X**2 + 13*X - 1,
     -(43*X**2 - 827*X + 184), ((2, 5), (11, 25))),
    ('D',  X**3 - 13*X**2 + 26*X - 1,
     -(43*X**2 - 375*X + 291), ((1, 50), (1, 25))),
]


def as_frac(t):
    """Convert (num, den) or Fraction into an exact Fraction."""
    if isinstance(t, Fraction):
        return t
    return Fraction(t[0], t[1])


def exact_sign(v):
    """Exact sign of a Fraction (never returns 0 for non-zero inputs here)."""
    if v > 0:
        return 1
    if v < 0:
        return -1
    raise AssertionError('zero value encountered in exact sign certificate')


def eval_poly_exact(coeffs, p):
    """Horner evaluation of a polynomial with Fraction coefficients at Fraction p."""
    acc = Fraction(0)
    for c in coeffs:
        acc = acc * p + c
    return acc


def quad_sign_set(coeffs, lo, hi):
    """Constant sign of quadratic c2*x^2 + c1*x + c0 = c2*(x-vi)^2+... on [lo,hi].

    Since the leading coefficient may be negative, the two extrema lie at the
    endpoints of the interval (a downward parabola attains its maximum, not its
    minimum, inside).  For each of the four candidates {lo, hi, vertex}, we take
    the sign; the union is the exact sign range on [lo,hi].
    """
    a, b, c = coeffs
    pts = [lo, hi]
    if a != 0:
        vertex = Fraction(-b, 2 * a)
        if lo < vertex < hi:
            pts.append(vertex)
    signs = {exact_sign(eval_poly_exact(coeffs, t)) for t in pts}
    return signs


def refine_interval(poly, lo, hi, max_iters=400):
    """Bisect the rational interval [lo,hi] until poly(lo) and poly(hi) differ in sign."""
    flo = exact_sign(poly(lo))
    fhi = exact_sign(poly(hi))
    if flo == fhi:
        raise AssertionError('initial interval does not bracket a sign change')
    for _ in range(max_iters):
        if flo != fhi:
            break
        mid = (lo + hi) / 2
        fm = exact_sign(poly(mid))
        if fm == flo:
            lo = mid
        else:
            hi = mid
            fhi = fm
    if flo == fhi:
        raise AssertionError('refinement failed to separate signs')
    return lo, hi


def main():
    all_ok = True
    for name, f_expr, N_expr, (lo0, hi0) in TERMS:
        f = sp.Poly(f_expr, X)
        fprime = sp.Poly(sp.diff(f_expr, X), X)
        N = sp.Poly(N_expr, X)
        lo = as_frac(lo0)
        hi = as_frac(hi0)
        # unique root inside (lo0, hi0) is certified by the polynomial itself
        if sp.Poly(f_expr, X).count_roots(lo, hi) != 1:
            raise AssertionError('no unique root in interval for branch ' + name)
        lo, hi = refine_interval(f, lo, hi)
        sN = quad_sign_set((sp.Rational(N.coeff_monomial(X**2)),
                            sp.Rational(N.coeff_monomial(X)),
                            sp.Rational(N.coeff_monomial(1))), lo, hi)
        sF = quad_sign_set((sp.Rational(fprime.coeff_monomial(X**2)),
                            sp.Rational(fprime.coeff_monomial(X)),
                            sp.Rational(fprime.coeff_monomial(1))), lo, hi)
        neg_prod = (sN == {-1} and sF == {1}) or (sN == {1} and sF == {-1})
        all_ok = all_ok and neg_prod
        print('%s  p-in-(%s,%s)  N-sign=%s fprime-sign=%s  N*fprime<0=%s' % (
            name, lo, hi, sN, sF, neg_prod))
    print('ALL SIX N(p)*f\'(p) < 0  (exact rational certificate):', all_ok)
    return 0 if all_ok else 1


if __name__ == '__main__':
    raise SystemExit(main())
