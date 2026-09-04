# -*- coding: utf-8 -*-
"""q=6 spectral screening: exact rational re-verification of the report's
specific claims, without any floating point.

Checks
  1. chi(x) = (x-1)*f1*f2*f3*f4  (exact integer factorization identity)
  2. chi(x) = (x-1)*x^6*p(x+1/x) with p = p1*p2 (exact identity)
  3. p1, p2 have no roots in (0,2) and exactly 3 roots in (2,300)
     (Sturm root counts on rational endpoints, no floats)
  4. each cubic f_j has exactly one root in its isolating (0,1) interval
  5. the alpha formula is printed at exact endpoints only (no float)
"""
from fractions import Fraction
import sympy as sp

X = sp.symbols('x')
T = sp.symbols('t')


def clamp_frac(lo, hi):
    """Verify lo < hi (each given as (num,den)) and return as Fractions."""
    lo_f = Fraction(lo[0], lo[1]) if isinstance(lo, tuple) else Fraction(lo)
    hi_f = Fraction(hi[0], hi[1]) if isinstance(hi, tuple) else Fraction(hi)
    if not (lo_f < hi_f):
        raise AssertionError('invalid interval')
    return lo_f, hi_f


def count_roots_on(poly_expr, var, lo, hi):
    lo_f, hi_f = clamp_frac(lo, hi)
    return sp.Poly(poly_expr, var).count_roots(lo_f, hi_f)


def main():
    ok = True

    # --- 1. chi factorization into (x-1)*f1*f2*f3*f4 ---
    chi = (X**13 - 375*X**12 + 31905*X**11 - 940863*X**10 + 11023137*X**9
           - 55190391*X**8 + 123722817*X**7 - 123722817*X**6 + 55190391*X**5
           - 11023137*X**4 + 940863*X**3 - 31905*X**2 + 375*X - 1)
    f1 = X**3 - 269*X**2 + 66*X - 1
    f2 = X**3 - 66*X**2 + 269*X - 1
    f3 = X**3 - 26*X**2 + 13*X - 1
    f4 = X**3 - 13*X**2 + 26*X - 1
    ok &= sp.expand(chi - (X - 1) * f1 * f2 * f3 * f4) == 0
    print('chi = (x-1)*f1*f2*f3*f4  exact:', sp.expand(chi - (X - 1) * f1 * f2 * f3 * f4) == 0)

    # --- 2. chi(x) = (x-1)*x^6*p1(x+1/x)*p2(x+1/x) ---
    p1 = T**3 - 335*T**2 + 18086*T - 76049
    p2 = T**3 - 39*T**2 + 374*T - 769
    # substitute t = x + 1/x on the rational function chi / ((x-1)*x^6)
    y = (X**2 + 1) / X
    lhs = sp.cancel(chi / ((X - 1) * X**6))
    rhs = sp.expand(p1.subs(T, y) * p2.subs(T, y))
    ok &= sp.cancel(lhs - rhs) == 0
    print('chi = (x-1)*x^6*p(x+1/x)  exact:', sp.cancel(lhs - rhs) == 0)

    # --- 3. Sturm counts for p1, p2 on (0,2) and (2,300) ---
    for name, poly in [('p1', p1), ('p2', p2)]:
        c02 = count_roots_on(poly, T, '0', '2')
        c2300 = count_roots_on(poly, T, '2', '300')
        good = (c02 == 0) and (c2300 == 3)
        ok &= good
        print('%s roots (0,2)=%d (2,300)=%d  -> all three >2: %s' % (name, c02, c2300, good))

    # --- 4. unique root of each cubic in the given (0,1) intervals ---
    cubics = [('f1', f1, (1, 100), (1, 50)),
              ('f1b', f1, (1, 5), (6, 25)),
              ('f2', f2, (1, 500), (1, 250)),
              ('f3', f3, (2, 25), (1, 10)),
              ('f3b', f3, (2, 5), (11, 25)),
              ('f4', f4, (1, 50), (1, 25))]
    for name, poly, lo, hi in cubics:
        c = count_roots_on(poly, X, lo, hi)
        ok &= (c == 1)
        print('%s root count in (%s,%s) = %d' % (name, lo, hi, c))

    # --- 5. alpha formula endpoints (exact rational outputs) ---
    # alpha_lambda = -N(p)*lambda/(169*f'(p)),  p=1/lambda,  lambda = 1/p
    # Only endpoint evaluations are printed; the positivity is certified in
    # q6_sign_cert.py (exact sign of N(p)*f'(p) on isolating intervals).
    def N_of(fname):
        return {'f1': -(17*X**2 - 3443*X + 374),
                'f2': -(17*X**2 - 748*X + 1130),
                'f3': -(43*X**2 - 827*X + 184),
                'f4': -(43*X**2 - 375*X + 291)}[fname]

    print('alpha endpoints (exact rational p in (0,1), lambda=1/p):')
    for name, poly, lo, hi in cubics:
        n_exp = N_of({'f1': 'f1', 'f1b': 'f1', 'f2': 'f2', 'f3': 'f3',
                      'f3b': 'f3', 'f4': 'f4'}[name])
        fp = sp.diff(poly, X)
        lo_f, hi_f = clamp_frac(lo, hi)
        vals = []
        for p in (lo_f, hi_f):
            Np = sp.Rational(sp.expand(n_exp).subs(X, p))
            fpv = sp.Rational(sp.expand(fp).subs(X, p))
            vals.append(-Np * (Fraction(1) / p) / (169 * fpv))
        assert all(v > 0 for v in vals), 'alpha endpoints must be positive'
        print('  %s: alpha(lo)=%s alpha(hi)=%s' % (name, vals[0], vals[1]))

    print('ALL EXACT SCREENING CHECKS PASSED:', ok)
    return 0 if ok else 1


if __name__ == '__main__':
    raise SystemExit(main())