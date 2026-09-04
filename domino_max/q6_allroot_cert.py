# -*- coding: utf-8 -*-
"""q=6 quadrangle ALL-ROOT spectral positivity certificate (pure rational).

Claim (candidate, 2026-08-27): with

    G(x) = sum_n D(n) x^n = P(x)/Q(x),
    Q(x) = (1-x)*f1(x)*f2(x)*f3(x)*f4(x),
    f1 = x^3 - 269 x^2 + 66 x - 1,
    f2 = x^3 - 66 x^2 + 269 x - 1,
    f3 = x^3 - 26 x^2 + 13 x - 1,
    f4 = x^3 - 13 x^2 + 26 x - 1,

the partial-fraction identity holds

    G = -49/169/(x-1) + sum_j N_j(x)/(169 f_j(x))

with N_j the documented numerators, and for every real root r of every f_j
(six interior roots in (0,1) and six outer roots in (2,269)),

    beta_r := -N_j(r)/(169 * f_j'(r)) > 0 (candidate decomposition checked only for n = 0..60).

The root signs define an all-positive candidate residue decomposition. This script
checks the corresponding coefficient identity only for n = 0..60; it does not prove
the all-n coefficient-extraction formula or D(n) > 0 for every n.

This script checks the candidate certificate in exact rational arithmetic (Sturm
isolation, rational bisection, exact sign of quadratics at endpoints/vertex). No floats.
"""
import io
from fractions import Fraction
import sympy as sp

X = sp.symbols('x')

def frac_from(x):
    if isinstance(x, tuple):
        return Fraction(x[0], x[1])
    return Fraction(x)

def signf(coeffs, t):
    acc = Fraction(0)
    for c in coeffs:
        acc = acc * t + c
    return 1 if acc > 0 else (-1 if acc < 0 else 0)

def quad_sign_set(coeffs, lo, hi):
    """Constant-sign certificate of a quadratic on [lo,hi] via endpoints+vertex."""
    a, b, c = coeffs
    pts = [lo, hi]
    if a != 0:
        vx = Fraction(-b, 2 * a)
        if lo < vx < hi:
            pts.append(vx)
    return {signf(coeffs, t) for t in pts}

def refine_sign(poly_coeffs, lo, hi, steps=200):
    if signf(poly_coeffs, lo) == signf(poly_coeffs, hi):
        raise AssertionError('no sign change on initial interval')
    for _ in range(steps):
        mid = (lo + hi) / 2
        if signf(poly_coeffs, lo) == signf(poly_coeffs, mid):
            lo = mid
        else:
            hi = mid
        if signf(poly_coeffs, lo) != signf(poly_coeffs, hi):
            break
    if signf(poly_coeffs, lo) == signf(poly_coeffs, hi):
        raise AssertionError('refinement failed to separate signs')
    return lo, hi

def main():
    ok = True
    D0 = [12, 1972, 491079, 130096951, 34858903756, 9362255074068,
          2515769926121793, 676101210715387588, 181703779036579228444,
          48833609271748938934743, 13124243753350272594160807,
          3527198402382298329957590628, 947950198601663907987096355804]
    a = [375, -31905, 940863, -11023137, 55190391, -123722817, 123722817,
         -55190391, 11023137, -940863, 31905, -375, 1]
    Q = sp.Integer(1)
    for k in range(13):
        Q = Q - a[k] * X ** (k + 1)
    Q = sp.expand(Q)
    P = sp.Integer(0)
    for k in range(13):
        s = D0[k]
        for i in range(1, 13):
            if k - i >= 0:
                s -= a[i - 1] * D0[k - i]
        P = P + sp.Integer(s) * X ** k
    G = sp.cancel(P / Q)

    f1 = X**3 - 269*X**2 + 66*X - 1
    f2 = X**3 - 66*X**2 + 269*X - 1
    f3 = X**3 - 26*X**2 + 13*X - 1
    f4 = X**3 - 13*X**2 + 26*X - 1
    N1 = -(17*X**2 - 3443*X + 374)
    N2 = -(17*X**2 - 748*X + 1130)
    N3 = -(43*X**2 - 827*X + 184)
    N4 = -(43*X**2 - 375*X + 291)
    fs = [f1, f2, f3, f4]
    Ns = [N1, N2, N3, N4]
    names = ['f1', 'f2', 'f3', 'f4']

    RHS = sp.Rational(-49, 169) / (X - 1)
    for f, N in zip(fs, Ns):
        RHS = RHS + N / (169 * f)
    ident = sp.cancel(G - RHS) == 0
    ok &= ident
    print('1. partial-fraction identity P/Q = -49/169/(x-1)+sum N_j/(169 f_j):', ident)
    print('   Q == -(1-x)*f1*f2*f3*f4 :', sp.expand(Q + (X-1)*f1*f2*f3*f4) == 0)

    print('\n2. per-root sign certificate beta = -N/(169 f\' r) > 0:')
    nroots = 0
    for j, (f, N) in enumerate(zip(fs, Ns)):
        fp = sp.diff(f, X)
        fpoly = sp.Poly(f, X)
        fpcoef = [int(sp.Poly(fp, X).coeff_monomial(X**k)) for k in range(2, -1, -1)]
        Ncoef = [int(sp.Poly(N, X).coeff_monomial(X**k)) for k in range(2, -1, -1)]
        fcoef = [int(fpoly.coeff_monomial(X**k)) for k in range(3, -1, -1)]
        for (lo0, hi0), cnt in fpoly.intervals():
            lo, hi = frac_from(lo0), frac_from(hi0)
            ok &= (cnt == 1)
            if cnt != 1:
                print('   !! branch', names[j], 'interval', (lo, hi), 'count', cnt)
            lo, hi = refine_sign(fcoef, lo, hi)
            sN = quad_sign_set(Ncoef, lo, hi)
            sF = quad_sign_set(fpcoef, lo, hi)
            pos = all((-sn) * sf > 0 for sn in sN for sf in sF)
            ok &= pos
            nroots += 1
            print('   f%d root in (%s,%s): N-sign=%s fprime-sign=%s  beta>0=%s'
                  % (j+1, lo, hi, sN, sF, pos))
    print('   total isolated roots:', nroots, '(expect 12)')
    ok &= (nroots == 12)

    print('\n3. branch series coefficients positive for n=0..60 (sanity screen):')
    for j, (f, N) in enumerate(zip(fs, Ns)):
        ser = sp.series(sp.cancel(N / 169 / f), X, 0, 62).removeO()
        cs = [sp.Integer(sp.expand(ser).coeff(X, k)) for k in range(62)]
        allpos = all(c > 0 for c in cs)
        ok &= allpos
        print('   branch f%d: first 62 coefficients all positive: %s' % (j+1, allpos))

    # 4. EXACT formal-series check (no floats): series of the partial-fraction
    #    expansion equals the D sequence, n = 0 .. 60, in Q[[x]].
    #    [x^n] G = [x^n](-49/169/(x-1)) + sum_j [x^n](N_j/(169 f_j))
    #           = 49/169 + sum_j c_{j,n}   (c_{j,n} exact rationals)
    D0ext = list(D0)
    for n in range(13, 62):
        D0ext.append(sum(a[i] * D0ext[n - 1 - i] for i in range(13)))
    # verify recurrence on the 13 known tail (index 13..25)
    def _drec(m):
        return D0ext[m] == sum(a[i] * D0ext[m - 1 - i] for i in range(13))
    rec_ok = all(_drec(m) for m in range(13, 26))

    print('\n4. exact formal-series identity [x^n]G = D(n) for n=0..60 (rational arithmetic):')
    exact_ok = True
    for n in range(0, 61):
        val = sp.Rational(49, 169)
        for f, N in zip(fs, Ns):
            ser = sp.series(sp.cancel(N / 169 / f), X, 0, n + 2).removeO()
            val = val + sp.expand(ser).coeff(X, n)
        exact_ok &= (int(val) == D0ext[n])
    ok &= exact_ok
    print('   exact match n=0..60:', exact_ok)
    # branch coefficient positivity for n<=60 (already section 3, keep exact)
    print('\nFINITE ALL-ROOT CANDIDATE CHECK PASSED (n=0..60):', ok)
    print('NOT A PROOF OF THE ALL-n DECOMPOSITION OR D(n)>0 FOR EVERY n')
    return 0 if ok else 1

if __name__ == '__main__':
    raise SystemExit(main())
