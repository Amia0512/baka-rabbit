# -*- coding: utf-8 -*-
# 独立校验：正式 P-s 口径下的三个中间恒等式 (2026-08-24, 证明草稿回归)
#  E1: CI = sum_{P in B} u_q(P) * (u_r(P) - u_r(P-s))        (定义)
#  E2: CI = sum_{P in B} u_q(P) * (u_r(P) - u_r(R(P)))       (引理2: u_r(R(P))=u_r(P-s))
#  E3: CI = sum_P (u_q(P)-u_q(P-s)) * (u_r(P)-u_r(P-s)) / 2  (SYM 轨道平均)
#  E4: CI = sum_Q c_q(Q)*u_r(Q)                              (系数重排，真实计数 u_h)
import sys, itertools
def mof(A):
    m = 0
    for c in A: m |= 1 << c
    return m
def shift(A, d):
    return frozenset(c + d for c in A)
def refl_rov(A, w, s):
    return frozenset(w - 1 + s - c for c in A)
def phi(A, w):
    return frozenset(w - 1 - c for c in A)
def T_rect(k, h):
    if k == 0: return 1
    n = 1 << k; full = n - 1
    succ = []
    for i in range(n):
        js = []
        for j in range(n):
            if j & i: continue
            hc = full ^ i ^ j
            run = 0; ok = True
            for b in range(k):
                if (hc >> b) & 1: run += 1
                else:
                    if run & 1: ok = False; break
                    run = 0
            if run & 1: ok = False
            if ok: js.append(j)
        succ.append(js)
    vec = [0]*n; vec[0] = 1
    for _ in range(h):
        nv = [0]*n
        for i in range(n):
            nv[i] = sum(vec[j] for j in succ[i])
        vec = nv
    return vec[0]
def u_h(Pset, w, h):
    segs = []
    run = 0
    for c in range(w):
        if c in Pset:
            if run: segs.append(run); run = 0
        else:
            run += 1
    if run: segs.append(run)
    prod = 1
    for L in segs: prod *= T_rect(L, h)
    return prod
def main():
    fails = []
    ncfg = 0
    for w in range(2, 7):
        Bs = [frozenset(c) for r in range(1, w - s + 1) for c in itertools.combinations(range(s, w), r)] if False else None
        for s in range(1, w):
            allP = [frozenset(c) for r in range(0, w - s + 1) for c in itertools.combinations(range(s, w), r)]
            allQ = [frozenset(c) for r in range(0, w + 1) for c in itertools.combinations(range(0, w), r)]
            for q in range(1, 5):
                for r in range(1, 5):
                    ncfg += 1
                    uq = {P: u_h(P, w, q) for P in allQ}
                    ur = {P: u_h(P, w, r) for P in allQ}
                    E1 = sum(uq[P] * (ur[P] - ur[shift(P, -s)]) for P in allP)
                    E2 = sum(uq[P] * (ur[P] - ur[refl_rov(P, w, s)]) for P in allP)
                    # 逐项核心: u_r(R(P)) == u_r(P-s)
                    inner_fail = 0
                    for P in allP:
                        if ur[refl_rov(P, w, s)] != ur[shift(P, -s)]:
                            inner_fail += 1
                    E3 = sum((uq[P] - uq[shift(P, -s)]) * (ur[P] - ur[shift(P, -s)]) for P in allP) / 2.0
                    c_full = {Q: 0 for Q in allQ}
                    for P in allP: c_full[P] += uq[P]
                    for P in allP: c_full[shift(P, -s)] -= uq[P]
                    E4 = sum(c_full[Q] * ur[Q] for Q in allQ)
                    for tag, v in (('E1E2', E1 - E2), ('E1E3', E1 - E3), ('E1E4', E1 - E4)):
                        if abs(v) > 1e-9:
                            fails.append((w, s, q, r, tag, v))
                    if inner_fail:
                        fails.append((w, s, q, r, 'INNER', inner_fail))
    print('ncfg=%d 恒等式偏差=%d' % (ncfg, len(fails)))
    for f in fails[:20]: print(f)
    sys.exit(1 if fails else 0)
if __name__ == '__main__':
    main()