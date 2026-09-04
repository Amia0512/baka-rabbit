# -*- coding: utf-8 -*-
# r=2 逐轨道同号强度 (w<=12, q<=8, 全 P) - 证明分支筛选
import sys, itertools, time
def refl_rov(A, w, s):
    return frozenset(w - 1 + s - c for c in A)
def fib(n):
    a, b = 0, 1
    for _ in range(n): a, b = b, a + b
    return a
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
    segs = []; run = 0
    for c in range(w):
        if c in Pset:
            if run: segs.append(run); run = 0
        else:
            run += 1
    if run: segs.append(run)
    prod = 1
    for L in segs: prod *= T_rect(L, h)
    return prod
def u_2_segprod(Pset, w):
    segs = []; run = 0
    for c in range(w):
        if c in Pset:
            if run: segs.append(run); run = 0
        else:
            run += 1
    if run: segs.append(run)
    prod = 1
    for L in segs: prod *= fib(L + 1)
    return prod
def main():
    t0 = time.time()
    total_orb = 0; neg_orb = 0; cex = []
    for w in range(2, 13):
        for s in range(1, w):
            allP = [frozenset(c) for r in range(0, w - s + 1) for c in itertools.combinations(range(s, w), r)]
            for q in range(1, 9):
                uq = {P: u_h(P, w, q) for P in allP}
                u2 = {P: u_2_segprod(P, w) for P in allP}
                seen = set()
                for P in allP:
                    if P in seen: continue
                    RP = refl_rov(P, w, s)
                    seen.add(P); seen.add(RP)
                    dq = uq[P] - uq[RP]
                    d2 = u2[P] - u2[RP]
                    if dq == 0 and d2 == 0: continue
                    total_orb += 1
                    if dq * d2 < 0:
                        neg_orb += 1
                        if len(cex) < 15:
                            cex.append((w, s, q, sorted(P), sorted(RP), dq, d2))
            sys.stdout.write('w=%d s=%d done (%.0fs)\n' % (w, s, time.time()-t0)); sys.stdout.flush()
    print('r=2 同号 (w<=12, q<=8, 全 P): 非平凡轨道=%d 异号=%d' % (total_orb, neg_orb))
    for c in cex: print('  ', c)
    print('结论:', 'P1 同号强命题保持' if neg_orb == 0 else 'P1 同号破裂')
if __name__ == '__main__':
    main()