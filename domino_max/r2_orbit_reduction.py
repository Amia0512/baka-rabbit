# -*- coding: utf-8 -*-
import itertools, time
F = [0, 1]
def T_table(q, Lmax):
    n = 1 << q; full = n - 1
    succ = []
    for i in range(n):
        js = []
        sub = full ^ i
        m2 = sub
        while True:
            horiz = full ^ i ^ m2
            run = 0; ok = True
            for b in range(q):
                if (horiz >> b) & 1: run += 1
                else:
                    if run & 1: ok = False; break
                    run = 0
            if run & 1: ok = False
            if ok: js.append(m2)
            if m2 == 0: break
            m2 = (m2 - 1) & sub
        succ.append(js)
    dp = [0]*n; dp[0] = 1
    out = [1]
    for _ in range(Lmax):
        ndp = [0]*n
        for i in range(n):
            v = dp[i]
            if v:
                for j in succ[i]: ndp[j] += v
        dp = ndp
        out.append(dp[0])
    return out
def sign(v): return (v > 0) - (v < 0)
def segs(X, w):
    X = set(X); run = 0; out = []
    for c in range(w):
        if c in X:
            if run: out.append(run); run = 0
        else: run += 1
    if run: out.append(run)
    return out
def u2(X, w):
    p = 1
    for L in segs(X, w): p *= F[L+1]
    return p
def uh(X, w, h):
    p = 1
    for L in segs(X, w): p *= TT[h][L]
    return p
def refl_rov(A, w, s):
    return frozenset(w - 1 + s - c for c in A)
TT = {}
def main():
    global F, TT
    wmax = 12; qmax = 6
    Lmax = wmax + 25
    F = [0, 1]
    for _ in range(Lmax + 2): F.append(F[-1] + F[-2])
    t0 = time.time()
    for q in range(1, qmax + 1):
        TT[q] = T_table(q, Lmax + 5)
    print(f'tables built ({time.time()-t0:.1f}s)')
    bad = []; total = 0; zz = 0
    for w in range(2, wmax + 1):
        for s in range(1, w):
            allP = [frozenset(c) for n in range(0, w - s + 1) for c in itertools.combinations(range(s, w), n)]
            for q in range(1, qmax + 1):
                uq = {P: uh(P, w, q) for P in allP}
                u2m = {P: u2(P, w) for P in allP}
                seen = set()
                for P in allP:
                    if P in seen: continue
                    RP = refl_rov(P, w, s)
                    seen.add(P); seen.add(RP)
                    dq = uq[P] - uq[RP]; d2 = u2m[P] - u2m[RP]
                    if dq == 0 and d2 == 0: zz += 1; continue
                    total += 1
                    if sign(dq) * sign(d2) < 0:
                        bad.append((w, s, q, sorted(P), sorted(RP), dq, d2))
                        if len(bad) <= 12:
                            print(f'NEG w={w} s={s} q={q} P={sorted(P)} RP={sorted(RP)} dq={dq} d2={d2}', flush=True)
        print(f'w={w} done ({time.time()-t0:.1f}s)', flush=True)
    print(f'full-orbit: w<={wmax}, q<={qmax}: 非平凡轨道={total}, 异号={len(bad)}, 双零={zz}')
    if bad:
        print('最小异号:', bad[0])
        print('结论: 逐轨道同号命题破裂')
    else:
        print('结论: 逐轨道同号命题保持 (全域 0 异号)')
if __name__ == '__main__':
    main()
