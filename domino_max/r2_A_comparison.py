# -*- coding: utf-8 -*-
# 最终 A 级大扫描: sign(A_q(l,r;s))==sign(A_2(l,r;s)) 全域
import time
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
def main():
    qmax = 12; smax = 25; lmax = 120; rmax = 120
    Lmax = lmax + smax + 5
    T = {}; t0 = time.time()
    for q in range(1, qmax + 1): T[q] = T_table(q, Lmax)
    print(f'tables built ({time.time()-t0:.1f}s)')
    neg = []; total = 0; zz = 0
    for q in range(2, qmax + 1):
        Tq = T[q]
        for s in range(1, smax + 1):
            for l in range(s, lmax + 1):
                for r in range(0, rmax + 1):
                    A2 = T[2][l]*T[2][r] - T[2][l-s]*T[2][r+s]
                    Aq = Tq[l]*Tq[r] - Tq[l-s]*Tq[r+s]
                    sg2 = sign(A2); sgq = sign(Aq)
                    if sg2 == 0 and sgq == 0: zz += 1; continue
                    total += 1
                    if sg2 * sgq < 0:
                        neg.append((q, s, l, r, Aq, A2))
                        if len(neg) <= 10:
                            print(f'NEG q={q} s={s} l={l} r={r} Aq={Aq} A2={A2}', flush=True)
    print(f'A-final: q<={qmax}, s<={smax}, l,r<={lmax}: 非零检查={total}, 反例={len(neg)}, 双零={zz}')
    print(f'用时 {time.time()-t0:.1f}s')
    if neg:
        print('最小反例:', sorted(neg, key=lambda z: (z[0], z[1], z[2], z[3]))[0])
    else:
        print('结论: A 级全域 0 反例 (最终大扫描)')
if __name__ == '__main__':
    main()
