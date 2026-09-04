# -*- coding: utf-8 -*-
# tm_obstacle_check.py : 统一 transfer matrix（论文 §2.2）的可复现实现与回归校验 (2026-08-24)
#
# 定义（与论文 §2.2 完全一致）：
#   - 状态 = 边界 mask σ ⊆ [0,w)，记录当前行哪些格已被上一行的竖骨牌覆盖。
#   - 转移 T_w[σ][τ] = 1 当且仅当 [0,w)\(σ∪τ) 的每个极大连续段长度为偶数
#     （即当前行剩余格可由横骨牌两两覆盖），且 σ∩τ=∅（同一格不能同时进出）。
#   - 障碍列 P：σ,τ 必须避开 P（不允许竖骨牌接触障碍列），且横填只能在非障碍列上，
#     障碍列把行切成互不跨越的段。
#   - u_h(P) = 从 σ=∅ 出发迭代 h 次，取末端 mask=∅ 的分量（底部没有竖骨牌伸出）。
# 校验：u_h(P) 与直接完美匹配递归在 w≤6, h≤4, 全 P 上一致（0 失败）。
import sys, itertools
from functools import lru_cache

def pmask(w, P):
    m = 0
    for c in P: m |= 1 << c
    return m

def build_T(w, P):
    pm = pmask(w, P)
    states = [i for i in range(1 << w) if not (i & pm)]
    sidx = {s: i for i, s in enumerate(states)}
    n = len(states)
    T = [[0] * n for _ in range(n)]
    for i in states:
        for j in states:
            if (j & i) or (j & pm):
                continue                      # 进出 mask 不相交；不能碰障碍列
            hcells = (((1 << w) - 1) ^ i ^ j) & (((1 << w) - 1) ^ pm)  # 横填格
            run = 0; ok = True
            for b in range(w):
                if (hcells >> b) & 1:
                    run += 1
                else:
                    if run & 1: ok = False; break
                    run = 0
            if run & 1: ok = False
            if ok: T[sidx[i]][sidx[j]] = 1
    return T, states, sidx

def u_h(w, P, h):
    T, states, sidx = build_T(w, P)
    n = len(states); s0 = sidx[0]
    vec = [0] * n; vec[s0] = 1
    for _ in range(h):
        vec = [sum(vec[k] * T[k][j] for k in range(n)) for j in range(n)]
    return vec[s0]                              # 末端 mask 必须为空

def tcount(pts):
    pts = list(pts); idx = {p: i for i, p in enumerate(pts)}; n = len(pts); full = (1 << n) - 1
    adj = {p: [q for q in ((p[0]+1,p[1]),(p[0]-1,p[1]),(p[0],p[1]+1),(p[0],p[1]-1)) if q in idx] for p in pts}
    @lru_cache(maxsize=None)
    def c(covered):
        if covered == full: return 1
        t = full ^ covered; f = (t & -t).bit_length() - 1; p = pts[f]; s = 0
        for q2 in adj[p]:
            j = idx[q2]
            if not ((covered >> j) & 1): s += c(covered | (1 << f) | (1 << j))
        return s
    return c(0)

def direct(w, h, P):
    return tcount([(r, c) for r in range(h) for c in range(w) if c not in P])

def main():
    fails = 0; n = 0
    for w in range(2, 7):
        for h in range(1, 5):
            for k in range(1 << w):
                P = [c for c in range(w) if (k >> c) & 1]
                n += 1
                a = u_h(w, P, h); b = direct(w, h, P)
                if a != b:
                    fails += 1
                    print('MISMATCH', w, h, P, a, b)
    seq = [u_h(2, [], k) for k in range(0, 7)]
    print('T(2,0..6) =', seq, '(expect 1,1,2,3,5,8,13)')
    print('obstacle transfer vs direct: n=%d fails=%d' % (n, fails))
    if fails: sys.exit(1)

if __name__ == '__main__':
    main()