# -*- coding: utf-8 -*-
# seam_id_v2.py : 坐标修正版接缝分解 (2026-08-22 审稿后重写)
# 定理(对两块 R = 上块 w*q + 下块 w*(h-q) 平移 s, |s|<w, s!=0, h*w 偶):
#   T(w,h) = TID + sum_{P in 2^[0,w), P!=0} U_P * W_P(0)
#   t(R)   = TID + sum_{P in 2^overlap, P!=0} U_P * W_{P-s}(0)   (坐标修正: 局部列 P-s)
#   overlap = [max(0,s), min(w,w+s))
#   缺口 T-t(R) = Ga + Gb
#     Ga = sum_{P not subseteq overlap, P!=0} U_P * W_P(0)        (非重叠列项, >=0)
#     Gb = sum_{emptyset != P subseteq overlap} U_P * (W_P(0) - W_{P-s}(0))
# 双重检查: (A) 恒等式 T-t(R)==Ga+Gb  (B) Ga>0  (C) Gb>=0  (D) t(R)<T(w,h)
import itertools
from functools import lru_cache

def tcount(pts):
    pts=list(pts); idx={p:i for i,p in enumerate(pts)}; n=len(pts); full=(1<<n)-1
    adj={p:[q for q in ((p[0]+1,p[1]),(p[0]-1,p[1]),(p[0],p[1]+1),(p[0],p[1]-1)) if q in idx] for p in pts}
    @lru_cache(maxsize=None)
    def c(covered):
        if covered==full: return 1
        t=full^covered; f=(t&-t).bit_length()-1; p=pts[f]; s=0
        for q2 in adj[p]:
            j=idx[q2]
            if not((covered>>j)&1): s+=c(covered|(1<<f)|(1<<j))
        return s
    return c(0)

def U(w,q,P): return tcount([(rr,cc) for rr in range(q) for cc in range(w) if not(rr==q-1 and cc in P)])
def Wloc(w,r,X): return tcount([(rr,cc) for rr in range(r) for cc in range(w) if not(rr==0 and cc in X)])

def main():
    fail_id=0; fail_ga=0; fail_gb=0; fail_gap=0; total=0
    ga_min=None; gap_min=None; gb_neg=0
    for h in range(2,9):
        for w in range(2,9):
            if h*w%2: continue
            Twh = tcount([(r,c) for r in range(h) for c in range(w)])
            for q in range(1,h):
                r=h-q
                for s in [x for x in range(-6,7) if x!=0]:
                    if abs(s)>=w: continue
                    total+=1
                    ol=max(0,s); orr=min(w,w+s)
                    Ga=0; Gb=0
                    for k in range(0,w+1):
                        for P in itertools.combinations(range(w),k):
                            P=frozenset(P)
                            if not P: continue
                            u=U(w,q,P); wp=Wloc(w,r,P)
                            sub_overlap = all(ol<=c<orr for c in P)
                            if sub_overlap:
                                Xs=frozenset(c-s for c in P)
                                Gb += u*(wp - Wloc(w,r,Xs))
                            else:
                                Ga += u*wp
                    tR = tcount([(rr,cc) for rr in range(q) for cc in range(w)]+
                                [(rr,cc) for rr in range(q,h) for cc in range(s,s+w)])
                    gap=Twh-tR
                    if gap!=Ga+Gb: fail_id+=1
                    if Ga<=0:
                        fail_ga+=1
                    if ga_min is None or Ga<ga_min[0]: ga_min=(Ga,(h,w,q,s))
                    if Gb<0:
                        fail_gb+=1; gb_neg+=1
                    if gap<=0: fail_gap+=1
                    if gap_min is None or gap<gap_min[0]: gap_min=(gap,(h,w,q,s))
    print('=== seam_id_v2 coordinate-fixed ===')
    print('cases=%d  (A)ID_fail=%d  (B)Ga<=0=%d Ga_min=%s  (C)Gb<0=%d  (D)gap<=0=%d gap_min=%s'%(
        total,fail_id,fail_ga,ga_min,gb_neg,fail_gap,gap_min))
    # 汇总
    txt=('cases=%d id_fail=%d ga_fail=%d ga_min=%s gb_neg=%d gap_fail=%d gap_min=%s\n'%(
        total,fail_id,fail_ga,ga_min,gb_neg,fail_gap,gap_min))
    import os
    try:
        with open(r'D:\smartrabbit\domino_max\seam_id_v2_results.txt','w',encoding='utf-8') as f:
            f.write(txt)
    except PermissionError:
        with open(os.path.join(os.environ['TEMP'],'seam_id_v2_results.txt'),'w',encoding='utf-8') as f:
            f.write(txt); print('(result also written to TEMP)')

if __name__=='__main__':
    main()