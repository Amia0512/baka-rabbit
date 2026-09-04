# -*- coding: utf-8 -*-
# ga_construct_check.py : 引理A(Ga>0)三情形显式构造的合法性复核 (2026-08-22)
# 验证: 对 wh 偶, 0<|s|<w, 按 w,q,r 奇偶选 P 与构造, 得到 U 侧与 W 侧合法平铺(每格恰好一次,骨牌相邻),
#       且 P 不包含于 overlap(即 P 含非重叠列) => Ga >= U_P*W_P >= 1.
import itertools

def tcount(pts):
    pts=list(pts); idx={p:i for i,p in enumerate(pts)}; n=len(pts); full=(1<<n)-1
    adj={p:[q for q in ((p[0]+1,p[1]),(p[0]-1,p[1]),(p[0],p[1]+1),(p[0],p[1]-1)) if q in idx] for p in pts}
    from functools import lru_cache
    @lru_cache(maxsize=None)
    def c(covered):
        if covered==full: return 1
        t=full^covered; f=(t&-t).bit_length()-1; p=pts[f]; s=0
        for q2 in adj[p]:
            j=idx[q2]
            if not((covered>>j)&1): s+=c(covered|(1<<f)|(1<<j))
        return s
    return c(0)

# ---- 三情形显式构造: 输入 (w, rows, P) 输出骨牌列表 ----
def construct(w, rows, P):
    # 情形1: w 偶, P={0,w-1}
    if w%2==0 and P==frozenset((0,w-1)):
        dom=[]
        for r in range(rows-1):            # 行 0..rows-2 全横放
            for c in range(0,w,2): dom.append(((r,c),(r,c+1)))
        for c in range(1,w-1,2):           # 顶行剩列 1..w-2 (偶) 横放
            dom.append(((rows-1,c),(rows-1,c+1)))
        return dom
    # 情形2: w 奇 rows 奇, P={0}
    if w%2==1 and rows%2==1 and P==frozenset((0,)):
        dom=[]
        r=0
        while r+1<=rows-2:                 # 行对 (0,1),(2,3),..,(rows-3,rows-2) 全列竖放
            for c in range(w): dom.append(((r,c),(r+1,c)))
            r+=2
        for c in range(1,w-1,2):           # 顶行剩列 1..w-1 (偶) 横放
            dom.append(((rows-1,c),(rows-1,c+1)))
        return dom
    # 情形3: w 奇 rows 偶, P={0,1}
    if w%2==1 and rows%2==0 and P==frozenset((0,1)):
        dom=[]
        r=0
        while r+2<=rows-2:                 # 行对 (0,1),..,(rows-4,rows-3) 全列竖放
            for c in range(w): dom.append(((r,c),(r+1,c)))
            r+=2
        # 末两行 rows-2, rows-1
        dom.append(((rows-2,0),(rows-2,1)))
        for c in range(2,w): dom.append(((rows-2,c),(rows-1,c)))
        return dom
    return None

def check(w, rows, P):
    dom = construct(w, rows, P)
    if dom is None: return None, 'NO_CONSTRUCT'
    cells=set((r,c) for r in range(rows) for c in range(w) if not (r==rows-1 and c in P))
    # 注意: 挖格统一在顶行(行 rows-1) 是本脚本约定(U侧); W侧挖底行需先转置处理
    cover=set()
    for (a,b) in dom:
        if not (a in cells and b in cells): return dom, 'OUTSIDE'
        if abs(a[0]-b[0])+abs(a[1]-b[1])!=1: return dom, 'NOT_ADJ'
        if a in cover or b in cover: return dom, 'OVERLAP'
        cover.add(a); cover.add(b)
    if cover!=cells: return dom, 'INCOMPLETE'
    return dom, 'OK'

def verify_side(w, rows, P, flip):
    # 支持镜像 P: 若 P 是 {w-1} 或 {w-2,w-1}, 先构造标准 P'={0}/{0,1}, 再镜像骨牌
    Pmir = frozenset(w-1-c for c in P)
    std = P if P in (frozenset((0,)), frozenset((0,1)), frozenset((0,w-1))) else (Pmir if Pmir in (frozenset((0,)), frozenset((0,1)), frozenset((0,w-1))) else None)
    if std is None: return None, 'NO_CONSTRUCT'
    dom = construct(w, rows, std)
    if dom is None: return None, 'NO_CONSTRUCT'
    if std!=P:
        dom=[((a[0],w-1-a[1]),(b[0],w-1-b[1])) for (a,b) in dom]
    if flip:
        dom=[((rows-1-a[0],a[1]),(rows-1-b[0],b[1])) for (a,b) in dom]
    cells=set((r,c) for r in range(rows) for c in range(w) if not ((r==rows-1 if not flip else r==0) and c in P))
    cover=set()
    for (a,b) in dom:
        if not (a in cells and b in cells): return dom, 'OUTSIDE'
        if abs(a[0]-b[0])+abs(a[1]-b[1])!=1: return dom, 'NOT_ADJ'
        if a in cover or b in cover: return dom, 'OVERLAP'
        cover.add(a); cover.add(b)
    if cover!=cells: return dom, 'INCOMPLETE'
    return dom, 'OK'

def mirror(dom, w):
    return [((a[0],w-1-a[1]),(b[0],w-1-b[1])) for (a,b) in dom]

def main():
    fails=[]; n=0; case_cnt={1:0,2:0,3:0}
    for h in range(2,9):
        for w in range(2,9):
            if (h*w)%2: continue
            for q in range(1,h):
                r=h-q
                for s in list(range(-(w-1),0))+list(range(1,w)):
                    n+=1
                    # 选 P 与情形
                    if w%2==0:
                        P=frozenset((0,w-1)); c1=1
                    elif q%2==1:   # w奇 q奇 => 需 r 奇 (wh偶 => wq,wr 同奇偶)
                        P=frozenset((0,)); c1=2
                    else:          # w奇 q偶 => r 偶
                        P=frozenset((0,1)); c1=3
                    # 镜像: s<0 时取 P' = mirror(P)  (u/w 构造同步镜像)
                    if s<0:
                        P=frozenset(w-1-c for c in P)
                    case_cnt[c1]+=1
                    # overlap
                    ol=max(0,s); orr=min(w,w+s); sub_ol=all(ol<=c<orr for c in P)
                    dU,stU=verify_side(w,q,P,flip=False)
                    dW,stW=verify_side(w,r,P,flip=True)
                    if sub_ol: fails.append(('P_IN_OVERLAP',h,w,q,s,P))
                    if stU!='OK': fails.append(('U_'+stU,h,w,q,s,P))
                    if stW!='OK': fails.append(('W_'+stW,h,w,q,s,P))
                    # 独立性: U_P>=1, W_P>=1 (构造即证), 且 Ga>=1
                    if len(fails)>200: break
                if len(fails)>200: break
            if len(fails)>200: break
        if len(fails)>200: break
    print('configs=%d case1/2/3=%s fails=%d'%(n,list(case_cnt.values()),len(fails)))
    for f in fails[:5]: print('FAIL',f)
    # 抽样: 直接数 U_P, W_P 确定 >=1
    import random
    random.seed(1)
    samp=[]
    for _ in range(60):
        h=random.randint(2,7); w=random.randint(2,7)
        if h*w%2: continue
        q=random.randint(1,h-1); r=h-q
        s=random.choice([x for x in range(-(w-1),w) if x!=0])
        if w%2==0: P=frozenset((0,w-1))
        elif q%2==1: P=frozenset((0,))
        else: P=frozenset((0,1))
        if s<0: P=frozenset(w-1-c for c in P)
        u=tcount([(rr,cc) for rr in range(q) for cc in range(w) if not(rr==q-1 and cc in P)])
        ww=tcount([(rr,cc) for rr in range(r) for cc in range(w) if not(rr==0 and cc in P)])
        samp.append((h,w,q,r,s,tuple(sorted(P)),u,ww))
    bad=[x for x in samp if x[6]<1 or x[7]<1]
    print('sampled=%d bad=%d'%(len(samp),len(bad)))
    for x in samp[:3]: print('S',x)
    import os
    res='configs=%d case1/2/3=%s fails=%d sampled=%d bad=%d\n'%(n,list(case_cnt.values()),len(fails),len(samp),len(bad))
    with open(os.path.join(os.environ['TEMP'],'ga_construct_results.txt'),'w',encoding='utf-8') as f:
        f.write(res)

if __name__=='__main__':
    main()
