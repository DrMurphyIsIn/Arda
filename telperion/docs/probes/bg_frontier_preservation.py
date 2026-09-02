import sys, math
sys.path.insert(0,"telperion/src")
from fractions import Fraction as Fr
from telperion.branch_potential import branch_ell, _adj, _um
F=math.log(621/64)/11
def tree_edges(tree):
    nxt=[0]
    def rec(t):
        me=nxt[0]; nxt[0]+=1; edges=[]
        for ch in t: cid=nxt[0]; edges.append((me,cid)); edges+=rec(ch)
        return edges
    return rec(tree),nxt[0]
def props(tree):  # returns (ell, h, d, n)
    edges,n=tree_edges(tree)
    if n==1: return (-F,1.0,1,1)
    ell,t=branch_ell(n,edges,0); adj=_adj(n,edges); deg={v:len(adj[v]) for v in range(n)}
    U,M,tot,sz=_um(adj,deg,0,-1); return (float(ell),float(U/tot),len(tree)+1,n)
def yof(p): return p[1]/p[2]   # y = h/d
def gen_rooted(N):
    bysize={1:[()]}
    for s in range(2,N+1):
        out=set()
        def parts(r,mn,cur):
            if r==0: out.add(tuple(sorted(cur))); return
            for cs in range(mn,r+1):
                for ct in bysize.get(cs,[]): parts(r-cs,cs,cur+[(cs,ct)])
        parts(s-1,1,[]); bysize[s]=[tuple(t for _,t in tup) for tup in out]
    return bysize
N=13; bysize=gen_rooted(N); trees=[]
for s in range(1,N+1):
    for tr in bysize[s]:
        p=props(tr); trees.append((tr,p[0],yof(p),len(tr)))
# concave upper hull Phi over (y=h/d, ell)
from collections import defaultdict
mx=defaultdict(lambda:-9)
for tr,ell,y,j in trees:
    if ell>mx[round(y,6)]: mx[round(y,6)]=ell
hp=sorted(mx.items())
def cross(o,a,b): return (a[0]-o[0])*(b[1]-o[1])-(a[1]-o[1])*(b[0]-o[0])
up=[]
for p in hp:
    while len(up)>=2 and cross(up[-2],up[-1],p)>=0: up.pop()
    up.append(p)
def Phi(y):
    if y<=up[0][0]: return up[0][1]
    if y>=up[-1][0]: return up[-1][1]
    for i in range(len(up)-1):
        (y0,e0),(y1,e1)=up[i],up[i+1]
        if y0<=y<=y1: return e0+(e1-e0)/(y1-y0)*(y-y0)
    return up[-1][1]
print(f"corrected frontier Phi(y=h/d) hull vertices: {[(round(y,3),round(e,4)) for y,e in up]}")
worst=-9; nbad=0; badex=None
for tr,ell,y,j in trees:
    if j==0: continue
    gs=[yof(props(ch)) for ch in tr]; Y=sum(gs); jj=len(gs)
    L0=math.log((jj+1+Y)/(jj+1))-F
    lhs=sum(Phi(g) for g in gs)+L0; rhs=Phi(y); gap=lhs-rhs
    if gap>worst: worst=gap; badex=(len(tr),jj,round(Y,3),round(lhs,4),round(rhs,4))
    if gap>1e-9: nbad+=1
print(f"\nfrontier preservation Sum Phi(g_i)+L0(Y) <= Phi(y_c): worst gap={worst:+.6f}, violations {nbad}/{len(trees)}")
print("  "+("PRESERVED -> frontier induction CLOSES" if nbad==0 else f"not preserved; worst at {badex}"))
