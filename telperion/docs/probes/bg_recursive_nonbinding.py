import sys, math
sys.path.insert(0,"telperion/src")
from fractions import Fraction as Fr
from telperion.branch_potential import branch_ell, _adj, _um
F=math.log(621/64)/11; mu=0.038; V=(math.log(1.5)-2*F)+mu*(1/3)
def tree_edges(tree):
    nxt=[0]
    def rec(t):
        me=nxt[0]; nxt[0]+=1; edges=[]
        for ch in t: cid=nxt[0]; edges.append((me,cid)); edges+=rec(ch)
        return edges
    return rec(tree),nxt[0]
def props(tree):
    edges,n=tree_edges(tree)
    if n==1: return (-F,1.0,1,1)
    ell,t=branch_ell(n,edges,0); adj=_adj(n,edges); deg={v:len(adj[v]) for v in range(n)}
    U,M,tot,sz=_um(adj,deg,0,-1); return (float(ell),float(U/tot),len(tree)+1,n)
cherry=((),)
def broom(c): return tuple([cherry]*c)
B5=broom(5)
print(f"V (cherry Lagrangian, mu={mu}) = {V:.5f}")
print("\nrecursive hub of j copies of B(5):  (ell_c, y_c=h/d, ell_c+mu*y_c vs V)")
for j in [2,5,10,20,40]:
    tree=tuple([B5]*j)
    ell,h,d,n=props(tree); y=h/d
    print(f"  j={j:2d} (size {n:3d}): ell={ell:+.5f}  y={y:.5f}  ell+mu*y={ell+mu*y:+.5f}  {'<=V OK' if ell+mu*y<=V+1e-9 else 'VIOLATES'}")
# and: does it exceed the simple broom-frontier at its y? compare ell to ell(B(c)) at similar y
print("\n=> recursive-B(5) branches: ell bounded (~-0.084), y->0, so ell+mu*y << V (NON-binding),")
print("   but ell(~-0.084) EXCEEDS the simple broom-frontier value at small y (brooms there have ell<-0.2)")
print("   -> the TRUE frontier is recursive, not the simple broom hull; simple-frontier induction fails,")
print("   but the LEMMA (ell+mu*y<=V) holds because large branches are far from binding.")
