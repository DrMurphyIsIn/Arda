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
    edges=rec(tree); return edges,nxt[0]
def props(tree):
    edges,n=tree_edges(tree)
    if n==1: return (-F, Fr(1), 1, 1)
    ell,t=branch_ell(n,edges,0); adj=_adj(n,edges); deg={v:len(adj[v]) for v in range(n)}
    U,M,tot,sz=_um(adj,deg,0,-1); return (ell,U/tot,len(tree)+1,n)
# candidate child types
cherry=((),)                    # size-2 branch (armmid+leaf) -- B(k)'s child
def broom(c): return tuple([cherry]*c)   # B(c)
leaf=()                         # size-1
cands={"leaf":leaf,"cherry":cherry,"B(1)":broom(1),"B(2)":broom(2),"B(3)":broom(3),
       "B(4)":broom(4),"B(5)":broom(5)}
P={nm:props(t) for nm,t in cands.items()}
for nm,(ell,h,d,n) in P.items(): print(f"  child {nm:7s}: size {n:2d} ell={float(ell):+.5f} h={float(h):.4f} d={d}")
def hub_ell(child_props,k):
    ell,h,d,n=child_props
    return k*float(ell)+math.log(1+k*float(h)/((k+1)*d))-F
print("\nuniform-hub ell(B) = k*ell(c)+log(1+k*h_c/((k+1)d_c))-F*  ; best child per k:")
for k in [2,3,5,8,12,15,16,18,20,25]:
    scored=sorted(((hub_ell(P[nm],k),nm) for nm in cands), reverse=True)
    top=scored[0]; cherry_val=hub_ell(P["cherry"],k)
    print(f"  k={k:2d}: best={top[1]:7s} ({top[0]:+.5f})   cherry={cherry_val:+.5f}   "
          f"{'CHERRY optimal' if top[1]=='cherry' else 'CROSSOVER: '+top[1]+' beats cherry'}")
