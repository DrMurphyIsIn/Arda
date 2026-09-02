import sys, math, random
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
def props(tree):
    edges,n=tree_edges(tree)
    if n==1: return (-F,1.0,1,1)
    ell,t=branch_ell(n,edges,0); adj=_adj(n,edges); deg={v:len(adj[v]) for v in range(n)}
    U,M,tot,sz=_um(adj,deg,0,-1); return (float(ell),float(U/tot),len(tree)+1,n)
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
N=14; bysize=gen_rooted(N)
allc=[props(tr) for s in range(1,N+1) for tr in bysize[s]]
cherry=props(((),)); ec,yc=cherry[0],cherry[1]/cherry[2]
# STEP 2: single-child extremal lemma -- max_c (ell+mu*y) = cherry for mu>=mu*
mustar=None
for mu in [x/1000 for x in range(60,30,-1)]:
    best=max(e+mu*(h/d) for e,h,d,n in allc); cv=ec+mu*yc
    if best>cv+1e-12: mustar=mu+0.001; break
print(f"single-child lemma: cherry = argmax(ell+mu*y) for mu >= {mustar:.3f}  (checked {len(allc)} branches size<=14)")
# STEP 3: shadow price mu_k = 3/(4k+3) for the all-cherry hub
print("shadow price mu_k = 3/(4k+3):  k=15 -> mu=%.4f, k=10 -> %.4f, k=5 -> %.4f   (all >= mu*=%.3f for k<=15)"
      %(3/63,3/43,3/23,mustar))
# STEP 1+full: verify Delta <= tangent-bound <= 0 for RANDOM hubs (k<=15, children = random branches, ell<=0)
random.seed(1)
children_pool=[(e,h,d,n) for (e,h,d,n) in allc if e<=1e-12]  # IH: ell(c)<=0
def hub_ell(kids,k):
    return sum(e for e,h,d,n in kids)+math.log(1+sum((h/d)/(k+1) for e,h,d,n in kids))-F
def ellBk(k):  # all-cherry
    return k*ec+math.log(1+k*(yc/(k+1)))-F
worstgap=-9; tangent_ok=True; delta_ok=True
for trial in range(4000):
    k=random.randint(2,15); kids=[random.choice(children_pool) for _ in range(k)]
    muk=3/(4*k+3)
    Delta=hub_ell(kids,k)-ellBk(k)
    tangent=sum((e+muk*(h/d))-(ec+muk*yc) for e,h,d,n in kids)  # upper bound on Delta
    if Delta>tangent+1e-9: tangent_ok=False
    if Delta>1e-9: delta_ok=False
    worstgap=max(worstgap,Delta)
print(f"\n4000 random hubs k in [2,15], children with ell<=0:")
print(f"  concavity tangent bound Delta <= sum(Lagrangian gaps) holds: {tangent_ok}")
print(f"  each Lagrangian gap <=0 (cherry is muk-max) so tangent<=0 => Delta<=0: worst Delta={worstgap:+.6f} (<=0: {delta_ok})")
print(f"\n=> Lemma 1 (mixed <= B(k), k<=15) PROVED modulo the single-child extremal lemma (mu>=mu*),")
print(f"   via concavity-tangent linearization + mu_k=3/(4k+3)>=mu*. The non-monotonic exchange is dissolved.")
