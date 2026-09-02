import sys, math, random
sys.path.insert(0,"telperion/src")
from fractions import Fraction as Fr
from telperion.branch_potential import _adj, _um
def tree_edges(tree):
    nxt=[0]
    def rec(t):
        me=nxt[0]; nxt[0]+=1; edges=[]
        for ch in t: cid=nxt[0]; edges.append((me,cid)); edges+=rec(ch)
        return edges
    return rec(tree),nxt[0]
def umd(tree):
    edges,n=tree_edges(tree)
    if n==1: return Fr(1),Fr(1),1,1
    adj=_adj(n,edges); deg={v:len(adj[v]) for v in range(n)}
    U,M,tot,sz=_um(adj,deg,0,-1); return U,tot,len(tree)+1,n
# KEY IDENTITY: total(hub) = (prod T_i)*(1 + (1/(j+1)) sum y_i),  y_i = h_i/d_i = (U_i/T_i)/d_i
def hub_total_direct(kids):
    j=len(kids); d=j+1; U=Fr(1)
    for U_i,T_i,d_i,_ in kids: U*=T_i
    M=Fr(0)
    for i,(U_i,T_i,d_i,_) in enumerate(kids):
        term=Fr(1,d*d_i)*U_i
        for jj,(U_j,T_j,d_j,_) in enumerate(kids):
            if jj!=i: term*=T_j
        M+=term
    return U+M
def hub_total_identity(kids):
    j=len(kids); prodT=Fr(1); Y=Fr(0)
    for U_i,T_i,d_i,_ in kids:
        prodT*=T_i; Y+=Fr(U_i,T_i)/d_i
    return prodT*(1+Y/(j+1))
random.seed(3)
pool=[umd(t) for t in [(),((),),((),())] ]  # a few branches
import itertools
def gen(N):
    bs={1:[()]}
    for s in range(2,N+1):
        out=set()
        def parts(r,mn,cur):
            if r==0: out.add(tuple(sorted(cur))); return
            for cs in range(mn,r+1):
                for ct in bs.get(cs,[]): parts(r-cs,cs,cur+[(cs,ct)])
        parts(s-1,1,[]); bs[s]=[tuple(t for _,t in tup) for tup in out]
    return bs
bs=gen(10); pool=[umd(t) for s in range(1,11) for t in bs[s]]
ok=True
for _ in range(3000):
    kids=[random.choice(pool) for _ in range(random.randint(1,6))]
    if hub_total_direct(kids)!=hub_total_identity(kids): ok=False; break
print(f"IDENTITY total(hub) = (prod T_i)(1 + (sum y_i)/(j+1)) verified exactly: {ok}")
print("=> log total(hub) = sum log T_i + log(1 + (sum y_i)/(j+1))   -- the SAME hub form as ell,")
print("   so BROOM DOMINANCE (max total) = max [sum log T_i + concave coupling in sum y_i]")
print("   = the SAME tangent-Lagrangian extremal problem as Lemma 1 (child value = log T_c + mu*y_c).")
print("   Lemma 1 (fixed k children) and Lemma A (fixed total size, variable k) are ONE problem,")
print("   both attackable by the concavity-tangent linearization. The (U,total,d) coupling that broke")
print("   the naive exchange is exactly the (log T, y) trade-off the tangent handles.")
