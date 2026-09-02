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
def umd(tree):  # returns (U, total, d_root, size)
    edges,n=tree_edges(tree)
    if n==1: return Fr(1),Fr(1),1,1
    adj=_adj(n,edges); deg={v:len(adj[v]) for v in range(n)}
    U,M,tot,sz=_um(adj,deg,0,-1); return U,tot,len(tree)+1,n
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
N=12; bysize=gen_rooted(N)
# champion per size = max total(B)
champ={}
for s in range(1,N+1):
    best=None
    for tr in bysize[s]:
        U,tot,d,n=umd(tr)
        if best is None or tot>best[1]: best=(tr,tot,U,d)
    champ[s]=best
for s in range(1,N+1):
    tr,tot,U,d=champ[s]; print(f"size {s:2d}: champion total={float(tot):.5f} d_root={d}  (is broom if odd)")
# hub total from children (U_i,tot_i,d_i): d_hub=len(children)+1; U=prod tot_i; M=sum (1/(d_hub d_i)) U_i prod_{j!=i} tot_j
def hub_total(kids):
    j=len(kids); d=j+1; U=Fr(1)
    for U_i,tot_i,d_i,_ in kids: U*=tot_i
    M=Fr(0)
    for i,(U_i,tot_i,d_i,_) in enumerate(kids):
        term=Fr(1,d*d_i)*U_i
        for jj,(U_j,tot_j,d_j,_) in enumerate(kids):
            if jj!=i: term*=tot_j
        M+=term
    return U+M
# TEST: replace one child by the same-size champion -> total(hub) should NOT decrease
random.seed(2); pool=[umd(tr) for s in range(1,N+1) for tr in bysize[s]]
bad=0; tested=0
for _ in range(6000):
    k=random.randint(2,6); kids=[random.choice(pool) for _ in range(k)]
    for i in range(k):
        s=kids[i][3]; ch=champ[s]; chq=(ch[2],ch[1],ch[3],s)  # (U,tot,d,size)
        before=hub_total(kids); after=hub_total(kids[:i]+[chq]+kids[i+1:])
        tested+=1
        if after<before-Fr(1,10**12): bad+=1
print(f"\nchild->same-size-champion replacement: {tested} tests, {bad} DECREASED total(hub)")
print("=> "+("EXCHANGE HOLDS: replacing any child by its size-champion never decreases total(hub)"
       if bad==0 else f"{bad} VIOLATIONS: the exchange is NOT monotone (the 3-quantity coupling bites)"))
