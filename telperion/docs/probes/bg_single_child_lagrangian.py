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
allc=[]
for s in range(1,N+1):
    for tr in bysize[s]:
        ell,h,d,n=props(tr); allc.append((ell,h/d,n,d))
cherry=props(((),)); ycherry=cherry[1]/cherry[2]; ec=cherry[0]
print(f"cherry: ell={ec:+.5f}, y=h/d={ycherry:.5f}   ({len(allc)} rooted branches up to size {N})")
# for a grid of mu, find argmax ell+mu*y ; report where cherry stops being the unique max
print("\nmu    argmax(ell+mu*y) over ALL branches      cherry rank/margin")
for mu in [0.15,0.10,0.06,0.050,0.045,0.040,0.038,0.036,0.030]:
    scored=sorted(((e+mu*y, (n,d)) for e,y,n,d in allc), reverse=True)
    topval,topid=scored[0]
    cval=ec+mu*ycherry
    is_cherry = abs(topval-cval)<1e-9
    # margin to best NON-cherry
    nxt=[v for v,idd in scored if abs(v-cval)>1e-12][0]
    print(f" {mu:.3f}  best={'CHERRY' if is_cherry else 'sz%d,d%d'%topid} val={topval:+.5f}  cherry margin over next={cval-nxt:+.5f}")
