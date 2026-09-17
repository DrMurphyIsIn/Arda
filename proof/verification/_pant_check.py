"""DECISIVE: does the repo's near-star tie beat Pant's counterexample families at ALIGNED sizes?
   near-star (repo tie): hub -> K arms -> each arm 5 cherries -> each cherry 1 leaf. size=1+11K. Aobj=(26/23)(621/64)^K.
   Pant families: T(a1..am) = core path, core vertex i has a_i pendant PATHS of length 2 (core-x-y).
   Compare Aobj = per(L)/prod(deg) (unrooted) at matched sizes."""
import os, sys
from fractions import Fraction as Fr
import networkx as nx
sys.path.insert(0, os.path.join("..","..","telperion","scratch"))
from a3_derisk import unrooted_Aobj  # exact per(L)/prod(deg) on tuple trees
LEAF=()
def cherry(): return (LEAF,)
def arm5(): return tuple(cherry() for _ in range(5))
def near_star(K): return tuple(arm5() for _ in range(K))  # rooted at hub
def pant(core_pendants):
    # build as nx graph: core path c_0..c_{m-1}; core i has a_i pendant length-2 paths
    G=nx.Graph(); nid=0
    core=[]
    for i in range(len(core_pendants)):
        core.append(nid); nid+=1
    for i in range(len(core)-1): G.add_edge(core[i],core[i+1])
    if len(core)==1: G.add_node(core[0])
    for i,a in enumerate(core_pendants):
        for _ in range(a):
            x=nid; y=nid+1; nid+=2
            G.add_edge(core[i],x); G.add_edge(x,y)
    return G
def aobj_graph(G):
    # per(L)/prod deg via matching-sum on the graph
    d={v:G.degree(v) for v in G.nodes()}
    E=[(u,v) for u,v in G.edges()]
    m=len(E); tot=Fr(0)
    import sys as _s; _s.setrecursionlimit(10000)
    def rec(i,used,acc):
        nonlocal tot
        if i==m: tot+=acc; return
        rec(i+1,used,acc)
        u,v=E[i]
        if u not in used and v not in used: rec(i+1,used|{u,v},acc*Fr(1,d[u]*d[v]))
    rec(0,set(),Fr(1)); return tot
def size_pant(cp): return len(cp) + 2*sum(cp)
def nearstar_aobj(K): return Fr(26,23)*(Fr(621,64)**K)
print("Compare near-star tie vs Pant counterexample families at matched sizes:")
for cp in [(3,4,3),(3,6,3),(3,10,3),(4,4,4,4),(6,6,6,6)]:
    n=size_pant(cp)
    ap=aobj_graph(pant(cp))
    # nearest near-star size <= n (K=(n-1)//11), and its Aobj
    K=(n-1)//11
    ans=nearstar_aobj(K); ns_size=1+11*K
    print(f"  T{cp}: n={n}, Aobj={float(ap):.4g} | near-star K={K}(size{ns_size}) Aobj={float(ans):.4g} | Pant {'BEATS' if ap>ans else 'below'} near-star (same-ish size)")
