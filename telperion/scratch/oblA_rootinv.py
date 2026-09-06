"""
Is Aobj root-invariant in my rooted model? And is the move monotone unrooted?
Build unrooted tree as adjacency, compute per(L)/prod(deg) by brute matching sum,
compare to rooted Aobj at each rooting.
"""
import sys
sys.path.insert(0,'/Users/peterwmurphy/repos/Arda-wt-w2a/telperion/scratch')
from oblA_probe import Aobj, pushInto
from sympy import Rational as R
from itertools import combinations

LEAF=();
def cherry(): return (LEAF,)

# ---- convert rooted UTree (nested tuple) to unrooted adjacency edge list ----
def to_edges(t):
    edges=[]; nid=[0]
    def rec(node):
        me=nid[0]; nid[0]+=1
        for c in node:
            ch=rec(c); edges.append((me,ch))
        return me
    rec(t)
    n=nid[0]
    return n, edges

def deg(n,edges):
    d=[0]*n
    for a,b in edges: d[a]+=1; d[b]+=1
    return d

def perm_L_over_prod(n, edges):
    """per(Laplacian)/prod(deg) = sum over matchings prod_{(i,j)} 1/(deg_i deg_j)  (tree identity)."""
    d=deg(n,edges)
    # sum over all matchings (incl empty) of prod over matched edges w_e, w_e=1/(d_i d_j)
    # DP over edges won't be simple; do recursion on matchings via inclusion of edges.
    E=[(a,b,R(1,d[a]*d[b])) for a,b in edges]
    # matching = subset of edges no shared vertex; weight prod w
    total=R(0)
    m=len(E)
    def rec(i, used, acc):
        nonlocal total
        if i==m:
            total+=acc; return
        # skip edge i
        rec(i+1, used, acc)
        a,b,w=E[i]
        if a not in used and b not in used:
            rec(i+1, used|{a,b}, acc*w)
    rec(0,set(),R(1))
    return total

def unrooted_val(t):
    n,edges=to_edges(t)
    return perm_L_over_prod(n,edges)

# check root-invariance: my rooted Aobj vs unrooted for a few trees
def all_rerootings(t):
    n,edges=to_edges(t)
    adj={i:[] for i in range(n)}
    for a,b in edges: adj[a].append(b); adj[b].append(a)
    def build(root,parent):
        return tuple(build(c,root) for c in adj[root] if c!=parent)
    return [build(r,-1) for r in range(n)]

print("=== root-invariance check ===")
for t in [(LEAF,LEAF),((LEAF,),(LEAF,)),((LEAF,LEAF),(LEAF,LEAF)),((LEAF,LEAF),(LEAF,LEAF),(LEAF,))]:
    u=unrooted_val(t)
    vals=set(Aobj(rt) for rt in all_rerootings(t))
    print(f"unrooted={u}  rooted-set={vals}  invariant={len(vals)==1 and list(vals)[0]==u}")
