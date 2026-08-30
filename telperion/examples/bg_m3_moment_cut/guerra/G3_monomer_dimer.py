"""G3 substrate: verify  per(L)/prod deg = Z_MD := sum over matchings M of prod_{e in M} 1/(d_u d_v),
the monomer-dimer partition function with edge weight w_e = 1/(d_u d_v).  Then F = (1/n) log Z_MD.

This reframes the tree free energy as an EXACT monomer-dimer log-partition-function -- the setting where
Heilmann-Lieb (real roots, no phase transition) and Guerra-Toninelli correlation inequalities live.
"""
import numpy as np, networkx as nx, random
from itertools import combinations

def F_eig(G):
    n=G.number_of_nodes(); idx={u:i for i,u in enumerate(G.nodes())}; A=np.zeros((n,n)); deg=dict(G.degree())
    for u,v in G.edges():
        w=1/np.sqrt(deg[u]*deg[v]); A[idx[u],idx[v]]=w; A[idx[v],idx[u]]=w
    lam=np.linalg.eigvalsh(A); return 0.5*np.mean(np.log1p(lam**2))

def Z_MD(G):
    """Exact monomer-dimer partition function sum_matchings prod 1/(d_u d_v) via edge-DP (tree recursion)."""
    deg=dict(G.degree()); w={frozenset(e): 1.0/(deg[e[0]]*deg[e[1]]) for e in G.edges()}
    # root the tree; DP: for each vertex, (f0 = matchings in subtree with v UNmatched-to-parent-side,
    #                                       f1 = ... with v matched to a child)  -- track total weight.
    root=next(iter(G.nodes())); parent={root:None}; order=[]
    stack=[root]; seen={root}
    while stack:
        u=stack.pop(); order.append(u)
        for c in G.neighbors(u):
            if c not in seen: seen.add(c); parent[c]=u; stack.append(c)
    # process leaves->root. dp[v] = (A, B): A=weight with v free (not matched to a child), B=with v matched down
    dp={}
    for v in reversed(order):
        children=[c for c in G.neighbors(v) if parent.get(c)==v]
        # v free: each child independently free-or-matched-down: prod (A_c + B_c)
        A=1.0
        for c in children: A*= (dp[c][0]+dp[c][1])
        # v matched to exactly one child c0 (edge v-c0 in matching, c0 must be free): sum_c0 w*A_c0 * prod_{other} (A+B)
        B=0.0
        for c0 in children:
            term=w[frozenset((v,c0))]*dp[c0][0]
            for c in children:
                if c is not c0: term*=(dp[c][0]+dp[c][1])
            B+=term
        dp[v]=(A,B)
    return dp[root][0]+dp[root][1]     # root free or matched down

def brute_Z(G):
    """Brute force over all matchings (small graphs) as a cross-check."""
    deg=dict(G.degree()); edges=list(G.edges()); w=[1.0/(deg[u]*deg[v]) for u,v in edges]
    tot=0.0
    for k in range(0, len(edges)+1):
        for combo in combinations(range(len(edges)),k):
            verts=[]; ok=True
            for idx in combo:
                u,v=edges[idx]
                if u in verts or v in verts: ok=False; break
                verts+= [u,v]
            if ok:
                p=1.0
                for idx in combo: p*=w[idx]
                tot+=p
    return tot

def catG(spine,a,L=2):
    G=nx.Graph();nid=spine
    for i in range(spine-1):G.add_edge(i,i+1)
    for i in range(spine):
        for _ in range(a):
            p=i
            for _ in range(L):G.add_edge(p,nid);p=nid;nid+=1
    return G

print("G3 substrate: F_eig  vs  (1/n) log Z_MD  [monomer-dimer, w_e=1/(d_u d_v)]")
tests={'P2':nx.path_graph(2),'P3':nx.path_graph(3),'P5':nx.path_graph(5),'star5':nx.star_graph(5),
       'cat a=3':catG(6,3),'cat a=7':catG(6,7),'binary d3':nx.balanced_tree(2,3)}
random.seed(2)
for s in range(6): tests[f'rand{s}']=nx.random_labeled_tree(random.randint(8,18),seed=s)
allok=True
for nm,G in tests.items():
    n=G.number_of_nodes(); fe=F_eig(G); z=Z_MD(G); fmd=np.log(z)/n; d=abs(fe-fmd); allok&=d<1e-9
    bz=brute_Z(G) if G.number_of_edges()<=16 else None
    bchk="" if bz is None else f" bruteZ diff={abs(bz-z):.1e}"
    print(f"  {nm:10s}: F_eig={fe:.8f}  (1/n)logZ_MD={fmd:.8f}  |diff|={d:.1e}  {'OK' if d<1e-9 else 'FAIL'}{bchk}")
print(f"\n  MONOMER-DIMER IDENTITY VERIFIED: {allok}")
print(f"  => F(T) = (1/n) log sum_{{matchings}} prod_{{e}} 1/(d_u d_v).  Heilmann-Lieb / Guerra-Toninelli setting.")
