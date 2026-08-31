"""Phase 0.1d: the fixed-degree Randic reduction 'argmax F = argmax m1' is FALSE (counterexample at N=14).

Holds for all 84 degree-seq groups at N=9-12, but BREAKS at N=14: degree sequence (1^8, 2^3, 3, 4, 5) has a
tree with LOWER m1 (0.4726 vs 0.4762) but HIGHER F (0.180481 vs 0.180338) than the m1-maximizer -- different
trees. So the fixed-degree F-max is genuinely irreducible to the weighted Randic index m1; corr(F,m1)~0.99 is
a strong heuristic (exact for caterpillar-family degree sequences) but not a theorem. conjecture1_proved=False.
"""
import numpy as np, networkx as nx

def F_m1(G):
    n=G.number_of_nodes(); idx={v:i for i,v in enumerate(G.nodes())}; A=np.zeros((n,n)); deg=dict(G.degree())
    for a,b in G.edges():
        w=1/np.sqrt(deg[a]*deg[b]); A[idx[a],idx[b]]=w; A[idx[b],idx[a]]=w
    u=np.linalg.eigvalsh(A)**2
    return 0.5*np.mean(np.log1p(u)), (2.0/n)*sum(1.0/(deg[a]*deg[b]) for a,b in G.edges())

if __name__ == "__main__":
    target=(1,1,1,1,1,1,1,1,2,2,2,3,4,5)
    cands=[F_m1(T)+(T,) for T in nx.nonisomorphic_trees(14)
           if tuple(sorted(d for _,d in T.degree()))==target]
    Fmax=max(cands,key=lambda c:c[0]); m1max=max(cands,key=lambda c:c[1])
    print(f"degree seq {target}: {len(cands)} trees")
    print(f"  F-max : F={Fmax[0]:.9f} m1={Fmax[1]:.9f}")
    print(f"  m1-max: F={m1max[0]:.9f} m1={m1max[1]:.9f}")
    print(f"  different trees: {not nx.is_isomorphic(Fmax[2], m1max[2])};  "
          f"F(Fmax)-F(m1max)={Fmax[0]-m1max[0]:+.2e} > 0 => reduction FALSE")
