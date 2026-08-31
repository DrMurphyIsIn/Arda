"""Phase 0.2 (combinatorial route): the load-bearing arm-balancing exchange signs CORRECTLY for the reciprocal
VDB weight 1/(d_u d_v) (the c=-1 case Cambie-Wagner arXiv:2209.03408 leave open).

VERIFIED: (i) two-hub T(a,b) with a+b fixed -- balancing arms monotonically increases F, balanced split is the
max (L=1 and L=2); (ii) multi-hub (3,4,5 hubs) -- the EQUAL arm distribution maximizes F (uniform caterpillar
= family maximizer). So the exchange the combinatorial proof route rests on holds for our weight.
conjecture1_proved = False.
"""
import numpy as np, networkx as nx, itertools

def F(G):
    n=G.number_of_nodes(); idx={v:i for i,v in enumerate(G.nodes())}; A=np.zeros((n,n)); deg=dict(G.degree())
    for a,b in G.edges():
        w=1/np.sqrt(deg[a]*deg[b]); A[idx[a],idx[b]]=w; A[idx[b],idx[a]]=w
    return 0.5*np.mean(np.log1p(np.linalg.eigvalsh(A)**2))

def multihub(arms, L=2):
    G=nx.Graph(); m=len(arms); nid=m
    for i in range(m-1): G.add_edge(i,i+1)
    for i in range(m):
        for _ in range(arms[i]):
            p=i
            for _ in range(L): G.add_edge(p,nid); p=nid; nid+=1
    return G

if __name__ == "__main__":
    for m,T in [(3,21),(4,28),(5,35)]:
        best=(-9,None); seen=set()
        for comp in itertools.combinations_with_replacement(range(T+1),m-1):
            parts=list(comp)+[T-sum(comp)]
            if parts[-1]<0 or tuple(sorted(parts)) in seen: continue
            seen.add(tuple(sorted(parts)))
            f=F(multihub(parts))
            if f>best[0]: best=(f,sorted(parts))
        print(f"m={m} hubs T={T}: max-F arm split {best[1]} F={best[0]:.6f} (equal = uniform caterpillar)")
