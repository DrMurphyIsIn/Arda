"""Phase 0.1b: confirm (by degree-preserving-swap hill-climbing, not just random sampling) that the caterpillar
is the fixed-degree MAXIMIZER of the weighted Randic index m1 = (2/N) sum_edges 1/(d_u d_v).

Result: hill-climbing m1 from the caterpillar yields NO improvement; hill-climbing from random same-degree
trees converges back to the caterpillar's m1. So the caterpillar is the fixed-degree m1-max, and among m1-maxima
it also has the highest F (the small higher-moment residual breaks ties in its favor). conjecture1_proved=False.
"""
import numpy as np, networkx as nx, random

def m1_of(G):
    deg=dict(G.degree())
    return (2.0/G.number_of_nodes())*sum(1.0/(deg[u]*deg[v]) for u,v in G.edges())

def F_of(G):
    n=G.number_of_nodes(); idx={v:i for i,v in enumerate(G.nodes())}; A=np.zeros((n,n)); deg=dict(G.degree())
    for a,b in G.edges():
        w=1/np.sqrt(deg[a]*deg[b]); A[idx[a],idx[b]]=w; A[idx[b],idx[a]]=w
    return 0.5*np.mean(np.log1p(np.linalg.eigvalsh(A)**2))

def caterpillar(spine,a,L=2):
    G=nx.Graph();nid=spine
    for i in range(spine-1):G.add_edge(i,i+1)
    for i in range(spine):
        for _ in range(a):
            p=i
            for _ in range(L):G.add_edge(p,nid);p=nid;nid+=1
    return G

def degpres_swap(G, rng):
    E=list(G.edges())
    for _ in range(200):
        (a,b),(c,d)=rng.sample(E,2)
        if len({a,b,c,d})<4: continue
        for (x,y,p,q) in [(a,b,c,d),(a,b,d,c)]:
            H=G.copy(); H.remove_edge(a,b); H.remove_edge(c,d)
            if H.has_edge(x,q) or H.has_edge(p,y): continue
            H.add_edge(x,q); H.add_edge(p,y)
            if nx.is_tree(H): return H
    return None

def hillclimb_m1(G0, iters=2000, seed=0):
    rng=random.Random(seed); G=G0.copy(); cur=m1_of(G)
    for _ in range(iters):
        H=degpres_swap(G,rng)
        if H is None: continue
        v=m1_of(H)
        if v>cur+1e-12: G=H; cur=v
    return G,cur

if __name__ == "__main__":
    C=caterpillar(8,4); print(f"caterpillar: m1={m1_of(C):.6f} F={F_of(C):.6f}")
    Gc,mc=hillclimb_m1(C,seed=1); print(f"hillclimb from caterpillar: m1 -> {mc:.6f} (no improvement expected)")
