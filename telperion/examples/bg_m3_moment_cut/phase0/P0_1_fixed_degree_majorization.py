"""Phase 0.1: at a FIXED degree sequence, does the caterpillar arrangement maximize F?
And does the moment vector relate to competitors by a majorization that predicts F (despite alternating signs)?

F(T) = 1/2 sum_{k>=1} (-1)^{k+1} m_k / k,  m_k = (1/N) Tr(N^{2k}) = mean(u^k), u = lambda^2, N=D^-1/2 A D^-1/2.
Generate random trees with a GIVEN degree multiset via random Prufer sequences (vertex v appears deg(v)-1
times), compare F and moment vectors to the caterpillar arrangement.
"""
import numpy as np, networkx as nx, random
from collections import Counter

def F_and_moments(G, K=8):
    n=G.number_of_nodes(); idx={v:i for i,v in enumerate(G.nodes())}; A=np.zeros((n,n)); deg=dict(G.degree())
    for a,b in G.edges():
        w=1/np.sqrt(deg[a]*deg[b]); A[idx[a],idx[b]]=w; A[idx[b],idx[a]]=w
    u=np.linalg.eigvalsh(A)**2
    F=0.5*np.mean(np.log1p(u))
    m=[float(np.mean(u**k)) for k in range(1,K+1)]
    return F, m

def caterpillar(spine,a,L=2):
    G=nx.Graph();nid=spine
    for i in range(spine-1):G.add_edge(i,i+1)
    for i in range(spine):
        for _ in range(a):
            p=i
            for _ in range(L):G.add_edge(p,nid);p=nid;nid+=1
    return G

def prufer_tree_from_degseq(degseq, rng):
    """Random tree with EXACT degree sequence via a random Prufer sequence.
    Vertex i must appear (degseq[i]-1) times in the Prufer sequence (length N-2)."""
    N=len(degseq)
    seq=[]
    for i,d in enumerate(degseq):
        seq += [i]*(d-1)
    assert len(seq)==N-2, (len(seq),N-2)
    rng.shuffle(seq)
    try:
        T=nx.from_prufer_sequence(seq)
    except Exception:
        return None
    return T

C=caterpillar(8,4)                      # reference caterpillar
degseq_multiset=sorted([d for _,d in C.degree()])
FC,mC=F_and_moments(C)
print(f"reference caterpillar a=4 spine8: N={C.number_of_nodes()}  F={FC:.6f}")
print(f"  degree multiset: {dict(Counter(degseq_multiset))}")
print(f"  moments m1..m8: {[round(x,4) for x in mC]}")

# generate random trees with the SAME degree sequence (same multiset, but Prufer needs a per-vertex assignment;
# any assignment realizing the multiset gives a tree with that degree multiset up to relabeling)
degseq=[d for _,d in sorted(C.degree())]   # a concrete degree sequence realizing the multiset
rng=random.Random(0)
Fs=[]; Ms=[]; ntried=0
for t in range(400):
    T=prufer_tree_from_degseq(degseq, rng)
    if T is None or not nx.is_tree(T): continue
    # verify degree multiset matches
    if sorted([d for _,d in T.degree()])!=degseq_multiset: continue
    f,m=F_and_moments(T); Fs.append(f); Ms.append(m); ntried+=1
Fs=np.array(Fs)
print(f"\n{ntried} random trees with the SAME degree multiset:")
print(f"  F range: [{Fs.min():.6f}, {Fs.max():.6f}]   caterpillar F={FC:.6f}")
print(f"  caterpillar is the MAX among same-degree trees? {FC >= Fs.max()-1e-9}  "
      f"(caterpillar rank: {int((Fs>FC+1e-9).sum())} trees above it)")
# moment structure: for trees with HIGHER F than caterpillar (if any), and LOWER, compare moment vectors
above=[Ms[i] for i in range(len(Fs)) if Fs[i]>FC+1e-9]
below=[Ms[i] for i in range(len(Fs)) if Fs[i]<FC-1e-9]
print(f"  trees strictly above caterpillar: {len(above)},  strictly below: {len(below)}")
if above:
    am=np.array(above).mean(0)
    print(f"  mean moments of ABOVE trees: {[round(x,4) for x in am]}")
    print(f"  caterpillar moments:         {[round(x,4) for x in mC]}")
# Schur/majorization signal: does F correlate with a simple moment functional? check m_1 (mean u) and spread
m1s=np.array([m[0] for m in Ms]); m2s=np.array([m[1] for m in Ms])
print(f"\n  corr(F, m1)={np.corrcoef(Fs,m1s)[0,1]:+.3f}  corr(F, m2)={np.corrcoef(Fs,m2s)[0,1]:+.3f}  "
      f"corr(F, m1-m2)={np.corrcoef(Fs,m1s-m2s)[0,1]:+.3f}")
print("  => if caterpillar is the fixed-degree F-max and F tracks a clean moment order, ingredient (I)+(IV) is live")
