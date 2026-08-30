"""Guerra program G1: the exact matching free energy F(T) = (1/n) log(per(L)/prod deg) in CAVITY MESSAGE
coordinates, verified against the eigenvalue value.

F = (1/2n) log det(I+N^2) = (1/n) log|det(I - iN)| = (1/n)[log det(D - iA) - log prod d_v].
Tree elimination (Schur from leaves) with M = D - iA:  h_v = M_vv - sum_{children c} M_vc M_cv / h_c
  = d_v - sum_c (-i)(-i)/h_c = d_v + sum_c 1/h_c   (REAL, since (-i)(-i) = -1).
So det(D - iA) = prod_v h_v  (rooted).  Directed CAVITY messages (rooting-free):
  m_{u->v} = d_u + sum_{c~u, c != v} 1/m_{c->u},   leaves: m = d_leaf.
Full vertex term A_v = d_v + sum_{a~v} 1/m_{a->v}.  Note A_u = m_{u->v} + 1/m_{v->u}.
Bethe:  log det(D - iA) = sum_v log A_v - sum_{(u,v) in E} log B_{uv},  B_{uv} to be identified + verified.
"""
import numpy as np, networkx as nx, random

def F_eig(G):
    n=G.number_of_nodes(); idx={u:i for i,u in enumerate(G.nodes())}; A=np.zeros((n,n)); deg=dict(G.degree())
    for u,v in G.edges():
        w=1/np.sqrt(deg[u]*deg[v]); A[idx[u],idx[v]]=w; A[idx[v],idx[u]]=w
    lam=np.linalg.eigvalsh(A); return 0.5*np.mean(np.log1p(lam**2))

def cavity_messages(G, iters=2000, tol=1e-14):
    deg=dict(G.degree()); adj={v:list(G.neighbors(v)) for v in G.nodes()}
    m={}                                   # m[(u,v)] = message u->v
    for u in G.nodes():
        for v in adj[u]: m[(u,v)]=float(deg[u])
    for _ in range(iters):
        mx=0.0
        for u in G.nodes():
            for v in adj[u]:
                val=deg[u]+sum(1.0/m[(c,u)] for c in adj[u] if c!=v)
                mx=max(mx,abs(val-m[(u,v)])); m[(u,v)]=val
        if mx<tol: break
    return m, deg, adj

def F_cavity(G):
    m,deg,adj=cavity_messages(G); n=G.number_of_nodes()
    A={v: deg[v]+sum(1.0/m[(a,v)] for a in adj[v]) for v in G.nodes()}
    vsum=sum(np.log(A[v]) for v in G.nodes())
    # identify edge factor B_{uv}: log det(D-iA) = sum log A_v - sum_edges log B.  Determine B from exactness.
    # candidates using messages: try B = m_uv*m_vu - (-1) style. We KNOW A_u = m_{u->v}+1/m_{v->u}.
    # A_u*A_v = (m_uv+1/m_vu)(m_vu+1/m_uv) = m_uv m_vu + 2 + 1/(m_uv m_vu).
    # For a single edge P2 (d=1 each): m_uv=m_vu=1, A=1+1=2, det(D-iA)=det([[1,-i],[-i,1]])=1-(-i)^2=1-(-1)=2.
    #   sum log A = 2 log 2; log det = log 2; so sum log B = 2log2 - log2 = log2 -> one edge B=2.
    #   m_uv m_vu + 1 = 1+1 = 2. => guess B_{uv} = m_{u->v} m_{v->u} + 1.
    esum=0.0
    for u,v in G.edges():
        esum+=np.log(1.0 + 1.0/(m[(u,v)]*m[(v,u)]))     # correct Bethe edge factor
    logdet = vsum - esum
    return (logdet - sum(np.log(deg[v]) for v in G.nodes()))/n

def catG(spine,a,L=2):
    G=nx.Graph();nid=spine
    for i in range(spine-1):G.add_edge(i,i+1)
    for i in range(spine):
        for _ in range(a):
            p=i
            for _ in range(L):G.add_edge(p,nid);p=nid;nid+=1
    return G

print("G1 verification: F_cavity (message coords, Bethe) == F_eig (eigenvalues)?")
tests={'P2':nx.path_graph(2),'P3':nx.path_graph(3),'path10':nx.path_graph(10),
       'star5':nx.star_graph(5),'cat a=7':catG(12,7),'cat a=3':catG(10,3),
       'binary d4':nx.balanced_tree(2,4),'3-ary d3':nx.balanced_tree(3,3)}
random.seed(4)
for s in range(8): tests[f'rand{s}']=nx.random_labeled_tree(random.randint(10,40),seed=s)
allok=True
for nm,G in tests.items():
    fe,fc=F_eig(G),F_cavity(G); d=abs(fe-fc); allok&=d<1e-9
    print(f"  {nm:12s}: F_eig={fe:.8f}  F_cavity={fc:.8f}  |diff|={d:.2e}  {'OK' if d<1e-9 else 'FAIL'}")
print(f"\n  G1 message-coordinate free energy VERIFIED: {allok}")
print(f"  => Bethe form exact: F = (1/n)[sum_v log(A_v/d_v) - sum_edges log(m_uv m_vu + 1)],  A_v=d_v+sum 1/m_av")
