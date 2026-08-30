"""Guerra G2/G3: is the Bethe functional Phi[mu] STATIONARY and CONCAVE at the caterpillar message fixed
point?  Phi[mu] = (1/n)[sum_v log(A_v/d_v) - sum_e log(1+1/(mu_uv mu_vu))], A_v = d_v + sum_{a~v} 1/mu_{a->v},
evaluated at ARBITRARY messages mu (not necessarily a BP fixed point).  At the fixed point mu*, Phi=F.

Known: Bethe free energy is STATIONARY at BP fixed points.  If additionally Phi is CONCAVE in mu at mu*
(the SSM/Heilmann-Lieb input), then mu* is a LOCAL MAX of the functional -- the message-space concavity that
a Guerra interpolation needs to turn into a global comparison F(T) <= F(caterpillar).
"""
import numpy as np, networkx as nx, random

def catG(spine,a,L=2):
    G=nx.Graph();nid=spine
    for i in range(spine-1):G.add_edge(i,i+1)
    for i in range(spine):
        for _ in range(a):
            p=i
            for _ in range(L):G.add_edge(p,nid);p=nid;nid+=1
    return G

def solve_messages(G, iters=5000, tol=1e-15):
    deg=dict(G.degree()); adj={v:list(G.neighbors(v)) for v in G.nodes()}
    dirs=[(u,v) for u in G.nodes() for v in adj[u]]
    m={e:float(deg[e[0]]) for e in dirs}
    for _ in range(iters):
        mx=0.0
        for (u,v) in dirs:
            val=deg[u]+sum(1.0/m[(c,u)] for c in adj[u] if c!=v); mx=max(mx,abs(val-m[(u,v)])); m[(u,v)]=val
        if mx<tol: break
    return m,deg,adj,dirs

def Phi(G, m, deg, adj):
    n=G.number_of_nodes()
    vsum=sum(np.log((deg[v]+sum(1.0/m[(a,v)] for a in adj[v]))/deg[v]) for v in G.nodes())
    esum=sum(np.log(1.0+1.0/(m[(u,v)]*m[(v,u)])) for u,v in G.edges())
    return (vsum-esum)/n

print("G2/G3: stationarity + concavity of Phi[mu] at the caterpillar BP fixed point")
for tag,G in [('caterpillar a=7 (spine20)',catG(20,7)),('caterpillar a=3',catG(20,3)),
              ('path40',nx.path_graph(40)),('binary d5',nx.balanced_tree(2,5))]:
    m,deg,adj,dirs=solve_messages(G); mv=np.array([m[e] for e in dirs])
    F0=Phi(G,m,deg,adj)
    # directional test: Phi(mu* + s*delta) for random delta, several s -> fit parabola a*s^2+b*s+c
    random.seed(0); np.random.seed(0)
    slopes=[]; curvs=[]; anyup=False
    for t in range(40):
        delta=np.random.randn(len(dirs)); delta/=np.linalg.norm(delta)
        vals=[]
        ss=[-1e-3,-5e-4,0,5e-4,1e-3]
        for s in ss:
            mp={e:mv[i]+s*delta[i] for i,e in enumerate(dirs)}
            vals.append(Phi(G,mp,deg,adj))
        b=(vals[3]-vals[1])/(1e-3)                    # first deriv ~ slope at 0
        c2=(vals[3]-2*vals[2]+vals[1])/(5e-4**2)      # second deriv
        slopes.append(abs(b)); curvs.append(c2)
        if max(vals)>F0+1e-11: anyup=True
    print(f"  {tag:26s}: F={F0:.6f}  max|Phi'|={max(slopes):.2e} (stationary if ~0)  "
          f"Phi'' in [{min(curvs):+.3e},{max(curvs):+.3e}]  concave={all(c<1e-6 for c in curvs)}  "
          f"any perturbation increased Phi? {anyup}")
print("\n  stationary (|Phi'|~0) + all Phi''<0 + no perturbation raises Phi  =>  mu* is a LOCAL MAX of the")
print("  Bethe functional in message space -- the concavity input a Guerra interpolation converts to global.")
