"""A1 via the EXACT per-vertex cavity free energy + surface-term discharge (NOT a density relaxation).

F(T) = (1/n) sum_v phi(v),  phi(v) = log(A_v/d_v) - (1/2) sum_{a~v} log B_{va},
  A_v = d_v + sum_{a~v} 1/mu_{a->v},  B_{va} = 1 + 1/(mu_{v->a} mu_{a->v}),  mu_{v->a} = A_v - 1/mu_{a->v}.
Messages are BOUNDED (mu in [d,2d-1]) and RDE-determined -- unlike the free worst-case S_a that made the
moment discharge loose.  Discharge:  phi(v) <= B0 + B1 d_v + [antisym telescoping]  =>  summed over a
CONNECTED tree (sum d = 2n-2):  F <= B0 + B1(2 - 2/n).  With B1<0 this gives F <= logrho* + |2B1|/n for
connected trees, and forests the correct WEAKER bound.  Here: examine phi(v) vs d_v across vertex types --
does a linear-in-degree envelope (the discharge without potential) already nearly separate, caterpillar tight?
"""
import numpy as np, networkx as nx, random, math

def messages(G, iters=4000, tol=1e-14):
    deg=dict(G.degree()); adj={v:list(G.neighbors(v)) for v in G.nodes()}
    dirs=[(u,v) for u in G.nodes() for v in adj[u]]
    m={e:float(deg[e[0]]) for e in dirs}
    for _ in range(iters):
        mx=0.0
        for (u,v) in dirs:
            val=deg[u]+sum(1.0/m[(c,u)] for c in adj[u] if c!=v); mx=max(mx,abs(val-m[(u,v)])); m[(u,v)]=val
        if mx<tol: break
    return m,deg,adj

def phi_vertex(G, m, deg, adj, v):
    A=deg[v]+sum(1.0/m[(a,v)] for a in adj[v])
    s=0.0
    for a in adj[v]:
        mva=A-1.0/m[(a,v)]                       # mu_{v->a}
        s+=math.log(1.0+1.0/(mva*m[(a,v)]))
    return math.log(A/deg[v]) - 0.5*s

def catG(spine,a,L=2):
    G=nx.Graph();nid=spine
    for i in range(spine-1):G.add_edge(i,i+1)
    for i in range(spine):
        for _ in range(a):
            p=i
            for _ in range(L):G.add_edge(p,nid);p=nid;nid+=1
    return G

LOGRHO=math.log(1.2276458)
# collect (d_v, phi(v), tree, role) for interior vertices of many trees
rows=[]
def add(G, tag, interior_only=True):
    m,deg,adj=messages(G)
    for v in G.nodes():
        rows.append((deg[v], phi_vertex(G,m,deg,adj,v), tag))

C=catG(40,7); add(C,'cat_a7')
for a in (3,5,6,8,9): add(catG(40,a),f'cat_a{a}')
add(catG(40,7,3),'cat_a7_L3'); add(nx.path_graph(120),'path')
for d,dep in [(3,7),(4,5)]: add(nx.balanced_tree(d-1,dep),f'reg{d}')
random.seed(1)
for s in range(10): add(nx.random_labeled_tree(random.randint(40,90),seed=s),f'r{s}')

# caterpillar bulk phi by role (interior)
mC,degC,adjC=messages(C)
roles={}
for v in C.nodes():
    d=degC[v]
    if d==9: roles.setdefault('hub',[]).append(phi_vertex(C,mC,degC,adjC,v))
    elif d==2: roles.setdefault('arm-mid',[]).append(phi_vertex(C,mC,degC,adjC,v))
    elif d==1: roles.setdefault('leaf',[]).append(phi_vertex(C,mC,degC,adjC,v))
print('caterpillar a=7 per-vertex phi by role:')
_drole={'hub':9,'arm-mid':2,'leaf':1}
for r,vals in roles.items(): print(f'  {r:8s} (d={_drole[r]}): phi={np.mean(vals):+.5f}')
F_C=np.mean([phi_vertex(C,mC,degC,adjC,v) for v in C.nodes()])
print(f'  caterpillar F = mean phi = {F_C:.6f}  (logrho*={LOGRHO:.6f})')

# discharge WITHOUT potential: find B0,B1 minimizing B0+2B1 s.t. phi <= B0+B1 d for ALL observed (d,phi).
# i.e. the tightest linear-in-degree UPPER envelope; check caterpillar roles on the envelope + B1 sign.
ds=np.array([r[0] for r in rows]); ph=np.array([r[1] for r in rows])
from scipy.optimize import linprog
# min B0+2B1 s.t. B0 + B1 d_i >= phi_i  for all i
res=linprog([1.0,2.0], A_ub=np.column_stack([-np.ones_like(ds),-ds.astype(float)]), b_ub=-ph, bounds=[(None,None),(None,None)], method='highs')
B0,B1=res.x
bound=B0+2*B1
print(f'\\nlinear-in-degree discharge (no potential): B0={B0:.5f} B1={B1:.5f}')
print(f'  density bound B0+2B1 = {bound:.6f}  vs logrho*={LOGRHO:.6f}  (gap {bound-LOGRHO:+.4f})')
print('  B1 sign:', 'NEGATIVE (surface term, correct)' if B1<0 else 'positive')
# which vertex types are on the envelope (tight)?
slack=B0+B1*ds-ph
tightidx=np.argsort(slack)[:8]
print('  tightest (envelope-saturating) vertices:')
for i in tightidx[:6]:
    print(f'    d={rows[i][0]} phi={rows[i][1]:+.5f} slack={slack[i]:.5f}  {rows[i][2]}')
print('\\n  => if caterpillar roles saturate the envelope + far trees have slack, the potential W only needs to')
print('     fix the residual; if the envelope is far from logrho*, the potential is doing the real work.')
