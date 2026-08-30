"""Is a REAL tree's edge-type matrix E[a,b] (density of edges between type-a and type-b vertices) PSD?
If not, constraining E>>0 wrongly excludes real trees (=> the naive PSD lift is invalid)."""
import sys
from fractions import Fraction as F
import numpy as np
sys.path.insert(0,'telperion/src')
def spine(SP,arms,L):
    e=[];nid=SP
    for i in range(SP-1):e.append((i,i+1))
    for i in range(SP):
        for _ in range(arms[i]):
            p=i
            for _ in range(L):e.append((p,nid));p=nid;nid+=1
    return nid,e
# a=2 caterpillar (hub deg 4): vertex types present = hub(4,{4,4,2,2}), armmid(2,{4,1}), leaf(1,{2}), spine-end...
n,e=spine(30,[2]*30,2)
d=[0]*n; adj=[[] for _ in range(n)]
for x,y in e: d[x]+=1;d[y]+=1;adj[x].append(y);adj[y].append(x)
def vtype(v):
    return (d[v], tuple(sorted(d[k] for k in adj[v])))
types=sorted(set(vtype(v) for v in range(n)))
idx={t:i for i,t in enumerate(types)}
E=np.zeros((len(types),len(types)))
for x,y in e:
    a=idx[vtype(x)]; b=idx[vtype(y)]
    E[a,b]+=1; E[b,a]+=1   # undirected edge -> both directions
eig=np.linalg.eigvalsh(E)
print("real a=2 caterpillar edge-type matrix E:")
print(f"  {len(types)} vertex types; E eigenvalues = {np.round(eig,3)}")
print(f"  min eigenvalue = {eig.min():.3f}  => E is {'PSD' if eig.min()>-1e-9 else 'NOT PSD (indefinite)'}")
print("  => constraining E>>0 EXCLUDES this real tree; the naive edge-matrix PSD lift is INVALID.")
