"""Corrected G-R3-vdb: is the DEGREE-EQUALIZING (Karamata-DOWN) leaf-exchange Aobj-non-decreasing?
The vdb gate showed Karamata-UP fails (submodular weight). Test the opposite direction, and
characterize the INTERIOR OPTIMUM (equalizing PAST the balanced form should decrease Aobj)."""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from fractions import Fraction as Fr
from a3_derisk import unrooted_Aobj, to_edges
from a3_wellposed import gen_trees
import networkx as nx

def degseq(G): return sorted((G.degree(i) for i in G.nodes()), reverse=True)
def majorizes(a, b):  # a majorizes b (a more spread), padded
    a=sorted(a,reverse=True); b=sorted(b,reverse=True)
    n=max(len(a),len(b)); a=a+[0]*(n-len(a)); b=b+[0]*(n-len(b))
    if sum(a)!=sum(b): return False
    sa=sb=0
    for i in range(n):
        sa+=a[i]; sb+=b[i]
        if sa<sb: return False
    return True

def leaf_exchanges(t):
    n,edges=to_edges(t); G=nx.Graph(); G.add_nodes_from(range(n)); G.add_edges_from(edges)
    leaves=[i for i in G.nodes() if G.degree(i)==1]
    for w in leaves:
        u=next(iter(G.neighbors(w)))
        for v in G.nodes():
            if v==w or v==u or G.degree(v)==0: continue
            H=G.copy(); H.remove_edge(u,w); H.add_edge(v,w)
            if H.number_of_edges()!=n-1 or not nx.is_connected(H): continue
            yield G,H

def run(maxn=12):
    equalizing=0; eq_up=0; eq_down_cases=[]
    for nn in range(4,maxn+1):
        for t in gen_trees(nn):
            aT=unrooted_Aobj(t)
            for G,H in leaf_exchanges(t):
                dg,dh=degseq(G),degseq(H)
                if dg==dh: continue
                if majorizes(dg,dh):  # before more-spread => this is degree-EQUALIZING (Karamata-down)
                    equalizing+=1
                    edges=list(H.edges())
                    aH=unrooted_Aobj_from_edges(nn,edges)
                    if aH>=aT: eq_up+=1
                    elif len(eq_down_cases)<5: eq_down_cases.append((dg,dh,str(aT),str(aH)))
    print(f"degree-EQUALIZING (Karamata-down) leaf-exchanges n<={maxn}: {equalizing}")
    print(f"  Aobj-non-decreasing: {eq_up}/{equalizing}  ({100*eq_up//max(1,equalizing)}%)")
    print(f"  sample Aobj-DECREASING equalizing moves (the interior-optimum overshoot):")
    for dg,dh,a,b in eq_down_cases: print(f"    {dg} -> {dh}: Aobj {a} -> {b}")

def unrooted_Aobj_from_edges(n, edges):
    d=[0]*n
    for a,b in edges: d[a]+=1; d[b]+=1
    E=[(a,b,Fr(1,d[a]*d[b])) for a,b in edges]; m=len(E); tot=Fr(0)
    def rec(i,used,acc):
        nonlocal tot
        if i==m: tot+=acc; return
        rec(i+1,used,acc)
        a,b,w=E[i]
        if a not in used and b not in used: rec(i+1,used|{a,b},acc*w)
    rec(0,set(),Fr(1)); return tot

if __name__=="__main__": run(11)
