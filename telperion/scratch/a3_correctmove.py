"""Characterize the CORRECT move (strDefect-down + Aobj-up) on genuine rooted cases:
geometry of the winning SPR relocation -- is it 'regraft onto a LOWER-degree vertex'
(equalizing) and is the moved thing a PIECE?  Tabulate over genuine trees."""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from a3_wellposed import (gen_trees, strDefect, isPiece, min_defect_over_roots,
                          to_edges, rooted_from)
from a3_derisk import Aobj_node, LEAF
import networkx as nx

def relocations_with_meta(t):
    """Yield (tp, moved_subtree_size, deg_source, deg_target, moved_is_leaf) for each edge-relocation
    reparent: remove (src,w), add (tgt,w); w's subtree moves from src to tgt.  Re-root at 0."""
    n,edges=to_edges(t)
    G=nx.Graph(); G.add_nodes_from(range(n)); G.add_edges_from(edges)
    deg={i:G.degree(i) for i in range(n)}
    for (x,y) in list(edges):
        for (src,w) in [(x,y),(y,x)]:
            H=G.copy(); H.remove_edge(src,w)
            keep=nx.node_connected_component(H,src)
            movedsize=n-len(keep)
            for tgt in keep:
                if tgt==src: continue
                Gp=H.copy(); Gp.add_edge(tgt,w)
                if Gp.number_of_edges()!=n-1 or not nx.is_connected(Gp): continue
                adj={i:list(Gp.neighbors(i)) for i in range(n)}
                tp=rooted_from(adj,0,-1)
                yield tp, movedsize, deg[src], deg[tgt], (deg[w]==1)

def run(maxn=12):
    geom={}     # (deg_src vs deg_tgt) among WINNING moves
    movedpiece={'leaf':0,'nonleaf':0}
    genuine=0; covered_by_lowdeg=0; covered_by_leaf=0
    for n in range(2,maxn+1):
        for t in gen_trees(n):
            md=min_defect_over_roots(t)
            if md<=0: continue
            genuine+=1
            aT=Aobj_node(t)
            wins=[]
            for tp,sz,ds,dt,wleaf in relocations_with_meta(t):
                if min_defect_over_roots(tp)<md and Aobj_node(tp)>=aT:
                    wins.append((sz,ds,dt,wleaf))
            if not wins: continue
            # does at least one winner regraft onto a STRICTLY lower-degree vertex (ds>dt)?
            if any(ds>dt for (sz,ds,dt,wl) in wins): covered_by_lowdeg+=1
            if any(wl for (sz,ds,dt,wl) in wins): covered_by_leaf+=1
            for (sz,ds,dt,wl) in wins:
                key = 'src>tgt' if ds>dt else ('eq' if ds==dt else 'src<tgt')
                geom[key]=geom.get(key,0)+1
                movedpiece['leaf' if wl else 'nonleaf']+=1
    print(f"genuine (min-defect>0) n<={maxn}: {genuine}")
    print(f"  covered by a winner regraft onto STRICTLY-lower-degree vertex (deg_src>deg_tgt): {covered_by_lowdeg}")
    print(f"  covered by a winner moving a LEAF (pendant): {covered_by_leaf}")
    print(f"  geometry of ALL winning moves (deg_src vs deg_tgt): {geom}")
    print(f"  moved-thing among winners: {movedpiece}")

if __name__=="__main__":
    run(int(sys.argv[1]) if len(sys.argv)>1 else 12)
