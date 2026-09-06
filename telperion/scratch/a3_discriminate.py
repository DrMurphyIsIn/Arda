"""What structural condition makes the LOCAL LEAF reparent (v adj u, w leaf, du>dv) positive?
Test candidate discriminators on the (True,True) leaf move WITHOUT the defect filter.
Candidates:
  C1: du - dv >= 2                     (strict degree gap, not just >)
  C2: du >= dv + 1 and dv is on the spine (dv path continues) -> hard to test simply
  C3: the move REDUCES defect (genuine straightening)  -> already known clean
  C4: du > dv AND v is not a leaf-ish piece parent ... 
We tabulate sign vs (du,dv) and vs defect-change to locate the discriminator."""
from fractions import Fraction as Fr
import networkx as nx
from a3_sweep import Aobj_G, min_defect, spr_relocations, deg

def tab(N=13):
    by_gap={}         # du-dv -> [pos,neg,zero]
    by_dudv={}        # (du,dv)->[pos,neg,zero]
    by_defect={}      # sign of (mdGp-mdT) -> [pos,neg,zero]
    for n in range(2,N+1):
        for T0 in nx.nonisomorphic_trees(n):
            T=nx.convert_node_labels_to_integers(T0)
            aT=Aobj_G(T); mdT=min_defect(T)
            for Gp,w,u,v in spr_relocations(T):
                du=deg(T,u); dv=deg(T,v)
                if not (du>dv): continue
                if not T.has_edge(u,v): continue
                if deg(T,w)!=1: continue           # leaf move
                margin=Aobj_G(Gp)-aT
                sgn = 0 if margin==0 else (1 if margin>0 else -1)
                gap=du-dv
                d1=by_gap.setdefault(gap,[0,0,0]); d1[ [1,2,0][sgn] if False else (0 if sgn>0 else (1 if sgn<0 else 2)) ]+=1
                d2=by_dudv.setdefault((du,dv),[0,0,0]); d2[(0 if sgn>0 else (1 if sgn<0 else 2))]+=1
                dd = min_defect(Gp)-mdT
                key = 'down' if dd<0 else ('same' if dd==0 else 'up')
                d3=by_defect.setdefault(key,[0,0,0]); d3[(0 if sgn>0 else (1 if sgn<0 else 2))]+=1
    print("LOCAL LEAF reparent (v adj u, du>dv), sign of Aobj-margin  [pos,neg,zero]")
    print(" by du-dv gap:")
    for k in sorted(by_gap): print(f"   gap={k}: {by_gap[k]}")
    print(" by (du,dv):")
    for k in sorted(by_dudv): print(f"   {k}: {by_dudv[k]}")
    print(" by defect change (of min_defect):")
    for k in ['down','same','up']:
        if k in by_defect: print(f"   {k}: {by_defect[k]}")

if __name__=="__main__":
    tab(13)
