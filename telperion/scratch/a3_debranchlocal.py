"""
DECISIVE test of SCAFFOLD's debranchLocal:
  node(node As :: B :: rest)  ->  node(node(As ++ [B]) :: rest)
triggering when isPiece(node As)=False AND isPiece(B)=False.

Question: does Aobj INCREASE (obligation satisfiable) or DECREASE (obligation UNSATISFIABLE
in this direction)?  Exhaustive over all trigger trees up to n=12-14.

Aobj via the exact engine (mirrors Lean).  Also report degree geometry:
  root degree BEFORE = 2 + |rest| ;  root degree AFTER = 1 + |rest|  (root loses a child)
  node-As degree BEFORE = |As|+1(parent) ;  AFTER = |As|+1+1 = |As|+2  (gains B)
"""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from a3_derisk import Aobj_node, LEAF, isPiece
from fractions import Fraction as Fr

def gen_trees(n):
    if n==1:
        yield (); return
    def parts(total):
        if total==0:
            yield []; return
        for first in range(1,total+1):
            for T in gen_trees(first):
                for rest in parts(total-first):
                    yield [T]+rest
    seen=set()
    for cs in parts(n-1):
        t=tuple(cs)
        if t not in seen:
            seen.add(t); yield t

def run(maxn=13):
    tested=0; up=0; down=0; tie=0
    down_examples=[]; up_examples=[]
    # geometry buckets: key on (root_deg_before vs nodeAs_deg_before) sign
    geom={}
    for n in range(3, maxn+1):
        for t in gen_trees(n):
            cs=list(t)
            # need at least: one child = node As (nonpiece), a B (nonpiece), + any rest
            for i in range(len(cs)):
                nodeAs = cs[i]
                if isPiece(nodeAs): continue          # node As must be NON-piece
                if nodeAs == (): continue             # node As has children As (node As, not a leaf)
                As = list(nodeAs)
                for j in range(len(cs)):
                    if j==i: continue
                    B = cs[j]
                    if isPiece(B): continue           # B must be NON-piece
                    rest=[cs[k] for k in range(len(cs)) if k!=i and k!=j]
                    before = tuple([nodeAs, B] + rest)
                    after  = tuple([tuple(As + [B])] + rest)
                    ab=Aobj_node(before); af=Aobj_node(after)
                    tested+=1
                    root_deg_b = 2+len(rest)      # children: nodeAs,B,rest
                    as_deg_b   = len(As)+1        # node As degree (incl parent)
                    key = ('rootHi' if root_deg_b>as_deg_b else ('eq' if root_deg_b==as_deg_b else 'asHi'))
                    g=geom.setdefault(key,[0,0,0])
                    if af>ab:
                        up+=1; g[0]+=1
                        if len(up_examples)<4: up_examples.append((before,after,af-ab))
                    elif af<ab:
                        down+=1; g[1]+=1
                        if len(down_examples)<6: down_examples.append((before,after,af-ab,root_deg_b,as_deg_b))
                    else:
                        tie+=1; g[2]+=1
    print(f"debranchLocal trigger cases n<={maxn}: tested={tested}")
    print(f"  Aobj INCREASE: {up}   DECREASE: {down}   TIE: {tie}")
    print(f"  geometry [up,down,tie] by (root_deg vs nodeAs_deg BEFORE):")
    for k in ('rootHi','eq','asHi'):
        if k in geom: print(f"    {k}: {geom[k]}")
    if down_examples:
        print("  DECREASE examples (before, after, delta, root_deg_b, as_deg_b):")
        for e in down_examples: print("   ",e)
    if up_examples:
        print("  INCREASE examples:")
        for e in up_examples: print("   ",e)

if __name__=="__main__":
    import sys
    run(int(sys.argv[1]) if len(sys.argv)>1 else 13)
