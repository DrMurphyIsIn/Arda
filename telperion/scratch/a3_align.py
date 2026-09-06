"""
ALIGNMENT: does the EXACT atomic SOS move
    u = node([leaf, leaf] ++ rest)  ->  u = node([node[leaf]] ++ rest)
(the leaf-onto-leaf path-extension, v=leaf w=leaf) STRICTLY DECREASE whole-tree strDefect
(root-fixed)?  And is it the SAME move that gives ΔAobj>=0?

Key subtlety (team-lead): isPiece(leaf)=isPiece(node[])=?  and isPiece(node[leaf])=isCherry=True.
So BEFORE u has children [leaf,leaf]+rest; AFTER [stem]+rest.  npCount over these children:
   leaf: isPiece(node[])? isArm(node[])=cs.all isCherry over [] = TRUE (vacuous) => isPiece=True.
   stem=node[leaf]: isCherry=True => isPiece=True.
So converting {leaf,leaf}->{stem} keeps ALL children pieces: npCount(u children) DROPS by 1
(two piece children -> one piece child) but BOTH counts contribute 0 to npCount!  npCount only
counts NON-piece children.  So npCount(u) is UNCHANGED by the #-of-children change among pieces.
=> strDefect(u) local term (npCount-1) unchanged.  Where's the drop?  ONLY if u is a
NON-PIECE child of its parent and the move changes u's OWN defect... but u's children are all
pieces both before/after (rest may have nonpiece).  Let's just COMPUTE it exactly.
"""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from a3_derisk import Aobj_node, LEAF
from a3_wellposed import strDefect, isPiece, gen_trees

# exact atomic move at a chosen node inside a whole tree (root-fixed strDefect).
# We embed u as the WHOLE ROOT for the cleanest test, and also as a child of an outer root.
def atomic_before(rest): return tuple([LEAF, LEAF]+list(rest))
def atomic_after(rest):  return tuple([tuple([LEAF])]+list(rest))

def test_root(maxrest=6):
    print("=== u AS ROOT: before=node([leaf,leaf]+rest), after=node([stem]+rest) ===")
    from a3_derisk import isPiece as ip
    for k in range(0, maxrest+1):
        rest=[LEAF]*k
        b=atomic_before(rest); a=atomic_after(rest)
        print(f" rest={k} leaves: strDefect {strDefect(b)}->{strDefect(a)}  Aobj {Aobj_node(b)}->{Aobj_node(a)}  dAobj={Aobj_node(a)-Aobj_node(b)}")
    # rest with a nonpiece to make u itself have defect
    print(" -- rest containing a NON-piece child (a vee) --")
    vee=(LEAF,LEAF)
    for k in range(0,4):
        rest=[vee]*k
        b=atomic_before(rest); a=atomic_after(rest)
        print(f" rest={k} vees: strDefect {strDefect(b)}->{strDefect(a)}  dAobj={Aobj_node(a)-Aobj_node(b)}")

def test_embedded():
    """u is a child of an outer root; measure WHOLE-tree strDefect root-fixed."""
    print("\n=== u EMBEDDED under an outer root (whole-tree root-fixed strDefect) ===")
    from a3_derisk import isPiece as ip
    vee=(LEAF,LEAF)
    cases=[
        ("u=[leaf,leaf], outer=[u]", [LEAF,LEAF], []),
        ("u=[leaf,leaf], outer=[u,vee]", [LEAF,LEAF], [vee]),
        ("u=[leaf,leaf,vee], outer=[u]", [LEAF,LEAF,vee], []),
        ("u=[leaf,leaf,vee], outer=[u,vee]", [LEAF,LEAF,vee], [vee]),
    ]
    for lab,ucs,outer in cases:
        # u before
        u_b=tuple(ucs)
        # apply atomic to first two leaf children of u:
        # find two leaves
        leaves=[i for i,c in enumerate(ucs) if c==LEAF]
        assert len(leaves)>=2, lab
        i,j=leaves[0],leaves[1]
        newu=[c for kk,c in enumerate(ucs) if kk!=i and kk!=j]
        u_a=tuple([tuple([LEAF])]+newu)
        tb=tuple([u_b]+outer); ta=tuple([u_a]+outer)
        print(f" {lab}: strDefect {strDefect(tb)}->{strDefect(ta)}  dAobj={Aobj_node(ta)-Aobj_node(tb)}")

if __name__=="__main__":
    test_root()
    test_embedded()
