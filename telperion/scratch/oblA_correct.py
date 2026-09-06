"""
Find the CORRECT local monotone move (degree-equalizing) and its cleanest statement.

Candidate: the 'pull off the root, extend the spine' move -- OPPOSITE of pushInto.
  Before: node (A :: B :: rest)      (B a sibling of A at a HIGH-degree node)
  After : node (extend A with B deeper as a SPINE step)  -- but that's pushInto...

Actually the equalizing direction is: REMOVE B from a high-degree node and make it a
NEW CHILD of a LOW-degree descendant leaf (extend a path). Test several precise forms
to find one that is monotone AND size-preserving AND drops strDefect.
"""
import sys
sys.path.insert(0,'/Users/peterwmurphy/repos/Arda-wt-w2a/telperion/scratch')
from oblA_probe import Aobj
from sympy import Rational as R
LEAF=();
def cherry(): return (LEAF,)
def arm(j): return tuple(cherry() for _ in range(j))

# The move that RAISED Aobj in reconcile: take pendant off deg-3 hub, attach to extend a path end.
# Local rooted form: at node N with children [B, rest...], and one child S that is a spine going
# down to a leaf-terminal, MOVE B to become a child of that terminal (deepening the path).
# But the cleanest MONOTONE local primitive is 'sibling -> child of sibling' when it EQUALIZES.

# Test: Before = node(P :: B :: rest) ; After = node((P with B appended as grand-descendant) :: rest)
# where P is a PATH (arm) so appending B at its tip extends the path (equalizes), vs at root (concentrates).

def append_at_tip(P, B):
    # descend P via its LAST child until a leaf, attach B there -> path extension
    if P==():          # leaf: becomes node[B]
        return (B,)
    cs=list(P)
    cs[-1]=append_at_tip(cs[-1],B)
    return tuple(cs)

def test(P,B,rest,lab):
    before=tuple([P,B]+list(rest));
    after=tuple([append_at_tip(P,B)]+list(rest))
    ab=Aobj(before); af=Aobj(after)
    print(f"{'OK ' if af>=ab else 'FAIL'} d_root={len(before)}: {ab}->{af} diff={af-ab}  {lab}")

print("== append B at the TIP of a path child P (extend path) ==")
for plen in range(1,5):
    P=arm(0);
    # build a path of length plen: node[node[...node[]...]]
    P=()
    for _ in range(plen): P=(P,)
    B=(LEAF,LEAF)
    for k in range(0,5):
        test(P,B,[cherry()]*k, f"path{plen} root+{k}cherry")
