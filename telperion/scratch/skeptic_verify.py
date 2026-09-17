"""
Independent adversarial verification of:
  "Aobj(T(6,6,6,6)) > tieArgmax(52)  implies  Hnorm FALSE at n=52"

Recomputes EVERYTHING from the repo's own cavity engine (a3_derisk), building
the UTree objects exactly as the Lean definitions do:

  cherryU  := node [ node [] ]                     (R47HubState.lean:30)
  armU j   := node (replicate j cherryU)           (R47HubState.lean:33)
  backboneU [(arms,c)] := node (arms.map armU ++ replicate c cherryU)  (single hub, rest=[])
  hubState a b c := [(replicate a 5 ++ replicate b 4, c)]              (R47TieBroadened.lean:25)

  usize (node cs) = 1 + sum usize cs                (R47StepSize.lean:32)
  stateSize s     = sum hubSize                      (R47StepSize.lean:86)
  hubSize (arms,c)= 1 + (len + 2*sum) + 2*c          (R47StepSize.lean:83)

  T(6,6,6,6): 4 core vertices in a PATH; each core vertex has 6 length-2 pendant paths
  (cherries). n=52.

Everything exact Fraction.
"""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from fractions import Fraction as Fr
from a3_derisk import Aobj_node, Ztot_sub, Zopen_sub, udeg, LEAF, ZtZo_sub

# ---------- build UTree objects exactly as Lean ----------
LEAFNODE = ()                       # node []
cherryU  = (LEAFNODE,)              # node [ node [] ]
def armU(j):
    return tuple([cherryU]*j)       # node (replicate j cherryU)

def backboneU_single(arms, c):
    # arms : list of loads; single hub, rest = []
    children = tuple(armU(j) for j in arms) + tuple([cherryU]*c)
    return children                 # this is `cs` for node cs; Aobj_node takes cs

def hubState_children(a, b, c):
    arms = [5]*a + [4]*b
    return backboneU_single(arms, c)

# ---------- usize ----------
def usize(node):
    return 1 + sum(usize(ch) for ch in node)

def usize_children(cs):
    return 1 + sum(usize(ch) for ch in cs)   # node cs

# ---------- T(6,6,6,6): 4 core vertices in a path, each with 6 cherries ----------
# A "cherry" pendant path of length 2 = cherryU (node[node[]]).
# Root the backbone at the first core vertex (matching backboneU root-at-first-hub).
# core4 = deepest: node( 6 cherries )
# core3 = node( 6 cherries ++ [core4] )
# core2 = node( 6 cherries ++ [core3] )
# core1(root) = node( 6 cherries ++ [core2] )     -> Aobj_node(children of core1)
def core_chain(loads):
    # loads = [6,6,6,6] from root to tail
    if len(loads) == 1:
        return tuple([cherryU]*loads[0])            # node cs; but need node object for nesting
    inner = ("NODE", core_chain(loads[1:]))         # placeholder
    # We must return an actual node (tuple of children) usable as a child.
    raise RuntimeError

# Simpler: build actual nested node objects (tuples of children).
def core_node(loads):
    """Return the NODE object (tuple of children) for the backbone rooted at loads[0]."""
    cherries = tuple([cherryU]*loads[0])
    if len(loads) == 1:
        return cherries
    tail_node = core_node(loads[1:])   # a node = tuple of children
    return cherries + (tail_node,)     # append tail hub as one further child

T_children = core_node([6,6,6,6])      # children of the ROOT core vertex
T_node = T_children                    # for usize we need node = this tuple

print("=== SIZE CHECKS ===")
uT = usize_children(T_children)
print("usize(T(6,6,6,6)) =", uT)

# tie hub argmax at n=52 baseline: (a,b,c)=(0,5,3)
tie_children = hubState_children(0,5,3)
u_tie = usize_children(tie_children)
print("usize(tieArgmax hub (0,5,3)) =", u_tie)

# stateSize via hubSize formula for hub (arms=[5]*0+[4]*5, c=3):
arms = [5]*0+[4]*5
hubSize = 1 + (len(arms) + 2*sum(arms)) + 2*3
print("stateSize([hub(0,5,3)]) via hubSize =", hubSize)

print()
print("=== Aobj CHECKS (exact Fraction) ===")
A_T = Aobj_node(T_children)
A_tie = Aobj_node(tie_children)
print("Aobj(T(6,6,6,6)) =", A_T)
print("Aobj(tie(0,5,3)) =", A_tie)
diff = A_T - A_tie
print("diff = Aobj(T) - Aobj(tie) =", diff, " sign:", "POS" if diff>0 else ("NEG" if diff<0 else "ZERO"))

print()
print("=== baseline claimed values ===")
base_AT   = Fr(1180837892027061, 26306674688)
base_Atie = Fr(4695479375868117, 104857600000)
base_diff = Fr(8862581903961897, 82208358400000)
print("baseline Aobj(T)   match:", A_T == base_AT)
print("baseline Aobj(tie) match:", A_tie == base_Atie)
print("baseline diff      match:", diff == base_diff)
