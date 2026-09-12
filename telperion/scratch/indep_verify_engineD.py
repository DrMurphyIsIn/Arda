"""
INDEPENDENT verification (Engine D - Balanced+Capped envelope).
Builds trees from the Lean grammar (R47HubState.lean / R47StepSize.lean) directly,
scores with the repo's own cavity engine (a3_derisk.Aobj_node), uses ONLY Fractions.
"""
from fractions import Fraction as Fr
import itertools
from a3_derisk import Aobj_node

LEAF = ()  # UTree.node []

# --- Lean grammar (R47HubState.lean) ---
# cherryU = node [node []]  == (LEAF,)
# armU j  = node (replicate j cherryU)
# backboneU [] = node []
# backboneU ((arms,c)::rest) = node ( map armU arms ++ replicate c cherryU ++ (tail))
CHERRY = (LEAF,)

def armU(j):
    return tuple([CHERRY] * j)

def backboneU(hubs):
    if not hubs:
        return LEAF
    arms, c = hubs[0]
    rest = hubs[1:]
    children = [armU(j) for j in arms] + [CHERRY] * c
    if rest:
        children.append(backboneU(rest))
    return tuple(children)

# --- usize (R47StepSize.lean): usize(node cs)=1+sum usize(child); leaf=1 ---
def usize(t):
    return 1 + sum(usize(c) for c in t)

# --- hubSize / stateSize (R47StepSize.lean:83-86) ---
# hubSize(arms,c) = 1 + (len(arms) + 2*sum(arms)) + 2*c
def hubSize(h):
    arms, c = h
    return 1 + (len(arms) + 2 * sum(arms)) + 2 * c

def stateSize(s):
    return sum(hubSize(h) for h in s)

# --- Balanced (R47Step.lean:41-45) / Capped (R47Capped.lean:39) ---
def balanced(s):
    return all(all(j in (4, 5) for j in arms) and c <= 5 for (arms, c) in s)

def capped(s):
    return all(len(arms) >= 5 for (arms, c) in s)

# ============================================================
# (A) T(6,6,6,6): 4 core hubs in a path, each 0 arms + 6 cherries
T = [([], 6), ([], 6), ([], 6), ([], 6)]
T_tree = backboneU(T)
usize_T = usize(T_tree)
statesize_T = stateSize(T)  # via hubSize (independent of realization)
aobj_T = Aobj_node(T_tree)
print("T(6,6,6,6): usize(tree) =", usize_T, " stateSize(hubSize) =", statesize_T)
print("  Balanced?", balanced(T), " Capped?", capped(T))
print("  Aobj(T) =", aobj_T)

# ============================================================
# (B) Single-hub Balanced+Capped states of size 52.
# hub(a,b,c): a load-5 arms, b load-4 arms, c cherries.
# stateSize = 1 + ((a+b) + 2*(5a+4b)) + 2c = 1 + (a+b) + 10a+8b + 2c = 1 + 11a + 9b + 2c
# size 52 => 11a+9b+2c = 51.  Balanced: arms in {4,5} (ok), c<=5.  Capped: a+b>=5.
best = None
argmax = None
sols = []
for a in range(0, 6):
    for b in range(0, 7):
        rem = 51 - 11 * a - 9 * b
        if rem < 0 or rem % 2 != 0:
            continue
        c = rem // 2
        if c > 5:
            continue
        if a + b < 5:
            continue
        arms = [5] * a + [4] * b
        s = [(arms, c)]
        assert balanced(s) and capped(s)
        assert stateSize(s) == 52, (a, b, c, stateSize(s))
        val = Aobj_node(backboneU(s))
        sols.append((a, b, c, val))
        if best is None or val > best:
            best = val
            argmax = (a, b, c)
print("\nSingle-hub Balanced+Capped size-52 states:", len(sols))
for a, b, c, val in sorted(sols, key=lambda x: x[3], reverse=True):
    tag = " <== ARGMAX" if (a, b, c) == argmax else ""
    print(f"  (a={a},b={b},c={c}) Aobj={val}{tag}")
tie = best
print("tieArgmax(52) =", tie, " at (a,b,c)=", argmax)
# confirm tie hub size
th = [[5]*argmax[0]+[4]*argmax[1], argmax[2]]
tie_hub = [(tuple([5]*argmax[0]+[4]*argmax[1]), argmax[2])]
print("tie hub stateSize =", stateSize(tie_hub), " usize(backboneU) =", usize(backboneU(tie_hub)))

# ============================================================
# (C) Multi-hub Balanced+Capped of size 52? Each hub stateSize>=46 => two hubs>=92>52.
min_hub = min(hubSize((tuple([5]*a+[4]*b), c))
              for a in range(0,6) for b in range(0,7) for c in range(0,6)
              if a+b>=5)
print("\nMin Balanced+Capped single-hub stateSize =", min_hub, "(matches Lean 46)")
print("Two Balanced+Capped hubs => stateSize >=", 2*min_hub, "> 52  => NO multi-hub at 52")

# ============================================================
# (D) Sign of Aobj(T) - tie
diff = aobj_T - tie
print("\ndiff = Aobj(T) - tie =", diff)
print("SIGN:", "T>tie" if diff > 0 else ("T<tie" if diff < 0 else "T=tie"))

# Baseline cross-check
BASE_AOBJ_T = Fr(1180837892027061, 26306674688)
BASE_TIE = Fr(4695479375868117, 104857600000)
BASE_DIFF = Fr(8862581903961897, 82208358400000)
print("\n--- baseline cross-check ---")
print("aobj_T matches baseline:", aobj_T == BASE_AOBJ_T)
print("tie matches baseline:   ", tie == BASE_TIE)
print("diff matches baseline:  ", diff == BASE_DIFF)
print("baseline argmax (0,5,3):", argmax == (0,5,3))
