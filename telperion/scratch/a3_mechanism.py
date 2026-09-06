"""Pin the EXACT ΔstrDefect mechanism. The atomic move turns u's children {leaf,leaf} into
{stem}. u itself: BEFORE = node([leaf,leaf]+rest); AFTER = node([stem]+rest).
Check u's OWN piece-status before/after and how that flips the PARENT's npCount."""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from a3_derisk import LEAF
from a3_wellposed import isPiece, isArm, isCherry, strDefect, npCount

def desc(K):
    return f"isCherry={isCherry(K)} isArm={isArm(K)} isPiece={isPiece(K)} npCount(children)={npCount(K)} strDefect={strDefect(K)}"

stem=(LEAF,)
print("leaf      :", desc(LEAF))
print("stem      :", desc(stem))
print("vee=[l,l] :", desc((LEAF,LEAF)))
print()
# u before/after with NO rest (the pure atomic)
u_b=(LEAF,LEAF); u_a=(stem,)
print("u_before=node[leaf,leaf]:", desc(u_b))
print("u_after =node[stem]     :", desc(u_a))
print("  ==> isPiece flips:", isPiece(u_b), "->", isPiece(u_a))
print()
# with rest = one leaf: u_b=node[leaf,leaf,leaf]; u_a=node[stem,leaf]
for rest,lab in [([LEAF],"1 leaf"),([ (LEAF,) ],"1 cherry"),([(LEAF,LEAF)],"1 vee")]:
    u_b=tuple([LEAF,LEAF]+rest); u_a=tuple([stem]+rest)
    print(f"rest={lab}: u_before {desc(u_b)}")
    print(f"           u_after  {desc(u_a)}")
    print(f"           isPiece {isPiece(u_b)}->{isPiece(u_a)}")
