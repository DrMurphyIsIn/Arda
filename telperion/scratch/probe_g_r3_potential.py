"""
GATE G-R3-potential : monotone Aobj potential under straightening.

Aobj_node / unrooted_Aobj are ROOT-INVARIANT (per(L)/prod-deg).
strDefect is a ROOTED scaffold measure.  The Lean StraightStep acts at the root,
so we use ROOT-FIXED strDefect (root = node 0) as the exact scaffold measure that
the straightening descent reduces.

We test the candidate potential
    Phi(t) = Aobj(max_n) - Aobj(t)     (>=0, ==0 exactly at the Aobj-maximizer)
where Aobj(max_n) = max over all trees of size n of unrooted Aobj.

CLAIMS TESTED, over all trees n<=CAP with strDefect(t) > 0 :
  (Q1) EXISTS a strDefect-reducing SPR move that ALSO strictly reduces Phi
       (i.e. strictly increases Aobj).                     [local well-posedness]
  (Q2) Is Phi monotone along the WHOLE straightening descent, i.e. is EVERY
       strDefect-reducing SPR move also Aobj-non-decreasing? (no back-slides)
  (Q3) Coupling: does strDefect==0  <=> Aobj is maximal (Phi==0) ?
"""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from a3_derisk import Aobj_node, unrooted_Aobj, LEAF
from a3_wellposed import strDefect, gen_trees, all_spr_rooted
from fractions import Fraction as Fr

CAP = int(sys.argv[1]) if len(sys.argv) > 1 else 13

def max_aobj(n, _cache={}):
    if n in _cache: return _cache[n]
    best = None; bestt = None
    for t in gen_trees(n):
        a = Aobj_node(t)
        if best is None or a > best:
            best = a; bestt = t
    _cache[n] = (best, bestt)
    return _cache[n]

def main():
    print(f"=== G-R3-potential probe, exhaustive cap n<={CAP} ===")
    total_genuine = 0
    q1_have_local = 0          # exists strDefect-down & Aobj-up move
    q1_fail = []               # genuine trees with NO strDefect-down-and-Aobj-up move
    q2_monotone_ok = 0         # every strDefect-down move is Aobj-non-decreasing
    q2_backslide = []          # trees admitting a strDefect-down move that LOWERS Aobj
    q3_zero_defect_notmax = [] # strDefect==0 but Aobj < max_n
    q3_max_haspositivedef = [] # Aobj==max_n but strDefect>0

    for n in range(2, CAP + 1):
        amax, _ = max_aobj(n)
        for t in gen_trees(n):
            aT = Aobj_node(t)
            dT = strDefect(t)   # ROOT-FIXED at node 0
            # Q3 coupling checks (all trees, incl. dT==0)
            if dT == 0 and aT < amax:
                q3_zero_defect_notmax.append((n, t, aT, amax))
            if aT == amax and dT > 0:
                q3_max_haspositivedef.append((n, t, dT))
            if dT == 0:
                continue
            total_genuine += 1
            # enumerate SPR moves; strDefect measured root-fixed on the SAME re-rooting
            # convention all_spr_rooted uses (re-root at node 0).
            down_moves = []
            for tp in all_spr_rooted(t):
                if strDefect(tp) < dT:
                    down_moves.append(tp)
            # Q1: exists a strDefect-down move that strictly raises Aobj
            if any(Aobj_node(tp) > aT for tp in down_moves):
                q1_have_local += 1
            else:
                q1_fail.append((n, t, dT, aT))
            # Q2: is EVERY strDefect-down move Aobj-non-decreasing?
            bad = [tp for tp in down_moves if Aobj_node(tp) < aT]
            if not bad:
                q2_monotone_ok += 1
            else:
                q2_backslide.append((n, t, dT, aT, len(bad), len(down_moves)))

    print(f"\ngenuine trees (root-fixed strDefect>0): {total_genuine}")
    print(f"[Q1] exists strDefect-DOWN & Aobj-UP move : {q1_have_local}"
          f"   fails: {len(q1_fail)}")
    for x in q1_fail[:10]:
        print("    Q1-FAIL:", x)
    print(f"[Q2] EVERY strDefect-DOWN move is Aobj-non-decreasing (no back-slide): "
          f"{q2_monotone_ok}   back-slide trees: {len(q2_backslide)}")
    for x in q2_backslide[:10]:
        print("    Q2-BACKSLIDE (n,t,defect,aobj,#bad,#down):", x)
    print(f"[Q3] strDefect==0 but Aobj<max : {len(q3_zero_defect_notmax)}")
    for x in q3_zero_defect_notmax[:6]:
        print("    Q3a:", x)
    print(f"[Q3] Aobj==max but strDefect>0 : {len(q3_max_haspositivedef)}")
    for x in q3_max_haspositivedef[:6]:
        print("    Q3b:", x)

    # Report the argmax shape per n (is it a caterpillar/spider?)
    print("\nargmax-Aobj shape per n and its root-fixed strDefect:")
    for n in range(2, CAP + 1):
        amax, tbest = max_aobj(n)
        print(f"  n={n:2d}  strDefect(argmax)={strDefect(tbest)}  argmax={tbest}")

if __name__ == "__main__":
    main()
