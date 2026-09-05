"""
Symmetric base case (Case-B) derisk for BGSCLRealOblBSymBase.lean.

Uses the a3_derisk cavity engine (exact fractions, mirrors the Lean model).

kstar(k)  = node (replicate k (node []))            -- a k-star (root of degree k)
before(k) = node [kstar k, kstar k]                  -- two k-stars under a root
after(k)  = node [ node (replicate (k-1) (node [])   -- first k-star, one leaf child
                        ++ [ node [kstar k] ]) ]     --   replaced by a stem carrying the sibling k-star
                                                     -- root collapses to a SINGLE child

Claim: Aobj(before k) = Aobj(after k) = (4k+2)/(k+1) for all k >= 2 (Aobj-NEUTRAL).

Also: ASYMMETRIC increment Aobj(node[j-star,k-star]) before/after for j != k.
"""
from fractions import Fraction as Fr
from a3_derisk import Aobj_node, LEAF

def kstar(k):
    return tuple([LEAF] * k)            # node (replicate k (node []))

def before(j, k):
    return (kstar(j), kstar(k))

def after_sym(k):
    # first k-star: replace one leaf child by a stem node[kstar k]
    stem = (kstar(k),)                  # node [kstar k]
    first = tuple([LEAF] * (k - 1) + [stem])   # node (replicate (k-1) leaf ++ [stem])
    return (first,)                     # root has a SINGLE child

def after_asym(j, k):
    # relocate the k-star onto a leaf of the j-star; root collapses to single child (the j-side)
    stem = (kstar(k),)                  # node [kstar k]
    first = tuple([LEAF] * (j - 1) + [stem])
    return (first,)

print("=== SYMMETRIC BASE CASE: Aobj(before) vs Aobj(after), closed form (4k+2)/(k+1) ===")
allok = True
for k in range(2, 13):
    ab = Aobj_node(before(k, k))
    af = Aobj_node(after_sym(k))
    cf = Fr(4 * k + 2, k + 1)
    ok = (ab == af == cf)
    allok &= ok
    print(f"k={k:2d}  before={ab!s:>10}  after={af!s:>10}  (4k+2)/(k+1)={cf!s:>10}  {'OK' if ok else 'MISMATCH'}")
print("ALL SYMMETRIC OK" if allok else "SYMMETRIC FAILED")

print()
print("=== ASYMMETRIC INCREMENT: dAobj = Aobj(after) - Aobj(before), j != k ===")
for j in range(2, 9):
    for k in range(2, 9):
        if j == k:
            continue
        ab = Aobj_node(before(j, k))
        af = Aobj_node(after_asym(j, k))
        d = af - ab
        sign = '+' if d > 0 else ('-' if d < 0 else '0')
        print(f"j={j} k={k}  before={ab!s:>12}  after={af!s:>12}  d={d!s:>14}  sign={sign}")
