"""
Uniform certificate for the symmetric-multi-star obstruction family ST(k,m) (the localized open core of hwh).

ST(k,m): centre of degree k, k hubs each with m leaves. alpha = (2m+1)/(m+1).
  Aobj(ST(k,m)) = 2*alpha^(k-1)                                  [verified k=2..5, m=1..4]
De-branching move ST_move: detach one arm from the centre, re-attach it as a pendant path via a leaf-leaf
edge (remove (centre,hub1), add (leaf of hub1, leaf of hub2)). Closed form (verified k=3..8, m=2..8):
  Aobj(ST_move) = tau2*a^(k-2) + (nu2*a^(k-2) + (k-2)*tau2*a^(k-3))/((k-1)(m+1)),
  tau2 = (20m^2-2m-1)/(4m(m+1)),  nu2 = (10m-3)/(4m).

Monotonicity Aobj(ST_move) - Aobj(ST) >= 0  reduces (alpha^(k-3)>0, (k-1)(m+1)>0) to F_num(k,m) >= 0:
  F_num(k,m) = (k-3)*(2m+1)(4m^3+2m^2-7m-1) + (2m+1)(8m^3+4m^2-11m-3),  linear in k.
Both cubics are positive for m>=2 (shift m=t+2: 4t^3+26t^2+49t+25, 8t^3+52t^2+101t+55, all coeffs >0),
and k>=3, so F_num>=0. Kernel-checked in R3Cert/R47HwhSymStarCert.lean (symstar_move_certificate).
"""
from fractions import Fraction as Fr
import sys, os
sys.path.insert(0, os.path.join("..", "..", "telperion", "scratch"))
from a3_derisk import Aobj_node

LEAF = ()
def plainhub(m): return tuple([LEAF] * m)
def ST(k, m): return tuple([plainhub(m)] * k)
def ST_move(k, m):
    hub1 = plainhub(m - 1); leaf_a = (hub1,); leaf_b = (leaf_a,)
    hub2 = tuple([leaf_b] + [LEAF] * (m - 1))
    return tuple([hub2] + [plainhub(m)] * (k - 2))
def al(m): return Fr(2 * m + 1, m + 1)
def tau2(m): return Fr(20 * m * m - 2 * m - 1, 4 * m * (m + 1))
def nu2(m): return Fr(10 * m - 3, 4 * m)
def AobjMove_cf(k, m):
    a = al(m)
    return tau2(m) * a**(k - 2) + Fr(1, (k - 1) * (m + 1)) * (nu2(m) * a**(k - 2) + (k - 2) * tau2(m) * a**(k - 3))
def Fnum(k, m):
    return (k - 3) * (2*m+1) * (4*m**3+2*m**2-7*m-1) + (2*m+1) * (8*m**3+4*m**2-11*m-3)

if __name__ == "__main__":
    bad = 0
    for k in range(2, 6):
        for m in range(1, 5):
            assert Aobj_node(ST(k, m)) == 2 * al(m)**(k - 1)
    for k in range(3, 9):
        for m in range(2, 9):
            if Aobj_node(ST_move(k, m)) != AobjMove_cf(k, m): bad += 1
            D = AobjMove_cf(k, m) - 2 * al(m)**(k - 1)
            # D >= 0 iff F_num >= 0 (positive alpha^(k-3), (k-1)(m+1))
            assert (D >= 0) == (Fnum(k, m) >= 0)
            assert D >= 0 and Fnum(k, m) >= 0
    print(f"Aobj(ST)=2*alpha^(k-1): verified. Aobj(ST_move) closed form: {bad} mismatches (k=3..8,m=2..8).")
    print("D = Aobj(ST_move)-Aobj(ST) >= 0 and F_num >= 0 for all k=3..8, m=2..8: verified.")
    print("Uniform certificate (F_num>=0 via shifted cubics) kernel-checked: R47HwhSymStarCert.symstar_move_certificate")
