"""
C1 part 3: analytic arm-count optimum + broad extremal confirmation.
The single-hub cherry rate: g(a) = log Ztot_sub / n,  Ztot_sub=(3/2)^a*(1+a/(3(a+1))), n=2a+1.
Show a=5 is the exact integer argmax and locate the continuous optimum.
Also: exhaustive-ish check that no small tree beats Ztot_sub^(1/n)=rhoB.
"""
from fractions import Fraction as Fr
import math
from a3_derisk import Ztot_sub, LEAF
from a3_wellposed import gen_trees   # enumerate trees

RHOB = (621/64)**(1/11)
CHERRY = (LEAF,)
def vsize(t): return 1 + sum(vsize(c) for c in t)

def Zhub_cherry(a): return Fr(3,2)**a * (1 + Fr(a, 3*(a+1)))
def g(a):  # per-vertex log-rate, continuous a
    Z = (1.5**a)*(1 + a/(3*(a+1)))
    return math.log(Z)/(2*a+1)

# continuous optimum
xs = [a/100 for a in range(100, 900)]
best = max(xs, key=g)
print(f"continuous argmax a*≈{best:.3f}, g={g(best):.12f}, exp={math.exp(g(best)):.12f}")
print(f"integer: g(4)={math.exp(g(4)):.12f}  g(5)={math.exp(g(5)):.12f}  g(6)={math.exp(g(6)):.12f}")
print(f"  -> integer argmax a=5 gives EXACTLY rhoB={RHOB:.12f}  (621/64 = (3/2)^5*(23/18), the near-broom)")

# The exact identity a=5: (3/2)^5*(1+5/18) = (243/32)*(23/18) = 621/64. Confirm.
print(f"  (3/2)^5*(1+5/18) = {Fr(3,2)**5*(1+Fr(5,18))} == 621/64? {Fr(3,2)**5*(1+Fr(5,18))==Fr(621,64)}")

print("\n=== BROAD extremal confirmation: over ALL trees up to n vertices, max Ztot_sub^(1/n) ===")
try:
    for N in range(2, 14):
        best_t=None; best_r=-1
        for t in gen_trees(N):
            r = float(Ztot_sub(t))**(1/N)
            if r>best_r: best_r=r; best_t=t
        flag = ' == rhoB' if abs(best_r-RHOB)<1e-9 else (' > rhoB!' if best_r>RHOB+1e-12 else '')
        print(f" n={N:2d}: max Ztot_sub^(1/n)={best_r:.12f}{flag}  argmax={best_t}")
except Exception as e:
    print("gen_trees unavailable or signature differs:", e)
