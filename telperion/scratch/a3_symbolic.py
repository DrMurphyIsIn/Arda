"""
SYMBOLIC crux for the degree-equalizing reparent, using the EXACT cavity factorization.

Model (root-invariant, so root anywhere).  Root the whole tree at a global root; u is a
node; v is a CHILD of u; B is a subtree that is a child of u BEFORE and a child of v AFTER.

Everything OUTSIDE u factors as a common positive constant (u appears once as a subtree
under its parent; by Ztot_node_deg applied at the parent, Aobj(whole) = C0 * Ztot(dtSub u)
for a shared C0>0 -- more precisely the whole-tree partition function is multilinear in the
subtree-cavity of u).  So the SIGN of Aobj(after)-Aobj(before) equals the sign of
   Ztot(dtSub u_after) * (parent-cavity dressing)  -  Ztot(dtSub u_before)*(...) .
We work at the level of u's SUBTREE cavity pair (Ztot, Zopen) since the parent edge dresses
them linearly and positively.  We track BOTH Ztot and Zopen of dtSub(u) because the parent
uses Ztot and (if matched) Zopen.  We prove the cleaner sufficient inequality:

   Zopen and Ztot of dtSub(u) BOTH do not decrease, and Ztot strictly increases.

Since any ancestor dressing is  a*Ztot + b*Zopen  with a,b >= 0 (a>0), monotonicity of BOTH
Ztot and Zopen of the u-subtree implies monotonicity of the whole-tree Aobj.  We verify this
is the right sufficient condition numerically too.

Cavity algebra for a node N of subtree-degree D (= #children + 1) with children c_i, edge
weight w_i = 1/(D * udeg(c_i)), letting q_i = Zopen(c_i)/Ztot(c_i)/udeg(c_i) (so w_i*Zopen_i
= q_i * Ztot_i / D ... careful):
   Popen(N)  = prod_i Ztot(c_i)
   Ztot(N)   = Popen(N) * (1 + (1/D) * sum_i Zopen(c_i)/Ztot(c_i)/udeg(c_i))
             = Popen(N) * (1 + Q/D),   Q := sum_i q_i,  q_i = Zopen_i/Ztot_i/udeg(c_i)
   Zopen(N)  = Popen(N).
So a node is fully summarized by (Popen, Q, D):
   Ztot = Popen*(1+Q/D),  Zopen = Popen,  and its own q-contribution to its parent (parent
   degree Dp) is  Zopen(N)/Ztot(N)/udeg(N) = 1/((1+Q/D)*udeg(N)), udeg(N)=D (as a child its
   udeg = its #children+1 = D).  [When N is realized as a subtree, D = its child count + 1.]
"""
import sympy as sp

# ---- u BEFORE: children = {v, B, rest_u}.  v BEFORE: children = {rest_v}. ----
# Summaries of the fixed blocks (all POSITIVE, independent of the move):
#   B     : Popen_B>0, Q_B>=0, degree D_B = childcount(B)+1  -> beta := Zopen_B/Ztot_B in (0,1)
#   rest_u: the OTHER children of u (besides v,B). Enters u only via Q_restu = sum of their q_i >=0
#   rest_v: children of v (besides, after, B). Enters v via Q_restv >=0
# We use the q-contribution of a child to its parent's Q:
#   qcontrib(child with (Ztot_c,Zopen_c,udeg_c)) = Zopen_c/Ztot_c/udeg_c.
# For B as a child: udeg_B = D_B, Zopen_B/Ztot_B = beta_B in (0,1). qB = beta_B/D_B.

# free positive symbols
PB, betaB, DB = sp.symbols('PB betaB DB', positive=True)   # B: Popen_B, beta_B=Zopen/Ztot in(0,1), degree
Qru = sp.symbols('Qru', nonnegative=True)   # sum of q of u's OTHER children (rest_u)
Pru = sp.symbols('Pru', positive=True)      # product of Ztot of rest_u children
Qrv = sp.symbols('Qrv', nonnegative=True)   # sum of q of v's children (rest_v)
Prv = sp.symbols('Prv', positive=True)      # product of Ztot of rest_v children
# structural child COUNTS (integers) enter via the 1/D weights and udeg of v.
# Let:
#   nu  = # children of u OTHER than v and B (so |rest_u| = nu)
#   mv  = # children of v OTHER than B        (so |rest_v| = mv)
# BEFORE: u has children {v,B}+rest_u  -> child count = nu+2, so u's subtree degree Du_b=nu+3
#         v has children rest_v         -> child count = mv,   v's subtree degree Dv_b=mv+1, udeg_v_b=mv+1
# AFTER : u has children {v}+rest_u     -> child count = nu+1, Du_a=nu+2
#         v has children {B}+rest_v     -> child count = mv+1, Dv_a=mv+2, udeg_v_a=mv+2
nu, mv = sp.symbols('nu mv', nonnegative=True, integer=True)

def qB():           return betaB/DB     # B's q-contribution to its parent
def Ztot_from(Popen,Q,D):  return Popen*(1+Q/D)
def Zopen_from(Popen,Q,D): return Popen
def qOfChild(Popen,Q,D,udeg): 
    # child summarized by (Popen,Q,D); its Zopen/Ztot = 1/(1+Q/D); its udeg = D (childcount+1)
    return (1/(1+Q/D))/udeg

# ---------- v as a subtree (child of u), BEFORE ----------
# v BEFORE: children = rest_v.  Popen_v_b = Prv, Q_v_b = Qrv, D_v_b = mv+1 (childcount mv +1)
Dv_b = mv+1
Pv_b = Prv; Qv_b = Qrv
qv_b = qOfChild(Pv_b, Qv_b, Dv_b, Dv_b)     # v's q into u  (udeg_v = Dv_b)

# ---------- v as a subtree, AFTER (B added as child) ----------
Dv_a = mv+2
Pv_a = Prv * Ztot_from(PB,0,DB)             # wait: B's Ztot; B summarized (PB, QB_internal, DB).
# B internal Q: we only know beta_B=Zopen/Ztot and DB. Ztot_B = PB? No: Ztot_B=PB*(1+QB/DB),
# Zopen_B=PB, beta_B=1/(1+QB/DB).  So Ztot_B = PB/beta_B, and B's qcontrib=beta_B/udeg_B, udeg_B=DB.
ZtotB = PB/betaB
Pv_a = Prv * ZtotB
Qv_a = Qrv + qB()                            # add B's q-contribution
qv_a = qOfChild(Pv_a, Qv_a, Dv_a, Dv_a)

# ---------- u as a subtree, BEFORE: children {v,B}+rest_u ----------
Du_b = nu+3
Pu_b = Pru * ZtotB * Ztot_from(Pv_b,Qv_b,Dv_b)
Qu_b = Qru + qB() + qv_b
Ztot_u_b = Ztot_from(Pu_b,Qu_b,Du_b)
Zopen_u_b = Pu_b

# ---------- u AFTER: children {v'}+rest_u  (v' now carries B) ----------
Du_a = nu+2
Pu_a = Pru * Ztot_from(Pv_a,Qv_a,Dv_a)
Qu_a = Qru + qv_a
Ztot_u_a = Ztot_from(Pu_a,Qu_a,Du_a)
Zopen_u_a = Pu_a

# The whole-tree Aobj increment sign is governed by (Ztot_u, Zopen_u) monotonicity.
dZtot = sp.simplify(Ztot_u_a - Ztot_u_b)
dZopen = sp.simplify(Zopen_u_a - Zopen_u_b)

print("=== dZopen(u) = Zopen_after - Zopen_before ===")
print(sp.factor(dZopen))
print()
print("=== dZtot(u) = Ztot_after - Ztot_before ===")
print(sp.factor(dZtot))

# ============================================================================
# NUMERIC CROSS-CHECK: does the (Ztot_u, Zopen_u) increment sign match the true
# whole-tree Aobj increment for the local reparent (v child of u, B child of u->v)?
# ============================================================================
import random
from fractions import Fraction as Fr
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from a3_derisk import (ZtZo_sub, Ztot_sub, Zopen_sub, qContrib, qSum, P_of, Aobj_node,
                       udeg, LEAF)

def rnd(depth, rng):
    if depth<=0 or rng.random()<0.4: return LEAF
    return tuple(rnd(depth-1,rng) for _ in range(rng.randint(1,3)))

def build_before(restu, v_children, B, extra_root):
    # global root: node([ u ] + extra_root); u = node([v, B]+restu); v=node(v_children)
    v = tuple(v_children)
    u = tuple([v, B] + list(restu))
    return tuple([u] + list(extra_root))

def build_after(restu, v_children, B, extra_root):
    v = tuple(list(v_children) + [B])
    u = tuple([v] + list(restu))
    return tuple([u] + list(extra_root))

def check(trials=3000, seed=7):
    rng=random.Random(seed)
    pos=neg=zero=0
    mismatch_subtree=0
    for _ in range(trials):
        restu=[rnd(3,rng) for _ in range(rng.randint(0,3))]
        vchildren=[rnd(3,rng) for _ in range(rng.randint(0,3))]
        B=rnd(3,rng)
        if B==LEAF and rng.random()<0.5: B=(LEAF,LEAF)
        extra=[rnd(2,rng) for _ in range(rng.randint(0,3))]
        tb=build_before(restu,vchildren,B,extra)
        ta=build_after(restu,vchildren,B,extra)
        ab=Aobj_node(tb); aa=Aobj_node(ta)
        m=aa-ab
        if m>0:pos+=1
        elif m<0:neg+=1
        else:zero+=1
        # u-subtree cavity increment
        u_b=tuple([tuple(vchildren),B]+restu)
        u_a=tuple([tuple(list(vchildren)+[B])]+restu)
        dZt = Ztot_sub(u_a)-Ztot_sub(u_b)
        dZo = Zopen_sub(u_a)-Zopen_sub(u_b)
        # sufficient condition: both >=0 and (dZt>0) => whole margin sign should be >=0
        if dZt>=0 and dZo>=0 and m<0: mismatch_subtree+=1
    print(f"whole-tree local-reparent: pos={pos} neg={neg} zero={zero}")
    print(f"  cases where (dZtot_u>=0 and dZopen_u>=0) but whole margin<0: {mismatch_subtree}")

if __name__=="__main__" and "check" in sys.argv:
    check()
