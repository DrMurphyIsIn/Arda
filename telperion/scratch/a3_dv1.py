"""Specialize the u-subtree cavity increment to dv=1 (mv=0): v is a LEAF, B extends it to a
path (the Phase-0 'extend the spine tip' witness).  Show BOTH dZopen(u)>=0 and dZtot(u)>=0
UNCONDITIONALLY (no cap), with strict Ztot increase.  This is the F2 reduced crux."""
import sympy as sp
PB, betaB, DB = sp.symbols('PB betaB DB', positive=True)  # B: Popen_B, beta_B in(0,1), degree>=1
Qru = sp.symbols('Qru', nonnegative=True)
Pru, Prv = sp.symbols('Pru Prv', positive=True)
nu = sp.symbols('nu', nonnegative=True, integer=True)
Qrv, mv = sp.Integer(0), sp.Integer(0)     # dv=1 : v has no other children

ZtotB = PB/betaB
def Ztot_from(P,Q,D): return P*(1+Q/D)
def qOfChild(P,Q,D,udeg): return (1/(1+Q/D))/udeg
def qB(): return betaB/DB

# v BEFORE: leaf.  Popen=Prv? v is a leaf => v = node[] => Popen=1, Ztot=1, but Prv models
#   possible pre-existing structure; for a true leaf Prv=1,Qrv=0,Dv_b=1.  Keep Prv general>0.
Dv_b = mv+1     # =1
Pv_b, Qv_b = Prv, Qrv
qv_b = qOfChild(Pv_b,Qv_b,Dv_b,Dv_b)
Dv_a = mv+2     # =2
Pv_a = Prv*ZtotB
Qv_a = Qrv + qB()
qv_a = qOfChild(Pv_a,Qv_a,Dv_a,Dv_a)

Du_b=nu+3
Pu_b = Pru*ZtotB*Ztot_from(Pv_b,Qv_b,Dv_b)
Qu_b = Qru + qB() + qv_b
Ztot_u_b = Ztot_from(Pu_b,Qu_b,Du_b); Zopen_u_b=Pu_b
Du_a=nu+2
Pu_a = Pru*Ztot_from(Pv_a,Qv_a,Dv_a)
Qu_a = Qru + qv_a
Ztot_u_a = Ztot_from(Pu_a,Qu_a,Du_a); Zopen_u_a=Pu_a

dZopen = sp.factor(sp.simplify(Zopen_u_a-Zopen_u_b))
dZtot  = sp.factor(sp.simplify(Ztot_u_a-Ztot_u_b))
print("dv=1 (mv=0):")
print(" dZopen(u) =", dZopen)
print(" dZtot(u)  =", dZtot)

# check positivity: substitute betaB in (0,1), DB>=1 integer, and see if numerator sign is clean
numZt, denZt = sp.fraction(sp.together(dZtot))
numZo, denZo = sp.fraction(sp.together(dZopen))
print("\n dZopen numerator (expand):", sp.expand(numZo))
print(" dZtot  numerator (expand):", sp.expand(numZt))
# Try to show numerators are >=0 for betaB in [0,1], DB>=1, nu>=0, Pos symbols>0.
# beta in (0,1) <=> DB>=1 & B has children.  substitution betaB=1/(1+t), t>=0 (t=QB/DB>=0)
t = sp.symbols('t', nonnegative=True)
subs={betaB: 1/(1+t)}
nZo=sp.factor(sp.expand(numZo.subs(subs)))
nZt=sp.factor(sp.expand(numZt.subs(subs)))
print("\n after betaB=1/(1+t), t>=0:")
print("  dZopen num:", sp.factor(sp.simplify(sp.numer(sp.together(dZopen.subs(subs))))))
print("  dZtot  num:", nZt)
