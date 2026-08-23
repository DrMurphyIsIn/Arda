from fractions import Fraction as F
import sympy as sp
mu = sp.symbols('mu')
W = sp.Rational(64,621); GAMMA = W**2*sp.Rational(5,3)**11; T=W*sp.Rational(5,3)**11

# Recompute Bernstein coeffs for each P on [lo,hi], degree d, to confirm all > 0.
def bern_coeffs(P, lo, hi, d):
    # P(mu) = sum_{i=0}^d c_i (mu-lo)^i (hi-mu)^(d-i)
    # substitute mu = lo + t*(hi-lo)? Standard: coeffs via expressing in shifted basis.
    # Solve linear: build via t = (mu-lo)/(hi-lo) mapping. Instead directly:
    Pp = sp.expand(P)
    # Represent in basis b_i = (mu-lo)^i (hi-mu)^(d-i). Use that these form a basis of deg<=d.
    x = mu - lo; y = hi - mu   # x+y = hi-lo constant
    # We can get coeffs by evaluating: c_i = binom scheme. Easiest: solve linear system at d+1 points.
    import numpy as np
    from fractions import Fraction as FF
    pts = [lo + (hi-lo)*sp.Rational(j, d+2) for j in range(1,d+2)]
    # Build matrix
    rows=[]; rhs=[]
    for p in pts:
        row=[ ((p-lo)**i * (hi-p)**(d-i)) for i in range(d+1)]
        rows.append([sp.Rational(r) for r in row]); rhs.append(Pp.subs(mu,p))
    M=sp.Matrix(rows); b=sp.Matrix(rhs)
    c=M.solve(b)
    return [sp.nsimplify(ci) for ci in c]

P_A  = T - (sp.Rational(7,6)+mu/2)**11
P_B  = T*(1+mu/3)**11 - (sp.Rational(7,6)+mu/2)**11*GAMMA
P_C2 = T*(1+mu/3)**22 - ((10+6*mu)/9)**11*GAMMA**2
P_C3 = T*(1+mu/3)**33 - (1+mu)**11*GAMMA**3

for name,P,lo,hi,d in [
    ("A", P_A, sp.Rational(0),sp.Rational(37,120),11),
    ("B", P_B, sp.Rational(37,120),sp.Rational(1,3),11),
    ("C1",P_B, sp.Rational(1,3),sp.Rational(1,2),11),
    ("C2",P_C2,sp.Rational(1,3),sp.Rational(1,2),22),
    ("C3",P_C3,sp.Rational(1,3),sp.Rational(1,2),33),
]:
    c=bern_coeffs(P,lo,hi,d)
    allpos = all(ci>0 for ci in c)
    mn=min(c); 
    print(f"{name}: deg={d} all_coeffs_pos={allpos}  min_coeff={float(mn):.4e}  c0={float(c[0]):.4e} c_last={float(c[-1]):.4e}")
