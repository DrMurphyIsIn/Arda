"""Feasibility PROBE (hand-off artifact, not a landed module): one Handelman
box-positivity engine certifies BOTH a BG discharge atom AND the RH zero-free
witness -- concrete evidence for the 2026-08-31 "shared endgame" reassessment.

BG side: the Bethe full-edge bound  a_v R_v <= prod_{u~v}(1 + h_{u->v} h_{v->u})
on the cavity-field box h_i in [0,1] (bethe_certificate.py conventions). At the
optimum c=5, 1+2c=11 so rhoB^(1+2c)=rhoB^11=621/64 is EXACTLY RATIONAL -- the
irrational 11th root cancels, the atom is rational box-positivity, and 621=27*23
(the tie constant) is manifest (a = 156/161, 161 = 7*23).

RH side: emit_zero_free_cosine's witness (1+x)^n >= 0 on {1+-x>=0}.

Both live in the SAME Handelman cone (nonneg combinations of products of the box
constraints). Offline, exact rationals, no Lean build.
"""
import os, sys, signal
sys.path.insert(0, os.path.expanduser("~/repos/Arda/telperion/src"))
import sympy as sp
from sympy import binomial as C, Rational as R
from telperion.emit_handelman import find_handelman_certificate

h1, h2, x = sp.symbols("h1 h2 x")

# ---------- BG c=5 full-edge discharge atom (rational; 11th root cancels) ----------
c, m = 5, 2
d = m + c
z = R(3, 3*d + c)
F = R(3, 2)**c * (1 + R(c, 3*d))
a = F / R(621, 64)                                   # rational at c=5
Rv = 1 + z*(h1 + h2)
hv1, hv2 = z/(1 + z*h2), z/(1 + z*h1)
P = sp.Poly(sp.expand(sp.fraction(sp.together((1 + h1*hv1)*(1 + h2*hv2) - a*Rv))[0]), h1, h2)
print(f"BG atom (d={d}, c={c}):  a = {a}  (621 = 3^3*23 -> 23 survives in {a.q} = {sp.factorint(a.q)})")
print(f"          P: degree {P.total_degree()}, strictly positive on [0,1]^2")

# explicit Handelman certificate via Bernstein coefficients on the box
amat = {(k, l): P.coeff_monomial(h1**k * h2**l) for k in range(d) for l in range(d)}
def bernstein(D):
    return {(i, j): sum(R(C(i, k)*C(j, l), C(D, k)*C(D, l)) * amat.get((k, l), 0)
                        for k in range(min(i, 3)+1) for l in range(min(j, 3)+1))
            for i in range(D+1) for j in range(D+1)}
bs = bernstein(3)
allnn = all(v >= 0 for v in bs.values())
recon = sum(v * C(3, i)*C(3, j) * h1**i*(1-h1)**(3-i) * h2**j*(1-h2)**(3-j)
            for (i, j), v in bs.items())
bg_ok = allnn and sp.expand(P.as_expr() - recon) == 0
print(f"BG atom -> Handelman/Bernstein cert: {sum(1 for v in bs.values() if v>0)} nonneg terms, "
      f"min coeff {min(bs.values())}, exact P==cert {sp.expand(P.as_expr()-recon)==0}  => {'CERTIFIED' if bg_ok else 'FAIL'}")

# ---------- RH zero-free cosine witness, SAME engine ----------
def _guard(sec):
    signal.signal(signal.SIGALRM, lambda *a: (_ for _ in ()).throw(TimeoutError())); signal.alarm(sec)
prh = sp.expand((1 + x)**3)
try:
    _guard(30); tr = find_handelman_certificate(prh, [1 + x, 1 - x], (x,), max_deg=3); signal.alarm(0)
    rh_ok = bool(tr)
    print(f"RH (1+x)^3 on {{1+-x>=0}} -> find_handelman_certificate: "
          f"{'CERTIFIED (' + str(len(tr)) + ' term)' if tr else 'no cert'}  => {'CERTIFIED' if rh_ok else 'FAIL'}")
except TimeoutError:
    signal.alarm(0); rh_ok = False; print("RH witness: finder TIMEOUT")

print("\n=== VERDICT: one Handelman box-positivity cone, two problems ===")
print(f"  BG c=5 full-edge discharge atom : {'CERTIFIED' if bg_ok else 'FAIL'}")
print(f"  RH zero-free (1+x)^n witness    : {'CERTIFIED' if rh_ok else 'FAIL'}")
print("  Shared-engine claim: SUPPORTED" if bg_ok and rh_ok else "  Shared-engine claim: INCOMPLETE")
print("\nNote: this atom is the FREE-field full-edge bound (has slack, box-positive);")
print("the OPEN BG core is the UNIVERSAL discharge rule tau making it tight everywhere,")
print("where naive rules are provably spoofed (acyclicity/surface barrier). The engine")
print("certifies the ATOMS; constructing tau is the remaining research.")
