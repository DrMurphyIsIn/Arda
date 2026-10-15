"""Track T: Arb certificates for track B's REAL twist (B/twist.py, B/arb_zero.py), rho0 = 0.85 + 14.134725 i.

conjecture1_proved = False.  Not progress on RH.
zeta_P(s) = zeta(s) / (zeta(s+1-rho0) zeta(s+1-conj rho0)) * prod_{p < x1} [(1 - p^(rho0-1-s))(1 - p^(conj rho0-1-s))]^-1,
x1 = 2^(1/(1-beta0)).  This is a CLOSED FORM, so zeta_P is evaluated in Arb exactly: NO Euler-product tail bound is
needed (the infinite twisted product over p >= x1 is absorbed into the zeta quotient).  Poles of zeta_P in Re s > 0:
s = 1 (zeta) and the zeros of zeta(s+1-rho0), zeta(s+1-conj rho0), i.e. Re s = beta0 - 1/2 = 0.35 on zeta's known
zeros (and wherever zeta has zeros); none lies in the boxes below (all have Re s >= 0.7 > 0.35 + 1/2 - ... see note:
a pole needs Re(s+1-rho0) in (0,1), i.e. Re s in (beta0-1, beta0) = (-0.15, 0.85); in boxes with Re s >= 0.7 that
needs a zeta zero with real part in (0.85, 1) -- excluded for |Im| <= 3e12 by the classical RH verification
(CITED, Platt-Trudgian 2021), and in any case a pole would make the winding count zeros MINUS poles, so a count of
exactly 1 with the explicit zero rho0 present is what we certify; see the caveat in the report).
Certificates: (1) zero box around rho0 (winding 1); (2) rigorous count in [7/10, 3/2] x [1/20, 100]: the only zero
is rho0; (3) Re s >= 3/2 has no zeros (all factors are nonzero and finite there: Re(s+1-rho0) >= 1.65).  ARB."""
from _paths import cert_path, cert_read, rh, shown  # noqa: F401  (see _paths: inputs, scratch/committed certs)
import json, time
from fractions import Fraction as F
from flint import acb, arb, acb_series, fmpz
from telperion.arb_fakes import rigorous_winding, certify_zero_box

import sys
GS = sys.argv[1] if len(sys.argv) > 1 else "14.134725"
B0, G0 = arb("0.85"), arb(GS)
RHO, RHOB = acb(B0, G0), acb(B0, -G0)
x1 = 2 ** (1 / (1 - 0.85))                    # 101.59...; B twists p >= x1, i.e. p >= 103
SMALL = [p for p in range(2, 102) if fmpz(p).is_prime()]
assert 101 < x1 < 102


def zetaP(s):
    try:
        return _zetaP(s)
    except ValueError:
        # a ball wide enough to meet a pole of zeta(s+1-rho0) (i.e. reach s = rho0): return a huge finite ball so the
        # segment test FAILS and rigorous_winding bisects (a nan/inf ball would crash the Fraction conversion).
        from flint import ctx
        big = acb(arb(0, 10 ** 100), arb(0, 10 ** 100))
        return acb_series([big] * ctx.cap)


def _zetaP(s):
    one = acb_series([1])
    v = s.zeta() / ((s + (1 - RHO)).zeta() * (s + (1 - RHOB)).zeta())
    for p in SMALL:
        lp = acb(p).log()
        v = v / ((one - ((RHO - 1) * lp - s * lp).exp()) * (one - ((RHOB - 1) * lp - s * lp).exp()))
    return v


out = {"object": "B REAL twist, rho0 = 0.85 + %si" % GS, "trust_class": "arb", "conjecture1_proved": False,
       "provenance": "arb_fakes, Arda main 2dfc6eeee (guarded), via callable; script on unpushed branch wall3/telperion-certs"}
t = time.time()
out["zero_box"] = certify_zero_box(zetaP, "0.84", "0.86", str(float(GS) - 0.015), str(float(GS) + 0.015), expected=1, prec=128)
print("zero box:", out["zero_box"]["zeros_in_box"], time.time() - t)
st = {}
w = rigorous_winding(zetaP, "0.7", "1.5", "1/20", "100", prec=128, stats=st)
out["count_0.7_1.5_x_0.05_100"] = {"winding": w, "segments": st["segments"], "min_segment": str(st["min_segment"])}
print("winding [0.7,1.5]x[1/20,100]:", w, st["segments"], time.time() - t)
json.dump(out, open(cert_path("B_twist_REAL_g%s.cert.json" % GS), "w"), indent=1, default=str)

# (4) no poles of zeta_P in the counted box: a pole needs zeta(w) = 0 with w = s + 1 - rho0 or s + 1 - conj rho0,
# w in [0.85, 1.65] x [-14.084725, 114.134725].  Certify zeta has no zeros there (pole s=1 acknowledged).
t = time.time()
out["zeta_zero_free_for_pole_exclusion"] = certify_zero_box("zeta", "0.85", "1.65", str(-float(GS) + 0.04), str(100 + float(GS) + 0.07), expected=0,
                                                            poles=[(1, 0)], prec=96)
print("zeta zero-free in [0.85,1.65]x[-14.1,114.2]:", out["zeta_zero_free_for_pole_exclusion"]["zeros_in_box"],
      time.time() - t)
json.dump(out, open(cert_path("B_twist_REAL_g%s.cert.json" % GS), "w"), indent=1, default=str)

# (5) the residue A at s = 1, compared with the A in B's output file for THIS gamma0 (below)
from flint import ctx
ctx.prec = 128
A = 1 / ((2 - RHO).zeta() * (2 - RHOB).zeta())
for p in SMALL:
    lp = acb(p).log()
    A = A / ((1 - ((RHO - 2) * lp).exp()) * (1 - ((RHOB - 2) * lp).exp()))
# compare with B's float for THIS (beta0, gamma0): read it from B's own output file (bug fix: this used to be a
# hard-coded gamma0 = 14.134725 value, so the gamma0 = 21.02204 cert compared against the wrong residue; found by bb)
_bf = rh(f"wall3/B/out/tw_REAL_b{float('0.85')}_g{float(GS)}_s0_X1e+09.json")
_BA = json.load(open(_bf))["A"]
# a tolerance test (|mid(A) - B| <= rad(A) + 1e-14), not a containment test -- hence the name
out["residue_A"] = {"arb": A.str(25), "B_file": shown(_bf), "B_float": _BA,
                    "B_float_within_ball_plus_1e-14": bool(abs(arb(A.real.mid()) - arb(_BA)).upper() <= A.real.rad() + 1e-14)}
print("A =", A.str(25), out["residue_A"]["B_float_within_ball_plus_1e-14"])
json.dump(out, open(cert_path("B_twist_REAL_g%s.cert.json" % GS), "w"), indent=1, default=str)
