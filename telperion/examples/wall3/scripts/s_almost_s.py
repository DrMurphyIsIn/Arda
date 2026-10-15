"""Track T: independent Arb zero boxes for WALL-4 S's almost-S objects (wall4/S/s1_almost_s.py, selberg.md §3).
Callables into arb_fakes.rigorous_winding / certify_zero_box (Arda main 2dfc6eeee); S's own ARB used direct ball
evaluation at the claimed point, this uses the argument principle on a box instead.  ARB.  conjecture1_proved = False.
  ZP  = zeta(s) (1 - 2.9 2^-s + 2^(1-2s));  zeros of the factor at s = log2(alpha) + 2 pi i k / log 2.
  SH  = L(s+3/10, chi_-4) L(s-3/10, chi_-4).
  SYM = zeta(s) / [zeta(s+1-r0) zeta(s+1-r0b) zeta(s+r0-1) zeta(s+r0b-1)], r0 = 0.85 + 14.1347 i (S's r0 string).
Poles of callables are not declared: each box below is accompanied by a pole-exclusion certificate where needed."""
from _paths import cert_path, cert_read, rh, shown  # noqa: F401  (see _paths: inputs, scratch/committed certs)
import json, math
from fractions import Fraction as F
from flint import acb, arb, acb_series, ctx
from telperion.arb_fakes import certify_zero_box, rigorous_winding

out = {"conjecture1_proved": False, "trust_class": "arb",
       "provenance": "arb_fakes, Arda main 2dfc6eeee; script on unpushed branch wall3/telperion-certs"}
L2 = acb(2).log()


def ZP(s):
    one = acb_series([1])
    u = (-s * L2).exp()
    return s.zeta() * (one - arb("2.9") * u + 2 * u * u)


def Lm4(s):
    return (-s * acb(4).log()).exp() * (s.zeta(acb(arb("1/4"))) - s.zeta(acb(arb("3/4"))))


def SH(s):
    return Lm4(s + arb("0.3")) * Lm4(s - arb("0.3"))


R0 = acb(arb("0.85"), arb("14.1347"))
R0B = R0.conjugate()


def _sym(s):
    return s.zeta() / ((s + (1 - R0)).zeta() * (s + (1 - R0B)).zeta() * (s + (R0 - 1)).zeta() * (s + (R0B - 1)).zeta())


def SYM(s):
    try:
        return _sym(s)
    except ValueError:
        big = acb(arb(0, 10 ** 100), arb(0, 10 ** 100))
        return acb_series([big] * ctx.cap)


# ZP: alpha = (2.9 + sqrt(2.9^2 - 8))/2 = 1.77015..., Re s0 = log2 alpha
alpha = (2.9 + math.sqrt(2.9 ** 2 - 8)) / 2
re0 = math.log2(alpha); im0 = 2 * math.pi / math.log(2)
out["ZP_zero_box"] = certify_zero_box(ZP, re0 - 0.01, re0 + 0.01, im0 - 0.01, im0 + 0.01, expected=1, prec=128)
st = {}
w = rigorous_winding(ZP, "0.7", "3/2", "1/20", "100", prec=96, stats=st)
kmax = int(100 * math.log(2) / (2 * math.pi))
out["ZP_count"] = {"box": ["0.7", "3/2", "1/20", "100"], "winding": w, "expected_from_factor": kmax,
                   "segments": st["segments"],
                   "note": "ZP has no poles in this box (zeta's pole s=1 has Im 0); zeta has no zeros there (classical "
                           "RH verification at this height, and in any case they would add, not cancel); the factor "
                           "contributes k = 1..%d" % kmax}
print("ZP box ok; count", w, "expected", kmax)
# SH: zero of L(w, chi_-4) at 1/2 + i 6.0209489..., so SH has zero 0.8 + i gamma
g = F("6.0209489046976")
out["SH_zero_box"] = certify_zero_box(SH, F(79, 100), F(81, 100), g - F(1, 100), g + F(1, 100), expected=1, prec=128)
print("SH box ok")
# SYM: zero at r0; pole exclusion: zeta(s+1-r0) etc. nonzero near the box -> certify zeta zero-free on covering boxes
b, gg, h = F("0.85"), F("14.1347"), F(1, 100)
out["SYM_zero_box"] = certify_zero_box(SYM, b - h, b + h, gg - h, gg + h, expected=1, prec=128)
# s in box => w = s + r0 - 1 in [0.69, 0.71] x [28.2594, 28.2794]; w = s + r0b - 1 in [0.69,0.71] x [-0.01, 0.01];
# w = s + 1 - r0 in [0.99, 1.01] x [-0.01, 0.01] (pole of zeta at 1 -> the zero), w = s + 1 - r0b in [0.99,1.01] x [28.26, 28.28]
pe = {"w=s+r0-1": certify_zero_box("zeta", "0.68", "0.72", "28.25", "28.29", expected=0, prec=96)["zeros_in_box"],
      "w=s+r0b-1": certify_zero_box("zeta", "0.68", "0.72", "-0.02", "0.02", expected=0, prec=96)["zeros_in_box"],
      "w=s+1-r0b": certify_zero_box("zeta", "0.98", "1.02", "28.25", "28.29", expected=0, prec=96)["zeros_in_box"]}
out["SYM_pole_exclusion_zeta_zero_free"] = pe
print("SYM box ok; pole exclusion", pe)
json.dump(out, open(cert_path("S_almost_s.cert.json"), "w"), indent=1, default=str)

# ZP5 = zeta(s) (1 - 5*5^-s + 5*25^-s) (S's s2_arb_boxes.py): factor zeros at 5^s = alpha = (5 + sqrt5)/2 * ... ;
# 1 - 5T + 5T^2 = 0 -> T = (5 - sqrt5)/10, alpha = 1/T = (5 + sqrt5)/2 = 3.618..., Re s = log_5 alpha
L5 = acb(5).log()


def ZP5(s):
    one = acb_series([1])
    u = (-s * L5).exp()
    return s.zeta() * (one - 5 * u + 5 * u * u)


a5 = (5 + math.sqrt(5)) / 2
r5, i5 = math.log(a5) / math.log(5), 2 * math.pi / math.log(5)
out["ZP5_zero_box"] = certify_zero_box(ZP5, r5 - 0.01, r5 + 0.01, i5 - 0.01, i5 + 0.01, expected=1, prec=128)
out["ZP5_centre_float"] = [r5, i5]
print("ZP5 box ok at", r5, i5)
json.dump(out, open(cert_path("S_almost_s.cert.json"), "w"), indent=1, default=str)

# S's s3_tw_coeffs: the untwisted quotient TW0 = zeta/(zeta(s+1-r0) zeta(s+1-r0b)) has prime weights
# a(p) = 1 - 2 p^(b0-1) cos(g0 log p).  Claim: a(p) < 0 exactly for p in {23, 53}.  For p >= 102, 2 p^-0.15 < 1, so
# a(p) > 0 (elementary); for p <= 101 decide each sign in Arb.
from flint import fmpz
ctx.prec = 128
g0 = arb("14.134725141734693790457251983562")
neg, undecided = [], []
for p in range(2, 102):
    if not fmpz(p).is_prime():
        continue
    ap = 1 - 2 * (arb("-0.15") * arb(p).log()).exp() * (g0 * arb(p).log()).cos()
    if ap < 0:
        neg.append(p)
    elif not ap > 0:
        undecided.append(p)
assert 2 * 102 ** -0.15 < 1
out["S_TW0_negative_prime_weights"] = {"negative": neg, "undecided": undecided, "S_claim": [23, 53],
                                       "agrees": neg == [23, 53] and not undecided}
print("TW0 negative prime weights:", neg, "undecided:", undecided)
json.dump(out, open(cert_path("S_almost_s.cert.json"), "w"), indent=1, default=str)
