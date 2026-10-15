"""Track T: Arb certificate of track P's dominance ratios (WALL-3 P, turan_powersums.py section C).

conjecture1_proved = False.  Not progress on RH.
Claim checked: for nu in {2,5,10,20,30,41},  R_nu = |(s1-rho0)^-nu| / |sum_{rho != rho0} (s1-rho)^-nu|,
s1 = 3/2 + i gamma0, where rho runs over ALL zeros of the completed xi (multiplicity), not a truncated list.
Rigorous route (no zero list, no tail): xi is entire of order 1, so for nu >= 2
    G_nu(s1) = sum_rho (s1-rho)^-nu = (-1)^(nu-1) nu [z^nu] log xi(s1+z)   (Hadamard; absolutely convergent)
computed as an Arb power series of xi'/xi at s1; rho0 is enclosed in a certified tiny zero box (arb_fakes,
guarded; Arda main 2dfc6eeee); others = G_nu - (s1-rho0)^-nu as a ball.  Trust: ARB.
"""
from _paths import cert_path, cert_read, rh, shown  # noqa: F401  (see _paths: inputs, scratch/committed certs)
import json, sys
from fractions import Fraction as F
from flint import acb, acb_series, arb, ctx
from telperion.arb_fakes import _xi_at, certify_zero_box, fake_jet

NUS = (2, 5, 10, 20, 30, 41)
PREC = 320
OBJ = {"EP5": ("0.932969697485", "15.668249531278"), "DH": ("0.808517", "85.699348")}


def refine(name, re, im):
    ctx.prec = PREC
    s = acb(arb(re), arb(im))
    for _ in range(60):
        f, d = fake_jet(name, acb(s.real.mid(), s.imag.mid()), prec=PREC)
        s = acb(s.real.mid(), s.imag.mid()) - f / d
        s = acb(s.real.mid(), s.imag.mid())
    return s


def frac_of(x):
    return F(x.mid().str(60, radius=False))


out = {"kind": "turan_dominance_ratio", "trust_class": "arb", "conjecture1_proved": False,
       "provenance": "arb_fakes, Arda main 2dfc6eeee (= 72470dd5f, guarded); script on unpushed branch wall3/telperion-certs; script " + __file__,
       "objects": {}}
for name, (re0, im0) in OBJ.items():
    r = refine(name, re0, im0)
    cr, ci = frac_of(r.real), frac_of(r.imag)
    h = F(1, 10 ** 40)
    box = certify_zero_box(name, cr - h, cr + h, ci - h, ci + h, expected=1, prec=PREC)
    ctx.prec = PREC
    rho0 = acb(arb(f"{cr.numerator}/{cr.denominator}", float(h)), arb(f"{ci.numerator}/{ci.denominator}", float(h)))
    gam = ci  # s1 = 3/2 + i * (certified centre's imaginary part, exact rational)
    s1 = acb(arb("3/2"), arb(f"{gam.numerator}/{gam.denominator}"))
    ctx.cap = max(NUS) + 2
    z = acb_series([0, 1])
    xi = _xi_at(name, z + s1)
    ld = xi.derivative() * xi.inv()        # xi'/xi(s1+z) = sum_m (-1)^m G_{m+1} z^m
    co = ld.coeffs()
    rows = []
    for nu in NUS:
        G = co[nu - 1] * (-1) ** (nu - 1)
        term = (s1 - rho0) ** (-nu)
        other = G - term
        lo_term = abs(term).lower()
        hi_other = abs(other).upper()
        ratio_lo = lo_term / hi_other
        rows.append({"nu": nu, "G_nu": G.str(12), "abs_term_lower": abs(term).lower().str(12),
                     "abs_others_upper": hi_other.str(12), "ratio_lower": ratio_lo.str(6),
                     "ratio_upper": (abs(term).upper() / abs(other).lower()).str(6) if abs(other).lower() > 0 else "inf"})
        print(name, nu, "ratio in [", ratio_lo.str(6), ",", rows[-1]["ratio_upper"], "]")
    out["objects"][name] = {"rho0_box": box["box"], "rho0_box_winding": box["winding"], "s1": f"3/2 + i*{float(gam)!r}", "s1_im_exact": f"{gam.numerator}/{gam.denominator}",
                            "rows": rows}
    ctx.cap = 10
json.dump(out, open(cert_path("P_dominance_ratios.cert.json"), "w"), indent=1)
