"""Track T: locate the third zero in [1/20,19/20] x [gamma0-2, gamma0+2] and decide whether it lies in P's disc
|s - s1| <= 2.  ARB. conjecture1_proved=False."""
from _paths import cert_path, cert_read, rh, shown  # noqa: F401  (see _paths: inputs, scratch/committed certs)
import json
from fractions import Fraction as F
from flint import acb, arb, ctx
from telperion.arb_fakes import fake_jet, certify_zero_box
cert = json.load(open(cert_read("P_dominance_ratios.cert.json")))
out = {}
for name in ("EP5", "DH"):
    g = F(cert["objects"][name]["s1_im_exact"])   # s1 = 3/2 + i g, the one s1 of all P scripts (p_dominance)
    ctx.prec = 128
    s = acb(arb("0.5"), arb(f"{(g + F(7,4)).numerator}/{(g + F(7,4)).denominator}"))
    for _ in range(40):
        f, d = fake_jet(name, s, prec=128); s = acb((s - f / d).real.mid(), (s - f / d).imag.mid())
    cr, ci = F(s.real.mid().str(30, radius=False)), F(s.imag.mid().str(30, radius=False))
    h = F(1, 10**12)
    box = certify_zero_box(name, cr - h, cr + h, ci - h, ci + h)
    # exact distance^2 lower bound from s1 = 3/2 + i g to the certified box (box lies above g and left of 3/2)
    assert ci - h > g and cr + h < F(3, 2)
    d2_lo = (F(3, 2) - (cr + h)) ** 2 + ((ci - h) - g) ** 2
    out[name] = {"zero_box": box["box"], "dist2_lower_to_s1": float(d2_lo), "in_disc": d2_lo <= 4}
    print(name, float(cr), float(ci), "delta =", float(ci - g), "dist^2 >=", float(d2_lo))
json.dump(out, open(cert_path("P_third_zero.cert.json"), "w"), indent=1, default=str)
