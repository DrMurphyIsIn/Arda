"""Track T: Arb certificate of track P's section-D positivity ratios
    rho_k = |[z^k] (F'/F)(s1 + z)| / |[z^k] (F'/F)(sigma1 + z)|,  s1 = sigma1 + i gamma, sigma1 = 3/2, k = 1,5,10,20,30.
F is the Dirichlet-series object itself (zeta, EP5, DH; arb_fakes normalisation), NOT the completed xi.
Coefficients are the exact local Taylor coefficients from an acb_series expansion at the centre (no contour, so no
radius can cross a singularity such as DH's trivial zero at s = -1; the old float values used an FFT circle of
radius ~4 around 3/2, which encloses s = -1).  ARB.  conjecture1_proved = False.
Provenance: arb_fakes, Arda main 2dfc6eeee; script on unpushed branch wall3/telperion-certs."""
from _paths import cert_path, cert_read, rh, shown  # noqa: F401  (see _paths: inputs, scratch/committed certs)
import json
from flint import acb, arb, acb_series, ctx
from telperion.arb_fakes import fake_series
KS = (1, 5, 10, 20, 30)
CASES = (("zeta", "15.668249531278"), ("zeta", "85.699348485378"), ("EP5", "15.668249531278"),
         ("DH", "85.699348485378"))


def dlog_coeffs(name, c, K=31, prec=384):
    ctx.prec, ctx.cap = prec, K + 2
    z = acb_series([c, 1])
    f = fake_series(name, z)
    return (f.derivative() / f).coeffs()


out = {"kind": "positivity_ratio_F_logderiv_taylor", "trust_class": "arb", "conjecture1_proved": False, "rows": []}
for name, g in CASES:
    a = dlog_coeffs(name, acb(arb("3/2"), arb(g)))
    b = dlog_coeffs(name, acb(arb("3/2")))
    rows = {}
    for k in KS:
        r = abs(a[k]) / abs(b[k])
        rows[k] = r.str(8)
    mx = max(range(1, 31), key=lambda k: float((abs(a[k]) / abs(b[k])).mid()))
    out["rows"].append({"object": name, "gamma": g, "ratios": rows, "argmax_k_le_30": mx,
                        "max_k_le_30": (abs(a[mx]) / abs(b[mx])).str(8)})
    print(name, g, rows, "max k<=30 at", mx, (abs(a[mx]) / abs(b[mx])).str(6))
json.dump(out, open(cert_path("P_positivity_ratios.cert.json"), "w"), indent=1)
