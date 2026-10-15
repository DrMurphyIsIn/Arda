"""Track T: wall4/S/T_REQUEST.md -- recheck S's four EXACT boxes with T's own callables (Hurwitz-zeta chi_-4, own
factor code), arb_fakes (Arda main 2dfc6eeee).  TW here is S's UNTWISTED quotient with S's full-precision gamma0.
ARB.  conjecture1_proved = False."""
from _paths import cert_path, cert_read, rh, shown  # noqa: F401  (see _paths: inputs, scratch/committed certs)
from pathlib import Path
SCRIPTS = Path(__file__).resolve().parent
import json, sys
from flint import acb, arb, acb_series, ctx
from telperion.arb_fakes import certify_zero_box
R0 = acb(arb("0.85"), arb("14.134725141734693790457251983562"))


def TW(s):
    try:
        return s.zeta() / ((s + (1 - R0)).zeta() * (s + (1 - R0.conjugate())).zeta())
    except ValueError:
        big = acb(arb(0, 10 ** 100), arb(0, 10 ** 100)); return acb_series([big] * ctx.cap)


L2, L5 = acb(2).log(), acb(5).log()
def ZP(s):
    u = (-s * L2).exp(); return s.zeta() * (acb_series([1]) - arb("2.9") * u + 2 * u * u)
def ZP5(s):
    u = (-s * L5).exp(); return s.zeta() * (acb_series([1]) - 5 * u + 5 * u * u)
def Lm4(s):
    return (-s * acb(4).log()).exp() * (s.zeta(acb(arb("1/4"))) - s.zeta(acb(arb("3/4"))))
def SH(s):
    return Lm4(s + arb("0.3")) * Lm4(s - arb("0.3"))


jobs = [("ZP", ZP, "0.823876", "0.823878", "9.064719", "9.064721"),
        ("ZP5", ZP5, "0.79898", "0.79902", "3.90395", "3.90398"),
        ("SH", SH, "0.79999", "0.80001", "6.02094", "6.02096"),
        ("TW", TW, "0.849999", "0.850001", "14.134724", "14.134726")]
out = {"trust_class": "arb", "conjecture1_proved": False, "rows": {}}
for name, f, a, b, c, d in jobs:
    r = certify_zero_box(f, a, b, c, d, expected=1, prec=128)
    out["rows"][name] = {"box": r["box"], "winding": r["winding"], "zeros_in_box": r["zeros_in_box"]}
    print(name, r["winding"])
# TW pole exclusion for S's box: a pole is s = rho_zeta + r0 - 1 (rho_zeta a zeta zero) or s = rho_zeta + conj(r0) - 1;
# in the box that needs a zeta zero within ~1.5e-6 of s = 1 (first case) or of 1 + 2i*gamma0 (second case).
pe1 = certify_zero_box("zeta", "0.99", "1.01", "-0.01", "0.01", expected=0, poles=[(1, 0)], prec=96)["zeros_in_box"]
pe2 = certify_zero_box("zeta", "0.99", "1.01", "28.259", "28.280", expected=0, prec=96)["zeros_in_box"]
out["TW_pole_exclusion"] = {"zeta zeros in [0.99,1.01]x[-0.01,0.01] (pole s=1 ack)": pe1,
                            "zeta zeros in [0.99,1.01]x[28.259,28.280]": pe2}
print("TW pole exclusion", out["TW_pole_exclusion"])
json.dump(out, open(cert_path("S_request_boxes.cert.json"), "w"), indent=1, default=str)
