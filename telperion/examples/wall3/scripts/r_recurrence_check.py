"""Track T: independent check of track R's new EP5 recurrence events (R/r_arb.py: Rouche on |s - rho0 - i tau| = 0.04,
rho0 = 0.937666906700 + 29.983395235156i, tau ~ 652.065, 666.390, 932.725).
Method independent of F1/R's arc-ball Rouche code: Newton from rho0 + i tau, then arb_fakes.certify_zero_box on a
1e-10 box, then exact check that the box lies inside the open disc |s - rho0 - i tau0| < 0.04 for every tau0 in R's
rational window (we take the float tau R reports to 1e-4 and allow +/- 1e-4).  ARB.  conjecture1_proved = False."""
import json
from fractions import Fraction as F
from flint import acb, arb, ctx
from telperion.arb_fakes import fake_jet, certify_zero_box
RHO = (F("0.937666906700"), F("29.983395235156"))
out = []
for t0 in (652.065, 666.390, 932.725):
    ctx.prec = 128
    s = acb(arb(str(RHO[0])), arb(str(RHO[1] + F(str(t0)))))
    for _ in range(50):
        f, d = fake_jet("EP5", s, prec=128); s = s - f / d; s = acb(s.real.mid(), s.imag.mid())
    cr, ci = F(s.real.mid().str(25, radius=False)), F(s.imag.mid().str(25, radius=False))
    h = F(1, 10**10)
    c = certify_zero_box("EP5", cr - h, cr + h, ci - h, ci + h)
    # farthest box corner from the disc centre, worst case over tau0 in [t0-1e-4, t0+1e-4] (rough: add 1e-4 to dy)
    dx = abs(cr - RHO[0]) + h
    dy = abs(ci - RHO[1] - F(str(t0))) + h + F(1, 10**4)
    d2 = dx * dx + dy * dy
    row = {"tau_approx": t0, "zero_centre": [float(cr), float(ci)], "box": c["box"], "winding": c["winding"],
           "dist_to_disc_centre_upper": float(d2) ** 0.5, "inside_r=0.04": d2 < F(4, 100) ** 2}
    out.append(row)
    print(row["tau_approx"], row["zero_centre"], "dist <=", row["dist_to_disc_centre_upper"], row["inside_r=0.04"])
json.dump({"kind": "R_recurrence_zero_check", "trust_class": "arb", "rows": out, "conjecture1_proved": False},
          open("/Users/peterwmurphy/rh-team/wall3/T/certs/R_recurrence_zero_check.cert.json", "w"), indent=1)
