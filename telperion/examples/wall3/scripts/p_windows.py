"""Track T: Arb check of P's section-B local Turan windows (two-zero discs: rho0 and 1-conj(rho0)).
max_{nu in window} |sum_j (z_j/|z_1|)^nu|, z_j = 1/(s1 - rho_j); rho0 from the certified tiny box. ARB. conjecture1_proved=False."""
from _paths import cert_path, rh, shown  # noqa: F401  (TELPERION_RH_TEAM / TELPERION_WALL3_CERTS)
import json, sys
from fractions import Fraction as F
from flint import acb, arb, ctx
from t3tools import powersum_certify
cert = json.load(open(cert_path("P_dominance_ratios.cert.json")))
ctx.prec = 320
res = {}
for name, claimed in (("EP5", [1.3957, 1.0620, 1.0002, 1.0000]), ("DH", [1.5284, 1.1476, 1.0032, 1.0000])):
    b = cert["objects"][name]["rho0_box"]
    lo_r, hi_r, lo_i, hi_i = (F(b[k]) for k in ("re0", "re1", "im0", "im1"))
    mid = lambda a, c: arb(f"{a.numerator}/{a.denominator}").union(arb(f"{c.numerator}/{c.denominator}"))
    rho0 = acb(mid(lo_r, hi_r), mid(lo_i, hi_i))
    s1 = acb(arb("3/2"), rho0.imag.mid())   # same s1 as p_dominance (centre's Im, exact)
    rhos = [rho0, 1 - rho0.conjugate()]
    zs = [1 / (s1 - r) for r in rhos]
    z1 = abs(zs[0])
    zn = [z / z1 for z in zs]
    rows = []
    for (m, N), c in zip(((0, 2), (2, 2), (8, 2), (40, 2)), claimed):
        out = powersum_certify([1, 1], zn, range(m + 1, m + N + 1), mode="max", prec=320)
        rows.append({"window": [m + 1, m + N], "certified_max_lower": out["certified_lower_float"], "P_float": c})
        print(name, rows[-1])
    res[name] = rows
json.dump({"kind": "turan_local_windows", "trust_class": "arb", "rows": res, "conjecture1_proved": False},
          open(cert_path("P_local_windows.cert.json"), "w"), indent=1)
