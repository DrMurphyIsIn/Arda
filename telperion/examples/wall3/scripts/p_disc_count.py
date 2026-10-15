"""Track T: the disc |s - s1| <= 2 (s1 = 3/2 + i gamma0) holds exactly the 2 zeros rho0, 1-conj(rho0) (P section B).
Rectangles [1/20, 8/5] and [19/20, 8/5] x [gamma0-2, gamma0+2] + FE mirror cover the disc minus {Re s >= 8/5}; the latter is zero-free (dominant-term
cert, arb_fakes.right_halfplane_nonvanishing).  ARB. conjecture1_proved=False."""
from _paths import cert_path, rh, shown  # noqa: F401  (TELPERION_RH_TEAM / TELPERION_WALL3_CERTS)
import json
from fractions import Fraction as F
from telperion.arb_fakes import count_offline, right_halfplane_nonvanishing
cert = json.load(open(cert_path("P_dominance_ratios.cert.json")))
out = {}
for name in ("EP5", "DH"):
    b = cert["objects"][name]["rho0_box"]
    g = (F(b["im0"]) + F(b["im1"])) / 2
    g = F(round(g * 10**6), 10**6)
    # Arb's Hurwitz-zeta jets go nan on wide balls at Re s < 0, so use the FE symmetry s -> 1 - conj(s) instead:
    # zeros in the disc with Re s < 1/20 mirror to zeros with Re s > 19/20 in the same height range.
    c = count_offline(name, F(1, 20), F(8, 5), g - 2, g + 2, cuts=[g], prec=96)
    c_right = count_offline(name, F(19, 20), F(8, 5), g - 2, g + 2, cuts=[g], prec=96)
    out.setdefault("right_strip", {})[name] = c_right
    print(name, "zeros with 19/20 < Re s < 8/5:", c_right["total"])
    rh = right_halfplane_nonvanishing(name, F(8, 5))
    out[name] = {"rect_count": c, "right_halfplane": rh}
    print(name, "rect total", c["total"], "| Re s >= 8/5 zero-free:", rh["certified"])
json.dump(out, open(cert_path("P_disc_count.cert.json"), "w"), indent=1, default=str)
