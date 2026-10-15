"""Track T: the disc |s - s1| <= 2 (s1 = 3/2 + i gamma0) holds exactly the 2 zeros rho0, 1-conj(rho0) (P section B).
Rectangles [1/20, 8/5] and [19/20, 8/5] x [g-2-1e-5, g+2+1e-5] (s1 = 3/2 + i g, exact) + FE mirror cover the disc minus {Re s >= 8/5}; the latter is zero-free (dominant-term
cert, arb_fakes.right_halfplane_nonvanishing).  ARB. conjecture1_proved=False."""
from _paths import cert_path, cert_read, rh, shown  # noqa: F401  (see _paths: inputs, scratch/committed certs)
import json
from fractions import Fraction as F
from telperion.arb_fakes import count_offline, right_halfplane_nonvanishing
cert = json.load(open(cert_read("P_dominance_ratios.cert.json")))
out = {}
for name in ("EP5", "DH"):
    g = F(cert["objects"][name]["s1_im_exact"])   # s1 = 3/2 + i g, the one s1 of all P scripts (p_dominance)
    e = F(1, 10**5)   # margin: the rectangles strictly contain the disc's height range [g - 2, g + 2]
    # Arb's Hurwitz-zeta jets go nan on wide balls at Re s < 0, so use the FE symmetry s -> 1 - conj(s) instead:
    # zeros in the disc with Re s < 1/20 mirror to zeros with Re s > 19/20 in the same height range.
    c = count_offline(name, F(1, 20), F(8, 5), g - 2 - e, g + 2 + e, cuts=[g + F(1, 1000)], prec=96)   # cut off the zero rho0 (Im rho0 = g)
    c_right = count_offline(name, F(19, 20), F(8, 5), g - 2 - e, g + 2 + e, cuts=[g + F(1, 1000)], prec=96)   # cut off the zero rho0 (Im rho0 = g)
    out.setdefault("right_strip", {})[name] = c_right
    print(name, "zeros with 19/20 < Re s < 8/5:", c_right["total"])
    rhp = right_halfplane_nonvanishing(name, F(8, 5))
    out[name] = {"rect_count": c, "right_halfplane": rhp}
    print(name, "rect total", c["total"], "| Re s >= 8/5 zero-free:", rhp["certified"])
json.dump(out, open(cert_path("P_disc_count.cert.json"), "w"), indent=1, default=str)
