"""Track T: wall5/D1/T_REQUEST.md R1 -- the iterated twist ITW (frontier.md §A.4, iterated.py).
zeta_P(s) = zeta(s) / prod_j [zeta(s+1-rj) zeta(s+1-rjb)] * zeta(s+2-r0-r1) zeta(s+2-r0-r1b) zeta(s+2-r0b-r1) zeta(s+2-r0b-r1b) * C(s),
C(s) = prod_{p<336} D(p^-s)/N(p^-s), N(z) = |1-a0 z|^2 |1-a1 z|^2 (as (1-a z)(1-ab z) products), D(z) = (1-a0a1 z)(1-a0ba1b z)(1-a0a1b z)(1-a0ba1 z),
aj = p^(rj-1).  Closed form => Arb exact, no tail.  (a) residue A at 1; (b) residues R1 at s1 = r0+r1-1, R2 at
s2 = r0+r1b-1; (c) windings: zeta_P has winding -1 on small boxes around s1 and conj(s2) (simple poles), and the
count on [0.3,1.5] x [1,60] equals #zeros - #poles = (13 zeta zeros + rho0 + rho1) - 2 = 13, with the 13 zeta zeros
certified separately.  ARB.  Provenance: arb_fakes, Arda main 2dfc6eeee; unpushed branch wall3/telperion-certs.
conjecture1_proved = False."""
from _paths import cert_path, rh, shown  # noqa: F401  (TELPERION_RH_TEAM / TELPERION_WALL3_CERTS)
import json, time
from flint import acb, arb, acb_series, ctx, fmpz
from telperion.arb_fakes import rigorous_winding, certify_zero_box, count_offline

ctx.prec = 128
R0 = acb(arb("0.75"), arb("14.134725")); R1 = acb(arb("0.70"), arb("21.02204"))
R0B, R1B = R0.conjugate(), R1.conjugate()
SMALL = [p for p in range(2, 336) if fmpz(p).is_prime()]
LP = [acb(p).log() for p in SMALL]
DEN1 = [1 - R0, 1 - R0B, 1 - R1, 1 - R1B]                   # zeta(s + c) in the denominator
NUM2 = [2 - R0 - R1, 2 - R0 - R1B, 2 - R0B - R1, 2 - R0B - R1B]  # zeta(s + c) in the numerator


def C(s, one):
    v = one
    for lp in LP:
        a0, a0b, a1, a1b = ((R0 - 1) * lp).exp(), ((R0B - 1) * lp).exp(), ((R1 - 1) * lp).exp(), ((R1B - 1) * lp).exp()
        z = (-s * lp).exp()
        N = (one - a0 * z) * (one - a0b * z) * (one - a1 * z) * (one - a1b * z)
        D = (one - a0 * a1 * z) * (one - a0b * a1b * z) * (one - a0 * a1b * z) * (one - a0b * a1 * z)
        v = v * D / N
    return v


def _zP(s):
    one = acb_series([1])
    v = s.zeta()
    for c in DEN1:
        v = v / (s + c).zeta()
    for c in NUM2:
        v = v * (s + c).zeta()
    return v * C(s, one)


def zP(s):
    try:
        r = _zP(s)
        if all(x.is_finite() for x in r.coeffs()):
            return r
    except (ValueError, ZeroDivisionError):
        pass
    big = acb(arb(0, 10 ** 100), arb(0, 10 ** 100))
    return acb_series([big] * ctx.cap)


def point_parts(s, skip_num=None, zeta_is_pole=False):
    """value of zeta_P at the point s with one pole-carrying factor replaced by its residue 1."""
    v = acb(1) if zeta_is_pole else s.zeta()
    for c in DEN1:
        v = v / (s + c).zeta()
    for i, c in enumerate(NUM2):
        if i != skip_num:
            v = v * (s + c).zeta()
    return v * C(s, acb(1))


out = {"object": "D1 ITW, r0 = 0.75 + 14.134725i, r1 = 0.70 + 21.02204i, x1 = 336", "trust_class": "arb",
       "conjecture1_proved": False}
A = point_parts(acb(1), zeta_is_pole=True)
s1 = R0 + R1 - 1; s2 = R0 + R1B - 1
Rs1 = point_parts(s1, skip_num=0); Rs2 = point_parts(s2, skip_num=1)
out["A"] = A.str(15); out["R1"] = Rs1.str(15); out["R2"] = Rs2.str(15)
out["D1_floats"] = {"A": 1.0106676742, "R1": [0.332257552238, 0.077202016284], "R2": [0.118037211743, -0.045553547574]}
print("A =", A.str(12)); print("R1 =", Rs1.str(12)); print("R2 =", Rs2.str(12), flush=True)
t = time.time()
s2b = s2.conjugate()
for name, c in (("s1", s1), ("conj_s2", s2b)):
    cr, ci = float(c.real.mid()), float(c.imag.mid())
    st = {}
    w = rigorous_winding(zP, cr - 0.01, cr + 0.01, ci - 0.01, ci + 0.01, prec=128, stats=st)
    out[f"pole_box_{name}"] = {"centre": [cr, ci], "half": 0.01, "winding_zetaP": w}
    print("pole box", name, "winding of zeta_P", w, flush=True)
st = {}
w = rigorous_winding(zP, "0.3", "1.5", "1", "60", prec=128, init_per_side=32, stats=st)
nz = count_offline("zeta", "0.3", "1.5", "1", "60", cuts=["30"], prec=96)["total"]
rb0 = certify_zero_box(zP, "0.74", "0.76", "14.12", "14.15", expected=1, prec=128)["zeros_in_box"]
rb1 = certify_zero_box(zP, "0.69", "0.71", "21.01", "21.03", expected=1, prec=128)["zeros_in_box"]
out["count"] = {"box": ["0.3", "1.5", "1", "60"], "winding_zetaP": w, "zeta_zeros_in_box": nz,
                "rho0_box_zeros": rb0, "rho1_box_zeros": rb1, "segments": st["segments"],
                "implied_poles": nz + rb0 + rb1 - w}
print("count: winding", w, "zeta zeros", nz, "-> implied #poles =", nz + rb0 + rb1 - w, round(time.time() - t, 1))
json.dump(out, open(cert_path("D1_ITW.cert.json"), "w"), indent=1, default=str)
