"""Track T: Arb certificates for lead note N8 (wall5/LEAD_NOTES.md, wall5/n8_continuous.py), the continuous Beurling system
    log zeta_P(s) = E1((s-1)v0) - E1((s-rho0)v0) - E1((s-conj rho0)v0),   v0 = log 103,  rho0 = 0.85 + 14.134725 i.
Branch-free closed form used here (E1(z) = -gamma - log z + Ein(z), Ein entire; the 2 pi i jumps of E1 vanish under exp):
    zeta_P(s) = e^gamma * v0 (s - rho0)(s - conj rho0)/(s - 1) * exp(Ein(a) - Ein(b) - Ein(bb)),
    a = (s-1) v0, b = (s-rho0) v0, bb = (s - conj rho0) v0.
So zeta_P is meromorphic with exactly: simple zeros at rho0, conj rho0 and a simple pole at s = 1 (PROVED from the form).
Ein(w) is evaluated rigorously: Taylor series with explicit tail bound for |w| <= 120 (or whenever the ball meets the
negative real axis), else Ein = E1 + log w + gamma via acb.expint(1) (ball strictly off the cut).  The callable
supports jets of order <= 1 (ctx.cap <= 2), which is what arb_fakes.rigorous_winding uses.  ARB.  conjecture1_proved = False.
Provenance: arb_fakes, Arda main 2dfc6eeee; script on unpushed branch wall3/telperion-certs."""
from _paths import cert_path, cert_read, rh, shown  # noqa: F401  (see _paths: inputs, scratch/committed certs)
import json, math, time
from fractions import Fraction as F
from flint import acb, arb, acb_series, ctx
from telperion.arb_fakes import certify_zero_box, rigorous_winding

ctx.prec = 320   # constants at high precision: Taylor evaluation of Ein amplifies input radii by ~e^|w|
B0, G0 = arb("0.85"), arb("14.134725")
RHO = acb(B0, G0); RHOB = RHO.conjugate()
V0 = arb(103).log()
EG = arb.const_euler().exp()
ctx.prec = 128


def _ein_taylor(w):
    """(Ein(w), Ein'(w)) by Taylor series with a rigorous tail bound."""
    Ra = abs(w).upper()            # rigorous upper bound for |w| (arb); R (float) only sizes K and the precision
    R = float(Ra)
    K = int(3 * R) + 60   # R^K/K! < e^-60 or so: tail negligible
    old = ctx.prec
    ctx.prec = old + int(1.5 * R) + 30
    try:
        s0 = acb(0); s1 = acb(0); term = acb(1)  # term = w^k / k!
        for k in range(1, K + 1):
            term = term * w / k
            sg = 1 if k % 2 == 1 else -1
            s0 += sg * term / k                    # (-1)^{k+1} w^k/(k k!)
            s1 += sg * term / w if False else 0    # placeholder (derivative below)
        # Ein'(w) = sum_{k>=0} (-1)^k w^k/(k+1)!
        d = acb(0); term = acb(1)
        for k in range(0, K + 1):
            d += (term if k % 2 == 0 else -term) / (k + 1)
            term = term * w / (k + 1)
        # tails: sum_{k>K} R^k/(k k!) and sum_{k>K} R^k/(k+1)!  <=  R^{K+1}/(K+1)! / (1 - R/(K+2))
        tb = Ra ** (K + 1) / arb(K + 1).fac() / (1 - Ra / (K + 2))
        e = arb(0, tb.upper())
        return s0 + acb(e, e), d + acb(e, e)
    finally:
        ctx.prec = old


def _ein_point(c):
    """(Ein(c), Ein'(c)) at an (almost) exact point c."""
    if float(abs(c).upper()) <= 120:
        return _ein_taylor(c)
    # Arb's E1 (acb_hypgeom_expint) is rigorous, but its ball width depends erratically on the working precision
    # for |w| ~ 1e2; try several precisions and keep the tightest (all are rigorous enclosures).
    old = ctx.prec
    cands = []
    for p in (53, 64, 96, 128, 192):
        ctx.prec = p
        z = c.expint(1)
        if z.is_finite():
            cands.append(z)
            if float(z.rad()) < 1e-12 * max(1.0, float(abs(z).mid())):
                break
    ctx.prec = old
    if not cands:
        raise ValueError("E1 not finite")
    e1 = min(cands, key=lambda z: float(z.rad()))
    return e1 + c.log() + arb.const_euler(), -((-c).expm1()) / c


def _sup_d1_d2(B):
    """upper bounds for sup_B |Ein'| and sup_B |Ein''| (Ein' = (1-e^-w)/w, Ein'' = ((1+w)e^-w - 1)/w^2)."""
    if float(abs(B).upper()) < 1 or B.contains(acb(0)) or float(abs(B).lower()) < 0.5:
        e = (abs(B).upper()).exp()       # |sum (-w)^k/(k+1)!| <= e^|w|, same for the second derivative series
        return e, e
    d1 = abs((1 - (-B).exp()) / B).upper()
    d2 = abs(((1 + B) * (-B).exp() - 1) / (B * B)).upper()
    return d1, d2


def _ein(w):
    """(Ein(w), Ein'(w)) as balls valid on the whole ball w: value at the centre plus radius * sup|derivative|."""
    c = acb(w.real.mid(), w.imag.mid())
    r = arb(w.real.rad()) + arb(w.imag.rad())   # |w - c| <= rad_re + rad_im, summed in arb (outward), not in floats
    v, d = _ein_point(c)
    if r == 0:
        return v, d
    d1, d2 = _sup_d1_d2(w)
    e0 = arb(0, (r * d1).upper()); e1 = arb(0, (r * d2).upper())
    return v + acb(e0, e0), d + acb(e1, e1)


def zetaP(s):
    try:
        r = _zetaP(s)
        if all(x.is_finite() for x in r.coeffs()):
            return r
    except (ValueError, ZeroDivisionError):
        pass
    # ball too wide (meets s = 1, or overflow): huge finite ball => segment test fails => rigorous_winding bisects
    big = acb(arb(0, 10 ** 100), arb(0, 10 ** 100))
    return acb_series([big] * ctx.cap)


def _zetaP(s):
    c = list(s.coeffs()) + [acb(0)] * 2   # acb_series strips zero coefficients (e.g. s = 0)
    cap = ctx.cap
    s0 = c[0]
    a, b, bb = (s0 - 1) * V0, (s0 - RHO) * V0, (s0 - RHOB) * V0
    Ea, Da = _ein(a); Eb, Db = _ein(b); Ebb, Dbb = _ein(bb)
    pref = EG * V0 * (s0 - RHO) * (s0 - RHOB) / (s0 - 1)
    f0 = pref * (Ea - Eb - Ebb).exp()
    if cap == 1:
        return acb_series([f0])
    # f'/f = 1/(s-rho0) + 1/(s-rhob) - 1/(s-1) + v0 (Ein'(a) - Ein'(b) - Ein'(bb)); write f' without dividing by
    # (s - rho0): d/ds[(s-rho0)(s-rhob)] = (2s - rho0 - rhob)
    E = (Ea - Eb - Ebb).exp()
    dpre = EG * V0 * ((2 * s0 - RHO - RHOB) * (s0 - 1) - (s0 - RHO) * (s0 - RHOB)) / ((s0 - 1) ** 2)
    f1 = dpre * E + pref * E * V0 * (Da - Db - Dbb)
    out = [f0, f1 * c[1]] + [acb(0)] * max(0, cap - 2)
    if cap > 2:
        raise ValueError("zetaP: jets of order <= 1 only")
    return acb_series(out[:cap])


def val(sr, si, prec=128):
    ctx.prec, ctx.cap = prec, 1
    return zetaP(acb_series([acb(arb(sr), arb(si))])).coeffs()[0]


res = {"object": "N8 continuous Beurling: exp(E1((s-1)v0) - E1((s-rho0)v0) - E1((s-rhob)v0)), v0 = log 103, "
                 "rho0 = 0.85 + 14.134725 i", "trust_class": "arb", "conjecture1_proved": False}
# sanity vs direct E1 formula for Re s > 1 (branch-free there)
ctx.prec = 128
s = acb(2, 3)
ctx.prec = 64   # Arb's E1 is tight at 64 bits here (see _ein)
direct = ((s - 1) * V0).expint(1) - ((s - RHO) * V0).expint(1) - ((s - RHOB) * V0).expint(1)
ctx.prec = 128
res["check_Re_s_2"] = {"closed_form": val("2", "3").str(20), "direct_E1": direct.exp().str(20),
                       "overlap": bool(val("2", "3").overlaps(direct.exp()))}
print("check at 2+3i:", res["check_Re_s_2"], flush=True)
t = time.time()
res["a_zero_box"] = certify_zero_box(zetaP, "0.84", "0.86", "14.12", "14.15", expected=1, prec=128)
print("(a) zero box ok", round(time.time() - t, 1), flush=True)
t = time.time(); st = {}
w = rigorous_winding(zetaP, "0.3", "1.5", "1/20", "100", prec=128, init_per_side=64, stats=st)
res["b_count"] = {"box": ["0.3", "1.5", "1/20", "100"], "winding": w, "segments": st["segments"],
                  "note": "closed box excludes s = 1 (Im >= 1/20): winding = zeros"}
print("(b) [0.3,1.5]x[1/20,100] winding", w, st["segments"], round(time.time() - t, 1), flush=True)
t = time.time()
st2 = {}
w2 = rigorous_winding(zetaP, "0.3", "1.5", "-1", "100", prec=128, init_per_side=64, stats=st2, poles=[(1, 0)])
st3 = {}
w3 = rigorous_winding(zetaP, "0.3", "1.5", "-1", "100", prec=192, init_per_side=97, stats=st3, poles=[(1, 0)])
assert w2 == w3
res["b_count_with_pole"] = {"box": ["0.3", "1.5", "-1", "100"], "winding": w2, "poles_in_box": 1,
                            "zeros_in_box": w2 + 1, "recheck_prec192_winding": w3, "segments": st2["segments"]}
print("(b') [0.3,1.5]x[-1,100] with pole s=1 acknowledged: zeros", res["b_count_with_pole"]["zeros_in_box"],
      "winding", res["b_count_with_pole"]["winding"], round(time.time() - t, 1))
rows = []
for sig in ("0.6", "0"):
    for tt in ("50", "200", "1000", "5000"):
        v = val(sig, tt, prec=192)
        d = abs(v - 1)
        rows.append({"sigma": sig, "t": tt, "abs_zetaP_minus_1": d.str(10)})
        print("(c) sigma", sig, "t", tt, "|zeta_P - 1| =", d.str(8))
res["c_vertical"] = rows
# D1 cross-checks (wall5/D1/out/continuous.txt): residue A at s = 1 and zeta_P'(rho0)
ctx.prec = 192
Eb1, _ = _ein((1 - RHO) * V0); Eb2, _ = _ein((1 - RHOB) * V0)
A = EG * V0 * (1 - RHO) * (1 - RHOB) * (-Eb1 - Eb2).exp()
Ea0, _ = _ein((RHO - 1) * V0); Ebb0, _ = _ein((RHO - RHOB) * V0)
dz = EG * V0 * (RHO - RHOB) / (RHO - 1) * (Ea0 - Ebb0).exp()
res["residue_A"] = A.str(15); res["zetaP_prime_rho0"] = dz.str(15)
res["D1_floats"] = {"A": 0.122010758984, "zetaP_prime_rho0": [8.0879161, 0.2576544]}
print("A =", A.str(12), " zeta_P'(rho0) =", dz.str(12), flush=True)
json.dump(res, open(cert_path("N8_continuous.cert.json"), "w"), indent=1, default=str)
