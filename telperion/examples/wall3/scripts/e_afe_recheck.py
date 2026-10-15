"""Track T: independent Arb recheck of track E's e4_arb table (main/reflected AFE terms on certified zero boxes).

conjecture1_proved = False.  Independent of E's code in three places:
  * coefficients: EP5's r_Q(n) by exact lattice count (E took them from the float harness);
  * chi: E uses exp(lgamma(1-s) - lgamma(s) + ...); T checks it against chi = F(s)/F(1-s) from arb_fakes' F
    at an off-zero test point near each zero (same branch-free identity F(s) = chi(s) F(1-s));
  * zero boxes: re-certified here at h = 1e-6 with arb_fakes.certify_zero_box (guarded, 72470dd5f).
Then M, R, |M+R| are recomputed and checked to OVERLAP E's printed intervals.  ARB."""
import json, math
from fractions import Fraction as F
from flint import acb, arb, ctx
from telperion.arb_fakes import certify_zero_box, fake_series, _kappa
from flint import acb_series
ctx.prec = 160
PI = arb.pi()
E = json.load(open("/Users/peterwmurphy/rh-team/wall3/E/out/e4_arb.cert.json"))


def coeffs(name, N):
    if name == "zeta":
        return [0] + [arb(1)] * N
    if name == "DH":
        k = _kappa()
        tab = [arb(0), arb(1), k, -k, arb(-1)]
        return [0] + [tab[n % 5] for n in range(1, N + 1)]
    r = [0] * (N + 1)
    M = int(math.isqrt(N)) + 1
    for m in range(-M, M + 1):
        for n in range(-M, M + 1):
            v = m * m + 5 * n * n
            if 0 < v <= N:
                r[v] += 1
    return [0] + [arb(r[k]) for k in range(1, N + 1)]


def F_at(name, s):
    ctx.cap = 1
    return fake_series(name, acb_series([s])).coeffs()[0]


def chi_E(name, s):  # E's formula, re-typed
    if name == "zeta":
        G = lambda u: -u / 2 * PI.log() + (u / 2).lgamma()
    elif name == "DH":
        G = lambda u: u / 2 * (arb(5) / PI).log() + ((u + 1) / 2).lgamma()
    else:
        G = lambda u: u * (arb(20).sqrt() / (2 * PI)).log() + u.lgamma()
    return (G(1 - s) - G(s)).exp()


Q = {"zeta": (1, 1), "DH": (5, 1), "EP5": (20, 2)}
rows = []
for e in E:
    name, (re, im) = e["name"], e["rho"]
    b = F(re).limit_denominator(10**12); g = F(im).limit_denominator(10**12); h = F(1, 10**6)
    cert = certify_zero_box(name, b - h, b + h, g - h, g + h, expected=1)
    q, d = Q[name]
    x = int(math.floor(math.sqrt(q * (float(g) / (2 * math.pi)) ** d)))
    assert x == e["x"], (name, x, e["x"])
    a = coeffs(name, x)
    # chi identity check at an off-zero point
    tp = acb(arb(f"{b.numerator}/{b.denominator}") + arb("0.05"), arb(f"{g.numerator}/{g.denominator}") + arb("0.3"))
    ch1 = chi_E(name, tp); ch2 = F_at(name, tp) / F_at(name, 1 - tp)
    chi_ok = (ch1 - ch2).overlaps(acb(0)) if True else None
    rad = arb(0, float(h) * 1.5)
    s = acb(arb(f"{b.numerator}/{b.denominator}") + rad, arb(f"{g.numerator}/{g.denominator}") + rad)
    Mv = sum((a[n] * acb(n) ** (-s) for n in range(1, x + 1)), acb(0))
    chi = chi_E(name, s)
    Rv = chi * sum((a[n] * acb(n) ** (s - 1) for n in range(1, x + 1)), acb(0))
    Fs = F_at(name, s)
    def iv(v): return (float(v.lower()), float(v.upper()))
    def ov(mine, theirs):
        lo, hi = map(float, theirs.strip("[]").split(","))
        return not (mine[1] < lo * (1 - 1e-5) or mine[0] > hi * (1 + 1e-5))
    row = {"name": name, "zero": [re, im], "x": x, "chi_identity_ok": bool(chi_ok),
           "chi_identity_err": float(abs(ch1 - ch2).upper()) / float(abs(ch2).lower()),
           "chi": iv(abs(chi)), "M": iv(abs(Mv)), "R": iv(abs(Rv)), "M+R": iv(abs(Mv + Rv)),
           "|F| on box ball (should contain 0)": iv(abs(Fs)),
           "overlap_E": {k: ov(iv(v), e[kk]) for k, v, kk in (("chi", abs(chi), "chi"), ("M", abs(Mv), "M"),
                                                               ("R", abs(Rv), "R"), ("M+R", abs(Mv + Rv), "E"))}}
    rows.append(row)
    print(name, f"{re:.6f}+{im:.4f}i", "chi-id", row["chi_identity_ok"], f"{row['chi_identity_err']:.1e}",
          "|M+R|", [f"{v:.6g}" for v in row["M+R"]], "E:", e["E"], row["overlap_E"])
json.dump({"kind": "afe_recheck_of_E_e4", "trust_class": "arb", "rows": rows, "conjecture1_proved": False},
          open("/Users/peterwmurphy/rh-team/wall3/T/certs/E_e4_recheck.cert.json", "w"), indent=1)
