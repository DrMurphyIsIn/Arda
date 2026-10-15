"""Track T: WALL-6 Q1 T_REQUEST -- G(s) = zeta(s) * Z_fake(3^-s), Z_fake(T) = P(T)/((1-T)(1-3T)),
P(T) = 1 - 2T + 9T^2 - 6T^3 + 9T^4 (WALL-3 E's genus-2 fake, Arb/exact/kernel certified in E_ff_fake.cert.json).
(a) winding-1 boxes at s0 and conj(s0); (b) zero count in [3/5, 19/20] x [1/20, 13] (expected 5); (c) FE ball check of
Lambda(s) = pi^(-s/2) Gamma(s/2) 3^s G(s) = Lambda(1-s).  Poles (s=1 double, 1 + 2 pi i k/log3, 2 pi i k/log3) all lie on
Re s in {0, 1}: none in the closed boxes used.  ARB; arb_fakes (Arda main 2dfc6eeee); unpushed branch
wall3/telperion-certs.  conjecture1_proved = False."""
import json
from _paths import cert_path  # noqa: E402  (see _paths: inputs, scratch/committed certs; puts t3tools on sys.path)
from t3tools import scrub_callables  # names, not 0x addresses
from flint import acb, arb, acb_series, ctx
from telperion.arb_fakes import certify_zero_box, rigorous_winding

L3 = acb(3).log()


def G(s):
    try:
        r = _G(s)
        if all(x.is_finite() for x in r.coeffs()):
            return r
    except (ValueError, ZeroDivisionError):
        pass
    big = acb(arb(0, 10 ** 100), arb(0, 10 ** 100))   # ball meets a pole: huge ball => segment fails => bisect
    return acb_series([big] * ctx.cap)


def _G(s):
    one = acb_series([1])
    T = (-s * L3).exp()
    P = one - 2 * T + 9 * T * T - 6 * T * T * T + 9 * T * T * T * T
    return s.zeta() * P / ((one - T) * (one - 3 * T))


out = {"object": "Q1 G = zeta(s) Z_fake(3^-s)", "trust_class": "arb", "conjecture1_proved": False}
out["a_box"] = certify_zero_box(G, "0.8747", "0.8749", "1.1848", "1.1850", expected=1, prec=128)
out["a_box_conj"] = certify_zero_box(G, "0.8747", "0.8749", "-1.1850", "-1.1848", expected=1, prec=128)
print("(a) boxes:", out["a_box"]["winding"], out["a_box_conj"]["winding"], flush=True)
st = {}
w = rigorous_winding(G, "3/5", "19/20", "1/20", "13", prec=128, init_per_side=32, stats=st)
w2 = rigorous_winding(G, "3/5", "19/20", "1/20", "13", prec=192, init_per_side=45)
out["b_count"] = {"box": ["3/5", "19/20", "1/20", "13"], "winding": w, "recheck_192": w2, "segments": st["segments"]}
print("(b) count:", w, w2, flush=True)
ctx.prec = 128; ctx.cap = 1
rows = []
for sr, si in (("0.3", "7.1"), ("0.9", "23.4"), ("0.874", "1.18"), ("2", "5")):
    s = acb(arb(sr), arb(si))
    def Lam(z):
        return (-z / 2 * acb.pi().log()).exp() * (z / 2).gamma() * (z * L3).exp() * G(acb_series([z])).coeffs()[0]
    a, b = Lam(s), Lam(1 - s)
    d = a - b
    rows.append({"s": f"{sr}+{si}i", "Lambda(s)": a.str(12), "Lambda(1-s)": b.str(12), "diff_contains_0": bool(d.contains(0)),
                 "rel_diff_upper": float(abs(d).upper()) / float(abs(a).lower())})
    print("(c)", rows[-1]["s"], rows[-1]["diff_contains_0"], f'{rows[-1]["rel_diff_upper"]:.1e}', flush=True)
out["c_FE"] = rows
json.dump(scrub_callables(out), open(cert_path("Q1_G.cert.json"), "w"), indent=1, default=str)
