"""Track T: Arb certificates for every REAL twist in B/out/summary.txt (B/twist.py), rho0 = beta0 + i gamma0.
zeta_P(s) = zeta(s) / (zeta(s+1-rho0) zeta(s+1-conj rho0)) * prod_{p < x1} [(1 - p^(rho0-1-s))(1 - p^(conj rho0-1-s))]^-1,
x1 = 2^(1/(1-beta0)): closed form, no Euler-product tail.  Per object:
  (1) zero box around rho0 (winding 1, re-checked at 1.5x precision);
  (2) [count mode] exactly one zero in [L, 3/2] x [1/20, 100], L = min(0.7, beta0 - 0.04), with no poles there:
      a pole needs zeta(w) = 0 at w = s + 1 - rho0 or s + 1 - conj(rho0); certify zeta zero-free on the covering box
      [L + 1 - beta0, 5/2 - beta0] x [1/20 - gamma0, 100 + gamma0] (pole s = 1 acknowledged);
  (3) residue A at s = 1.
ARB.  Provenance: arb_fakes, Arda main 2dfc6eeee (guarded) via callable; script on unpushed branch
wall3/telperion-certs.  conjecture1_proved = False."""
from _paths import cert_path, cert_read, rh, shown  # noqa: F401  (see _paths: inputs, scratch/committed certs)
import json, sys, time
from t3tools import scrub_callables  # names, not 0x addresses (t3tools is on sys.path via _paths)
from fractions import Fraction as F
from flint import acb, arb, acb_series, ctx, fmpz
from telperion.arb_fakes import rigorous_winding, certify_zero_box

CASES = [("0.60", "14.134725", True), ("0.75", "14.134725", True), ("0.85", "30.424876", True),
         ("0.85", "50", True), ("0.95", "14.134725", False)]
if len(sys.argv) > 1:
    CASES = [c for c in CASES if c[0] == sys.argv[1] and (len(sys.argv) < 3 or c[1] == sys.argv[2])]
results = {}
for bs, gs, count in CASES:
    ctx.prec = 128
    B0, G0 = arb(bs), arb(gs)
    RHO, RHOB = acb(B0, G0), acb(B0, -G0)
    x1 = 2 ** (1 / (1 - float(bs)))
    small = [p for p in range(2, int(x1) + 1) if fmpz(p).is_prime() and p < x1]
    lps = [acb(p).log() for p in small]

    def _z(s):
        one = acb_series([1])
        v = s.zeta() / ((s + (1 - RHO)).zeta() * (s + (1 - RHOB)).zeta())
        for lp in lps:
            v = v / ((one - ((RHO - 1) * lp - s * lp).exp()) * (one - ((RHOB - 1) * lp - s * lp).exp()))
        return v

    def zetaP(s):
        try:
            return _z(s)
        except ValueError:  # ball meets a pole of zeta(s+1-rho0): huge finite ball => segment fails => bisect
            big = acb(arb(0, 10 ** 100), arb(0, 10 ** 100))
            return acb_series([big] * ctx.cap)

    key = f"b{bs}_g{gs}"
    r = {"rho0": f"{bs} + {gs} i", "x1": x1, "n_small_primes": len(small), "conjecture1_proved": False}
    t = time.time()
    b, g = F(bs), F(gs)
    h = F(1, 100)
    r["zero_box"] = certify_zero_box(zetaP, b - h, b + h, g - h, g + h, expected=1, prec=128)
    r["zero_box_seconds"] = round(time.time() - t, 1)
    if count:
        L = min(F(7, 10), b - F(4, 100))
        st = {}
        w = rigorous_winding(zetaP, L, F(3, 2), F(1, 20), 100, prec=128, stats=st)
        r["count"] = {"box": [str(L), "3/2", "1/20", "100"], "winding": w, "segments": st["segments"]}
        pe = certify_zero_box("zeta", L + 1 - b, F(5, 2) - b, F(1, 20) - g - F(1, 100), 100 + g + F(1, 100),
                              expected=0, poles=[(1, 0)], prec=96)
        r["pole_exclusion_zeta_box"] = pe["box"]
        r["zeros_in_count_box"] = w  # = zeros - poles, poles excluded by pe
    ctx.prec = 128
    A = 1 / ((2 - RHO).zeta() * (2 - RHOB).zeta())
    for lp in lps:
        A = A / ((1 - ((RHO - 2) * lp).exp()) * (1 - ((RHOB - 2) * lp).exp()))
    r["residue_A"] = A.real.str(15)
    r["seconds"] = round(time.time() - t, 1)
    results[key] = r
    print(key, "box ok", r.get("count", {}).get("winding"), "A =", r["residue_A"], r["seconds"], "s", flush=True)
    json.dump(scrub_callables(results), open(cert_path(f"B_twist_REAL_all{'_' + sys.argv[1] if len(sys.argv) > 1 else ''}.cert.json"), "w"),
              indent=1, default=str)
