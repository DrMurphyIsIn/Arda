"""Track T: cross-wiring audit of the B REAL-twist residue comparisons.  For every TW run in B/out/tw_REAL_*.json,
recompute A = 1/(zeta(2-rho0) zeta(2-conj rho0)) * prod_{p<x1} [(1-p^(rho0-2))(1-p^(conj rho0-2))]^-1 in Arb and
compare with the A stored in THAT file (matched by its own beta0, gamma0 fields).  ARB.  conjecture1_proved = False."""
from _paths import cert_path, rh, shown  # noqa: F401  (TELPERION_RH_TEAM / TELPERION_WALL3_CERTS)
import glob, json
from flint import acb, arb, ctx, fmpz
ctx.prec = 128
rows = []
for f in sorted(glob.glob(str(rh("wall3/B/out/tw_REAL_*.json")))):
    d = json.load(open(f))
    b0, g0, BA = d["beta0"], d["gamma0"], d["A"]
    rho = acb(arb(repr(b0)), arb(repr(g0))); rhob = rho.conjugate()
    x1 = 2 ** (1 / (1 - b0))
    A = 1 / ((2 - rho).zeta() * (2 - rhob).zeta())
    for p in range(2, int(x1) + 1):
        if p < x1 and fmpz(p).is_prime():
            lp = acb(p).log()
            A = A / ((1 - ((rho - 2) * lp).exp()) * (1 - ((rhob - 2) * lp).exp()))
    ok = bool(abs(A.real - arb(BA)).upper() <= A.real.rad() + 1e-14)
    rows.append({"file": f.split("/")[-1], "beta0": b0, "gamma0": g0, "A_arb": A.real.str(16), "A_B": BA,
                 "B_inside_ball_plus_1e-14": ok})
    print(rows[-1]["file"], rows[-1]["A_arb"], BA, ok)
json.dump({"kind": "B_residue_crosswire_audit", "trust_class": "arb", "rows": rows, "conjecture1_proved": False},
          open(cert_path("B_residue_audit.cert.json"), "w"), indent=1)
