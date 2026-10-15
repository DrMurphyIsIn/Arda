"""Track T: per-arc margins for track R's Arb Rouche certificates (R/r_arb.py -> out/arb_rouche_new.txt), reusing F1's
f1_arb_rouche (read-only) but re-running the arc loop to record min over accepted arcs of (lo - du)/lo, where
lo = lower|EP5(B_j)|, du = upper|EP5(B_j + i tau) - EP5(B_j)|.  Comparisons here are on the exact arb endpoints
(arb < arb), not float().  ARB.  conjecture1_proved = False."""
from _paths import cert_path, cert_read, rh, shown  # noqa: F401  (see _paths: inputs, scratch/committed certs)
import sys, json
from fractions import Fraction
sys.path.insert(0, str(rh("wall2/F1")))
import numpy as np
from flint import acb, arb
import f1_arb_rouche as F

rows = []
for tau in (Fraction(652063, 1000), Fraction(666389, 1000), Fraction(37309, 40)):
    itau = acb(0, arb(tau.numerator) / tau.denominator)
    stack = [(2 * np.pi * (j + 0.5) / 256, np.pi / 256, 0) for j in range(256)]
    worst, narcs, fails = None, 0, 0
    while stack:
        phi, half, d = stack.pop()
        B = F.ball(phi, half)
        f0 = F.ep5_acb(B)
        f1 = F.ep5_acb(B + itau)
        lo = f0.abs_lower()
        du = (f1 - f0).abs_upper()
        if not (du < lo) and d < 6:
            stack += [(phi - half / 2, half / 2, d + 1), (phi + half / 2, half / 2, d + 1)]
            continue
        narcs += 1
        if not (du < lo):
            fails += 1
            continue
        m = (lo - du) / lo
        if worst is None or m < worst:
            worst = m
    rows.append({"tau": str(tau), "arcs": narcs, "failing_arcs_exact": fails,
                 "min_rel_margin": float(worst.lower()) if worst is not None else None})
    print(rows[-1], flush=True)
json.dump({"kind": "R_rouche_margins", "trust_class": "arb", "rows": rows, "conjecture1_proved": False},
          open(cert_path("R_rouche_margins.cert.json"), "w"), indent=1)
