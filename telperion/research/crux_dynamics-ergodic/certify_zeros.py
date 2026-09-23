"""Certified (Arb, segment-enclosure) off-line zeros for the dynamics-ergodic negative controls.

conjecture1_proved = False.  Trust class: Arb interval arithmetic, not the Lean kernel.

Claims CERTIFIED (each box lies strictly inside Re s > 1/2, so winding number 1 is a zero OFF the
critical line):
  (a) the Heegner point i*sqrt5 (x^2 + 5y^2, class number 2): Z_{x^2+5y^2} has exactly one zero in
      (0.90, 0.96) x (15.64, 15.70) (genus identity, no truncation);
  (b) the Davenport-Heilbronn function: exactly one zero in (0.79, 0.83) x (85.68, 85.72);
plus a control box with winding 0 for each.
Claim NUMERICAL ONLY (not certified): the Hecke neighbour 21i/20 = (21 i + 0)/20 in T_420(i) has a
zero of E*(21i/20, .) at 0.77598584986280365159 + 21.665526398629925215 i (Newton on the Fourier
expansion, residual printed).  Segment certification fails there: Arb's K_nu for a BALL of complex
order nu = s - 1/2 with Im nu ~ 21.7 amplifies the input radius by ~e^{pi |Im nu|} (cancellation
between I_{-nu} and I_nu), so no segment ball is ever accepted.  A certificate for points of the
Hecke orbit of i needs a Bessel-free representation (genus theory where the class group is
2-torsion; see hecke_orbit_genus.py for 3i in T_3(i)).
Consistency checks of the evaluators: Fourier expansion vs lattice sum at s = 3, and the rigorous
Fourier expansion (with tail ball) vs the genus identity at i*sqrt5.
Output: certify_zeros_output.json (and stdout).
"""
from __future__ import annotations

import json
import time
from fractions import Fraction as Fr

from flint import acb, arb

import eisenstein as E
from arb_winding import winding_number


def newton(f, s, steps=8):
    h = acb("1e-25")
    for _ in range(steps):
        v = f(s)
        d = (f(s + h) - v) / h
        s = s - v / d
        s = acb(s.real.mid(), s.imag.mid())
    return s


def main():
    out = {"trust_class": "Arb interval arithmetic (python-flint 0.6), segment-certified winding; "
                          "not a Lean kernel proof", "conjecture1_proved": False, "checks": [],
           "certificates": []}

    # consistency of the evaluators
    for (x, y, lab) in [(Fr(0), Fr(1), "i"), (Fr(0), Fr(2), "2i"), (Fr(0), Fr(21, 20), "21i/20")]:
        four = E.estar(x, y, acb(3), N=40, rigorous=False)
        latt = E.estar_lattice(float(x), float(y), 3.0, M=250)
        out["checks"].append({"what": f"E*({lab}, 3): Fourier vs lattice sum (M=250)",
                              "fourier": four.real.mid().str(15), "lattice": repr(latt.real)})
    s = acb("0.9", "15.7")
    y5 = arb(5).sqrt()
    four = E.estar(0, y5, s, N=30)
    gen = arb.pi() ** (-s) * s.gamma() * acb(5) ** (s / 2) * E.epstein_x2_5y2(s) / 2
    out["checks"].append({"what": "E*(i sqrt5, 0.9+15.7i): rigorous Fourier vs genus identity",
                          "fourier": str(four), "genus": str(gen),
                          "overlap": bool(four.overlaps(gen))})

    f21_float = lambda s: E.estar(0, Fr(21, 20), s, N=40, rigorous=False)
    z = newton(f21_float, acb("0.78", "21.67"), steps=10)
    res = E.estar(0, Fr(21, 20), z, N=40)
    scale = E.estar(0, Fr(21, 20), acb("0.70", "21.665"), N=40)
    out["numerical_only"] = {
        "function": "E*(21i/20, s), 21i/20 in T_420(i)",
        "zero": [z.real.mid().str(25), z.imag.mid().str(25)],
        "rigorous_enclosure_of_E*_at_the_zero_midpoint": str(res),
        "for_scale_rigorous_enclosure_of_E*_at_0.70+21.665i": str(scale),
        "status": "NUMERICAL: the point evaluation is a rigorous enclosure, but a small value at one "
                  "point does not certify a zero; NOT segment-certified (see module docstring)"}
    print(json.dumps(out["numerical_only"]), flush=True)
    jobs = [
        ("i*sqrt5 (x^2+5y^2, h=2): Z_Q(s) via genus identity", E.epstein_x2_5y2, E.epstein_x2_5y2,
         acb("0.933", "15.668"),
         (Fr(90, 100), Fr(96, 100), Fr(1564, 100), Fr(1570, 100)),
         (Fr(60, 100), Fr(66, 100), Fr(1564, 100), Fr(1570, 100))),
        ("Davenport-Heilbronn D(s)", E.dh, E.dh, acb("0.8085", "85.6993"),
         (Fr(79, 100), Fr(83, 100), Fr(8568, 100), Fr(8572, 100)),
         (Fr(60, 100), Fr(70, 100), Fr(8568, 100), Fr(8572, 100))),
    ]
    for lab, f, ffloat, guess, box, ctrl in jobs:
        t0 = time.time()
        z = newton(ffloat, guess)
        w = winding_number(f, *box)
        wc = winding_number(f, *ctrl)
        rec = {"function": lab, "located_zero": [z.real.mid().str(20), z.imag.mid().str(20)],
               "box": w, "control_box": wc, "seconds": round(time.time() - t0, 1)}
        out["certificates"].append(rec)
        print(json.dumps(rec), flush=True)
    for c in out["checks"]:
        print(json.dumps(c))
    with open("certify_zeros_output.json", "w") as fh:
        json.dump(out, fh, indent=2)


if __name__ == "__main__":
    main()
