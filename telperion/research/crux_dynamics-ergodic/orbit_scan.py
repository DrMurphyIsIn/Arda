"""Float argument-principle scan for zeros of E*(z, .) in (0.55, 0.99) x [1, TMAX] at points of the
Hecke orbit of i (and the class-number-one controls i, 2i).

conjecture1_proved = False.  Trust class: FLOATING POINT (Arb midpoints at 400 bits, every value's
ball radius checked to be < 1e-6 of its modulus), adaptive phase tracking with an initial mesh of
0.04; NOT a certificate.  Certified zeros are in hecke_orbit_genus.py and certify_zeros.py.

Output: orbit_scan_output.txt (cells [t, t+1] whose boundary winding is nonzero).
"""
from __future__ import annotations

import cmath
import math
import sys
from fractions import Fraction as Fr

from flint import acb, arb, ctx

import eisenstein as E

ctx.prec = 400
BAD = [0]


def val(x, y, a, b):
    v = E.estar(x, y, acb(repr(a), repr(b)), N=25, rigorous=False)
    if not (v.rad() < v.abs_lower() * arb("1e-6")):
        BAD[0] += 1
    return complex(float(v.real.mid()), float(v.imag.mid()))


def seg(x, y, p, q, vp, vq, depth=0):
    d = cmath.phase(vq / vp)
    if abs(d) < math.pi / 6 or depth > 14:
        return d
    m = ((p[0] + q[0]) / 2, (p[1] + q[1]) / 2)
    vm = val(x, y, *m)
    return seg(x, y, p, m, vp, vm, depth + 1) + seg(x, y, m, q, vm, vq, depth + 1)


def winding(x, y, a0, a1, b0, b1, h=0.04):
    c = [(a0, b0), (a1, b0), (a1, b1), (a0, b1), (a0, b0)]
    tot = 0.0
    for p, q in zip(c, c[1:]):
        k = max(1, int(math.ceil(math.hypot(q[0] - p[0], q[1] - p[1]) / h)))
        pts = [(p[0] + (q[0] - p[0]) * j / k, p[1] + (q[1] - p[1]) * j / k) for j in range(k + 1)]
        vals = [val(x, y, *pt) for pt in pts]
        for j in range(k):
            tot += seg(x, y, pts[j], pts[j + 1], vals[j], vals[j + 1])
    return tot / (2 * math.pi)


def main():
    TMAX = float(sys.argv[1]) if len(sys.argv) > 1 else 60.0
    lines = []
    for (x, y, lab) in [(Fr(0), Fr(1), "i (disc -4, h = 1)"), (Fr(0), Fr(2), "2i in T_2(i) (disc -16, h = 1)"),
                        (Fr(0), Fr(3), "3i in T_3(i) (disc -36, h = 2)"),
                        (Fr(0), Fr(4), "4i in T_4(i) (disc -64, h = 2)"),
                        (Fr(0), Fr(21, 20), "21i/20 in T_420(i) (disc -4*420^2, h = 256)")]:
        found = []
        b = 1.0
        while b < TMAX:
            w = winding(x, y, 0.55, 0.99, b, b + 1.0)
            if abs(w) > 0.5:
                found.append((b, round(w, 3)))
            b += 1.0
        line = (f"{lab}: cells [t, t+1] in (0.55, 0.99) x [1, {TMAX:g}] with nonzero winding: {found}; "
                f"imprecise evaluations: {BAD[0]}")
        BAD[0] = 0
        print(line, flush=True)
        lines.append(line)
    with open("orbit_scan_output.txt", "w") as fh:
        fh.write("\n".join(lines) + "\n")


if __name__ == "__main__":
    main()
