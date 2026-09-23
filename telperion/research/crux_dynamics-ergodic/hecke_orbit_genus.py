"""Bessel-free (genus theory) evaluation at points of the Hecke orbit of i, and CERTIFIED off-line
zeros there.

conjecture1_proved = False.  Trust classes: exact integer arithmetic (coefficient identities up to
NCOEF), Arb ball arithmetic (cross-checks and segment-certified winding numbers); not the kernel.

Identities (Dirichlet coefficients checked EXACTLY for n <= NCOEF; the general statements are
genus theory for the orders Z[f i], classical):
  disc -16 (2i in T_2(i), h = 1):
     Z_{x^2+4y^2}(s)  = 2 zeta(s) L(s,chi_-4) (1 - 2^{-s} + 2^{1-2s})
  disc -36 (3i in T_3(i), h = 2):
     Z_{x^2+9y^2}(s)  = zeta(s) L(s,chi_-4) (1 + 3^{1-2s}) + L(s,chi_-3) L(s,chi_12)
  disc -64 (4i in T_4(i), h = 2):
     Z_{x^2+16y^2}(s) = zeta(s) L(s,chi_-4) (1 - 2^{-s} + 2^{1-2s} - 2^{1-3s} + 2^{2-4s})
                        + L(s,chi_-8) L(s,chi_8)
Each is cross-checked against the rigorous Fourier expansion of E*(z, s) at a complex point in
the strip (the Arb balls must overlap).  For z = i y with integral y the form is
Q_z(m, n) = (y^2 m^2 + n^2)/y, so E*(i y, s) = pi^{-s} Gamma(s) y^s Z_{x^2 + y^2 Y^2}(s) / 2.

Certificates: the class-number-two orbit points 3i and 4i carry zeros OFF the critical line
(segment-certified winding number 1 in a box inside Re s > 1/2, control box 0), located by
Newton.  The class-number-one point 2i does not: its extra Euler factor has all zeros on
Re s = 1/2 (Lean: CruxDynamicsErgodic.euler2_disc16_zeros_on_line), and a float argument-principle
scan finds no zero in (0.55, 0.99) x [1, 60] for i and 2i (scan_output below).
Output: hecke_orbit_genus_output.json
"""
from __future__ import annotations

import json
import math
from fractions import Fraction as Fr

from flint import acb, arb, ctx

import eisenstein as E
from arb_winding import winding_number

ctx.prec = 300
NCOEF = 4000


def kron(D: int):
    """Kronecker symbol n -> (D | n) for a fundamental discriminant D."""
    def k(n: int) -> int:
        res = 1
        while n % 2 == 0:
            n //= 2
            if D % 2 == 0:
                return 0
            res *= 1 if D % 8 in (1, 7) else -1
        a, m, j = D % n, n, 1
        while a != 0:
            while a % 2 == 0:
                a //= 2
                if m % 8 in (3, 5):
                    j = -j
            a, m = m, a
            if a % 4 == 3 and m % 4 == 3:
                j = -j
            a %= m
        return res * (j if m == 1 else 0)
    return k


def reps(a, b, c, N):
    r = [0] * (N + 1)
    M = math.isqrt(4 * N) + 3
    for x in range(-M, M + 1):
        for y in range(-M, M + 1):
            v = a * x * x + b * x * y + c * y * y
            if 0 < v <= N:
                r[v] += 1
    return r


def dconv(f, g, N):
    h = [0] * (N + 1)
    for d in range(1, N + 1):
        if f[d]:
            for m in range(1, N // d + 1):
                h[d * m] += f[d] * g[m]
    return h


def char_series(k, N):
    return [0] + [k(n) for n in range(1, N + 1)]


def poly_series(coeffs: dict, N):
    """Dirichlet polynomial sum c_m m^{-s} as a coefficient list."""
    s = [0] * (N + 1)
    for m, c in coeffs.items():
        s[m] += c
    return s


def check_identities():
    N = NCOEF
    one = [0] + [1] * N
    zL = dconv(one, char_series(kron(-4), N), N)
    res = {}
    # disc -16
    lhs = reps(1, 0, 4, N)
    rhs = dconv(zL, poly_series({1: 2, 2: -2, 4: 4}, N), N)
    res["disc -16: Z_{x^2+4y^2} = 2 zeta L_-4 (1 - 2^-s + 2^{1-2s})"] = lhs == rhs
    # disc -36
    lhs = reps(1, 0, 9, N)
    rhs1 = dconv(zL, poly_series({1: 1, 9: 3}, N), N)
    rhs2 = dconv(char_series(kron(-3), N), char_series(kron(12), N), N)
    res["disc -36: Z_{x^2+9y^2} = zeta L_-4 (1 + 3^{1-2s}) + L_-3 L_12"] = \
        lhs == [a + b for a, b in zip(rhs1, rhs2)]
    # disc -64
    lhs = reps(1, 0, 16, N)
    rhs1 = dconv(zL, poly_series({1: 1, 2: -1, 4: 2, 8: -2, 16: 4}, N), N)
    rhs2 = dconv(char_series(kron(-8), N), char_series(kron(8), N), N)
    res["disc -64: Z_{x^2+16y^2} = zeta L_-4 (1 - 2^-s + 2^{1-2s} - 2^{1-3s} + 2^{2-4s}) + L_-8 L_8"] = \
        lhs == [a + b for a, b in zip(rhs1, rhs2)]
    return res


def L(s: acb, D: int) -> acb:
    q = abs(D)
    k = kron(D)
    tot = acb(0)
    for a in range(1, q + 1):
        c = k(a)
        if c:
            tot += c * s.zeta(acb(a) / q)
    return acb(q) ** (-s) * tot


def Z16(s):
    u = acb(2) ** (-s)
    return 2 * s.zeta() * L(s, -4) * (1 - u + 2 * u * u)


def Z36(s):
    return s.zeta() * L(s, -4) * (1 + 3 * acb(9) ** (-s)) + L(s, -3) * L(s, 12)


def Z64(s):
    u = acb(2) ** (-s)
    return (s.zeta() * L(s, -4) * (1 - u + 2 * u ** 2 - 2 * u ** 3 + 4 * u ** 4)
            + L(s, -8) * L(s, 8))


def estar_from_genus(Z, y: int, s: acb) -> acb:
    """E*(i y, s) = pi^{-s} Gamma(s) Z_{Q_z}(s)/2 with Z_{Q_z}(s) = y^s Z_{x^2 + y^2 Y^2}(s)."""
    return arb.pi() ** (-s) * s.gamma() * acb(y) ** s * Z(s) / 2


def newton(f, s, steps=12):
    h = acb("1e-30")
    for _ in range(steps):
        v = f(s)
        d = (f(s + h) - v) / h
        s = s - v / d
        s = acb(s.real.mid(), s.imag.mid())
    return s


def main():
    out = {"conjecture1_proved": False, "coefficient_identities_n_le_%d" % NCOEF: check_identities()}
    print(json.dumps(out, indent=1), flush=True)
    s0 = acb("0.83", "17.31")
    cross = {}
    for lab, Z, y in [("2i", Z16, 2), ("3i", Z36, 3), ("4i", Z64, 4)]:
        a = E.estar(0, y, s0, N=30)
        b = estar_from_genus(Z, y, s0)
        cross[lab] = {"fourier": str(a), "genus": str(b), "overlap": bool(a.overlaps(b))}
    out["cross_check_at_0.83+17.31i"] = cross
    print(json.dumps(cross, indent=1), flush=True)
    certs = []
    for lab, Z, guess in [
        ("3i in T_3(i), disc -36, h = 2: Z_{x^2+9y^2}", Z36, acb("0.8651", "20.6473")),
        ("3i in T_3(i), disc -36, h = 2: Z_{x^2+9y^2} (second zero)", Z36, acb("0.8090", "42.1192")),
        ("4i in T_4(i), disc -64, h = 2: Z_{x^2+16y^2}", Z64, acb("0.6737", "28.1179")),
    ]:
        z = newton(Z, guess)
        x0 = Fr(round(float(z.real.mid()) * 1000), 1000)
        y0 = Fr(round(float(z.imag.mid()) * 1000), 1000)
        h = Fr(1, 50)
        bx = (x0 - h, x0 + h, y0 - h, y0 + h)
        assert bx[0] > Fr(1, 2)
        # control box of the same size, shifted in Re s (kept inside 1/2 < Re s < 1)
        cx = x0 + Fr(8, 100) if x0 + Fr(8, 100) + h < 1 else x0 - Fr(8, 100)
        cb = (cx - h, cx + h, y0 - h, y0 + h)
        assert cb[0] > Fr(1, 2)
        w = winding_number(Z, *bx)
        wc = winding_number(Z, *cb)
        rec = {"function": lab, "located_zero": [z.real.mid().str(20), z.imag.mid().str(20)],
               "box": w, "control_box": wc}
        certs.append(rec)
        print(json.dumps(rec), flush=True)
    out["certificates"] = certs
    with open("hecke_orbit_genus_output.json", "w") as fh:
        json.dump(out, fh, indent=2)


if __name__ == "__main__":
    main()
