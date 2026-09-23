"""The Hecke orbit of i: which of its points are class-number-one CM points?

conjecture1_proved = False.  Exact integer computation (no floating point in the claims).

Claim checked here (correction to the submitted idea, which said the orbit is "i together with
class-number >= 2 CM points"):
  * A point (a i + b)/d of T_n(i) (ad = n, 0 <= b < d) is a CM point whose primitive form has
    discriminant -4 f^2 with f = n / gcd(d^2, 2bd, a^2 + b^2) ... computed exactly below.
  * h(-4 f^2) = 1 exactly for f in {1, 2}; for 3 <= f <= FMAX it is >= 2 (reduced-form count),
    matching the order class number formula h(-4f^2) = (f/2) prod_{p | f} (1 - chi_{-4}(p)/p)
    for f >= 2.
  * So the orbit contains exactly two class-number-one points up to SL2(Z): i (f = 1) and 2i
    (f = 2, 2i in T_2(i)); every other orbit point has class number >= 2.
Output: hecke_orbit_class_numbers_output.txt
"""
from __future__ import annotations

from fractions import Fraction
from math import gcd, isqrt

FMAX = 300
NMAX = 60


def class_number(D: int) -> int:
    """Number of reduced primitive positive definite forms (a, b, c), b^2 - 4ac = D < 0."""
    h = 0
    a = 1
    while 3 * a * a <= -D:
        for b in range(-a + 1, a + 1):
            if (b * b - D) % (4 * a):
                continue
            c = (b * b - D) // (4 * a)
            if c < a:
                continue
            if b < 0 and a == c:
                continue
            if gcd(gcd(a, abs(b)), c) != 1:
                continue
            h += 1
        a += 1
    return h


def chi_m4(p: int) -> int:
    return 0 if p % 2 == 0 else (1 if p % 4 == 1 else -1)


def formula(f: int) -> Fraction:
    val = Fraction(f, 2)
    n, p = f, 2
    while n > 1:
        if n % p == 0:
            val *= 1 - Fraction(chi_m4(p), p)
            while n % p == 0:
                n //= p
        p += 1
    return val


def orbit_point_conductor(a: int, b: int, d: int) -> int:
    """z = (a i + b)/d satisfies d^2 z^2 - 2bd z + (a^2 + b^2) = 0; primitive disc = -4 f^2."""
    A, B, C = d * d, -2 * b * d, a * a + b * b
    g = gcd(gcd(A, abs(B)), C)
    A, B, C = A // g, B // g, C // g
    D = B * B - 4 * A * C
    f2 = -D // 4
    f = isqrt(f2)
    assert f * f == f2 and D == -4 * f * f
    return f


def main():
    lines = []
    ones = []
    for f in range(1, FMAX + 1):
        h = class_number(-4 * f * f)
        if f >= 2:
            assert Fraction(h) == formula(f), (f, h, formula(f))
        if h == 1:
            ones.append(f)
    lines.append(f"class number h(-4 f^2) = 1 exactly for f in {ones} (checked for 1 <= f <= {FMAX}); "
                 f"the order formula (f/2) prod (1 - chi_-4(p)/p) matches the reduced-form count "
                 f"for every 2 <= f <= {FMAX}")
    lines.append("f : h(-4 f^2) for f <= 12: " +
                 ", ".join(f"{f}:{class_number(-4 * f * f)}" for f in range(1, 13)))
    seen_one = set()
    for n in range(1, NMAX + 1):
        for a in range(1, n + 1):
            if n % a:
                continue
            d = n // a
            for b in range(d):
                f = orbit_point_conductor(a, b, d)
                if class_number(-4 * f * f) == 1:
                    seen_one.add((n, a, b, d, f))
    firsts = sorted(seen_one)[:12]
    lines.append(f"orbit points (a i + b)/d in T_n(i), n <= {NMAX}, with class number one: "
                 f"{len(seen_one)} occurrences, conductors f = {sorted({x[4] for x in seen_one})}; "
                 f"first ones (n, a, b, d, f): {firsts}")
    lines.append("examples: 2i = (2 i + 0)/1 in T_2(i) has f = %d (disc -16, h = %d); "
                 "3i in T_3(i) has f = %d (h = %d); 4i in T_4(i) has f = %d (h = %d); "
                 "21i/20 in T_420(i) has f = %d (h = %d)" % (
                     orbit_point_conductor(2, 0, 1), class_number(-16),
                     orbit_point_conductor(3, 0, 1), class_number(-36),
                     orbit_point_conductor(4, 0, 1), class_number(-64),
                     orbit_point_conductor(21, 0, 20), class_number(-4 * 420 * 420)))
    out = "\n".join(lines)
    print(out)
    with open("hecke_orbit_class_numbers_output.txt", "w") as fh:
        fh.write(out + "\n")


if __name__ == "__main__":
    main()
