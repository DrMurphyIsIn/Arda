"""Strictness companion to homog_master_probe.py — exact strict-margin probe + Lean emission.

Establishes the STRICT half of the achievable homogeneous master bound:

    for all k >= 1 and achievable mu (mu=1 or 0<mu<=1/2),
        GS(k,mu) = T   <=>   (k,mu) = (1,1)     (the arm),
    equivalently  GS(k,mu) < T  for every achievable (k,mu) != (1,1).

Two independent slack sources:
  (1) On 0 < mu <= 1/2 (any k): each region cert has a POSITIVE interval minimum,
      so the cert polynomial P(mu) satisfies P(mu) >= eps > 0 (strict).  We certify
      P(mu) - eps >= 0 by the SAME nonneg-Bernstein construction as the <= certs
      (degree possibly +1..2), then 0 < eps <= P(mu).
  (2) On mu = 1 (k >= 2): the arm ratio is strictly < 1 (integer cert 64*16^11 <
      621*15^11 is already strict), so armGS(k+1) < armGS(k), hence armGS(k) < T
      for k >= 2.

Every eps and margin here is exact rational.  emit_strict_lean_file() produces the
kernel-checkable `HomogMasterStrict.lean`.  Companion to (does not replace)
homog_master_probe.py.  conjecture1_proved = False.
"""
from __future__ import annotations

import os
import sys

import sympy as sp

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import homog_master_probe as HM  # noqa: E402

R = sp.Rational
mu = HM.mu
x = HM.x

# The five cleared cert polynomials (identical to the <= certs' integrands).
POLY_A = sp.expand(HM.T - (R(7, 6) + mu / 2) ** 11)
POLY_B = sp.expand(HM.T * (1 + mu / 3) ** 11 - (R(7, 6) + mu / 2) ** 11 * HM.GAMMA)
POLY_C1 = POLY_B
POLY_C2 = sp.expand(HM.T * (1 + mu / 3) ** 22 - HM.base(2, mu) ** 11 * HM.GAMMA ** 2)
POLY_C3 = sp.expand(HM.T * (1 + mu / 3) ** 33 - (1 + mu) ** 11 * HM.GAMMA ** 3)

# Region, cleared poly, [a,b], strict eps (a simple rational strictly below the
# exact interval minimum), Bernstein degree cap.
STRICT_SPECS = [
    ("certA_strict", POLY_A, R(0), R(74, 240), R(1), 26),
    ("certB_strict", POLY_B, R(74, 240), R(1, 3), R(1), 26),
    ("certC1_strict", POLY_C1, R(1, 3), R(1, 2), R(1), 26),
    ("certC2_strict", POLY_C2, R(1, 3), R(1, 2), R(1), 40),
    ("certC3_strict", POLY_C3, R(1, 3), R(1, 2), R(1), 50),
]


def exact_interval_min(poly, a, b):
    """Exact minimum of `poly` on [a,b] (endpoints + interior critical points)."""
    dp = sp.diff(poly, mu)
    crit = [r for r in sp.Poly(dp, mu).real_roots() if a < r < b]
    pts = [a, b] + list(crit)
    return min((poly.subs(mu, pt) for pt in pts))


def find_strict_certs():
    """For each region, verify eps < interval-min exactly and find a nonneg-Bernstein
    cert for `poly - eps` on [a,b].  Returns list of dicts with the data."""
    out = []
    for name, poly, a, b, eps, nmax in STRICT_SPECS:
        mn = exact_interval_min(poly, a, b)
        assert eps < mn, f"{name}: eps {eps} !< interval min {mn}"
        res = HM.find_bernstein(sp.expand(poly - eps), a, b, n_max=nmax)
        assert res is not None, f"{name}: strict Bernstein not found"
        n, betas = res
        # exact re-verification of the Bernstein identity for poly-eps
        basis = [sp.binomial(n, i) * (mu - a) ** i * (b - mu) ** (n - i) / (b - a) ** n
                 for i in range(n + 1)]
        recon = sp.expand(sum(be * ba for be, ba in zip(betas, basis)))
        assert sp.expand(recon - (poly - eps)) == 0, f"{name}: Bernstein identity mismatch"
        deg = sp.Poly(poly, mu).degree()
        out.append({"name": name, "poly": poly, "a": a, "b": b, "eps": eps,
                    "n": n, "betas": betas, "deg": deg, "min": mn})
    return out


def emit_strict_bernstein_lean(name, poly, a, b, eps, n, betas, var="mu"):
    """Emit a kernel-checkable `0 < poly` on [a,b] from `poly = eps + Bernstein_sum`.

    Same skeleton as HM.emit_bernstein_lean, but the identity is
    `poly = eps + sum(nonneg terms)` and the final step is `0 < eps <= poly`."""
    a, b = R(a), R(b)
    xa = f"({var} - {HM._rat_lean(a)})"
    bx = f"({HM._rat_lean(b)} - {var})"
    p_s = str(sp.expand(poly)).replace("**", "^")
    haves, summands, tnames = [], [], []
    for i, beta in enumerate(betas):
        if beta == 0:
            continue
        coef = sp.binomial(n, i) / (b - a) ** n
        scalar = HM._rat_lean(R(beta) * R(coef))
        proof = f"(by norm_num : (0:ℝ) ≤ {scalar})"
        factors = [scalar]
        if i > 0:
            factors.append(f"{xa}^{i}")
            proof = f"mul_nonneg ({proof}) (pow_nonneg hxa {i})"
        if n - i > 0:
            factors.append(f"{bx}^{n - i}")
            proof = f"mul_nonneg ({proof}) (pow_nonneg hbx {n - i})"
        term = " * ".join(factors)
        haves.append(f"  have t{i} : (0:ℝ) ≤ {term} := {proof}")
        summands.append(term)
        tnames.append(f"t{i}")
    rhs = " + ".join(summands) if summands else "0"
    body = "\n".join(haves)
    eps_s = HM._rat_lean(eps)
    hb = "" if n <= 12 else f"set_option maxHeartbeats {max(400000, n * 30000)} in\n"
    # Sum the per-term nonneg facts (t_i) and the strict eps by linarith; the
    # Bernstein identity `poly = eps + sum(t_i-terms)` then gives 0 < poly.
    return (
        f"-- {name}: strict Bernstein-basis positivity (degree {n}, eps={eps}) on [{a}, {b}].\n"
        f"{hb}"
        f"theorem {name} : ∀ {var} : ℝ, {HM._rat_lean(a)} ≤ {var} → {var} ≤ {HM._rat_lean(b)}"
        f" → (0:ℝ) < ({p_s}) := by\n"
        f"  intro {var} hlo hhi\n"
        f"  have hxa : (0:ℝ) ≤ {xa} := by linarith\n"
        f"  have hbx : (0:ℝ) ≤ {bx} := by linarith\n"
        f"{body}\n"
        f"  have hid : (({p_s}) : ℝ) = {eps_s} + ({rhs}) := by ring\n"
        f"  rw [hid]; linarith\n"
    )


def emit_strict_lean_file():
    certs = find_strict_certs()
    parts = ["import Mathlib\n\nnamespace HomogMasterStrict\n"]
    for c in certs:
        parts.append(emit_strict_bernstein_lean(
            c["name"], c["poly"], c["a"], c["b"], c["eps"], c["n"], c["betas"]))
    parts.append("end HomogMasterStrict\n")
    return "\n".join(parts)


def strict_margin_checks():
    """Exact strict-margin sanity: every achievable (k,mu)!=(1,1) has GS < T, and
    GS(1,1)=T is the unique equality.  Fraction-exact."""
    # arm line: GS(1,1)=T, GS(k,1)<T strictly for k>=2
    assert HM.GS(1, 1) == HM.T
    for kk in range(2, 30):
        assert HM.GS(kk, 1) < HM.T, f"GS({kk},1) !< T"
    # achievable mu<=1/2: no (k,mu) reaches T (strict)
    for i in range(1, 121):
        m = R(i, 240)
        for kk in range(1, 45):
            assert HM.GS(kk, m) < HM.T, f"GS({kk},{m}) !< T"
    # unique equality is (1,1)
    assert HM.GS(1, 1) == HM.T
    return True


def run_all():
    ok = True
    certs = None
    try:
        certs = find_strict_certs()
        for c in certs:
            print(f"[OK]  {c['name']}: eps={c['eps']} < min~{float(c['min']):.4f}, "
                  f"Bernstein n={c['n']} (poly deg {c['deg']}, elev +{c['n'] - c['deg']})")
    except Exception as e:  # noqa: BLE001
        ok = False
        print(f"[FAIL] strict certs: {e}")
    try:
        strict_margin_checks()
        print("[OK]  strict-margin checks (arm tail + achievable region, exact)")
    except Exception as e:  # noqa: BLE001
        ok = False
        print(f"[FAIL] strict margins: {e}")
    # arm ratio strict integer cert
    lhs, rhs = 64 * 16 ** 11, 621 * 15 ** 11
    assert lhs < rhs
    print(f"[OK]  arm ratio strict cert: 64*16^11={lhs} < 621*15^11={rhs}")
    print("ALL STRICT ASSERTIONS PASSED" if ok else "SOME STRICT ASSERTIONS FAILED")
    return ok, certs


if __name__ == "__main__":
    import sys
    ok, _ = run_all()
    sys.exit(0 if ok else 1)
