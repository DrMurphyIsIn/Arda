"""SOS-Positivstellensatz REFUTATION finder — upgrading the SOS-refutation
emitter from checker to searcher.

`find_sos_refutation` searches (numeric SDP over SOS σ blocks + FREE λ blocks ->
EXACT rational rounding) for a refutation `−1 = σ_0 + Σ σ_i·g_i + Σ λ_j·h_j` of
the ℝ-infeasibility of `{g_i ≥ 0} ∪ {h_j = 0}` — AUTOMATICALLY closing the
real-only gap the ideal refutation cannot reach (e.g. `x² + 1 = 0`).  The emitter
uses it whenever a family returns ``sigma0 = None``.  The finder is untrusted —
every result is re-verified EXACTLY by `certify_sos_refutation_point` before any
Lean is emitted — so these tests cover that it FINDS the refutation, re-verifies
exactly over Q, and REFUSES cleanly on a satisfiable system.  Skipped without
cvxpy.  (Shares the engine of `find_putinar_certificate`; see also
`test_putinar_finder.py`.)
"""
import sys
from pathlib import Path

import pytest
import sympy as sp

pytest.importorskip("cvxpy")

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

from telperion import (  # noqa: E402
    CertificationError, GridSpec, LeanProfile, SOSRefutationEmitter,
    ValidationReport, certify, check_lean_text, emit, sos_refutation_family,
)
from telperion.sos_sdp import find_sos_refutation  # noqa: E402

GREEN = ValidationReport(checks=(("spot", True),))


def _recon(sigma0, out_ineqs, out_eqs):
    """σ_0 + Σ σ_i·g_i + Σ λ_j·h_j from finder-shaped term lists."""
    def sos(terms):
        return sum((sp.nsimplify(c) * sp.sympify(b) ** 2 for c, b in terms),
                   sp.Integer(0))
    acc = sos(sigma0)
    for g, sigma_i, _hyp in out_ineqs:
        acc += sp.sympify(g) * sos(sigma_i)
    for h, lam, _hyp in out_eqs:
        acc += sp.sympify(h) * sp.sympify(lam)
    return sp.expand(acc)


def test_find_sos_refutation_closes_real_gap():
    # x^2 + 1 = 0 is R-infeasible only BY POSITIVITY (complex roots, so no ideal
    # refutation) — the finder must discover an SOS sigma0 (= x^2) and free lambda.
    x, y = sp.symbols("x y")
    r = find_sos_refutation([], [(x ** 2 + 1, "he1")], (x, y), half_deg=1)
    assert r is not None
    sigma0, out_ineqs, out_eqs = r
    assert _recon(sigma0, out_ineqs, out_eqs) == -1  # equals -1
    # every SOS coefficient a nonnegative rational
    for c, _b in sigma0:
        assert sp.nsimplify(c).is_rational and sp.nsimplify(c) >= 0


def test_find_sos_refutation_ineq_plus_eq():
    # {x >= 0, x + 1 = 0}: infeasible (x = -1 violates x >= 0) — a mixed
    # inequality/equality system the finder refutes.
    x = sp.Symbol("x")
    r = find_sos_refutation([(x, "hg1")], [(x + 1, "he1")], (x,), half_deg=1)
    assert r is not None
    sigma0, out_ineqs, out_eqs = r
    assert _recon(sigma0, out_ineqs, out_eqs) == -1


def test_find_sos_refutation_refuses_satisfiable():
    # x - y = 0 alone is satisfiable over R -> no refutation exists.
    x, y = sp.symbols("x y")
    assert find_sos_refutation([], [(x - y, "he1")], (x, y), half_deg=1) is None


def test_sos_refutation_finder_is_deterministic():
    x, y = sp.symbols("x y")
    a = find_sos_refutation([], [(x ** 2 + 1, "he1")], (x, y), half_deg=1)
    b = find_sos_refutation([], [(x ** 2 + 1, "he1")], (x, y), half_deg=1)
    assert a == b  # byte-stability of frozen output depends on this


def test_sos_refutation_finder_mode_certifies_and_emits():
    # spec returns sigma0=None with constraint-only ineqs/eqs -> Telperion finds
    # the refutation, certifies EXACTLY, then emits `... -> False`.
    x = sp.Symbol("x")

    def spec(pt):
        return (None, [], [(x ** 2 + 1, "he1")])

    fam = sos_refutation_family("SF", (x,), GridSpec([("j", [0])]),
                                lambda pt: "sf", spec)
    res = emit(certify(fam), LeanProfile(namespace=("T",)),
               [SOSRefutationEmitter()], GREEN)
    body = next(iter(res.files.values()))
    check_lean_text(body)
    assert res.n_theorems == 1 and "False" in body and "linarith" in body


def test_sos_refutation_finder_mode_refuses_when_satisfiable():
    x, y = sp.symbols("x y")

    def spec(pt):
        return (None, [], [(x - y, "he1")])

    fam = sos_refutation_family("B", (x, y), GridSpec([("j", [0])]),
                                lambda pt: "sf_none", spec)
    with pytest.raises(CertificationError):
        certify(fam)


def test_sos_refutation_finder_result_re_verifies_exactly():
    # The finder's own output must pass the EXISTING exact certifier unchanged
    # (the honesty contract: the finder is untrusted, the certifier is the gate).
    x = sp.Symbol("x")
    r = find_sos_refutation([], [(x ** 2 + 1, "he1")], (x,), half_deg=1)
    assert r is not None
    sigma0, out_ineqs, out_eqs = r

    from telperion.emit_sos_refutation import certify_sos_refutation_point
    from telperion.family import InequalityFamily

    def spec(pt):
        return (sigma0, out_ineqs, out_eqs)

    fam = InequalityFamily(
        name="V", symbols=(x,), grid=GridSpec([("j", [0])]),
        lean_name=lambda pt: "v", special=("sos_refutation", spec),
    )
    inst, checks = certify_sos_refutation_point(fam, {"j": 0}, "v")
    assert checks >= 1  # exact identity + per-coefficient checks all passed
