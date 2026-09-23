"""preordering_multiplier emitter -- positivity on a semialgebraic set with POLYNOMIAL generators,
by a positive multiplier and an exact constant-coefficient preordering identity.

The shape (SHAPES_AUDIT_48H_2026-09-22.md section 2 rank 3; SHAPES_AUDIT_D_LI_FACE section 3.1):
`M p = sum c_alpha prod g_i^alpha_i` with `c_alpha >= 0` and `M = kappa g_j^e`, checked by `ring`,
folded by `positivity`, the zero locus of a non-constant `M` pinned to one point by
`nlinarith only` and closed there by `norm_num`.

Acceptance is pinned on the dogfood family (the Li box rungs of
`examples/li_positivity/lean/LiBoxRungs.lean`): the targets and the three hand certificates are
compared against the island source, the LP finder is shown to re-find them, and every refusal the
audit lists has its own test.  The Lean kernel is the arbiter: the dogfood probe
`examples/li_positivity/lean/Probes/Dogfood_preordering_multiplier.lean` is pinned byte-for-byte to
the generator here and compiled on the island (opt-in kernel test at the bottom:
`TELPERION_PM_KERNEL=1`, run it under the machine's Lean slot lock).

conjecture1_proved = False.
"""
import importlib.util
import os
import re
import sys
from fractions import Fraction
from pathlib import Path

import pytest
import sympy as sp

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))
sys.path.insert(0, str(Path(__file__).resolve().parent))

import telperion  # noqa: E402,F401  (loads every Emitter subclass + adapter)
from telperion import (  # noqa: E402
    ComplexFace,
    GridSpec,
    LeanProfile,
    LocusCertificate,
    PreorderingGenerator as Generator,
    PreorderingMultiplierEmitter,
    PreorderingObstruction,
    PreorderingRefusal,
    ValidationReport,
    certify,
    chebyshev_pair_polynomial,
    derive_locus,
    emit,
    find_preordering_terms,
    li_box_rung_target,
    li_disk_generators,
    locate_negative_witness,
    obstruction_refutation_lean,
    preordering_multiplier_certificate,
    preordering_multiplier_family,
    solve_nonneg_exact,
)
from telperion.certify import emitter_for  # noqa: E402
from telperion.emit_preordering_multiplier import (  # noqa: E402
    HYP,
    MAX_MULTIPLIER_POWER,
    positivity_closable,
)
from telperion.lean_lint import lint_lean_text  # noqa: E402
from telperion.verdict import Verdict  # noqa: E402
from lean_env import lean_env_ready  # noqa: E402

_ROOT = Path(__file__).resolve().parents[1]
_LI = _ROOT / "examples" / "li_positivity" / "lean"
_RUNGS = _LI / "LiBoxRungs.lean"
_DOGFOOD_GEN = _ROOT / "examples" / "li_positivity" / "dogfood_preordering_multiplier.py"
_DOGFOOD_LEAN = _LI / "Probes" / "Dogfood_preordering_multiplier.lean"

x, y = sp.symbols("x y")
GENS = li_disk_generators(x, y)
LOC0 = LocusCertificate((("x", 0), ("y", 0)), (1, 1))


def _load_generator():
    spec = importlib.util.spec_from_file_location("dogfood_preordering_multiplier", _DOGFOOD_GEN)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


GEN = _load_generator()


def _cert(N, **kw):
    kw.setdefault("symbols", (x, y))
    kw.setdefault("target", li_box_rung_target(N, x, y))
    kw.setdefault("generators", GENS)
    return preordering_multiplier_certificate(**kw)


def _hand(N, **kw):
    mult, _text = GEN.HAND_CERTIFICATES[N]
    kw.setdefault("multiplier", mult)
    kw.setdefault("terms", GEN.hand_terms(N))
    if mult[1] is not None:
        kw.setdefault("locus", LOC0)
    return _cert(N, **kw)


def _fam(spec, name="t_inst", fam_name="PreorderingTest"):
    return preordering_multiplier_family(fam_name, (x, y), GridSpec([("i", [0])]),
                                         lambda pt: name, spec=lambda pt: dict(spec))


def _emit_text(spec, name="t_inst"):
    report = emit(
        certify(_fam(spec, name)),
        LeanProfile(namespace=("PreorderingTest",), imports=("Mathlib",)),
        [PreorderingMultiplierEmitter()],
        ValidationReport(checks=(("preordering_multiplier", True),)),
    )
    return next(iter(report.files.values()))


def _island_text():
    return _RUNGS.read_text(encoding="utf-8")


def _squash(s):
    return re.sub(r"\s+", "", s)


def _lean_poly(text, names):
    """A Lean polynomial over `z.re`/`z.im` (or aliases) as sympy."""
    t = text.replace("z.re", "x").replace("z.im", "y").replace("^", "**")
    return sp.expand(sp.sympify(t, locals={n: sp.Symbol(n) for n in names}))


# --- registry wiring --------------------------------------------------------

def test_kind_is_preordering_multiplier():
    assert _fam(dict(target=x, generators=GENS)).kind == "preordering_multiplier"


def test_emitter_for_round_trips():
    assert emitter_for("preordering_multiplier").kind == "preordering_multiplier"


def test_emitter_is_classified_sensitive_wired_with_an_adapter():
    from telperion.emitter_sensitivity import (
        CERTIFICATE_SENSITIVE, NEG_CONTROL_ADAPTER, REGISTRY, wired_sensitive_emitters)
    from telperion.negative_control_harness import ADAPTERS
    stance = REGISTRY["PreorderingMultiplierEmitter"]
    assert stance.stance == CERTIFICATE_SENSITIVE and stance.reason.strip()
    assert stance.checked_in == "emit_preordering_multiplier"
    assert "PreorderingMultiplierEmitter" in wired_sensitive_emitters()
    assert stance.neg_control is not None and stance.neg_control.kind == NEG_CONTROL_ADAPTER
    assert "PreorderingMultiplierEmitter" in ADAPTERS


# --- the dogfood data is the island's -----------------------------------------

@pytest.mark.parametrize("N", [1, 2, 3, 4, 5])
def test_chebyshev_pair_polynomial_matches_the_island_definitions(N):
    m = re.search(rf"noncomputable def Q{N} \(z : ℂ\) : ℂ := (.+)", _island_text())
    assert m, f"LiBoxRungs.lean lacks Q{N}"
    z = sp.Symbol("z")
    island = sp.expand(sp.sympify(m.group(1).replace("^", "**"), locals={"z": z}))
    assert sp.expand(chebyshev_pair_polynomial(N, z) - island) == 0


def test_chebyshev_pair_polynomial_recurrence_and_refusals():
    z = sp.Symbol("z")
    # the INHOMOGENEOUS Q recurrence of SHAPES_AUDIT_D section 2.6: Q_{N+1} = (2 - z) Q_N - Q_{N-1} + 2 z
    for N in range(2, 9):
        lhs = chebyshev_pair_polynomial(N + 1, z)
        rhs = (2 - z) * chebyshev_pair_polynomial(N, z) - chebyshev_pair_polynomial(N - 1, z) + 2 * z
        assert sp.expand(lhs - rhs) == 0
    for bad in (0, -1, True, 2.0):
        with pytest.raises(ValueError, match="REFUSED"):
            chebyshev_pair_polynomial(bad, z)


@pytest.mark.parametrize("N", [3, 4, 5])
def test_li_box_rung_target_matches_the_island_hre(N):
    m = re.search(rf"have hre : \(Q{N} z\)\.re\s*= (.+?) := by", _island_text(), re.S)
    assert m, f"LiBoxRungs.lean lacks the hre of Q{N}"
    assert sp.expand(li_box_rung_target(N, x, y) - _lean_poly(m.group(1), ["x", "y"])) == 0


@pytest.mark.parametrize("N", [3, 4, 5])
def test_hand_certificates_are_verbatim_island_text(N):
    """The dogfood's transcription of each `key` right-hand side IS the island's text."""
    _mult, text = GEN.HAND_CERTIFICATES[N]
    assert _squash(text) in _squash(_island_text())


def test_li_disk_generators_are_the_hand_aliases():
    d, B, s = GENS
    assert (d.name, d.tag, d.hyp_name) == ("d", HYP, "hz")
    assert sp.expand(d.expr - (x - x ** 2 - y ** 2)) == 0
    assert (B.name, s.name) == ("B", "s")


# --- acceptance: the supplied hand certificates --------------------------------

def test_hand_q3_certificate_is_accepted():
    cert = _hand(3)
    assert cert.trivial_multiplier and cert.mult_coeff == 1 and cert.locus is None
    assert len(cert.terms) == 8 and cert.identity_residual == 0
    assert cert.found_by == "supplied"
    assert cert.identity_degree == 3


def test_hand_q4_certificate_is_accepted_with_the_14s_multiplier():
    cert = _hand(4)
    assert (cert.mult_coeff, cert.generators[cert.mult_index].name, cert.mult_power) == (14, "s", 1)
    assert len(cert.terms) == 14 and cert.identity_residual == 0
    assert cert.locus == LocusCertificate((("x", 0), ("y", 0)), (1, 1))
    assert cert.identity_degree == 6


def test_hand_q5_certificate_is_accepted_with_the_s2_multiplier():
    cert = _hand(5)
    assert (cert.mult_coeff, cert.mult_power) == (1, 2) and len(cert.terms) == 18
    assert cert.identity_degree == 9


def test_locus_auto_derivation_matches_the_hand_locus():
    assert _hand(4, locus="auto").locus == _hand(4).locus
    assert derive_locus(x ** 2 + y ** 2, (x, y)) == LOC0
    got = derive_locus(2 * (x - 1) ** 2 + 3 * (y + sp.Rational(1, 2)) ** 2, (x, y))
    assert got.point == (("x", 1), ("y", sp.Rational(-1, 2))) and got.weights == (2, 3)
    # not a single point: a line, a circle, a negative weight, a cross term
    for g in (y ** 2, x - x ** 2 - y ** 2, x ** 2 - y ** 2, x ** 2 + x * y + y ** 2, x ** 4 + y ** 2):
        assert derive_locus(g, (x, y)) is None


def test_generator_symbols_match_by_name_and_strings_parse():
    xr, yr = sp.symbols("x y", real=True)
    cert = _cert(3, symbols=("x", "y"), target=str(li_box_rung_target(3, x, y)),
                 generators=li_disk_generators(xr, yr), terms=GEN.hand_terms(3),
                 multiplier=(1, None, 0))
    assert cert.identity_residual == 0


# --- acceptance: the LP finder -------------------------------------------------

def test_finder_refinds_the_hand_q3_certificate_exactly():
    found = _cert(3)
    hand = _hand(3)
    assert found.found_by == "lp (product degree <= 3)"
    assert sorted(found.terms) == sorted(hand.terms)


def test_finder_q1_q2_certificates():
    q1 = _cert(1)
    assert {a: c for c, a in q1.terms} == {(1, 0, 0): 1, (0, 0, 1): 1}          # d + s
    q2 = _cert(2)
    assert {a: c for c, a in q2.terms} == {(1, 0, 0): 4, (0, 1, 0): 2, (0, 0, 1): 3}


def test_finder_auto_candidates_choose_s_for_q4_and_s2_for_q5():
    q4 = _cert(4, multiplier_candidates="auto", max_total_degree=5)
    assert (q4.generators[q4.mult_index].name, q4.mult_power, q4.mult_coeff) == ("s", 1, 1)
    assert q4.found_by == "lp (product degree <= 4)" and q4.locus == LOC0
    assert all(c.q == 1 for c, _a in q4.terms), "the LP vertex for Q_4 is integral"
    q5 = _cert(5, multiplier_candidates="auto", max_total_degree=5)
    assert (q5.generators[q5.mult_index].name, q5.mult_power) == ("s", 2)
    assert q5.found_by == "lp (product degree <= 5)"


def test_finder_with_the_hand_multiplier_14s():
    q4 = _cert(4, multiplier=(14, "s", 1), locus="auto")
    assert q4.mult_coeff == 14 and q4.identity_residual == 0


def test_the_multipliers_are_genuinely_needed():
    """M = 1 is LP-infeasible for Q_4 and Q_5 (and M = s for Q_5) at every degree <= 5."""
    for N, mult in ((4, None), (5, None), (5, (1, "s", 1))):
        kw = dict(max_total_degree=5)
        if mult is not None:
            kw.update(multiplier=mult, locus="auto")
        with pytest.raises(PreorderingRefusal, match="no certificate up to the cap"):
            _cert(N, **kw)


def test_solve_nonneg_exact_small_cases():
    F = Fraction
    assert solve_nonneg_exact([[F(1), F(1)]], [F(2)]) is not None
    assert solve_nonneg_exact([[F(1), F(1)]], [F(-1)]) is None          # c >= 0 cannot sum to -1
    sol = solve_nonneg_exact([[F(1), F(0)], [F(0), F(2)]], [F(3), F(4)])
    assert sol == [F(3), F(2)]
    assert solve_nonneg_exact([], []) == []


def test_find_preordering_terms_is_exact_and_untrusted_output_reconstructs():
    gx = [g.expr for g in GENS]
    terms = find_preordering_terms(li_box_rung_target(2, x, y), gx, (x, y), 1)
    recon = sum(c * sp.prod([g ** a for g, a in zip(gx, al)]) for c, al in terms)
    assert sp.expand(recon - li_box_rung_target(2, x, y)) == 0
    assert find_preordering_terms(-x, gx, (x, y), 3) is None           # -x is not in the cone


# --- refusals: the audit's phantom list ------------------------------------------

def test_refuse_q6_obstructed_and_located_with_the_exact_witness():
    with pytest.raises(PreorderingObstruction, match="OBSTRUCTED_AND_LOCATED") as ei:
        _cert(6, multiplier_candidates="auto", scan_box=GEN.SCAN_BOX, scan_steps=GEN.SCAN_STEPS)
    obs = ei.value
    assert obs.witness == {"x": sp.Rational(4, 5), "y": sp.Rational(-2, 5)}
    assert obs.value == sp.Rational(-27772, 15625)
    # the witness is EXACT: in the (closed) disk, and p really is that negative number there
    wx, wy = obs.witness["x"], obs.witness["y"]
    assert wx ** 2 + wy ** 2 <= wx
    assert li_box_rung_target(6, x, y).subs({x: wx, y: wy}) == obs.value
    assert obs.verdict.verdict == Verdict.OBSTRUCTED_AND_LOCATED
    assert "-27772/15625" in obs.verdict.obstruction
    assert isinstance(obs, ValueError)                                  # certify() records it


def test_q6_is_also_refused_without_a_scan_but_not_as_a_verdict():
    with pytest.raises(PreorderingRefusal, match="NOT a verdict on the claim") as ei:
        _cert(6, multiplier_candidates="auto", max_total_degree=4)
    assert not isinstance(ei.value, PreorderingObstruction)


def test_scan_finds_no_witness_for_true_rungs():
    gx = [g.expr for g in GENS]
    for N in (1, 2, 3, 4, 5):
        assert locate_negative_witness(li_box_rung_target(N, x, y), gx, (x, y),
                                       GEN.SCAN_BOX, steps=30) is None


def test_refuse_negative_coefficient_even_with_an_exact_identity():
    terms = [(1, (1, 0, 0)), (-1, (0, 1, 0))]                          # p = d - B, exact
    with pytest.raises(PreorderingRefusal, match="NEGATIVE coefficient"):
        _cert(3, target=x - x ** 2 - 2 * y ** 2, terms=terms, multiplier=(1, None, 0))


def test_refuse_identity_that_does_not_reconstruct():
    terms = [(c + 1 if a == (0, 1, 0) else c, a) for c, a in GEN.hand_terms(3)]   # 15 B -> 16 B
    with pytest.raises(PreorderingRefusal, match="does NOT reconstruct"):
        _cert(3, terms=terms, multiplier=(1, None, 0))


def test_refuse_hyp_generator_without_a_binder():
    d = Generator("d", x - x ** 2 - y ** 2, "hyp")
    with pytest.raises(PreorderingRefusal, match="not literally a hypothesis"):
        _cert(3, generators=(d,) + GENS[1:])


def test_refuse_hyp_generator_whose_stated_form_is_not_the_generator():
    d = Generator("d", x - x ** 2 - y ** 2, "hyp", "hz", (x ** 2 + y ** 2, 2 * x))
    with pytest.raises(PreorderingRefusal, match="does not say what the certificate uses"):
        _cert(3, generators=(d,) + GENS[1:])


@pytest.mark.parametrize("g", [x - x ** 2 - y ** 2, x, x * y, x ** 2 - 2 * x * y + y ** 2])
def test_refuse_structural_generator_positivity_cannot_close(g):
    assert not positivity_closable(g, (x, y))
    with pytest.raises(PreorderingRefusal, match="positivity` cannot close"):
        _cert(3, generators=(GENS[0], Generator("B", g), GENS[2]))


def test_positivity_closable_accepts_the_even_forms():
    for g in (x ** 2 + y ** 2, y ** 2, sp.Rational(3, 4), x ** 2 * y ** 4, 2 * x ** 4 + 3 * y ** 2):
        assert positivity_closable(g, (x, y))


def test_refuse_structural_generator_carrying_a_binder_or_stated_form():
    with pytest.raises(PreorderingRefusal, match="carries a hypothesis binder"):
        _cert(3, generators=(GENS[0], Generator("B", y ** 2, "structural", "hB"), GENS[2]))
    with pytest.raises(PreorderingRefusal, match="carries a `stated` form"):
        _cert(3, generators=(GENS[0], Generator("B", y ** 2, "structural", "", (0, y ** 2)),
                             GENS[2]))


def test_refuse_multiplier_with_an_uncertified_zero_locus():
    with pytest.raises(PreorderingRefusal, match="uncertified multiplier zero locus"):
        _hand(4, locus=None)
    wrong_point = LocusCertificate((("x", 1), ("y", 0)), (1, 1))
    with pytest.raises(PreorderingRefusal, match="NOT the single supplied point"):
        _hand(4, locus=wrong_point)
    with pytest.raises(PreorderingRefusal, match="must all be positive"):
        _hand(4, locus=LocusCertificate((("x", 0), ("y", 0)), (1, 0)))
    with pytest.raises(PreorderingRefusal, match="do not match the base variables"):
        _hand(4, locus=LocusCertificate((("x", 0),), (1,)))


def test_refuse_multiplier_whose_zero_set_is_not_a_point():
    # M = d vanishes on the whole boundary circle: the identity d * x = d^2 + d s HOLDS, but no
    # single-point locus certificate exists, so the instance is refused at the locus
    with pytest.raises(PreorderingRefusal, match="not a single point"):
        _cert(1, multiplier=(1, "d", 1), locus="auto", max_total_degree=2)


def test_refuse_multiplier_not_in_the_cone():
    for mult, msg in (((0, None, 0), "not positive"), ((-14, "s", 1), "not positive"),
                      ((1, "q", 1), "not one of the declared generators"),
                      ((1, "s", MAX_MULTIPLIER_POWER + 1), "outside 1.."),
                      ((1, "s", 0), "outside 1.."),
                      ((1, None, 2), "must have power 0"),
                      ((1, "s"), "products of several generators"),
                      ((1, "s", 1.0), "not an int")):
        with pytest.raises(PreorderingRefusal, match=msg):
            _cert(4, multiplier=mult, locus="auto")


def test_refuse_locus_point_where_p_is_negative_outside_the_set():
    gens = (Generator("s", x ** 2 + y ** 2),
            Generator("h", x ** 2 + y ** 2 - 1, "hyp", "hout", (1, x ** 2 + y ** 2)))
    with pytest.raises(PreorderingRefusal, match="lies outside the set"):
        preordering_multiplier_certificate(
            symbols=(x, y), target=x ** 2 + y ** 2 - 1, generators=gens,
            multiplier=(1, "s", 1), terms=[(1, (1, 1))], locus="auto")


def test_refuse_locus_point_where_p_is_negative_inside_the_set_as_located():
    # the set {x^2 + y^2 <= 0} is the single point 0, where p = -1 - x^2 - y^2 = -1 < 0; the
    # identity s * p = h + s h holds, so only the locus branch can see the claim is false
    gens = (Generator("s", x ** 2 + y ** 2),
            Generator("h", -x ** 2 - y ** 2, "hyp", "hpt", (x ** 2 + y ** 2, 0)))
    with pytest.raises(PreorderingObstruction, match="OBSTRUCTED_AND_LOCATED") as ei:
        preordering_multiplier_certificate(
            symbols=(x, y), target=-1 - x ** 2 - y ** 2, generators=gens,
            multiplier=(1, "s", 1), terms=[(1, (0, 1)), (1, (1, 1))], locus="auto")
    assert ei.value.witness == {"x": 0, "y": 0} and ei.value.value == -1


def test_refuse_identity_above_the_degree_cap():
    with pytest.raises(PreorderingRefusal, match="past the cost cliff"):
        _hand(5, max_identity_degree=8)


def test_refuse_floats_everywhere():
    with pytest.raises(PreorderingRefusal, match="float"):
        _cert(3, target=0.5 * x)
    with pytest.raises(PreorderingRefusal, match="float"):
        _cert(4, multiplier=(14.0, "s", 1), locus="auto")
    with pytest.raises(PreorderingRefusal, match="float"):
        _cert(3, multiplier=(1, None, 0), terms=[(15.0, (0, 1, 0))] + GEN.hand_terms(3)[1:])
    with pytest.raises(PreorderingRefusal, match="float"):
        _hand(4, locus=LocusCertificate((("x", 0.0), ("y", 0)), (1, 1)))
    with pytest.raises(PreorderingRefusal, match="float"):
        locate_negative_witness(x, [x], (x,), {"x": (0.0, 1)})


@pytest.mark.parametrize("bad", [sp.exp(x), 1 / x, sp.sqrt(2) * x, sp.I * x, sp.Symbol("w") * x])
def test_refuse_non_polynomial_or_non_rational_targets(bad):
    with pytest.raises(PreorderingRefusal, match="REFUSED"):
        _cert(3, target=bad)


def test_refuse_constant_and_zero_targets():
    for t in (0, 3, sp.Rational(1, 2)):
        with pytest.raises(PreorderingRefusal, match="constant"):
            _cert(3, target=t)


def test_refuse_generator_list_defects():
    with pytest.raises(PreorderingRefusal, match="no generators"):
        _cert(3, generators=())
    with pytest.raises(PreorderingRefusal, match="duplicate generator aliases"):
        _cert(3, generators=(GENS[0], Generator("d", y ** 2), GENS[2]))
    with pytest.raises(PreorderingRefusal, match="identically zero"):
        _cert(3, generators=GENS + (Generator("z0", 0),))
    with pytest.raises(PreorderingRefusal, match="unknown tag"):
        _cert(3, generators=GENS + (Generator("q", y ** 2, "maybe"),))
    with pytest.raises(PreorderingRefusal, match="exceeds the cap"):
        _cert(3, generators=tuple(Generator(f"g{i}", y ** 2) for i in range(9)))
    with pytest.raises(PreorderingRefusal, match="duplicate hypothesis binder"):
        _cert(3, generators=GENS + (Generator("e", x, "hyp", "hz"),))


@pytest.mark.parametrize("names, gens, msg", [
    (("x", "x"), GENS, "duplicate base variable"),
    (("key", "y"), None, "collide with names the emitted proof binds"),
    (("hlocy", "y"), None, "collide with names the emitted proof binds"),
    (("sq_nonneg", "y"), None, "reserved name"),
    (("x", "y"), (Generator("P", x - x ** 2 - y ** 2, "hyp", "hz", None),), "collide"),
    (("x", "y"), (Generator("d", x - x ** 2 - y ** 2, "hyp", "hd0", None),), "collide"),
    (("x", "y"), (Generator("x", y ** 2),), "collides with a base variable"),
    (("x", "y"), (Generator("d", x - x ** 2 - y ** 2, "hyp", "d", None),), "collides"),
    (("x", "y"), (Generator("1d", y ** 2),), "not a plain ASCII Lean identifier"),
])
def test_refuse_name_collisions(names, gens, msg):
    syms = tuple(sp.Symbol(n) for n in names)
    if gens is None:
        gens = li_disk_generators(syms[0], syms[1])
    target = li_box_rung_target(3, syms[0], syms[1]) if len(set(names)) == 2 else x
    with pytest.raises(PreorderingRefusal, match=msg):
        preordering_multiplier_certificate(symbols=syms, target=target, generators=gens)


def test_refuse_term_list_defects():
    base = GEN.hand_terms(3)
    for terms, msg in (([], "empty certificate"),
                       ([(0, (1, 0, 0))], "every certificate coefficient is zero"),
                       ([(1, (1, 0))], "does not match 3 generators"),
                       ([(1, (1, 0, -1))], "nonnegative ints"),
                       ([(1, (True, 0, 0))], "nonnegative ints"),
                       ([(1, (1, 0, 0)), (2, (1, 0, 0))], "appears twice"),
                       ([(1, (1, 0, 0), 3)], "not a (coef, alpha) pair"),
                       ([("x", (1, 0, 0))] + base, "not rational")):
        with pytest.raises(PreorderingRefusal, match=re.escape(msg) if "(" in msg else msg):
            _cert(3, terms=terms, multiplier=(1, None, 0))


def test_malformed_inputs_are_refusals_not_crashes():
    # a negative coefficient on a malformed exponent vector: the vector is refused first
    with pytest.raises(PreorderingRefusal, match="does not match 3 generators"):
        _cert(3, terms=[(-1, 5)], multiplier=(1, None, 0))
    for bad in (LocusCertificate(((0, 0),), (1, 1)), LocusCertificate(5, (1, 1)),
                LocusCertificate((("x", 0), ("y", 0)), 7)):
        with pytest.raises(PreorderingRefusal, match="REFUSED"):
            _hand(4, locus=bad)


def test_candidate_list_with_a_conditional_locus_accepts_the_constant():
    """A locus supplied alongside a candidate list is used only if a non-constant multiplier
    wins; when the constant wins (Q_3) it is simply not needed."""
    cert = _cert(3, multiplier_candidates=[(1, None, 0), (1, "s", 1)], locus=LOC0)
    assert cert.trivial_multiplier and cert.locus is None


def test_refuse_mode_and_argument_misuse():
    with pytest.raises(PreorderingRefusal, match="not both"):
        _cert(4, multiplier=(1, "s", 1), multiplier_candidates="auto")
    with pytest.raises(PreorderingRefusal, match="ONE multiplier"):
        _cert(3, terms=GEN.hand_terms(3), multiplier_candidates=[(1, None, 0), (1, "s", 1)])
    with pytest.raises(PreorderingRefusal, match="max_total_degree"):
        _cert(3, max_total_degree=99)
    with pytest.raises(PreorderingRefusal, match="locus must be"):
        _hand(4, locus="guess")
    with pytest.raises(PreorderingRefusal, match="drop the locus"):
        _hand(3, locus=LOC0)
    with pytest.raises(PreorderingRefusal, match="needs `target` and `generators`"):
        certify_point_spec({"target": x})
    with pytest.raises(PreorderingRefusal, match="unknown spec keys"):
        certify_point_spec({"target": x, "generators": GENS, "mode": "fast"})


def certify_point_spec(spec):
    from telperion.emit_preordering_multiplier import certify_preordering_multiplier_point
    return certify_preordering_multiplier_point(_fam(spec), {"i": 0}, "t")


def test_refuse_scan_box_defects():
    gx = [g.expr for g in GENS]
    p = li_box_rung_target(6, x, y)
    for box, msg in (({"x": (0, 1)}, "do not match"), ({"x": (1, 0), "y": (0, 1)}, "inverted"),
                     ({"x": (0, 1, 2), "y": (0, 1)}, "(lo, hi) pair")):
        with pytest.raises(PreorderingRefusal, match=re.escape(msg)):
            locate_negative_witness(p, gx, (x, y), box)
    with pytest.raises(PreorderingRefusal, match="exceeds the cap"):
        locate_negative_witness(p, gx, (x, y), GEN.SCAN_BOX, steps=1000)
    with pytest.raises(PreorderingRefusal, match="positive int"):
        locate_negative_witness(p, gx, (x, y), GEN.SCAN_BOX, steps=0)


def _face(**kw):
    base = dict(var="z", target="LowHeightBox.Q3 z", coords=(("x", "z.re"), ("y", "z.im")),
                unfold=("LowHeightBox.Q3", "Complex.sub_re"))
    base.update(kw)
    return ComplexFace(**base)


@pytest.mark.parametrize("kw, msg", [
    (dict(coords=(("x", "z.re"),)), "exactly once"),
    (dict(coords=(("x", "z.re"), ("y", "z.re"))), "used twice"),
    (dict(coords=(("x", "z.re"), ("y", "w.im"))), "only"),
    (dict(unfold=()), "unfold list is empty"),
    (dict(unfold=("LowHeightBox.Q3", "sorry")), "not a Lean constant name"),
    (dict(unfold=("Q3]; exact foo",)), "not a Lean constant name"),
    (dict(target="LowHeightBox.Q3 z := by sorry"), "not a plain Lean term"),
    (dict(target="decide (Q3 z)"), "forbidden token"),
    (dict(target="(LowHeightBox.Q3 z"), "malformed"),
    (dict(var="hz", coords=(("x", "hz.re"), ("y", "hz.im"))), "collides"),
    (dict(simp_closes=1), "must be a bool"),
])
def test_refuse_complex_face_defects(kw, msg):
    with pytest.raises(PreorderingRefusal, match=msg):
        _cert(3, face=_face(**kw))


def test_refuse_names_shadowing_a_face_namespace():
    syms = (sp.Symbol("Complex"), sp.Symbol("y"))
    with pytest.raises(PreorderingRefusal, match="reserved"):
        preordering_multiplier_certificate(
            symbols=syms, target=li_box_rung_target(3, *syms),
            generators=li_disk_generators(*syms), face=_face(coords=(("Complex", "z.re"),
                                                                      ("y", "z.im"))))
    gens = (li_disk_generators(x, y)[0], Generator("LowHeightBox", y ** 2), GENS[2])
    with pytest.raises(PreorderingRefusal, match="shadow a namespace"):
        _cert(3, generators=gens, face=_face())


# --- emission --------------------------------------------------------------------

def _hand_spec(N, **kw):
    mult, _t = GEN.HAND_CERTIFICATES[N]
    spec = dict(target=li_box_rung_target(N, x, y), generators=GENS, multiplier=mult,
                terms=GEN.hand_terms(N))
    if mult[1] is not None:
        spec["locus"] = "auto"
    spec.update(kw)
    return spec


def test_emit_q3_is_the_hand_proof_shape():
    txt = _emit_text(_hand_spec(3), name="re_Q3_core")
    assert "theorem re_Q3_core (x y : ℝ) (hz : x ^ 2 + y ^ 2 ≤ x) :" in txt
    assert "0 ≤ 9 * x + 6 * y ^ 2 + x ^ 3 - 6 * x ^ 2 - 3 * x * y ^ 2 := by" in txt
    assert ("  obtain ⟨d, hd0, hde⟩ : ∃ d : ℝ, 0 ≤ d ∧ d = x - x ^ 2 - y ^ 2 :=\n"
            "    ⟨_, by linarith, rfl⟩") in txt
    assert ("  obtain ⟨s, hs0, hse⟩ : ∃ s : ℝ, 0 ≤ s ∧ s = x ^ 2 + y ^ 2 :=\n"
            "    ⟨_, by positivity, rfl⟩") in txt
    assert "    rw [hde, hBe, hse]\n    ring\n  rw [key]\n  positivity\n" in txt
    assert "generalize" not in txt and "rcases" not in txt


def test_emit_q4_multiplier_and_locus_branch():
    txt = _emit_text(_hand_spec(4), name="re_Q4_core")
    assert "  generalize hP : 16 * x + 20 * y ^ 2" in txt and "- x ^ 4 - y ^ 4 = P\n" in txt
    assert "  have key : 14 * s * P = 44 * d * B + 180 * d * s + 433 * B ^ 2" in txt
    assert "    rw [← hP, hde, hBe, hse]\n    ring\n" in txt
    assert "  have hcert : 0 ≤ 14 * s * P := by rw [key]; positivity" in txt
    assert "  rcases eq_or_lt_of_le hs0 with hs' | hs'" in txt
    assert "    have hlocx : x = 0 := by nlinarith only [hs', hse, sq_nonneg x, sq_nonneg y]" in txt
    assert "    have hlocy : y = 0 := by nlinarith only [hs', hse, sq_nonneg x, sq_nonneg y]" in txt
    assert "    rw [← hP, hlocx, hlocy]\n    norm_num\n" in txt
    assert ("  · exact (mul_nonneg_iff_of_pos_left (by positivity : (0 : ℝ) < 14 * s)).mp hcert"
            in txt)
    assert "Multiplier zero locus: s = 0 forces (x = 0, y = 0), where p = 0 >= 0." in txt


def test_emit_q5_multiplier_is_s_squared():
    txt = _emit_text(_hand_spec(5), name="re_Q5_core")
    assert "  have key : s ^ 2 * P = " in txt
    assert "(by positivity : (0 : ℝ) < s ^ 2)).mp hcert" in txt


def test_emit_binds_only_the_generators_the_certificate_uses():
    txt = _emit_text(dict(target=li_box_rung_target(1, x, y), generators=GENS), name="q1")
    assert "obtain ⟨d," in txt and "obtain ⟨s," in txt and "obtain ⟨B," not in txt
    assert "    rw [hde, hse]\n" in txt
    # the target IS a variable (x): the `generalize`-free M = 1 path rewrites the goal only
    assert "  have key : x = d + s := by" in txt


def test_emit_constant_multiplier_other_than_one():
    txt = _emit_text(dict(target=li_box_rung_target(3, x, y), generators=GENS,
                          multiplier=("3/2", None, 0)), name="q3c")
    assert "  have key : (3 / 2) * P = " in txt
    assert "(mul_nonneg_iff_of_pos_left (by norm_num : (0 : ℝ) < (3 / 2))).mp hcert" in txt
    assert "rcases" not in txt


def test_emit_locus_rewrites_only_the_coordinates_the_target_contains():
    # target free of y: `s * (x^2 + x) = ...` style instance on {s >= 0, x >= 0}
    gens = (Generator("s", x ** 2 + y ** 2), Generator("u", x, "hyp", "hu", None))
    spec = dict(target=x ** 2 + x, generators=gens, multiplier=(1, "s", 1), locus="auto",
                max_total_degree=4)
    txt = _emit_text(spec, name="noy")
    assert "have hlocx : x = 0" in txt and "hlocy" not in txt
    assert "    rw [← hP, hlocx]\n" in txt


def test_emit_locus_off_the_origin_uses_offset_squares():
    # m = (x - 1)^2 + 2 y^2 renders with an odd monomial, so it is a `hyp` generator here
    gens = (Generator("m", (x - 1) ** 2 + 2 * y ** 2, "hyp", "hm", None),)
    spec = dict(target=(x - 1) ** 2 + 2 * y ** 2, generators=gens,
                multiplier=(1, "m", 1), locus="auto", max_total_degree=2)
    cert = preordering_multiplier_certificate(symbols=(x, y), **spec)
    assert cert.locus.point == (("x", 1), ("y", 0))
    txt = _emit_text(spec, name="off")
    assert "nlinarith only [hm', hme, sq_nonneg (x - 1), sq_nonneg y]" in txt
    assert "have hlocx : x = 1" in txt


def test_emit_complex_face_two_theorems():
    txt = _emit_text(_hand_spec(4, face=GEN.face(4)), name="re_Q4_face")
    assert "theorem re_Q4_face_real (x y : ℝ) (hz : x ^ 2 + y ^ 2 ≤ x) :" in txt
    assert ("theorem re_Q4_face {z : ℂ} (hz : z.re ^ 2 + z.im ^ 2 ≤ z.re) :\n"
            "    0 ≤ (LowHeightBox.Q4 z).re := by") in txt
    assert "  have hre : (LowHeightBox.Q4 z).re = 16 * z.re + 20 * z.im ^ 2" in txt
    assert "    simp only [LowHeightBox.Q4, Complex.sub_re, Complex.mul_re" in txt
    assert "Complex.add_re]\n    ring\n  rw [hre]\n  exact re_Q4_face_real z.re z.im hz\n" in txt


def test_emit_complex_face_simp_closes_drops_ring():
    txt = _emit_text(dict(target=li_box_rung_target(1, x, y), generators=GENS,
                          face=GEN.face(1)), name="q1f")
    assert "    simp only [LowHeightBox.Q1]\n  rw [hre]\n" in txt


def test_theorem_counts():
    fam = preordering_multiplier_family(
        "Counts", (x, y), GridSpec([("i", [0, 1, 2])]), lambda pt: f"c{pt['i']}",
        spec=lambda pt: [dict(target=x, generators=GENS),
                         _hand_spec(4, face=GEN.face(4)), _hand_spec(5)][pt["i"]])
    report = emit(certify(fam), LeanProfile(namespace=("Counts",)),
                  [PreorderingMultiplierEmitter()], ValidationReport(checks=(("x", True),)))
    assert report.n_theorems == 4           # the face instance emits core + face


def test_emit_is_lint_clean_deterministic_and_honest():
    for spec in (_hand_spec(3), _hand_spec(4), _hand_spec(5, face=GEN.face(5)),
                 dict(target=li_box_rung_target(2, x, y), generators=GENS)):
        txt = _emit_text(spec)
        assert txt == _emit_text(spec), "emission is not byte-deterministic"
        errs = [i for i in lint_lean_text(txt) if i.severity == "error"]
        assert errs == [], errs
        for bad in ("sorry", "admit", "native_decide", "decide", "axiom "):
            assert bad not in txt
        assert "conjecture1_proved = False" in txt
        for ch in txt:
            assert ord(ch) < 0x1F000, f"emoji {ch!r} in emitted Lean"


def test_emit_header_facts_are_computed_not_asserted():
    """A hand-minted certificate with a negative coefficient is DESCRIBED as such."""
    from telperion.negative_control_harness import registered_adapters
    ad = registered_adapters()["PreorderingMultiplierEmitter"]
    false_txt = " ".join(ad.emit_call(ad.make_false_cert(), "forged").split())
    assert "MIXED sign (not a preordering certificate)" in false_txt
    assert "hand-minted for the negative control (Layer 1 bypassed)" in false_txt
    assert "nonnegative rational coefficients" not in false_txt
    assert "re-checked" not in false_txt
    true_txt = " ".join(ad.emit_call(ad.make_true_cert(), "honest").split())
    assert "nonnegative rational coefficients" in true_txt


def test_certify_failure_path_records_the_refusal():
    """Through the generic certify(): the Q_6 obstruction is a recorded failure, never Lean."""
    from telperion.certify import CertificationError
    spec = dict(target=li_box_rung_target(6, x, y), generators=GENS,
                multiplier_candidates="auto", scan_box=GEN.SCAN_BOX)
    with pytest.raises(CertificationError, match="OBSTRUCTED_AND_LOCATED") as ei:
        certify(_fam(spec))
    assert len(ei.value.failures) == 1 and "p = -27772/15625" in ei.value.failures[0][1]


def test_obstruction_refutation_lean_text():
    with pytest.raises(PreorderingObstruction) as ei:
        _cert(6, multiplier_candidates="auto", scan_box=GEN.SCAN_BOX)
    txt = obstruction_refutation_lean(ei.value, "q6_false")
    assert "theorem q6_false :\n    ¬ ∀ x y : ℝ, x ^ 2 + y ^ 2 ≤ x → 0 ≤ 36 * x" in txt
    assert "  intro h\n  have hw := h (4 / 5) (-(2 / 5)) (by norm_num)\n  norm_num at hw\n" in txt
    assert "p = -27772/15625" in txt and "conjecture1_proved = False" in txt
    with pytest.raises(PreorderingRefusal, match="needs a PreorderingObstruction"):
        obstruction_refutation_lean(ValueError("x"), "q6_false")
    with pytest.raises(PreorderingRefusal, match="identifier"):
        obstruction_refutation_lean(ei.value, "q6 false")


# --- the dogfood file ---------------------------------------------------------------

def test_dogfood_file_is_regenerable_byte_for_byte():
    """The checked-in probe is exactly what the generator writes: banner + frozen emitter
    output + the Q_6 refutation + the kernel cross-checks -- the emitter cannot drift from it."""
    assert GEN.OUT == _DOGFOOD_LEAN
    assert _DOGFOOD_LEAN.is_file(), "run examples/li_positivity/dogfood_preordering_multiplier.py"
    assert _DOGFOOD_LEAN.read_text(encoding="utf-8") == GEN.build_text()


def test_dogfood_file_regenerates_the_rungs_under_new_names():
    txt = _DOGFOOD_LEAN.read_text(encoding="utf-8")
    assert txt.startswith("/-\n  Dogfood_preordering_multiplier")
    assert "conjecture1_proved = False" in txt and "Nothing here bears on RH" in txt
    assert "\nimport LiBoxRungs\n" in txt
    assert "namespace DogfoodPreorderingMultiplier" in txt
    names = [nm for nm, _N, _how in GEN.INSTANCES]
    for nm in names:
        assert f"theorem {nm} " in txt and f"theorem {nm}_real " in txt
        assert f"#print axioms DogfoodPreorderingMultiplier.{nm}\n" in txt
        assert f"#print axioms DogfoodPreorderingMultiplier.{nm}_real\n" in txt
    assert "theorem re_Q6_disk_claim_false :" in txt
    assert "#print axioms DogfoodPreorderingMultiplier.re_Q6_disk_claim_false" in txt
    # the originals are consumed, never redefined
    for n in (3, 4, 5):
        assert f"LowHeightBox.re_Q{n}_nonneg hz" in txt
        assert f"theorem re_Q{n}_nonneg " not in txt
    assert "exact re_Q5_nonneg_regen hz" in txt and "interval_cases n" in txt
    stripped = re.sub(r"/-.*?-/", "", txt, flags=re.S)
    assert not re.search(r"\b(sorry|admit|native_decide)\b", stripped)
    for ch in txt:
        assert ord(ch) < 0x1F000, f"emoji {ch!r} in the dogfood file"


def test_dogfood_generator_check_mode_reports_ok():
    assert GEN.main(["--check"]) == 0


# --- the kernel (opt-in: TELPERION_PM_KERNEL=1, run under the Lean slot lock) ---------

_KERNEL = os.environ.get("TELPERION_PM_KERNEL") == "1" and lean_env_ready(_LI)


@pytest.mark.skipif(not _KERNEL, reason="opt-in kernel check (TELPERION_PM_KERNEL=1 and a built "
                                        "li_positivity island)")
def test_dogfood_compiles_on_the_island_axiom_clean():
    import subprocess
    proc = subprocess.run(["lake", "env", "lean", "Probes/Dogfood_preordering_multiplier.lean"],
                          cwd=str(_LI), capture_output=True, text=True, timeout=1800)
    out = proc.stdout + proc.stderr
    assert proc.returncode == 0, out
    assert "error" not in out.lower(), out
    lines = [ln for ln in out.splitlines() if "depends on axioms" in ln]
    assert len(lines) == 2 * len(GEN.INSTANCES) + 1, out
    for ln in lines:
        assert ln.endswith("[propext, Classical.choice, Quot.sound]"), ln
