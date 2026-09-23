"""enclosure_tree emitter -- rational two-sided enclosures of expression trees over transcendental
atoms (SHAPES_AUDIT_48H_2026-09-22.md section 2 rank 1; A N2/N3/N4, B C2, C 4.7, D 4).

Acceptance is pinned on the dogfood instances with EXACT certificates: the two pi-face rate
corollaries of `LiLadderHeight` / `LiLadderSharp` (the ladder search must land on d4 and d6 by
itself) and the nine `LeakageDictionary.lean:276-359` bracket lemmas with their ORIGINAL claims.
Every refusal of the module docstring has its own test.  The emitted Lean is pinned by substring
and compared line by line against the hand proofs it regenerates.  The Lean kernel is the arbiter
(`examples/li_positivity/lean/Probes/Dogfood_enclosure_tree.lean` is compiled on the island); these
are the pre-CI self-checks.

conjecture1_proved = False.
"""
import importlib.util
import re
import sys
from fractions import Fraction as R
from pathlib import Path

import pytest
import sympy as sp

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

import telperion  # noqa: E402,F401  (loads every Emitter subclass + adapter)
from telperion import (  # noqa: E402
    EnclosureTreeEmitter,
    GridSpec,
    LeanProfile,
    ValidationReport,
    certify,
    emit,
    enclosure_tree_certificate,
    enclosure_tree_family,
    log_sqrt_certificate,
)
from telperion.certify import _SPECIAL_DISPATCH, _SPECIAL_KINDS, emitter_for  # noqa: E402
from telperion.emit_enclosure_tree import (  # noqa: E402
    DEFAULT_LOG_ORDER,
    LOG_TWO_HI,
    LOG_TWO_LO,
    PI_LADDER,
    EnclosureTreeRefusal,
    Node,
    exp_taylor_box,
    lean_expr,
    log_taylor_box,
    node_add,
    node_arctan,
    node_div,
    node_exp,
    node_log,
    node_mul,
    node_neg,
    node_pi,
    node_pow,
    node_rat,
    node_sqrt,
    node_sub,
    sqrt_bracket,
)
from telperion.lean_lint import lint_lean_text  # noqa: E402

_ROOT = Path(__file__).resolve().parents[1]
_EX = _ROOT / "examples"
_LEAKAGE = _EX / "quasicrystal" / "lean" / "LeakageDictionary.lean"
_LI_HEIGHT = _EX / "li_positivity" / "lean" / "LiLadderHeight.lean"
_LI_SHARP = _EX / "li_positivity" / "lean" / "LiLadderSharp.lean"
_E6B23 = _EX / "rvm_bridge" / "lean" / "E6Bridge23.lean"
_GEN = _EX / "li_positivity" / "dogfood_enclosure_tree.py"
_OUT_LI = _EX / "li_positivity" / "lean" / "Probes" / "Dogfood_enclosure_tree.lean"
_OUT_QC = _EX / "quasicrystal" / "lean" / "Probes" / "Dogfood_enclosure_tree.lean"


def _load_generator():
    spec = importlib.util.spec_from_file_location("dogfood_enclosure_tree", _GEN)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


_G = _load_generator()


def _pi_face():
    return node_div(node_mul(node_mul(node_rat(3), node_pi()), node_rat(4000)), node_rat(2))


def _pi_sharp():
    return node_mul(node_mul(node_rat(2), node_pi()), node_sub(node_rat(4000), node_rat(R(1, 2))))


def _fam(specs: dict, fam_name="EnclosureTreeTest"):
    keys = list(specs)
    return enclosure_tree_family(fam_name, GridSpec([("i", list(range(len(keys))))]),
                                 lambda pt: keys[pt["i"]], spec=lambda pt: specs[keys[pt["i"]]])


def _emit_text(specs: dict, fam_name="EnclosureTreeTest") -> str:
    report = emit(
        certify(_fam(specs, fam_name)),
        LeanProfile(namespace=(fam_name,), imports=("Mathlib",)),
        [EnclosureTreeEmitter()],
        ValidationReport(checks=(("enclosure_tree", True),)),
    )
    return next(iter(report.files.values()))


def _refused(match: str, fn, *a, **kw):
    with pytest.raises(ValueError, match=match) as ei:
        fn(*a, **kw)
    assert "enclosure_tree REFUSED" in str(ei.value)
    assert isinstance(ei.value, EnclosureTreeRefusal)


# --- registry wiring -------------------------------------------------------------------

def test_kind_is_registered_in_both_certify_tables():
    assert "enclosure_tree" in _SPECIAL_KINDS
    assert _SPECIAL_DISPATCH["enclosure_tree"] == (
        "emit_enclosure_tree", "certify_enclosure_tree_point", "EnclosureTreeEmitter")
    assert _fam({"x": dict(tree=node_pi())}).kind == "enclosure_tree"


def test_emitter_for_round_trips():
    assert emitter_for("enclosure_tree").kind == "enclosure_tree"
    assert isinstance(emitter_for("enclosure_tree"), EnclosureTreeEmitter)


def test_emitter_is_classified_with_a_wired_adapter():
    from telperion.emitter_sensitivity import (
        NEG_CONTROL_ADAPTER, REGISTRY, STRUCTURALLY_NONVACUOUS,
    )
    from telperion.negative_control_harness import ADAPTERS
    stance = REGISTRY["EnclosureTreeEmitter"]
    assert stance.stance == STRUCTURALLY_NONVACUOUS
    assert "conjecture1_proved = False" in stance.reason
    assert stance.neg_control is not None and stance.neg_control.kind == NEG_CONTROL_ADAPTER
    assert "EnclosureTreeEmitter" in ADAPTERS


# --- acceptance: the pi face (LiLadderHeight / LiLadderSharp) -----------------------------

def test_pi_face_height_lands_on_d4_exactly_like_the_hand_proof():
    cert = enclosure_tree_certificate(_pi_face(), rate_cap=18848)
    assert cert.pi_digits == 4                       # the hand proof's `Real.pi_gt_d4`
    assert cert.lo == 18849 == sp.Integer(18848 + 1)  # 3 * 3.1415 * 4000 / 2, exactly tight
    assert cert.hi == sp.Rational(94248, 5)           # 3 * 3.1416 * 4000 / 2
    assert cert.root.lo_strict and cert.root.hi_strict  # open: pi_gt_d4 is strict
    assert [n.op for n in cert.order] == ["pi", "div"]  # the linear chain is seen through
    assert cert.n_theorems == 3


def test_pi_face_height_d2_is_one_rung_short():
    # the ladder search is forced: at d2 the bound is 3 * 3.14 * 2000 = 18840 < 18849
    _refused("rate cap 18848 is NOT reached", enclosure_tree_certificate,
             node_div(node_mul(node_mul(node_rat(3), node_pi(digits=2)), node_rat(4000)),
                      node_rat(2)), rate_cap=18848)


def test_pi_face_sharp_lands_on_d6_exactly_like_the_hand_proof():
    cert = enclosure_tree_certificate(_pi_sharp(), rate_cap=25128)
    assert cert.pi_digits == 6                       # the hand proof's `Real.pi_gt_d6`
    assert cert.lo == 7999 * PI_LADDER[6][0] == sp.Rational(3141199301, 125000)
    assert cert.lo >= 25129
    # d4 is one rung short: 7999 * 3.1415 = 25128.8585 < 25129
    assert 7999 * PI_LADDER[4][0] < 25129
    _refused("rate cap 25128 is NOT reached", enclosure_tree_certificate,
             node_mul(node_mul(node_rat(2), node_pi(digits=4)),
                      node_sub(node_rat(4000), node_rat(R(1, 2)))), rate_cap=25128)


def test_pi_face_expressions_render_as_the_island_writes_them():
    assert lean_expr(enclosure_tree_certificate(_pi_face()).root) == "3 * Real.pi * 4000 / 2"
    assert lean_expr(enclosure_tree_certificate(_pi_sharp()).root) == \
        "2 * Real.pi * (4000 - 1 / 2)"
    # the island statements the emitted rate lemmas must match (with `π` for `Real.pi`)
    assert "(n + 1 : ℝ) ≤ 3 * π * 4000 / 2" in _LI_HEIGHT.read_text(encoding="utf-8")
    assert "(n + 1 : ℝ) ≤ 2 * π * (4000 - 1 / 2)" in _LI_SHARP.read_text(encoding="utf-8")


def test_pinned_pi_rung_is_honoured_not_overridden():
    cert = enclosure_tree_certificate(node_pi(digits=20))
    assert cert.root.digits == 20 and cert.pi_digits is None
    assert cert.lo == PI_LADDER[20][0]


# --- acceptance: LeakageDictionary.lean:276-359 with the ORIGINAL claims ------------------

def test_leakage_nine_brackets_certify_with_the_original_claims():
    certs = {k: certify(_fam({k: v})).instances[0].payload for k, v in _G.qc_specs().items()}
    s5 = certs["qc_sqrt_five_bounds"]
    assert (s5.lo, s5.hi) == (sp.Rational(1118033988749, 500000000000),
                              sp.Rational(2236067977501, 1000000000000))
    assert s5.lo ** 2 < 5 < s5.hi ** 2                 # the two exact rational squares
    inner = certs["qc_sqrt_inner_bounds"].root
    radicand = inner.children[0]
    assert (radicand.lo, radicand.hi) == (10 - 2 * s5.hi, 10 - 2 * s5.lo)   # exact fold
    assert inner.lo ** 2 < radicand.lo and radicand.hi < inner.hi ** 2
    kappa = certs["qc_dhKappa_bounds"]
    assert (kappa.lo, kappa.hi) == (sp.Rational(284079041, 10 ** 9),
                                    sp.Rational(142039523, 500000000))
    num, den = kappa.root.children
    assert kappa.root.box_lo == min(num.lo / den.lo, num.lo / den.hi, num.hi / den.lo,
                                    num.hi / den.hi)
    assert kappa.lo < kappa.root.box_lo and kappa.root.box_hi < kappa.hi   # strict slack
    l32 = certs["qc_log_three_halves_bounds"]
    assert l32.root.order == DEFAULT_LOG_ORDER == 24 and l32.root.route == "taylor"
    assert (l32.lo, l32.hi) == log_taylor_box(sp.Rational(3, 2), 24)   # zero slack, closed
    assert not l32.root.lo_strict and not l32.root.hi_strict
    l2 = certs["qc_log_two_bounds"]
    assert (l2.lo, l2.hi) == (LOG_TWO_LO, LOG_TWO_HI) and l2.root.route == "mathlib2"
    assert l2.root.lo_strict and l2.root.hi_strict     # open: log_two_gt_d9 is strict
    for key, coeffs in (("qc_log_six_bounds", (2, 1)), ("qc_log_three_bounds", (1, 1))):
        fold = certs[key].root
        assert fold.route == "fold" and fold.coeffs == coeffs
        assert fold.box_lo == coeffs[0] * LOG_TWO_LO + coeffs[1] * l32.lo == fold.lo
        assert fold.box_hi == coeffs[0] * LOG_TWO_HI + coeffs[1] * l32.hi == fold.hi
        assert fold.lo_strict and fold.hi_strict       # inherited from the open log 2 atom


def test_leakage_claims_are_the_island_literals():
    src = _LEAKAGE.read_text(encoding="utf-8")
    for lit in ("1118033988749 / 500000000000", "2236067977501 / 1000000000000",
                "1175570504583 / 500000000000", "2351141009173 / 1000000000000",
                "284079041 / 1000000000", "142039523 / 500000000",
                "6070423640075591 / 14971509072199680", "6070425424818551 / 14971509072199680",
                "52393246555737784416259 / 29241228656640000000000",
                "52393250070805106822899 / 29241228656640000000000",
                "32124771363880211544067 / 29241228656640000000000",
                "32124774864326919622387 / 29241228656640000000000"):
        assert lit in src, lit


def test_sharing_proves_each_atom_once_and_consumes_it_by_name():
    txt = _emit_text(_G.qc_specs(), "ShareTest")
    assert txt.count("theorem qc_sqrt_five_bounds :") == 1
    assert txt.count("theorem qc_log_two_bounds :") == 1
    assert txt.count("theorem qc_log_three_halves_bounds :") == 1
    assert txt.count("obtain ⟨h0lo, h0hi⟩ := qc_sqrt_five_bounds") == 1   # the inner radical
    assert "obtain ⟨h1lo, h1hi⟩ := qc_sqrt_five_bounds" in txt            # the DH quotient
    assert txt.count(":= qc_log_two_bounds") == 2                         # both folds
    assert len(re.findall(r"(?m)^theorem ", txt)) == 7


# --- the exact arithmetic ----------------------------------------------------------------

def test_sqrt_bracket_is_outward_and_tight():
    for lo, hi, d in ((5, 5, 12), (sp.Rational(1, 3), sp.Rational(2, 3), 6), (2, 7, 3)):
        s, t = sqrt_bracket(sp.Rational(lo), sp.Rational(hi), d)
        assert s * s <= lo and hi <= t * t
        step = sp.Rational(1, 10 ** d)
        assert (s + step) ** 2 > lo and (t - step) ** 2 < hi       # one grid step is too far
    assert sqrt_bracket(sp.Integer(4), sp.Integer(4), 5) == (2, 2)


def test_taylor_boxes_match_the_island_and_the_exp_emitter():
    lo, hi = log_taylor_box(sp.Rational(3, 2), 24)
    assert lo == sp.Rational(6070423640075591, 14971509072199680)
    assert hi == sp.Rational(6070425424818551, 14971509072199680)
    from telperion.emit_exp_enclosure import taylor_box
    for x, n in ((sp.Rational(1, 10), 6), (sp.Integer(-1), 14), (sp.Rational(1, 2), 9)):
        assert exp_taylor_box(x, n) == taylor_box(x, n)


def test_order_level_search_raises_unpinned_taylor_atoms_only_when_needed():
    tree = node_add(node_log(R(3, 2)), node_log(R(4, 3)))
    loose = enclosure_tree_certificate(tree)
    assert loose.order_level is None
    assert {c.order for c in loose.root.children} == {DEFAULT_LOG_ORDER}
    tight = enclosure_tree_certificate(tree, lo=R(693147180, 10 ** 9), hi=R(693147181, 10 ** 9))
    assert tight.order_level == 32
    assert {c.order for c in tight.root.children} == {32}


def test_claimed_taylor_atom_takes_the_least_fitting_order():
    box = log_taylor_box(sp.Rational(3, 2), 30)
    cert = enclosure_tree_certificate(node_log(R(3, 2), lo=box[0], hi=box[1]))
    assert cert.root.order == 30


def test_strictness_is_decided_per_side_and_only_when_provable():
    mixed = enclosure_tree_certificate(node_add(node_pi(digits=4), node_log(R(3, 2))))
    assert mixed.root.lo_strict and mixed.root.hi_strict        # pi open propagates through +
    closed = enclosure_tree_certificate(node_log(R(3, 2)))
    assert not closed.root.lo_strict and not closed.root.hi_strict
    # (the order is pinned: with ONLY `hi` claimed the least-fitting search stops at order 1,
    # whose box [0, 1] meets the claim with zero slack -- the documented least-order rule)
    one_side = enclosure_tree_certificate(node_log(R(3, 2), order=24), hi=1)
    assert not one_side.root.lo_strict and one_side.root.hi_strict
    forced = enclosure_tree_certificate(node_log(R(3, 2), order=24), hi=1, strict=False)
    assert not forced.root.hi_strict
    least = enclosure_tree_certificate(node_log(R(3, 2)), hi=1)
    assert least.root.order == 1 and (least.lo, least.hi) == (0, 1)
    assert not least.root.hi_strict


def test_arctan_routes_are_chosen_exactly():
    half = enclosure_tree_certificate(node_arctan(node_rat(R(1, 2))))
    assert half.root.route == "half" and (half.lo, half.hi) == (R(1, 4), R(1, 2))
    wide = enclosure_tree_certificate(node_arctan(node_rat(2)))
    assert wide.root.route == "abs" and (wide.lo, wide.hi) == (-2, 2)
    cheap = enclosure_tree_certificate(node_arctan(node_rat(R(1, 2)), lo=R(-1, 2), hi=R(1, 2)))
    assert cheap.root.route == "abs"                 # the abs route already carries the claim


def test_log_sqrt_face_defaults_reproduce_the_island_constants():
    c = log_sqrt_certificate(shift=4, floor=1)       # E6Bridge23 log_add_four_le
    assert (c.k, c.c) == (3, 6)
    c0 = log_sqrt_certificate(floor=2)               # E6Bridge16 log n <= 2 sqrt n
    assert (c0.shift, c0.k, c0.c) == (0, 1, 2)
    c3 = log_sqrt_certificate(shift=5, floor=4, k=R(3, 2), c=4)
    assert (c3.k, c3.c) == (sp.Rational(3, 2), 4)


# --- refusals (the anti-phantom face) -------------------------------------------------------

def test_refuses_negative_radicand():
    _refused("radicand interval", enclosure_tree_certificate,
             node_sqrt(node_sub(node_pi(), node_rat(4))))


def test_refuses_denominator_containing_zero_or_negative():
    # at the pinned rung d0 the denominator pi - 3 has the box [0, 1]: it contains 0
    _refused("contains 0", enclosure_tree_certificate,
             node_div(node_rat(1), node_sub(node_pi(digits=0), node_rat(3))))
    # (unpinned, the ladder search moves on to d2, where pi - 3 lies in [0.14, 0.15])
    assert enclosure_tree_certificate(
        node_div(node_rat(1), node_sub(node_pi(), node_rat(3)))).pi_digits == 2
    _refused("contains 0", enclosure_tree_certificate, node_div(node_pi(), node_rat(0)))
    _refused("strictly NEGATIVE", enclosure_tree_certificate,
             node_div(node_pi(), node_sub(node_rat(3), node_pi())))


def test_refuses_a_claim_the_fold_does_not_imply_at_any_node():
    # the forge case at the root ...
    _refused("NOT implied by the exact interval fold", enclosure_tree_certificate,
             node_pi(digits=4), lo=R(31416, 10000))
    # ... and at an inner node whose parent would otherwise be fine
    inner = node_sqrt(node_rat(2), hi=R(141, 100))   # sqrt 2 = 1.41421... > 1.41
    _refused("sqrt", enclosure_tree_certificate, node_add(inner, node_pi()))
    _refused("NOT implied", enclosure_tree_certificate, node_log(R(3, 2), order=24),
             lo=0, hi=R(4, 10))


def test_refuses_sqrt_claims_by_the_exact_squares_not_a_grid():
    # a claim TIGHTER than the 1e-12 grid is fine when its square is right ...
    tight = sp.Rational(22360679774997, 10 ** 13)
    assert tight ** 2 < 5
    ok = enclosure_tree_certificate(node_sqrt(node_rat(5), lo=tight))
    assert ok.lo == tight
    # ... and refused the moment its square crosses the radicand
    over = sp.Rational(22360679774998, 10 ** 13)
    assert over ** 2 > 5
    _refused("NOT implied", enclosure_tree_certificate, node_sqrt(node_rat(5), lo=over))
    _refused("NOT implied", enclosure_tree_certificate, node_sqrt(node_rat(5), lo=-3, hi=-1))


def test_refuses_inverted_bracket():
    _refused("inverted bracket", enclosure_tree_certificate, node_pi(), lo=4, hi=3)


def test_refuses_strict_without_slack_or_open_endpoint():
    box = log_taylor_box(sp.Rational(3, 2), 24)
    _refused("STRICT claim", enclosure_tree_certificate,
             node_log(R(3, 2), order=24, lo=box[0], hi=box[1], strict=True))
    _refused("STRICT claim", enclosure_tree_certificate, node_log(R(3, 2), order=24),
             strict=True)
    # an OPEN endpoint needs no slack: log 2 at the Mathlib box, strict
    ok = enclosure_tree_certificate(node_log(2, lo=LOG_TWO_LO, hi=LOG_TWO_HI, strict=True))
    assert ok.root.lo_strict and ok.root.hi_strict


def test_refuses_log_out_of_domain_and_log_one():
    _refused("<= 0 is outside the domain", enclosure_tree_certificate, node_log(0))
    _refused("<= 0 is outside the domain", enclosure_tree_certificate, node_log(-2))
    _refused("log 1 = 0 exactly", enclosure_tree_certificate, node_log(1))


def test_refuses_log_outside_the_taylor_radius_without_a_factorisation():
    _refused(r"\|1 - r\| = 2 >= 1", enclosure_tree_certificate, node_log(3))
    _refused(r"\|1 - r\| = 5 >= 1", enclosure_tree_certificate, node_log(6))
    ok = enclosure_tree_certificate(node_log(3, factors=[(1, 2), (1, R(3, 2))]))
    assert ok.root.route == "fold"


def test_refuses_taylor_orders_outside_one_to_sixty_four():
    _refused("exceeds the cap 64", enclosure_tree_certificate, node_log(R(3, 2), order=65))
    _refused("< 1", enclosure_tree_certificate, node_log(R(3, 2), order=0))
    _refused("exceeds the cap 64", enclosure_tree_certificate, node_exp(R(1, 2), order=65))
    _refused("not an int", enclosure_tree_certificate, node_log(R(3, 2), order=True))
    _refused("takes no Taylor order", enclosure_tree_certificate, node_log(2, order=5))


def test_refuses_fold_phantoms():
    _refused("multiplies to 9", enclosure_tree_certificate,
             node_log(6, factors=[(2, 2), (1, R(9, 4))]))
    _refused("not positive", enclosure_tree_certificate,
             node_log(6, factors=[(0, 2), (1, 6)]))
    _refused("exceeds the cap 8", enclosure_tree_certificate,
             node_log(2 ** 9, factors=[(9, 2)]))
    _refused("one-log fold", enclosure_tree_certificate, node_log(R(3, 2), factors=[(1, R(3, 2))]))
    _refused("empty factorisation", enclosure_tree_certificate, node_log(6, factors=[]))
    _refused("<= 0", enclosure_tree_certificate,
             node_log(4, factors=[(1, -2), (1, -2)]))
    _refused("not a \\(multiplicity, factor\\) pair", node_log, 6, factors=[(2,)])
    _refused("must be a log node", enclosure_tree_certificate,
             Node(op="log", const=sp.Integer(4), factors=((2, node_pi()),)))
    _refused("fold factors exceed", enclosure_tree_certificate,
             node_log(2 ** 9, factors=[(1, 2)] * 9))


def test_refuses_exp_outside_exp_bound_and_at_zero():
    _refused(r"\|x\| = 2 > 1", enclosure_tree_certificate, node_exp(2))
    _refused(r"\|x\| = 6 > 1", enclosure_tree_certificate, node_exp(-6))   # E6Bridge16 e^-6
    _refused("exp 0 = 1", enclosure_tree_certificate, node_exp(0))


def test_refuses_power_phantoms():
    _refused("not >= 0 under the power", enclosure_tree_certificate,
             node_pow(node_sub(node_pi(), node_rat(4)), 2))
    _refused("must be an int >= 2", enclosure_tree_certificate, node_pow(node_pi(), 1))
    _refused("exceeds the cap 8", enclosure_tree_certificate, node_pow(node_pi(), 9))
    _refused("must be an int >= 2", enclosure_tree_certificate, node_pow(node_pi(), True))


def test_refuses_pi_off_the_ladder_and_unreachable_claims():
    _refused("not on Mathlib's ladder", enclosure_tree_certificate, node_pi(digits=3))
    _refused("not on Mathlib's ladder", enclosure_tree_certificate, node_pi(digits=True))
    # no rung up to d20 carries pi > 3.14159265358979323847
    _refused("NOT implied", enclosure_tree_certificate, node_pi(),
             lo=R(314159265358979323847, 10 ** 20))


def test_refuses_rate_caps_the_bound_does_not_reach():
    _refused("rate cap 18849 is NOT reached", enclosure_tree_certificate, _pi_face(),
             rate_cap=18849)
    _refused("rate cap -1 < 0", enclosure_tree_certificate, _pi_face(), rate_cap=-1)
    _refused("not an int", enclosure_tree_certificate, _pi_face(), rate_cap=18848.0)


def test_refuses_trees_without_transcendental_content():
    _refused("rational-constant tree", enclosure_tree_certificate, node_rat(3))
    _refused("no transcendental content", enclosure_tree_certificate,
             node_add(node_rat(3), node_rat(4)))
    _refused("takes no name or claim", enclosure_tree_certificate,
             node_add(node_pi(), node_sub(node_rat(4), node_rat(1), lo=0)))
    _refused("annihilates", enclosure_tree_certificate, node_mul(node_rat(0), node_pi()))


def test_refuses_floats_bools_and_non_rationals_everywhere():
    _refused("float", node_rat, 0.1)
    _refused("float", node_rat, sp.Float(0.1))
    _refused("bool", node_rat, True)
    _refused("not rational", node_rat, sp.sqrt(2))
    _refused("float", node_log, 1.5)
    _refused("float", node_exp, 0.5)
    _refused("float", node_pi, lo=3.14)
    _refused("float", enclosure_tree_certificate, node_pi(), hi=3.2)
    _refused("float", enclosure_tree_certificate,
             Node(op="pi", claim_lo=3.1))                  # a directly-built Node, too


def test_refuses_malformed_nodes_and_names():
    _refused("unknown node op", enclosure_tree_certificate, Node(op="cos"))
    _refused("takes 2 child", enclosure_tree_certificate, Node(op="add", children=(node_pi(),)))
    _refused("expected a Node", enclosure_tree_certificate,
             Node(op="neg", children=("pi",)))
    _refused("not an ASCII Lean identifier", enclosure_tree_certificate,
             node_pi(name="bad name"))
    _refused("strict must be", enclosure_tree_certificate, node_pi(strict="yes"))
    _refused("exceeds 64 nodes", enclosure_tree_certificate,
             _deep_sum(40))


def _deep_sum(n: int) -> Node:
    t = node_pi()
    for _ in range(n):
        t = node_add(t, node_rat(1))
    return t


def test_refuses_log_sqrt_phantoms():
    _refused("alpha = 1/3", log_sqrt_certificate, floor=1, alpha=R(1, 3))
    _refused("shift a = -1 < 0", log_sqrt_certificate, shift=-1, floor=2)
    _refused("floor y0 = 0 <= 0", log_sqrt_certificate, floor=0)
    _refused("FAILS at the floor", log_sqrt_certificate, shift=4, floor=1, k=2)   # 3 * 1 < 4
    _refused("k = 1/2 < 1", log_sqrt_certificate, shift=1, floor=1, k=R(1, 2))
    _refused("needs no k", log_sqrt_certificate, shift=0, floor=1, k=2)
    _refused("c = 5 < 2k = 6", log_sqrt_certificate, shift=4, floor=1, c=5)
    _refused("c = 1 < 2k = 2", log_sqrt_certificate, floor=1, c=1)
    _refused("usable Lean identifier", log_sqrt_certificate, floor=1, var="hy")
    _refused("float", log_sqrt_certificate, floor=1.0)


def test_certify_refuses_unknown_spec_keys_and_misnamed_roots():
    # certify() collects per-point refusals into a CertificationError
    with pytest.raises(Exception, match="unknown enclosure_tree spec key"):
        certify(_fam({"x": dict(tree=node_pi(), rate=3)}))
    with pytest.raises(Exception, match="unknown log_sqrt spec key"):
        certify(_fam({"x": dict(face="log_sqrt", floor=1, cc=3)}))
    with pytest.raises(Exception, match="unknown face"):
        certify(_fam({"x": dict(face="cos", tree=node_pi())}))
    with pytest.raises(Exception, match="takes the instance name"):
        certify(_fam({"x": dict(tree=node_pi(name="y"))}))
    with pytest.raises(Exception, match="rate cap 18849 is NOT reached"):
        certify(_fam({"x": dict(tree=_pi_face(), rate_cap=18849)}))


def test_emit_refuses_duplicate_theorem_names():
    with pytest.raises(ValueError, match="duplicate emitted theorem name 'x_rate'"):
        _emit_text({"x": dict(tree=_pi_face(), rate_cap=18848),
                    "x_rate": dict(tree=node_log(R(3, 2)))})


# --- the emitted Lean, pinned ---------------------------------------------------------------

def test_emit_pi_face_pins_atom_root_and_rate_lemma():
    txt = _emit_text({"li_height_rate_4000": _G.li_specs()["li_height_rate_4000"]})
    assert ("theorem li_height_rate_4000_n0 :\n"
            "    (6283 / 2000 : ℝ) < Real.pi ∧ Real.pi < (3927 / 1250 : ℝ) := by\n"
            "  constructor <;> linarith [Real.pi_gt_d4, Real.pi_lt_d4]\n") in txt
    assert ("theorem li_height_rate_4000 :\n"
            "    (18849 : ℝ) < 3 * Real.pi * 4000 / 2 ∧ 3 * Real.pi * 4000 / 2 < (94248 / 5 : ℝ)"
            " := by\n"
            "  obtain ⟨h0lo, h0hi⟩ := li_height_rate_4000_n0\n"
            "  constructor <;> linarith\n") in txt
    assert ("theorem li_height_rate_4000_rate (n : ℕ) (hn : n ≤ 18848) :\n"
            "    (n + 1 : ℝ) ≤ 3 * Real.pi * 4000 / 2 := by\n"
            "  obtain ⟨hlo, _hhi⟩ := li_height_rate_4000\n"
            "  have hn' : (n : ℝ) ≤ (18848 : ℝ) := by exact_mod_cast hn\n"
            "  linarith\n") in txt


def test_emit_sharp_rate_uses_d6():
    txt = _emit_text({"s": _G.li_specs()["li_sharp_rate_4000"]})
    assert "constructor <;> linarith [Real.pi_gt_d6, Real.pi_lt_d6]" in txt
    assert "(n + 1 : ℝ) ≤ 2 * Real.pi * (4000 - 1 / 2) := by" in txt


def test_emitted_leakage_skeletons_are_the_island_lines():
    """The regenerated proofs are the hand proofs' own lines (LeakageDictionary.lean:276-359),
    up to the literal spelling of the Taylor point and the `generalize` hardening."""
    txt = _emit_text(_G.qc_specs(), "LeakTest")
    src = _LEAKAGE.read_text(encoding="utf-8")
    # (island line, emitted line): identical, or differing only by the `(0 : R)` ascription the
    # emitter always writes and the `harg` it names separately
    pairs = (
        ("  have hn : 0 ≤ Real.sqrt 5 := Real.sqrt_nonneg 5",
         "  have hn : (0 : ℝ) ≤ Real.sqrt 5 := Real.sqrt_nonneg _"),
        ("  have h2 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)",
         "  have h2 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt harg"),
        ("  have h2 : Real.sqrt (10 - 2 * Real.sqrt 5) ^ 2 = 10 - 2 * Real.sqrt 5 :=\n"
         "    Real.sq_sqrt harg",
         "  have h2 : Real.sqrt (10 - 2 * Real.sqrt 5) ^ 2 = 10 - 2 * Real.sqrt 5 := "
         "Real.sq_sqrt harg"),
        ("  have hn : 0 ≤ Real.sqrt (10 - 2 * Real.sqrt 5) := Real.sqrt_nonneg _",
         "  have hn : (0 : ℝ) ≤ Real.sqrt (10 - 2 * Real.sqrt 5) := Real.sqrt_nonneg _"),
        ("  have hden : (0:ℝ) < Real.sqrt 5 - 1 := by linarith",
         "  have hden : (0 : ℝ) < Real.sqrt 5 - 1 := by linarith"),
    )
    for island, emitted in pairs:
        assert island in src, island
        assert emitted in txt, emitted
    verbatim = (
        "  have h := Real.abs_log_sub_add_sum_range_le hx 24",
        "  rw [abs_le] at h",
        "  norm_num [Finset.sum_range_succ] at h",
        "  constructor <;> linarith [h.1, h.2]",
        "  have h1 := Real.log_two_gt_d9",
        "  have h2 := Real.log_two_lt_d9",
        "  norm_num at h1 h2",
    )
    for line in verbatim:
        assert line in src and line in txt, line
    assert "  constructor <;> nlinarith [h2, hn]\n" in txt              # sqrt_five_bounds
    assert "  constructor <;> nlinarith [h2, hn, h0lo, h0hi]\n" in txt  # sqrt_inner_bounds
    assert "  have hden : (0 : ℝ) < Real.sqrt 5 - 1 := by linarith" in txt
    assert "  · rw [lt_div_iff₀ hden]" in txt and "  · rw [div_lt_iff₀ hden]" in txt
    assert "  generalize Real.log (3 / 2) = L at h ⊢" in txt
    assert ("    rw [← Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) "
            "(by norm_num : ((3 / 2) : ℝ) ≠ 0)]") in txt                  # log_three_bounds
    assert ("  have hfold : Real.log 6 = Real.log 2 + Real.log 2 + Real.log (3 / 2) := by\n"
            "    rw [← Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by norm_num : (2 : ℝ) ≠ 0)]\n"
            "    rw [← Real.log_mul (by norm_num : (2 * 2 : ℝ) ≠ 0) "
            "(by norm_num : ((3 / 2) : ℝ) ≠ 0)]\n"
            "    norm_num\n"
            "  rw [hfold]\n") in txt
    # the original statements, verbatim, for the ones whose literals are in lowest terms
    for stmt in ("(1118033988749 / 500000000000 : ℝ) < Real.sqrt 5 ∧",
                 "(284079041 / 1000000000 : ℝ) < (Real.sqrt (10 - 2 * Real.sqrt 5) - 2) / "
                 "(Real.sqrt 5 - 1) ∧",
                 "(6070423640075591 / 14971509072199680 : ℝ) ≤ Real.log (3 / 2) ∧"):
        assert stmt in txt, stmt


def test_emitted_log_sqrt_face_is_the_island_proof():
    txt = _emit_text({"log_add_four_le_regen": dict(face="log_sqrt", shift=4, floor=1)})
    src = _E6B23.read_text(encoding="utf-8")
    for line in (
        "  have h1 : Real.log (y + 4) = 2 * Real.log (Real.sqrt (y + 4)) := by",
        "    rw [Real.log_sqrt (by linarith)]; ring",
        "  have h2 : Real.log (Real.sqrt (y + 4)) ≤ Real.sqrt (y + 4) - 1 :=",
        "    Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr (by linarith))",
        "  have h3 : Real.sqrt (y + 4) ≤ 3 * Real.sqrt y := by",
        "    rw [show (3 : ℝ) * Real.sqrt y = Real.sqrt (3 ^ 2 * y) by",
        "      rw [Real.sqrt_mul (by norm_num), Real.sqrt_sq (by norm_num)]]",
        "    exact Real.sqrt_le_sqrt (by nlinarith)",
    ):
        assert line in src, line
        assert line in txt, line
    assert ("theorem log_add_four_le_regen {y : ℝ} (hy : (1 : ℝ) ≤ y) :\n"
            "    Real.log (y + 4) ≤ 6 * Real.sqrt y := by\n") in txt
    t0 = _emit_text({"log_le_two_sqrt": dict(face="log_sqrt", floor=2)})
    assert ("theorem log_le_two_sqrt {y : ℝ} (hy : (2 : ℝ) ≤ y) : "
            "Real.log y ≤ 2 * Real.sqrt y := by\n") in t0
    assert "  rw [Real.log_sqrt hy0.le] at h1\n" in t0


def test_emit_every_route_pins_its_skeleton():
    txt = _emit_text(_G.route_specs(), "RouteTest")
    # exp (the emit_exp_enclosure route)
    assert "  have hb := Real.exp_bound hx (n := 14) (by norm_num)\n" in txt
    assert "  have hx : |((-1) : ℝ)| ≤ 1 := by rw [abs_le]; constructor <;> norm_num\n" in txt
    # arctan: both routes, inline lemmas
    assert "  have hhalf : ∀ u : ℝ, 0 ≤ u → u ≤ 1 → u / 2 ≤ Real.arctan u := by\n" in txt
    assert "  have hu1 : (1 / 2 : ℝ) ≤ 1 := by norm_num\n" in txt
    assert "  have harct : ∀ t : ℝ, |Real.arctan t| ≤ |t| := by\n" in txt
    assert "  obtain ⟨ha1, ha2⟩ := abs_le.mp hall\n" in txt
    # McCormick
    for k in (1, 2, 3, 4):
        assert f"  have hm{k} : (0 : ℝ) ≤ (" in txt
    assert "  constructor <;> linarith [hm1, hm2, hm3, hm4]\n" in txt
    # power
    assert "    pow_le_pow_left₀ hnn (by linarith) 2\n" in txt
    # the non-strict general quotient
    assert "  · rw [le_div_iff₀ hden]" in txt and "  · rw [div_le_iff₀ hden]" in txt
    # the Taylor log at 1/2 (numerator 1) with the generalize hardening
    assert "  generalize Real.log (1 / 2) = L at h ⊢\n" in txt
    # the order-level search at 32
    assert "Real.abs_log_sub_add_sum_range_le hx 32" in txt
    # the shared-root alias and the named linear node
    assert ("theorem rt_sqrt_two_alias :\n"
            "    (1414213562373 / 1000000000000 : ℝ) < Real.sqrt 2 ∧ Real.sqrt 2 < (3 / 2 : ℝ)"
            " :=\n  rt_sqrt_two\n") in txt
    assert "theorem rt_radicand :\n" in txt


def test_emit_is_lint_clean_deterministic_and_honest():
    for specs in (_G.li_specs(), _G.qc_specs(), _G.route_specs()):
        txt = _emit_text(specs)
        assert txt == _emit_text(specs), "emission is not byte-deterministic"
        errs = [i for i in lint_lean_text(txt) if i.severity == "error"]
        assert errs == [], errs
        assert not re.search(r"\b(sorry|admit|native_decide|decide|axiom|opaque|"
                             r"implemented_by|skipKernelTC)\b", txt)
        n_thm = len(re.findall(r"(?m)^theorem ", txt))
        assert txt.count("conjecture1_proved = False") >= n_thm
        for ch in txt:
            assert ord(ch) < 0x1F000, f"emoji {ch!r} in emitted Lean"


def test_theorem_counts_and_single_emission_unit():
    fam = certify(_fam({**_G.li_specs(), **_G.qc_specs()}))
    report = emit(fam, LeanProfile(namespace=("Counts",)), [EnclosureTreeEmitter()],
                  ValidationReport(checks=(("x", True),)))
    assert report.n_theorems == 6 + 7
    units = EnclosureTreeEmitter().emit_units(fam, LeanProfile())
    assert len(units) == 1 and units[0][1] == 13


# --- the dogfood files ----------------------------------------------------------------------

def test_dogfood_files_are_regenerable_byte_for_byte():
    """The checked-in probes are exactly what the generator writes: banner + frozen emitter
    output + the kernel cross-checks -- the emitter cannot drift from the island files."""
    outs = _G.outputs()
    assert set(outs) == {_OUT_LI, _OUT_QC}
    for out, text in outs.items():
        assert out.is_file(), f"run {_GEN.name}"
        assert out.read_text(encoding="utf-8") == text, out


def test_li_dogfood_regenerates_the_pi_face_and_feeds_the_hand_theorems():
    txt = _OUT_LI.read_text(encoding="utf-8")
    assert txt.startswith("/-\n  Dogfood_enclosure_tree")
    assert "conjecture1_proved = False" in txt and "Nothing here bears on RH" in txt
    assert "import LiLadderHeight\nimport LiLadderSharp" in txt
    assert "namespace DogfoodEnclosureTree" in txt and "end DogfoodEnclosureTree" in txt
    assert ("fun n hn => LiLadderHeight.li_rungs_of_bands_4000 hall n "
            "(li_height_rate_4000_rate n hn)") in txt
    assert ("fun n hn => LiLadderHeight.li_rungs_of_bands_4000_sharp hall n "
            "(li_sharp_rate_4000_rate n hn)") in txt
    # the originals are consumed, never redefined
    assert "theorem li_rungs_of_bands_4000" not in txt
    names = re.findall(r"(?m)^theorem (\S+)", txt)
    assert len(names) == 40
    for nm in names:
        assert f"#print axioms DogfoodEnclosureTree.{nm}\n" in txt
    assert not re.search(r"\b(sorry|admit|native_decide)\b", txt)
    for ch in txt:
        assert ord(ch) < 0x1F000, f"emoji {ch!r} in the dogfood file"


def test_qc_dogfood_cross_checks_every_original_statement_verbatim():
    txt = _OUT_QC.read_text(encoding="utf-8")
    src = " ".join(_LEAKAGE.read_text(encoding="utf-8").split())
    assert "import LeakageDictionary" in txt
    assert "namespace DogfoodEnclosureTreeQC" in txt
    assert len(_G.QC_ORIGINALS) == 9
    for orig, regen, _proj, stmt in _G.QC_ORIGINALS:
        # the cross-checked statement IS the island statement (whitespace-normalized)
        assert f"theorem {orig} : {' '.join(stmt.split())} :=" in src or \
            f"theorem {orig} : {' '.join(stmt.split())} := by" in src, orig
        assert f"`Quasicrystal.{orig}`" in txt
        assert f"theorem {regen} :" in txt
    for regen in ("qc_sqrt_five_bounds", "qc_sqrt_inner_bounds", "qc_dhKappa_bounds",
                  "qc_log_three_halves_bounds", "qc_log_six_bounds", "qc_log_two_bounds",
                  "qc_log_three_bounds"):
        assert f"example : type_of% {regen} := by" in txt
        assert f"#print axioms DogfoodEnclosureTreeQC.{regen}\n" in txt
    assert "theorem sqrt_five_bounds" not in txt       # consumed, never redefined
    assert not re.search(r"\b(sorry|admit|native_decide)\b", txt)


def test_refuses_the_remaining_parameter_phantoms():
    _refused("sqrt bracket precision 0 outside 1..40", enclosure_tree_certificate,
             node_sqrt(node_rat(2), digits=0))
    _refused("sqrt bracket precision 41 outside 1..40", enclosure_tree_certificate,
             node_sqrt(node_rat(2), digits=41))
    _refused("not an int", enclosure_tree_certificate, node_sqrt(node_rat(2), digits=True))
    _refused("exceeds 1000000000000", enclosure_tree_certificate, _pi_face(),
             rate_cap=10 ** 12 + 1)
    _refused("fold multiplicity 1.5 is not an int", enclosure_tree_certificate,
             node_log(4, factors=[(1.5, 2), (1, R(4, 3))]))
    _refused("exp order 0 < 1", enclosure_tree_certificate, node_exp(R(1, 2), order=0))
    _refused("rational constant carries no content", enclosure_tree_certificate,
             node_add(node_pi(), Node(op="rat", const=sp.Integer(1), name="one")))
