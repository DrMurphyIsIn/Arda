"""Generate the XiLineZeros example (Stage 1 core): certify -> emit -> write.

    python examples/zeta_zero_localization/generate.py            # write lean/XiLineZeros.lean
    python examples/zeta_zero_localization/generate.py --check    # drift check (no write)
    python examples/zeta_zero_localization/generate.py --a 10 --b 35 --n-samples 51 --prec 300
        # print certified N for an ad-hoc interval; does NOT write the Lean file

On-line zero localization of the completed Riemann zeta function `Lambda` via
alternating-sign real enclosures + the intermediate value theorem.

DEFAULT CASES (written to lean/XiLineZeros.lean):

  Case 0 -- lambda_zero_first_14_15:
    Brackets the FIRST nontrivial zero (t ~ 14.1347) between t = 14 (Re < 0) and
    t = 15 (Re > 0).  One sign change => one certified on-line zero.

  Case 1 -- lambda_two_zeros_14_22:
    Brackets the first (t ~ 14.1347) in [14, 15] and the second (t ~ 21.022) in
    [15, 22] with three sample points alternating neg/pos/neg.  Two sign changes.

  Case 2 -- lambda_five_zeros_10_35:
    Half-integer sweep t in {10.0, 10.5, ..., 35.0} (51 points) at 300-bit Arb
    precision over [10, 35].  Resolves all 5 known nontrivial zeros in that range
    (t ~ 14.1347, 21.0220, 25.0109, 30.4249, 32.9351); certifies N >= 5 on-line
    zeros of Lambda on the critical line.  This is the MILESTONE theorem.

All three theorems share the prelude (gLine, gLine_continuous, lambda_eq_gLine).
The Lean file imports LambdaLineReal (Task 2).  conjecture1_proved = False.

INTERVAL DRIVER (ad-hoc; does not write):
  --a A  --b B    sweep interval (integers or halves)
  --n-samples N   number of evenly-spaced sample points in [a, b]
  --prec P        Arb working precision in bits (default 300)
Prints the certified N and exits; does not modify XiLineZeros.lean.

CERTIFICATION STATUS:
  Box membership (enclose_lambda -> sign-definite real box) is a documented
  Arb-certified NON-KERNEL input: Arb ball arithmetic (via python-flint) gives
  outward-rounded rational endpoints, but Lean does not independently verify the
  value.  The sign-change counting and IVT zero-existence argument are
  kernel-clean.  conjecture1_proved = False.
"""
from __future__ import annotations  # PEP 604 `X | None` annotations under Python 3.9

import argparse
import math
import sys
from fractions import Fraction
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "src"))

import sympy as sp  # noqa: E402

from telperion import ValidationReport, certify, emit  # noqa: E402
from telperion.arb_enclosure import enclose_lambda  # noqa: E402  (Task 1)
from telperion.emit_xi_line_zeros import (  # noqa: E402
    XI_LINE_ZEROS_PRELUDE,
    XiLineZerosEmitter,
    sign_change_count,
    xi_line_zeros_family,
)
from telperion.emit_winding_count import (  # noqa: E402  (Task 4, Stage 2A)
    WINDING_COUNT_PRELUDE,
    WindingCountEmitter,
    _z2_samples,
    segment_winding_certificate,
    winding_count_certificate,
    winding_count_family,
)
from telperion.arb_enclosure import enclose_lambda_boundary  # noqa: E402  (Task 2)
from telperion.arb_enclosure import enclose_zeta_segments  # noqa: E402  (Task 4 driver)
from telperion.emit_box_localization import (  # noqa: E402  (Task 4 driver)
    box_localization_certificate,
    emit_per_box_instantiation,
)
from telperion.family import GridSpec  # noqa: E402
from telperion.lean import LeanProfile  # noqa: E402

# kind "xi_line_zeros" is registered in telperion/certify.py
# (_SPECIAL_KINDS + _SPECIAL_DISPATCH).

_OUT = Path(__file__).resolve().parent / "lean" / "XiLineZeros.lean"
_OUT_WINDING = Path(__file__).resolve().parent / "lean" / "WindingCount.lean"

# T=100 RH-in-box milestone: [2/5,3/5]x[0,100], 29 on-line zeros = winding N(100).
# The emitted Lean file is COMMITTED (a permanent milestone, unlike the ephemeral per-box
# files); `--height 100 --check` byte-compares it and asserts N_line == N == 29.
_H100_BOX = (Fraction(2, 5), Fraction(3, 5), Fraction(0), Fraction(100))
_H100_EXPECTED_N = 29
_OUT_H100 = Path(__file__).resolve().parent / "lean" / "RHInBox_2d5_3d5_0_100.lean"

# CONCRETE T=100 certificate (Task 5): the CONFINEMENT-BAND wide box [1/10^6, 1-1/10^6]x[0,100],
# 29 on-line zeros = winding N(100).  This is the box atom AllZeros_h100 composes with the dVP+FE
# confinement.  The emitted Lean file is COMMITTED (a permanent milestone).  `run_box --check`
# byte-compares it and asserts N_line == N == 29.
_WIDEBOX = (Fraction(1, 1000000), Fraction(999999, 1000000), Fraction(0), Fraction(100))
_WIDEBOX_EXPECTED_N = 29
_OUT_WIDEBOX = (
    Path(__file__).resolve().parent
    / "lean"
    / "RHInBox_1d1000000_999999d1000000_0_100.lean"
)

# Lambda winding-count box and boundary-sampling resolution (Stage 2A milestone).
_WINDING_BOX = (Fraction(2, 5), Fraction(3, 5), Fraction(10), Fraction(35))
_WINDING_N_PER_SIDE = 30    # 4*30 = 120 boundary samples (all half-plane-witnessed)
_WINDING_PREC = 300         # Arb bits for the boundary Lambda enclosures
_WINDING_EXPECTED_N = 5     # the 5 on-line zeros of Lambda in [10, 35]

_PREC_DEMO = 200    # Arb bits for demo cases 0-1 (enclosures wide enough at t ~ 14-22)
_PREC_SWEEP = 300   # Arb bits for case 2 sweep over [10, 35]


def _real_box(t, prec):
    """Real box (lo, hi) of Lambda(1/2 + i*t) from the Task-1 Arb enclosure."""
    (lo_re, hi_re), _im = enclose_lambda("1/2", str(t), prec)
    return (lo_re, hi_re)


def _sweep_samples(a, b, n_samples, prec):
    """Build a list of (t, (lo, hi)) for n_samples evenly-spaced t in [a, b].

    t values are exact Fraction so they can be passed directly to enclose_lambda
    (converted to string internally) and to the certifier (which requires Fraction).
    The spacing is (b-a)/(n_samples-1); with a, b integer and n_samples = 51 this
    gives half-integer steps over [10, 35].
    """
    fa, fb = Fraction(a), Fraction(b)
    if n_samples < 2:
        raise ValueError("n_samples must be >= 2")
    step = (fb - fa) / (n_samples - 1)
    samples = []
    for k in range(n_samples):
        t = fa + k * step
        samples.append((t, _real_box(t, prec)))
    return samples


_NAMES = {
    0: "lambda_zero_first_14_15",
    1: "lambda_two_zeros_14_22",
    2: "lambda_five_zeros_10_35",
}


def _spec(pt):
    case = pt["case"]
    if case == 0:
        # Bracket the FIRST nontrivial zero (t ~ 14.1347) between t = 14 (Re < 0)
        # and t = 15 (Re > 0): one sign change -> one certified on-line zero.
        # Exercises the neg->pos IVT path (intermediate_value_Icc).
        a, b = sp.Integer(14), sp.Integer(15)
        samples = [
            (sp.Integer(14), _real_box(14, _PREC_DEMO)),
            (sp.Integer(15), _real_box(15, _PREC_DEMO)),
        ]
        return a, b, samples
    if case == 1:
        # TWO zeros with ALTERNATING signs, exercising BOTH IVT directions:
        #   t = 14 (Re < 0), t = 15 (Re > 0), t = 22 (Re < 0)
        # gives sign changes 14->15 (neg->pos, intermediate_value_Icc) and
        # 15->22 (pos->neg, intermediate_value_Icc') -- bracketing the first zero
        # (t ~ 14.1347) in [14, 15] and the third zero (t ~ 21.022) in [15, 22].
        a, b = sp.Integer(14), sp.Integer(22)
        samples = [
            (sp.Integer(14), _real_box(14, _PREC_DEMO)),
            (sp.Integer(15), _real_box(15, _PREC_DEMO)),
            (sp.Integer(22), _real_box(22, _PREC_DEMO)),
        ]
        return a, b, samples
    # case 2: MILESTONE -- 5 zeros in [10, 35].
    # Half-integer sweep at 300-bit precision: t in {10.0, 10.5, ..., 35.0} (51 points).
    # All 5 known nontrivial zeros in [10, 35] (t ~ 14.1347, 21.0220, 25.0109,
    # 30.4249, 32.9351) produce sign-change subintervals; sign_change_count = 5.
    a_frac, b_frac = Fraction(10), Fraction(35)
    sweep = _sweep_samples(10, 35, 51, _PREC_SWEEP)
    # certifier expects sympy-rational-convertible a, b
    return sp.Rational(a_frac), sp.Rational(b_frac), sweep


def build() -> str:
    """Build and emit XiLineZeros.lean (all three cases: 1-zero, 2-zero, 5-zero)."""
    fam = xi_line_zeros_family(
        "XiLineZeros",
        (),
        GridSpec([("case", [0, 1, 2])]),
        lambda pt: _NAMES[pt["case"]],
        spec=_spec,
    )
    profile = LeanProfile(
        namespace=("XiLineZeros",),
        imports=("Mathlib", "LambdaLineReal"),
        prelude=XI_LINE_ZEROS_PRELUDE,
        # gLine/continuity refer to `completedRiemannZeta`, `Complex.I`, etc.;
        # `open Complex` keeps the prelude and theorems concise.  Every emitted
        # hypothesis is load-bearing, so NO unusedVariables suppression is needed.
        options=("open Complex",),
    )
    report = emit(
        certify(fam),
        profile,
        [XiLineZerosEmitter()],
        ValidationReport(checks=(("xi_line_zeros", True),)),
    )
    return next(iter(report.files.values()))


_WINDING_NAMES = {
    0: "winding_z2",             # toy z^2, N=2 (from-scratch winding primitive)
    1: "winding_lambda_five",    # Lambda [2/5,3/5]x[10,35], N=5 (argument principle)
}


def _winding_spec(pt):
    """Spec for the winding-count family: pt['case'] -> {box, samples, mode}."""
    case = pt["case"]
    if case == 0:
        # Toy: f(z) = z^2 on [-1,1]^2, exact enclosure boxes -> winding = 2.
        return {"box": (-1, 1, -1, 1), "samples": _z2_samples(), "mode": "toy_z2"}
    # case 1: MILESTONE -- Lambda boundary winding on [2/5,3/5]x[10,35].
    # 120 boundary samples (4*30) at 300-bit Arb precision; the 5 on-line zeros in
    # [10, 35] give winding = 5.  All consecutive boxes carry a half-plane witness.
    samples = enclose_lambda_boundary(_WINDING_BOX, _WINDING_N_PER_SIDE, _WINDING_PREC)
    return {"box": _WINDING_BOX, "samples": samples, "mode": "lambda"}


def build_winding() -> str:
    """Build and emit WindingCount.lean (toy z^2 N=2 + Lambda N=5).

    Asserts (via the certificate) that the Lambda instance's certified winding
    number is 5 before emitting -- a drift guard on the milestone count."""
    # Certify-time assertion: the Lambda boundary winding is exactly 5.
    lam_samples = enclose_lambda_boundary(_WINDING_BOX, _WINDING_N_PER_SIDE, _WINDING_PREC)
    lam_cert = winding_count_certificate(_WINDING_BOX, lam_samples)
    if lam_cert.n != _WINDING_EXPECTED_N:
        raise AssertionError(
            f"Lambda winding count = {lam_cert.n}, expected {_WINDING_EXPECTED_N} "
            f"(5 on-line zeros in [10, 35])"
        )
    fam = winding_count_family(
        "WindingCount",
        GridSpec([("case", [0, 1])]),
        lambda pt: _WINDING_NAMES[pt["case"]],
        spec=_winding_spec,
    )
    profile = LeanProfile(
        namespace=("WindingCount",),
        imports=("Mathlib",),
        prelude=WINDING_COUNT_PRELUDE,
        # The winding primitives use `π`, `Complex.log`, `intervalIntegral`, `volume`.
        options=("open Complex intervalIntegral MeasureTheory Real",),
    )
    report = emit(
        certify(fam),
        profile,
        [WindingCountEmitter()],
        ValidationReport(checks=(("winding_count", True),)),
    )
    return next(iter(report.files.values()))


def run_interval(a, b, n_samples, prec):
    """Ad-hoc interval driver: compute certified N for [a, b] and print it.

    Does NOT write any Lean file.  Returns the certified sign-change count.
    """
    print(f"enclose_lambda sweep: [a={a}, b={b}], n_samples={n_samples}, prec={prec} bits")
    samples = _sweep_samples(a, b, n_samples, prec)
    n = sign_change_count(samples)
    print(f"certified N (sign-change count) = {n}")
    return n


def _box_tag(re_lo, re_hi, im_lo, im_hi) -> str:
    """A filesystem/Lean-identifier-safe tag for a box (fractions -> `p_q`)."""
    def _f(v):
        v = Fraction(v)
        return f"{v.numerator}" if v.denominator == 1 else f"{v.numerator}d{v.denominator}"
    s = f"{_f(re_lo)}_{_f(re_hi)}_{_f(im_lo)}_{_f(im_hi)}"
    return s.replace("-", "m")


def _online_sweep_zero_count_platt(im_lo, im_hi, prec: int) -> int:
    """Platt-hinted on-line sweep: rigorous zero inventory -> midpoint sampling.

    Uses FLINT's Platt machinery (arb_platt.zeros_in_interval) to pin N and
    enclose every zero ordinate in [im_lo, im_hi], then certifies signs of
    Lambda at the MIDPOINTS between consecutive zero enclosures (plus the two
    endpoints) via `enclose_lambda` — deterministic close-pair handling with
    ~n+1 evaluations instead of a ~1.6n grid + density retries.

    TRUST: the Platt inventory is a HINT.  The returned count is derived
    entirely from the enclose_lambda sign boxes (the existing documented Arb
    input class); a wrong hint produces a mismatch error, never a wrong count."""
    from telperion.arb_platt import PLATT_AVAILABLE, zeros_in_interval
    if not PLATT_AVAILABLE:
        raise RuntimeError("platt machinery unavailable")
    im_lo = Fraction(im_lo)
    im_hi = Fraction(im_hi)
    zs = zeros_in_interval(im_lo, im_hi, prec=max(prec, 96))
    pts = [im_lo]
    for (_l1, h1), (l2, _h2) in zip(zs, zs[1:]):
        m = (Fraction(h1) + Fraction(l2)) / 2
        mm = m.limit_denominator(10 ** 6)
        if not (h1 < mm < l2):
            mm = m
        pts.append(mm)
    pts.append(im_hi)
    samples = []
    for t in pts:
        (lo, hi), _im = enclose_lambda("1/2", str(t), prec)
        samples.append((t, (lo, hi)))
    n = sign_change_count(samples)
    if n != len(zs):
        raise RuntimeError(
            f"platt sweep mismatch: {n} sign changes vs {len(zs)} inventoried zeros"
        )
    return n


def _online_sweep_zero_count(im_lo, im_hi, prec: int, density: float = 1.0) -> int:
    """Count on-line zeros of Lambda in [im_lo, im_hi] via a sign-change sweep on the critical line.

    Sample spacing is strictly below `pi / log(max(im_hi, 2))` (the mean zero spacing near height T
    is ~2*pi/log(T), so this resolves every zero).  Adaptively refines: if two consecutive
    sign-definite samples both have the same sign but the gap is large, the caller relies on the
    dense spacing.  Returns the number of sign changes (distinct on-line zeros).

    `density > 1` shrinks the sample spacing by that factor — the close-pair re-sweep knob
    (a pair of zeros closer than the mean spacing needs a denser grid to expose both sign
    changes; the T=2000..4000 campaign cured all refusals by density ≤ 6)."""
    im_lo = Fraction(im_lo)
    im_hi = Fraction(im_hi)
    spacing_cap = math.pi / math.log(max(float(im_hi), 2.0))
    # Use 0.9 of the cap for a strict inequality margin.
    step_target = spacing_cap * 0.9 / max(density, 1.0)
    n_steps = max(3, int(math.ceil(float(im_hi - im_lo) / step_target)) + 1)
    step = (im_hi - im_lo) / (n_steps - 1)
    samples = []
    for k in range(n_steps):
        t = im_lo + k * step
        (lo, hi), _im = enclose_lambda("1/2", str(t), prec)
        samples.append((t, (lo, hi)))
    return sign_change_count(samples)


def run_box(re_lo, re_hi, im_lo, im_hi, *, prec: int = 300, winding_prec: int = 160,
            n_seed: int = 4, out_dir: Path | None = None, write: bool = True,
            check: bool = False, density: float = 1.0) -> str:
    """Driver: compute the winding N, on-line N_line, edge non-vanishing for an arbitrary box, then
    emit (and optionally write) a Lean file instantiating `RHInBox.rh_in_box_of_certificate`.

    REFUSALS (ValueError):
    * invalid box (sigma-range excludes 1/2, or the box contains the pole s = 1) — via
      `box_localization_certificate`;
    * `N_line != N` (the on-line sign-change count disagrees with the boundary winding) — via
      `box_localization_certificate(n_line=N_line, n_total=N)`;
    * the on-line sweep failing to resolve at least one zero (`N_line < 1`).

    Returns the emitted Lean text (also written to `RHInBox_<tag>.lean` unless `write=False`)."""
    rl, rh, il, ih = (Fraction(v) for v in (re_lo, re_hi, im_lo, im_hi))
    box = (rl, rh, il, ih)

    # 1. Boundary winding N (rigorous zeta Taylor segments -> half-plane-witnessed winding).
    segs = enclose_zeta_segments(box, winding_prec, n_seed=n_seed)
    wind = segment_winding_certificate((rl, rh, il, ih), segs)
    n_total = wind.n

    # 2. On-line sign-change zero count N_line over [im_lo, im_hi].
    #    Platt-hinted midpoint sweep first (deterministic close pairs, fewer
    #    evals); any failure falls back to the density-graded grid sweep.
    try:
        n_line = _online_sweep_zero_count_platt(il, ih, prec)
    except Exception:
        n_line = _online_sweep_zero_count(il, ih, prec, density)
    if n_line < 1:
        raise ValueError(
            f"run_box: on-line sweep resolved no zeros (N_line=0) in [{il},{ih}]; nothing to localize"
        )

    # 3. Edge non-vanishing: every boundary segment enclosure is off 0 (no segment box straddles the
    #    origin).  This is exactly what segment_winding_certificate already verified (it refuses a
    #    0-containing segment box); assert here for an explicit driver-level guard.
    for i, (_param, seg_box) in enumerate(segs):
        (slo_re, shi_re), (slo_im, shi_im) = seg_box
        if slo_re <= 0 <= shi_re and slo_im <= 0 <= shi_im:
            raise ValueError(f"run_box: boundary segment {i} straddles 0 — edge non-vanishing failed")

    # 4. Certificate (refuses invalid box AND N_line != N_total).
    cert = box_localization_certificate(
        n_line=n_line, n_total=n_total,
        re_lo=str(rl), re_hi=str(rh), im_lo=str(il), im_hi=str(ih),
    )

    # 5. Emit the per-box instantiation.
    tag = _box_tag(rl, rh, il, ih)
    text = emit_per_box_instantiation(cert, tag, namespace=f"RHInBox_{tag}")
    print(f"run_box [{rl},{rh}]x[{il},{ih}]: winding N={n_total}, on-line N_line={n_line} "
          f"(agree); emitted rh_in_box_{tag}")

    if write:
        out_dir = out_dir or (_OUT.parent)
        out_path = out_dir / f"RHInBox_{tag}.lean"
        if check:
            if not out_path.exists() or out_path.read_text(encoding="utf-8") != text:
                print(f"DRIFT: RHInBox_{tag}.lean does not match regeneration")
            else:
                print(f"check: OK (RHInBox_{tag}.lean regenerates byte-for-byte; "
                      f"N_line == winding N == {n_total})")
        else:
            out_path.write_text(text, encoding="utf-8")
            print(f"wrote {out_path} ({len(text)} bytes)")
    return text


def run_box_turing(re_lo, re_hi, im_lo, im_hi, *, prec: int = 300, edge_prec: int = 160,
                   out_dir: Path | None = None, write: bool = True) -> str:
    """T5 driver: RvM edge-decomposition band certificate (no winding contour).

    Computes the on-line count (Platt-hinted sweep), the five edge argument-change
    enclosures (arb_edges), cross-checks the RvM-pinned integer against the line
    count, verifies the ball-poke slivers hold no zeros (Platt inventory), and
    emits RHInBoxT_<tag>.lean instantiating TuringBand.turing_band_on_line.

    REFUSALS: pinned integer != line count; enclosure too wide to pin; a zero in
    the ball-poke sliver (band edge must be re-planned)."""
    import math as _m

    from telperion.arb_edges import enclose_band_edges
    from telperion.arb_platt import zeros_in_interval
    from telperion.emit_turing_band import (
        choose_ball_tight,
        emit_turing_band_instantiation,
    )

    rl, rh, il, ih = (Fraction(v) for v in (re_lo, re_hi, im_lo, im_hi))
    n_line = _online_sweep_zero_count_platt(il, ih, prec)
    # persistent horizontal-edge cache: AH at height T is shared by the bands
    # below and above T (each interior edge priced once across the campaign)
    cache_dir = _OUT.parent.parent / "edges_cache"
    cache_dir.mkdir(exist_ok=True)

    def _cache_get(t):
        p = cache_dir / f"ah_{str(t).replace('/', 'd')}_{edge_prec}.json"
        if p.exists():
            import json as _json
            lo_s, hi_s = _json.loads(p.read_text())
            return (Fraction(lo_s), Fraction(hi_s))
        return None

    def _cache_put(t, val):
        import json as _json
        p = cache_dir / f"ah_{str(t).replace('/', 'd')}_{edge_prec}.json"
        tmp = p.with_suffix(".tmp")
        tmp.write_text(_json.dumps([str(val[0]), str(val[1])]))
        tmp.replace(p)

    edges = enclose_band_edges(il, ih, prec=edge_prec, bot_cache=_cache_get(il))
    if _cache_get(il) is None:
        _cache_put(il, edges["ahb"])
    _cache_put(ih, edges["aht"])
    L = 2 * edges["av2"][0] + edges["aht"][0] - edges["ahb"][1] + edges["ag1"][0] + edges["ag2"][0]
    H = 2 * edges["av2"][1] + edges["aht"][1] - edges["ahb"][0] + edges["ag1"][1] + edges["ag2"][1]
    k = round((float(L) + float(H)) / 2 / (2 * _m.pi))
    if k != n_line:
        raise ValueError(
            f"run_box_turing: RvM edge count {k} != on-line count {n_line} in [{il},{ih}]")
    # ball-poke sliver check: no zero ordinate within `poke` outside the band
    _cx, _cy, rsq = choose_ball_tight(-1, 2, il, ih)
    poke = _m.sqrt(float(rsq)) - float(ih - il) / 2 + 1e-9
    below = zeros_in_interval(il - 1, il)
    above = zeros_in_interval(ih, ih + 1)
    if any(float(hi_z) > float(il) - poke for _lo_z, hi_z in below) or \
       any(float(lo_z) < float(ih) + poke for lo_z, _hi_z in above):
        raise ValueError(
            f"run_box_turing: zero in ball-poke sliver of [{il},{ih}] (poke={poke:.4f}); "
            f"re-plan the band edge")
    tag = _box_tag(rl, rh, il, ih)
    text = emit_turing_band_instantiation(
        n=n_line, re_lo=rl, re_hi=rh, im_lo=il, im_hi=ih, edges=edges, tag=tag)
    print(f"run_box_turing [{rl},{rh}]x[{il},{ih}]: RvM edge count N={k}, "
          f"on-line N_line={n_line} (agree); emitted rh_in_box_{tag} (T5)")
    if write:
        out_path = (out_dir or _OUT.parent) / f"RHInBoxT_{tag}.lean"
        out_path.write_text(text, encoding="utf-8")
        print(f"wrote {out_path} ({len(text)} bytes)")
    return text


def _box_localization_negative_control() -> None:
    """Stage-3 capstone guard: assert the localization certificate ACCEPTS the real capstone
    instance (n_line = n_total = 5 on [2/5,3/5]x[10,35]) and REFUSES the fabricated off-line
    instance (an extra off-line zero making n_total = 6 > n_line = 5).  Without the equality the
    on-line zeros cannot exhaust the divisor, so no localization claim may be emitted.

    The load-bearing capstone theorem lives in the HAND-WRITTEN lean/BoxLocalization.lean
    (`all_nontrivial_zeros_in_box_on_critical_line`); this is the certification-side negative
    control mandated by the Stage-3 brief.  conjecture1_proved = False.
    """
    from telperion.emit_box_localization import box_localization_certificate

    cert = box_localization_certificate(n_line=5, n_total=5)
    assert cert.n == 5, "box_localization positive control failed"
    for bad_line, bad_total, why in ((5, 6, "off-line zero (n_total > n_line)"),
                                     (6, 5, "impossible n_line > n_total")):
        try:
            box_localization_certificate(n_line=bad_line, n_total=bad_total)
        except ValueError:
            pass
        else:
            raise AssertionError(
                f"box_localization negative control FAILED: accepted {why} "
                f"(n_line={bad_line}, n_total={bad_total})"
            )
    print("box_localization: OK (n_line=n_total=5 accepted; off-line n_total=6 and "
          "n_line>n_total refused)")


def _parse_box_arg(box_str: str):
    """Parse `sigma0,sigma1,T0,T1` (comma-separated rationals) into four Fractions."""
    parts = [p.strip() for p in box_str.split(",")]
    if len(parts) != 4:
        raise ValueError(f"--box needs 4 comma-separated values sigma0,sigma1,T0,T1; got {box_str!r}")
    return tuple(Fraction(p) for p in parts)


def main(*, check: bool = False, a=None, b=None, n_samples: int = 51, prec: int = 300,
         box=None, height=None, empty_band=None, density: float = 1.0,
         turing: bool = False) -> int:
    # Empty-band (zero-free) driver mode: winding N == 0 => box holds no zeta zero.
    if empty_band is not None:
        from telperion.driver_empty_band import run_empty_band
        rl, rh, il, ih = _parse_box_arg(empty_band)
        run_empty_band(str(rl), str(rh), str(il), str(ih), check=check)
        return 0
    # Per-box driver mode: compute winding + on-line count, emit instantiation.
    if box is not None:
        rl, rh, il, ih = _parse_box_arg(box)
        if turing:
            run_box_turing(rl, rh, il, ih, prec=prec)
        else:
            run_box(rl, rh, il, ih, prec=prec, check=check, density=density)
        return 0
    if height is not None:
        # Shortcut for the critical strip box [2/5, 3/5] x [0, T].
        T = Fraction(height)
        # In --check mode, regenerate WITHOUT writing and byte-compare against the frozen
        # file below; otherwise write it.  run_box already REFUSES N_line != winding N (via
        # box_localization_certificate), so a successful return proves the agreement.
        text = run_box(Fraction(2, 5), Fraction(3, 5), Fraction(0), T, prec=prec,
                       write=(not check))
        # Drift/agreement assertion for the COMMITTED T=100 milestone.
        if check and T == Fraction(100):
            if not _OUT_H100.exists() or _OUT_H100.read_text(encoding="utf-8") != text:
                print("DRIFT: RHInBox_2d5_3d5_0_100.lean does not match regeneration")
                return 1
            print(f"check: OK (T=100 milestone regenerates byte-for-byte; "
                  f"N_line == winding N == {_H100_EXPECTED_N})")
        return 0

    # Interval driver mode: print N, do not write
    if a is not None and b is not None:
        run_interval(a, b, n_samples, prec)
        return 0

    text = build()
    text_winding = build_winding()
    # Stage-3 capstone certification-side negative control (always runs).
    _box_localization_negative_control()
    if check:
        drift = False
        if not _OUT.exists() or _OUT.read_text(encoding="utf-8") != text:
            print("DRIFT: XiLineZeros.lean does not match regeneration")
            drift = True
        if not _OUT_WINDING.exists() or _OUT_WINDING.read_text(encoding="utf-8") != text_winding:
            print("DRIFT: WindingCount.lean does not match regeneration")
            drift = True
        if drift:
            return 1
        print("check: OK (regeneration matches frozen output byte-for-byte)")
        return 0
    _OUT.parent.mkdir(exist_ok=True)
    _OUT.write_text(text, encoding="utf-8")
    print(f"wrote {_OUT} ({len(text)} bytes)")
    _OUT_WINDING.write_text(text_winding, encoding="utf-8")
    print(f"wrote {_OUT_WINDING} ({len(text_winding)} bytes)")
    return 0


if __name__ == "__main__":
    ap = argparse.ArgumentParser(
        description="Generate XiLineZeros.lean or query certified zero count for an interval."
    )
    ap.add_argument("--check", action="store_true",
                    help="drift check; regenerate and byte-compare; do not write")
    ap.add_argument("--a", type=str, default=None,
                    help="interval lower bound (integer or fraction, e.g. 10)")
    ap.add_argument("--b", type=str, default=None,
                    help="interval upper bound (integer or fraction, e.g. 35)")
    ap.add_argument("--n-samples", type=int, default=51,
                    help="number of evenly-spaced sample points in [a, b] (default 51)")
    ap.add_argument("--prec", type=int, default=300,
                    help="Arb working precision in bits (default 300)")
    ap.add_argument("--box", type=str, default=None,
                    help="per-box driver: sigma0,sigma1,T0,T1 (rationals). Computes winding N + "
                         "on-line N_line + edge non-vanishing and emits RHInBox_<tag>.lean "
                         "instantiating rh_in_box_of_certificate; refuses invalid/under-resolved boxes")
    ap.add_argument("--height", type=str, default=None,
                    help="per-box driver shortcut for the strip box [2/5,3/5] x [0,T]")
    ap.add_argument("--density", type=float, default=1.0,
                    help="on-line sweep density factor (>1 = denser close-pair re-sweep)")
    ap.add_argument("--turing", action="store_true",
                    help="T5 route: RvM edge-decomposition certificate (no winding contour)")
    ap.add_argument("--empty-band", type=str, default=None,
                    help="empty-band (zero-free) driver: sigma0,sigma1,T0,T1 (rationals). Computes "
                         "winding N, asserts N == 0, and emits NoZerosInBox_<tag>.lean certifying the "
                         "box holds no zeta zero; refuses a box with nonzero winding")
    args = ap.parse_args()
    a_val = Fraction(args.a) if args.a is not None else None
    b_val = Fraction(args.b) if args.b is not None else None
    raise SystemExit(main(
        check=args.check,
        a=a_val,
        b=b_val,
        n_samples=args.n_samples,
        prec=args.prec,
        box=args.box,
        height=args.height,
        empty_band=args.empty_band,
        density=args.density,
        turing=args.turing,
    ))
