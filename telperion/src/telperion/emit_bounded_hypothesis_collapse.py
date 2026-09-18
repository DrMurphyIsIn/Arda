"""BoundedHypothesisCollapse emitter (kind ``bounded_hypothesis_collapse``) --
a TRIVIALITY certificate for a registry STATEMENT SHAPE, not for a theorem.

The shape it audits
-------------------
A recurring proposal in the RH-adjacent registries reads

    exists C >= 0, forall T >= T0,  P(T)  ->  -(C * log T / T^k) <= W        (S)

with a decaying error term, a height-indexed hypothesis family ``P`` (typically
"every zero below height T is on the critical line" -- the certified zero
ladder), and a conclusion ``W`` that does NOT depend on ``T`` (typically the Weil
functional of a fixed test function).  The shape LOOKS quantitative.  It is not:

  * if ``W >= 0`` the choice ``C := 0`` closes it, and
  * if ``W < 0`` then (S) is still closable whenever ``P`` fails above some finite
    height ``B``, because the hypothesis then confines ``T`` to ``[T0, B]``, where
    ``log T / T^k`` has a positive minimum -- so a large enough constant works.

Classically one of the two cases always holds (either the intended positivity is
true, or the hypothesis family is falsified at some finite height), so (S) is a
theorem of excluded middle: a ``by_cases`` on RH closes it with no mathematics.
The intended content -- summability of the truncated sum, the tail estimate, the
on-line square channel -- is entirely absent from (S).

What this emitter certifies
---------------------------
Per instance it emits a real Lean theorem, the COLLAPSE WITNESS: for the audited
``(T0, k)``, an explicit constant

    C* = max 0 (-W) * B^k / log T0

closes (S) for every ``W``, every hypothesis family ``P``, and every finite
failure height ``B >= T0``.  The constant is IN the statement, so it is the
corruptible certificate: emit ``B^(k-1)``, or the log of a different base, and
the proof breaks.  A statement author who sees this theorem knows the audited
shape carries no content and must be re-shaped (the standard repair: hoist the
conjuncts that do NOT need the hypothesis OUT of the implication, so the
hypothesis-free part must hold at every height and the case split cannot help).

Refusals (the negative controls, all at certify time)
-----------------------------------------------------
  * ``k <= 0``     -- no decay, so the shape is not of this family;
  * ``T0 <= 1``    -- ``log T0 <= 0``, the constant is not well formed;
  * ``B < T0``     -- the hypothesis range is EMPTY: the shape is vacuous, a
                      different (and more obvious) defect, named rather than
                      silently folded into the collapse;
  * a sample with ``W >= 0`` -- collapse by ``C := 0``, the benign case; the
                      adversarial case ``W < 0`` is the one worth certifying;
  * a probe height outside ``[T0, B]`` -- outside the range the hypothesis can
                      hold, so it witnesses nothing;
  * no samples at all.

HONESTY: this refutes a SHAPE, never a piece of mathematics.  It says nothing
about whether the intended inequality is true -- only that the sentence as
written does not express it.  ``conjecture1_proved = False``.
"""
from __future__ import annotations

from dataclasses import dataclass
from typing import Callable, Sequence

import sympy as sp

from .certify import CertifiedInstance
from .expr import rat_lean
from .family import GridSpec, InequalityFamily
from .lean import LeanProfile
from .workflow import Emitter


@dataclass(frozen=True)
class BoundedHypothesisCollapseCert:
    """One statement-shape collapse certificate.

    ``T0`` is the lower height bound of the audited shape, ``k`` its decay
    exponent, and ``samples`` a tuple of ``(W, B, T, C_star, margin)`` witnesses:
    ``W < 0`` is an adversarial conclusion value, ``B >= T0`` a finite height above
    which the hypothesis family fails, ``T in [T0, B]`` a probe height, ``C_star``
    the collapsing constant ``-W * B^k / log T0`` and ``margin`` the exact slack
    ``C_star * log T / T^k - (-W) >= 0`` (zero only at the corner ``T = B``,
    ``T0 = T``)."""

    T0: sp.Rational
    k: int
    samples: tuple  # ((W, B, T, C_star, margin), ...)


def _collapse_constant(W: sp.Rational, B: sp.Rational, T0: sp.Rational, k: int) -> sp.Expr:
    """The exact collapsing constant ``max(0, -W) * B^k / log T0``."""
    M = sp.Max(sp.Integer(0), -W)
    return M * B ** k / sp.log(T0)


def bounded_hypothesis_collapse_certificate(
    T0, k: int, samples: Sequence[Sequence],
) -> BoundedHypothesisCollapseCert:
    """Build and EXACTLY re-check the collapse certificate for the shape

        exists C >= 0, forall T >= T0, P(T) -> -(C * log T / T^k) <= W.

    ``samples`` is a sequence of ``(W, B, T)`` triples.  Each is re-checked: the
    collapsing constant is computed, and the slack
    ``C_star * log T / T^k - (-W)`` is verified nonnegative -- structurally, from
    ``T^k <= B^k`` and ``log T0 <= log T``, and numerically to 40 digits.  See the
    module docstring for the refusal list."""
    T0 = sp.Rational(sp.nsimplify(T0))
    k = int(k)
    if k <= 0:
        raise ValueError(
            f"bounded_hypothesis_collapse REFUSED: need a decaying error term k >= 1; got k={k}")
    if T0 <= 1:
        raise ValueError(
            f"bounded_hypothesis_collapse REFUSED: need T0 > 1 so that log T0 > 0; got T0={T0}")
    if not len(samples):
        raise ValueError(
            "bounded_hypothesis_collapse REFUSED: no samples -- a collapse claim with no "
            "adversarial witness certifies nothing")
    out = []
    for raw in samples:
        W, B, T = (sp.Rational(sp.nsimplify(x)) for x in raw)
        if W >= 0:
            raise ValueError(
                f"bounded_hypothesis_collapse REFUSED: sample W={W} >= 0 collapses by the "
                "benign route C := 0; supply the adversarial case W < 0")
        if B < T0:
            raise ValueError(
                f"bounded_hypothesis_collapse REFUSED: B={B} < T0={T0} -- the hypothesis range "
                "is EMPTY, so the shape is vacuous rather than collapsed (a different defect)")
        if not (T0 <= T <= B):
            raise ValueError(
                f"bounded_hypothesis_collapse REFUSED: probe height T={T} outside [T0, B] = "
                f"[{T0}, {B}] -- the hypothesis cannot hold there, so it witnesses nothing")
        C_star = _collapse_constant(W, B, T0, k)
        # No sp.simplify here: the log-of-large-rational expressions blow up symbolic
        # simplification; the sign is settled structurally below and numerically to 40 digits.
        margin = C_star * sp.log(T) / T ** k + W
        # Structural check: B^k >= T^k and log T >= log T0 > 0, so the margin is >= 0.
        if not (T ** k <= B ** k and sp.log(T0) <= sp.log(T)):
            raise ValueError(
                f"bounded_hypothesis_collapse REFUSED: monotonicity broken at T={T} "
                "(the collapse argument needs T^k <= B^k and log T0 <= log T)")
        if sp.Float(margin.evalf(40)) < 0:
            raise ValueError(
                f"bounded_hypothesis_collapse REFUSED: computed margin {margin} is negative at "
                f"W={W}, B={B}, T={T} -- the constant does not close the shape")
        out.append((W, B, T, C_star, margin))
    return BoundedHypothesisCollapseCert(T0=T0, k=k, samples=tuple(out))


def certify_bounded_hypothesis_collapse_point(family, pt, name):
    """Certify one collapse instance: ``(CertifiedInstance, n_checks)``.

    Reads ``(T0, k, samples) = family.special[1](pt)``; ``n_checks`` is the number
    of exactly re-checked adversarial samples."""
    T0, k, samples = family.special[1](pt)
    cert = bounded_hypothesis_collapse_certificate(T0, k, samples)
    inst = CertifiedInstance(
        point=dict(pt), lean_name=name, corners=(), payload=cert)
    return inst, len(cert.samples)


@dataclass
class BoundedHypothesisCollapseEmitter(Emitter):
    """Emit, per instance, the COLLAPSE WITNESS for an audited statement shape:
    the explicit constant ``max 0 (-W) * B^k / log T0`` closes

        exists C >= 0, forall T >= T0, P T -> -(C * log T / T^k) <= W

    for every ``W``, every hypothesis family ``P`` and every finite height ``B``
    above which ``P`` fails.  A real Lean theorem (Mathlib ``Real.log``), whose
    explicit constant is the corruptible certificate.  It certifies that the
    AUDITED SHAPE is contentless; it proves nothing about the intended
    mathematics."""

    def __post_init__(self):
        self.kind = "bounded_hypothesis_collapse"

    def emit_body(self, fam, profile: LeanProfile) -> tuple[str, int]:
        lines: list[str] = []
        n_thm = 0
        for inst in fam.instances:
            cert: BoundedHypothesisCollapseCert = inst.payload  # type: ignore[assignment]
            nm = inst.lean_name
            t0 = rat_lean(cert.T0)
            k = cert.k
            sample_txt = "; ".join(
                f"W={W}, B={B}, T={T}" for W, B, T, _, _ in cert.samples)
            lines.append(
                f"-- {nm}: STATEMENT-SHAPE COLLAPSE witness (kind bounded_hypothesis_collapse).\n"
                f"-- The shape `exists C >= 0, forall T >= {cert.T0}, P T -> -(C * log T / T^{k}) <= W`\n"
                f"-- is closed, for EVERY W and EVERY hypothesis family P that fails above some\n"
                f"-- finite height B, by the explicit constant max 0 (-W) * B^{k} / log {cert.T0}.\n"
                f"-- Hence the shape carries none of its intended content: a classical case split\n"
                f"-- (RH true -> W >= 0 -> C := 0; RH false -> the ladder hypothesis is falsified\n"
                f"-- above a finite height -> this constant) closes it with no mathematics.\n"
                f"-- Exactly re-checked adversarial samples: {sample_txt}.\n"
                f"-- Refutes a SHAPE, not a theorem.  conjecture1_proved = False.\n"
                f"theorem {nm} (W : ℝ) (Pr : ℝ → Prop) (B : ℝ) (hB : ({t0} : ℝ) ≤ B)\n"
                f"    (hfail : ∀ T : ℝ, B < T → ¬ Pr T) :\n"
                f"    (0 : ℝ) ≤ max 0 (-W) * B ^ {k} / Real.log {t0} ∧\n"
                f"      ∀ T : ℝ, ({t0} : ℝ) ≤ T → Pr T →\n"
                f"        -(max 0 (-W) * B ^ {k} / Real.log {t0} * Real.log T / T ^ {k}) ≤ W := by\n"
                f"  have hT0pos : (0 : ℝ) < {t0} := by norm_num\n"
                f"  have hlogT0 : 0 < Real.log {t0} := Real.log_pos (by norm_num)\n"
                f"  have hM : (0 : ℝ) ≤ max 0 (-W) := le_max_left _ _\n"
                f"  have hBpos : (0 : ℝ) < B := lt_of_lt_of_le hT0pos hB\n"
                f"  refine ⟨by positivity, ?_⟩\n"
                f"  intro T hT hP\n"
                f"  have hTB : T ≤ B := by\n"
                f"    by_contra hcon\n"
                f"    exact hfail T (lt_of_not_ge hcon) hP\n"
                f"  have hTpos : (0 : ℝ) < T := lt_of_lt_of_le hT0pos hT\n"
                f"  have hTk : (0 : ℝ) < T ^ {k} := pow_pos hTpos {k}\n"
                f"  have hBk : T ^ {k} ≤ B ^ {k} := pow_le_pow_left₀ hTpos.le hTB {k}\n"
                f"  have hlogT : Real.log {t0} ≤ Real.log T := Real.log_le_log hT0pos hT\n"
                f"  have h1 : Real.log {t0} * T ^ {k} ≤ B ^ {k} * Real.log T := by\n"
                f"    calc Real.log {t0} * T ^ {k} ≤ Real.log {t0} * B ^ {k} := by nlinarith\n"
                f"      _ ≤ Real.log T * B ^ {k} := by nlinarith [pow_pos hBpos {k}]\n"
                f"      _ = B ^ {k} * Real.log T := by ring\n"
                f"  have h2 := mul_le_mul_of_nonneg_left h1 hM\n"
                f"  have hkey : max 0 (-W)\n"
                f"      ≤ max 0 (-W) * B ^ {k} / Real.log {t0} * Real.log T / T ^ {k} := by\n"
                f"    rw [div_mul_eq_mul_div, div_div, le_div_iff₀ (by positivity)]\n"
                f"    calc max 0 (-W) * (Real.log {t0} * T ^ {k})\n"
                f"        ≤ max 0 (-W) * (B ^ {k} * Real.log T) := h2\n"
                f"      _ = max 0 (-W) * B ^ {k} * Real.log T := by ring\n"
                f"  have hW : -W ≤ max 0 (-W) := le_max_right _ _\n"
                f"  linarith\n"
            )
            n_thm += 1
        return "\n".join(lines), n_thm


def bounded_hypothesis_collapse_family(
    name: str,
    grid: GridSpec,
    lean_name: Callable,
    spec: Callable,
    constants: dict | None = None,
) -> InequalityFamily:
    """Build a collapse-audit family (kind ``bounded_hypothesis_collapse``).

    ``spec: pt -> (T0, k, samples)`` -- ``T0 > 1`` the audited shape's lower height
    bound, ``k >= 1`` its decay exponent, ``samples`` a finite list of adversarial
    ``(W, B, T)`` triples with ``W < 0`` and ``T0 <= T <= B``.  The emitted theorem
    is abstract in ``W``, ``P`` and ``B``; the samples are the python-side exact
    self-check that the collapse is real rather than sign-degenerate."""
    return InequalityFamily(
        name=name,
        symbols=(sp.Symbol("T", positive=True),),
        grid=grid,
        lean_name=lean_name,
        special=("bounded_hypothesis_collapse", spec),
        constants=dict(constants or {}),
    )
