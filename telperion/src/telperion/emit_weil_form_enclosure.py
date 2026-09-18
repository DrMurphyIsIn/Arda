"""Weil-form enclosure emitter (`weil_form_enclosure`) -- the certificate shape the MIRRORMERE
W3c membership goal was missing.

conjecture1_proved = False.  Nothing here proves, approaches or claims RH.

WHY THIS EMITTER EXISTS
-----------------------
The MIRRORMERE goal node `MM_zeta_comb_membership` (design memo
telperion/docs/MM_w3c_goal_weil_membership_DESIGN_2026-09-18.md) states defect-0 membership of
the Guinand-Weil regularized triple as Weil positivity of the primes-side functional

    W(g) := Re (WeilExplicit.weilForm (WeilExplicit.autocorr g)),
    weilForm f = archSide f - primeSide f

over the test class `WeilExplicit.IsWeilTest`.  That statement is RH-EQUIVALENT (Weil 1952;
Bombieri 2000 on C_c^infinity), so it is never attempted.  What IS finite, checkable and
falsifiable is the VALUE of W at one explicit test function: a rigorous two-sided rational
enclosure `lo <= W(g) <= hi`.  Before this emitter the registry had no certificate kind for
that shape -- the roadmap's finite faces of A5 (D2's Weil-Gram matrix, D3's certified-height
bound) both consume exactly this datum, and the goal's mandatory numeric read-back (does the
sentence have honest, order-one values, or is it a junk-Bochner-integral zero?) is the same
computation.  This kind fills that gap.

WHAT THE EMITTED THEOREMS CERTIFY (read before citing)
------------------------------------------------------
`weil_form_enclosure_<name>` is a pure rational implication: GIVEN the Arb-enclosed bounds
as hypotheses (`lo <= W` and `W <= hi`), it concludes `0 < W` (or `W < 0` in the refutation
branch) together with the order-of-magnitude reading `W <= hi`.  The enclosure itself is the
documented non-kernel trust seam (python-flint ball arithmetic, backend
`telperion.weil_gauss`), exactly as in the Li ladder and the Bragg floor: a FORGED enclosure
falsifies the hypothesis and leaves the implication kernel-valid.

The bridge from `W` to the registry vocabulary -- that this rational number IS
`Re (weilForm (autocorr g))` for the g in question -- is NOT discharged here and is NOT
claimed: it is carried as an explicit hypothesis `heval` in the membership face, whose
discharge for a concrete g is an analytic evaluation problem (the D2/D3 finite faces).

THE FALSIFIABILITY FACE (this is an experiment, not a confirmation ritual)
--------------------------------------------------------------------------
`weil_form_neg_refutes_rh` says: given Weil's criterion in the forward direction as an
UNDISCHARGED hypothesis (`hcrit : RiemannHypothesis -> forall f, IsTest f -> 0 <= Wre f`,
classical, not in Mathlib), a certified STRICTLY NEGATIVE enclosure at an admissible g
refutes RH.  The instrument could therefore have falsified; it does not (every instance we
can certify is positive, in agreement with the independently computed zero-side sum).  The
face is stated over abstract `Wre`/`IsTest` parameters so the emitted file elaborates against
bare Mathlib and no vocabulary is duplicated a third time; the instantiation at
`WeilExplicit.weilForm . autocorr` lives in the mirrormere probe file.

REFUSALS (honest, never a false theorem)
----------------------------------------
`weil_form_certificate` refuses: an inconsistent enclosure (`lo > hi`); an enclosure that
STRADDLES zero (the sign is simply not decided at this precision -- raise the precision or
the truncation, do not emit); and an enclosure that CONTRADICTS the independently computed
zero-side reading of the same functional, when one is supplied (`zero_side_lo/hi` outside
`[lo, hi]` means a normalisation bug in one of the two readings -- the E8 identity is the
cross-check, and a mismatch aborts rather than ships).
"""
from __future__ import annotations

from dataclasses import dataclass
from typing import Callable, Optional

import sympy as sp

from .certify import CertifiedInstance
from .expr import rat_lean
from .family import GridSpec, InequalityFamily
from .lean import LeanProfile
from .workflow import Emitter


@dataclass(frozen=True)
class WeilFormData:
    """Arb-enclosed input for one instance: the label, the enclosure, and the optional
    independent zero-side reading of the same functional (the E8 cross-check)."""

    label: str
    lo: sp.Rational
    hi: sp.Rational
    zero_side_lo: Optional[sp.Rational] = None
    zero_side_hi: Optional[sp.Rational] = None
    note: str = ""


@dataclass(frozen=True)
class WeilFormCert:
    """One certified Weil-form enclosure.  `sign` is "pos" or "neg"; a straddling enclosure is
    refused at construction, so `sign` is always decided."""

    label: str
    lo: sp.Rational
    hi: sp.Rational
    sign: str
    note: str = ""

    @property
    def margin(self) -> sp.Rational:
        """Distance of the enclosure from zero: `lo` when positive, `-hi` when negative."""
        return sp.Rational(self.lo if self.sign == "pos" else -self.hi)


def weil_form_certificate(data: WeilFormData) -> WeilFormCert:
    """Validate and re-check one Weil-form enclosure.  See the module docstring for the three
    refusals; each raises rather than emitting a vacuous or false theorem."""
    lo, hi = sp.Rational(data.lo), sp.Rational(data.hi)
    if lo > hi:
        raise ValueError(
            f"weil_form REFUSED [{data.label}]: inconsistent enclosure lo={lo} > hi={hi}")
    if lo <= 0 <= hi:
        raise ValueError(
            f"weil_form REFUSED [{data.label}]: enclosure [{lo}, {hi}] straddles zero -- the "
            f"sign of the Weil form is NOT decided at this precision; raise the working "
            f"precision or the truncations, do not emit")
    if data.zero_side_lo is not None and data.zero_side_hi is not None:
        zlo, zhi = sp.Rational(data.zero_side_lo), sp.Rational(data.zero_side_hi)
        if zhi < lo or zlo > hi:
            raise ValueError(
                f"weil_form REFUSED [{data.label}]: the primes-side enclosure [{lo}, {hi}] and "
                f"the independent zero-side reading [{zlo}, {zhi}] are DISJOINT -- the two "
                f"sides of the explicit formula disagree, which is a normalisation bug, not a "
                f"certificate")
    return WeilFormCert(label=data.label, lo=lo, hi=hi,
                        sign="pos" if lo > 0 else "neg", note=data.note)


def certify_weil_form_point(family, pt, name):
    """Certify one Weil-form instance: `(CertifiedInstance, 1)`."""
    data = family.special[1](pt)
    cert = weil_form_certificate(data)
    inst = CertifiedInstance(point=dict(pt), lean_name=name, corners=(), payload=cert)
    return inst, 1


@dataclass
class WeilFormEnclosureEmitter(Emitter):
    """Emit `lo <= W -> W <= hi -> 0 < W and W <= hi` (or the negative branch) from an
    Arb-enclosed rational pair.  Deterministic `norm_num` on the literal comparison only; the
    enclosure hypotheses carry the numeric trust seam."""

    def __post_init__(self):
        self.kind = "weil_form_enclosure"

    def emit_body(self, fam, profile: LeanProfile) -> tuple[str, int]:
        lines: list[str] = []
        n_thm = 0
        for inst in fam.instances:
            cert: WeilFormCert = inst.payload  # type: ignore[assignment]
            lo, hi = rat_lean(cert.lo), rat_lean(cert.hi)
            nm = inst.lean_name
            head = (
                f"-- {nm}: certified enclosure of the Weil form W = Re (weilForm (autocorr g))\n"
                f"-- at the test function {cert.label}: {cert.lo} <= W <= {cert.hi}"
                f"{(' -- ' + cert.note) if cert.note else ''}.\n"
                f"-- Trust seam: lo/hi are Arb (python-flint) enclosures produced by\n"
                f"-- telperion.weil_gauss (closed forms anchored against the DEFINING integrals of\n"
                f"-- WeilExplicit.autocorr / weilKernel, and cross-checked against the independent\n"
                f"-- zero-side reading of the same functional).  A forged enclosure falsifies the\n"
                f"-- hypotheses and leaves this implication kernel-valid.\n"
                f"-- This is a FINITE value certificate at ONE test function.  It proves NOTHING\n"
                f"-- about RH: the registry goal MM_zeta_comb_membership quantifies over the whole\n"
                f"-- class and is RH-equivalent (Weil 1952 / Bombieri 2000).\n"
                f"-- conjecture1_proved = False.\n"
            )
            if cert.sign == "pos":
                lines.append(
                    head
                    + f"theorem {nm} (W : ℝ) (hlo : ({lo} : ℝ) ≤ W) (hhi : W ≤ ({hi} : ℝ)) :\n"
                    + f"    (0 : ℝ) < W ∧ W ≤ ({hi} : ℝ) :=\n"
                    + f"  ⟨lt_of_lt_of_le (by norm_num) hlo, hhi⟩\n"
                )
            else:
                lines.append(
                    head
                    + f"theorem {nm} (W : ℝ) (hlo : ({lo} : ℝ) ≤ W) (hhi : W ≤ ({hi} : ℝ)) :\n"
                    + f"    W < (0 : ℝ) ∧ ({lo} : ℝ) ≤ W :=\n"
                    + f"  ⟨lt_of_le_of_lt hhi (by norm_num), hlo⟩\n"
                )
            n_thm += 1
        return "\n".join(lines), n_thm


def weil_form_neg_refutes_rh_lean() -> str:
    """The falsifiability face, emitted once per generated file.

    A certified STRICTLY NEGATIVE Weil form at an admissible test function refutes RH -- through
    Weil's criterion in the forward direction, carried as the UNDISCHARGED hypothesis `hcrit`
    (classical: Weil 1952, Bombieri 2000; not in Mathlib, and NOT proved here).  The functional
    and the test predicate are abstract parameters, so the file needs no registry vocabulary;
    the mirrormere probe file instantiates them at `WeilExplicit.weilForm . autocorr` and
    `WeilExplicit.IsWeilTest`.  Not expected to fire: every certified instance is positive and
    agrees with the independent zero-side sum.  conjecture1_proved = False."""
    return (
        "-- weil_form_neg_refutes_rh: the falsifiability face of the Weil-form instrument.\n"
        "-- GIVEN Weil's criterion in the forward direction (hcrit, classical, UNDISCHARGED and\n"
        "-- not in Mathlib), a certified strictly negative Weil form at an admissible test\n"
        "-- function refutes RH.  The instrument is therefore an experiment that could have\n"
        "-- falsified; it does not.  conjecture1_proved = False.\n"
        "theorem weil_form_neg_refutes_rh\n"
        "    (Wre : (ℝ → ℂ) → ℝ) (IsTest : (ℝ → ℂ) → Prop) (g : ℝ → ℂ) (W : ℝ)\n"
        "    (hcrit : RiemannHypothesis → ∀ f : ℝ → ℂ, IsTest f → 0 ≤ Wre f)\n"
        "    (hg : IsTest g) (heval : Wre g = W) (hneg : W < 0) :\n"
        "    ¬ RiemannHypothesis := by\n"
        "  intro hrh\n"
        "  exact absurd (heval ▸ hcrit hrh g hg) (not_le.mpr hneg)\n"
    )


def weil_form_membership_face_lean() -> str:
    """The membership face: the enclosure read back onto an abstract functional.

    States that a certified positive value at one admissible g is exactly ONE instance of the
    membership goal's conclusion -- and nothing more: the universal quantifier over the class is
    the wall, and no finite family of instances approaches it (roadmap section 1, "why finite
    certificates cannot reach any wall form").  conjecture1_proved = False."""
    return (
        "-- weil_form_instance_of_enclosure: a certified positive enclosure at ONE admissible\n"
        "-- test function gives the membership goal's conclusion AT THAT g -- and nothing more.\n"
        "-- The goal MM_zeta_comb_membership quantifies over the entire class; no finite family\n"
        "-- of instances approaches that quantifier (roadmap section 1).  conjecture1_proved = False.\n"
        "theorem weil_form_instance_of_enclosure\n"
        "    (Wre : (ℝ → ℂ) → ℝ) (g : ℝ → ℂ) (lo W : ℝ)\n"
        "    (heval : Wre g = W) (hpos : 0 < lo) (hlo : lo ≤ W) :\n"
        "    0 ≤ Wre g := by\n"
        "  rw [heval]\n"
        "  exact le_trans hpos.le hlo\n"
    )


def weil_form_family(
    name: str,
    grid: GridSpec,
    lean_name: Callable,
    spec: Callable,
    constants: dict | None = None,
) -> InequalityFamily:
    """Build a Weil-form-enclosure family (kind ``weil_form_enclosure``).
    ``spec: pt -> WeilFormData`` -- the Arb-enclosed value data for one test function."""
    return InequalityFamily(
        name=name,
        symbols=(),
        grid=grid,
        lean_name=lean_name,
        special=("weil_form_enclosure", spec),
        constants=dict(constants or {}),
    )
