"""Weil-form enclosure emitter (`tool-weil-form-enclosure`) -- routes-roadmap D2, the numeric
substrate of `MM_weil_gram_trace`.

WHAT SHAPE WAS MISSING
----------------------
The MIRRORMERE D2 node packages the infinite-height explicit formula as a finite Hermitian
matrix `weilGram g` whose entry `(i, j)` is

    W_ij = archSide (crossCorr (g i) (g j)) - primeSide (crossCorr (g i) (g j)),

a FINITE von Mangoldt sum, two transform values, a `log pi` term, and one digamma integral.
Every existing Telperion enclosure emitter certifies a single scalar rung (`bragg_floor`,
`li_positivity_ladder`, `enclosure_interval_fold`); NONE folds a *signed, multi-component*
analytic functional -- a difference of an archimedean part and an exactly-finite prime part --
into a single certified rational interval.  That fold is what the Gram instrument needs before
any inertia can be read, so this module builds it.

WHAT THE CERTIFICATE CERTIFIES (read this before citing it)
-----------------------------------------------------------
Exactly two finite, kernel-checkable rational facts, and nothing else:

  1. the PRIME-SIDE FOLD is exact: the claimed prime-side interval `[primeLo, primeHi]` is the
     interval sum of the per-prime-power term intervals supplied as input.  Emitted as a
     `norm_num` rational identity, so a corrupted endpoint is kernel-rejected;
  2. the ENTRY ENCLOSURE is implied: for every real `arch` in `[archLo, archHi]` and every real
     `prime` in `[primeLo, primeHi]`, `lo <= arch - prime <= hi` with
     `lo = archLo - primeHi`, `hi = archHi - primeLo`.  Emitted with the archimedean and prime
     values as UNIVERSALLY QUANTIFIED reals constrained by hypotheses, discharged by `linarith`.

The hypotheses are the trust seam and are NEVER discharged in Lean: `archLo/archHi` come from an
Arb (python-flint) enclosure of `weilKernel f 0 + weilKernel f 1 - f 0 * log pi +
(1/(2 pi)) * integral of archIntegrand f`, and each per-term prime interval from an Arb enclosure
of `Lambda(n)/sqrt n * (f (log n) + f (-log n))`.  The kernel checks the FOLD and the
IMPLICATION, not the analysis -- exactly the BraggFloor / Li-ladder posture.

It does NOT assert that the enclosed number is a Weil-Gram entry of any particular test family;
that identification is `MM_weil_gram_trace` itself (a Lean theorem, not a numeric certificate),
and the Gram-level inertia reading is the separate `interval_gram_inertia` emitter, which
consumes this one's output.

HONEST REFUSAL (the built-in forge / negative control)
------------------------------------------------------
`weil_form_enclosure_certificate` REFUSES: an inverted interval anywhere (`lo > hi`); a supplied
prime-side interval that disagrees with the recomputed exact fold (the certificate-sensitivity
check -- a forged prime side cannot ship); a term list that is empty when a nonzero cutoff was
declared; and a declared support radius `R` inconsistent with the term list (terms must be exactly
the `n >= 2` with `log n <= R`, since `crossCorr` of compactly supported test functions has
compact support and `Lambda(0) = Lambda(1) = 0` -- an omitted in-range prime power would make the
"finite sum" claim false rather than merely loose).

No RH progress is claimed anywhere in this module.  conjecture1_proved = False.
"""
from __future__ import annotations

import math
from dataclasses import dataclass
from typing import Callable, Sequence

import sympy as sp

from .certify import CertifiedInstance
from .expr import rat_lean
from .family import GridSpec, InequalityFamily
from .lean import LeanProfile
from .workflow import Emitter


@dataclass(frozen=True)
class PrimeTermInterval:
    """One prime-power term of the (finite) prime side: `n`, and a rational enclosure of
    `Lambda(n)/sqrt n * (f (log n) + f (-log n))` for `f = crossCorr (g i) (g j)`."""

    n: int
    lo: sp.Rational
    hi: sp.Rational


@dataclass(frozen=True)
class WeilFormData:
    """Arb-enclosed input for ONE Weil-form value `archSide f - primeSide f`.

    `support_radius` is the declared `R` with `supp f subset [-R, R]`; the prime side is then the
    finite sum over `2 <= n <= exp R`.  `terms` must list exactly those `n` (the emitter refuses
    an incomplete list).  `arch_lo/arch_hi` enclose the whole archimedean side in one interval --
    the digamma integral is not separately certified here, and saying so is the point.
    """

    label: str
    support_radius: sp.Rational
    arch_lo: sp.Rational
    arch_hi: sp.Rational
    terms: tuple[PrimeTermInterval, ...]


@dataclass(frozen=True)
class WeilFormCert:
    """One certified Weil-form enclosure: the exact prime-side fold and the entry interval."""

    label: str
    support_radius: sp.Rational
    arch_lo: sp.Rational
    arch_hi: sp.Rational
    terms: tuple[PrimeTermInterval, ...]
    prime_lo: sp.Rational
    prime_hi: sp.Rational

    @property
    def lo(self) -> sp.Rational:
        return sp.Rational(self.arch_lo - self.prime_hi)

    @property
    def hi(self) -> sp.Rational:
        return sp.Rational(self.arch_hi - self.prime_lo)

    @property
    def width(self) -> sp.Rational:
        return sp.Rational(self.hi - self.lo)


def _prime_powers_up_to(bound: int) -> list[int]:
    """Every `n` in `[2, bound]` with `Lambda(n) != 0` (the prime powers), ascending."""
    out: list[int] = []
    for n in range(2, max(bound, 1) + 1):
        m, p = n, None
        d = 2
        while d * d <= m:
            if m % d == 0:
                p = d
                while m % d == 0:
                    m //= d
                break
            d += 1
        if p is None:
            out.append(n)          # n itself prime
        elif m == 1:
            out.append(n)          # n = p^k
    return out


def weil_form_enclosure_certificate(data: WeilFormData) -> WeilFormCert:
    """Build (and exactly re-check) a Weil-form enclosure certificate.

    Re-derives the prime-side interval from `data.terms` by exact rational interval addition and
    refuses every degeneracy listed in the module docstring.  The returned certificate carries the
    RE-DERIVED prime interval, never a supplied one, so the emitted Lean cannot inherit a forged
    fold.
    """
    R = sp.Rational(data.support_radius)
    if R <= 0:
        raise ValueError(f"weil_form_enclosure REFUSED [{data.label}]: support radius R={R} <= 0")
    if sp.Rational(data.arch_lo) > sp.Rational(data.arch_hi):
        raise ValueError(
            f"weil_form_enclosure REFUSED [{data.label}]: inverted archimedean interval "
            f"[{data.arch_lo}, {data.arch_hi}]")

    cutoff = int(math.floor(math.exp(float(R))))
    expected = _prime_powers_up_to(cutoff)
    got = [int(t.n) for t in data.terms]
    if got != sorted(got):
        raise ValueError(
            f"weil_form_enclosure REFUSED [{data.label}]: term list is not ascending: {got}")
    if got != expected:
        raise ValueError(
            f"weil_form_enclosure REFUSED [{data.label}]: the prime-side term list is not the "
            f"complete set of prime powers n <= exp(R) = {cutoff}; expected {expected}, got {got} "
            f"-- an omitted in-range term makes the finite-sum claim FALSE, not merely loose")

    prime_lo = sp.Rational(0)
    prime_hi = sp.Rational(0)
    for t in data.terms:
        tlo, thi = sp.Rational(t.lo), sp.Rational(t.hi)
        if tlo > thi:
            raise ValueError(
                f"weil_form_enclosure REFUSED [{data.label}]: inverted term interval at n={t.n}: "
                f"[{tlo}, {thi}]")
        prime_lo += tlo
        prime_hi += thi

    cert = WeilFormCert(
        label=str(data.label), support_radius=R,
        arch_lo=sp.Rational(data.arch_lo), arch_hi=sp.Rational(data.arch_hi),
        terms=tuple(PrimeTermInterval(int(t.n), sp.Rational(t.lo), sp.Rational(t.hi))
                    for t in data.terms),
        prime_lo=prime_lo, prime_hi=prime_hi,
    )
    if cert.lo > cert.hi:
        raise ValueError(
            f"weil_form_enclosure REFUSED [{data.label}]: derived entry interval is inverted "
            f"[{cert.lo}, {cert.hi}]")
    return cert


def certify_weil_form_enclosure_point(family, pt, name):
    """Certify one Weil-form enclosure: ``(CertifiedInstance, 2)`` (fold + implication)."""
    data = family.special[1](pt)
    cert = weil_form_enclosure_certificate(data)
    inst = CertifiedInstance(point=dict(pt), lean_name=name, corners=(), payload=cert)
    return inst, 2


@dataclass
class WeilFormEnclosureEmitter(Emitter):
    """Emit, per instance, (i) the exact prime-side interval fold as a `norm_num` rational
    identity and (ii) the entry enclosure `lo <= arch - prime <= hi` for every `arch`, `prime`
    in the input intervals, by `linarith`.  Mathlib-only Lean; no prelude."""

    def __post_init__(self):
        self.kind = "weil_form_enclosure"

    def emit_body(self, fam, profile: LeanProfile) -> tuple[str, int]:
        lines: list[str] = []
        n_thm = 0
        for inst in fam.instances:
            cert: WeilFormCert = inst.payload  # type: ignore[assignment]
            nm = inst.lean_name
            lo, hi = rat_lean(cert.lo), rat_lean(cert.hi)
            plo, phi = rat_lean(cert.prime_lo), rat_lean(cert.prime_hi)
            alo, ahi = rat_lean(cert.arch_lo), rat_lean(cert.arch_hi)
            sum_lo = " + ".join(rat_lean(t.lo) for t in cert.terms)
            sum_hi = " + ".join(rat_lean(t.hi) for t in cert.terms)
            ns = ", ".join(str(t.n) for t in cert.terms)

            lines.append(
                f"-- {nm}_fold: the PRIME-SIDE FOLD of the Weil-form value '{cert.label}'.\n"
                f"-- supp f subset [-R, R] with R = {cert.support_radius}, so primeSide f is the "
                f"FINITE sum over the prime powers n in [{ns}]\n"
                f"-- (Lambda(0) = Lambda(1) = 0).  Each term interval encloses "
                f"Lambda(n)/sqrt n * (f (log n) + f (-log n)) (Arb, python-flint -- the trust seam);\n"
                f"-- the kernel re-does the interval ADDITION exactly in the rationals.  "
                f"A corrupted endpoint is kernel-rejected.  conjecture1_proved = False.\n"
                f"theorem {nm}_fold : ({plo} : ℝ) = {sum_lo} ∧ ({phi} : ℝ) = {sum_hi} := by\n"
                f"  constructor <;> norm_num\n"
            )
            n_thm += 1

            lines.append(
                f"-- {nm}: the ENTRY ENCLOSURE for '{cert.label}'.  For EVERY real arch in the\n"
                f"-- certified archimedean interval [{cert.arch_lo}, {cert.arch_hi}] (the pole terms,\n"
                f"-- the -f 0 * log pi term and the digamma integral, enclosed as ONE Arb interval --\n"
                f"-- the trust seam) and EVERY real prime in the folded prime interval\n"
                f"-- [{cert.prime_lo}, {cert.prime_hi}], the Weil-form value arch - prime lies in\n"
                f"-- [{cert.lo}, {cert.hi}] (width {cert.width}).  Pure interval arithmetic; the\n"
                f"-- identification of arch - prime with a Weil-Gram entry is the Lean node\n"
                f"-- MM_weil_gram_trace, NOT this certificate.  conjecture1_proved = False.\n"
                f"theorem {nm} (arch prime : ℝ)\n"
                f"    (harchLo : ({alo} : ℝ) ≤ arch) (harchHi : arch ≤ ({ahi} : ℝ))\n"
                f"    (hprimeLo : ({plo} : ℝ) ≤ prime) (hprimeHi : prime ≤ ({phi} : ℝ)) :\n"
                f"    ({lo} : ℝ) ≤ arch - prime ∧ arch - prime ≤ ({hi} : ℝ) := by\n"
                f"  constructor <;> linarith\n"
            )
            n_thm += 1
        return "\n".join(lines), n_thm


def weil_form_enclosure_family(
    name: str,
    grid: GridSpec,
    lean_name: Callable,
    spec: Callable,
    constants: dict | None = None,
) -> InequalityFamily:
    """Build a Weil-form enclosure family (kind ``weil_form_enclosure``).
    ``spec: pt -> WeilFormData``."""
    return InequalityFamily(
        name=name,
        symbols=(),
        grid=grid,
        lean_name=lean_name,
        special=("weil_form_enclosure", spec),
        constants=dict(constants or {}),
    )


def gram_entry_intervals(
    certs: Sequence[WeilFormCert],
) -> dict[str, tuple[sp.Rational, sp.Rational]]:
    """Collect certified entry intervals by label -- the hand-off to
    ``emit_interval_gram_inertia``.  Labels are the caller's (e.g. ``"0,1:re"``)."""
    return {c.label: (c.lo, c.hi) for c in certs}
