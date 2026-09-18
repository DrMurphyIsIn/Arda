"""Interval-Gram inertia emitter (`tool-interval-gram-inertia`) -- routes-roadmap D2, the
inertia reading of an Arb-enclosed Weil-Gram matrix.

WHAT SHAPE WAS MISSING
----------------------
`MM_offline_pairs_le_defect` (W2b) says the defect of a Hermitian matrix COUNTS off-line pairs,
and `MM_weil_gram_trace` (D2) says the Weil-Gram matrix of a finite test family is Hermitian with
genuine zeta data on its trace side.  Between them sits an object no Telperion emitter could
certify: a Hermitian matrix whose entries are known only as *rational intervals* (Arb enclosures
of the Weil form, produced by `emit_weil_form_enclosure`).  `RayleighGramEmitter` certifies a
Gram form at EXACT rational entries; `EnclosureIntervalFoldEmitter` folds enclosures but reads no
inertia.  This module is the missing piece: kernel-read inertia data for an INTERVAL Hermitian
matrix.

THE TWO CERTIFICATE SHAPES (both Mathlib-only, both finite, both load-bearing)
------------------------------------------------------------------------------
`mode = "negative"` -- A CERTIFIED NEGATIVE DIRECTION.  For a rational complex witness vector
`x`, the Hermitian form is the exactly-rational LINEAR functional of the entry data

    hermForm A x = sum_i |x i|^2 * a_ii + sum_{i<j} (alpha_ij * a_ij + beta_ij * b_ij),
    alpha_ij = 2 Re(conj (x i) * x j),  beta_ij = -2 Im(conj (x i) * x j),

(`A_ij = a_ij + i b_ij`, `a_ji = a_ij`, `b_ji = -b_ij`, `b_ii = 0` by Hermitian-ness).  The
emitter maximises that functional over the entry box in exact rational arithmetic and, when the
maximum is strictly negative, emits `hermForm A x <= -margin` from the box hypotheses, discharged
by `linarith`.  Reading: EVERY Hermitian matrix in the enclosure has a negative direction, hence
`1 <= defect` via `DefectDictionary.NegativeWitness.ofNegDir` + `offline_pairs_le_defect`.  On
genuine zeta data this is the FALSIFIABILITY face: it is not expected to fire, and it is emitted
so that the instrument could have fired.

`mode = "dominance"` -- A CERTIFIED ABSENCE OF NEGATIVE DIRECTIONS AT THIS PRECISION.  Per row,
a rational modulus bound `m_ij` for each off-diagonal entry (`a_ij^2 + b_ij^2 <= m_ij^2`, from the
box, by `nlinarith`) together with the constant inequality `sum_{j != i} m_ij < dLo_i` for the
certified diagonal lower bound.  Strict Hermitian diagonal dominance with positive diagonal is
positive definiteness (Gershgorin), so the reading is `defect = 0`, `posIndex = k` FOR THIS
ENCLOSED FAMILY.

WHAT IS NOT CLAIMED
-------------------
The emitted theorems are the finite inequalities above and nothing more.  In particular the
dominance mode does NOT emit `Matrix.PosDef`, `posIndex = k` or `defect = 0`: the step from
diagonal dominance to positive definiteness is a Lean lemma that belongs to the consuming island's
prelude (`RHLinalg`), and an emitter that asserted it from its own text would be claiming a
theorem it does not carry.  More importantly, `defect = 0` for ONE test family is DATA; for every
test family it is Weil's criterion and therefore RH (roadmap section 3, B10/D11).  This emitter
produces instances, never the universal statement.  conjecture1_proved = False.

HONEST REFUSAL (the built-in forge / negative control)
------------------------------------------------------
`interval_gram_inertia_certificate` REFUSES: an inverted interval; a non-Hermitian input (an
imaginary part supplied for a diagonal entry whose interval does not contain 0); a zero witness
vector in `negative` mode (`hermForm A 0 = 0` is not a negative direction); a `negative` instance
whose box maximum is `>= 0` (the enclosure does NOT force a negative direction -- an honest
refusal, never a false theorem); and a `dominance` instance with a non-positive diagonal lower
bound or a row whose off-diagonal modulus budget does not clear it.
"""
from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
from typing import Callable

import sympy as sp

from .certify import CertifiedInstance
from .expr import rat_lean
from .family import GridSpec, InequalityFamily
from .lean import LeanProfile
from .workflow import Emitter

Interval = tuple[sp.Rational, sp.Rational]


@dataclass(frozen=True)
class IntervalHermitian:
    """A `k x k` Hermitian matrix known entrywise as rational intervals.

    `diag[i]` encloses the (real) diagonal entry `a_ii`; `off[(i, j)]` for `i < j` is the pair
    `(re_interval, im_interval)` enclosing `a_ij` and `b_ij`.  The lower triangle is NOT supplied:
    Hermitian-ness fixes it (`a_ji = a_ij`, `b_ji = -b_ij`).
    """

    k: int
    diag: tuple[Interval, ...]
    off: dict[tuple[int, int], tuple[Interval, Interval]]


@dataclass(frozen=True)
class GramInertiaData:
    """Input for one inertia reading.  `mode` is ``"negative"`` or ``"dominance"``.

    `witness` (negative mode) is the rational complex test vector as `(p_i, q_i)` pairs,
    `x i = p_i + i q_i`.  `moduli` (dominance mode) optionally pins the rational modulus bounds
    `m_ij`; when omitted the emitter derives them from the box.
    """

    label: str
    matrix: IntervalHermitian
    mode: str
    witness: tuple[tuple[sp.Rational, sp.Rational], ...] = ()
    moduli: dict[tuple[int, int], sp.Rational] | None = None


@dataclass(frozen=True)
class GramInertiaCert:
    """A certified inertia reading of an interval Hermitian matrix."""

    label: str
    matrix: IntervalHermitian
    mode: str
    witness: tuple[tuple[sp.Rational, sp.Rational], ...]
    # negative mode
    diag_coeff: tuple[sp.Rational, ...] = ()
    off_coeff: tuple[tuple[int, int, sp.Rational, sp.Rational], ...] = ()
    box_max: sp.Rational = sp.Rational(0)
    margin: sp.Rational = sp.Rational(0)
    # dominance mode
    moduli: tuple[tuple[int, int, sp.Rational], ...] = ()
    row_slack: tuple[sp.Rational, ...] = ()


def _check_interval(label: str, what: str, iv: Interval) -> Interval:
    lo, hi = sp.Rational(iv[0]), sp.Rational(iv[1])
    if lo > hi:
        raise ValueError(
            f"interval_gram_inertia REFUSED [{label}]: inverted interval for {what}: [{lo}, {hi}]")
    return (lo, hi)


def _normalise(label: str, m: IntervalHermitian) -> IntervalHermitian:
    if m.k < 1:
        raise ValueError(f"interval_gram_inertia REFUSED [{label}]: k = {m.k} < 1")
    if len(m.diag) != m.k:
        raise ValueError(
            f"interval_gram_inertia REFUSED [{label}]: {len(m.diag)} diagonal intervals for k = {m.k}")
    diag = tuple(_check_interval(label, f"a_{i}{i}", iv) for i, iv in enumerate(m.diag))
    off: dict[tuple[int, int], tuple[Interval, Interval]] = {}
    for (i, j), (re_iv, im_iv) in sorted(m.off.items()):
        if not (0 <= i < j < m.k):
            raise ValueError(
                f"interval_gram_inertia REFUSED [{label}]: off-diagonal index ({i}, {j}) is not a "
                f"strict upper-triangular index of a {m.k} x {m.k} matrix")
        off[(i, j)] = (_check_interval(label, f"a_{i}{j}", re_iv),
                       _check_interval(label, f"b_{i}{j}", im_iv))
    missing = [(i, j) for i in range(m.k) for j in range(i + 1, m.k) if (i, j) not in off]
    if missing:
        raise ValueError(
            f"interval_gram_inertia REFUSED [{label}]: missing off-diagonal enclosures {missing} "
            f"-- an unenclosed entry cannot be bounded, so no inertia can be read")
    return IntervalHermitian(k=m.k, diag=diag, off=off)


def _sup_of_linear(coeff: sp.Rational, iv: Interval) -> sp.Rational:
    """Supremum of `coeff * t` for `t` in `iv` (exact rational)."""
    lo, hi = iv
    return sp.Rational(coeff * hi) if coeff >= 0 else sp.Rational(coeff * lo)


def _ceil_sqrt_rational(q: sp.Rational, denom: int = 10 ** 6) -> sp.Rational:
    """Smallest multiple of `1/denom` whose square is `>= q` (exact check)."""
    if q < 0:
        return sp.Rational(0)
    f = Fraction(int(q.p), int(q.q))
    n = 0
    # integer sqrt of q * denom^2, rounded up
    target = f * denom * denom
    n = sp.integer_nthroot(int(target.numerator // target.denominator), 2)[0]
    while sp.Rational(n, denom) ** 2 < q:
        n += 1
    return sp.Rational(n, denom)


def interval_gram_inertia_certificate(data: GramInertiaData) -> GramInertiaCert:
    """Build (and exactly re-check) one inertia certificate.  See the module docstring for the
    refusal list; every check is exact rational arithmetic."""
    label = str(data.label)
    m = _normalise(label, data.matrix)

    if data.mode == "negative":
        if len(data.witness) != m.k:
            raise ValueError(
                f"interval_gram_inertia REFUSED [{label}]: witness has {len(data.witness)} entries "
                f"for k = {m.k}")
        x = tuple((sp.Rational(p), sp.Rational(q)) for p, q in data.witness)
        if all(p == 0 and q == 0 for p, q in x):
            raise ValueError(
                f"interval_gram_inertia REFUSED [{label}]: the zero witness gives hermForm = 0, "
                f"which is not a negative direction")
        diag_coeff = tuple(sp.Rational(p * p + q * q) for p, q in x)
        off_coeff: list[tuple[int, int, sp.Rational, sp.Rational]] = []
        for (i, j) in sorted(m.off):
            pi, qi = x[i]
            pj, qj = x[j]
            u = sp.Rational(pi * pj + qi * qj)          # Re (conj (x i) * x j)
            v = sp.Rational(pi * qj - qi * pj)          # Im (conj (x i) * x j)
            off_coeff.append((i, j, sp.Rational(2 * u), sp.Rational(-2 * v)))
        box_max = sp.Rational(0)
        for i in range(m.k):
            box_max += _sup_of_linear(diag_coeff[i], m.diag[i])
        for (i, j, alpha, beta) in off_coeff:
            re_iv, im_iv = m.off[(i, j)]
            box_max += _sup_of_linear(alpha, re_iv)
            box_max += _sup_of_linear(beta, im_iv)
        if box_max >= 0:
            raise ValueError(
                f"interval_gram_inertia REFUSED [{label}]: the enclosure does not force a negative "
                f"direction at this witness -- sup over the box is {box_max} >= 0.  No certificate "
                f"is emitted (an honest refusal; widen nothing, this is the instrument saying it "
                f"sees no off-line pair here)")
        return GramInertiaCert(
            label=label, matrix=m, mode="negative", witness=x,
            diag_coeff=diag_coeff, off_coeff=tuple(off_coeff),
            box_max=box_max, margin=sp.Rational(-box_max),
        )

    if data.mode == "dominance":
        moduli: list[tuple[int, int, sp.Rational]] = []
        for (i, j) in sorted(m.off):
            (rlo, rhi), (ilo, ihi) = m.off[(i, j)]
            rmax = max(abs(rlo), abs(rhi))
            imax = max(abs(ilo), abs(ihi))
            need = sp.Rational(rmax ** 2 + imax ** 2)
            if data.moduli is not None and (i, j) in data.moduli:
                mij = sp.Rational(data.moduli[(i, j)])
                if mij < 0 or mij ** 2 < need:
                    raise ValueError(
                        f"interval_gram_inertia REFUSED [{label}]: supplied modulus bound "
                        f"m_{i}{j} = {mij} does not dominate the box (needs m^2 >= {need})")
            else:
                mij = _ceil_sqrt_rational(need)
            moduli.append((i, j, mij))
        mdict = {(i, j): mij for (i, j, mij) in moduli}
        row_slack: list[sp.Rational] = []
        for i in range(m.k):
            dlo = m.diag[i][0]
            if dlo <= 0:
                raise ValueError(
                    f"interval_gram_inertia REFUSED [{label}]: diagonal lower bound a_{i}{i} >= "
                    f"{dlo} is not positive, so no dominance reading is available")
            budget = sp.Rational(0)
            for j in range(m.k):
                if j == i:
                    continue
                key = (i, j) if i < j else (j, i)
                budget += mdict[key]
            slack = sp.Rational(dlo - budget)
            if slack <= 0:
                raise ValueError(
                    f"interval_gram_inertia REFUSED [{label}]: row {i} is not strictly dominant "
                    f"-- off-diagonal modulus budget {budget} does not clear the diagonal lower "
                    f"bound {dlo} (slack {slack} <= 0)")
            row_slack.append(slack)
        return GramInertiaCert(
            label=label, matrix=m, mode="dominance", witness=(),
            moduli=tuple(moduli), row_slack=tuple(row_slack),
        )

    raise ValueError(
        f"interval_gram_inertia REFUSED [{label}]: unknown mode {data.mode!r} "
        f"(expected 'negative' or 'dominance')")


def certify_interval_gram_inertia_point(family, pt, name):
    """Certify one interval-Gram inertia reading: ``(CertifiedInstance, 1)``."""
    data = family.special[1](pt)
    cert = interval_gram_inertia_certificate(data)
    inst = CertifiedInstance(point=dict(pt), lean_name=name, corners=(), payload=cert)
    return inst, 1


def _diag_var(i: int) -> str:
    return f"a{i}{i}"


def _re_var(i: int, j: int) -> str:
    return f"a{i}{j}"


def _im_var(i: int, j: int) -> str:
    return f"b{i}{j}"


def _vars_of(m: IntervalHermitian) -> list[str]:
    names = [_diag_var(i) for i in range(m.k)]
    for (i, j) in sorted(m.off):
        names += [_re_var(i, j), _im_var(i, j)]
    return names


def _box_hyps(m: IntervalHermitian) -> list[str]:
    hyps: list[str] = []
    for i in range(m.k):
        lo, hi = m.diag[i]
        v = _diag_var(i)
        hyps.append(f"    (h{v}lo : ({rat_lean(lo)} : ℝ) ≤ {v}) (h{v}hi : {v} ≤ ({rat_lean(hi)} : ℝ))")
    for (i, j) in sorted(m.off):
        (rlo, rhi), (ilo, ihi) = m.off[(i, j)]
        vr, vi = _re_var(i, j), _im_var(i, j)
        hyps.append(f"    (h{vr}lo : ({rat_lean(rlo)} : ℝ) ≤ {vr}) (h{vr}hi : {vr} ≤ ({rat_lean(rhi)} : ℝ))")
        hyps.append(f"    (h{vi}lo : ({rat_lean(ilo)} : ℝ) ≤ {vi}) (h{vi}hi : {vi} ≤ ({rat_lean(ihi)} : ℝ))")
    return hyps


@dataclass
class IntervalGramInertiaEmitter(Emitter):
    """Emit the inertia reading of an interval Hermitian (Weil-)Gram matrix: a certified negative
    direction (`linarith`) or certified strict diagonal dominance (`nlinarith`).  Mathlib-only
    Lean; no prelude, and no `PosDef` / `posIndex` / `defect` claim is emitted."""

    def __post_init__(self):
        self.kind = "interval_gram_inertia"

    def emit_body(self, fam, profile: LeanProfile) -> tuple[str, int]:
        lines: list[str] = []
        n_thm = 0
        for inst in fam.instances:
            cert: GramInertiaCert = inst.payload  # type: ignore[assignment]
            m = cert.matrix
            nm = inst.lean_name
            binders = " ".join(_vars_of(m))
            hyps = "\n".join(_box_hyps(m))

            if cert.mode == "negative":
                terms = [f"{rat_lean(cert.diag_coeff[i])} * {_diag_var(i)}"
                         for i in range(m.k) if cert.diag_coeff[i] != 0]
                for (i, j, alpha, beta) in cert.off_coeff:
                    if alpha != 0:
                        terms.append(f"{rat_lean(alpha)} * {_re_var(i, j)}")
                    if beta != 0:
                        terms.append(f"{rat_lean(beta)} * {_im_var(i, j)}")
                form = " + ".join(terms) if terms else "0"
                xs = ", ".join(f"({p} + {q} i)" for p, q in cert.witness)
                lines.append(
                    f"-- {nm}: CERTIFIED NEGATIVE DIRECTION of the enclosed Hermitian matrix "
                    f"'{cert.label}' (k = {m.k}).\n"
                    f"-- Witness x = ({xs}).  For a Hermitian A with A i i = a_ii (real), "
                    f"A i j = a_ij + i b_ij (i < j)\n"
                    f"-- and A j i = conj (A i j), RHLinalg.hermForm A x is exactly the rational "
                    f"linear functional below\n"
                    f"-- (diagonal coefficients |x i|^2, off-diagonal 2 Re(conj (x i) * x j) and "
                    f"-2 Im(conj (x i) * x j)).\n"
                    f"-- Every matrix in the certified entry box makes it <= {cert.box_max} < 0, so "
                    f"EVERY such matrix has a negative\n"
                    f"-- direction: 1 <= defect, via NegativeWitness.ofNegDir + "
                    f"offline_pairs_le_defect (MM_offline_pairs_le_defect).\n"
                    f"-- The entry intervals are Arb (python-flint) enclosures of Weil-form values "
                    f"(emit_weil_form_enclosure) --\n"
                    f"-- the documented trust seam; the kernel re-does the interval maximisation.  "
                    f"On genuine zeta data this\n"
                    f"-- certificate is the FALSIFIABILITY face and is not expected to fire.  "
                    f"conjecture1_proved = False.\n"
                    f"set_option linter.unusedVariables false in\n"
                    f"theorem {nm} ({binders} : ℝ)\n{hyps} :\n"
                    f"    {form} ≤ {rat_lean(cert.box_max)} := by\n"
                    f"  linarith\n"
                )
                n_thm += 1
            else:
                conj_parts: list[str] = []
                for (i, j, mij) in cert.moduli:
                    conj_parts.append(
                        f"{_re_var(i, j)} ^ 2 + {_im_var(i, j)} ^ 2 ≤ {rat_lean(mij ** 2)}")
                mdict = {(i, j): mij for (i, j, mij) in cert.moduli}
                for i in range(m.k):
                    budget = sp.Rational(0)
                    for j in range(m.k):
                        if j == i:
                            continue
                        budget += mdict[(i, j) if i < j else (j, i)]
                    conj_parts.append(
                        f"({rat_lean(budget)} : ℝ) < {rat_lean(m.diag[i][0])}")
                body = " ∧\n      ".join(conj_parts)
                refine = ", ".join("?_" for _ in conj_parts)
                hint_terms = []
                for (i, j) in sorted(m.off):
                    vr, vi = _re_var(i, j), _im_var(i, j)
                    hint_terms += [f"h{vr}lo", f"h{vr}hi", f"h{vi}lo", f"h{vi}hi"]
                hints = ", ".join(hint_terms)
                lines.append(
                    f"-- {nm}: CERTIFIED STRICT DIAGONAL DOMINANCE of the enclosed Hermitian matrix "
                    f"'{cert.label}' (k = {m.k}).\n"
                    f"-- Per off-diagonal entry a modulus bound |A i j|^2 <= m_ij^2 valid on the "
                    f"whole entry box, and per row the\n"
                    f"-- constant inequality (sum over j != i of m_ij) < (certified lower bound for "
                    f"a_ii); row slacks "
                    f"{', '.join(str(s) for s in cert.row_slack)}.\n"
                    f"-- READING (not emitted as a claim): strict Hermitian diagonal dominance with "
                    f"positive diagonal is positive\n"
                    f"-- definiteness (Gershgorin), so this enclosed family has defect 0 and "
                    f"posIndex {m.k}.  The dominance -> PosDef\n"
                    f"-- lemma belongs to the consuming island's RHLinalg prelude and is NOT "
                    f"asserted here.  defect = 0 for ONE test\n"
                    f"-- family is DATA; for EVERY test family it is Weil's criterion and therefore "
                    f"RH, which is NOT claimed.\n"
                    f"-- Entry intervals are Arb enclosures (emit_weil_form_enclosure) -- the trust "
                    f"seam.  conjecture1_proved = False.\n"
                    f"set_option linter.unusedVariables false in\n"
                    f"theorem {nm} ({binders} : ℝ)\n{hyps} :\n"
                    f"    {body} := by\n"
                    f"  refine ⟨{refine}⟩\n"
                    f"  all_goals nlinarith [{hints}]\n"
                )
                n_thm += 1
        return "\n".join(lines), n_thm


def interval_gram_inertia_family(
    name: str,
    grid: GridSpec,
    lean_name: Callable,
    spec: Callable,
    constants: dict | None = None,
) -> InequalityFamily:
    """Build an interval-Gram inertia family (kind ``interval_gram_inertia``).
    ``spec: pt -> GramInertiaData``."""
    return InequalityFamily(
        name=name,
        symbols=(),
        grid=grid,
        lean_name=lean_name,
        special=("interval_gram_inertia", spec),
        constants=dict(constants or {}),
    )
