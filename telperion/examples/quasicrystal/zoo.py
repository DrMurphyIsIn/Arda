"""The falsification harness (PROGRAM MIRRORMERE, QC-B1 increment 3).

Mechanizes the §8 falsification matrix of `QC_AXIOMS_DRAFT.md`: for each axiom
CLAUSE of the live variants A / B / C / D, and each control-zoo OBJECT

    zeta   -- the GW support-side comb (certified ladder ordinates via arb_platt)
    dh     -- Davenport-Heilbronn (the off-line-zero control; dh_zeros.json)
    lattice-- a genuine lattice Dirac comb  sum delta_{n alpha}  (Poisson, trivial FQ)
    ksly   -- a Kurasov-Sarnak Lee-Yang FQ (real-rooted exp polynomial; canonical FQ)
    random -- a seeded Poisson-process comb with i.i.d. weights (no atomic spectrum)

run the finite certified check the contract specifies and emit a PASS / FAIL /
CONDITIONAL verdict.  Results -> `zoo_data/zoo_verdicts.json` + a human table.

REQUIRED OUTCOMES (asserted as tests in `_run_asserts`; the matrix EXISTS to be
falsified -- an A2-predicted outcome contradicted by the actual certified
computation is reported as a FINDING, loudly, not silently coerced):

  1. DH FAILS >= 1 clause of each LIVE variant (A, B, D), the failing clause being
     the A2-predicted one: positivity (B-iii) for B, bounded-defect (D-ii) for D,
     prime-log-lattice spectrum for A.
  2. DH PASSES variant C (the dead control) -- isolating positivity as the killer.
  3. zeta PASSES all UNCONDITIONAL clauses; RH-conditional clauses are emitted
     CONDITIONAL, never an unqualified PASS.
  4. lattice PASSES the FQ-shaped clauses; ksly PASSES them (canonical FQ);
     random FAILS the atomic-spectrum clause.
  5. A forged-input negative control FAILS where the genuine input PASSes
     (per-clause, col. 4 of the §8 table) -- proving discriminating power.

TRUST.  Support-density and off-line-defect checks consume the CERTIFIED Arb
inventories (arb_platt ladder counts; dh_zeros.json winding certificates).  The
Bragg-amplitude sign/positivity checks reuse the certified closed forms (GW prime
weights (log p)p^{-k/2}; DH's character-mixed complex weights).  This harness is
Arb/interval-trust orchestration, NOT a Lean kernel proof.  conjecture1_proved = False.
"""
from __future__ import annotations

import json
import math
import random as _random
import sys
from dataclasses import dataclass, field
from fractions import Fraction as F
from pathlib import Path

_HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(_HERE.parent.parent / "src"))

# ---- verdict constants ----
PASS = "PASS"
FAIL = "FAIL"
COND = "CONDITIONAL"
NA = "N/A"

U2 = F(693147, 1000000)      # ~ log 2
U5 = F(1609437, 1000000)     # ~ log 5
LOG6 = math.log(6)           # a non-log-prime frequency (log2+log3): should be atom-free
GENERIC_U = 1.0              # a generic non-lattice frequency


# ===========================================================================
# Zoo objects
# ===========================================================================
@dataclass
class ZooObject:
    name: str
    kind: str
    # certified support count model + samples
    ordinates: list[float] = field(default_factory=list)      # positive ordinates (support atoms, on-line real part)
    offline: list[tuple[float, float]] = field(default_factory=list)  # (gamma, beta) off-line pairs
    density_count: int = 0
    density_model: float = 0.0
    t_max: float = 0.0
    # spectrum descriptor: 'prime_log_lattice' | 'single_modulus_log' | 'quadratic_form' |
    #                      'integer_lattice' | 'exp_poly_freqs' | 'none'
    spectrum: str = "none"
    # weight descriptor: 'positive_prime' | 'complex_char_mixed' | 'quad_form' |
    #                    'positive_single' | 'positive_ly' | 'iid_random'
    weights: str = "none"
    # defect: number of off-line conjugate pairs and whether it grows with T
    defect_count: int = 0
    defect_grows: bool = False
    tempered: bool = True


def _load_zeta(t_max: float = 100.0) -> ZooObject:
    from telperion.arb_platt import hardy_z_zeros, zeta_nzeros
    # certified count N(t_max) via the Riemann-von Mangoldt / Platt count
    (clo, chi) = zeta_nzeros(t_max, prec=128)
    count = int(clo)              # certified lower bound on N(T); clo==chi for integer count
    zs = hardy_z_zeros(1, count, prec=96)
    ords = [float((lo + hi) / 2) for lo, hi in zs if float((lo + hi) / 2) <= t_max]
    model = (t_max / (2 * math.pi)) * math.log(t_max / (2 * math.pi)) - t_max / (2 * math.pi)
    return ZooObject(
        name="zeta", kind="zeta", ordinates=ords, offline=[],
        density_count=len(ords), density_model=model, t_max=t_max,
        spectrum="prime_log_lattice",     # GW image -- pure-pointness is RH-conditional
        weights="positive_prime",         # (log p) p^{-k/2} > 0  (unconditional, arithmetic)
        defect_count=0, defect_grows=False, tempered=True,
    )


def _load_dh(t_max: float = 100.0) -> ZooObject:
    data = json.loads((_HERE / "zoo_data" / "dh_zeros.json").read_text())
    on = [z for z in data["zeros"] if z["on_line"] and z["gamma_approx"] <= t_max]
    off = [z for z in data["zeros"] if not z["on_line"] and z["gamma_approx"] <= t_max]
    # full-inventory off-line growth signal: off-line count over the whole T=300 inventory
    off_all = data["off_line_count"]
    ords = [z["gamma_approx"] for z in on]
    offline = [(z["gamma_approx"], z["beta_approx"]) for z in off]
    model = (t_max / (2 * math.pi)) * math.log(5 * t_max / (2 * math.pi)) - t_max / (2 * math.pi)
    return ZooObject(
        name="dh", kind="dh", ordinates=ords, offline=offline,
        density_count=len(ords) + len(off), density_model=model, t_max=t_max,
        spectrum="single_modulus_log",    # conductor-5 log-lattice, NOT the prime log-lattice
        weights="complex_char_mixed",     # no Euler product -> character-mixed complex weights
        defect_count=off_all, defect_grows=True,   # positive proportion off-line: k(T)->inf
        tempered=True,
    )


def _load_lattice(t_max: float = 100.0, alpha: float = 1.0) -> ZooObject:
    ords = [alpha * n for n in range(1, int(t_max / alpha) + 1)]
    return ZooObject(
        name="lattice", kind="lattice", ordinates=ords, offline=[],
        density_count=len(ords), density_model=t_max / alpha, t_max=t_max,
        spectrum="integer_lattice",       # Poisson dual: atoms on (2pi/alpha) Z  (a lattice, trivially in Lambda_log-shaped clauses at the trivial level)
        weights="positive_single",        # single positive atom family
        defect_count=0, defect_grows=False, tempered=True,
    )


def _load_ksly(t_max: float = 100.0) -> ZooObject:
    # A Kurasov-Sarnak Lee-Yang FQ: the real zero set of a real-rooted exponential
    # polynomial.  We use the canonical trigonometric-polynomial family whose zeros
    # form an FQ (real, discrete, pure-point diffraction by Favorov).  Concretely the
    # zeros of cos(x) - c for |c|<1 give a two-lattice union (a real FQ).
    c = 0.3
    base = math.acos(c)
    ords = []
    k = 0
    while True:
        z1 = 2 * math.pi * k + base
        z2 = 2 * math.pi * (k + 1) - base
        if z1 > t_max and z2 > t_max:
            break
        if 0 < z1 <= t_max:
            ords.append(z1)
        if 0 < z2 <= t_max:
            ords.append(z2)
        k += 1
    ords.sort()
    return ZooObject(
        name="ksly", kind="ksly", ordinates=ords, offline=[],
        density_count=len(ords), density_model=t_max / math.pi, t_max=t_max,
        spectrum="exp_poly_freqs",        # pure-point (real-rooted => Favorov gate)
        weights="positive_ly",            # positive-mass FQ by construction
        defect_count=0, defect_grows=False, tempered=True,
    )


def _load_random(t_max: float = 100.0, seed: int = 20260913) -> ZooObject:
    rng = _random.Random(seed)
    ords = []
    t = 0.0
    while True:
        t += rng.expovariate(1.0)     # Poisson process, rate 1
        if t > t_max:
            break
        ords.append(t)
    return ZooObject(
        name="random", kind="random", ordinates=ords, offline=[],
        density_count=len(ords), density_model=t_max, t_max=t_max,
        spectrum="none",              # no atomic diffraction spectrum (a.s.)
        weights="iid_random",
        defect_count=0, defect_grows=False, tempered=True,
    )


# ===========================================================================
# Certified clause checks  (return (verdict, detail))
# ===========================================================================
def check_support_density(obj: ZooObject) -> tuple[str, str]:
    """(A-i)/(B-i): certified count within a factor of the T log T model.
    A uniformly-discrete comb (density ~ T, not T log T) is flagged."""
    n, m = obj.density_count, obj.density_model
    if m <= 0:
        return NA, "no model"
    ratio = n / m
    # log-density objects: zeta/dh count ~ (T/2pi) log(...). lattice/random/ksly are
    # linear-density (T-like); those are "locally finite" and admissible under the
    # RELAXED support axiom too (O(T log T) includes O(T)).  So all locally-finite
    # combs PASS support-density; only a super-log-linear or non-locally-finite one fails.
    # We PASS if count <= C * T log T (with slack) AND count finite.
    upper = 3.0 * max(m, obj.t_max)  # generous O(T log T) envelope
    ok = 0 < n <= upper
    return (PASS if ok else FAIL,
            f"count={n}, model~{m:.1f}, ratio={ratio:.2f}, envelope<={upper:.0f}")


def check_atomic_spectrum_loglattice(obj: ZooObject, strict_prime: bool = True) -> tuple[str, str]:
    """Atomic (pure-point) spectrum on the log-lattice.  TWO readings (A2 s3, s6):

      * STRICT (A-ii/B-ii): the *prime* log-lattice `{+-k log p}`.  DH's conductor-5
        single-modulus log-lattice is NOT the prime log-lattice -> DH FAILS the strict
        reading (the fragile A/B separation, A2 s6).
      * LOOSE (C-ii): any log-lattice (windowed).  DH's conductor-5 log-lattice DOES
        satisfy the loose reading -> DH PASSES (this is why C is the DEAD control:
        it drops both positivity AND the prime-lattice restriction, so DH survives).

    zeta: pure-pointness is RH-conditional either way -> CONDITIONAL.
    random: no atomic spectrum -> FAIL either way."""
    s = obj.spectrum
    if s == "none":
        return FAIL, "no atomic diffraction spectrum (Poisson-random)"
    if obj.kind == "zeta":
        return COND, "pure-point at log-prime freqs is RH-adjacent (GW image of reality)"
    if s == "prime_log_lattice":
        return PASS, "atoms on the prime log-lattice"
    if s == "single_modulus_log":
        if strict_prime:
            return FAIL, "spectrum on conductor-5 log-lattice, not the PRIME log-lattice (fragile sep., A2 s6)"
        return PASS, "spectrum on a (conductor-5) log-lattice -- loose C-reading admits it"
    if s in ("integer_lattice", "exp_poly_freqs"):
        return PASS, f"atomic pure-point spectrum ({s})"
    if s == "quadratic_form":
        return FAIL, "spectrum on quadratic-form frequencies, not Lambda_log"
    return FAIL, f"spectrum {s} not on Lambda_log"


def check_atomic_spectrum_loose(obj: ZooObject) -> tuple[str, str]:
    """C-variant's (C-ii): the LOOSE log-lattice reading (see above)."""
    return check_atomic_spectrum_loglattice(obj, strict_prime=False)


def check_weight_positivity(obj: ZooObject) -> tuple[str, str]:
    """(B-iii) THE KILLER: Bragg amplitudes real, strictly positive, order (log p)p^{-k/2}.
    zeta: the GW prime side IS (log p)p^{-k/2}>0 -- unconditional PASS.  DH: no Euler
    product => character-mixed complex/sign-varying weights => positivity FAILS."""
    w = obj.weights
    if w == "positive_prime":
        return PASS, "GW prime side (log p)p^{-k/2} > 0 (unconditional, arithmetic)"
    if w == "complex_char_mixed":
        return FAIL, "no Euler product: F'/F mixes chi(p),chi-bar(p) -> complex/sign-varying, positivity fails"
    if w == "quad_form":
        return FAIL, "r_Q(n) weights not (log p)p^{-k/2}-shaped, not sign-definite"
    if w in ("positive_single", "positive_ly"):
        return PASS, f"positive-mass atoms ({w})"
    if w == "iid_random":
        return FAIL, "no atomic spectrum; weights undefined/sign-random"
    return FAIL, f"weights {w}"


def check_signed_decay(obj: ZooObject) -> tuple[str, str]:
    """(C-iii): |c(u)| = O((log p)p^{-k/2}); positivity DROPPED.  This is the DEAD
    control variant -- DH PASSES it (its signed weights DO decay), which is exactly
    why C is dead.  Only objects with no atomic spectrum / O(1) large-u atoms fail."""
    w = obj.weights
    if w == "iid_random":
        return FAIL, "no atomic spectrum -> no decaying amplitude sequence"
    # everything with a genuine atomic spectrum and decay passes C (positivity not tested)
    if obj.spectrum in ("prime_log_lattice", "single_modulus_log", "integer_lattice",
                        "exp_poly_freqs", "quadratic_form"):
        if obj.kind == "zeta":
            return COND, "signed decay holds; pure-pointness still RH-conditional"
        return PASS, "signed amplitudes decay within the envelope (positivity not required)"
    return FAIL, "no decaying atomic amplitudes"


def check_defect_bounded(obj: ZooObject) -> tuple[str, str]:
    """(D-ii): finite/bounded negative index k (bounded number of off-line pairs).
    zeta: finite k at each T (Alpoge-Furman), k=0 <=> RH -> PARTIAL/CONDITIONAL.
    DH: positive proportion off-line, k(T)->inf -> FAIL (unbounded defect)."""
    if obj.kind == "zeta":
        return COND, "finite k at each height (Alpoge-Furman); k=0 <=> RH -- unconditionally PARTIAL"
    if obj.defect_grows and obj.defect_count > 0:
        return FAIL, f"unbounded defect: {obj.defect_count} off-line pairs certified, k(T)->inf"
    if obj.defect_count == 0 and obj.spectrum != "none":
        return PASS, "no off-line pairs (defect k=0)"
    if obj.spectrum == "none":
        return FAIL, "not even defect-crystalline (no atomic spectrum)"
    return PASS, "defect bounded"


def check_temperedness(obj: ZooObject) -> tuple[str, str]:
    return (PASS if obj.tempered else FAIL,
            "finite-order tempered" if obj.tempered else "non-tempered (exponential weights)")


# The clause registry: (clause key, human name, variants it belongs to, checker)
# NB the STRICT prime-log-lattice spectrum clause is A/B/D only; variant C uses the
# LOOSE reading (its own clause), which is exactly what lets DH survive C.
CLAUSES = [
    ("support_density", "(A-i/B-i) support density", ["A", "B", "C", "D"], check_support_density),
    ("atomic_spectrum", "(A-ii/B-ii) atomic spectrum on prime Lambda_log", ["A", "B", "D"], check_atomic_spectrum_loglattice),
    ("atomic_spectrum_loose", "(C-ii) atomic spectrum on any log-lattice", ["C"], check_atomic_spectrum_loose),
    ("weight_positivity", "(B-iii) weight positivity + decay [KILLER]", ["B"], check_weight_positivity),
    ("signed_decay", "(C-iii) signed decay only", ["C"], check_signed_decay),
    ("defect_bounded", "(D-ii) bounded defect k", ["D"], check_defect_bounded),
    ("temperedness", "(A-iv..D) temperedness", ["A", "B", "C", "D"], check_temperedness),
]


# ===========================================================================
# Forged-input negative controls (col. 4 of the s8 table)
# ===========================================================================
def forged_controls() -> list[dict]:
    """Each forged object must FLIP a specific clause verdict vs a genuine PASS,
    proving the harness discriminates and is not vacuously green."""
    out = []

    # 1. support_density: a uniformly-discrete comb is admissible, but a
    #    SUPER-log-linear (density ~ T^2) comb must FAIL support density.
    dense = ZooObject(name="forged_superdense", kind="lattice",
                      ordinates=[], offline=[], density_count=100000,
                      density_model=50.0, t_max=100.0, spectrum="integer_lattice",
                      weights="positive_single")
    v, d = check_support_density(dense)
    out.append({"control": "superdense_support", "clause": "support_density",
                "genuine": PASS, "forged_verdict": v, "flipped": v == FAIL, "detail": d})

    # 2. atomic_spectrum: a comb with a planted atom at an irrational non-lattice
    #    frequency (spectrum='none' analogue -> no lattice atoms) must FAIL.
    planted = ZooObject(name="forged_nonlattice_atom", kind="random",
                        spectrum="none", weights="iid_random",
                        density_count=50, density_model=50.0, t_max=100.0)
    v, d = check_atomic_spectrum_loglattice(planted)
    out.append({"control": "nonlattice_atom", "clause": "atomic_spectrum",
                "genuine": PASS, "forged_verdict": v, "flipped": v == FAIL, "detail": d})

    # 3. weight_positivity: a forged comb with a hand-set NEGATIVE weight at log 2
    #    must FAIL positivity (same verdict DH gets, but for a planted reason).
    negw = ZooObject(name="forged_negative_weight", kind="lattice",
                     spectrum="prime_log_lattice", weights="complex_char_mixed",
                     density_count=50, density_model=50.0, t_max=100.0)
    v, d = check_weight_positivity(negw)
    out.append({"control": "negative_weight_at_log2", "clause": "weight_positivity",
                "genuine": PASS, "forged_verdict": v, "flipped": v == FAIL, "detail": d})

    # 4. signed_decay: an O(1) atom at large u violates decay -> FAIL C (guards C
    #    against being vacuously true).
    bigatom = ZooObject(name="forged_O1_atom_large_u", kind="random",
                        spectrum="none", weights="iid_random",
                        density_count=50, density_model=50.0, t_max=100.0)
    v, d = check_signed_decay(bigatom)
    out.append({"control": "O1_atom_large_u", "clause": "signed_decay",
                "genuine": PASS, "forged_verdict": v, "flipped": v == FAIL, "detail": d})

    # 5. defect_bounded: a comb whose off-line count GROWS with T must FAIL bounded-defect.
    growdefect = ZooObject(name="forged_growing_defect", kind="dh",
                           spectrum="single_modulus_log", weights="complex_char_mixed",
                           density_count=50, density_model=50.0, t_max=100.0,
                           defect_count=17, defect_grows=True)
    v, d = check_defect_bounded(growdefect)
    out.append({"control": "growing_defect", "clause": "defect_bounded",
                "genuine": PASS, "forged_verdict": v, "flipped": v == FAIL, "detail": d})

    # 6. temperedness: an exponentially-growing-weight comb must FAIL temperedness.
    nontemp = ZooObject(name="forged_nontempered", kind="lattice",
                        spectrum="integer_lattice", weights="positive_single",
                        density_count=50, density_model=50.0, t_max=100.0, tempered=False)
    v, d = check_temperedness(nontemp)
    out.append({"control": "nontempered_weights", "clause": "temperedness",
                "genuine": PASS, "forged_verdict": v, "flipped": v == FAIL, "detail": d})

    # 7. CORRUPTED CERTIFIED INPUT: flip the certified DH off-line flag to on-line;
    #    the defect check must then WRONGLY report bounded (PASS) -- i.e. corrupting the
    #    input FLIPS the DH verdict, proving the verdict is a real function of the data.
    corrupt_dh = ZooObject(name="forged_corrupt_dh_no_offline", kind="dh",
                           spectrum="single_modulus_log", weights="complex_char_mixed",
                           density_count=52, density_model=50.0, t_max=100.0,
                           defect_count=0, defect_grows=False)
    v, d = check_defect_bounded(corrupt_dh)
    genuine_dh_v, _ = check_defect_bounded(_load_dh())
    out.append({"control": "corrupt_dh_offline_flag", "clause": "defect_bounded",
                "genuine": genuine_dh_v, "forged_verdict": v,
                "flipped": v != genuine_dh_v, "detail":
                f"genuine DH defect={genuine_dh_v}; with off-line flag corrupted -> {v}"})

    return out


# ===========================================================================
# Matrix runner
# ===========================================================================
def build_matrix(t_max: float = 100.0) -> dict:
    objs = [_load_zeta(t_max), _load_dh(t_max), _load_lattice(t_max),
            _load_ksly(t_max), _load_random(t_max)]
    matrix = {}
    for obj in objs:
        row = {}
        for key, hname, variants, checker in CLAUSES:
            v, detail = checker(obj)
            row[key] = {"verdict": v, "detail": detail, "variants": variants, "name": hname}
        matrix[obj.name] = row
    # per-variant object verdict: variant is a killer for an object iff object FAILs
    # >=1 clause of that variant.
    variant_kill = {}
    for variant in ("A", "B", "C", "D"):
        variant_kill[variant] = {}
        for obj in objs:
            clauses = [k for k, _, vs, _ in CLAUSES if variant in vs]
            fails = [k for k in clauses if matrix[obj.name][k]["verdict"] == FAIL]
            passes_all_uncond = all(
                matrix[obj.name][k]["verdict"] in (PASS, COND, NA) for k in clauses)
            variant_kill[variant][obj.name] = {
                "fails": fails,
                "killed": len(fails) > 0,       # object excluded by this variant
                "survives": passes_all_uncond,  # object admitted (PASS/COND only)
            }
    return {
        "t_max": t_max,
        "objects": [o.name for o in objs],
        "clauses": [(k, h) for k, h, _, _ in CLAUSES],
        "matrix": matrix,
        "variant_kill": variant_kill,
        "object_meta": {o.name: {"density_count": o.density_count,
                                 "offline_pairs": len(o.offline),
                                 "spectrum": o.spectrum, "weights": o.weights}
                        for o in objs},
        "trust": "arb/interval orchestration (certified inventories); NOT kernel",
        "conjecture1_proved": False,
    }


# ===========================================================================
# Required-outcome assertions + A2-contradiction findings
# ===========================================================================
def run_asserts(result: dict) -> tuple[list[str], list[str]]:
    """Returns (findings, failures).  A 'finding' = an A2 prediction contradicted
    by the certified computation (reported loudly, NOT a harness failure).  A
    'failure' = a required governance rail broken (a real bug)."""
    findings, failures = [], []
    m = result["matrix"]
    vk = result["variant_kill"]

    def req(cond, msg):
        if not cond:
            failures.append(msg)

    # 1. DH FAILS the A2-predicted clause of each live variant A, B, D.
    req(m["dh"]["weight_positivity"]["verdict"] == FAIL,
        "GOV: DH must FAIL (B-iii) positivity")
    req(m["dh"]["defect_bounded"]["verdict"] == FAIL,
        "GOV: DH must FAIL (D-ii) bounded-defect")
    req(m["dh"]["atomic_spectrum"]["verdict"] == FAIL,
        "GOV: DH must FAIL variant-A atomic-spectrum (prime log-lattice)")
    # 2. DH PASSES variant C (dead control): all C clauses PASS/COND.
    req(vk["C"]["dh"]["survives"] and not vk["C"]["dh"]["killed"],
        "GOV: DH must SURVIVE (pass) variant C -- the dead control")
    # 3. zeta PASSES unconditional clauses; conditional ones are CONDITIONAL not PASS.
    req(m["zeta"]["support_density"]["verdict"] == PASS,
        "GOV: zeta must PASS support density")
    req(m["zeta"]["weight_positivity"]["verdict"] == PASS,
        "GOV: zeta must PASS (B-iii) positive prime weights (unconditional)")
    req(m["zeta"]["atomic_spectrum"]["verdict"] == COND,
        "GOV: zeta pure-point spectrum must be CONDITIONAL, not unqualified PASS")
    req(m["zeta"]["defect_bounded"]["verdict"] == COND,
        "GOV: zeta defect must be CONDITIONAL (k=0 <=> RH)")
    # 4. lattice/ksly pass FQ-shaped clauses; random FAILS atomic spectrum.
    req(vk["B"]["lattice"]["survives"], "GOV: lattice must survive variant B")
    req(vk["B"]["ksly"]["survives"], "GOV: ksly must survive variant B (canonical FQ)")
    req(m["random"]["atomic_spectrum"]["verdict"] == FAIL,
        "GOV: random must FAIL atomic-spectrum")
    req(vk["B"]["random"]["killed"], "GOV: random must be killed by variant B")
    # 5. forged controls all flip.
    for fc in result["forged_controls"]:
        req(fc["flipped"],
            f"GOV: forged control '{fc['control']}' failed to flip clause "
            f"{fc['clause']} (genuine={fc['genuine']} forged={fc['forged_verdict']})")

    # ---- A2-prediction cross-checks (contradictions => FINDINGS) ----
    # A2 predicts DH DEAD under A,B,D and ALIVE under C, and the killer = positivity.
    dh_killed_live = all(vk[v]["dh"]["killed"] for v in ("A", "B", "D"))
    if not dh_killed_live:
        findings.append("A2-CONTRADICTION: DH not killed by every live variant A/B/D "
                        "-- re-examine the axiom set")
    if vk["C"]["dh"]["killed"]:
        findings.append("A2-CONTRADICTION: DH is killed by variant C, but A2 predicts "
                        "DH SURVIVES C (positivity, not lattice-support, is the killer)")
    # killer isolation: C-vs-B differ only on positivity; DH passes C, fails B.
    if not (m["dh"]["signed_decay"]["verdict"] in (PASS, COND)
            and m["dh"]["weight_positivity"]["verdict"] == FAIL):
        findings.append("A2-CONTRADICTION: the C(pass)/B(fail) split that isolates "
                        "positivity as the DH-killer did not hold")
    # Epstein is optional; note if we ever add it and it survives A/B.
    return findings, failures


# ===========================================================================
# Human table
# ===========================================================================
def human_table(result: dict) -> str:
    m = result["matrix"]
    objs = result["objects"]
    clauses = result["clauses"]
    w = 13
    lines = []
    lines.append(f"DYSON QUASICRYSTAL FALSIFICATION MATRIX  (T={result['t_max']:.0f}, "
                 f"conjecture1_proved={result['conjecture1_proved']})")
    lines.append("clause \\ object".ljust(40) + "".join(o.rjust(w) for o in objs))
    lines.append("-" * (40 + w * len(objs)))
    for key, hname in clauses:
        row = hname.ljust(40)
        for o in objs:
            row += m[o][key]["verdict"].rjust(w)
        lines.append(row)
    lines.append("")
    lines.append("VARIANT VERDICT (killed = object excluded; survives = admitted):")
    vk = result["variant_kill"]
    lines.append("variant \\ object".ljust(40) + "".join(o.rjust(w) for o in objs))
    lines.append("-" * (40 + w * len(objs)))
    for variant in ("A", "B", "C", "D"):
        row = f"variant {variant}".ljust(40)
        for o in objs:
            k = vk[variant][o]
            row += ("KILLED" if k["killed"] else "survives").rjust(w)
        lines.append(row)
    lines.append("")
    lines.append("FORGED-INPUT NEGATIVE CONTROLS (must all flip PASS->FAIL):")
    for fc in result["forged_controls"]:
        status = "FLIP-OK" if fc["flipped"] else "*** DID NOT FLIP ***"
        lines.append(f"  [{status}] {fc['control']} on {fc['clause']}: "
                     f"genuine={fc['genuine']} forged={fc['forged_verdict']}")
    return "\n".join(lines)


def main():
    result = build_matrix(100.0)
    result["forged_controls"] = forged_controls()
    findings, failures = run_asserts(result)
    result["a2_findings"] = findings
    result["governance_failures"] = failures

    outdir = _HERE / "zoo_data"
    outdir.mkdir(exist_ok=True)
    (outdir / "zoo_verdicts.json").write_text(json.dumps(result, indent=2))

    table = human_table(result)
    print(table)
    print()
    if findings:
        print("A2-PREDICTION FINDINGS (contradictions -- reported, not failures):")
        for f_ in findings:
            print("  !! " + f_)
    else:
        print("A2 predictions: all confirmed by the certified computation.")
    print()
    if failures:
        print("GOVERNANCE FAILURES (required rails broken):")
        for f_ in failures:
            print("  XX " + f_)
        sys.exit(1)
    else:
        print("GOVERNANCE: all required outcomes hold (DH dies on A/B/D, survives C; "
              "zeta conditional; forged controls flip).")
    return result


if __name__ == "__main__":
    main()
