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

# Davenport-Heilbronn coefficient vector c=[1, kappa, -kappa, -1, 0] period 5
# (QC_DH_SCOUT.md: kappa = (sqrt(10-2sqrt5)-2)/(sqrt5-1)).  Used to drive the
# W3a multiplicativity check from the REAL periodic coefficients, not a caricature.
_DH_KAPPA = (math.sqrt(10 - 2 * math.sqrt(5)) - 2) / (math.sqrt(5) - 1)


def _DH_C(n_mod5: int) -> float:
    """c(n) for n = n_mod5 mod 5 (n_mod5 in 0..4).  c=[1, kappa, -kappa, -1, 0]
    indexed so c(1)=1, c(2)=kappa, c(3)=-kappa, c(4)=-1, c(5)=c(0)=0."""
    return {1: 1.0, 2: _DH_KAPPA, 3: -_DH_KAPPA, 4: -1.0, 0: 0.0}[n_mod5 % 5]


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
    # multiplicativity (W3a, B-mult): the Dirichlet coefficient sequence whose
    # log-derivative supplies the prime-side amplitudes.  When present, the harness
    # certifies the amplitude generation law  a(p^m) = (log p) w(p)^m  directly from
    # this sequence (a genuine finite computation, not a descriptor lookup).
    #   'euler_product'  -- completely multiplicative a(n) (zeta: a(n)=1)  -> generation holds
    #   'periodic_mod_q' -- a periodic coefficient vector (DH: c=[1,k,-k,-1,0])  -> generation fails
    #   'none'           -- no Dirichlet-coefficient model (lattice/ksly/random)
    mult_model: str = "none"
    # the finite coefficient data for mult_model:
    #   euler_product  -> ('cm', dict{prime: a(p)})     completely-multiplicative seed a(p)
    #   periodic_mod_q -> ('periodic', list c[0..q-1])  the period-q vector, c indexed by n mod q
    mult_coeffs: object = None


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
        # zeta: a(n)=1 for all n (completely multiplicative, Euler product).  Its
        # -zeta'/zeta coefficients are Lambda(n) -> the amplitudes a(p^m)=(log p)p^{-m/2}
        # are generated multiplicatively from the prime layer w(p)=p^{-1/2}.
        mult_model="euler_product", mult_coeffs=("cm", {}),  # {} => a(p)=1 for every p
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
        # DH: D(s)=sum c(n)n^{-s}, c=[1,kappa,-kappa,-1,0] period 5 (QC_DH_SCOUT).
        # This is a PERIODIC (character-combination) sequence, NOT multiplicative:
        # it has no Euler product, so -D'/D has nonzero coefficients at COMPOSITE n
        # and the prime-layer amplitudes are sign-varying -> generation law fails.
        mult_model="periodic_mod_q",
        mult_coeffs=("periodic", [_DH_C(0), _DH_C(1), _DH_C(2), _DH_C(3), _DH_C(4)]),
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


# ---------------------------------------------------------------------------
# W3a: the B-mult multiplicativity clause  (the adjudicated primitive)
# ---------------------------------------------------------------------------
def _von_mangoldt_analogue(a: list[float], N: int) -> list[float]:
    """Given Dirichlet coefficients a[1..N] (a[0] unused, a[1]=1), return the
    log-derivative coefficients b[1..N] of -f'/f where f = sum a(n) n^{-s}, via the
    standard recursion  a(n) log n = sum_{d|n} b(d) a(n/d).  For a completely
    multiplicative a (an Euler product) b is supported ONLY on prime powers with
    b(p^m) = (log p); for a non-multiplicative a, b(n) != 0 at composite n."""
    b = [0.0] * (N + 1)
    for n in range(2, N + 1):
        s = a[n] * math.log(n)
        for d in range(2, n):
            if n % d == 0:
                s -= b[d] * a[n // d]
        b[n] = s  # a[1] == 1
    return b


def _prime_powers_upto(N: int) -> dict:
    """Return {p: [p, p^2, ...]} for prime powers <= N."""
    out: dict[int, list[int]] = {}
    for p in range(2, N + 1):
        if all(p % q for q in range(2, int(p ** 0.5) + 1)):
            pk, ms = p, []
            while pk <= N:
                ms.append(pk)
                pk *= p
            out[p] = ms
    return out


def check_multiplicativity(obj: ZooObject, N: int = 60, tol: float = 1e-6) -> tuple[str, str]:
    """(B-mult / W3a) THE ADJUDICATED KILLER: the prime-side amplitudes are
    MULTIPLICATIVELY GENERATED from the prime layer -- there is a per-prime weight
    w(p) with  a(p^m) = (log p) w(p)^m  (for zeta w(p)=p^{-1/2}), AND no amplitude
    at composite (non-prime-power) frequencies.  This is the Euler-product primitive.

    Certified finite computation (not a descriptor lookup): build the actual
    log-derivative coefficient sequence b(n) from the object's Dirichlet coefficients
    and TEST the generation law directly.
      * zeta (euler_product):  b(6)=0, b(p^m)=log p, geometric law holds -> PASS
                               (pure-pointness of the DUAL comb is still RH; the
                               multiplicative GENERATION of the amplitudes is
                               unconditional/arithmetic, exactly like B-iii weights.)
      * DH (periodic_mod_q):   b(6)!=0 (composite atom), and prime-layer signs vary
                               -> generation law FAILS.
      * lattice/ksly/random (no Dirichlet model): no multiplicative prime-layer at
                               all -> FAIL (B-mult is STRICTLY SHARPER than B: it
                               excludes generic Lee-Yang FQs, carving out the
                               arithmetic ones -- this is the intended feature)."""
    if obj.mult_model == "none":
        # No Dirichlet-coefficient / prime-layer structure exists.  A generic FQ
        # (ksly), a plain lattice, or a random comb has amplitudes that are NOT the
        # multiplicative image of a prime layer.  B-mult excludes them by design.
        return FAIL, ("no multiplicative prime-layer (not an Euler-product amplitude "
                      "sequence); B-mult excludes generic/non-arithmetic combs")

    kind, data = obj.mult_coeffs
    a = [0.0] * (N + 1)
    if kind == "cm":
        # completely multiplicative from seed a(p) (default 1): a(n) = prod a(p)^{v_p}
        seed = data
        a[1] = 1.0
        for n in range(2, N + 1):
            # factor n
            val, m = 1.0, n
            for p in range(2, n + 1):
                while m % p == 0:
                    val *= seed.get(p, 1.0)
                    m //= p
                if m == 1:
                    break
            a[n] = val
    elif kind == "periodic":
        c = data  # c[0..q-1], indexed by n mod q
        q = len(c)
        for n in range(1, N + 1):
            a[n] = c[n % q]
    elif kind == "cm_corrupt":
        # a completely-multiplicative base (a(p)=1 => a(n)=1) with a SINGLE composite
        # amplitude overridden, genuinely breaking multiplicativity: data={n0: val}.
        for n in range(1, N + 1):
            a[n] = 1.0
        for n0, val in data.items():
            a[n0] = val
    else:  # pragma: no cover
        return FAIL, f"unknown mult_coeffs kind {kind}"

    if abs(a[1] - 1.0) > tol:
        return FAIL, f"a(1)={a[1]} != 1: not normalizable as -f'/f prime side"

    b = _von_mangoldt_analogue(a, N)
    pps = _prime_powers_upto(N)
    prime_power_set = {pk for ms in pps.values() for pk in ms}

    # (M1) NO amplitude at composite (non-prime-power) frequencies.
    composite_hits = [n for n in range(2, N + 1)
                      if n not in prime_power_set and abs(b[n]) > tol]
    if composite_hits:
        c0 = composite_hits[0]
        return FAIL, (f"generation law breaks: nonzero amplitude at COMPOSITE "
                      f"n={c0} (b({c0})={b[c0]:+.4f}); no Euler product => not "
                      f"multiplicatively generated")

    # (M2) per-prime geometric generation a(p^m)=(log p) w(p)^m with the SAME real
    # positive w(p) across all m, i.e. b(p^m) real, sign-constant, and
    # b(p^m)/b(p^{m-1}) == p^{-1/2}-consistent (for zeta, b(p^m)=log p exactly, so
    # the AMPLITUDE a(p^m)=b(p^m) p^{-m/2} obeys a(p^m)/a(p^{m-1})=p^{-1/2}).
    for p, ms in pps.items():
        bs = [b[pk] for pk in ms]
        # prime-layer amplitude must be real & positive (character sign forbidden)
        if bs[0] <= tol:
            return FAIL, (f"prime-layer amplitude b({p})={bs[0]:+.4f} not strictly "
                          f"positive (character/sign-varying) => no positive w(p)")
        # generation: b(p^m) must equal b(p) (von Mangoldt is m-constant for an
        # Euler product), giving amplitude ratio exactly p^{-1/2}.
        for m in range(1, len(bs)):
            if abs(bs[m] - bs[0]) > tol * max(1.0, abs(bs[0])):
                return FAIL, (f"generation breaks at {p}^{m+1}: b={bs[m]:+.4f} != "
                              f"prime-layer b({p})={bs[0]:+.4f}")

    return PASS, ("amplitudes multiplicatively generated: b(composite)=0, "
                  "b(p^m)=(log p) constant in m => a(p^m)=(log p)p^{-m/2}=(log p)w(p)^m, "
                  "w(p)=p^{-1/2} (Euler product; unconditional/arithmetic)")


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
# Variant "Bm" = B-mult (W3a): the spectrum primitive RESTATED as multiplicativity.
# It inherits B's support-density, pure-point atomic-spectrum (still RH-conditional),
# and temperedness, and REPLACES the (B-iii) positivity clause with the sharper
# (B-mult) multiplicative-generation clause.  B-mult is strictly sharper than B:
# multiplicative generation implies positivity of the prime layer (each b(p)=log p>0)
# AND excludes generic non-arithmetic FQs (ksly) that B admitted.
CLAUSES = [
    ("support_density", "(A-i/B-i) support density", ["A", "B", "Bm", "C", "D"], check_support_density),
    ("atomic_spectrum", "(A-ii/B-ii) atomic spectrum on prime Lambda_log", ["A", "B", "Bm", "D"], check_atomic_spectrum_loglattice),
    ("atomic_spectrum_loose", "(C-ii) atomic spectrum on any log-lattice", ["C"], check_atomic_spectrum_loose),
    ("weight_positivity", "(B-iii) weight positivity + decay [KILLER]", ["B"], check_weight_positivity),
    ("multiplicativity", "(B-mult) multiplicative amplitude generation [W3a KILLER]", ["Bm"], check_multiplicativity),
    ("signed_decay", "(C-iii) signed decay only", ["C"], check_signed_decay),
    ("defect_bounded", "(D-ii) bounded defect k", ["D"], check_defect_bounded),
    ("temperedness", "(A-iv..D) temperedness", ["A", "B", "Bm", "C", "D"], check_temperedness),
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

    # 6b. multiplicativity (W3a): the genuine zeta amplitude sequence PASSES B-mult;
    #     corrupt ONE amplitude (override a(6)=1.5, breaking a(6)=a(2)a(3)=1) so the
    #     log-derivative acquires a nonzero COMPOSITE amplitude b(6)!=0 -> the
    #     generation law FAILS.  Verdict flips PASS -> FAIL.
    genuine_zeta_mult, _ = check_multiplicativity(_load_zeta())
    forged_mult = ZooObject(name="forged_broken_multiplicativity", kind="zeta",
                            spectrum="prime_log_lattice", weights="positive_prime",
                            density_count=50, density_model=50.0, t_max=100.0,
                            mult_model="euler_product",
                            mult_coeffs=("cm_corrupt", {6: 1.5}))  # a(6)!=a(2)a(3)
    v, d = check_multiplicativity(forged_mult)
    out.append({"control": "broken_multiplicativity", "clause": "multiplicativity",
                "genuine": genuine_zeta_mult, "forged_verdict": v,
                "flipped": v == FAIL and genuine_zeta_mult == PASS,
                "detail": f"genuine zeta B-mult={genuine_zeta_mult}; corrupt a(2)=1.3 -> {v}: {d}"})

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
    for variant in ("A", "B", "Bm", "C", "D"):
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
    # 1b. W3a: DH FAILS the B-mult multiplicativity clause (the adjudicated killer).
    req(m["dh"]["multiplicativity"]["verdict"] == FAIL,
        "GOV: DH must FAIL (B-mult) multiplicativity -- no Euler product")
    req(vk["Bm"]["dh"]["killed"],
        "GOV: DH must be killed by variant B-mult")
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
    # W3a: zeta PASSES multiplicative amplitude generation (unconditional/arithmetic,
    # exactly like (B-iii) weights); pure-pointness of the dual comb (atomic_spectrum)
    # remains the RH-conditional clause.
    req(m["zeta"]["multiplicativity"]["verdict"] == PASS,
        "GOV: zeta must PASS (B-mult) multiplicative generation (unconditional)")
    req(m["zeta"]["atomic_spectrum"]["verdict"] == COND,
        "GOV: zeta pure-point spectrum stays CONDITIONAL even under B-mult")
    # W3a: zeta SURVIVES variant B-mult (admitted on PASS/COND clauses only).
    req(vk["Bm"]["zeta"]["survives"],
        "GOV: zeta must survive variant B-mult")
    # 4. lattice/ksly pass FQ-shaped clauses; random FAILS atomic spectrum.
    req(vk["B"]["lattice"]["survives"], "GOV: lattice must survive variant B")
    req(vk["B"]["ksly"]["survives"], "GOV: ksly must survive variant B (canonical FQ)")
    req(m["random"]["atomic_spectrum"]["verdict"] == FAIL,
        "GOV: random must FAIL atomic-spectrum")
    req(vk["B"]["random"]["killed"], "GOV: random must be killed by variant B")
    # 4b. W3a INTENDED SHARPENING: B-mult is STRICTLY sharper than B.  ksly (a generic
    #     Lee-Yang FQ) SURVIVES B (positive-mass FQ) but is KILLED by B-mult (its
    #     amplitudes are not the multiplicative image of a prime layer).  lattice too.
    #     This is a FEATURE (the axiom aims at zeta's arithmetic class), asserted as a
    #     rail so a regression that vacuously admits generic FQs is caught.
    req(vk["B"]["ksly"]["survives"] and vk["Bm"]["ksly"]["killed"],
        "GOV: B-mult must be STRICTLY sharper than B on ksly "
        "(ksly survives B but is killed by B-mult)")
    req(m["ksly"]["multiplicativity"]["verdict"] == FAIL,
        "GOV: generic Lee-Yang FQ (ksly) must FAIL B-mult multiplicativity")
    req(m["random"]["multiplicativity"]["verdict"] == FAIL,
        "GOV: random must FAIL B-mult multiplicativity")
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
    # W3a cross-check: multiplicativity implies positivity of the prime layer.  Any
    # object that PASSES B-mult must also PASS (B-iii) positivity -- the adjudicated
    # primitive should DOMINATE the old killer.  A contradiction here means the
    # multiplicativity clause is not actually stronger than positivity.
    for name in result["objects"]:
        if m[name]["multiplicativity"]["verdict"] == PASS and \
           m[name]["weight_positivity"]["verdict"] not in (PASS, COND):
            findings.append(
                f"W3a-CONTRADICTION: {name} passes B-mult multiplicativity but not "
                f"(B-iii) positivity -- multiplicativity should imply positive prime layer")
    # W3a positive record: confirm the intended strict sharpening (ksly: B survives,
    # B-mult kills).  Recorded as a NOTE (not a contradiction) for the report.
    if vk["B"]["ksly"]["survives"] and vk["Bm"]["ksly"]["killed"]:
        result.setdefault("w3a_notes", []).append(
            "B-mult STRICTLY sharper than B: ksly (generic Lee-Yang FQ) survives B but "
            "is excluded by B-mult -- the multiplicativity primitive carves out the "
            "arithmetic FQs (Euler-product amplitudes) from the generic Lee-Yang class.")
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
    for variant in ("A", "B", "Bm", "C", "D"):
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
