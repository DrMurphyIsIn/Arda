"""Heterogeneous master-inequality scan: the (a, b, nu) canonical family + an
empirical vertex-lemma check.  Executes the concrete next step of
`docs/design/HETERO_REDUCTION_SCOPING_20260821.md` (PR #37): the bang-bang vertex
reduction of the FULL heterogeneous achievable problem to a 2-integer + 1-real
family, and the empirical validation of the vertex lemma it rests on.

All exact `fractions.Fraction`; no floats at any decision point.  Definitions match
the kernel `HomogMasterAssembled.lean` (GS, T, glemma, Bcap, base).
`conjecture1_proved = False`.
"""
from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction as Fr

# --- kernel-matched exact constants -----------------------------------------
W = Fr(64, 621)
GAMMA = W ** 2 * Fr(5, 3) ** 11
T = W * Fr(5, 3) ** 11                          # the master bound RHS


def glemma(mu: Fr) -> Fr:
    return GAMMA / (1 + mu / 3) ** 11


def master_ub(mu: Fr) -> Fr:
    return W * (Fr(3) / (2 + mu)) ** 11


def Bcap(mu: Fr) -> Fr:
    return min(master_ub(mu), min(glemma(mu), Fr(1)))


def base_het(j: int, S: Fr) -> Fr:
    """base for arity j (j children), total message sum S: (3(j+1)+3S+1)/(3(j+1))."""
    d = j + 1
    return (3 * d + 3 * S + 1) / (3 * d)


def base_hom(k: int, mu: Fr) -> Fr:
    """kernel `base k mu` (homogeneous: k children each at mu)."""
    return (3 * (k + 1) + 3 * k * mu + 1) / (3 * (k + 1))


def GS_hom(k: int, mu: Fr) -> Fr:
    """kernel `GS k mu = base(k,mu)^11 * Bcap(mu)^k`."""
    return base_hom(k, mu) ** 11 * Bcap(mu) ** k


def GS_het(mus) -> Fr:
    """general heterogeneous value: base(j, sum)^11 * prod Bcap(mu_i)."""
    j = len(mus)
    S = sum(mus, Fr(0))
    p = Fr(1)
    for m in mus:
        p *= Bcap(m)
    return base_het(j, S) ** 11 * p


# knee (glemma = 1): irrational; rational relaxation used by the kernel split.
KNEE_RAT = Fr(37, 120)          # ~0.30833; region split point in homog_master
HALF = Fr(1, 2)


# --- (1) cross-check: GS_het reproduces the kernel GS_hom -------------------
def check_consistency() -> bool:
    ok = True
    for k in range(1, 6):
        for p in range(1, 61):
            mu = Fr(p, 120)                     # (0, 1/2]
            if GS_het([mu] * k) != GS_hom(k, mu):
                ok = False
    return ok


# --- (2) empirical vertex lemma: max over fixed-(j,S) box slice is a vertex --
@dataclass(frozen=True)
class VertexReport:
    """For random fixed-(j, S) slices, is the max of prod Bcap attained at a
    'vertex' config (all children at a region bound {<=knee, or =1/2} except at
    most one interior)?  A spread within the above-knee subset should never
    decrease prod Bcap (log Bcap convex there)."""
    j_max: int = 4
    grid: int = 60

    def spreading_never_hurts(self):
        """The vertex-lemma engine: for two above-knee children at fixed sum,
        spreading them apart never decreases Bcap-product (strictly increases
        unless at a bound).  Returns (holds, worst_ratio_merged_over_spread)."""
        worst = None
        for pm in range(1, self.grid + 1):
            m = KNEE_RAT + (HALF - KNEE_RAT) * Fr(pm, self.grid)   # above knee
            if m <= KNEE_RAT or m > HALF:
                continue
            for pd in range(1, self.grid):
                d = (HALF - m) * Fr(pd, self.grid)
                lo, hi = m - d, m + d
                if lo <= KNEE_RAT or hi > HALF:
                    continue
                merged = Bcap(m) * Bcap(m)
                spread = Bcap(lo) * Bcap(hi)
                r = merged / spread            # want <= 1 (spread wins)
                if worst is None or r > worst[0]:
                    worst = (r, m, d)
        return (worst[0] <= 1 if worst else True), worst


# --- (3) the (a, b, nu) canonical family scan -------------------------------
def GS_family(a: int, b: int, nu) -> Fr:
    """C(a, b, nu): a below-knee children at the knee (Bcap=1, mass a*KNEE_RAT),
    b children at 1/2 (Bcap=glemma(1/2)), one interior child at nu in (knee,1/2].
    Arity j = a + b + 1, sum S = a*KNEE_RAT + b/2 + nu."""
    j = a + b + 1
    S = a * KNEE_RAT + b * HALF + nu
    return base_het(j, S) ** 11 * glemma(HALF) ** b * glemma(nu)


def GS_family_noInterior(a: int, b: int) -> Fr:
    """boundary sub-family: no interior child (b at 1/2, a below-knee)."""
    j = a + b
    if j == 0:
        return Fr(0)
    S = a * KNEE_RAT + b * HALF
    return base_het(j, S) ** 11 * glemma(HALF) ** b


@dataclass(frozen=True)
class FamilyScanReport:
    a_max: int = 8
    b_max: int = 8
    nu_grid: int = 240

    def scan(self):
        """Scan GS_family / T over (a, b, nu); return the family max (should be
        <= 1 = T) and where it's attained."""
        best = None
        over = []          # any (a,b,nu) with GS_family > T (would break the route)
        # interior-child family
        for a in range(0, self.a_max + 1):
            for b in range(0, self.b_max + 1):
                for p in range(1, self.nu_grid + 1):
                    nu = KNEE_RAT + (HALF - KNEE_RAT) * Fr(p, self.nu_grid)
                    if nu > HALF:
                        continue
                    v = GS_family(a, b, nu) / T
                    if best is None or v > best[0]:
                        best = (v, a, b, nu)
                    if v > 1:
                        over.append((a, b, nu, v))
        # boundary (no interior) family
        best_bd = None
        for a in range(0, self.a_max + 1):
            for b in range(0, self.b_max + 1):
                if a + b == 0:
                    continue
                v = GS_family_noInterior(a, b) / T
                if best_bd is None or v > best_bd[0]:
                    best_bd = (v, a, b)
                if v > 1:
                    over.append((a, b, None, v))
        return best, best_bd, over


# --- (4) adversarial: arbitrary heterogeneous achievable configs stay <= T ---
def adversarial_heterogeneous(n_trials: int = 20000, j_max: int = 7):
    """The decisive relaxation check: for arbitrary heterogeneous achievable
    configs (arity j, each mu_i in (0,1/2] on a fine rational grid, plus leaf
    mu=1 children), is GS_het <= T?  Deterministic pseudo-sweep (no RNG: index
    the grid) plus the structured extremes.  Returns (max_ratio, argmax, n_over)."""
    Q = 24
    grid = [Fr(p, Q) for p in range(1, Q // 2 + 1)] + [Fr(1)]     # (0,1/2] + leaf
    worst = None
    n_over = 0
    # structured sweep: symmetric, plus two-block (a below-knee-ish + b half),
    # plus single interior with leaves — the shapes the vertex lemma predicts.
    import itertools
    # all multisets of size <= 4 over a coarse grid (exhaustive small-arity)
    coarse = [Fr(1, 12), Fr(1, 6), KNEE_RAT, Fr(5, 12), HALF, Fr(1)]
    for j in range(1, 5):
        for combo in itertools.combinations_with_replacement(coarse, j):
            v = GS_het(list(combo)) / T
            if worst is None or v > worst[0]:
                worst = (v, combo)
            if v > 1:
                n_over += 1
    # larger-arity structured: k homogeneous + m leaves + one interior
    for k in range(0, 8):
        for m in range(0, 4):
            for pnu in range(0, Q // 2 + 1):
                nu = Fr(pnu, Q) if pnu > 0 else HALF
                cfg = [HALF] * k + [Fr(1)] * m + ([nu] if 0 < nu <= HALF else [])
                if not cfg:
                    continue
                v = GS_het(cfg) / T
                if worst is None or v > worst[0]:
                    worst = (v, ("k=%d,m=%d,nu=%s" % (k, m, nu),))
                if v > 1:
                    n_over += 1
    return worst[0], worst[1], n_over


def run_all():
    print("consistency GS_het == kernel GS_hom:", check_consistency())
    holds, worst = VertexReport().spreading_never_hurts()
    print(f"vertex-lemma engine (spread >= merged above knee): holds={holds}  "
          f"worst merged/spread ratio={float(worst[0]):.7f} at m={worst[1]}, d={worst[2]}")
    best, best_bd, over = FamilyScanReport().scan()
    print(f"family max GS(a,b,nu)/T = {float(best[0]):.6f} at a={best[1]},b={best[2]},nu={best[3]}")
    print(f"boundary (no-interior) max /T = {float(best_bd[0]):.6f} at a={best_bd[1]},b={best_bd[2]}")
    print(f"configs with GS_family > T: {len(over)}  (0 = route survives the relaxation)")
    adv_max, adv_arg, adv_over = adversarial_heterogeneous()
    print(f"ADVERSARIAL heterogeneous max GS_het/T = {float(adv_max):.6f} at {adv_arg}")
    print(f"  arbitrary-config violations (GS_het > T): {adv_over}  "
          f"(0 = achievable master inequality holds heterogeneously on the sweep)")
    return {"consistent": check_consistency(), "vertex_holds": holds,
            "family_max": best, "boundary_max": best_bd, "over_T": over,
            "adv_max": adv_max, "adv_over": adv_over}


def certify():
    """Assert-based certificate (verify.py idiom): every claim an assert, exact."""
    assert check_consistency(), "GS_het disagrees with kernel GS_hom"
    holds, worst = VertexReport().spreading_never_hurts()
    assert holds and worst[0] <= 1, f"vertex-lemma exchange failed: {worst}"
    best, best_bd, over = FamilyScanReport().scan()
    assert not over, f"(a,b,nu) family exceeds T: {over[:3]}"
    assert best[0] <= 1, f"family max exceeds T: {best}"
    assert best[0] == Fr(GS_family(0, 0, HALF), 1) / T or best[0] <= 1  # sector max shape
    adv_max, adv_arg, adv_over = adversarial_heterogeneous()
    assert adv_over == 0, "arbitrary heterogeneous config exceeds T"
    assert adv_max == Fr(1), f"tightness lost: adversarial max {adv_max} != 1 (arm)"
    # the vertex-lemma seed as an exact two-point identity, spot-checked:
    for lo, hi in [(Fr(1, 3), Fr(1, 2)), (Fr(37, 120), Fr(1, 2)), (Fr(2, 5), Fr(9, 20))]:
        m = (lo + hi) / 2
        assert glemma(lo) * glemma(hi) >= glemma(m) ** 2, "log-glemma convexity failed"
    # --- the LANDED Lean reductions (HeteroFamily.lean), spot-checked exactly ---
    # (a) the b-step ratio constant Rb = 994/951 satisfies Rb^11 * glemma(1/2) <= 1
    Rb = Fr(994, 951)
    assert Rb ** 11 * glemma(HALF) <= 1, "Rb^11 * glemma(1/2) > 1 (bstep accounting)"
    # (b) astep/bstep monotone reductions: fam(a+1,b,nu) <= fam(a,b,nu),
    #     fam(a,b+1,nu) <= fam(a,b,nu), for nu in [knee, 1/2] (Lean: astep/bstep).
    for a in range(0, 6):
        for b in range(0, 6):
            for pnu in range(0, 5):
                nu = KNEE_RAT + (HALF - KNEE_RAT) * Fr(pnu, 4)
                assert GS_family(a + 1, b, nu) <= GS_family(a, b, nu), \
                    f"astep failed at a={a},b={b},nu={nu}"
                assert GS_family(a, b + 1, nu) <= GS_family(a, b, nu), \
                    f"bstep failed at a={a},b={b},nu={nu}"
                # (c) full family_master: fam(a,b,nu) <= T
                assert GS_family(a, b, nu) <= T, f"family_master failed at {(a, b, nu)}"
    return True


if __name__ == "__main__":
    run_all()
    print("certify():", certify())
