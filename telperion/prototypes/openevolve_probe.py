"""THROWAWAY PROTOTYPE (spike) -- do NOT freeze, do NOT wire into CI.

Question this probe answers
---------------------------
Can Telperion's `certify -> hunt -> emit -> lake build` pipeline be wrapped as a
single, non-gameable *fitness function* and driven by an OpenEvolve/AlphaEvolve
style evolutionary loop that searches over CERTIFICATE PROGRAMS (not witness
points, which is what the shipped `hunt_evolve` already does)?

What this demonstrates
----------------------
A real family whose *naive* certificate shape does NOT certify:

    target(a) = (u^2 - u + a) / (u + 1)      for a in {1,2,3},  u >= 0

It is genuinely >= 0, but not Polya-as-spelled (the numerator is not a sum of
nonneg-coefficient terms). Telperion's `auto_lift` (multiply num+den by (1+u)^k)
and `auto_subdivide` knobs can rescue it. We treat those two knobs as an evolvable
GENOME and let a tiny GA discover a certifying, *parsimonious* certificate --
scored by the exact-arithmetic pipeline, with the Lean kernel as ground truth.

The four fitness tiers (cheap -> expensive), mirroring OpenEvolve's artifact loop:

    Tier 0  hunt()          adversarial: is the claim even TRUE? (exact witness)
    Tier 1  certify()       does this genome's certificate shape close, exactly?
    Tier 2  parsimony       among certifying genomes, prefer smaller Lean
    Tier 3  lake env lean   the champion is kernel-checked against real Mathlib

Tier 0 is the load-bearing distinction from a soft metric: a certify() FAILURE
is ambiguous (wrong shape vs false claim); hunt() disambiguates with an exact
rational counterexample, so we never waste a Lean compile on a false claim. This
is exactly the non-gameable property that makes Telperion a strong AlphaEvolve
substrate.

Run:  python3 prototypes/openevolve_probe.py
"""
from __future__ import annotations

import contextlib
import io
import os
import random
import subprocess
import sys
from dataclasses import dataclass
from pathlib import Path

import sympy as sp

REPO = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(REPO / "src"))

from telperion import (  # noqa: E402
    DirectPolyaEmitter,
    GridSpec,
    InequalityFamily,
    LeanProfile,
    ValidationReport,
    CertificationError,
    certify,
    emit,
)
from telperion.hunt import hunt_minimum  # noqa: E402

u = sp.Symbol("u", nonnegative=True)

# The prebuilt Mathlib project we borrow for the kernel gate (7.7G .lake, v4.32.0).
LEAN_PROJECT = REPO / "examples" / "g1_floors" / "lean"

# ---------------------------------------------------------------------------
# The two claims in the pool: one TRUE-but-wrong-shape, one FALSE control.
# ---------------------------------------------------------------------------
TARGETS = {
    # a>=1 => numerator u^2-u+a > 0, but not Polya as spelled -> needs a lift.
    "true": lambda pt: (u**2 - u + pt["a"]) / (u + 1),
    # (u-1)/(u+1) < 0 for u<1 (witness u=0 -> -1): a genuinely FALSE claim.
    "false": lambda pt: (u - 1) / (u + 1),
}


@dataclass(frozen=True)
class Genome:
    """The evolvable certificate structure. This is what an LLM would mutate."""
    lift: int          # auto_lift: multiply num+den by (1+u)^lift
    subdivide: int     # auto_subdivide: split the orthant into 2^subdivide cells
    target: str = "true"

    def mutate(self, rng: random.Random) -> "Genome":
        lift = max(0, min(6, self.lift + rng.choice((-1, 0, 1, 1))))
        sub = max(0, min(3, self.subdivide + rng.choice((-1, 0, 1))))
        return Genome(lift, sub, self.target)


def _family(g: Genome) -> InequalityFamily:
    return InequalityFamily(
        name="ToyLift",
        symbols=(u,),
        grid=GridSpec([("a", [1, 2, 3])]),
        lean_name=lambda pt: f"toy_lift_a{pt['a']}",
        target=lambda pt: TARGETS[g.target](pt),
        auto_lift=g.lift,
        auto_subdivide=g.subdivide,
    )


# ---------------------------------------------------------------------------
# The fitness cascade.  Returns (score, tag).  Higher is better.
# ---------------------------------------------------------------------------
DISPROVEN = -10_000.0

_hunt_cache: dict[str, bool] = {}


def _is_true(g: Genome) -> bool:
    """Tier 0: hunt() -- exact adversarial minimum over the closed orthant.
    Cached per target since it is genome-independent (shape does not change truth)."""
    if g.target in _hunt_cache:
        return _hunt_cache[g.target]
    truth = True
    fam = _family(g)
    for pt in fam.grid.points():
        r = hunt_minimum(fam.target(pt), [u], iters=120, restarts=4, seed=1)
        if r.is_disproof:
            truth = False
            break
    _hunt_cache[g.target] = truth
    return truth


def _certifies(g: Genome) -> tuple[bool, int]:
    """Tier 1: exact-arithmetic certify(). Returns (ok, n_failing_instances)."""
    fam = _family(g)
    with contextlib.redirect_stdout(io.StringIO()), contextlib.redirect_stderr(io.StringIO()):
        try:
            certify(fam)
            return True, 0
        except CertificationError as e:
            # count failing cells from the message; fall back to 1
            n = str(e).count("{'a'") or 1
            return False, n
        except Exception:
            return False, 3


def fitness(g: Genome) -> tuple[float, str]:
    if not _is_true(g):
        return DISPROVEN, "DISPROVEN (hunt exact witness) -- never emitted"
    ok, n_fail = _certifies(g)
    if not ok:
        # true claim, wrong shape: negative but ABOVE disproven, so the loop
        # keeps searching shapes instead of abandoning the claim.
        return -100.0 * n_fail, f"true, shape fails ({n_fail} cell(s))"
    # certifying: reward, minus parsimony penalty (smaller Lean preferred).
    complexity = g.lift + 2 * g.subdivide
    return 1000.0 - complexity, f"CERTIFIES (lift={g.lift}, subdivide={g.subdivide})"


# ---------------------------------------------------------------------------
# The evolutionary loop: a tiny GA over genomes.  The GA is a stand-in for
# LLM-driven mutation -- the *evaluator* is the point, the mutator is pluggable.
# A MAP-Elites-style archive keeps the best genome per complexity bin.
# ---------------------------------------------------------------------------
def evolve(target: str, gens: int = 12, pop: int = 8, seed: int = 0):
    rng = random.Random(seed)
    # Seed the population at the NAIVE shape (lift=0) and its neighbourhood, so we
    # can see the loop climb away from the failing baseline.
    population = [Genome(0, 0, target)]
    while len(population) < pop:
        population.append(Genome(rng.randint(0, 3), rng.randint(0, 1), target))

    archive: dict[int, tuple[float, Genome, str]] = {}   # complexity-bin -> best
    evals = 0
    history = []

    def record(g: Genome):
        nonlocal evals
        evals += 1
        s, tag = fitness(g)
        cbin = g.lift + 2 * g.subdivide
        if cbin not in archive or s > archive[cbin][0]:
            archive[cbin] = (s, g, tag)
        return s, tag

    scored = [(record(g)[0], g) for g in population]
    for gen in range(gens):
        scored.sort(key=lambda t: t[0], reverse=True)
        best_s, best_g = scored[0]
        history.append((gen, best_s, best_g))
        # elitism + tournament-selected mutated children
        nxt = scored[:2]
        while len(nxt) < pop:
            a = max(rng.sample(scored, min(3, len(scored))), key=lambda t: t[0])[1]
            child = a.mutate(rng)
            nxt.append((record(child)[0], child))
        scored = nxt

    scored.sort(key=lambda t: t[0], reverse=True)
    champ_s, champ = scored[0]
    return champ, champ_s, archive, evals, history


# ---------------------------------------------------------------------------
# Tier 3: the champion is emitted and kernel-checked against real Mathlib.
# ---------------------------------------------------------------------------
def kernel_check(g: Genome) -> tuple[bool, str]:
    fam = _family(g)
    with contextlib.redirect_stdout(io.StringIO()), contextlib.redirect_stderr(io.StringIO()):
        cert = certify(fam)
        res = emit(
            cert,
            LeanProfile(namespace=("ProbeToy",)),
            [DirectPolyaEmitter()],
            ValidationReport(checks=(("spot", True),)),
        )
    lean_src = next(iter(res.files.values()))
    kernel_check.last_lean = lean_src  # type: ignore[attr-defined]  # for reporting
    out_file = LEAN_PROJECT / "ProbeToy.lean"
    out_file.write_text(lean_src)
    try:
        proc = subprocess.run(
            ["lake", "env", "lean", str(out_file)],
            cwd=str(LEAN_PROJECT),
            capture_output=True,
            text=True,
        )
        ok = proc.returncode == 0
        msg = "kernel-GREEN" if ok else f"kernel-RED: {proc.stderr[:300]}"
        return ok, msg
    finally:
        out_file.unlink(missing_ok=True)


# ---------------------------------------------------------------------------
def main() -> None:
    print("=" * 74)
    print("Telperion x OpenEvolve -- evaluator-wrapper probe (THROWAWAY)")
    print("=" * 74)

    # --- baseline: the naive shape a human would write first ---
    naive = Genome(0, 0, "true")
    s, tag = fitness(naive)
    print(f"\n[baseline] naive genome {naive}: score={s:.0f}  -- {tag}")

    # --- control: the FALSE claim, to show hunt rejects it pre-emit ---
    false_g = Genome(0, 0, "false")
    fs, ftag = fitness(false_g)
    print(f"[control ] false  genome {false_g}: score={fs:.0f}  -- {ftag}")

    # --- evolve the TRUE claim ---
    print("\n[evolve  ] searching certificate genomes for the true claim ...")
    champ, champ_s, archive, evals, history = evolve("true")
    for gen, bs, bg in history:
        print(f"    gen {gen:2d}: best score {bs:7.0f}  lift={bg.lift} subdivide={bg.subdivide}")
    print(f"\n[champion] {champ}: score={champ_s:.0f}   ({evals} exact evaluations)")

    print("\n[archive ] MAP-Elites-style best-per-complexity-bin:")
    for cbin in sorted(archive):
        s, g, tag = archive[cbin]
        mark = "<-- champion" if g == champ else ""
        print(f"    complexity {cbin}: score {s:7.0f}  {tag} {mark}")

    # --- Tier 3: kernel gate on the champion ---
    print("\n[kernel  ] emitting champion + `lake env lean` against real Mathlib ...")
    ok, msg = kernel_check(champ)
    print(f"    {msg}")

    print("\n" + "=" * 74)
    print("VERDICT")
    print("=" * 74)
    print(f"  naive shape certifies : {'YES' if _certifies(naive)[0] else 'NO'}")
    print(f"  false claim rejected  : {'YES (hunt exact witness)' if fs == DISPROVEN else 'NO'}")
    print(f"  evolved champion cert : {'YES' if _certifies(champ)[0] else 'NO'} (lift={champ.lift}, subdivide={champ.subdivide})")
    print(f"  champion kernel-green : {'YES' if ok else 'NO'}")
    lean = getattr(kernel_check, "last_lean", "")
    thm = [l for l in lean.splitlines() if l.strip().startswith("theorem")]
    if thm:
        print(f"  emitted theorem       : {thm[0].strip()}")


if __name__ == "__main__":
    main()
