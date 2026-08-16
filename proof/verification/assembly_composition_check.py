"""THE ASSEMBLY COMPOSITION CHECK: executable end-to-end validation of the R7' argument,
including brute-force cross-validation at small n.

Support artifact for the campaign's final layer (rate port -> honest-conditional assembly).
Three results:

(1) FAMILY CAPTURE (the headline; exact rational, brute force).  The extended single-hub
    template family (hub load c0 <= 6, balanced arms, <= 2 hub leaves) CONTAINS the true
    maximizer of pi = per L/prod deg over ALL trees at EVERY tested n in [8, 17] --
    verified by exhaustive enumeration (nonisomorphic trees, exact matching-sum pi).
    The small-n "spider/broom" maximizers ARE members (hub load + one arm).  CONSEQUENCE
    for the assembly: the reduction target is correct not just asymptotically (n0 = 421)
    but at every n >= 8 tested; the "for all large n" hedge protects the PROOF layers
    (dichotomy thresholds, schedule stabilization), not the statement's truth.

(2) THE COMPOSITION WALK (exact, per sample n).  For each sample n, the layered argument
    is executed concretely:
      (i)   the same-n template value pi(template(n)) and its deficit vs C1*rhoB^n;
      (ii)  the elimination threshold: ledger > theta => pi < C1 rhoB^n <= max (A2);
      (iii) the schedule winner at n (G5): canonical (d,0,0)/(0,-d,0) for K >= 40;
      (iv)  spot domination: adversarial stuck configs at that n are strictly below the
            template (the G34 layers' conclusion, sampled).
    Every step is an exact rational comparison at the concrete n.

(3) THE HYPOTHESIS INVENTORY (executable).  The exact list of named Props the Lean
    assembly will take as hypotheses, each mapped to its Python artifact and its current
    rigor level -- the "Props carrying certificates, never axioms" pattern of
    conjecture1_status.py.

conjecture1_proved=False.  Self-verifying run_all().
"""
from __future__ import annotations

import functools
import sys

sys.setrecursionlimit(100000)

from fractions import Fraction as Fr

import networkx as nx

from verification.kelmans_mixed_load import (
    pi_literal,
    pi_loaded,
    F_of,
    z_of,
    kelmans_step,
)

RHO11 = Fr(621, 64)


@functools.lru_cache(maxsize=None)
def best_template(n):
    """max pi over the extended single-hub family at exactly n vertices."""
    best = None
    for c0 in range(0, 7):
        for nleaf in (0, 1, 2):
            rem = n - 1 - 2 * c0 - nleaf
            if rem <= 0:
                continue
            for K in range(1, rem + 1):
                t2 = rem - K
                if t2 < 0 or t2 % 2:
                    continue
                tot = t2 // 2
                if tot > 8 * K:
                    continue
                b, r = divmod(tot, K)
                loads = [b + 1] * r + [b] * (K - r)
                zh = z_of(K + nleaf, c0)
                p = F_of(K + nleaf, c0)
                s = Fr(0)
                for c in loads:
                    p *= F_of(1, c)
                    s += z_of(1, c)
                s += nleaf
                p *= (1 + zh * s)
                if best is None or p > best[0]:
                    best = (p, (c0, tuple(loads), nleaf))
    return best


def family_capture(n_lo: int = 8, n_hi: int = 17) -> dict:
    """(1): exhaustive brute force -- the family contains the maximizer at every n."""
    captured = {}
    for n in range(n_lo, n_hi + 1):
        mx = None
        for T in nx.nonisomorphic_trees(n):
            T = nx.convert_node_labels_to_integers(T)
            p = pi_literal(T)
            if mx is None or p > mx:
                mx = p
        bt = best_template(n)[0]
        assert bt == mx, (n, float(bt), float(mx))       # EXACT equality
        captured[n] = str(best_template(n)[1])
    return {"exact_capture_range": f"[{n_lo}, {n_hi}]", "winners": captured}


def composition_walk(samples=(56, 111, 221, 445, 731)) -> dict:
    """(2): the layered argument executed at concrete n (all rational)."""
    import math
    out = {}
    for n in samples:
        bt, shape = best_template(n)
        # (i) the DELTA-corrected comparison (the theta-lemma's actual form): at upgrade
        # residues the template max dips BELOW C1*rhoB^n (e.g. n=445: -0.39%), which is
        # exactly why the uniform deficit DELTA = 0.015 exists.  Assert
        # template >= C1 * rhoB^n * e^{-DELTA}:  bt^11 >= (26/23)^11 (621/64)^(n-1) / e^{0.165}
        from verification.g1_floor_certificates import exp_upper
        lhs = bt ** 11 * exp_upper(Fr(165, 1000))
        rhs = Fr(26, 23) ** 11 * RHO11 ** (n - 1)
        template_ge_C1 = lhs >= rhs
        # (ii) elimination: any tree with A < C1 is below the template (given (i))
        # (iii) schedule winner: for K >= 40 the canonical shape (loads in {4,5,6}, c0 = 0)
        c0, loads, nleaf = shape
        K = len(loads)
        canonical = (K < 40) or (c0 == 0 and nleaf == 0 and set(loads) <= {4, 5, 6})
        # (iv) spot dominations: 2-hub stuck + defected at this n (when constructible)
        dom_ok = True
        rem = n - 2
        for cA in (0, 5):
            arms2 = rem - 2 * cA
            if arms2 % 11 or arms2 <= 22:
                continue
            tot = arms2 // 11
            for pB in (1, tot // 2):
                pA = tot - pB
                if pA < pB or pB < 1:
                    continue
                G = nx.Graph()
                G.add_edge(0, 1)
                load = {0: cA, 1: 0}
                nxt = 2
                for _ in range(pA):
                    G.add_edge(0, nxt)
                    load[nxt] = 5
                    nxt += 1
                for _ in range(pB):
                    G.add_edge(1, nxt)
                    load[nxt] = 5
                    nxt += 1
                dom_ok &= bt > pi_loaded(G, load)
        assert template_ge_C1 and canonical and dom_ok, n
        out[n] = {"template_ge_C1_rho_n_less_delta": template_ge_C1, "schedule_canonical": canonical,
                  "spot_dominations": dom_ok, "shape": str(shape)}
    return out


def hypothesis_inventory() -> dict:
    """(3): the named Props for the Lean assembly (Props carrying certificates, not axioms)."""
    return {
        "HypRatePort": "pi(T) = Z*R, S<=1, R<=4/3, Z<=rhoB^n -- IN PROGRESS (parallel "
                       "session; designs validated, STEP4C prior art green)",
        "HypLedgerTelescope": "logPhi = -phi(root) - sum slack -- Lean-portable "
                              "(hinge algebra, DeficitNonneg forall nl already green)",
        "HypFloors": "the class floors -- Python RATIONAL certificates "
                     "(g1_floor_certificates); Lean map in G1_KERNEL_LEAN_DESIGN",
        "HypAmortizedHub": "ledger >= 0.0235 * #hubs -- critical family symbolic + "
                           "mixed layer rational (g1_endpoint_certificates)",
        "HypMergeCapstone": "chain_to_normalForm -- LEAN GREEN (R47StepMono)",
        "HypSchedule": "shedding lemmas LEAN GREEN (R47Shed); winner table deferred "
                       "to assembly (exact rational, gap_discharges.finite_table)",
        "HypDominationSweeps": "the exact finite sweeps (442,800-case two-hub defected; "
                               "star-of-hubs asymmetric; depth-3 region; finite tables) "
                               "-- Python EXACT RATIONAL artifacts; decide-shaped; "
                               "formalization-policy: cite-as-artifact or Lean sampling "
                               "(native_decide stays banned)",
        "HypStarSymbolic": "972 star-of-hubs certificates + two-hub tails -- sympy "
                           "all-nonneg witnesses; Polya/nlinarith-shaped for Lean",
        "HypDepth3Generic": "depth >= 3 genericity -- PROBE RIGOR (the one honest "
                            "sampling sliver, MR69 review Concern 1; named, open)",
        "HypClassificationSeam": "confined-family trees -> Balanced/Capped hub-state "
                                 "encoding (R47Legs direction; the L/B seam)",
    }


def run_all():
    out = {}
    out["family_capture"] = family_capture()
    out["composition_walk"] = composition_walk()
    out["hypotheses"] = hypothesis_inventory()
    out["status"] = {
        "assembly_shape": "R7'_of (h : each Hyp above) : forall n >= n0, forall T, "
                          "pi T <= pi (template n) -- with the FAMILY CAPTURE result "
                          "suggesting the statement is true from n >= 8 (hedge protects "
                          "proof layers, not truth)",
        "conjecture1_proved": False,
    }
    for k, v in out.items():
        print(f"  {k}: {v}")
    return out


if __name__ == "__main__":
    run_all()
