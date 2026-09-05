"""RESIDUAL-CELL HUB-MOVER PROBE -- corrects the `three_hub_residual_probe` conjecture.

`kelmans_mixed_load.certify_general_env_box` box-certifies 25 of 30 load cells for the
adjacent hubward Kelmans step; the 5 residual cb-heavy cells {(0,5),(1,4),(1,5),(2,5),(3,5)}
are not box-certifiable.  `three_hub_residual_probe` tested them on 3-hub backbones and,
finding 0 decreases, conjectured the failure is "a CERTIFICATE artifact, not a real failure".

THAT PROBE ONLY TESTED B WITH >= 1 ARMS.  The box's failing corner is `sigma_S -> 0`, which
is reached when B's SOLE mover is a large de-loaded HUB (`z_C = 3/(3 deg_C + 4 load_C) -> 0`),
NOT an arm.  Probing that corner with EXACT Fraction arithmetic (below), restricted to the
theorem's own hypothesis `z_x <= 3/23` for every environment neighbour, shows:

    * (1,4), (1,5), (2,5):  the direct hubward step STRICTLY DECREASES pi at in-scope
      hub-mover configs -- a GENUINE failure, refuting the "certificate artifact" conjecture.
      These are true K/H-stuck configs: the direct merge is the wrong move (cf. the assisted
      merge for de-loaded donors).
    * (0,5), (3,5):  NO decrease found over the scanned in-scope region -- plausibly
      non-decreasing, the genuine "sharp follow-up" candidates (still unproven).

So the 5 residual cells are NOT a uniform certification gap: 3 are real obstructions to the
DIRECT step, 2 are plausibly certifiable.  The 25-cell `certify_general_env_box` theorem is
unaffected (it already excludes all 5).  Self-verifying: `run()` asserts the split.
conjecture1_proved = False.
"""
from __future__ import annotations

from fractions import Fraction as Fr

import networkx as nx

from verification.kelmans_mixed_load import pi_loaded, kelmans_step

RESIDUAL = [(0, 5), (1, 4), (1, 5), (2, 5), (3, 5)]
GENUINE_FAILURE = {(1, 4), (1, 5), (2, 5)}
NO_DECREASE_FOUND = {(0, 5), (3, 5)}


def _z(deg: int, load: int) -> Fr:
    return Fr(3, 3 * deg + 4 * load)


def _build(ca: int, cb: int, cc: int, pA: int, qB: int, r: int):
    """A(ca) - B(cb) - C(cc) path; A has pA arms, B has qB arms, C has r arms (load-5 leaves).
    The step merges B -> A (hubward when deg A >= deg B)."""
    G = nx.Graph()
    G.add_edge(0, 1)
    G.add_edge(1, 2)
    load = {0: ca, 1: cb, 2: cc}
    nxt = 3
    for hub, cnt in ((0, pA), (1, qB), (2, r)):
        for _ in range(cnt):
            G.add_edge(hub, nxt)
            load[nxt] = 5
            nxt += 1
    return G, load


def scan_cell(ca: int, cb: int, *, pA_max=14, r_max=32, qB_max=3):
    """Exact-Fraction scan of in-scope (`z_C <= 3/23`) hub-mover configs.  Returns
    ``(n_tested, n_decrease, worst_gain_or_None)``."""
    tested = neg = 0
    worst = None
    for pA in range(1, pA_max):
        for qB in range(0, qB_max):
            for r in range(0, r_max):
                for cc in (0, 5):
                    if _z(1 + r, cc) > Fr(3, 23):     # C outside the theorem's hypothesis
                        continue
                    G, load = _build(ca, cb, cc, pA, qB, r)
                    if not (G.degree(0) >= G.degree(1) >= 2):
                        continue
                    g = pi_loaded(kelmans_step(G, 0, 1), load) - pi_loaded(G, load)
                    tested += 1
                    if g < 0:
                        neg += 1
                        if worst is None or g < worst:
                            worst = g
    return tested, neg, worst


def run() -> dict:
    out = {}
    for (ca, cb) in RESIDUAL:
        tested, neg, worst = scan_cell(ca, cb)
        out[(ca, cb)] = {"tested": tested, "decreases": neg, "worst": float(worst) if worst else None}
        if (ca, cb) in GENUINE_FAILURE:
            assert neg > 0, f"expected in-scope decreases for genuine-failure cell {(ca, cb)}"
        else:
            assert neg == 0, f"unexpected decrease for no-decrease cell {(ca, cb)}"
    out["verdict"] = {
        "genuine_direct_step_failures": sorted(GENUINE_FAILURE),
        "no_decrease_found": sorted(NO_DECREASE_FOUND),
        "corrects": "three_hub_residual_probe 'certificate artifact' conjecture (refuted for 3/5 cells)",
        "conjecture1_proved": False,
    }
    return out


if __name__ == "__main__":
    for k, v in run().items():
        print(f"  {k}: {v}")
