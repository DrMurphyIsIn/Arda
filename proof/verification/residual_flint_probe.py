"""Flint-accelerated large-scale verification of the residual-cell split.

`residual_hub_mover_probe.py` establishes, with `fractions.Fraction`, that the 5 residual
general-env cells split into 3 genuine direct-step failures (rescued by the anti-hubward
step) + 2 certifiable cells (0,5),(3,5).  The exact permanents blow up to hundreds of digits
for large hub-movers, so the Fraction scan is limited to `deg_C < ~32`.

This module reimplements `pi` with `python-flint`'s `fmpq` (~20x faster on the big-rational
matching-sum DP; VALIDATED against `kelmans_mixed_load.pi_loaded`) and re-runs the split over
a MUCH larger in-scope region, so the "no decrease" evidence for (0,5),(3,5) and the
"anti-hubward rescues all" claim for (1,4),(1,5),(2,5) rest on far more configs.  Requires
python-flint; `run()` is self-verifying.  conjecture1_proved = False.
"""
from __future__ import annotations

from fractions import Fraction as Fr

import networkx as nx
from flint import fmpq

from verification.kelmans_mixed_load import kelmans_step, pi_loaded

RESIDUAL = [(0, 5), (1, 4), (1, 5), (2, 5), (3, 5)]
GENUINE_FAILURE = {(1, 4), (1, 5), (2, 5)}
NO_DECREASE = {(0, 5), (3, 5)}


def _zf(deg: int, c: int) -> fmpq:
    return fmpq(3, 3 * deg + 4 * c)


def _Ff(deg: int, c: int) -> fmpq:
    if c == 0:
        return fmpq(1)
    D = deg + c
    return fmpq(3, 2) ** c + fmpq(c, 2 * D) * fmpq(3, 2) ** (c - 1)


def pi_flint(G: nx.Graph, load: dict) -> fmpq:
    """`pi = per(L)/prod(deg)` via the per-vertex factorization + matching-sum DP, in `fmpq`.
    Exactly reproduces `kelmans_mixed_load.pi_loaded` (validated in `_selftest`)."""
    z = {v: _zf(G.degree(v), load[v]) for v in G.nodes()}
    p = fmpq(1)
    for v in G.nodes():
        p *= _Ff(G.degree(v), load[v])
    total = fmpq(1)
    seen: set = set()
    for root in G.nodes():
        if root in seen:
            continue
        comp = nx.node_connected_component(G, root)
        seen |= comp
        parent = {root: None}
        order = [root]
        for v in order:
            for w in G.neighbors(v):
                if w not in parent:
                    parent[w] = v
                    order.append(w)
        a: dict = {}
        b: dict = {}
        for v in reversed(order):
            kids = [w for w in G.neighbors(v) if w != parent[v]]
            av = fmpq(1)
            for c in kids:
                av *= (a[c] + b[c])
            bv = fmpq(0)
            for c in kids:
                prod = fmpq(1)
                for cp in kids:
                    if cp != c:
                        prod *= (a[cp] + b[cp])
                bv += z[c] * a[c] * prod
            a[v] = av
            b[v] = z[v] * bv
        total *= (a[root] + b[root])
    return p * total


def _build(ca, cb, cc, pA, qB, r):
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


def _gain(G, load, u, v) -> fmpq | None:
    H = kelmans_step(G, u, v)
    return None if H is None else pi_flint(H, load) - pi_flint(G, load)


def _selftest(n: int = 20) -> None:
    """pi_flint must equal pi_loaded exactly."""
    import random
    random.seed(7)
    for _ in range(n):
        ca, cb, cc = (random.randint(0, 5) for _ in range(3))
        pA, qB, r = random.randint(0, 5), random.randint(0, 5), random.randint(0, 6)
        G, load = _build(ca, cb, cc, pA, qB, r)
        pl = pi_loaded(G, load)
        assert pi_flint(G, load) == fmpq(pl.numerator, pl.denominator), (ca, cb, cc, pA, qB, r)


def run(*, pA_max=22, r_max=60, qB_max=4) -> dict:
    """Large-scale in-scope verification: (0,5),(3,5) never decrease; (1,4),(1,5),(2,5) do,
    and every such decrease is rescued by the anti-hubward step.  Asserts the split."""
    _selftest()
    out = {}
    fails = rescued = 0
    for (ca, cb) in RESIDUAL:
        tested = neg = 0
        for pA in range(1, pA_max):
            for qB in range(0, qB_max):
                for r in range(0, r_max):
                    for cc in (0, 5):
                        if _zf(1 + r, cc) > fmpq(3, 23):
                            continue
                        G, load = _build(ca, cb, cc, pA, qB, r)
                        if not (G.degree(0) >= G.degree(1) >= 2):
                            continue
                        tested += 1
                        g = _gain(G, load, 0, 1)
                        if g < 0:
                            neg += 1
                            if (ca, cb) in GENUINE_FAILURE:
                                fails += 1
                                if _gain(G, load, 1, 0) > 0:      # anti-hubward
                                    rescued += 1
        out[(ca, cb)] = {"tested": tested, "decreases": neg}
        if (ca, cb) in NO_DECREASE:
            assert neg == 0, f"{(ca, cb)} decreased at large scale: NOT certifiable after all"
        else:
            assert neg > 0, f"{(ca, cb)} expected to fail"
    assert fails == rescued, f"anti-hubward failed to rescue {fails - rescued} configs"
    out["antihub_rescue"] = {"direct_failures": fails, "rescued": rescued}
    out["verdict"] = {
        "certifiable_no_decrease": sorted(NO_DECREASE),
        "genuine_failures_all_rescued": sorted(GENUINE_FAILURE),
        "conjecture1_proved": False,
    }
    return out


if __name__ == "__main__":
    for k, v in run().items():
        print(f"  {k}: {v}")
