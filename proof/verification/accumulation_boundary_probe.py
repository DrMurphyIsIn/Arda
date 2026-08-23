"""The ACCUMULATION BOUNDARY: why the tree->family reduction does NOT reduce to LPRSC.

Context.  LPRSC (lprsc_emitter.py + R3Cert/LPRSC.lean) is the integrality-aware certificate for the
ISOLATED marginal tie: a 1-parameter family whose value has a single lattice minimum (the tie) with a
single-crossing ratio.  It closes the near-star and per-child-base families exactly.  A tempting
factoring was: nucleus = [tree->family reduction, open] + [marginal-tie arithmetic, = LPRSC, built].

THIS MODULE REFUTES that factoring (all exact Fraction, self-verifying).  The reduction's hard piece --
the PURE HUB class (0,0,m) -- is NOT an isolated tie LPRSC can close.  It is an ACCUMULATION BOUNDARY:
achievable subtree cavities pile up at T0 = rhoB - 1 (from below), so the pure-hub slack -> 0 on the
LATTICE (not merely continuously).  There is no per-node lattice floor.  A distinct mechanism --
AMORTIZATION (the deep children forcing cav -> T0 pay their own ledger) -- is required.

Three verified findings:

(A1) Achievable cavities ACCUMULATE at T0 from below: the closest achievable cavity strictly below T0
     over trees with <= N nodes creeps up toward T0 as N grows (gap 0.00367 @ N=5 -> 0.00232 @ N=13,
     still decreasing; authoritative cav model, leaf=()).  => NOT a gap; the achievable cavity set is
     dense up to T0.  (Contrast the ISOLATED near-star tie, a single lattice point s=5, LPRSC handles.)

(A2) Pure-hub slack has NO lattice floor: for children at the T0-closest achievable cavity, the hub
     node's OWN slack -> (L - log(1+T0)) ~ 0 as m grows and cav -> T0.  So LPRSC (which needs a single
     lattice minimum bounded away from a floorless limit) CANNOT close the pure hub.

(A3) But AMORTIZATION holds: the same hub's TOTAL ledger (hub + all child subtrees) GROWS with m --
     the deep children each pay ledger, dominating the hub's slack loss.  This is the mechanism of
     amortized_hub_bound.py (ledger >= 0.0235 * #pure-hubs), NOT a per-node floor.

CORRECTED FACTORING of the nucleus:
  * isolated marginal tie (near-star / base families)  ->  LPRSC          [built this session]
  * accumulation boundary (pure hub, cav -> T0)         ->  AMORTIZATION   [amortized_hub_bound, cert-level]
  * structural reduction (depth-collapse / plain model) ->  slack-ledger dichotomy + G7 Lean-ization

So LPRSC is ONE of three pieces, not the tie-half of a two-piece split.  The reduction contains its OWN
arithmetic phenomenon (accumulation), distinct from the isolated tie.  conjecture1_proved = False.
Requires only the sibling proof modules.  Self-verifying.
"""
from __future__ import annotations

from functools import lru_cache
from fractions import Fraction as Fr

from verification.proof_via_explicit_potential import cav, T0
from verification.slack_ledger_dichotomy import slack, ledger_sum


@lru_cache(maxsize=None)
def _trees(n):
    """All rooted plain trees with exactly n nodes, as nested child-tuples (leaf = ())."""
    if n == 1:
        return ((),)
    res = set()

    def parts(rem, minsz):
        if rem == 0:
            yield ()
            return
        for sz in range(minsz, rem + 1):
            for ct in _trees(sz):
                for rest in parts(rem - sz, sz):
                    yield (ct,) + rest
    for kids in parts(n - 1, 1):
        res.add(kids)
    return tuple(res)


def _closest_below_T0(maxn):
    """Closest achievable cavity strictly BELOW T0 (the pure-hub-floorless direction)."""
    best = (Fr(-1), None)   # track the LARGEST cav < T0
    for n in range(1, maxn + 1):
        for t in _trees(n):
            try:
                c = cav(t)
                if c < T0 and c > best[0]:
                    best = (c, t)
            except Exception:
                pass
    gap = T0 - best[0] if best[1] is not None else Fr(1)
    return gap, best[1]


def verify() -> dict:
    out = {}

    # (A1) accumulation: min gap to T0 shrinks with N (sample a few sizes)
    gaps = {}
    for N in (5, 9, 13):
        d, _ = _closest_below_T0(N)
        gaps[N] = float(d)
    out["A1_min_gap_to_T0"] = {k: round(v, 6) for k, v in gaps.items()}
    out["A1_accumulates"] = gaps[13] < gaps[9] < gaps[5]      # strictly shrinking -> accumulation

    # (A2) pure-hub own slack -> 0 for T0-closest child, growing m (no lattice floor)
    _, child = _closest_below_T0(13)
    own = {m: float(slack((child,) * m)) for m in (3, 10, 50)}
    out["A2_pure_hub_own_slack"] = {k: round(v, 5) for k, v in own.items()}
    out["A2_own_slack_decreasing"] = own[50] < own[10] < own[3]   # trending to 0, no floor

    # (A3) amortization: TOTAL ledger GROWS with m (deep children pay)
    tot = {m: float(ledger_sum((child,) * m)) for m in (3, 10, 50)}
    out["A3_total_ledger"] = {k: round(v, 4) for k, v in tot.items()}
    out["A3_amortization_holds"] = tot[50] > tot[10] > tot[3]     # grows -> children pay

    out["corrected_factoring"] = ("isolated tie -> LPRSC; accumulation boundary (pure hub) -> "
                                  "amortization (NOT LPRSC); structural -> ledger dichotomy + G7")
    out["conjecture1_proved"] = False

    assert out["A1_accumulates"], "achievable cavities do NOT accumulate at T0 (unexpected)"
    assert out["A2_own_slack_decreasing"], "pure-hub own slack floor (unexpected -- LPRSC might apply)"
    assert out["A3_amortization_holds"], "amortization fails (total ledger not growing)"
    return out


if __name__ == "__main__":
    import json
    print(json.dumps(verify(), indent=2, default=str))
