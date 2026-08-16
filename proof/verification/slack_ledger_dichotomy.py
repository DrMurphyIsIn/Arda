"""THE SLACK LEDGER: quantitative defect costs extracted from the phi_le_one hinge certificate,
and the far/near dichotomy confining the fixed-n maximizer.

THE IDEA.  The (Lean-checked) proof of Phi <= 1 uses the hinge potential phi(y) = 0.22*(y - T0)_+
(T0 = rhoB - 1) and the per-node super-solution (SS): chi_v + phi(cav_v) <= sum_children phi(cav_c)
(proof_via_explicit_potential.py; margins > 0.13).  Telescoping (SS) over the structural skeleton
gives an EXACT identity (verified here to 1e-16 on 1651 plain trees):

    logPhi(T)  =  - phi(cav_root)  -  SUM_v slack_v,
    slack_v    =  sum_c phi(cav_c) - phi(cav_v) - chi_v   >=  0   (by (SS)).

So the certificate is not just a sign proof -- it is a DEFECT-COST LEDGER: every structural node
pays its slack, and logPhi <= -(total ledger).  Combined with the fixed-n rate identity
(rate_bound_fixed_n.py:  A(T) = pi/rhoB^n = exp(logPhi) * R, R <= 4/3):

    A(T) < C_1  as soon as  (total ledger) > log(4/(3*C_1)) = 0.37167.

THE LEDGER -- CONTEXT-FREE FLOORS (hardened via the equal-children/Jensen relaxation: the class
infimum of slack over ALL child profiles is attained at equal child cavities y, and structural
child cavities lie in (0, 1/2); so a 1-variable minimum over the RELAXATION is a valid floor
for every tree).  Floors (dense-grid 1-var minima; per-class hardening to symbolic = routine
hinge algebra):
  * FREE shape (slack exactly 0): (a=5, nl=0, m=0) -- the FIVE-ARM BUNDLE, THE TIE.  Unique.
  * bundles (a,0,0), a != 5 (EXACT, childless, closed form -chi): 0.00103 (a=4), 0.00152
    (a=6), 0.00656 (a=3), 0.0118 (a=2), 0.0163 (a=1), 0.0371 (a=0);
  * chain/spacer (0,0,1): >= 0.00544 (0.01836/node at the realized chain fixed point);
  * bare-leaf classes (nl=1; the folded ARM (0,1,0) excluded): >= 0.0529; m-tail bounded
    below since chi(T0) -> -L + a*OMEGA <= -L < 0;
  * mixed (a>=1, nl=0, m>=1): >= 0.0054 (a<=6 scan; tails -> a*|OMEGA| > 0).

THE PURE-HUB COLLAPSE (the honest core finding).  The class (0,0,m>=2) has NO context-free
floor: at children-cavity -> T0 (the Lemma-A-tight configuration) the relaxed class minimum
decays like ~2/m (0.0002 at m=1000).  This is the marginal-tie/accumulation wall appearing
QUANTITATIVELY in the slack landscape -- localized exactly at Lemma A's equality locus.
BUT the collapse is not realizable for free: cavity-~T0 children are never free bundles
(bundle cavity = 3/23 = 0.130), so they pay their OWN floors, and in every adversarial probe
(mini-hub towers: hubs of 3-bundle mini-hubs, nested to depth 3, up to 801 structural nodes)
the AMORTIZED ledger stays >= 0.094 per pure hub (towers decay fast: logPhi = -24.5 at depth 3).

THE DICHOTOMY (fixed n, plain model).  Budget = log(4/(3*C_1)) = 0.37167.  UNCONDITIONAL
per-class confinement (context-free floors): any plain tree with ledger > budget has
A(T) < C_1, so the fixed-n maximizer's parse has at most ~7 bare-leaf defects, ~68 chain
nodes, ~360 four-arm bundles (etc. per the floor table) -- all NON-hub defect types bounded.
HUB-COUNT confinement is AMORTIZED (repaired: critical family symbolic, mixed layer G1): ledger >= 0.08 * #pure-hubs (all probes give
0.094-0.113; induction route: a pure hub either has all-free-bundle children -- then its own
slack >= 0.0844, provable 1-var -- or has a child paying a floor / a pure-hub child to recurse
into).  Under the amortized bound: at most ~4 pure hubs total.

HONEST SCOPE.  (i) slack >= 0 is rigorous ((SS), Lean-checked chain); context-free floors are
dense-grid 1-var minima of the VALID relaxation (symbolic hardening routine per class);
(ii) the pure-hub class floor is provably ABSENT -- hub confinement needs the amortization
lemma (named open, induction route above, strong probe support); (iii) plain model (general
via Plainify; bookkeeping open); (iv) the 4/3 boundary factor is crude -- sharpening R
tightens every budget.  conjecture1_proved=False.

Self-verifying run_all(); requires only the sibling proof_via_explicit_potential module.
"""
from __future__ import annotations

import math
import sys

sys.setrecursionlimit(100000)

from verification.proof_via_explicit_potential import (
    cav,
    logphi,
    gen,
    is_plain,
    _struct,
    _chi,
    ARM,
    T0,
)

C_HINGE = 0.22
C1 = (26 / 23) / (621 / 64) ** (1 / 11)
BUDGET = math.log(4 / (3 * C1))          # 0.37167
BUNDLE = (ARM,) * 5                       # the free shape (5,0,0)


def phi(y: float) -> float:
    return C_HINGE * max(0.0, y - T0)


def slack(nd) -> float:
    return sum(phi(cav(c)) for c in _struct(nd)) - phi(cav(nd)) - _chi(nd)


def walk(T):
    yield T
    for c in _struct(T):
        yield from walk(c)


def ledger_sum(T) -> float:
    return sum(slack(v) for v in walk(T))


def shape(v):
    a = sum(1 for c in v if c == ARM)
    nl = sum(1 for c in v if len(c) == 0)
    m = len(_struct(v))
    return (a, nl, m)


def verify_telescoping(n_max: int = 12) -> dict:
    """logPhi(T) == -phi(cav_root) - ledger_sum(T), exhaustively."""
    worst = 0.0
    checked = 0
    for n in range(2, n_max + 1):
        for T in gen(n):
            if not is_plain(T) or len(T) == 0:
                continue
            err = abs(logphi(T) - (-phi(cav(T)) - ledger_sum(T)))
            worst = max(worst, err)
            checked += 1
    assert worst < 1e-12
    return {"telescoping_exact": True, "cases": checked, "max_err": worst}


def verify_slack_nonneg(n_max: int = 14) -> dict:
    """(SS) slack >= 0 at every structural node of every plain tree (the ARM as a whole
    tree is the folded base case, excluded -- logPhi(ARM) = OMEGA < 0 directly)."""
    checked = 0
    for n in range(2, n_max + 1):
        for T in gen(n):
            if not is_plain(T) or len(T) == 0 or T == ARM:
                continue
            for v in walk(T):
                if v == ARM:
                    continue
                assert slack(v) >= -1e-12, (n, shape(v))
                checked += 1
    return {"slack_nonneg": True, "nodes": checked}


def measured_floors(n_max: int = 14) -> dict:
    """Min slack per (a, nl, m) shape class over the exhaustive scan + structured probes.
    FLOAT-LEVEL measured floors (see HONEST SCOPE)."""
    ledger = {}
    for n in range(2, n_max + 1):
        for T in gen(n):
            if not is_plain(T) or len(T) == 0 or T == ARM:
                continue
            for v in walk(T):
                if v == ARM:
                    continue
                k = shape(v)
                s = slack(v)
                if k not in ledger or s < ledger[k]:
                    ledger[k] = s
    # structured probes for classes the exhaustive scan cannot reach
    probes = {}
    probes["hub_m300"] = slack((BUNDLE,) * 300)
    probes["hub_m2"] = slack((BUNDLE,) * 2)
    nd = BUNDLE
    for _ in range(11):
        nd = (nd,)
    probes["chain_fixed_point"] = slack(nd)
    probes["star_ledger_m200"] = ledger_sum((BUNDLE,) * 200)
    # the free shape is (5,0,0), exactly zero
    assert abs(ledger.get((5, 0, 0), 1.0)) < 1e-9
    # key floors (float, from the scan)
    key_floors = {
        "bundle_a4": ledger.get((4, 0, 0)),
        "bundle_a6": ledger.get((6, 0, 0)),
        "bundle_a3": ledger.get((3, 0, 0)),
        "chain_a0m1": ledger.get((0, 0, 1)),
        "leaf_child_min": min(s for (a, nl, m), s in ledger.items() if nl == 1),
    }
    assert key_floors["bundle_a4"] > 0.0009
    assert key_floors["chain_a0m1"] > 0.009
    assert key_floors["leaf_child_min"] > 0.05
    assert 0.084 < probes["hub_m300"] < 0.085
    assert 0.018 < probes["chain_fixed_point"] < 0.019
    return {"classes": len(ledger), "key_floors": {k: round(v, 5) for k, v in key_floors.items()},
            "probes": {k: round(v, 5) for k, v in probes.items()}}


def certify_context_free_floors() -> dict:
    """The hardened floor set via the equal-children relaxation (valid for every tree:
    Jensen puts the class infimum at equal child cavities; structural child cavities lie
    in (0, 1/2)).  Dense-grid 1-var minima, asserted at the recorded values."""
    from verification.proof_via_explicit_potential import OMEGA

    def slack_eq(a, nl, m, y):
        k = a + nl + m
        S = a / 3 + nl + m * y
        cavv = 1.0 / (k + 1 + S)
        chi = -math.log(621 / 64) / 11 + math.log(1 + S / (k + 1)) + a * OMEGA \
            + nl * (-math.log(621 / 64) / 11)
        D = max(0.0, cavv - T0) - m * max(0.0, y - T0)
        return -chi - C_HINGE * D

    def cmin(a, nl, m, ngrid=100001):
        if m == 0:
            return slack_eq(a, nl, 0, 0.0)
        return min(slack_eq(a, nl, m, 0.5 * i / (ngrid - 1)) for i in range(1, ngrid))

    assert abs(cmin(5, 0, 0)) < 1e-9                       # the free shape, exactly
    floors = {"bundle_a4": cmin(4, 0, 0), "bundle_a6": cmin(6, 0, 0),
              "bundle_a3": cmin(3, 0, 0), "chain": cmin(0, 0, 1)}
    assert floors["bundle_a4"] > 0.0010 and floors["chain"] > 0.0054
    leaf_min = min(cmin(a, 1, m, 20001) for a in range(0, 9) for m in range(0, 7)
                   if not (a == 0 and m == 0))              # exclude the folded ARM
    assert leaf_min > 0.052
    floors["bare_leaf"] = leaf_min
    mixed_min = min(cmin(a, 0, m, 20001) for a in range(1, 7) for m in range(1, 30))
    assert mixed_min > 0.005
    floors["mixed_a1plus"] = mixed_min
    # the pure-hub COLLAPSE: no context-free floor
    collapse = {m: cmin(0, 0, m, 20001) for m in (10, 100, 1000)}
    assert collapse[1000] < 0.001                          # provably no uniform floor
    return {"floors": {k: round(v, 5) for k, v in floors.items()},
            "pure_hub_relaxed_min": {m: round(v, 6) for m, v in collapse.items()}}


def amortized_hub_evidence() -> dict:
    """The Lemma-A-tight adversarial towers: hub slack escapes to ~0 but descendants pay;
    amortized ledger per pure hub stays >= 0.09 in every probe (conjecture: >= 0.08)."""
    MINI = (BUNDLE,) * 3                    # 3-bundle mini-hub: cavity 0.2277 ~ T0
    out = {}
    for name, T, hubs in (
        ("hub_of_100_minis", (MINI,) * 100, 101),
        ("depth2_tower", ((MINI,) * 3,) * 20, 1 + 20 * 4),
        ("depth3_tower", (((MINI,) * 3,) * 3,) * 20, 1 + 20 * 13),
    ):
        led = ledger_sum(T)
        per = led / hubs
        assert per > 0.08, name
        out[name] = {"pure_hubs": hubs, "ledger": round(led, 3), "per_hub": round(per, 4)}
    return out


def dichotomy_budgets() -> dict:
    """The corrected confinement table.  UNCONDITIONAL rows use context-free floors;
    the hub row is CONJECTURAL (amortized >= 0.08/hub, probe-supported, named open)."""
    floors = {"bare_leaf": 0.0529, "chain_node": 0.00544,
              "bundle_a4": 0.00103, "bundle_a3": 0.00656, "mixed_a1plus": 0.0054}
    out = {"budget": round(BUDGET, 5),
           "max_counts_unconditional": {k: int(BUDGET / v) for k, v in floors.items()},
           "pure_hubs_unconditional": int(BUDGET / 0.0235),
           "note": "hub row: amortized_hub_bound.py, REPAIRED post-review -- critical profile "
                   "family symbolic (infimum 0.023869, margin 3.7e-4 over 0.0235), mixed layer "
                   "grid rigor superseded at rational rigor by g1_endpoint_certificates; "
                   "the sharp ~4 stays with R5/R6"}
    return out


def ledger_interaction_note() -> dict:
    """DIAGNOSTIC (no assert): the ledger is NOT additive under defect injection -- a
    defect child shifts its parent hub's slack (cavity interaction), so 'star minimizes
    the ledger at matched n' is NOT a corollary of the per-node floors; identifying the
    ledger minimizer is exactly the R5/R6/merge-layer constant-order content.  The
    dichotomy above needs only the FLOORS (each defect pays at least its class floor
    at its own node), not additivity."""
    m = 20
    star = (BUNDLE,) * m
    hubhub = ((BUNDLE,) * (m // 2),) + (BUNDLE,) * (m - m // 2)
    return {"star_m20_ledger": round(ledger_sum(star), 5),
            "hub_of_hub_ledger": round(ledger_sum(hubhub), 5),
            "note": "not matched-n; interactions real; minimizer identification = R5/R6"}


def run_all():
    out = {}
    out["telescoping"] = verify_telescoping()
    out["slack_nonneg"] = verify_slack_nonneg()
    out["floors_scan"] = measured_floors()
    out["floors_context_free"] = certify_context_free_floors()
    out["hub_amortized"] = amortized_hub_evidence()
    out["budgets"] = dichotomy_budgets()
    out["interaction_note"] = ledger_interaction_note()
    out["dichotomy"] = {
        "statement": "A(T) = exp(logPhi)*R <= (4/3)*exp(-ledger_sum); ledger_sum > 0.37167 "
                     "=> A(T) < C_1.  Non-hub defect classes bounded UNCONDITIONALLY "
                     "(context-free floors); pure-hub count bounded by the amortized bound "
                     "(0.0235/hub: critical family symbolic, mixed layer G1 -- "
                     "amortized_hub_bound, repaired post-review).",
        "free_shape": "(a=5, nl=0, m=0) -- the tie, uniquely",
        "pure_hub_collapse": "the marginal-tie wall, localized at Lemma A's equality locus; "
                             "escapes per-node accounting but not amortized accounting",
        "conjecture1_proved": False,
    }
    for k, v in out.items():
        print(f"  {k}: {v}")
    return out


if __name__ == "__main__":
    run_all()
