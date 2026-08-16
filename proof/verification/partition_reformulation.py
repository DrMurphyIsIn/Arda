"""A NEW probabilistic reformulation of Phi<=1 (plain trees) -- the geometric-mean of self-probabilities.

Creative reframing (NOT a proof; the conjecture is preserved).  For a plain tree, the cavity identity
`cav_v * (k_v+1+S_v) = 1` is a PARTITION OF UNITY: define the cavity-Markov transition probabilities

    p_v0  := (k_v+1) * cav_v        (the node's "stay / to-parent" probability),
    p_vc  := cav_v * cav_c          (descend to child c),      p_v0 + sum_c p_vc = 1   (exact, verified).

Then, from logPhi = sum_v [-L - log(k_v+1) - log(cav_v)] and p_v0 = (k_v+1) cav_v = e^{-L}/(e^{-L} ... ),
    Phi(T) = rhoB^{-N} / prod_v p_v0,        so     Phi<=1  <=>  (prod_v p_v0)^(1/N) >= 1/rhoB.

*** THE CONJECTURE IS EXACTLY: the GEOMETRIC MEAN of the node self-probabilities p_v0 is >= 1/rhoB,
    i.e. the tie N(0,5) is the MINIMIZER of the geometric-mean self-probability over all plain trees
    (min = 1/rhoB, attained at the tie). ***

Why this is a genuinely new entry point.  The four routes ruled out this session all live in the
"amplitude" world (smooth certificate, p-adic valuation, per-cavity potential, discrete envelope).  This
reformulation is in the PROBABILITY world: p_v0 are transition probabilities of an explicit Markov chain
on the tree (from a node, stay w.p. p_v0 or descend to a child), and the target is a geometric-mean
lower bound = an entropy-rate / spectral-radius-type statement.  Tools that do NOT apply to amplitudes --
entropy inequalities, many-to-one / spine change-of-measure, spectral radius of the transfer operator --
are natural here.

HONEST SCOPE.  This does NOT close the conjecture.  Like every equivalent form, it is TIGHT at the tie
(geom-mean = 1/rhoB with zero slack), so no local/pairing/flow certificate can work (any pairing's product
is exactly (1/rhoB)^N at the tie, so some pair must fall below); and the global statement "the tie
minimizes the geometric mean" is the conjecture itself.  It is offered as a verified stepping stone that
recasts the crux in probabilistic/spectral language.  conjecture1_proved = False.

Self-verifying (plain model, exact-rational cavities).  Standard library only.
"""
from __future__ import annotations

import functools
import math
from fractions import Fraction as Fr

L = math.log(621 / 64) / 11
RHOB = (621 / 64) ** (1 / 11)


def pcav(C) -> Fr:
    S = sum(pcav(ch) for ch in C)
    return Fr(1, len(C) + 1 + S)


@functools.lru_cache(maxsize=None)
def gen(n: int):
    if n == 1:
        return (tuple(),)
    res = []

    def parts(rem, mn):
        if rem == 0:
            yield ()
            return
        for s in range(mn, rem + 1):
            for sub in gen(s):
                for rest in parts(rem - s, s):
                    yield (sub,) + rest
    for kids in parts(n - 1, 1):
        res.append(kids)
    return tuple(res)


def partition_ok(C) -> bool:
    """p_v0 + sum_c p_vc = 1 at every node (exact rational)."""
    ok = True

    def rec(nd):
        nonlocal ok
        cv = pcav(nd)
        p0 = (len(nd) + 1) * cv
        psum = sum(cv * pcav(c) for c in nd)
        if p0 + psum != 1:
            ok = False
        for c in nd:
            rec(c)
    rec(C)
    return ok


def geomean_p0(C) -> float:
    logp, N = 0.0, 0

    def rec(nd):
        nonlocal logp, N
        N += 1
        logp += math.log(float((len(nd) + 1) * pcav(nd)))
        for c in nd:
            rec(c)
    rec(C)
    return math.exp(logp / N)


def logphi_from_p0(C) -> float:
    """logPhi = -N L - sum log p_v0 (the reformulation)."""
    logp, N = 0.0, 0

    def rec(nd):
        nonlocal logp, N
        N += 1
        logp += math.log(float((len(nd) + 1) * pcav(nd)))
        for c in nd:
            rec(c)
    rec(C)
    return -N * L - logp


def verify(nmax: int = 12) -> dict:
    part = all(partition_ok(T) for n in range(1, 10) for T in gen(n))
    # cross-check logPhi form against the direct plain formula
    def plog(C):
        t = 0.0
        def rec(nd):
            nonlocal t
            k = len(nd); S = sum(pcav(c) for c in nd)
            t += -L + math.log(1 + float(S) / (k + 1))
            for c in nd: rec(c)
        rec(C); return t
    err = max(abs(logphi_from_p0(T) - plog(T)) for n in range(1, nmax + 1) for T in gen(n))
    min_gm = min(geomean_p0(T) for n in range(1, nmax + 1) for T in gen(n))
    tie = tuple(((),) for _ in range(5))
    return {
        "partition_of_unity_exact": part,
        "logphi_equals_minus_NL_minus_sum_log_p0_err": err,
        "min_geomean_p0": round(min_gm, 8),
        "one_over_rhoB": round(1 / RHOB, 8),
        "min_attained_at_tie": abs(geomean_p0(tie) - 1 / RHOB) < 1e-12,
        "conjecture1_proved": False,
        "statement": ("Phi<=1 <=> geom-mean of node self-probabilities p_v0=(k+1)cav_v is >= 1/rhoB "
                      "(min = 1/rhoB, attained ONLY at the tie N(0,5)). A NEW probabilistic reformulation "
                      "(partition of unity => cavity Markov chain), recasting the crux as an entropy-rate / "
                      "spectral-radius statement -- a fresh toolbox vs the amplitude-world routes. NOT a "
                      "proof: tight at the tie (no local slack), and 'tie minimizes geom-mean' is the crux."),
    }


if __name__ == "__main__":
    import json
    print(json.dumps(verify(), indent=2, default=str))
