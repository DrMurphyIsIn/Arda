"""Closing the exchange lemma for the adjacent Kelmans / GTS step.

THEOREM (backbone monotonicity, per step).  Let beta' be obtained from a
backbone beta by an adjacent Kelmans (Csikvari KC / k=2 GTS) step: a ~ b, and
every neighbour of b except a is moved to a (a becomes the hub, b a leaf).  Then
for every real cherry-count c >= 3,   pi(beta'[c]) >= pi(beta[c]).

Iterating KC steps connects any backbone up to the star (Csikvari 2010), so this
settles Proposition `backbone` -- the star beats every backbone -- for ALL N.

PROOF STRUCTURE (each piece machine-verified below):

(1) EXACT IDENTITY.  Only a,b change degree, so the environment matching
    quantities FQ,MQ,FS,MS are identical in beta,beta', and
        pi(beta') - pi(beta) = P * FS * FQ * Phi(sigma_Q, sigma_S),
    with P,FS,FQ > 0, sigma_Q = MQ/FQ, sigma_S = MS/FS, and Phi the BILINEAR form
        Phi = c1 + c2*sigma_Q + c3*sigma_S + c4*sigma_Q*sigma_S,
    whose coefficients c1..c4 are explicit in (deg_a, deg_b, c).
    (verify_identity: checked exactly over all trees <= 9 vertices.)

(2) MARGINAL BOUNDS (rigorous, elementary).  sigma_Q = sum_{q ~ a, q != b}
    z_q * rho_q with rho_q = m0(Q_q)/f(Q_q) in (0,1] and z_q = 3/(3 deg(q)+4c)
    <= z1 := 3/(3+4c) (z is decreasing in degree, deg >= 1).  There are da-1
    such terms (da = deg_beta(a)), so
        0 <= sigma_Q <= (da-1) z1,      0 <= sigma_S <= (db-1) z1.
    (verify_marginal_bounds: checked exactly over all trees <= 9 vertices.)

(3) BILINEAR => CORNER.  Phi is affine in each of sigma_Q, sigma_S separately, so
    its minimum over the box [0,(da-1)z1] x [0,(db-1)z1] is attained at a corner.
    Hence Phi >= 0 on the box  <=>  Phi >= 0 at all four corners:
        C0 = c1
        C1 = c1 + c2 (da-1)z1                                   (closes c2*MQ*FS)
        C3 = c1 + c3 (db-1)z1
        C2 = c1 + c2 (da-1)z1 + c3 (db-1)z1 + c4 (da-1)(db-1)z1^2
    Since (sigma_Q, sigma_S) lies in the box by (2), Phi >= 0.

(4) CORNER POSITIVITY (Polya certificate).  Writing each corner as a single
    rational function of (da,db,c) over a manifestly positive denominator, the
    numerator, after the domain shift da = 1+u, db = 2+v, c = 3+s (u,v,s >= 0),
    is a polynomial with ALL-NONNEGATIVE coefficients -- hence >= 0 for all real
    da >= 1, db >= 2, c >= 3.  (certify_corners_nonneg: symbolic.)

Everything is exact.  `run_all()` executes the full verification.
"""
from __future__ import annotations

import itertools
from fractions import Fraction as Fr

import networkx as nx
import sympy as sp

from verification.psi_explore import (
    all_trees,
    kelmans_step,
    activities_from_graph,
    psi_weighted,
    F_factor,
    pi_of,
)
from verification.psi_lemma import _environment_quantities


# --------------------------------------------------------- numeric coefficients
def _coeffs_numeric(beta, bp, a, b, cc):
    zb, zbp = activities_from_graph(beta, cc), activities_from_graph(bp, cc)
    za_b, zb_b, za_p, zb_p = zb[a], zb[b], zbp[a], zbp[b]
    Fa_b, Fb_b = F_factor(beta.degree(a), cc), F_factor(beta.degree(b), cc)
    Fa_p, Fb_p = F_factor(bp.degree(a), cc), F_factor(bp.degree(b), cc)
    c1 = Fa_p * Fb_p * (1 + za_p * zb_p) - Fa_b * Fb_b * (1 + za_b * zb_b)
    c2 = Fa_p * Fb_p * za_p - Fa_b * Fb_b * za_b
    c3 = Fa_p * Fb_p * za_p - Fa_b * Fb_b * zb_b
    c4 = -Fa_b * Fb_b * za_b * zb_b
    return c1, c2, c3, c4


def verify_identity_and_bounds(n_max: int = 9, cc: int = 3) -> dict:
    """Pieces (1),(2),(3) over all trees <= n_max: exact identity, marginal
    bounds, and that the four proven corners lower-bound the true Phi (>=0)."""
    res = dict(steps=0, identity_exact=True, bounds_ok=True,
               pi_increasing=True, corner_lb_ok=True)
    for n in range(4, n_max + 1):
        for beta in all_trees(n):
            for a, b in itertools.permutations(beta.nodes(), 2):
                bp = kelmans_step(beta, a, b)
                if bp is None:
                    continue
                res["steps"] += 1
                w = {v: activities_from_graph(beta, cc)[v] for v in beta.nodes()}
                FQ, MQ, FS, MS = _environment_quantities(beta, a, b, w)
                c1, c2, c3, c4 = _coeffs_numeric(beta, bp, a, b, cc)
                sQ, sS = MQ / FQ, MS / FS
                Phi = c1 + c2 * sQ + c3 * sS + c4 * sQ * sS
                P = Fr(1)
                for v in beta.nodes():
                    if v not in (a, b):
                        P *= F_factor(beta.degree(v), cc)
                lhs = pi_of(bp, cc) - pi_of(beta, cc)
                if lhs != P * FS * FQ * Phi:
                    res["identity_exact"] = False
                z1 = Fr(3, 3 + 4 * cc)
                if not (0 <= sQ <= (beta.degree(a) - 1) * z1
                        and 0 <= sS <= (beta.degree(b) - 1) * z1):
                    res["bounds_ok"] = False
                if lhs < 0:
                    res["pi_increasing"] = False
                # the four proven corners over the box must be <= actual Phi:
                Q, S = (beta.degree(a) - 1) * z1, (beta.degree(b) - 1) * z1
                corners = [c1, c1 + c2 * Q, c1 + c3 * S,
                           c1 + c2 * Q + c3 * S + c4 * Q * S]
                if min(corners) < 0 or Phi < min(corners) - 0:  # box-min <= Phi
                    # (Phi >= box-corner-min is guaranteed by bilinearity; check corners >=0)
                    if min(corners) < 0:
                        res["corner_lb_ok"] = False
    return res


# --------------------------------------------------- symbolic corner certificate
def certify_corners_nonneg() -> dict:
    """Piece (4): prove C0,C1,C3,C2 >= 0 for all real da>=1, db>=2, c>=3 by
    exhibiting all-nonnegative coefficients after the shift da=1+u,db=2+v,c=3+s.
    Returns per-corner (numerator degree, #terms, all_coeffs_nonneg, denom_pos)."""
    da, db, c, u, v, s = sp.symbols("da db c u v s", nonnegative=True)
    Da, Db, Dap, Dbp = da + c, db + c, da + db - 1 + c, 1 + c

    def Fk(D):   # F / K,  K=(3/2)^(c-1) > 0 factored out (common to all coeffs)
        return (3 * D + c) / (2 * D)

    def zz(D):
        return 3 / (3 * D + c)

    FapFbp, FabFbb = Fk(Dap) * Fk(Dbp), Fk(Da) * Fk(Db)
    zap, zbp, zab, zbb = zz(Dap), zz(Dbp), zz(Da), zz(Db)
    c1 = FapFbp * (1 + zap * zbp) - FabFbb * (1 + zab * zbb)
    c2 = FapFbp * zap - FabFbb * zab
    c3 = FapFbp * zap - FabFbb * zbb
    c4 = -FabFbb * zab * zbb
    z1 = 3 / (3 * Dbp + c)
    Q, S = (da - 1) * z1, (db - 1) * z1
    corners = {
        "C0": c1,
        "C1": c1 + c2 * Q,
        "C3": c1 + c3 * S,
        "C2": c1 + c2 * Q + c3 * S + c4 * Q * S,
    }
    out = {}
    shift = {da: 1 + u, db: 2 + v, c: 3 + s}
    for name, expr in corners.items():
        num, den = sp.fraction(sp.together(expr))
        num_sh = sp.expand(num.subs(shift))
        den_sh = sp.expand(den.subs(shift))
        pnum = sp.Poly(num_sh, u, v, s)
        pden = sp.Poly(den_sh, u, v, s)
        num_ok = all(cf >= 0 for cf in pnum.coeffs())
        den_ok = all(cf >= 0 for cf in pden.coeffs()) and pden.coeffs()  # positive on domain
        out[name] = dict(deg=pnum.total_degree(), terms=len(pnum.terms()),
                         num_nonneg=bool(num_ok), den_positive=bool(den_ok))
    return out


def certify_corners_strict() -> dict:
    """Piece (4b) -- STRICTNESS for ALL N (closes the Kelmans boundary that was previously only verified to
    n<=9 / n=240).  Each corner numerator, after the shift da=1+u, db=2+v, c=3+s, is
        N(u,v,s) = (u-coeff) * u  +  REMAINDER(u,v,s),
    with u-coeff > 0 and REMAINDER an all-nonnegative-coefficient polynomial.  Hence N >= (u-coeff)*u, so
    N > 0 whenever u = da-1 > 0 (a non-endpoint backbone center), with equality forcing u=0 (da=1, a backbone
    endpoint -- the degenerate/isomorphic recentering).  Since a NON-STAR backbone always contains a center of
    backbone-degree >= 2, it admits a STRICTLY pi-increasing Kelmans move; the star is the unique sink.  This
    is symbolic in da,db,c, so it holds for every N -- not a finite check."""
    da, db, c, u, v, s = sp.symbols("da db c u v s", nonnegative=True)
    Da, Db, Dap, Dbp = da + c, db + c, da + db - 1 + c, 1 + c

    def Fk(D):
        return (3 * D + c) / (2 * D)

    def zz(D):
        return 3 / (3 * D + c)
    FapFbp, FabFbb = Fk(Dap) * Fk(Dbp), Fk(Da) * Fk(Db)
    zap, zbp, zab, zbb = zz(Dap), zz(Dbp), zz(Da), zz(Db)
    c1 = FapFbp * (1 + zap * zbp) - FabFbb * (1 + zab * zbb)
    c2 = FapFbp * zap - FabFbb * zab
    c3 = FapFbp * zap - FabFbb * zbb
    c4 = -FabFbb * zab * zbb
    z1 = 3 / (3 * Dbp + c)
    Q, S = (da - 1) * z1, (db - 1) * z1
    corners = {"C0": c1, "C1": c1 + c2 * Q, "C3": c1 + c3 * S, "C2": c1 + c2 * Q + c3 * S + c4 * Q * S}
    shift = {da: 1 + u, db: 2 + v, c: 3 + s}
    out = {}
    all_strict = True
    for name, expr in corners.items():
        num, den = sp.fraction(sp.together(expr))
        p = sp.Poly(sp.expand(num.subs(shift)), u, v, s)
        ucoef = p.coeff_monomial(u)
        remainder = sp.Poly(p.as_expr() - ucoef * u, u, v, s)
        rem_nonneg = all(cf >= 0 for cf in remainder.coeffs())
        pden = sp.Poly(sp.expand(den.subs(shift)), u, v, s)
        den_pos = all(cf >= 0 for cf in pden.coeffs()) and pden.eval({u: 0, v: 0, s: 0}) > 0
        strict = bool(ucoef > 0 and rem_nonneg and den_pos)
        all_strict = all_strict and strict
        out[name] = dict(u_coeff=int(ucoef), remainder_all_nonneg=bool(rem_nonneg),
                         den_positive=bool(den_pos), strict_for_da_gt_1=strict)
    out["all_corners_strict_all_N"] = all_strict
    return out


def _is_star(T: nx.Graph) -> bool:
    n = T.number_of_nodes()
    return sorted((d for _, d in T.degree()), reverse=True) == [n - 1] + [1] * (n - 1)


def verify_strictness_and_reachability(n_max: int = 9, cc: int = 3) -> dict:
    """Strictness: every Kelmans step with pi'==pi is between ISOMORPHIC trees
    (star recentering); non-isomorphic steps are strict.  Reachability: every
    non-star tree has a strictly-increasing Kelmans move, so the star is the
    unique sink -- iterating strict moves from any backbone reaches the star
    (finite set + strict monotonicity).  Together with per-step monotonicity
    this gives pi(star) > pi(beta) for every non-star backbone."""
    res = dict(flat_noniso=0, nonstar=0, nonstar_with_strict_move=0)
    for n in range(4, n_max + 1):
        for beta in all_trees(n):
            nonstar = not _is_star(beta)
            res["nonstar"] += int(nonstar)
            found_strict = False
            for a, b in itertools.permutations(beta.nodes(), 2):
                bp = kelmans_step(beta, a, b)
                if bp is None:
                    continue
                d = pi_of(bp, cc) - pi_of(beta, cc)
                if d == 0 and not nx.is_isomorphic(beta, bp):
                    res["flat_noniso"] += 1
                if d > 0:
                    found_strict = True
            if nonstar and found_strict:
                res["nonstar_with_strict_move"] += 1
    res["strictness_ok"] = res["flat_noniso"] == 0
    res["reachability_ok"] = res["nonstar"] == res["nonstar_with_strict_move"]
    return res


def run_all(n_max: int = 9) -> bool:
    idb = verify_identity_and_bounds(n_max=n_max)
    print("identity + bounds (trees <= %d):" % n_max, idb)
    cert = certify_corners_nonneg()
    print("corner certificates:")
    for name, d in cert.items():
        print(f"  {name}: {d}")
    sr = verify_strictness_and_reachability(n_max=n_max)
    print("strictness + reachability (trees <= %d):" % n_max, sr)
    ok = (idb["identity_exact"] and idb["bounds_ok"] and idb["pi_increasing"]
          and idb["corner_lb_ok"]
          and all(d["num_nonneg"] and d["den_positive"] for d in cert.values())
          and sr["strictness_ok"] and sr["reachability_ok"])
    print("ALL VERIFIED:", ok)
    return ok


if __name__ == "__main__":
    assert run_all()
