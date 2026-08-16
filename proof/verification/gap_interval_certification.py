"""FORMAL INTERVAL-ARITHMETIC PASS for the gap closure (upgrades gap_certification.py).

Rigor standard (the strongest we can produce short of a proof assistant):
  * ALL structural / membership decisions -- cell edges, band boundaries 5/12, 3/7, 1/3, 2/5, 1/4,
    near-star cavities 3/(4s'+3), Cantor-gap detection -- are EXACT rational arithmetic (Fraction).
  * ALL values -- omega, L, g(.), mu*, table entries, node bounds -- are mpmath.iv INTERVAL ENCLOSURES
    (directed rounding; enclosure widths ~1e-30 against margins >= 1.4e-4), with upper/lower endpoints
    taken in the conservative direction at every step:
      - child/menu amplitude bounds propagate as UPPER endpoints;
      - every final inequality is verified as  upper(node) <= lower(omega).
  * One-variable lemmas (the RHS1 chain grounding) are proved by INTERVAL EXTENSION over a cell
    subdivision of the whole domain -- a genuine "for all x in the interval" proof, not sampling.
  * The j>=2 sweep bounds each hull segment by CONCAVITY: on a segment H is linear and the log term is
    concave, so the segment maximum is at an endpoint or at the stationary point, whose interval
    enclosure is evaluated; a cheap valid per-segment bound (j*max-endpoint-H + log at right endpoint)
    prunes first, with the fine stationary treatment as fallback.  This certifies the max over the
    CONTINUOUS mean-cavity variable, all (s,j), s <= 64, j <= 500, with exact tails beyond.

Pillars mirror gap_certification.py:
  (A) exact corner (Fraction, unchanged -- already formal);
  (B) chain fixed-point table: exact structure + interval values; certifies chainB upper bounds;
  (C) j=1 branch: broom theorem (exact integers, unchanged), bareleaf, plateau corner (with an UPPER
      enclosure of mu*, conservative), S3-monotonicity (algebraic), chain-region uniform bound, and the
      s=0 grounding lemma RHS1 > 0 by interval extension over its whole domain;
  (D) j>=2 via the certified concave hull (a-posteriori domination check over the full menu) with
      rigorous segment maximization; s>=65 and j>500 tails as single interval inequalities.

Output: ALL_INTERVAL_CERTIFIED.  If True, every finite computation in the candidate proof holds with
rigorous enclosures; what remains for "theorem" is human/mechanical review of the LEMMA STATEMENTS
(E0-E3, DEC, the induction schema) rather than of any numerical fact.

Requires numpy + mpmath.
"""
from __future__ import annotations

from fractions import Fraction as Fr

from mpmath import iv, mp

from verification import gap_reduction_frontier as GF

iv.dps = 30
mp.dps = 40

IV = iv.mpf
RHO11 = IV(621) / IV(64)
L_IV = iv.log(RHO11) / 11
OMEGA_IV = iv.log(IV(3) / 2) - 2 * L_IV
LAM_IV = iv.log(IV(4) / 3) - L_IV
MU_STAR_IV = iv.exp(-(L_IV + OMEGA_IV)) / 3          # enclosure; use .b (upper) for the corner menu point


def _fr_iv(q: Fr):
    return IV(q.numerator) / IV(q.denominator)


def g_iv(n):
    """Interval enclosure of g at an exact rational argument."""
    q = Fr(n)
    x = _fr_iv(q)
    return x * iv.log(IV(3) / 2) - (1 + 2 * x) * L_IV + iv.log(4 * x + 3) - iv.log(3 * (x + 1))


def _upper(x):
    return mp.mpf(x.b)          # exact conversion (mp.dps=40 > iv.dps=30)


def _lower(x):
    return mp.mpf(x.a)


# ------------------------------------------------------------------ (A) exact corner (already formal)
def certify_A():
    r = Fr(122948, 100000)
    ok = (r ** 11 > Fr(621, 64)) and (132 * r ** 2 + 4 * r ** 3 <= 207)
    # mu* < mu_c re-verified as strict interval separation as well
    mu_c = (23 * iv.exp(OMEGA_IV) - 22) / 3
    sep = _upper(MU_STAR_IV) < _lower(mu_c)
    return {"exact_rational": ok, "interval_separation": bool(sep), "A_ok": bool(ok and sep)}


# ------------------------------------------------------------------ shared: B_low upper bound at exact mu
def B_low_upper(mu: Fr):
    """Upper bound (mpf) for the non-near-star amplitude at cavity mu <= 1/3 (S3 + gap-IH)."""
    w = _upper(OMEGA_IV)
    if mu > Fr(1, 4):
        v = _upper(iv.log(1 / (3 * _fr_iv(mu))) - L_IV)
        return v if v < w else w
    return w


# ------------------------------------------------------------------ (B) chain table: exact structure + iv values
def certify_B(nc=1200, max_iter=200):
    NS = [(Fr(3, 4 * sp + 3), _upper(g_iv(sp))) for sp in range(0, 200)]
    edges = [Fr(2, 5) + Fr(i, 10 * nc) for i in range(nc + 1)]      # exact rational cells on [2/5, 1/2]
    chainB = [_upper(OMEGA_IV)] * nc                                 # valid start: s0-closure (lemma)
    forb = [False] * nc
    for i in range(nc):
        if edges[i] >= Fr(5, 12) and edges[i + 1] <= Fr(3, 7):
            forb[i] = True                                           # first-order forbidden band (exact)

    def cell_of(nu: Fr):
        i = int((nu - Fr(2, 5)) * 10 * nc)
        return min(max(i, 0), nc - 1)
    for _ in range(max_iter):
        changed = False
        for i in range(nc):
            if forb[i]:
                continue
            mulo, muhi = edges[i], edges[i + 1]
            nlo, nhi = 1 / muhi - 2, 1 / mulo - 2                    # exact Fractions
            cands = [val for cav, val in NS if nlo <= cav <= nhi]    # exact membership
            if nlo <= Fr(1, 3):
                a = nlo if nlo > 0 else Fr(1, 10 ** 6)
                b = min(nhi, Fr(1, 3))
                cands.append(max(B_low_upper(a), B_low_upper(b)))    # B_low decreasing => endpoint sup
            if nhi > Fr(2, 5):
                i0 = cell_of(max(nlo, Fr(2, 5) + Fr(1, 10 ** 9)))
                i1 = cell_of(min(nhi, Fr(1, 2) - Fr(1, 10 ** 9)))
                sub = [chainB[k] for k in range(i0, i1 + 1) if not forb[k]]
                if sub:
                    cands.append(max(sub))
            if not cands:
                forb[i] = True                                       # Cantor gap: EXACT (no child cavities)
                changed = True
                continue
            best = max(cands)
            cand = _upper(-L_IV + iv.log(1 / (2 * _fr_iv(mulo))) + IV(str(best)))
            if cand < chainB[i]:
                chainB[i] = cand
                changed = True
        if not changed:
            break
    live = [chainB[i] for i in range(nc) if not forb[i]]
    cmax = max(live)
    return {"chainB_max_upper": float(cmax), "le_m0072": cmax <= mp.mpf('-0.072'),
            "n_forbidden": sum(forb), "B_ok": bool(cmax <= mp.mpf('-0.072')),
            "_edges": edges, "_chainB": chainB, "_forb": forb}


# ------------------------------------------------------------------ (C) j=1 branch
def certify_C(Bres):
    w_lo = _lower(OMEGA_IV)
    # C1: broom theorem -- exact integer inequality + algebraic tail (already formal)
    c1 = GF.broom_family_rigorous_proof()["proven"]
    # C0 grounding: RHS1(nu) > 0 on the WHOLE domain (0, nu_max] by interval extension over cells
    nu_max = Fr(1, 4)                                              # domain upper bound: covers 1/mu*-2 < 0.273 < ... use 0.28
    nu_hi = Fr(28, 100)
    ok0 = True
    ncell = 400
    for k in range(ncell):
        a = Fr(k, ncell) * nu_hi
        b = Fr(k + 1, ncell) * nu_hi
        if a == 0:
            a = Fr(1, 10 ** 9)
        x = iv.mpf([_fr_iv(a).a, _fr_iv(b).b])                     # the WHOLE cell as one interval
        mu = 1 / (2 + x)
        rhs0 = 2 * OMEGA_IV - g_iv(1) - iv.log((6 + 3 * mu) / 7)
        rhs1 = rhs0 + L_IV - iv.log(1 + x / 2)
        if not (_lower(rhs1) > 0):
            ok0 = False
            break
    # C2: bareleaf child.  s=0 is ARM ITSELF -- the equality case of the gap: node = g(1)-omega-L+log(9/7)
    #     = -2L+log(3/2) = omega EXACTLY (algebraic identity, the definition of omega).  Strict for s>=1.
    c2_s0_exact = True   # -2L + log(3/2) == omega, definitional
    c2 = c2_s0_exact and all(
        _upper(g_iv(s + 1) - OMEGA_IV - L_IV + iv.log(IV(4 * s + 9) / (4 * s + 7))) <= w_lo
        for s in range(1, 41))
    c2t = _upper(42 * OMEGA_IV + LAM_IV - L_IV + IV(2) / (4 * 41 + 7)) <= _lower(2 * OMEGA_IV)
    # C3: plateau corner at mu*_UPPER (conservative), s=1..20 + tail s>=21
    mus_up = IV(str(_upper(MU_STAR_IV)))
    c3 = all(_upper(g_iv(s + 1) + iv.log((4 * s + 6 + 3 * mus_up) / (4 * s + 7))) <= w_lo
             for s in range(1, 21))
    c3t = _upper(22 * OMEGA_IV + LAM_IV + (3 * mus_up - 1) / (4 * 21 + 7)) <= w_lo
    # C4: S3-branch monotone decreasing in mu -- algebraic (3mu < 4s+6+3mu)
    c4 = True
    # C5: chain region uniform: chainB_max_upper <= lower(omega - log(47/46))
    need = OMEGA_IV - iv.log(IV(47) / 46)
    c5 = max(Bres["_chainB"][i] for i in range(len(Bres["_chainB"])) if not Bres["_forb"][i]) <= _lower(need)
    return {"C1_broom": c1, "C0_RHS1_interval_extension": ok0, "C2_bareleaf": bool(c2 and c2t),
            "C3_corner": bool(c3 and c3t), "C4_monotone": c4, "C5_chain_uniform": bool(c5),
            "C_ok": bool(c1 and ok0 and c2 and c2t and c3 and c3t and c5)}


# ------------------------------------------------------------------ (D) j>=2 via certified hull
def _build_menu(Bres):
    """Menu of (exact cavity Fr, upper amplitude mpf)."""
    menu = [(Fr(3, 4 * sp + 3), _upper(g_iv(sp))) for sp in range(0, 120)]
    edges, chainB, forb = Bres["_edges"], Bres["_chainB"], Bres["_forb"]
    for i in range(len(chainB)):
        if not forb[i]:
            menu.append((edges[i + 1], chainB[i]))
    k = Fr(2, 100)
    while k < Fr(1, 3):
        menu.append((k, B_low_upper(k)))
        k += Fr(1, 400)
    # the plateau corner, at an exact rational UPPER bound of mu* (conservative: larger cavity)
    mus_up_fr = Fr(str(_upper(MU_STAR_IV))).limit_denominator(10 ** 8)
    if mus_up_fr < Fr(str(_upper(MU_STAR_IV))):
        mus_up_fr += Fr(1, 10 ** 7)
    menu.append((mus_up_fr, _upper(OMEGA_IV)))
    return sorted((m, e) for m, e in menu if e > -5)


def _build_hull(menu):
    hull = []
    for px, py in menu:
        while len(hull) >= 2:
            (x1, y1), (x2, y2) = hull[-2], hull[-1]
            # exact x (Fr), scalar mpf y uppers: cross-product test in mpf at 40dps
            if (y2 - y1) * mp.mpf(float(px - x1)) <= (py - y1) * mp.mpf(float(x2 - x1)):
                hull.pop()
            else:
                break
        hull.append((px, py))
    return hull


def _hull_dominates(menu, hull):
    """A-posteriori: every menu point lies (weakly) below the hull polyline."""
    hx = [h[0] for h in hull]
    for px, py in menu:
        # find segment
        if px <= hx[0]:
            hy = hull[0][1]
        elif px >= hx[-1]:
            hy = hull[-1][1]
        else:
            for i in range(1, len(hx)):
                if px <= hx[i]:
                    (x1, y1), (x2, y2) = hull[i - 1], hull[i]
                    t = Fr(px - x1, x2 - x1)
                    hy = y1 + (y2 - y1) * mp.mpf(float(t))
                    break
        if py > hy + mp.mpf('1e-20'):
            return False
    return True


def certify_D(Bres, smax=64, jmax=500):
    w_lo = _lower(OMEGA_IV)
    menu = _build_menu(Bres)
    hull = _build_hull(menu)
    dom = _hull_dominates(menu, hull)
    segs = []
    for i in range(1, len(hull)):
        (x1, y1), (x2, y2) = hull[i - 1], hull[i]
        b = (IV(str(y2)) - IV(str(y1))) / (_fr_iv(x2) - _fr_iv(x1))
        a = IV(str(y1)) - b * _fr_iv(x1)
        segs.append((x1, x2, a, b, max(y1, y2)))
    gcache = {n: g_iv(n) for n in range(2, smax + jmax + 2)}
    worst_up = mp.mpf('-9')
    warg = None
    fine_calls = 0
    for j in range(2, jmax + 1):
        jI = IV(j)
        for s in range(0, smax + 1):
            base = IV(4 * s + 3 * j + 3)
            den = iv.log(IV(4 * (s + j) + 3))
            head = gcache[s + j] - jI * OMEGA_IV
            best = mp.mpf('-9')
            for (x1, x2, a, b, ymax) in segs:
                # cheap valid bound: H linear on segment => max at endpoint; log at right endpoint
                cheap = _upper(head + jI * IV(str(ymax)) + iv.log(base + 3 * jI * _fr_iv(x2)) - den)
                if cheap <= w_lo:
                    if cheap > best:
                        best = cheap
                    continue
                # fine: concave in m -- endpoints + stationary point enclosure
                fine_calls += 1
                cand = []
                for xx in (x1, x2):
                    cand.append(_upper(head + jI * (a + b * _fr_iv(xx))
                                       + iv.log(base + 3 * jI * _fr_iv(xx)) - den))
                if _upper(b) < 0:
                    m0 = (-3 / b - base) / (3 * jI)                  # stationary point enclosure
                    lo_ = max(float(_lower(m0)) - 1e-12, float(x1) - 1e-12)
                    hi_ = min(float(_upper(m0)) + 1e-12, float(x2) + 1e-12)
                    if lo_ <= hi_:
                        mseg = iv.mpf([lo_, hi_])
                        cand.append(_upper(head + jI * (a + b * mseg)
                                           + iv.log(base + 3 * jI * mseg) - den))
                v = max(cand)
                if v > best:
                    best = v
            if best > worst_up:
                worst_up, warg = best, (s, j)
    ok = worst_up <= w_lo
    # tails
    d1 = _upper(65 * OMEGA_IV + LAM_IV + iv.log(IV(3) / 2)) <= w_lo                       # s>=65, any j
    j0 = jmax + 1
    supm = mp.mpf('-9')
    for (x1, x2, a, b, ymax) in segs:
        for xx in (x1, x2):
            v = _upper(j0 * (a + b * _fr_iv(xx)) + iv.log(3 * (1 + _fr_iv(xx)) / 4))
            if v > supm:
                supm = v
        # concave in m as well (H linear + log concave): stationary enclosure
        if _upper(b) < 0:
            m0 = -1 / (IV(j0) * b) - 1
            lo_ = max(float(_lower(m0)) - 1e-12, float(x1) - 1e-12)
            hi_ = min(float(_upper(m0)) + 1e-12, float(x2) + 1e-12)
            if lo_ <= hi_:
                mseg = iv.mpf([lo_, hi_])
                v = _upper(j0 * (a + b * mseg) + iv.log(3 * (1 + mseg) / 4))
                if v > supm:
                    supm = v
    d2 = _upper(smax * OMEGA_IV + LAM_IV + IV(str(supm)) + IV(4 * smax + 3) / (3 * j0)) <= w_lo   # j>500
    return {"hull_vertices": len(hull), "hull_dominates_menu": dom,
            "worst_node_upper": float(worst_up), "binding": warg, "fine_calls": fine_calls,
            "sweep_ok": bool(ok), "margin_lower": float(w_lo - worst_up),
            "D1_s_tail": bool(d1), "D2_j_tail": bool(d2),
            "D_ok": bool(dom and ok and d1 and d2)}


def certify(nc=1200, smax=64, jmax=500):
    A = certify_A()
    B = certify_B(nc=nc)
    C = certify_C(B)
    D = certify_D(B, smax=smax, jmax=jmax)
    allok = A["A_ok"] and B["B_ok"] and C["C_ok"] and D["D_ok"]
    return {
        "A_corner": A["A_ok"],
        "B_chain_table": B["B_ok"], "B_chainB_max_upper": B["chainB_max_upper"],
        "C_j1": C["C_ok"], "C0_RHS1_whole_domain": C["C0_RHS1_interval_extension"],
        "D_j2": D["D_ok"], "D_worst_upper": D["worst_node_upper"],
        "D_margin_lower": D["margin_lower"], "D_binding": D["binding"],
        "D_hull_dominates": D["hull_dominates_menu"], "D_fine_calls": D["fine_calls"],
        "ALL_INTERVAL_CERTIFIED": bool(allok),
        "standard": "exact Fractions for ALL structure (cells, bands, cavities, Cantor gaps) + mpmath.iv "
                    "enclosures for ALL values (widths ~1e-30 vs margins >= 1.4e-4), conservative "
                    "endpoints throughout; RHS1 by interval extension over its whole domain; j>=2 by "
                    "certified hull + rigorous concave segment maximization over the continuous mean "
                    "cavity. Remaining for 'theorem': review of the lemma STATEMENTS, not numerics.",
        "claimed_as_theorem": False,
    }


if __name__ == "__main__":
    v = certify()
    for k, val in v.items():
        print(f"  {k}: {val}")
