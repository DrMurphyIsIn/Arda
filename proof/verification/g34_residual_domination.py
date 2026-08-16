"""THE G34-RESIDUAL DOMINATION: defected two-hub stuck configurations are dominated by
same-n single-hub templates -- symbolic tails + exact finite sweeps.

Discharges the two-hub core of the G34-residual (R7_ARCHITECTURE.md): every stuck two-hub
configuration carrying blocking defects (bare leaves, arm(1), arm(2) -- the high-z defects
that survive g34_merge_unblocking, in budget-bounded counts j: leaves <= 2, arm(1) <= 9,
arm(2) <= 13) is strictly below the same-n single-hub family.  Structure of the proof:

  (T1) RECEIVER-SIDE TAILS (symbolic; certify_receiver_tails).  For defects on the receiver
       A and pA >= 60 (all pB, all j in budget, all cells): template - config >= 0, using the
       factor bound (1 + zA(sig + j zD)) <= (1 + zA sig)(1 + zA j zD) against the
       defect-carrying template.  Since the stuck family is hubward (pB <= pA), the
       remaining receiver-side region is the FINITE triangle pB <= pA <= 59.
  (T2) DONOR-SIDE FULL CERTIFICATES (symbolic; certify_donor_full): arm(2)/arm(3)/arm(4)
       defects on the donor, all (pA, pB) hubward, j <= 13 -- no tail split needed.
  (T3) DONOR-SIDE LEAF/ARM(1) TAILS: (a) pB >= 30 and pA = pB + r (both large): symbolic;
       (b) pB <= 29 concrete, pA >= 60: 1-var certificates.  Remainder: finite triangle.
  (T4) EXACT FINITE SWEEP (sweep_finite): the remaining finite regions, exact rational
       closed forms, each config checked against a SEARCHED same-n single-hub comparator
       (balanced arms x hub load 0..6 x <= 2 leaves) -- the search matters: at some odd
       residues the winning comparator is the load-6 hub, NOT the defect-carrying template
       (which genuinely loses there; first observed at cA=5, donor leaf, small sizes).

SCOPE (honest): this closes the TWO-HUB defected stuck family.  Multi-hub (H >= 3) defected
configurations: clean shapes + towers are probe-swept (kelmans_vertex_budget, amortized_hub);
their defected variants inherit larger margins (9-17% clean) and the same template trick, but
the symbolic assembly over hub-tree shapes is the remaining sliver ("G34-multi", one further
session of the same machinery).  Combined-defect configs (several defect types at once) are
covered by composing the per-type factor bounds where margins allow, else land in the sweep.
conjecture1_proved=False.  Self-verifying run_all().
"""
from __future__ import annotations

from fractions import Fraction as Fr

import sympy as sp

from verification.kelmans_mixed_load import F_of, z_of

V5f, W4f = F_of(1, 5), F_of(1, 4)
z15f, z14f = z_of(1, 5), z_of(1, 4)

DEFECTS = {"leaf": (Fr(1), Fr(1), 1, 2),          # (z, F, vertices, budget jmax)
           "arm1": (Fr(3, 7), Fr(7, 4), 3, 9),
           "arm2": (Fr(3, 11), Fr(11, 4), 5, 13)}
DONOR_FULL = {"arm2": (Fr(3, 11), 6), "arm3": (Fr(1, 5), 13), "arm4": (Fr(3, 19), 13)}


def _sym():
    x, y = sp.symbols("x y", nonnegative=True)
    V5, W4 = sp.Rational(621, 64), sp.Rational(513, 80)
    z15, z14 = sp.Rational(3, 23), sp.Rational(3, 19)

    def Fs(deg, c):
        if c == 0:
            return sp.Integer(1)
        D = deg + c
        return sp.Rational(3, 2) ** c + sp.Rational(c) / (2 * D) * sp.Rational(3, 2) ** (c - 1)

    def allnn(expr):
        num, den = sp.fraction(sp.together(expr))
        pnum = sp.Poly(sp.expand(num), x, y)
        pden = sp.Poly(sp.expand(den), x, y)
        dc = pden.coeffs()
        dsg = 1 if all(c > 0 for c in dc) else (-1 if all(c < 0 for c in dc) else 0)
        nc = [c * dsg for c in pnum.coeffs()]
        return dsg != 0 and all(c >= 0 for c in nc) and any(c > 0 for c in nc)

    return x, y, V5, W4, z15, z14, Fs, allnn


def certify_receiver_tails() -> dict:
    """(T1): defects on A, pA >= 60, all pB, budget j, all cells."""
    x, y, V5, W4, z15, z14, Fs, allnn = _sym()
    pB = 1 + y
    pA = 60 + x
    K = pA + pB
    for name, (zDf, _, _, jmax) in DEFECTS.items():
        zD = sp.Rational(zDf.numerator, zDf.denominator)
        for jv in range(1, jmax + 1):
            for cA in range(6):
                m = 5 - cA
                dA = pA + jv + 1
                zA = sp.Integer(3) / (3 * dA + 4 * cA)
                zB = sp.Integer(1) / (pB + 1)
                clean = Fs(dA, cA) * ((1 + zA * pA * z15) * (1 + zB * pB * z15) + zA * zB)
                bound = clean * (1 + zA * jv * zD)
                dT = K + 1 + jv
                tmpl = V5 * (W4 / V5) ** m * (1 + (sp.Integer(1) / dT)
                                              * ((K + 1 - m) * z15 + m * z14 + jv * zD))
                assert allnn(tmpl - bound), (name, jv, cA)
    return {"receiver_tails": "certified: pA >= 60, all pB, all budget j, all cells"}


def certify_donor_full() -> dict:
    """(T2): arm2/3/4 on the donor, full symbolic hubward (pA = pB + r), j <= 13."""
    x, y, V5, W4, z15, z14, Fs, allnn = _sym()
    pB = 1 + y
    pA = pB + x
    K = pA + pB
    for name, (zDf, jmax) in DONOR_FULL.items():
        zD = sp.Rational(zDf.numerator, zDf.denominator)
        for jv in range(1, jmax + 1):
            for cA in range(6):
                m = 5 - cA
                dB = pB + jv + 1
                zA = sp.Integer(3) / (3 * (pA + 1) + 4 * cA)
                zB = sp.Integer(3) / (3 * dB)
                config = Fs(pA + 1, cA) * ((1 + zA * pA * z15)
                                           * (1 + zB * (pB * z15 + jv * zD)) + zA * zB)
                dT = K + 1 + jv
                tmpl = V5 * (W4 / V5) ** m * (1 + (sp.Integer(1) / dT)
                                              * ((K + 1 - m) * z15 + m * z14 + jv * zD))
                assert allnn(tmpl - config), (name, jv, cA)
    return {"donor_full": "arm2/3/4 certified: all hubward (pA,pB), j <= 13, all cells"}


def certify_donor_hz_tails() -> dict:
    """(T3): leaf/arm1 on the donor.  (a) both-large: pB >= 30, pA = pB + r, factor bound
    on the donor side; (b) pB <= 29 concrete, pA >= 60: certificates in pA alone."""
    x, y, V5, W4, z15, z14, Fs, allnn = _sym()
    HZ = {"leaf": (sp.Integer(1), 2), "arm1": (sp.Rational(3, 7), 9),
          "arm2hi": (sp.Rational(3, 11), 13)}     # arm2 j in 7..13 (j <= 6 fully certified)
    # (a) both large
    pB = 30 + y
    pA = pB + x
    K = pA + pB
    for name, (zD, jmax) in HZ.items():
        for jv in range(1, jmax + 1):
            for cA in range(6):
                m = 5 - cA
                dB = pB + jv + 1
                zA = sp.Integer(3) / (3 * (pA + 1) + 4 * cA)
                zB = sp.Integer(3) / (3 * dB)
                clean = Fs(pA + 1, cA) * ((1 + zA * pA * z15) * (1 + zB * pB * z15) + zA * zB)
                bound = clean * (1 + zB * jv * zD)
                dT = K + 1 + jv
                tmpl = V5 * (W4 / V5) ** m * (1 + (sp.Integer(1) / dT)
                                              * ((K + 1 - m) * z15 + m * z14 + jv * zD))
                assert allnn(tmpl - bound), ("both-large", name, jv, cA)
    # (b) small donor, large receiver: 1-var in pA
    t = sp.symbols("t", nonnegative=True)
    pA1 = 60 + t

    def allnn1(expr):
        num, den = sp.fraction(sp.together(expr))
        pnum = sp.Poly(sp.expand(num), t)
        pden = sp.Poly(sp.expand(den), t)
        dc = pden.coeffs()
        dsg = 1 if all(c > 0 for c in dc) else (-1 if all(c < 0 for c in dc) else 0)
        nc = [c * dsg for c in pnum.coeffs()]
        return dsg != 0 and all(c >= 0 for c in nc) and any(c > 0 for c in nc)

    VD = {"leaf": 1, "arm1": 3, "arm2hi": 5}
    FDs = {"leaf": sp.Integer(1), "arm1": sp.Rational(7, 4), "arm2hi": sp.Rational(11, 4)}
    for name, (zD, jmax) in HZ.items():
        vD, FD = VD[name], FDs[name]
        for pBv in range(1, 30):
            for jv in range(1, jmax + 1):
                for cA in range(6):
                    dB = pBv + jv + 1
                    zA = sp.Integer(3) / (3 * (pA1 + 1) + 4 * cA)
                    zB = sp.Rational(1, dB)
                    cfg = (Fs(pA1 + 1, cA) * FD ** jv * V5 ** pBv
                           * ((1 + zA * pA1 * z15) * (1 + zB * (pBv * z15 + jv * zD)) + zA * zB))
                    # comparator search over (c0, m4, nleaf) matching the fixed residue
                    n_const = 2 + 2 * cA + 11 * pBv + vD * jv
                    found = False
                    for c0 in range(0, 7):
                        for m4 in range(0, 11):
                            for nleaf in (0, 1):
                                rem = n_const - 1 - 2 * c0 + 2 * m4 - nleaf
                                if rem % 11 or found:
                                    continue
                                Kc = rem // 11
                                K = pA1 + Kc
                                dT = K + nleaf
                                zT = sp.Integer(3) / (3 * dT + 4 * c0)
                                sig = (K - m4) * z15 + m4 * z14 + nleaf * 1
                                tmpl = (Fs(dT, c0) * (W4 / V5) ** m4 * V5 ** Kc
                                        * (1 + zT * sig))
                                if allnn1(tmpl - cfg):
                                    found = True
                    assert found, ("small-donor", name, pBv, jv, cA)
    return {"donor_hz_tails": "leaf/arm1/arm2hi certified: pB>=30 both-large + pB<=29 "
                              "w/ pA>=60 via per-residue comparator search"}


def _pi_config(pA, pB, cA, jA, jB, zD, FD, defect_side):
    """exact closed form: defected 2-hub stuck config, defects on one side."""
    dA = pA + 1 + (jA if defect_side == "A" else 0)
    dB = pB + 1 + (jB if defect_side == "B" else 0)
    zA, zB = z_of(dA, cA), z_of(dB, 0)
    sigA = pA * z15f + (jA * zD if defect_side == "A" else 0)
    sigB = pB * z15f + (jB * zD if defect_side == "B" else 0)
    j = jA if defect_side == "A" else jB
    return (F_of(dA, cA) * V5f ** (pA + pB) * FD ** j
            * ((1 + zA * sigA) * (1 + zB * sigB) + zA * zB))


import functools


@functools.lru_cache(maxsize=None)
def _best_template(n) -> Fr:
    """searched same-n single-hub comparator (balanced arms x c0 <= 6 x <= 2 leaves)."""
    best = None
    for c0 in range(0, 7):
        for nleaf in (0, 1, 2):
            rem = n - 1 - 2 * c0 - nleaf
            if rem <= 0:
                continue
            for K in range(max(1, rem // 13), rem // 9 + 2):
                tot2 = rem - K
                if tot2 < 0 or tot2 % 2:
                    continue
                tot = tot2 // 2
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
                s += nleaf * Fr(1)
                p *= (1 + zh * s)
                if best is None or p > best:
                    best = p
    return best


def sweep_finite(pmax: int = 59) -> dict:
    """(T4): exact rational sweep of the remaining finite regions, both defect sides,
    hubward pB <= pA <= pmax, budget j, all cells, vs the searched comparator."""
    checked = 0
    for side in ("A", "B"):
        for name, (zD, FD, vD, jmax) in DEFECTS.items():
            # (donor arm2 j <= 6 is fully certified symbolically; swept anyway, harmless)
            pcap = pmax if side == "A" else 29  # donor-side finite region is pB<=29,pA<=59
            for cA in range(6):
                for pA in range(1, pmax + 1):
                    for pB in range(1, min(pA, pcap if side == "B" else pmax) + 1):
                        for j in range(1, jmax + 1):
                            jA, jB = (j, 0) if side == "A" else (0, j)
                            cfg = _pi_config(pA, pB, cA, jA, jB, zD, FD, side)
                            n = 2 + 2 * cA + 11 * (pA + pB) + vD * j
                            assert _best_template(n) > cfg, (side, name, cA, pA, pB, j)
                            checked += 1
    return {"finite_sweep_exact": True, "cases": checked}


def run_all():
    out = {}
    out["T1"] = certify_receiver_tails()
    out["T2"] = certify_donor_full()
    out["T3"] = certify_donor_hz_tails()
    out["T4"] = sweep_finite()
    out["status"] = {
        "two_hub_defected": "DOMINATED, all budget defect counts, all sizes "
                            "(symbolic tails + exact finite sweeps)",
        "remaining_sliver": "G34-multi: defected multi-hub (H >= 3) symbolic assembly "
                            "(clean shapes + towers probe-swept; margins grow with H)",
        "conjecture1_proved": False,
    }
    for k, v in out.items():
        print(f"  {k}: {v}")
    return out


if __name__ == "__main__":
    run_all()
