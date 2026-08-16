"""The mixed-layer H-floor pieces, Telperion-encoded — the agreed cross-session
deliverable feeding HypAmortizedHub.

Input specification: ``g1_hfloor_table.json`` — the origin session's
feasibility-probe piece table (origin commit e898a452,
experiments/graph_hunter/laplacian_ratio/g1_hfloor_table.json): 56 pieces
across m in 2..7 at the 47/2000 floor, S in (0, m/2], each piece carrying
(S0, S1, u0, q, u1, cav_hi, chat(S0/m)) — Fraction-verified origin-side
through their own H_lower.

SPELLING CONTRACT (the agreed coordination condition — the G1 bridge-cost
lesson): claims are stated in ORIGIN'S H/slackForm spelling.  The origin
minorant is

    H_lower(m, S0, S1) = L - log1p_upper(S1/(m+1)) + m*chat(S0/m)
                         - (11/50) * max(0, 1/(m+1+S0) - T_LO)

with log1p_upper(u1) = q + (u1 - u0)/(1 + u0) at the piece's dyadic anchor.
Every quantity is an exact rational EXCEPT the bracketed constant
L = log(621/64)/11 in [206586, 206587]/10^6 — so each piece claim is LINEAR
in the single interval symbol L, lowered onto the box machinery by
``interval_family`` (the G1Floors pattern, one axis).  Instantiating at the
real L (bracket facts already kernel-checked in G1Anchors: L_bracket_lo/hi)
yields the true per-piece floor; the chat <= true-cost validity connection
and the m >= 8 uniform lemma remain ORIGIN-SIDE work by the agreed split.

The anchors family emits the deduped log1p concavity anchors
(1 + u0 <= Taylor_K(q) at minimal closing depth K) that the pieces stand on.

conjecture1_proved = False; this discharges the H-floor piece stratum at
generator level — the Lean build is the verdict.
"""
from __future__ import annotations

import json
from fractions import Fraction as Fr
from pathlib import Path

import sympy as sp

from telperion import GridSpec, LeanProfile, ValidationReport, interval_family

HERE = Path(__file__).resolve().parent

# ---- origin constants (g1_floor_certificates / g1_endpoint_certificates) -----
L_LO, L_HI = Fr(206586, 10**6), Fr(206587, 10**6)
T_LO, T_HI = Fr(2294736, 10**7), Fr(2294737, 10**7)
C_HINGE = Fr(11, 50)
EPS_WIN = Fr(29, 1000)
B_WIN = T_HI - EPS_WIN                # chat's certain-window start
FLOOR = Fr(47, 2000)

L = sp.Symbol("L", nonnegative=True)


def chat(y: Fr) -> Fr:
    """Exact port of the origin chat minorant (independent engine)."""
    if y <= B_WIN:
        return Fr(0)
    if y <= T_HI + EPS_WIN:
        return (C_HINGE / 2) * (y - B_WIN)
    return C_HINGE * (y - T_HI)


def exp_lower(x: Fr, K: int) -> Fr:
    s, term = Fr(0), Fr(1)
    for k in range(K + 1):
        s += term
        term = term * x / (k + 1)
    return s


# ---- the piece table (the origin-side specification, verbatim) ---------------

_PIECES = None


def pieces():
    """(m, S0, S1, u0, q, u1, cav_hi, chat_S0m) per piece, table order."""
    global _PIECES
    if _PIECES is None:
        doc = json.loads((HERE / "g1_hfloor_table.json").read_text())
        out = []
        for m_str, entry in doc.items():
            assert Fr(entry["floor"]) == FLOOR
            for p in entry["pieces"]:
                out.append((int(m_str), Fr(p["S0"]), Fr(p["S1"]), Fr(p["u0"]),
                            Fr(p["q"]), Fr(p["u1"]), Fr(p["cav_hi"]),
                            Fr(p["chat_S0m"])))
        _PIECES = out
    return _PIECES


def H_lower_fraction(m, S0, u0, q, u1, cav_hi, chat_S0m, Lv: Fr) -> Fr:
    """The origin H_lower with log1p_upper opened at the piece anchor."""
    log_up = q + (u1 - u0) / (1 + u0)
    pen = C_HINGE * max(Fr(0), cav_hi - T_LO)
    return Lv - log_up + m * chat_S0m - pen


def _target(pc) -> sp.Expr:
    m, S0, S1, u0, q, u1, cav_hi, chat_S0m = pc
    log_up = q + (u1 - u0) / (1 + u0)
    pen = C_HINGE * max(Fr(0), cav_hi - T_LO)   # decided exactly at build time
    return (L - sp.Rational(log_up) + sp.Rational(m * chat_S0m)
            - sp.Rational(pen) - sp.Rational(FLOOR))


def _name(pc) -> str:
    m, S0, S1 = pc[0], pc[1], pc[2]
    return (f"hfloor_m{m}_S{S0.numerator}_{S0.denominator}"
            f"_{S1.numerator}_{S1.denominator}")


def family():
    ps = pieces()
    return interval_family(
        name="HFloors",
        symbols=(),
        grid=GridSpec([("piece", list(range(len(ps))))]),
        lean_name=lambda pt: _name(ps[pt["piece"]]),
        target=lambda pt: _target(ps[pt["piece"]]),
        brackets={L: (sp.Rational(L_LO), sp.Rational(L_HI))},
    )


# ---- the anchors the pieces stand on (deduped, minimal Taylor depth) ---------


def anchor_facts():
    """(name, u0, q, K) for every distinct anchor pair in the table, with the
    MINIMAL K closing exp_lower(q, K) >= 1 + u0."""
    seen = {}
    for m, S0, S1, u0, q, u1, cav_hi, chat_S0m in pieces():
        if u0 in seen:
            assert seen[u0][1] == q, f"conflicting q for anchor {u0}"
            continue
        K = next(k for k in range(1, 31) if exp_lower(q, k) >= 1 + u0)
        seen[u0] = (f"anchor_{u0.numerator}_{u0.denominator}", q, K)
    return [(nm, u0, q, K) for u0, (nm, q, K) in sorted(seen.items())]


def profile() -> LeanProfile:
    # The single-axis interval family still lowers onto the bilinear box
    # machinery (with an inert second axis), whose assembly calls the
    # box-corner lemma — so every self-contained frozen file must carry it in
    # its own namespace (the G1 lesson: the compile gate, not the self-checks,
    # is what catches a missing prelude dependency).
    prelude = """/-- A bilinear form nonnegative at the four corners of a box is nonnegative on it. -/
theorem bilinear_corner_nonneg {A B C E s t s0 s1 t0 t1 : ℝ}
    (hs0 : s0 ≤ s) (hs1 : s ≤ s1) (ht0 : t0 ≤ t) (ht1 : t ≤ t1)
    (h00 : 0 ≤ A + B * s0 + C * t0 + E * (s0 * t0))
    (h01 : 0 ≤ A + B * s0 + C * t1 + E * (s0 * t1))
    (h10 : 0 ≤ A + B * s1 + C * t0 + E * (s1 * t0))
    (h11 : 0 ≤ A + B * s1 + C * t1 + E * (s1 * t1)) :
    0 ≤ A + B * s + C * t + E * (s * t) := by
  have hfix : ∀ sv : ℝ, 0 ≤ A + B * sv + C * t0 + E * (sv * t0) →
      0 ≤ A + B * sv + C * t1 + E * (sv * t1) →
      0 ≤ A + B * sv + C * t + E * (sv * t) := by
    intro sv e0 e1
    rcases le_total 0 (C + E * sv) with hb | hb
    · nlinarith [mul_nonneg hb (sub_nonneg.mpr ht0)]
    · nlinarith [mul_nonneg (neg_nonneg.mpr hb) (sub_nonneg.mpr ht1)]
  have H0 := hfix s0 h00 h01
  have H1 := hfix s1 h10 h11
  rcases le_total 0 (B + E * t) with hb | hb
  · nlinarith [mul_nonneg hb (sub_nonneg.mpr hs0)]
  · nlinarith [mul_nonneg (neg_nonneg.mpr hb) (sub_nonneg.mpr hs1)]"""
    return LeanProfile(namespace=("G1", "HFloor"), prelude=prelude)


def validation() -> ValidationReport:
    """Trust-but-verify the origin table: every derived column recomputed
    from (m, S0, S1) by the independent engine; every anchor kernel-checked;
    every piece bound re-established at the pessimistic bracket corner."""

    def table_consistent():
        for m, S0, S1, u0, q, u1, cav_hi, chat_S0m in pieces():
            assert Fr(0) <= S0 < S1 <= Fr(m, 2), (m, S0, S1)
            assert u1 == S1 / (m + 1), (m, S1, u1)
            assert cav_hi == Fr(1) / (m + 1 + S0), (m, S0, cav_hi)
            assert chat_S0m == chat(S0 / Fr(m)), (m, S0, chat_S0m)
            assert u0 == Fr(int(u1 * 512), 512), (u1, u0)   # dyadic anchor
            assert u0 <= u1

    def anchors_verified():
        for name, u0, q, K in anchor_facts():
            assert exp_lower(q, K) >= 1 + u0, name
            assert exp_lower(q, 30) >= 1 + u0, name

    def floors_hold_at_corner():
        n = 0
        for pc in pieces():
            m, S0, S1, u0, q, u1, cav_hi, chat_S0m = pc
            assert H_lower_fraction(m, S0, u0, q, u1, cav_hi, chat_S0m,
                                    L_LO) >= FLOOR, pc
            n += 1
        assert n == 56, n

    def coverage_contiguous():
        """The pieces tile (0, m/2] per m: sorted intervals abut exactly."""
        by_m: dict[int, list] = {}
        for m, S0, S1, *_ in pieces():
            by_m.setdefault(m, []).append((S0, S1))
        assert sorted(by_m) == list(range(2, 8))
        for m, iv in by_m.items():
            iv.sort()
            assert iv[0][0] == 0 and iv[-1][1] == Fr(m, 2), m
            for (a0, a1), (b0, b1) in zip(iv, iv[1:]):
                assert a1 == b0, (m, a1, b0)

    return ValidationReport.from_asserts([
        ("hfloor_table_consistent", table_consistent),
        ("hfloor_anchors_verified", anchors_verified),
        ("hfloor_bound_at_corner", floors_hold_at_corner),
        ("hfloor_coverage_contiguous", coverage_contiguous),
    ])
