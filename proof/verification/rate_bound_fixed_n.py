"""THE FIXED-n RATE BOUND: pi(T) <= (4/3) * rhoB^n for EVERY n-vertex tree -- the stratum-(i)
pillar, reduced to two elementary lemmas on top of the machine-checked Lean bridge.

THE THEOREM.  For every tree T on n >= 2 vertices,

    pi(T)  =  per(L(T)) / prod deg  <=  (4/3) * rhoB^n,        rhoB = (621/64)^(1/11).

This is the first UNIFORM fixed-n bound in the program (the conjectured sharp constant is
C_1 = (26/23)/rhoB ~ 0.919446; the 4/3 is a crude root-boundary constant, NOT the sharp one).  It
makes "rate <= rhoB for every tree family" a fixed-n statement -- the stratification's stratum-(i)
premise -- and it is rigorous MODULO exactly one input: phi_le_one (logPhi <= 0 for every Branch),
which is already a machine-checked, CI-green Lean theorem (PotentialFinal.lean).

PROOF (all pieces verified exactly below).  Root T at any LEAF r.
  (1) EXACT IDENTITY (verify_identity, every tree <= 9 x every root):
          pi(T) = Z(T^r) * R(r),
      where Z(T^r) is the PHANTOM-ROOT matching partition function -- the matching sum with
      vertex weights 1/deg except 1/(deg+1) at the root -- which IS the machine-checked bridge
      object Ztot(litRealize(b)) = exp(logPhi b) * rhoB^Vb for the Branch parse b of T^r
      (convention pinned by the tie: Z(N(5,0) at its hub) = 621/64 = rhoB^11 EXACTLY, the
      phi_le_one equality case; verified below).  Both pi and Z are LINEAR in the root weight:
      pi = A0 + A1/d, Z = A0 + A1/(d+1), so pi/Z = R = (1 + S/d)/(1 + S/(d+1)), S = A1/A0.
  (2) S <= 1 AT A LEAF ROOT (verify_S_le_1):  A1 = z_c * M(T - r - c) and A0 = M(T - r)
      (c = the leaf's neighbour); every matching of T-r-c is one of T-r, and z_c = 1/deg(c) <= 1,
      so A1 <= A0.  [One-line injection; no structure theory needed.]
  (3) R <= 4/3 (leaf root, d = 1):  R = (1+S)/(1+S/2) is increasing in S, and at S = 1 equals
      4/3.  SHARP: attained by the 2-path P2 (S = 1).
  (4) Z <= rhoB^n:  exp(logPhi b) <= 1  (phi_le_one)  times  rhoB^Vb,  via the bridge identity
      exp_logPhi_mul_rhoB_pow (BridgeStep4c, CI-green).  Cross-checked here rationally
      (Z^11 * 64^V <= 621^V * Zden^11) on ALL 1808 rooted trees <= 10 vertices, 0 violations,
      0 ties (first tie at V = 11, the near-star, as the theory demands).

THE REFRAMING (the deeper value for R7').  The identity pi(T) = Z(T^r) * R(r) is EXACT, so the
fixed-n maximizer problem is EXACTLY

    maximize   exp(logPhi b) * R   over Branch parses b of n-vertex rooted trees,

i.e. the whole of R7' lives in the Branch model with an explicit, elementary boundary factor
R in (1, 4/3].  Sharpening 4/3 toward C_1 = the remaining constant-order structure theory
(R5/R6/merge layer); the RATE level is closed by this module + phi_le_one.

LEAN PORT (cheap; all heavy inputs exist CI-green):
  (a) parse : rooted tree -> Branch with litRealize(parse) = the tree -- or directly on the
      campaign's UTree: define Z as the phantom-weight matching sum and prove Z = Ztot(litRealize
      (parseB t)) by the BridgeStep2/4c machinery;
  (b) the A0/A1 linear split in the root weight (one matching-sum case split);
  (c) S <= 1 (the injection above) and R <= 4/3 (field_simp);
  (d) chain with exp_logPhi_mul_rhoB_pow + phi_le_one.

conjecture1_proved=False (this bounds the rate, it does not identify the maximizer).
Requires networkx.  Self-verifying run_all(); every claim is an assert.
"""
from __future__ import annotations

from fractions import Fraction as Fr

import networkx as nx

from verification.kelmans_mixed_load import (
    psi_weighted,
    pi_literal,
)


def f_at(T: nx.Graph, r, zr: Fr) -> Fr:
    """Matching sum with root weight zr, all other vertices 1/deg."""
    z = {v: (zr if v == r else Fr(1, T.degree(v))) for v in T.nodes()}
    return psi_weighted(T, z)


def Z_of(T: nx.Graph, r) -> Fr:
    """The phantom-root partition function = Ztot(litRealize(parse(T^r)))."""
    return f_at(T, r, Fr(1, T.degree(r) + 1))


def verify_identity(n_max: int = 9) -> dict:
    """pi = Z * R with R = (1+S/d)/(1+S/(d+1)), S = A1/A0, on every tree x every root."""
    checked = 0
    for n in range(2, n_max + 1):
        for T in nx.nonisomorphic_trees(n):
            T = nx.convert_node_labels_to_integers(T)
            for r in T.nodes():
                d = T.degree(r)
                A0 = f_at(T, r, Fr(0))
                A1 = f_at(T, r, Fr(1)) - A0
                pi = f_at(T, r, Fr(1, d))
                Z = f_at(T, r, Fr(1, d + 1))
                assert pi == pi_literal(T)
                assert pi == A0 + A1 * Fr(1, d) and Z == A0 + A1 * Fr(1, d + 1)
                S = A1 / A0
                R = (1 + S * Fr(1, d)) / (1 + S * Fr(1, d + 1))
                assert pi == Z * R, (n, r)
                checked += 1
    return {"identity_exact": True, "cases": checked}


def verify_S_le_1_and_R(n_max: int = 9) -> dict:
    """At every LEAF root: S <= 1 and R <= 4/3, with 4/3 attained (P2)."""
    checked = 0
    worstR = Fr(0)
    for n in range(2, n_max + 1):
        for T in nx.nonisomorphic_trees(n):
            T = nx.convert_node_labels_to_integers(T)
            for r in T.nodes():
                if T.degree(r) != 1:
                    continue
                A0 = f_at(T, r, Fr(0))
                A1 = f_at(T, r, Fr(1)) - A0
                S = A1 / A0
                assert S <= 1, (n, r)
                R = (1 + S) / (1 + S / 2)
                assert R <= Fr(4, 3), (n, r)
                worstR = max(worstR, R)
                checked += 1
    assert worstR == Fr(4, 3)          # sharp (P2)
    return {"leaf_roots": checked, "S_le_1": True, "max_R": str(worstR), "sharp": True}


def verify_convention_tie() -> dict:
    """Z(N(5,0) at its hub) == 621/64 == rhoB^11 -- pins the phantom convention to the
    machine-checked Branch object (the phi_le_one equality case)."""
    T = nx.Graph()
    for i in range(5):
        m, l = 1 + 2 * i, 2 + 2 * i
        T.add_edge(0, m)
        T.add_edge(m, l)
    assert Z_of(T, 0) == Fr(621, 64)
    return {"tie_convention": True, "Z": "621/64"}


def verify_Z_le_rhoB_pow(n_max: int = 10) -> dict:
    """Cross-check of phi_le_one's reach over ARBITRARY rooted trees, rationally:
    Znum^11 * 64^V <= 621^V * Zden^11.  (The theorem input; verified independently.)"""
    checked = 0
    ties = 0
    for n in range(2, n_max + 1):
        for T in nx.nonisomorphic_trees(n):
            T = nx.convert_node_labels_to_integers(T)
            for r in T.nodes():
                Z = Z_of(T, r)
                lhs = Z.numerator ** 11 * 64 ** n
                rhs = 621 ** n * Z.denominator ** 11
                assert lhs <= rhs, (n, r)
                ties += int(lhs == rhs)
                checked += 1
    assert ties == 0                    # first tie is at V = 11 (the near-star)
    return {"rooted_trees": checked, "Z_le_rhoB_pow": True, "ties_below_11": 0}


def verify_rate_bound(n_max: int = 10) -> dict:
    """The THEOREM end-to-end, rationally: pi(T)^11 * 64^n * 3^11 <= 621^n * 4^11 * (piden)^11
    i.e. pi <= (4/3) rhoB^n, on every tree <= n_max."""
    checked = 0
    for n in range(2, n_max + 1):
        for T in nx.nonisomorphic_trees(n):
            T = nx.convert_node_labels_to_integers(T)
            pi = pi_literal(T)
            lhs = pi.numerator ** 11 * 64 ** n * 3 ** 11
            rhs = 621 ** n * 4 ** 11 * pi.denominator ** 11
            assert lhs <= rhs, n
            checked += 1
    return {"trees": checked, "rate_bound_holds": True}


def run_all():
    out = {}
    out["identity"] = verify_identity()
    out["S_and_R"] = verify_S_le_1_and_R()
    out["tie_convention"] = verify_convention_tie()
    out["Z_le_rhoB_pow"] = verify_Z_le_rhoB_pow()
    out["rate_bound"] = verify_rate_bound()
    out["theorem"] = {
        "statement": "pi(T) <= (4/3) * rhoB^n for EVERY n-vertex tree",
        "inputs": "phi_le_one + exp_logPhi_mul_rhoB_pow (both CI-green Lean theorems) + "
                  "the two elementary lemmas verified here (S<=1 at leaf roots; R<=4/3)",
        "reframing": "pi(T) = Z(T^r) * R(r) EXACTLY -- R7' fixed-n maximization lives in the "
                     "Branch model with an explicit boundary factor in (1, 4/3]",
        "conjecture1_proved": False,
    }
    for k, v in out.items():
        print(f"  {k}: {v}")
    return out


if __name__ == "__main__":
    run_all()
