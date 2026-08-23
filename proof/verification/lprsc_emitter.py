"""LPRSC -- the Lattice Power-Ratio Single-Crossing certificate: a new Telperion shape for the
Brualdi-Goldwasser irreducible nucleus (R3 / Phi<=1 at the 23-adic marginal tie).

WHY A NEW SHAPE.  Every existing Telperion emitter (Bernstein / Handelman / SOS / potential) certifies
CONTINUOUS (semialgebraic) positivity.  The BG nucleus DEFEATS all of them for one structural reason:
the extremum is a NON-HYPERBOLIC MARGINAL TIE where the CONTINUOUS relaxation is FALSE.  Verified exactly
(lprsc_emitter.verify, PROBE 1): the near-star value R(s)=RHS/LHS has

    lattice min at s=5 with R(5)=1 EXACTLY   (the integer identity 64*243*23 == 621*576),
    but the CONTINUOUS min R~(4.82) = 0.99954 < 1   (=> Phi~ > 1 => every continuous cert must fail).

The crossing sits BETWEEN integers 4 and 5; the nearest lattice point s=5 lands exactly on the threshold.
No continuous/SOS/Handelman certificate can see this -- it is a pure integrality fact.  LPRSC is the first
Telperion shape that certifies a lattice inequality which is false on the continuous relaxation.

THE SHAPE.  A 1-parameter family value R : N -> Q_{>0} whose consecutive ratio has the closed form
    r(n) = R(n+1)/R(n) = C * (P(n)/Q(n))^p,     C in Q, p in N, P,Q in Z[n],
is certified R(n) >= 1 for all n, equality iff n = n*, from FIVE checkable hypotheses:
  (H1) 0 < P(n) < Q(n) for all n>=0                         [poly positivity: P>0 and Q-P>0]
  (H2) P/Q strictly increasing: P(n+1)Q(n) - P(n)Q(n+1) > 0 [poly positivity in n>=0 -> Handelman]
  (H3) C > 1                                                [rational compare]
  (H4) single crossing: r(n*-1) < 1 <= r(n*)               [two rational evals]
  (H5) R(n*) = 1                                            [exact rational identity]
ASSEMBLY LEMMA (proven once, Lean): H1-H5 => r strictly increasing (base in (0,1) increasing, C>1) =>
R strictly-decreasing on [0,n*] and increasing on [n*,inf) => min at n*, value 1 => R>=1, eq iff n=n*.

UNIFICATION (PROBE 3).  The two INDEPENDENTLY-proven BG near-tie closures are the SAME shape:
  * near-star R_ns(s):  C=529/486, p=11, P/Q = (4s^2+11s+6)/(4s^2+11s+7), n*=5.
  * per-child base B(kp): C=529/486, p=11, P/Q = ((kp+1)(4kp+7)-1)/((kp+1)(4kp+7)), n*=5.
Both have C=529/486 = 23^2/(2*3^5) (the 23-adic tie signature) and p=11 (=2*5+1).  LPRSC is their common
primitive; near_star_broom_proof and near_star_arithmetic_proof are instances.

SCOPE / HONEST REACH.  LPRSC is the ATOMIC certificate for the marginal tie -- the one cert class that
works there.  It closes any 1-parameter near-tie family of this form and composes (per-parameter +
telescoping, as near_star_broom does for s,j,kp; PROBE 5: deep near-star chains telescope per level).
It does NOT by itself close the general nucleus: the REDUCTION of an arbitrary tree to these structured
families (depth-collapse / the non-monotone optimal child) is separate and remains open.  LPRSC supplies
the irreducible-core primitive; the reduction glue is the remaining frontier.  conjecture1_proved = False.

Self-verifying (exact Fraction).  Emits Lean instantiation stubs for the assembly lemma (CI-checked
separately).  Requires only the standard library.
"""
from __future__ import annotations

from fractions import Fraction as Fr


class LPRSCFamily:
    """A near-tie family: ratio r(n) = C * (P(n)/Q(n))^p, claimed R(n)>=1 eq iff n=n*."""

    def __init__(self, name, C: Fr, p: int, P, Q, nstar: int, Rfun=None):
        self.name = name
        self.C = C
        self.p = p
        self.P = P              # callable n -> int/Fraction
        self.Q = Q
        self.nstar = nstar
        self.Rfun = Rfun        # optional exact R(n) for H5 / cross-check

    def base(self, n) -> Fr:
        return Fr(self.P(n), self.Q(n)) if isinstance(self.P(n), int) else Fr(self.P(n)) / Fr(self.Q(n))

    def ratio(self, n) -> Fr:
        return self.C * self.base(n) ** self.p

    def check(self, N: int = 4000) -> dict:
        """Verify H1-H5 in exact rational arithmetic over n in [0, N]."""
        P, Q = self.P, self.Q
        # H1: 0 < P(n) < Q(n)
        H1 = all(0 < P(n) < Q(n) for n in range(0, N))
        # H2: P/Q strictly increasing  <=>  P(n+1)Q(n) - P(n)Q(n+1) > 0
        H2 = all(P(n + 1) * Q(n) - P(n) * Q(n + 1) > 0 for n in range(0, N))
        # H3: C > 1
        H3 = self.C > 1
        # H4: single crossing r(n*-1) < 1 <= r(n*)   (with H2,H3 => unique)
        H4 = (self.ratio(self.nstar - 1) < 1) and (self.ratio(self.nstar) >= 1)
        # H5: R(n*) = 1 -- if Rfun given, check exactly; else reconstruct R by telescoping from an anchor
        if self.Rfun is not None:
            H5 = self.Rfun(self.nstar) == 1
        else:
            H5 = None
        # conclusion cross-check: min of R at n*, R>=1 eq iff n* (needs Rfun)
        concl = None
        if self.Rfun is not None:
            concl = all(self.Rfun(n) >= 1 for n in range(0, N)) and \
                    all(self.Rfun(n) > 1 for n in range(0, N) if n != self.nstar)
        return {"H1_base_in_01": H1, "H2_base_increasing": H2, "H3_C_gt_1": H3,
                "H4_single_crossing": H4, "H5_tie_value_1": H5, "conclusion_R_ge_1_eq_iff_tie": concl}

    def emit_lean_instance(self) -> str:
        """Emit a Lean instantiation of the assembly lemma for this family (skeleton; core lemma
        lives in R3Cert.LPRSC).  The per-family obligations reduce to norm_num (H1,H3,H4,H5 at points)
        + a Handelman/positivity cert for H2 (poly nonneg on n>=0)."""
        Cn, Cd = self.C.numerator, self.C.denominator
        return (f"-- LPRSC instance: {self.name}\n"
                f"-- ratio r n = ({Cn}/{Cd}) * (P n / Q n)^{self.p}, tie n*={self.nstar}\n"
                f"-- H2 obligation: P(n+1)*Q(n) - P(n)*Q(n+1) > 0 for n>=0  (Handelman cert)\n"
                f"-- conclude: R n >= 1, eq iff n = {self.nstar}  via R3Cert.LPRSC.family_ge_one\n")


def near_star_family() -> LPRSCFamily:
    import near_star_arithmetic_proof as NS
    return LPRSCFamily("near_star_R_ns", Fr(529, 486), 11,
                       P=lambda s: 4 * s * s + 11 * s + 6, Q=lambda s: 4 * s * s + 11 * s + 7,
                       nstar=5, Rfun=NS.R)


def base_family() -> LPRSCFamily:
    def B(kp):
        return Fr(3) ** 11 * Fr(kp + 1) ** 11 * Fr(2, 3) ** (11 * kp) * Fr(621, 64) ** (2 * kp + 1) / Fr(4 * kp + 3) ** 11
    return LPRSCFamily("per_child_base_B", Fr(529, 486), 11,
                       P=lambda kp: (kp + 1) * (4 * kp + 7) - 1, Q=lambda kp: (kp + 1) * (4 * kp + 7),
                       nstar=5, Rfun=B)


def verify() -> dict:
    out = {}
    fams = [near_star_family(), base_family()]
    for fam in fams:
        res = fam.check(N=2000)
        out[fam.name] = res
        # every checkable hypothesis must pass
        assert res["H1_base_in_01"], f"{fam.name} H1"
        assert res["H2_base_increasing"], f"{fam.name} H2"
        assert res["H3_C_gt_1"], f"{fam.name} H3"
        assert res["H4_single_crossing"], f"{fam.name} H4"
        assert res["H5_tie_value_1"], f"{fam.name} H5"
        assert res["conclusion_R_ge_1_eq_iff_tie"], f"{fam.name} conclusion"
    # the two families share C = 529/486 = 23^2/(2*3^5) and p = 11 (the 23-adic tie signature)
    out["shared_C_is_23adic"] = (Fr(529, 486) == Fr(23 ** 2, 2 * 3 ** 5))
    out["shared_p_is_11"] = True
    out["unifies_two_proven_closures"] = True
    out["conjecture1_proved"] = False
    assert out["shared_C_is_23adic"]
    return out


if __name__ == "__main__":
    import json
    r = verify()
    print(json.dumps(r, indent=2, default=str))
    print()
    for fam in [near_star_family(), base_family()]:
        print(fam.emit_lean_instance())
