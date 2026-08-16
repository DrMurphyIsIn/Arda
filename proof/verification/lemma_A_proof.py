"""SYMBOLIC PROOF of LEMMA A (chi_v(y=T0) <= 0), the last non-symbolic piece of proof_via_explicit_potential.
Reduces to two elementary facts + the already-proven near-star bound.  Self-verifying (exact where possible).

LEMMA A.  For every a>=0, nl in {0,1}, m>=0, the charge of a node with a arms, nl leaf, and m structural
children ALL at cavity T0=rho_B-1 is nonpositive:
    chi(T0) := -L + log(1 + S/w) + a*OMEGA + nl*(-L) <= 0,   S=a/3+nl+m*T0,  w=a+nl+m+1.
(L=log rho_B, OMEGA=log(3/2)-2L, rho_B=(621/64)^(1/11), and 1+T0=rho_B so log(1+T0)=L.)

REDUCTION (exact algebra).  Using 1+T0=rho_B=:r, w+S = 4a/3 + 2nl + m*r + 1, so
    chi(T0)<=0  <=>  log((4a/3+2nl+m*r+1)/(a+nl+m+1)) <= L(1+nl+2a) - a*log(3/2).
Exponentiating (exp monotone) and with C := r^(1+nl+2a)*(2/3)^a:
    chi(T0)<=0  <=>  4a/3+2nl+1 + m*r <= (a+nl+1)*C + m*C
              <=>  m*(C - r) + B(a,nl) >= 0,   B(a,nl) := (a+nl+1)*C - (4a/3+2nl+1).
Since m>=0, it suffices to show  C >= r  AND  B(a,nl) >= 0.  Then m*(C-r)>=0 and B>=0 give the sum >=0.

STEP 1:  C >= r.   C/r = r^nl * (r^2 * 2/3)^a.  Now r^2*(2/3) >= 1  <=>  (621/64)^2 >= (3/2)^11  <=>
    621^2 * 2^11 >= 3^11 * 64^2, i.e. 789792768 >= 725594112 (TRUE, exact integers).  With r^nl>=1 and the
    base >=1, C/r>=1 for all a>=0, nl in {0,1}.  So C-r>=0 (equality only at a=0,nl=0).

STEP 2:  B(a,1) >= 0  (elementary, NO tie).   P1(a):=(a+2)*C = (a+2)*r^(2+2a)*(2/3)^a = (a+2)*r^2*rho^a,
    rho:=r^2*(2/3)>=1 (Step 1).  Hence P1(a) >= (a+2)*r^2 >= (a+2)*(3/2)  [since r^2>=3/2, same integer ineq
    as Step 1] = 3a/2+3 >= 4a/3+3 = Q1(a)  [since 3/2 > 4/3].  So B(a,1)=P1(a)-Q1(a) >= 0.

STEP 3:  B(a,0) >= 0.   This is EXACTLY the near-star bound g(a)<=0: B(a,0)=(a+1)*r^(1+2a)*(2/3)^a -
    (4a/3+1) >= 0  <=>  logPhi(N(0,a))=g(a)<=0, PROVEN in near_star_arithmetic_proof (R(s) unimodal, tie
    at a=5 where B(5,0)=0 exactly: 6*(621/64)*(2/3)^5 = 23/3).

CONCLUSION.  C-r>=0 (Step 1) and B(a,nl)>=0 (Steps 2,3), so m*(C-r)+B(a,nl)>=0 for all m>=0, i.e.
chi(T0)<=0.  LEMMA A PROVED.  (Note: only B(a,0), the near-star case, is delicate/has a tie; the
m-dependence and the nl=1 case are elementary.)  This closes the last analytic gap of
proof_via_explicit_potential (m>=3 branch of the crux); m in {1,2} remain finite-verified.
conjecture1_proved stays False pending the Lean port + independent review.
"""
from __future__ import annotations

import math
from fractions import Fraction as F

L = math.log(621 / 64) / 11
OMEGA = math.log(3 / 2) - 2 * L
r = (621 / 64) ** (1 / 11)
T0 = r - 1


def chiT0(a, nl, m):
    k = a + nl + m; S = a / 3 + nl + m * T0; w = k + 1
    return -L + math.log(1 + S / w) + a * OMEGA + nl * (-L)


def C(a, nl):
    return r ** (1 + nl + 2 * a) * (2 / 3) ** a


def B(a, nl):
    return (a + nl + 1) * C(a, nl) - (4 * a / 3 + 2 * nl + 1)


def verify() -> dict:
    import random
    random.seed(0)
    # (0) reduction exact: chi(T0)<=0 iff m*(C-r)+B>=0
    reduction_ok = True
    for _ in range(5000):
        a = random.randint(0, 40); nl = random.randint(0, 1); m = random.randint(0, 250)
        if (chiT0(a, nl, m) <= 1e-12) != (m * (C(a, nl) - r) + B(a, nl) >= -1e-9):
            reduction_ok = False
    # (1) C>=r  <=>  r^2*(2/3)>=1  <=>  621^2*2^11 >= 3^11*64^2 (exact)
    step1_int = (621 ** 2 * 2 ** 11, 3 ** 11 * 64 ** 2)
    step1 = step1_int[0] >= step1_int[1]
    # (2) B(a,1)>=0 chain: (a+2)(3/2) >= 4a/3+3 for all a>=0 (elementary, 3/2>4/3); + numeric small-a
    step2_chain = all((a + 2) * F(3, 2) >= F(4, 3) * a + 3 for a in range(0, 500))
    step2_num = all(B(a, 1) >= -1e-12 for a in range(0, 400))  # float ok for a<400
    # (3) B(a,0)>=0 = near-star; exact tie at a=5
    tie5 = (6 * F(621, 64) * F(2, 3) ** 5 == F(23, 3))  # P0(5)==Q0(5)
    step3_num = all(B(a, 0) >= -1e-9 for a in range(0, 400))
    return {
        "reduction_chiT0_le0_iff_m(C-r)+B_ge0": reduction_ok,
        "step1_C_ge_r_exact_int": {"621^2*2^11": step1_int[0], "3^11*64^2": step1_int[1], "holds": step1},
        "step2_B_a1_ge0_elementary_chain": step2_chain and step2_num,
        "step3_B_a0_ge0_nearstar_tie_at_5_exact": tie5 and step3_num,
        "lemma_A_proved": reduction_ok and step1 and step2_chain and step2_num and tie5 and step3_num,
        "conjecture1_proved": False,
        "statement": (
            "LEMMA A (chi(y=T0)<=0) PROVED symbolically: chi(T0)<=0 <=> m*(C-r)+B(a,nl)>=0, C=r^(1+nl+2a)"
            "(2/3)^a. Step1 C>=r <=> 621^2*2^11>=3^11*64^2 (789792768>=725594112, exact). Step2 B(a,1)>=0 "
            "elementary: (a+2)C=(a+2)r^2 rho^a >= (a+2)r^2 >= (a+2)(3/2) >= 4a/3+3 (r^2>=3/2, 3/2>4/3). "
            "Step3 B(a,0)>=0 = near-star g(a)<=0 (proven, tie a=5: 6*(621/64)*(2/3)^5=23/3). => "
            "m*(C-r)+B>=0 for all m>=0. Closes the last analytic gap of the candidate proof "
            "(m>=3 branch). conjecture1_proved=False pending Lean port + independent review."
        ),
    }


if __name__ == "__main__":
    import json
    res = verify()
    print(json.dumps(res, indent=2, default=str))
    assert res["reduction_chiT0_le0_iff_m(C-r)+B_ge0"]
    assert res["step1_C_ge_r_exact_int"]["holds"]
    assert res["step2_B_a1_ge0_elementary_chain"]
    assert res["step3_B_a0_ge0_nearstar_tie_at_5_exact"]
    assert res["lemma_A_proved"]
    assert not res["conjecture1_proved"]
    print("\nAll assertions pass. LEMMA A proved symbolically (reduction + C>=r + B(a,1) elementary + "
          "B(a,0)=near-star). conjecture1_proved=False (pending Lean + review).")
