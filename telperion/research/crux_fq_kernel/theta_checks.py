"""Numerical sanity checks for the theta-form statements of Crux/CruxFQ_kernel.lean.

conjecture1_proved = False.  Trust class: COMPUTED (mpmath, 40 digits, single process). These are
cross-checks of kernel theorems and of their hypotheses, not proofs.

(a) Jacobi for the comb: theta(1/t) = sqrt(t) theta(t)                     [kernel: jθ_inv, intComb_theta]
(b) the fooling family nu_{p,c} satisfies the modular relation with beta=0 [kernel: nup_theta]
(c) NEGATIVE: comb + delta_{1/2} + delta_{-1/2} satisfies NO modular relation
    (the defect D(t) = theta(1/t) - sqrt(t) theta(t) is not of the form beta (sqrt t - 1))
(d) the growth bound theta(4^-i) <= 2^i (theta(1) + 2|beta|) for the comb [kernel: mθ_dyadic_le]
(e) r delta_0 + c sum_{n != 0} delta_n has modular relation with beta = c - r (pole footprint)
"""
import json
import os

import mpmath as mp

mp.mp.dps = 40


def theta_comb(u, a=1):
    """sum_{n in Z} exp(-pi u (a n)^2)"""
    return mp.jtheta(3, 0, mp.exp(-mp.pi * u * a * a))


def m_nup(t, p, c):
    sp = mp.sqrt(p)
    p = mp.mpf(p)
    return theta_comb(t, 1 / p) / sp + c * theta_comb(t, 1) + sp * theta_comb(t, p)


def main():
    out = {"conjecture1_proved": False, "trust": "COMPUTED (mpmath 40 digits), not interval-certified"}
    ts = [mp.mpf("0.3"), mp.mpf("1.7"), mp.mpf(5)]
    out["a_jacobi_max_defect"] = mp.nstr(max(abs(theta_comb(1 / t) - mp.sqrt(t) * theta_comb(t)) for t in ts), 3)
    fam = {"W1(29,11/sqrt29)": (29, 11 / mp.sqrt(29)), "golden(5,sqrt5)": (5, mp.sqrt(5)), "(2,2.1)": (2, mp.mpf("2.1"))}
    out["b_nup_theta_max_defect"] = {k: mp.nstr(max(abs(m_nup(1 / t, p, c) - mp.sqrt(t) * m_nup(t, p, c)) for t in ts), 3)
                                    for k, (p, c) in fam.items()}
    # (c) extra atoms at +-1/2
    th = lambda u: theta_comb(u) + 2 * mp.exp(-mp.pi * u / 4)
    ratios = [(th(1 / t) - mp.sqrt(t) * th(t)) / (mp.sqrt(t) - 1) for t in [mp.mpf("0.25"), mp.mpf("0.5"), mp.mpf(2), mp.mpf(4)]]
    out["c_negative_control_defect_over_(sqrt t - 1)"] = [mp.nstr(r, 8) for r in ratios]
    out["c_is_constant"] = bool(max(ratios) - min(ratios) < mp.mpf("1e-20"))
    # (d) growth bound for the comb (beta = 0)
    out["d_growth"] = [{"i": i, "theta(4^-i)": mp.nstr(theta_comb(mp.mpf(4) ** -i), 10),
                        "bound 2^i theta(1)": mp.nstr(2 ** i * theta_comb(1), 10)} for i in range(0, 6)]
    # (e) pole footprint: nu = r delta_0 + c sum_{n!=0} delta_n: theta = r + c (theta_comb - 1)
    r, c = mp.mpf("0.7"), mp.mpf("1.3")
    thp = lambda u: r + c * (theta_comb(u) - 1)
    beta = c - r
    out["e_pole_footprint_max_defect"] = mp.nstr(max(abs(thp(1 / t) - mp.sqrt(t) * thp(t) - beta * (mp.sqrt(t) - 1)) for t in ts), 3)
    return out


if __name__ == "__main__":
    res = main()
    here = os.path.dirname(os.path.abspath(__file__))
    with open(os.path.join(here, "theta_checks.json"), "w") as fh:
        json.dump(res, fh, indent=2)
    print(json.dumps(res, indent=2))
