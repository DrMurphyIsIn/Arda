"""Floating-point sanity checks of the kernel-checked scattering statements (and of the DH
rational-face slices quoted in the idea).

conjecture1_proved = False.  Trust class: mpmath floating point (50 digits); these are sanity
checks and illustrations, NOT certificates.  The theorems themselves are kernel-checked in
telperion/examples/li_positivity/lean/Crux/Crux_dynamics_ergodic.lean.

(a) xi_inner: |xi(2s-1)| <= |xi(2s)| on Re s >= 1/2, equality on Re s = 1/2 (random sample).
(b) modScat_eq: the true scattering matrix phi = Lambda(2s-1)/Lambda(2s) exceeds 1 near s = 1
    (residual pole), while phi_xi = phi (s-1)/s stays <= 1.
(c) bk_phase_identity and bk_of_inner: logDeriv phi_xi(1/2 + it) = -4 Re xi'/xi(1 + 2it) <= 0.
(d) channelAxioms_fakeXi: the fake xi * Q_{rho0}, rho0 = 3/4 + 20i, is contractive on the sample.
(e) finite_euler_blowup_on_axis: |prod_{p in {2,3,5}} c_p(1/2 + it)| as t -> 0.
(f) DH rational face: min_t Re Lambda_DH'/Lambda_DH(sigma + it), t in [1, TMAX], for several sigma.
Output: scattering_checks_output.json
"""
from __future__ import annotations

import json
import random

import mpmath as mp

mp.mp.dps = 50
random.seed(20260923)


def xi(s):
    return s * (s - 1) / 2 * mp.pi ** (-s / 2) * mp.gamma(s / 2) * mp.zeta(s)


def Lam(s):
    return mp.pi ** (-s / 2) * mp.gamma(s / 2) * mp.zeta(s)


def quad(rho, w):
    c = mp.conj(rho)
    return (w - rho) * (w - c) * (w - (1 - rho)) * (w - (1 - c))


def main():
    out = {"conjecture1_proved": False, "trust_class": "mpmath floats (50 digits), not a certificate"}
    # (a)
    worst, eqdev = mp.mpf(-10), mp.mpf(0)
    for _ in range(400):
        s = mp.mpc(0.5 + 1.5 * random.random() ** 2, 60 * (2 * random.random() - 1))
        r = abs(xi(2 * s - 1)) / abs(xi(2 * s))
        worst = max(worst, r)
        s0 = mp.mpc(0.5, 60 * (2 * random.random() - 1))
        eqdev = max(eqdev, abs(abs(xi(2 * s0 - 1)) / abs(xi(2 * s0)) - 1))
    out["a_max_|phi_xi|_on_sample_Re_s_ge_half"] = mp.nstr(worst, 12)
    out["a_max_||phi_xi|-1|_on_axis_sample"] = mp.nstr(eqdev, 5)
    # (b)
    rows = []
    for x in ["1.001", "1.01", "1.1", "1.5", "3"]:
        s = mp.mpf(x)
        phi = Lam(2 * s - 1) / Lam(2 * s)
        rows.append({"s": x, "|phi|": mp.nstr(abs(phi), 10), "|phi_xi|": mp.nstr(abs(phi * (s - 1) / s), 10)})
    out["b_true_scattering_matrix_vs_phi_xi"] = rows
    # (c)
    rows = []
    for t in [0.3, 1.0, 3.7, 7.05, 14.0, 25.5]:
        s = mp.mpc(0.5, t)
        f = lambda z: xi(2 * z - 1) / xi(2 * z)
        ld = mp.diff(f, s) / f(s)
        a = mp.mpc(1, 2 * t)
        lx = mp.diff(xi, a) / xi(a)
        rows.append({"t": t, "logDeriv_phi_xi": mp.nstr(ld, 12), "-4 Re xi'/xi(1+2it)": mp.nstr(-4 * mp.re(lx), 12)})
    out["c_phase_identity"] = rows
    # (d)
    rho0 = mp.mpc(0.75, 20)
    worst = mp.mpf(-10)
    for _ in range(300):
        s = mp.mpc(0.5 + 1.5 * random.random() ** 2, 40 * (2 * random.random() - 1))
        r = abs(xi(2 * s - 1) * quad(rho0, 2 * s - 1)) / abs(xi(2 * s) * quad(rho0, 2 * s))
        worst = max(worst, r)
    out["d_max_|phi_fake|_on_sample"] = mp.nstr(worst, 12)
    out["d_fake_value_at_rho0"] = mp.nstr(abs(xi(rho0) * quad(rho0, rho0)), 5)
    # (e)
    rows = []
    for t in ["0.3", "0.1", "0.03", "0.01", "0.001"]:
        s = mp.mpc(0.5, mp.mpf(t))
        c = mp.mpf(1)
        for p in [2, 3, 5]:
            c *= (1 - mp.mpf(p) ** (-2 * s)) / (1 - mp.mpf(p) ** (1 - 2 * s))
        rows.append({"t": t, "|c_{2,3,5}(1/2+it)|": mp.nstr(abs(c), 8)})
    out["e_finite_euler_product_on_axis"] = rows
    # (f) Davenport-Heilbronn completed function: Lambda_DH(s) = (5/pi)^{s/2} Gamma((s+1)/2) D(s)
    kappa = (mp.sqrt(10 - 2 * mp.sqrt(5)) - 2) / (mp.sqrt(5) - 1)

    def D(s):
        return mp.mpf(5) ** (-s) * (mp.zeta(s, mp.mpf(1) / 5) + kappa * mp.zeta(s, mp.mpf(2) / 5)
                                    - kappa * mp.zeta(s, mp.mpf(3) / 5) - mp.zeta(s, mp.mpf(4) / 5))

    def Dp(s):
        return (-mp.log(5) * D(s) + mp.mpf(5) ** (-s) * (
            mp.zeta(s, mp.mpf(1) / 5, 1) + kappa * mp.zeta(s, mp.mpf(2) / 5, 1)
            - kappa * mp.zeta(s, mp.mpf(3) / 5, 1) - mp.zeta(s, mp.mpf(4) / 5, 1)))

    def reLD(s):
        return mp.re(mp.log(5 / mp.pi) / 2 + mp.digamma((s + 1) / 2) / 2 + Dp(s) / D(s))

    mp.mp.dps = 20
    TMAX, step = 200.0, 0.25
    rows = []
    for sig in [1.0, 0.9, 0.82, 0.8]:
        mn, tmn, firstneg = None, None, None
        t = 1.0
        while t <= TMAX:
            v = reLD(mp.mpc(sig, t))
            if mn is None or v < mn:
                mn, tmn = v, t
            if firstneg is None and v < 0:
                firstneg = t
            t += step
        rows.append({"sigma": sig, "min_Re_LambdaDH'/LambdaDH_on_[1,%g]" % TMAX: mp.nstr(mn, 6),
                     "argmin_t": tmn, "first_t_with_negative_value": firstneg})
        print(rows[-1], flush=True)
    out["f_DH_rational_face_slices_step_%g" % step] = rows
    print(json.dumps(out, indent=1))
    with open("scattering_checks_output.json", "w") as fh:
        json.dump(out, fh, indent=2)


if __name__ == "__main__":
    main()
