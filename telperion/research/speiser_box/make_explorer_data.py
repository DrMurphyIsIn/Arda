#!/usr/bin/env python3
"""Float-model data for the Explorer's "The zeta' box" tab (MM_speiser_box_probe).

    python research/speiser_box/make_explorer_data.py           # rewrite explorer_data.json
    python research/speiser_box/make_explorer_data.py --check   # exit 1 if the committed file is stale

Two halves, kept apart on purpose.

  * EXACT.  The model polynomial M of every disc, its derivative test and its error budget, taken
    from the generator `examples/zeta_reflection/arbecon/gen_speiser_box.py` by importing it and
    running its own `build()` (the same Fractions the kernel re-checks with `decide +kernel`), never
    retyped.  `exact_data()` is pure rational arithmetic and runs in well under a second; the
    explorer's build.py recomputes it and refuses to run if this file disagrees with the generator.

  * FLOAT.  mpmath at a fixed precision, on fixed grids, no randomness: log10 |zeta'(s)| and
    log10 |zeta(s)| over Re s in [-1/4, 11/4], Im s in [0, 30]; the zero of zeta' below height 30;
    and, per disc, |zeta(z) - M(z - c)| on a polar grid of the outer disc.  Every number here is a
    FLOAT MODEL for pictures, not a certificate: the certificate is the kernel check, whose exact
    numbers sit in the other half.

The output is rounded (two decimals of a log10, or six significant digits) so it is small and
stable across mpmath versions.  conjecture1_proved = False.
"""
from __future__ import annotations

import json
import math
import sys
from fractions import Fraction as Fr
from pathlib import Path

HERE = Path(__file__).resolve().parent                       # telperion/research/speiser_box
TELPERION = HERE.parent.parent                                # telperion
ARBECON = TELPERION / "examples" / "zeta_reflection" / "arbecon"
OUT = HERE / "explorer_data.json"
sys.path.insert(0, str(ARBECON))

import gen_speiser_box as G  # noqa: E402  (the generator: parameters, GQ arithmetic, build())

# ---------------------------------------------------------------------------- grids
RE0, RE1, RE_STEP = Fr(-1, 4), Fr(11, 4), Fr(1, 32)         # 97 columns
IM0, IM1, IM_STEP = Fr(0), Fr(30), Fr(1, 8)                  # 241 rows
LOG_SCALE = 100                                              # stored value = round(100 * log10 |.|)
LOG_CLIP = 400                                               # |log10| clipped at 4 (the pole at s = 1)
N_RAD, N_ANG = 10, 60                                        # polar grid of each outer disc
ERR_CLIP = 1200                                              # the disc error grid reaches 1e-12
DPS = 20


def frs(x: Fr) -> str:
    x = Fr(x)
    return "%d/%d" % (x.numerator, x.denominator) if x.denominator != 1 else "%d" % x.numerator


def gq_str(a) -> list:
    return [frs(a[0]), frs(a[1])]


def gq_float(a) -> list:
    return [float(a[0]), float(a[1])]


# ---------------------------------------------------------------------------- exact half
def exact_data() -> dict:
    """Everything the kernel sees, as the generator computes it (Fractions), plus float views."""
    cells, Qr, ER, Bmax, accbad = G.build()
    discs = []
    for cl in cells:
        cQ = (G.SIG, cl["tc"])
        xs1, xs2 = list(cl["s1"].acc), list(cl["sN"].acc)
        M = G.modelPoly(64, cQ, G.N, G.K, G.J, xs1, xs2)
        D = G.pderiv(M)
        d0, Dt = D[0], D[1:]
        r_pnub = G.R_ * G.pnub(G.R_, Dt)
        abs_d0 = math.sqrt(float(G.nsq(d0)))
        ok, bud, margin = G.checkD(64, cQ, G.N, G.K, G.p, G.J, xs1, xs2, cl["sN"].lhi, G.R_, G.RHO, G.F, ER)
        bad, _, _ = G.checkD(64, cQ, G.N, G.K, G.p, G.J, xs1, xs2, cl["sN"].lhi, G.R_, G.RHO, Fr(1, 10 ** 9), ER)
        assert ok and not bad
        discs.append({
            "i": cl["i"],
            "tc": frs(cl["tc"]),
            "tc_float": float(cl["tc"]),
            "M_exact": [gq_str(a) for a in M],
            "M_float": [gq_float(a) for a in M],
            "abs_Mp0": abs_d0,
            "r_pnub": float(r_pnub),
            "deriv_bound": float(r_pnub + G.F),
            "margin": abs_d0 - float(r_pnub + G.F),
            "budget_exact": frs(bud),
            "budget_float": float(bud),
            "checkD": bool(ok),
            "checkD_F_tiny": bool(bad),
        })
    # the forged accumulator control on disc 0 (the generator's accbad)
    c0 = cells[0]
    cQ0 = (G.SIG, c0["tc"])
    Mbad = G.modelPoly(64, cQ0, G.N, G.K, G.J, list(c0["s1"].acc), accbad)
    Dbad = G.pderiv(Mbad)
    badok, badbud, _ = G.checkD(64, cQ0, G.N, G.K, G.p, G.J, list(c0["s1"].acc), accbad, c0["sN"].lhi,
                                G.R_, G.RHO, G.F, ER)
    assert not badok
    forged = {
        "disc": 0,
        "M_float": [gq_float(a) for a in Mbad],
        "abs_Mp0": math.sqrt(float(G.nsq(Dbad[0]))),
        "r_pnub": float(G.R_ * G.pnub(G.R_, Dbad[1:])),
        "deriv_bound": float(G.R_ * G.pnub(G.R_, Dbad[1:]) + G.F),
        "budget_float": float(badbud),
        "checkD": bool(badok),
        "what": "disc 0's k = 1 accumulator after N terms shifted by M'(0)/gamma_0, which cancels M'(0); "
                "the budget still passes, the derivative test fails",
    }
    half_diag = math.sqrt(17) / 16
    return {
        "params": {
            "N": G.N, "K": G.K, "p": G.p, "J": G.J,
            "sigma": frs(G.SIG), "sigma_float": float(G.SIG),
            "r": frs(G.R_), "r_float": float(G.R_),
            "rho": frs(G.RHO), "rho_float": float(G.RHO),
            "F": frs(G.F), "F_float": float(G.F),
            "F_rho": frs(G.F * G.RHO), "F_rho_float": float(G.F * G.RHO),
            "F_tiny": "1/1000000000", "F_tiny_rho_float": float(Fr(1, 10 ** 9) * G.RHO),
            "ER": frs(ER), "ER_float": float(ER), "Qr": frs(Qr),
            "box": {"re0": "1/4", "re1": "3/8", "im0": "6", "im1": "10"},
            "row_half_diagonal": half_diag,
            "row_half_diagonal_formula": "sqrt(17)/16",
            "degree_M": len(discs[0]["M_exact"]) - 1,
        },
        "discs": discs,
        "forged_disc0": forged,
    }


# ---------------------------------------------------------------------------- float half
def float_data(exact: dict) -> dict:
    import mpmath as mp
    mp.mp.dps = DPS

    def log_int(v, clip=LOG_CLIP) -> int:
        if v == 0 or not mp.isfinite(v):
            return -clip if v == 0 else clip
        x = float(mp.log10(abs(v)))
        return max(-clip, min(clip, int(round(LOG_SCALE * x))))

    ncols = int((RE1 - RE0) / RE_STEP) + 1
    nrows = int((IM1 - IM0) / IM_STEP) + 1
    lz, ldz = [], []
    for j in range(nrows):
        t = IM0 + j * IM_STEP
        for i in range(ncols):
            x = RE0 + i * RE_STEP
            s = mp.mpc(mp.mpf(x.numerator) / x.denominator, mp.mpf(t.numerator) / t.denominator)
            if s == 1:                      # the pole
                lz.append(LOG_CLIP); ldz.append(LOG_CLIP); continue
            lz.append(log_int(mp.zeta(s)))
            ldz.append(log_int(mp.zeta(s, derivative=1)))

    # the zero of zeta' below height 30 (a grid of Newton starts, deduplicated)
    def dz(s):
        return mp.zeta(s, derivative=1)
    found = []
    for a in range(-2, 8):
        for b in range(0, 31):
            try:
                z = mp.findroot(dz, mp.mpc(a / 2 + 0.25, b + 0.5), tol=1e-18, maxsteps=40)
            except (ValueError, ZeroDivisionError):
                continue
            if -1 <= z.real <= 4 and 0 <= z.imag <= 30 and abs(dz(z)) < 1e-12:
                if not any(abs(z - f) < 1e-6 for f in found):
                    found.append(z)
    found.sort(key=lambda z: (float(z.imag), float(z.real)))
    dz_zeros = [{"re": float(mp.nstr(z.real, 12)), "im": float(mp.nstr(z.imag, 12))} for z in found]

    # per disc: |zeta(z) - M(z - c)| on a polar grid of the outer disc, M from the exact coefficients
    P = exact["params"]
    R = Fr(P["r"]) + Fr(P["rho"])
    sigma = Fr(P["sigma"])

    def mpq(q: str):
        f = Fr(q)
        return mp.mpf(f.numerator) / f.denominator

    discs = []
    for d in exact["discs"]:
        coef = [mp.mpc(mpq(a[0]), mpq(a[1])) for a in d["M_exact"]]
        c = mp.mpc(mpq(P["sigma"]), mpq(d["tc"]))

        def M_at(h):
            acc = mp.mpc(0)
            for a in reversed(coef):
                acc = a + h * acc
            return acc
        rows = []
        bmax = 0.0
        for k in range(1, N_RAD + 1):
            rad = mp.mpf(R.numerator) / R.denominator * k / N_RAD
            for m in range(N_ANG):
                h = rad * mp.expjpi(2 * mp.mpf(m) / N_ANG)
                err = abs(mp.zeta(c + h) - M_at(h))
                rows.append(log_int(err, ERR_CLIP))
                if k == N_RAD:
                    bmax = max(bmax, float(err))
        err0 = abs(mp.zeta(c) - M_at(0))
        # float min of |zeta'| and of |M'| over a Cartesian sample of the inner disc
        r = Fr(P["r"])
        rf = mp.mpf(r.numerator) / r.denominator
        dcoef = [coef[k] * k for k in range(1, len(coef))]

        def Mp_at(h):
            acc = mp.mpc(0)
            for a in reversed(dcoef):
                acc = a + h * acc
            return acc
        mins_dz, mins_mp = None, None
        G_ = 24
        for a in range(-G_, G_ + 1):
            for b in range(-G_, G_ + 1):
                h = mp.mpc(rf * a / G_, rf * b / G_)
                if abs(h) > rf:
                    continue
                v1, v2 = abs(mp.zeta(c + h, derivative=1)), abs(Mp_at(h))
                mins_dz = v1 if mins_dz is None else min(mins_dz, v1)
                mins_mp = v2 if mins_mp is None else min(mins_mp, v2)
        discs.append({
            "i": d["i"],
            "nrad": N_RAD, "nang": N_ANG,
            "centre_log10_err": log_int(err0, ERR_CLIP),
            "err_clip": ERR_CLIP,
            "log10_err": rows,
            "boundary_max_err": float("%.6g" % bmax),
            "inner_min_abs_dzeta": float("%.6g" % mins_dz),
            "inner_min_abs_Mp": float("%.6g" % mins_mp),
            "dzeta_at_centre": [float("%.10g" % mp.zeta(c, derivative=1).real),
                                float("%.10g" % mp.zeta(c, derivative=1).imag)],
        })
    return {
        "trust": "float model (mpmath, %d digits), not a certificate; the certificate is the kernel check "
                 "in SpeiserDerivBox.lean, whose exact numbers are in the `exact` half" % DPS,
        "grid": {
            "re0": float(RE0), "re1": float(RE1), "ncols": ncols,
            "im0": float(IM0), "im1": float(IM1), "nrows": nrows,
            "scale": LOG_SCALE, "clip": LOG_CLIP,
            "log10_abs_dzeta": ldz, "log10_abs_zeta": lz,
            "note": "row-major, Im outer / Re inner; value = round(100 log10 |.|), clipped at +-400; "
                    "the pole s = 1 is stored as +400",
        },
        "dzeta_zeros": dz_zeros,
        "dzeta_zeros_note": "every zero of zeta' with 0 <= Im <= 30 and -1 <= Re <= 4 that mpmath's Newton "
                            "iteration found from a half-unit grid of starts (float model; the literature "
                            "value is 2.46316 + 23.29832 i)",
        "discs": discs,
    }


def build() -> str:
    exact = exact_data()
    data = {
        "conjecture1_proved": False,
        "note": "conjecture1_proved = False. NOT the Speiser wall: Speiser (1935) makes zeta' zero-free on the "
                "whole open strip 0 < Re s < 1/2 equivalent to RH; one box decides nothing, and this theorem "
                "says nothing about zeros of zeta. The `exact` half is the generator's own arithmetic; the "
                "`float` half is an mpmath picture.",
        "source_generator": "telperion/examples/zeta_reflection/arbecon/gen_speiser_box.py",
        "source_lean": "telperion/examples/zeta_reflection/lean/SpeiserDerivBox.lean",
        "exact": exact,
        "float": float_data(exact),
    }
    return json.dumps(data, separators=(",", ":"), sort_keys=True) + "\n"


def main(argv=None) -> int:
    argv = sys.argv[1:] if argv is None else argv
    text = build()
    if "--check" in argv:
        cur = OUT.read_text(encoding="utf-8") if OUT.is_file() else ""
        if cur != text:
            print("STALE: %s differs from a fresh run" % OUT)
            return 1
        print("explorer data: up to date")
        return 0
    OUT.write_text(text, encoding="utf-8")
    print("wrote %s (%d bytes)" % (OUT.relative_to(TELPERION), len(text.encode("utf-8"))))
    return 0


if __name__ == "__main__":
    sys.exit(main())
