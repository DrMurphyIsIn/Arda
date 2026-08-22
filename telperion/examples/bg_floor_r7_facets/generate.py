"""Generate the remaining BG R7 ledger-floor facets: m=0, m>=4, and tax windows.

    python examples/bg_floor_r7_facets/generate.py           # write lean/BGFloorR7Facets.lean
    python examples/bg_floor_r7_facets/generate.py --check    # drift check (no write)

Completes the context-free floor layer beyond the y-interval families
(examples/bg_floor, examples/bg_floor_families) with the three remaining facets:

  * m=0 (childless): slack has no cavity y -- a POINT value
        slack = p*L - a*log(3/2) - log(1+u0),  u0 = (a/3+nl)/(k+1),  k=a+nl
    >= class floor.  Emitted as a `norm_num` rational inequality (bare-leaf nl=1
    a in 1..9 floor 26/500; nl=2 a in 0..6 floor 54/500; tax shape (1,1,0) floor 52/1000).

  * m>=4 (collapse tail): the collapse monotonicity (R3Cert.R7CollapseMono.g_mono,
    the kernel session's brick) puts the min at y=T0, and u is monotone in m toward
    T0, so a single m-UNIFORM point bound
        slack >= p*L_LO - a*G_HI - log1p_upper(u_env),  u_env = max(u(4,T_HI), T_HI)
    >= floor covers all m>=4.  Emitted as `norm_num` (mixed a in 1..6 floor 27/5000;
    bare-leaf a in 0..9 floor 26/500; nl=2 a in 0..6 floor 54/500).

  * tax windows (amortized-hub tax lemma): six in-window floors >= their targets on
    the y-subrange where the cavity meets the window [T0-29/1000, T0+29/1000], plus
    the below-window m in {2,3} shapes >= 24/500.  These are the TIGHT binding floors
    (the (2,0,1) shape clears by ~5e-5), so they use a degree-9 log bound and the
    exact cav = 1/(k+1+S) with hinge splits at y=T0 (T_LO/T_HI) and cav=T0 (a bracketed
    y-threshold) -- Bernstein positivity per cell.

All transcendentals are bracketed by the BG kernel's verified rationals
(g1_floor_certificates: L>=L_LO, log(3/2)<=G_HI, log(1+u)<=truncated series, T0 in
[T_LO,T_HI]), so the emitted `slack_lb >= floor` implies `slack >= floor`.
conjecture1_proved = False.
"""
import argparse
import sys
from fractions import Fraction as Fr
from pathlib import Path

import sympy as sp

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "src"))
sys.path.insert(0, str(Path(__file__).resolve().parents[2].parent / "proof" / "verification"))

import g1_floor_certificates as _G  # noqa: E402  (kernel: log1p_upper, verified constants)
from telperion import BernsteinEmitter, ValidationReport, certify, emit  # noqa: E402
from telperion.emit_bernstein import bernstein_family  # noqa: E402
from telperion.family import GridSpec  # noqa: E402
from telperion.lean import LeanProfile  # noqa: E402

_OUT = Path(__file__).resolve().parent / "lean" / "BGFloorR7Facets.lean"

_L_LO = sp.Rational(_G.L_LO.numerator, _G.L_LO.denominator)
_G_HI = sp.Rational(_G.G_HI.numerator, _G.G_HI.denominator)
_T_LO = sp.Rational(_G.T_LO.numerator, _G.T_LO.denominator)
_T_HI = sp.Rational(_G.T_HI.numerator, _G.T_HI.denominator)
_C = sp.Rational(11, 50)
_HALF = sp.Rational(1, 2)
_EPS = sp.Rational(29, 1000)
_Y = sp.Symbol("y")


def _rat(fr):
    return sp.Rational(fr.numerator, fr.denominator)


# ---- point facts (m=0 childless, and m>=4 collapse tail) ----------------------
def _point_facts():
    """(name, structured Lean expr string >= 0, exact value for the self-check, comment)."""
    facts = []
    def render(p, a, l, fl):
        # slack_lb - floor = p*L_LO - a*G_HI - log1p_upper - floor, all rationals shown.
        return (f"({p} : ℝ) * (206586 / 1000000) - ({a} : ℝ) * (405466 / 1000000)"
                f" - ({l.numerator} / {l.denominator}) - ({fl.numerator} / {fl.denominator})")
    # m=0 childless
    m0 = [(a, 1, Fr(26, 500)) for a in range(1, 10)] \
        + [(a, 2, Fr(54, 500)) for a in range(0, 7)] \
        + [(1, 1, Fr(52, 1000))]                              # tax shape (1,1,0)
    for a, nl, fl in m0:
        k = a + nl
        u0 = (Fr(a, 3) + nl) / (k + 1)
        p = 1 + 2 * a + nl
        l = _G.log1p_upper(u0)
        val = p * _G.L_LO - a * _G.G_HI - l - fl
        facts.append((f"bg_floor_m0_a{a}_nl{nl}", render(p, a, l, fl), val,
                      f"m=0 (a={a},nl={nl}): p*L_LO - a*G_HI - log1p_upper({u0}) - {fl} >= 0"))
    # m>=4 collapse tail (m-uniform; min at y=T0 via R3Cert.R7CollapseMono.g_mono)
    m4 = [(a, 0, Fr(27, 5000)) for a in range(1, 7)] \
        + [(a, 1, Fr(26, 500)) for a in range(0, 10)] \
        + [(a, 2, Fr(54, 500)) for a in range(0, 7)]
    for a, nl, fl in m4:
        p = 1 + 2 * a + nl
        u_env = max((Fr(a, 3) + nl + 4 * _G.T_HI) / (a + nl + 4 + 1), _G.T_HI)
        l = _G.log1p_upper(u_env)
        val = p * _G.L_LO - a * _G.G_HI - l - fl
        facts.append((f"bg_floor_mge4_a{a}_nl{nl}", render(p, a, l, fl), val,
                      f"m>=4 collapse (a={a},nl={nl}): min at y=T0 (g_mono), u_env-uniform - {fl} >= 0"))
    return facts


# ---- tax / below-window Bernstein cells --------------------------------------
def _log9(u):
    return sum(((-1) ** (i + 1)) * u ** i / i for i in range(1, 10))  # deg-9 upper bound


def _window_cells(a, nl, m, ylo, yhi, floor):
    k = a + nl + m
    p = 1 + 2 * a + nl
    S = sp.Rational(a, 3) + nl + m * _Y
    u = S / (k + 1)
    cav = 1 / (k + 1 + S)
    log_ub = _log9(u)
    ythr = (sp.Integer(1) / _T_LO - (k + 1) - sp.Rational(a, 3) - nl) / m   # cav = T_LO
    bnds = sorted(set([ylo, yhi] + [t for t in (_T_LO, _T_HI, ythr) if ylo < t < yhi]))
    cells = []
    for i in range(len(bnds) - 1):
        lo, hi = bnds[i], bnds[i + 1]
        mid = (lo + hi) / 2
        cavub = (cav - _T_LO) if mid < ythr else sp.Integer(0)   # (cav-T0)_+ <= cav-T_LO if cav>=T_LO else 0
        yhelp = m * (_Y - _T_HI) if mid > _T_HI else sp.Integer(0)  # (y-T0)_+ >= y-T_HI if y>=T_HI else >=0
        expr = p * _L_LO - a * _G_HI - log_ub - _C * (cavub - yhelp)
        num = sp.expand(sp.fraction(sp.together(expr - _rat(floor)))[0])
        cells.append((num, lo, hi))
    return cells


def _window_specs():
    out = []  # (name, num, lo, hi)
    def yr(a, nl, m):
        k = a + nl + m
        ls, hs = Fr(1) / (_G.T_HI + _EPS), Fr(1) / (_G.T_LO - _EPS)
        ylo = max(Fr(1, 10**6), (ls - (k + 1) - Fr(a, 3) - nl) / m)
        yhi = min(Fr(1, 2), (hs - (k + 1) - Fr(a, 3) - nl) / m)
        return _rat(ylo), _rat(yhi)
    tax = [((0, 0, 2), Fr(33, 1000)), ((0, 0, 3), Fr(47, 1000)), ((0, 1, 1), Fr(66, 1000)),
           ((1, 0, 2), Fr(33, 1000)), ((2, 0, 1), Fr(99, 5000))]
    for (a, nl, m), fl in tax:
        ylo, yhi = yr(a, nl, m)
        for j, (num, lo, hi) in enumerate(_window_cells(a, nl, m, ylo, yhi, fl)):
            out.append((f"bg_floor_taxwin_a{a}_nl{nl}_m{m}_c{j}", num, lo, hi))
    # below-window (0,0,m) m in {2,3}, floor 24/500 on [1e-6, T_LO-EPS]
    for m in (2, 3):
        lo, hi = sp.Rational(1, 10**6), _T_LO - _EPS
        for j, (num, l, h) in enumerate(_window_cells(0, 0, m, lo, hi, Fr(24, 500))):
            out.append((f"bg_floor_belowwin_m{m}_c{j}", num, l, h))
    return out


def build() -> str:
    # tax/below-window Bernstein theorems via the emitter
    cells = _window_specs()
    names = {i: c[0] for i, c in enumerate(cells)}
    specs = {i: (c[1], c[2], c[3]) for i, c in enumerate(cells)}
    fam = bernstein_family(
        "BGFloorR7Facets", (_Y,), GridSpec([("cell", list(range(len(cells))))]),
        lambda pt: names[pt["cell"]], spec=lambda pt: specs[pt["cell"]], n_max=18,
    )
    report = emit(certify(fam), LeanProfile(namespace=("BGFloorR7Facets",)),
                  [BernsteinEmitter()], ValidationReport(checks=(("bernstein", True),)))
    text = next(iter(report.files.values()))
    for nm in names.values():
        text = text.replace(f"theorem {nm}", f"set_option maxHeartbeats 8000000 in\ntheorem {nm}")
    # point facts (norm_num) appended before the closing `end`
    lines = []
    for name, expr_s, val, comment in _point_facts():
        assert val >= 0, (name, val)
        lines.append(f"-- {comment}\ntheorem {name} : (0:ℝ) ≤ {expr_s} := by norm_num\n")
    end = "\nend BGFloorR7Facets\n"
    body = "\n".join(lines)
    if text.rstrip().endswith("end BGFloorR7Facets"):
        text = text.rstrip()[: -len("end BGFloorR7Facets")].rstrip() + "\n\n" + body + end
    else:
        text = text.rstrip() + "\n\n" + body + end
    return text


def main(*, check: bool = False) -> int:
    text = build()
    if check:
        if not _OUT.exists() or _OUT.read_text(encoding="utf-8") != text:
            print("DRIFT: BGFloorR7Facets.lean does not match regeneration")
            return 1
        print("check: OK (regeneration matches frozen output byte-for-byte)")
        return 0
    _OUT.parent.mkdir(exist_ok=True)
    _OUT.write_text(text, encoding="utf-8")
    print(f"wrote {_OUT} ({len(text)} bytes)")
    return 0


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("--check", action="store_true", help="drift check; do not write")
    raise SystemExit(main(check=ap.parse_args().check))
