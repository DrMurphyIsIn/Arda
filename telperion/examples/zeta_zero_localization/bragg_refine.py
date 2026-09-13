"""Bragg amplitude driver (ANDURIL 3, B0/B1 pilot at T = 100).

Emits `BraggH100.lean`: the first kernel-certified truncated Bragg amplitude
`F_100(u*) = sum_{0<gamma_k<=100} cos(gamma_k * u*)` at the rational frequency
`u* = 693147/1000000 ~= log 2`, over the 29 nontrivial zeta zeros up to height 100.

Pipeline (VERIFY-NOT-COMPUTE, same trust boundary as the band `hLine` inputs):

  1. Fetch the 29 Arb-ball zero ordinates via `arb_platt.hardy_z_zeros` (rigorous
     FLINT/Platt ball arithmetic; width ~1e-56 -- already far below the 1e-6 target,
     so no bisection refinement is needed).
  2. Per zero, pin a rational SIGN-CHANGE bracket [a_k, b_k] straddling the ball and
     VERIFY the sign change of gLine = Re Lambda(1/2+it) at a_k, b_k via the same
     `enclose_lambda` sign boxes the band emitter uses (documented Arb non-kernel
     input).  The emitted Lean re-derives each zero by IVT from these signs.
  3. Per zero, certify cos(gamma_k * u*) by the CosEnclosure double-angle chain:
     sample at c_k (the ball's exact lower dyadic endpoint), enclose cos(c_k*u*) via
     M = 30 doublings from an order-4 base bracket, then absorb the bracket width by
     the Lipschitz bound |cos x - cos y| <= |x - y|.
  4. Interval-fold the 29 cos boxes into the amplitude enclosure [A_lo, A_hi].
  5. Emit `BraggH100.lean` with the whole chain as norm_num-checked hypotheses.

The completeness step (that the 29 witnessed ordinates are ALL zeros up to 100 -- the
count is 29 by the winding certificate `AllZeros_h100`) is documented but the emitted
theorem is stated over the 29 CERTIFIED ordinates (the same set `hLine` carries).  See
the module docstring emitted into BraggH100.lean.  conjecture1_proved = False.
"""
from __future__ import annotations

import math
import sys
from fractions import Fraction as F
from pathlib import Path

_HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(_HERE.parent.parent / "src"))

from telperion.arb_platt import hardy_z_zeros  # noqa: E402
from telperion.arb_enclosure import enclose_lambda  # noqa: E402

# --- Bragg parameters --------------------------------------------------------
U_STAR = F(693147, 1000000)          # ~= log 2
T_HEIGHT = 100
N_ZEROS = 29
M_DOUBLE = 30                         # double-angle reduction depth
GRID = F(10) ** 30                    # outward-rounding grid for cos intervals (1e-30)
BRACKET_DEN = 10 ** 6                 # sign-change bracket rational denominator (width ~1e-6)
PREC = 192                            # Arb working precision (bits)


def _rdown(x: F, D: F) -> F:
    return F(math.floor(x * D), 1) / D


def _rup(x: F, D: F) -> F:
    return F(math.ceil(x * D), 1) / D


def cos_chain(theta: F):
    """Return (lo, hi, base, steps) certifying cos(theta) via M_DOUBLE doublings.

    `base = (y, blo, bhi)` is the order-4 base bracket at y = theta / 2^M.
    `steps` is a list of (plo, phi, nlo, nhi, case) -- the input bracket, output
    bracket, and the parabola-branch case flag for each doubling, in order.
    """
    y = theta / F(2) ** M_DOUBLE
    if abs(y) > 1:
        raise ValueError(f"reduced argument y={float(y)} exceeds 1 (raise M)")
    center = 1 - y ** 2 / 2
    rem = y ** 4 * F(5, 96)
    lo = _rdown(center - rem, GRID)
    hi = _rup(center + rem, GRID)
    base = (y, lo, hi)
    steps = []
    for _ in range(M_DOUBLE):
        cands = [2 * lo ** 2 - 1, 2 * hi ** 2 - 1]
        straddle = lo <= 0 <= hi
        if straddle:
            cands.append(F(-1))
        nlo = _rdown(min(cands), GRID)
        nhi = _rup(max(cands), GRID)
        if lo >= 0:
            case = "lo_nonneg"
        elif hi <= 0:
            case = "hi_nonpos"
        else:
            case = "straddle"
        steps.append((lo, hi, nlo, nhi, case))
        lo, hi = nlo, nhi
    return lo, hi, base, steps


def build():
    """Fetch zeros, verify signs, build the full certificate data structure."""
    zs = hardy_z_zeros(1, N_ZEROS, prec=PREC)
    if len(zs) != N_ZEROS:
        raise RuntimeError(f"expected {N_ZEROS} zeros, got {len(zs)}")

    zeros = []
    total_lo = F(0)
    total_hi = F(0)
    for i, (zlo, zhi) in enumerate(zs):
        # --- sign-change bracket [a, b] straddling the Arb ball, width ~1e-6 ---
        a = _rdown(zlo, F(BRACKET_DEN))
        b = _rup(zhi, F(BRACKET_DEN))
        if not (a < zlo and zhi < b):
            # ball wider than the grid step: widen bracket by one grid unit
            a = a - F(1, BRACKET_DEN)
            b = b + F(1, BRACKET_DEN)
        # VERIFY the sign change of gLine = Re Lambda at the bracket endpoints.
        (alo, ahi), _ = enclose_lambda("1/2", str(a), PREC)
        (blo, bhi), _ = enclose_lambda("1/2", str(b), PREC)
        sa = _sign_definite(alo, ahi)
        sb = _sign_definite(blo, bhi)
        if sa == 0 or sb == 0 or sa == sb:
            raise RuntimeError(
                f"zero {i+1}: no certified sign change on [{float(a)},{float(b)}]: "
                f"Re Lambda(a) in [{float(alo)},{float(ahi)}], Re Lambda(b) in [{float(blo)},{float(bhi)}]"
            )
        neg_then_pos = sa < 0  # True: gLine(a)<0<gLine(b); False: gLine(a)>0>gLine(b)

        # --- cos(c*u*) chain at the sample c = exact lower ball endpoint ---
        c = zlo
        theta = c * U_STAR
        clo, chi, base, steps = cos_chain(theta)
        # --- Lipschitz bracket-width absorption ---
        # gamma_k in [a,b] and sample c = zlo in [a,b], so |gamma*u - c*u| <= (b-a)*u.
        w_arg = (b - a) * U_STAR
        w = _rup(w_arg, GRID)
        box_lo = clo - w
        box_hi = chi + w
        total_lo += box_lo
        total_hi += box_hi
        zeros.append({
            "idx": i + 1,
            "a": a, "b": b,
            "neg_then_pos": neg_then_pos,
            "gLine_a": (alo, ahi), "gLine_b": (blo, bhi),
            "c": c, "theta": theta,
            "cos_lo": clo, "cos_hi": chi,
            "base": base, "steps": steps,
            "w": w, "box_lo": box_lo, "box_hi": box_hi,
        })

    return {
        "zeros": zeros,
        "A_lo": total_lo,
        "A_hi": total_hi,
        "width": total_hi - total_lo,
        "true_float": sum(math.cos(float(U_STAR) * (float(zl) + float(zh)) / 2) for zl, zh in zs),
    }


def _sign_definite(lo: F, hi: F) -> int:
    if lo > 0:
        return 1
    if hi < 0:
        return -1
    return 0


# ---------------------------------------------------------------------------
# Lean emitter
# ---------------------------------------------------------------------------
def _q(fr: F) -> str:
    """Rational literal as a Lean ℝ."""
    if fr < 0:
        return f"(-({-fr.numerator} / {fr.denominator}) : ℝ)"
    return f"({fr.numerator} / {fr.denominator} : ℝ)"


def _case_term(case: str) -> str:
    if case == "lo_nonneg":
        return "Or.inl (by norm_num)"
    if case == "hi_nonpos":
        return "Or.inr (Or.inl (by norm_num))"
    return "Or.inr (Or.inr (by norm_num))"


def emit_cos_chain(z: dict, out: list) -> str:
    """Emit the CosEnclosure double-angle chain for zero z.

    Establishes `hcos{i} : cos_lo ≤ Real.cos (c*u*) ∧ Real.cos (c*u*) ≤ cos_hi`,
    where the nested `2*(2*...(y))` is rewritten to `c*u*` (= 2^M * y) at the end.
    Returns the name of the final hypothesis.
    """
    i = z["idx"]
    y, blo, bhi = z["base"]
    cu = z["c"] * U_STAR
    out.append(f"  -- zero {i}: cos({float(z['theta']):.9f}) chain (M={M_DOUBLE} doublings)")
    # Argument atoms: t{i}_0 = c*u* / 2^M = y ; t{i}_{j} = c*u* / 2^{M-j}.  Each is a plain
    # rational literal (kept O(1)); the doubling identity 2*t{i}_{j-1} = t{i}_{j} is one norm_num.
    args = [cu / F(2) ** (M_DOUBLE - j) for j in range(M_DOUBLE + 1)]
    a0 = f"t{i}_0"
    out.append(f"  have hy{i} : |({_q(args[0])} : ℝ)| ≤ 1 := by rw [abs_le]; constructor <;> norm_num")
    out.append(f"  have hb{i} : {_q(blo)} ≤ Real.cos {_q(args[0])} ∧ Real.cos {_q(args[0])} ≤ {_q(bhi)} :=")
    out.append(f"    CosEnclosure.cos_base_interval (y := {_q(args[0])}) hy{i} (by norm_num) (by norm_num)")
    prev = f"hb{i}"
    prev_arg = _q(args[0])
    for j, (plo, phi, nlo, nhi, case) in enumerate(z["steps"]):
        hname = f"hs{i}_{j+1}"
        cur_arg = _q(args[j + 1])
        # cos_double_interval gives cos(2 * prev_arg); rewrite 2*prev_arg = cur_arg first.
        out.append(f"  have hdbl{i}_{j+1} : (2 : ℝ) * {prev_arg} = {cur_arg} := by norm_num")
        out.append(f"  have {hname} : {_q(nlo)} ≤ Real.cos {cur_arg} ∧ Real.cos {cur_arg} ≤ {_q(nhi)} := by")
        out.append(f"    have h := CosEnclosure.cos_double_interval (y := {prev_arg}) "
                   f"(lo' := {_q(nlo)}) (hi' := {_q(nhi)}) {prev}.1 {prev}.2 "
                   f"(by norm_num) (by norm_num) (by norm_num) (by norm_num) ({_case_term(case)})")
        out.append(f"    rw [hdbl{i}_{j+1}] at h; exact h")
        prev = hname
        prev_arg = cur_arg
    # args[M] = cu exactly, so `prev` already concludes at c*u*.
    hcos = f"hcos{i}"
    out.append(f"  have {hcos} : {_q(z['cos_lo'])} ≤ Real.cos ({_q(cu)}) ∧ "
               f"Real.cos ({_q(cu)}) ≤ {_q(z['cos_hi'])} := {prev}")
    return hcos


def _henc_params(z: dict) -> list[str]:
    i = z["idx"]
    alo, ahi = z["gLine_a"]
    blo_, bhi_ = z["gLine_b"]
    if z["neg_then_pos"]:
        return [f"(henca{i} : gLine {_q(z['a'])} ≤ {_q(ahi)})",
                f"(hencb{i} : {_q(blo_)} ≤ gLine {_q(z['b'])})"]
    return [f"(henca{i} : {_q(alo)} ≤ gLine {_q(z['a'])})",
            f"(hencb{i} : gLine {_q(z['b'])} ≤ {_q(bhi_)})"]


def emit_zero_lemma(z: dict, out: list) -> None:
    """Emit a self-contained per-zero lemma: from its 2 gLine sign hyps, produce a
    root r in (a, b) with Lambda(1/2+ri)=0 and cos(r*uStar) in [box_lo, box_hi]."""
    i = z["idx"]
    a, b = z["a"], z["b"]
    cu = z["c"] * U_STAR
    w = z["w"]
    out.append("")
    out.append(f"/-- Zero {i} of 29: root in ({float(a):.7f}, {float(b):.7f}) with certified cos box. -/")
    out.append(f"theorem bragg_zero_{i}")
    for p in _henc_params(z):
        out.append(f"    {p}")
    out.append(f"    : ∃ r : ℝ, ({_q(a)} < r ∧ r < {_q(b)}) ∧")
    out.append(f"      completedRiemannZeta (1 / 2 + (r : ℂ) * Complex.I) = 0 ∧")
    out.append(f"      ({_q(z['box_lo'])} ≤ Real.cos (r * uStar) ∧ "
               f"Real.cos (r * uStar) ≤ {_q(z['box_hi'])}) := by")
    # IVT
    out.append(f"  have hle{i} : {_q(a)} ≤ {_q(b)} := by norm_num")
    out.append(f"  have hcont{i} : ContinuousOn gLine (Set.Icc {_q(a)} {_q(b)}) := "
               "gLine_continuous.continuousOn")
    if z["neg_then_pos"]:
        out.append(f"  have hneg{i} : gLine {_q(a)} < 0 := by linarith [henca{i}]")
        out.append(f"  have hpos{i} : (0 : ℝ) < gLine {_q(b)} := by linarith [hencb{i}]")
        out.append(f"  have hmem{i} : (0 : ℝ) ∈ gLine '' Set.Icc {_q(a)} {_q(b)} := "
                   f"intermediate_value_Icc hle{i} hcont{i} ⟨le_of_lt hneg{i}, le_of_lt hpos{i}⟩")
        out.append(f"  obtain ⟨r, hIcc, hz⟩ := hmem{i}")
        out.append(f"  have hrlo : {_q(a)} < r := by")
        out.append(f"    rcases lt_or_eq_of_le hIcc.1 with h | h")
        out.append(f"    · exact h")
        out.append(f"    · exfalso; rw [← h] at hz; rw [hz] at hneg{i}; exact lt_irrefl 0 hneg{i}")
        out.append(f"  have hrhi : r < {_q(b)} := by")
        out.append(f"    rcases lt_or_eq_of_le hIcc.2 with h | h")
        out.append(f"    · exact h")
        out.append(f"    · exfalso; rw [h] at hz; rw [hz] at hpos{i}; exact lt_irrefl 0 hpos{i}")
    else:
        out.append(f"  have hpos{i} : (0 : ℝ) < gLine {_q(a)} := by linarith [henca{i}]")
        out.append(f"  have hneg{i} : gLine {_q(b)} < 0 := by linarith [hencb{i}]")
        out.append(f"  have hmem{i} : (0 : ℝ) ∈ gLine '' Set.Icc {_q(a)} {_q(b)} := "
                   f"intermediate_value_Icc' hle{i} hcont{i} ⟨le_of_lt hneg{i}, le_of_lt hpos{i}⟩")
        out.append(f"  obtain ⟨r, hIcc, hz⟩ := hmem{i}")
        out.append(f"  have hrlo : {_q(a)} < r := by")
        out.append(f"    rcases lt_or_eq_of_le hIcc.1 with h | h")
        out.append(f"    · exact h")
        out.append(f"    · exfalso; rw [← h] at hz; rw [hz] at hpos{i}; exact lt_irrefl 0 hpos{i}")
        out.append(f"  have hrhi : r < {_q(b)} := by")
        out.append(f"    rcases lt_or_eq_of_le hIcc.2 with h | h")
        out.append(f"    · exact h")
        out.append(f"    · exfalso; rw [h] at hz; rw [hz] at hneg{i}; exact lt_irrefl 0 hneg{i}")
    out.append(f"  have hLam : completedRiemannZeta (1 / 2 + (r : ℂ) * Complex.I) = 0 := by")
    out.append(f"    rw [lambda_eq_gLine, hz]; simp")
    # cos chain (uses local name r); emit_cos_chain uses r{i} -> adapt: it references r{i}? No, chain uses c*u* literals.
    hcos = emit_cos_chain(z, out)
    # Lipschitz absorption
    out.append(f"  have hdist : |r * uStar - {_q(cu)}| ≤ {_q(w)} := by")
    out.append(f"    have hcu : ({_q(cu)} : ℝ) = {_q(z['c'])} * uStar := by rw [uStar]; norm_num")
    out.append(f"    rw [hcu, ← sub_mul, abs_mul, abs_of_nonneg (by rw [uStar]; norm_num : (0:ℝ) ≤ uStar)]")
    out.append(f"    have hrc : |r - {_q(z['c'])}| ≤ {_q(z['b'] - z['a'])} := by")
    out.append(f"      rw [abs_le]; constructor <;> [linarith [hrlo, hrhi]; linarith [hrlo, hrhi]]")
    out.append(f"    calc |r - {_q(z['c'])}| * uStar ≤ {_q(z['b'] - z['a'])} * uStar := by")
    out.append(f"            apply mul_le_mul_of_nonneg_right hrc (by rw [uStar]; norm_num)")
    out.append(f"      _ ≤ {_q(w)} := by rw [uStar]; norm_num")
    out.append(f"  have hbox : {_q(z['box_lo'])} ≤ Real.cos (r * uStar) ∧ "
               f"Real.cos (r * uStar) ≤ {_q(z['box_hi'])} := by")
    out.append(f"    have h := CosEnclosure.cos_encl_bracket (arg := r * uStar) (c := {_q(cu)}) "
               f"(w := {_q(w)}) (by norm_num) hdist {hcos}.1 {hcos}.2")
    out.append(f"    exact ⟨by linarith [h.1], by linarith [h.2]⟩")
    out.append(f"  exact ⟨r, ⟨hrlo, hrhi⟩, hLam, hbox⟩")


def emit(data: dict) -> str:
    zeros = data["zeros"]
    out: list[str] = []
    W = "\n".join
    # ---- header ----
    out.append("/-  BraggH100.lean -- FIRST kernel-certified truncated Bragg amplitude.")
    out.append("")
    out.append("    The finite-volume diffraction amplitude of the certified zeta zeros at the")
    out.append("    rational frequency u* = 693147/1000000 (~= log 2):")
    out.append("")
    out.append("        F_100(u*) := sum_{k=1}^{29} cos(gamma_k * u*)")
    out.append("")
    out.append(f"    over the N = 29 nontrivial zeros gamma_k with 0 < gamma_k <= 100.  Proven to lie")
    out.append(f"    in the certified interval")
    out.append("")
    out.append(f"        F_100(u*) in [{data['A_lo']}, {data['A_hi']}]")
    out.append(f"        (~= [{float(data['A_lo']):.10f}, {float(data['A_hi']):.10f}], width {float(data['width']):.2e};")
    out.append(f"         float truth {data['true_float']:.10f}).")
    out.append("")
    out.append("    STRUCTURE (all kernel-checked, no sorry):")
    out.append("      * Each zero gamma_k is re-derived by the IVT from a certified sign change of")
    out.append("        gLine = Re Lambda(1/2+it) across a rational bracket [a_k, b_k] (width ~1e-6) --")
    out.append("        the same mechanism as XiLineZeros; the endpoint signs (`henc*`) are the")
    out.append("        documented Arb non-kernel input (`enclose_lambda`), identical trust class to")
    out.append("        the band `hLine`.")
    out.append("      * cos(gamma_k*u*) is enclosed by the CosEnclosure double-angle chain (base order-4")
    out.append("        Taylor at |y|<=1, M=30 doublings) at the sample c_k, then the bracket width is")
    out.append("        absorbed by the Lipschitz bound |cos x - cos y| <= |x - y|.")
    out.append("      * The 29 cos boxes are interval-folded (CosEnclosure.add_encl).")
    out.append("")
    out.append("    COMPLETENESS (honest scope).  The winding certificate `AllZeros_h100` establishes")
    out.append("    that there are EXACTLY 29 nontrivial zeros up to height 100 and all lie on the line;")
    out.append("    the 29 ordinates witnessed here are those zeros.  This theorem is stated over the 29")
    out.append("    CERTIFIED ordinates (the set `hLine` carries).  Promoting `sum over witnesses` to")
    out.append("    `sum over the abstract zero set` needs a pigeonhole/injectivity step tying the")
    out.append("    winding Finset to these witnesses -- NOT done here; see the relay note.")
    out.append("")
    out.append("    conjecture1_proved = False.  Finite-T diffraction snapshot only.")
    out.append("-/")
    out.append("import Mathlib")
    out.append("import XiLineZeros")
    out.append("import CosEnclosure")
    out.append("")
    out.append("open Complex Real")
    out.append("open XiLineZeros")
    out.append("")
    out.append("namespace BraggH100")
    out.append("")
    out.append("set_option maxHeartbeats 4000000")
    out.append("")
    out.append("/-- u* = 693147/1000000 ~= log 2, the Bragg frequency. -/")
    out.append(f"noncomputable def uStar : ℝ := {_q(U_STAR)}")
    out.append("")

    # ---- per-zero lemmas ----
    out.append("/-! ### Per-zero certified roots + cos boxes (one lemma each) -/")
    for z in zeros:
        emit_zero_lemma(z, out)

    # ---- assembly theorem ----
    out.append("")
    out.append("/-! ### Assembly: the Bragg amplitude -/")
    out.append("")
    henc_params = []
    for z in zeros:
        henc_params += _henc_params(z)
    out.append("/-- **First kernel-certified Bragg amplitude at T = 100.**  From the 29 certified")
    out.append("    gLine sign changes (documented Arb `enclose_lambda` inputs, same trust class as")
    out.append("    the band `hLine`), there exist 29 strictly increasing on-line zeros whose cos-sum")
    out.append("    at u* lies in the certified interval `[A_lo, A_hi]`.  conjecture1_proved = False. -/")
    out.append("theorem bragg_amplitude_h100")
    for p in henc_params:
        out.append(f"    {p}")
    xs = " ".join(f"x{z['idx']}" for z in zeros)
    ordering = " ∧ ".join(
        [f"{_q(zeros[0]['a'])} ≤ x1"]
        + [f"x{i} < x{i+1}" for i in range(1, N_ZEROS)]
        + [f"x{N_ZEROS} ≤ {_q(zeros[-1]['b'])}"]
    )
    zerocond = " ∧\n       ".join(
        f"completedRiemannZeta (1 / 2 + (x{z['idx']} : ℂ) * Complex.I) = 0" for z in zeros
    )
    sum_expr = " + ".join(f"Real.cos (x{z['idx']} * uStar)" for z in zeros)
    out.append(f"    : ∃ {xs} : ℝ,")
    out.append(f"      ({ordering}) ∧")
    out.append(f"      ({zerocond}) ∧")
    out.append(f"      ({_q(data['A_lo'])} ≤ {sum_expr} ∧")
    out.append(f"       {sum_expr} ≤ {_q(data['A_hi'])}) := by")
    # invoke each per-zero lemma
    for z in zeros:
        i = z["idx"]
        out.append(f"  obtain ⟨r{i}, ⟨hrlo{i}, hrhi{i}⟩, hLam{i}, hbox{i}⟩ := "
                   f"bragg_zero_{i} henca{i} hencb{i}")
    # fold cos boxes
    acc = "hbox1"
    for k in range(1, N_ZEROS):
        fname = f"hsum{k+1}"
        out.append(f"  have {fname} := CosEnclosure.add_encl {acc} hbox{k+1}")
        acc = fname
    # witnesses
    rs = ", ".join(f"r{z['idx']}" for z in zeros)
    out.append(f"  refine ⟨{rs}, ?_, ?_, ?_⟩")
    ord_terms = ["by linarith [hrlo1]"] + \
                [f"by linarith [hrhi{i}, hrlo{i+1}]" for i in range(1, N_ZEROS)] + \
                [f"by linarith [hrhi{N_ZEROS}]"]
    out.append("  · exact ⟨" + ", ".join(ord_terms) + "⟩")
    out.append("  · exact ⟨" + ", ".join(f"hLam{z['idx']}" for z in zeros) + "⟩")
    out.append(f"  · exact ⟨by linarith [{acc}.1], by linarith [{acc}.2]⟩")
    out.append("")
    out.append("end BraggH100")
    return W(out) + "\n"


def write_lean():
    data = build()
    src = emit(data)
    path = _HERE / "lean" / "BraggH100.lean"
    path.write_text(src)
    print(f"wrote {path} ({len(src.splitlines())} lines)")
    print(f"  amplitude enclosure [{float(data['A_lo']):.10f}, {float(data['A_hi']):.10f}] "
          f"width {float(data['width']):.2e}, truth {data['true_float']:.10f}")
    return data


if __name__ == "__main__":
    import argparse
    ap = argparse.ArgumentParser()
    ap.add_argument("--emit", action="store_true", help="write BraggH100.lean")
    args = ap.parse_args()
    if args.emit:
        write_lean()
    else:
        data = build()
        print(f"F_{T_HEIGHT}(u*) enclosure: [{float(data['A_lo'])}, {float(data['A_hi'])}]")
        print(f"  width = {float(data['width']):.3e}")
        print(f"  true (float) = {data['true_float']:.12f}")
        for z in data["zeros"][:3]:
            print(f"  zero {z['idx']}: cos in [{float(z['cos_lo']):.12f}, {float(z['cos_hi']):.12f}], "
                  f"sign {'-,+' if z['neg_then_pos'] else '+,-'}")
