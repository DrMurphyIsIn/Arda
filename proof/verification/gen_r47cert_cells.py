"""Generator for the R47 Phase 4b+ Lean cell certificates (R47CertB/C/D.lean).

Emits, for each cell (cA, cb) of the unified topped-up merge table, the Lean text of:
  * the four bilinear coefficients c1..c4 (defs in terms of Fw/zw),
  * the bilinear decomposition theorem (afterD - beforeD = c1 + c2 sQ + c3 sr + c4 sQ sr),
  * the four Polya corner certificates (sympy-exported nonneg-coefficient numerator over
    a factored positive denominator; equality by field_simp+ring, nonneg by positivity),
  * the assembled box theorem via bilinear_corner_nonneg.

The template mirrors the CI-validated hand-written cell in R47Cert.lean (direct cA=0)
EXACTLY -- run only after that file is lean-verify green.  Self-checks: every emitted
numerator is re-verified all-nonneg and equal (as a sympy rational function) to the
corner expression before any text is written; the bilinear decomposition is re-verified
symbolically per cell.

Parameterization (matches kelmans_unified_merge.certify_unified_table):
  topped-up cells (cb in 0..4, k = 5-cb): db = (k+1) + v, da = db + u,
      corners sQ in {0, (da-1)*cap}, sr in {0, v*cap};
  direct cells (cb = 5, k = 0): db = 2 + v, da = db + u,
      corners sQ in {0, (da-1)*cap}, sS in {3/23, (db-1)*cap}.
  cap = 3/16.

Usage:
  .venv python3 proof/verification/gen_r47cert_cells.py \
      [--cells "cb=4" | "direct"] [--out FILE]
Prints (or writes) the Lean body; the file header/imports are added by hand.
conjecture1_proved=False -- this generates certificate text only.
"""
from __future__ import annotations

import argparse
import sys

import sympy as sp

U, V = sp.symbols("u v", nonnegative=True)
CAP = sp.Rational(3, 16)
Z15, Z14 = sp.Rational(3, 23), sp.Rational(3, 19)
WT, V5 = sp.Rational(76, 115), sp.Rational(621, 64)


def Fs(deg, c):
    if c == 0:
        return sp.Integer(1)
    D_ = deg + c
    return sp.Rational(3, 2) ** c + sp.Rational(c) / (2 * D_) * sp.Rational(3, 2) ** (c - 1)


def zs(deg, c):
    return sp.Integer(3) / (3 * deg + 4 * c)


def poly_lean(p: sp.Poly) -> str:
    """Nonneg-coefficient polynomial in (u, v) as Lean source (asserts nonnegativity)."""
    terms = []
    for monom, coeff in zip(p.monoms(), p.coeffs()):
        assert coeff >= 0 and sp.Integer(coeff) == coeff, (monom, coeff)
        eu, ev = monom
        factors = []
        if int(coeff) != 1 or (eu == 0 and ev == 0):
            factors.append(str(int(coeff)))
        if eu == 1:
            factors.append("u")
        elif eu > 1:
            factors.append(f"u ^ {eu}")
        if ev == 1:
            factors.append("v")
        elif ev > 1:
            factors.append(f"v ^ {ev}")
        terms.append(" * ".join(factors))
    return " + ".join(terms)


def den_lean(den: sp.Expr) -> str:
    """Factored positive denominator as Lean source (asserts positivity structure)."""
    const, factors = sp.factor_list(den)
    assert const > 0, den
    parts = [str(int(const))]
    for base, exp in factors:
        pb = sp.Poly(base, U, V)
        assert all(c > 0 for c in pb.coeffs()), (base, "factor must have positive coeffs")
        bs = sp.sstr(sp.expand(base)).replace("**", " ^ ").replace("*", " * ")
        parts.extend([f"({bs})"] * int(exp))
    return " * ".join(parts)


def expr_lean_linear(e: sp.Expr) -> str:
    """Small linear (u,v)-expression as Lean source."""
    return sp.sstr(sp.expand(e)).replace("**", " ^ ").replace("*", " * ")


def ne_hyps(cA: int, cb: int, k: int, da, db) -> list[str]:
    """The nonzero hypotheses matching the syntactic forms field_simp will see."""
    dap = da + db - 1
    hs = []
    seen = set()

    def add(form: str):
        if form not in seen:
            seen.add(form)
            hs.append(form)

    # Fw denominators 2*(d + c) for loaded factors actually unfolded
    if cA >= 1:
        add(f"(2 : ℝ) * ({expr_lean_linear(da)} + {cA})")
        add(f"(2 : ℝ) * ({expr_lean_linear(dap)} + {cA})")
    if cb >= 1:
        add(f"(2 : ℝ) * ({expr_lean_linear(db)} + {cb})")
    # zw denominators 3*d + 4*c
    add(f"3 * ({expr_lean_linear(da)} : ℝ) + 4 * {cA}")
    add(f"3 * ({expr_lean_linear(db)} : ℝ) + 4 * {cb}")
    add(f"3 * ({expr_lean_linear(dap)} : ℝ) + 4 * {cA}")
    return hs


def gen_cell(cA: int, cb: int) -> str:
    k = 5 - cb
    if cb == 5:
        db = 2 + V
        sr_corners = [(Z15, "(3 / 23)"), ((db - 1) * CAP, "((v + 1) * (3 / 16))")]
    else:
        db = (k + 1) + V
        sr_corners = [(sp.Integer(0), "0"), (V * CAP, "(v * (3 / 16))")]
    da = db + U
    dap = da + db - 1
    sq_corners = [(sp.Integer(0), "0"),
                  ((da - 1) * CAP, f"(({expr_lean_linear(da - 1)}) * (3 / 16))")]

    Fa, Fb = Fs(da, cA), Fs(db, cb)
    Fap = Fs(dap, cA)
    za, zb, zap = zs(da, cA), zs(db, cb), zs(dap, cA)

    # bilinear coefficients (verified below against D_unified's form)
    c1 = WT ** k * Fap * V5 * (1 + zap * (k * Z14 + Z15)) \
        - Fa * Fb * (1 + zb * k * Z15 + za * zb)
    c2 = WT ** k * Fap * V5 * zap - Fa * Fb * za * (1 + zb * k * Z15)
    c3 = WT ** k * Fap * V5 * zap - Fa * Fb * zb
    c4 = -Fa * Fb * za * zb
    # self-check the decomposition
    sQ, sr = sp.symbols("sQ sr")
    before = Fa * Fb * ((1 + za * sQ) * (1 + zb * (k * Z15 + sr)) + za * zb)
    after = WT ** k * Fap * V5 * (1 + zap * (sQ + k * Z14 + sr + Z15))
    assert sp.simplify((after - before) - (c1 + c2 * sQ + c3 * sr + c4 * sQ * sr)) == 0, (cA, cb)

    name = f"d{'T' if cb < 5 else 'A'}{cA}{cb if cb < 5 else ''}"
    da_l, db_l, dap_l = expr_lean_linear(da), expr_lean_linear(db), expr_lean_linear(dap)
    fw_l = {0: "1"}
    def FwL(d_l, c):
        return f"Fw ({d_l}) {c}"
    c1_l = (f"(76 / 115) ^ {k} * {FwL(dap_l, cA)} * (621 / 64) "
            f"* (1 + zw ({dap_l}) {cA} * (({k} : ℝ) * (3 / 19) + 3 / 23))\n"
            f"    - {FwL(da_l, cA)} * {FwL(db_l, cb)} "
            f"* (1 + zw ({db_l}) {cb} * (({k} : ℝ) * (3 / 23)) + zw ({da_l}) {cA} * zw ({db_l}) {cb})")
    c2_l = (f"(76 / 115) ^ {k} * {FwL(dap_l, cA)} * (621 / 64) * zw ({dap_l}) {cA}\n"
            f"    - {FwL(da_l, cA)} * {FwL(db_l, cb)} * zw ({da_l}) {cA} "
            f"* (1 + zw ({db_l}) {cb} * (({k} : ℝ) * (3 / 23)))")
    c3_l = (f"(76 / 115) ^ {k} * {FwL(dap_l, cA)} * (621 / 64) * zw ({dap_l}) {cA}\n"
            f"    - {FwL(da_l, cA)} * {FwL(db_l, cb)} * zw ({db_l}) {cb}")
    c4_l = f"-({FwL(da_l, cA)} * {FwL(db_l, cb)} * (zw ({da_l}) {cA} * zw ({db_l}) {cb}))"

    out = []
    out.append(f"/-! ### Cell (cA, cb) = ({cA}, {cb}) -/\n")
    for i, cl in enumerate((c1_l, c2_l, c3_l, c4_l), 1):
        out.append(f"noncomputable def {name}c{i} (u v : ℝ) : ℝ :=\n  {cl}\n")

    # bilinear decomposition theorem
    out.append(f"""theorem {name}_bilinear (u v sQ sr : ℝ) :
    afterD ({da_l}) ({db_l}) {cA} {k} sQ sr - beforeD ({da_l}) ({db_l}) {cA} {cb} {k} sQ sr
      = {name}c1 u v + {name}c2 u v * sQ + {name}c3 u v * sr + {name}c4 u v * (sQ * sr) := by
  simp only [afterD, beforeD, {name}c1, {name}c2, {name}c3, {name}c4,
    Fw_zero, Fw_one, Fw_two, Fw_three, Fw_four, Fw_five, zw]
  push_cast
  ring
""")

    hyps = ne_hyps(cA, cb, k, da, db)
    hyp_lines = "\n".join(
        f"  have hd{j} : {h} ≠ 0 := by positivity" for j, h in enumerate(hyps, 1))

    corner_names = []
    for qi, (sqv, sq_l) in enumerate(sq_corners):
        for ri, (srv, sr_l) in enumerate(sr_corners):
            expr = c1 + c2 * sqv + c3 * srv + c4 * sqv * srv
            num, den = sp.fraction(sp.together(expr))
            pn = sp.Poly(sp.expand(num), U, V)
            pd = sp.Poly(sp.expand(den), U, V)
            if all(c < 0 for c in pd.coeffs()):
                num, den = -num, -den
                pn = sp.Poly(sp.expand(num), U, V)
            num_l, den_l = poly_lean(pn), den_lean(den)
            cn = f"{name}_corner{qi}{ri}"
            corner_names.append((cn, sq_l, sr_l))
            body = (f"{name}c1 u v + {name}c2 u v * {sq_l} + {name}c3 u v * {sr_l}\n"
                    f"        + {name}c4 u v * ({sq_l} * {sr_l})")
            out.append(f"""theorem {cn} (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    0 ≤ {body} := by
{hyp_lines}
  have hkey : {body}
      = ({num_l})
        / ({den_l}) := by
    simp only [{name}c1, {name}c2, {name}c3, {name}c4,
      Fw_zero, Fw_one, Fw_two, Fw_three, Fw_four, Fw_five, Fw_one_five, zw_one_five, zw]
    push_cast
    field_simp
    ring
  rw [hkey]
  positivity
""")

    # assembled cell theorem
    (n00, _, _), (n01, _, _), (n10, _, _), (n11, _, _) = corner_names
    sq1_l = sq_corners[1][1]
    sr0_l, sr1_l = sr_corners[0][1], sr_corners[1][1]
    hS0 = f"{sr0_l} ≤ sr" if cb == 5 else "0 ≤ sr"
    out.append(f"""theorem {name}_cell (u v sQ sr : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hQ0 : 0 ≤ sQ) (hQ1 : sQ ≤ {sq1_l})
    (hS0 : {hS0}) (hS1 : sr ≤ {sr1_l}) :
    beforeD ({da_l}) ({db_l}) {cA} {cb} {k} sQ sr ≤ afterD ({da_l}) ({db_l}) {cA} {k} sQ sr := by
  rw [← sub_nonneg, {name}_bilinear]
  exact bilinear_corner_nonneg hQ0 hQ1 hS0 hS1 ({n00} u v hu hv) ({n01} u v hu hv)
    ({n10} u v hu hv) ({n11} u v hu hv)
""")
    return "\n".join(out)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--cells", default="direct",
                    help='"direct" (cb=5, cA 1..5), "cb=N" (topped-up row), or "cA,cb"')
    ap.add_argument("--out", default=None)
    args = ap.parse_args()
    cells = []
    if args.cells == "direct":
        cells = [(cA, 5) for cA in range(1, 6)]
    elif args.cells.startswith("cb="):
        cb = int(args.cells[3:])
        cells = [(cA, cb) for cA in range(6)]
    else:
        cA, cb = map(int, args.cells.split(","))
        cells = [(cA, cb)]
    text = "\n".join(gen_cell(cA, cb) for cA, cb in cells)
    if args.out:
        with open(args.out, "w") as f:
            f.write(text)
        print(f"wrote {args.out} ({len(cells)} cells)", file=sys.stderr)
    else:
        print(text)


if __name__ == "__main__":
    main()


# ------------------------------------------------------------------ P5d-2 dispatch
def gen_dispatch(cA: int, cb: int) -> str:
    """The N-degree adapter for cell (cA, cb): box in (dA, dB) form -> the cell."""
    k = 5 - cb
    kk = k + 1 if cb < 5 else 2          # v = dB - kk
    name = f"d{'T' if cb < 5 else 'A'}{cA}{cb if cb < 5 else ''}"
    u, v = f"((dA - dB : ℕ) : ℝ)", f"((dB - {kk} : ℕ) : ℝ)"
    if cb < 5:
        e1_rhs = f"{u} + {v} + {kk}"
        e2_rhs = f"{v} + {kk}"
        hs0 = "0 ≤ sr"
        hs1_cell = f"{v} * (3 / 16)"
        sq1_off = k  # (dA-1) = u + v + (kk-1) = u + v + k
    elif cA == 0:
        # the HAND-written directA0_cell uses argument order (2 + v + u) (2 + v)
        e1_rhs = f"2 + {v} + {u}"
        e2_rhs = f"2 + {v}"
        hs0 = "3 / 23 ≤ sr"
        hs1_cell = f"({v} + 1) * (3 / 16)"
        sq1_off = 1  # (dA-1) = u + v + 1
    else:
        # the GENERATED dA1..dA5 cells use sympy order (u + v + 2) (v + 2)
        e1_rhs = f"{u} + {v} + 2"
        e2_rhs = f"{v} + 2"
        hs0 = "3 / 23 ≤ sr"
        hs1_cell = f"({v} + 1) * (3 / 16)"
        sq1_off = 1  # (dA-1) = u + v + 1
    return f"""theorem dispatch_{name} (dA dB : ℕ) (sQ sr : ℝ)
    (hord : dB ≤ dA) (hdb : {kk} ≤ dB)
    (hQ0 : 0 ≤ sQ) (hQ1 : sQ ≤ ((dA : ℝ) - 1) * (3 / 16))
    (hS0 : {hs0}) (hS1 : sr ≤ ((dB : ℝ) - {kk - 1 if cb == 5 else kk}) * (3 / 16)) :
    beforeD (dA : ℝ) (dB : ℝ) {cA} {cb} {k} sQ sr
      ≤ afterD (dA : ℝ) (dB : ℝ) {cA} {k} sQ sr := by
  have e1 : (dA : ℝ) = {e1_rhs} := by
    push_cast [Nat.cast_sub hord, Nat.cast_sub hdb]
    ring
  have e2 : (dB : ℝ) = {e2_rhs} := by
    push_cast [Nat.cast_sub hdb]
    ring
  have hu : (0 : ℝ) ≤ {u} := by positivity
  have hv : (0 : ℝ) ≤ {v} := by positivity
  have hQ1' : sQ ≤ ({u} + {v} + {sq1_off}) * (3 / 16) := by
    have h : ((dA : ℝ) - 1) = {u} + {v} + {sq1_off} := by
      push_cast [Nat.cast_sub hord, Nat.cast_sub hdb]
      ring
    rw [← h]
    exact hQ1
  have hS1' : sr ≤ {hs1_cell} := by
    have h : ((dB : ℝ) - {kk - 1 if cb == 5 else kk}) = {hs1_cell.split(' * ')[0] if cb < 5 else '(' + v + ' + 1)'} := by
      push_cast [Nat.cast_sub hdb]
      ring
    calc sr ≤ ((dB : ℝ) - {kk - 1 if cb == 5 else kk}) * (3 / 16) := hS1
      _ = {hs1_cell} := by rw [h]
  rw [e1, e2]
  exact {'directA0_cell' if (cA, cb) == (0, 5) else name + '_cell'} {u} {v} sQ sr hu hv hQ0 hQ1' hS0 hS1'
"""


def gen_all_dispatch() -> str:
    out = []
    for cb in [5, 4, 3, 2, 1, 0]:
        for cA in range(6):
            out.append(gen_dispatch(cA, cb))
    return "\n".join(out)


def gen_head_merge_le() -> str:
    """The assembled head-merge monotonicity theorem: box data + 36-way dispatch."""
    branches = []
    for cb in range(6):
        k = 5 - cb
        kk = k + 1 if cb < 5 else 2
        for cA in range(6):
            name = f"d{'T' if cb < 5 else 'A'}{cA}{cb if cb < 5 else ''}"
            if cb < 5:
                sub_lit = kk          # hS1 bound offset = k+1
                hcast_rhs = "(others.length : ℝ) + ((tailU rest).length : ℝ)"
            else:
                sub_lit = 1
                hcast_rhs = "(others.length : ℝ) + ((tailU rest).length : ℝ)"
            floor = ("(by\n"
                     "        have hne : others ≠ [] := by\n"
                     "          intro h0\n"
                     "          rw [h0] at hlenB\n"
                     "          simp only [List.length_nil] at hlenB\n"
                     "          omega\n"
                     "        have h1 := sigmaArms_floor others hbalO hne\n"
                     "        have h2 := qSum_tailU_nonneg rest\n"
                     "        linarith)") if cb == 5 else "hS0"
            branches.append(f"""  · obtain rfl : k = {k} := by omega
    exact dispatch_{name} dA dB _ _ hordN (by omega) hQ0 hQ1 {floor}
      (by
        have hcast : ((dB : ℝ) - {sub_lit}) = {hcast_rhs} := by
          rw [hdB, hlenB]
          push_cast
          ring
        have h1 : sigmaArms others ≤ (others.length : ℝ) * (3 / 16) :=
          sum_zw_arms_le others hbalO
        have h2 := qSum_tailU_le rest hcap
        rw [hcast]
        linarith)""")
    body = "\n".join(branches)
    return f"""/-- **THE HEAD-MERGE MONOTONICITY THEOREM** on the certified family: balanced arms,
    capped tail, donor split, and the hubward degree ordering (S5; the anti-hubward
    direction is a named residual).  The merge does not decrease the objective. -/
theorem head_merge_le (armsA : List ℕ) (cA : ℕ) (armsB others : List ℕ) (cb k : ℕ)
    (rest : List Hub)
    (hcA : cA ≤ 5) (hcb : cb ≤ 5) (hk : k = 5 - cb)
    (hsplit : armsB.Perm (List.replicate k 5 ++ others))
    (hbalA : BalancedArms armsA) (hbalO : BalancedArms others)
    (hcap : Capped rest) (hB5 : 5 ≤ armsB.length)
    (hord : armsB.length + (tailU rest).length ≤ armsA.length) :
    Aobj (backboneU ((armsA, cA) :: (armsB, cb) :: rest))
      ≤ Aobj (backboneU ((armsA ++ List.replicate k 4 ++ others ++ [5], cA) :: rest)) := by
  apply head_merge_le_of_cellD armsA cA armsB others cb k rest hsplit
  have hlenB : armsB.length = k + others.length := by
    simpa [List.length_append, List.length_replicate] using hsplit.length_eq
  set dA : ℕ := armsA.length + 1 with hdA
  set dB : ℕ := armsB.length + (tailU rest).length + 1 with hdB
  have hordN : dB ≤ dA := by omega
  have hQ0 : 0 ≤ sigmaArms armsA := sum_zw_arms_nonneg armsA
  have hQ1 : sigmaArms armsA ≤ ((dA : ℝ) - 1) * (3 / 16) := by
    have h := sum_zw_arms_le armsA hbalA
    have hcast : ((dA : ℝ) - 1) = (armsA.length : ℝ) := by
      rw [hdA]
      push_cast
      ring
    rw [hcast]
    exact h
  have hS0 : 0 ≤ sigmaArms others + qSum (tailU rest) :=
    add_nonneg (sum_zw_arms_nonneg others) (qSum_tailU_nonneg rest)
  interval_cases cb <;> interval_cases cA
{body}
"""


def gen_vee_merge_le(mirror: bool = False) -> str:
    """The Vee (or mirror) merge monotonicity: box data + 36-way dispatch."""
    dtail = "upc" if mirror else "dn"
    dcap = "hcapU" if mirror else "hcapD"
    branches = []
    for cLoop in range(6):          # the DONOR's load (cb hubward; cA mirror)
        k = 5 - cLoop
        kk = k + 1 if cLoop < 5 else 2
        sub_lit = kk if cLoop < 5 else 1
        for cKeep in range(6):      # the ABSORBER's load
            name = f"d{'T' if cLoop < 5 else 'A'}{cKeep}{cLoop if cLoop < 5 else ''}"
            floor = ("(by\n"
                     "        have hne : othersD ≠ [] := by\n"
                     "          intro h0\n"
                     "          rw [h0] at hlenB\n"
                     "          simp only [List.length_nil] at hlenB\n"
                     "          omega\n"
                     "        have h1 := sigmaArms_floor othersD hbalO hne\n"
                     f"        have h2 := qSum_tailU_nonneg {dtail}\n"
                     "        linarith)") if cLoop == 5 else "hS0"
            branches.append(f"""  · obtain rfl : k = {k} := by omega
    exact dispatch_{name} dA dB _ _ hordN (by omega) hQ0 hQ1 {floor}
      (by
        have hcast : ((dB : ℝ) - {sub_lit})
            = (othersD.length : ℝ) + ((tailU {dtail}).length : ℝ) := by
          rw [hdB, hlenB]
          push_cast
          ring
        have h1 : sigmaArms othersD ≤ (othersD.length : ℝ) * (3 / 16) :=
          sum_zw_arms_le othersD hbalO
        have h2 := qSum_tailU_le {dtail} {dcap}
        rw [hcast]
        linarith)""")
    body = "\n".join(branches)
    if not mirror:
        return f"""/-- **THE VEE MERGE MONOTONICITY THEOREM** (hubward at any rooting): balanced arms,
    capped tails both sides, donor split, hubward ordering. -/
theorem vee_merge_le (armsA : List ℕ) (cA : ℕ) (armsB othersD : List ℕ) (cb k : ℕ)
    (dn upc : List Hub)
    (hcA : cA ≤ 5) (hcb : cb ≤ 5) (hk : k = 5 - cb)
    (hsplit : armsB.Perm (List.replicate k 5 ++ othersD))
    (hbalA : BalancedArms armsA) (hbalO : BalancedArms othersD)
    (hcapD : Capped dn) (hcapU : Capped upc) (hB5 : 5 ≤ armsB.length)
    (hord : armsB.length + (tailU dn).length ≤ armsA.length + (tailU upc).length) :
    AobjV upc (armsA, cA) ((armsB, cb) :: dn)
      ≤ AobjV upc (armsA ++ List.replicate k 4 ++ othersD ++ [5], cA) dn := by
  apply vee_merge_le_of_cellD armsA cA armsB othersD cb k dn upc hsplit
  have hlenB : armsB.length = k + othersD.length := by
    simpa [List.length_append, List.length_replicate] using hsplit.length_eq
  set dA : ℕ := armsA.length + (tailU upc).length + 1 with hdA
  set dB : ℕ := armsB.length + (tailU dn).length + 1 with hdB
  have hordN : dB ≤ dA := by omega
  have hQ0 : 0 ≤ sigmaArms armsA + qSum (tailU upc) :=
    add_nonneg (sum_zw_arms_nonneg armsA) (qSum_tailU_nonneg upc)
  have hQ1 : sigmaArms armsA + qSum (tailU upc) ≤ ((dA : ℝ) - 1) * (3 / 16) := by
    have h1 : sigmaArms armsA ≤ (armsA.length : ℝ) * (3 / 16) :=
      sum_zw_arms_le armsA hbalA
    have h2 := qSum_tailU_le upc hcapU
    have hcast : ((dA : ℝ) - 1)
        = (armsA.length : ℝ) + ((tailU upc).length : ℝ) := by
      rw [hdA]
      push_cast
      ring
    rw [hcast]
    linarith
  have hS0 : 0 ≤ sigmaArms othersD + qSum (tailU dn) :=
    add_nonneg (sum_zw_arms_nonneg othersD) (qSum_tailU_nonneg dn)
  interval_cases cb <;> interval_cases cA
{body}
"""
    else:
        return f"""/-- **THE MIRROR MERGE MONOTONICITY THEOREM** (anti-hubward): the donor heads the
    up-chain; same table at the role-swapped instantiation. -/
theorem mirror_merge_le (armsA othersD : List ℕ) (cA : ℕ) (armsB : List ℕ)
    (cb k : ℕ) (dn upc : List Hub)
    (hcA : cA ≤ 5) (hcb : cb ≤ 5) (hk : k = 5 - cA)
    (hsplit : armsA.Perm (List.replicate k 5 ++ othersD))
    (hbalB : BalancedArms armsB) (hbalO : BalancedArms othersD)
    (hcapD : Capped dn) (hcapU : Capped upc) (hA5 : 5 ≤ armsA.length)
    (hord : armsA.length + (tailU upc).length ≤ armsB.length + (tailU dn).length) :
    AobjV ((armsA, cA) :: upc) (armsB, cb) dn
      ≤ AobjV upc (armsB ++ List.replicate k 4 ++ othersD ++ [5], cb) dn := by
  apply mirror_merge_le_of_cellD armsA othersD cA armsB cb k dn upc hsplit
  have hlenB : armsA.length = k + othersD.length := by
    simpa [List.length_append, List.length_replicate] using hsplit.length_eq
  set dA : ℕ := armsB.length + (tailU dn).length + 1 with hdA
  set dB : ℕ := armsA.length + (tailU upc).length + 1 with hdB
  have hordN : dB ≤ dA := by omega
  have hQ0 : 0 ≤ sigmaArms armsB + qSum (tailU dn) :=
    add_nonneg (sum_zw_arms_nonneg armsB) (qSum_tailU_nonneg dn)
  have hQ1 : sigmaArms armsB + qSum (tailU dn) ≤ ((dA : ℝ) - 1) * (3 / 16) := by
    have h1 : sigmaArms armsB ≤ (armsB.length : ℝ) * (3 / 16) :=
      sum_zw_arms_le armsB hbalB
    have h2 := qSum_tailU_le dn hcapD
    have hcast : ((dA : ℝ) - 1)
        = (armsB.length : ℝ) + ((tailU dn).length : ℝ) := by
      rw [hdA]
      push_cast
      ring
    rw [hcast]
    linarith
  have hS0 : 0 ≤ sigmaArms othersD + qSum (tailU upc) :=
    add_nonneg (sum_zw_arms_nonneg othersD) (qSum_tailU_nonneg upc)
  interval_cases cA <;> interval_cases cb
{body}
"""
