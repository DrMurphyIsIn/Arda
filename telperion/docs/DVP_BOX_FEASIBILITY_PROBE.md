# DVP + Box Combination — Task 1 Feasibility Probe (GO/NO-GO)

**Project:** "dVP + box = all zeros up to height T lie on Re = 1/2."
**Question this probe answers:** to capture *every* zero up to height `T = 100`, the
box `[a, 1-a] × [0, T]` must have `a ≤ dlvpRateC / log T`. At `T = 100` this forces an
extreme-precision box edge `a ≈ 1.6e-6` sitting a hair off the pole `s = 1`. Are the
three risks that creates tractable *before* the full concrete build (Task 5)?

**VERDICT: GO.** All three risks clear. The concrete `T = 100` certificate is buildable.
Chosen concrete edge: **`a = 1/10^6`** (`= 1e-6`).

`conjecture1_proved = False` (this is a kernel-verified reduction for a concrete height,
NOT a proof of RH).

---

## Risk 1 — Effective-rate value + rational lower bound + discharge

`dlvpRateC` closed form (from `zero_free_bridge/lean/DlvpZetaRateEffective.lean`):

```
dlvpRateK = 1 + 2 * ((8 / (3 * log((23/16)/(11/8))) + 608/9) / 16) * (log(15/(2 - π²/6)) + 1)
dlvpRateC = 1 / (112 * 16 * dlvpRateK)
```

Note `(23/16)/(11/8) = 23/22`.

### Numerics (mpmath, 50 dps)

| quantity | value |
|---|---|
| `log(23/22)` | 0.0444517625708… |
| `M = (8/(3·log(23/22)) + 608/9)/16` | 7.97160485696… |
| `log(15/(2 − π²/6))` | 3.74350198066… |
| **`dlvpRateK`** | **76.6266468561…** |
| **`dlvpRateC`** | **7.28252817e-6** |
| `log 100` | 4.60517018598… |
| **`delta_100 = dlvpRateC / log 100`** | **1.58138090e-6** |
| `a = 1e-6 ≤ delta_100` | **True** (margin **1.581×**) |

### Safe rational LOWER bound on `dlvpRateC`

To bound `dlvpRateC = 1/(112·16·K)` from below, bound `K` from above, using rational
bounds each of which is itself rationally provable (via one `Real.exp` enclosure):

- `log(23/22) ≥ 444/10000` — since `exp(444/10000) ≈ 1.045400 ≤ 23/22 = 1.045454…` ✔
- `log(15/(2−π²/6)) ≤ 3744/1000` — since `15/(2−π²/6) ≈ 42.2457 ≤ exp(3.744) ≈ 42.2667` ✔
  (`8/(3·L)` is *decreasing* in `L`, so the lower bound on `L = log(23/22)` yields the
  upper bound on that term — direction handled by `gcongr`.)

⟹ `M ≤ 7.975976`, `dlvpRateK ≤ 76.67607`, and

```
dlvpRateC ≥ 41625 / 5719420672 ≈ 7.277835e-6.
```

And `log 100 ≤ 47/10` (`= 4.7 > 4.60517`; `exp(4.7) ≥ 100`). Hence

```
dlvpRateC / log 100 ≥ (41625/5719420672) / (47/10) ≈ 1.548476e-6 ≥ 1e-6   (margin 1.548×).
```

So `a = 1/10^6 ≤ dlvpRateC / log 100` holds even with the *conservative rational* chain.

### Discharge assessment (Lean, v4.32.0) — **TRACTABLE (GO)**

The inequality `(1/10^6 : ℝ) ≤ dlvpRateC / Real.log 100` reduces to standard Mathlib steps:

1. Two `Real.log ↔ Real.exp` rational enclosures (`Real.le_log_iff_exp_le` /
   `Real.log_le_iff_le_exp`, then a rational `Real.exp` bound) for the two `log` terms.
2. Monotone substitution into `dlvpRateK`'s closed form → rational `K_upper` (`gcongr`,
   note the decreasing `8/(3·L)` term).
3. `one_div_le_one_div_of_le` for `dlvpRateC ≥ 1/(112·16·K_upper)`.
4. `Real.log 100 ≤ 47/10` (`Real.log_le_iff_le_exp` + `exp(4.7) ≥ 100`).
5. `div` monotonicity + final `norm_num`.

Every lemma exists in v4.32.0, and `DlvpZetaRateEffective.lean` already discharges the
sibling facts (`two_sub_pi_sq_div_six_pos`, `Real.log_pos`, `Real.log_nonneg` on these
exact arguments). The only genuinely new ingredients are two routine `Real.exp` rational
enclosures. **Assessed GO.** (In the throwaway probe this target carries a single LABELED
`sorry` naming exactly these two missing enclosures — it is a placeholder, not a claim.)

---

## Risk 2 — Arb winding over the wide box `[1/10^6, 1-1/10^6] × [0, 100]`

Ran the PR #312 driver:

```python
run_box("1/1000000", "999999/1000000", "0", "100", write=False)
```

**Result: SUCCESS.**

| metric | value |
|---|---|
| winding `N` | **29** |
| on-line `N_line` | **29** (agree) |
| segment straddling 0 | none (driver's edge-non-vanishing guard passed) |
| emit time | **≈ 1.3 s** (`prec=300`, `winding_prec=160`) |
| result | emitted `rh_in_box_1d1000000_999999d1000000_0_100`, 48 455 bytes |

The extreme `a = 1e-6` width does **not** break Arb — the rigorous zeta Taylor segments
resolve cleanly and the boundary winding matches the on-line sign-change count (29 = 29),
so `box_localization_certificate` accepts. No fallback to a wider `a` was needed.

### `choose_ball` for this box (exact rationals)

```
center  cPB = ⟨1/2, 50⟩
RPB²         = 5000499999000001 / 2000000000000   ≈ 2500.24999950
box dc2      = 2500249999000001 / 1000000000000   ≈ 2500.24999900   (corner dist²)
pole d12     = 10001/4                              = 2500.25000000   (|1 − c|²)
```

`dc2 < RPB² < d12` ⟹ box strictly inside the ball, pole `s = 1` strictly outside.
The three values agree to ~10 significant figures (separated by ~5e-7 relative) — this is
the tightness that Risk 3 must survive.

---

## Risk 3 — Geometry `nlinarith`/`norm_num` at `a ≈ 1e-6`

Throwaway probe `examples/zeta_zero_localization/lean/DvpBoxProbe.lean` (NOT in any
`lakefile.toml` `defaultTargets`, imported by no built target). Built standalone with
`lake env lean DvpBoxProbe.lean` after `lake exe cache get`.

**Result: sorry-free for both geometric facts.**

- `hbox_ball_probe` (box ⊆ ball) — verbatim driver `hbox_ball` at `a = 1e-6`: the
  `nlinarith [..., sq_nonneg (ρ.re − 1/2), sq_nonneg (ρ.im − 50)]` discharges the tight
  `RPB²` separation. **No error.**
- `hs1_probe` (`1 ∉ ball`) — verbatim driver `hs1`: `Real.sqrt_le_sqrt (by norm_num)` +
  `linarith`. **No error.**

The only diagnostic from the whole file is the expected `declaration uses sorry` warning
at the Risk-1 effective-rate `example` (the labeled placeholder). Build time ≈ 28 s
(dominated by `import Mathlib`).

So the extreme-precision denominators (`2000000000000`, numerators like
`5000499999000001`) do **not** defeat `nlinarith`/`norm_num` — the box geometry the
driver emits is kernel-checkable at `a = 1e-6`. **Risk 3 clears.**

---

## Verdict

| Risk | Status |
|---|---|
| 1. Effective-rate value + rational lower bound + Lean discharge | **CLEAR** (`a=1e-6 ≤ delta_100`, margin 1.55–1.58×; discharge tractable) |
| 2. Arb winding at `a = 1e-6` | **CLEAR** (`N = N_line = 29`, 1.3 s, no straddle) |
| 3. Geometry `nlinarith`/`norm_num` at `a ≈ 1e-6` | **CLEAR** (both facts sorry-free) |

**GO.** The concrete `T = 100` all-zeros-up-to-height certificate (Task 5) is buildable
with box edge **`a = 1/10^6`**. The reduction-theorem fallback (Task 4 stating the theorem
with `a ≤ dlvpRateC/log T` as an *undischarged hypothesis*) is **not** needed as a
substitute, though it remains a valid parallel deliverable.

**Chosen concrete `a = 1/10^6`.** `conjecture1_proved = False`.

---

### Reproduction

```bash
# Numerics + rational lower bound
cd telperion && PYTHONPATH=src /Users/peterwmurphy/arda-trading/.venv/bin/python3 - <<'PY'
import mpmath as mp; from fractions import Fraction as F
mp.mp.dps = 60
Lr = mp.log(mp.mpf('23')/16/(mp.mpf('11')/8)); M=(8/(3*Lr)+mp.mpf('608')/9)/16
K = 1+2*M*(mp.log(15/(2-mp.pi**2/6))+1); C = 1/(112*16*K)
print('dlvpRateC=',C,'delta_100=',C/mp.log(100))
PY

# Arb winding at a=1e-6
cd telperion && PYTHONPATH=src /Users/peterwmurphy/arda-trading/.venv/bin/python3 - <<'PY'
import sys; sys.path.insert(0,'examples/zeta_zero_localization'); import generate
generate.run_box('1/1000000','999999/1000000','0','100', write=False)
PY

# Geometry probe (sorry-free except the labeled effective-rate example)
cd telperion/examples/zeta_zero_localization/lean
/Users/peterwmurphy/.elan/bin/lake exe cache get
/Users/peterwmurphy/.elan/bin/lake env lean DvpBoxProbe.lean   # only warning: line ~131 labeled sorry
```
