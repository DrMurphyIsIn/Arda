# `enclosure_tree` -- rational enclosures of expression trees over transcendental atoms (2026-09-22)

`conjecture1_proved = False`. Everything below is a finite rational arithmetic fact about real
constants (`lo <= E <= hi` for a closed-form constant `E`), plus one elementary real inequality (the
log/sqrt face). Nothing here says anything about the zeros of zeta, and nothing here is a step
toward RH.

Source: `SHAPES_AUDIT_48H_2026-09-22.md` section 2, rank 1 ("about 30 sites, all four audits"),
merging `SHAPES_AUDIT_A_MISSIONS_2026-09-22.md` N2 (`RadicalExpressionEnclosure`), N3
(`LogTaylorBracket`) and N4 (`AtomPolynomialEnclosure`) with the fold-ins B C2 (`sqrt_of_bracketed`),
C 4.7 (`log y <= c y^alpha`) and D 4 (the `pi` and `arctan` faces of `transcendental_enclosure`).
Build order: sprint 1, item 1. Module: `src/telperion/emit_enclosure_tree.py`.

## The shape that had no certificate type

Every island that needs a numeric constant writes the same few lines by hand: a Mathlib fact per
atom (`Real.pi_gt_d4`, `Real.log_two_gt_d9`, `Real.abs_log_sub_add_sum_range_le`, `Real.sq_sqrt`),
then `nlinarith` or `linarith` to push the atom brackets through `+ - * /`. The four cluster audits
found about thirty such sites; three independent candidates (A N2, N3, N4) and three fold-ins turned
out to be one object: an interval fold over an expression tree, with one Mathlib fact per leaf.

| site | what it proves | faces used |
|---|---|---|
| `LiLadderHeight.lean` `li_rungs_of_bands_4000_upto` (the audit's `:602-609`) | `n <= 18848 -> (n + 1 : R) <= 3 pi 4000 / 2` via `pi_gt_d4` | `pi`, rate |
| `LiLadderSharp.lean` `li_rungs_of_bands_4000_upto_sharp` (`:154-161`) | `n <= 25128 -> (n + 1 : R) <= 2 pi (4000 - 1/2)` via `pi_gt_d6` | `pi`, rate |
| `quasicrystal/.../LeakageDictionary.lean:276-359` | `sqrt 5`, `sqrt (10 - 2 sqrt 5)`, the DH constant `kappa`, `log (3/2)`, `log 2`, `log 3`, `log 6` | `sqrt` (nested), `/`, Taylor `log`, `log 2`, fold |
| `E6Bridge11.lean:1063-1099, 1437-1455`, `E6Bridge16.lean:341-350, 467, 681-685, 770-790` | `sqrt (2 pi) <= 2.51`, `sqrt 2 <= 1.5`, `pi^2/6 <= 2`, `1.648 <= e^(1/2)`, ... | `sqrt` of a bracketed radicand, `^`, `exp` |
| `E6Bridge23.lean:123-132`, `E6Bridge16.lean:330-333` | `log (y + 4) <= 6 sqrt y` (`y >= 1`), `log n <= 2 sqrt n` | log/sqrt face |
| `LiFacePrelude.lean:244` (was `LiLadderHeight.lean:303-315`), `E6Bridge28.lean:200-231` | `|arctan x| <= |x|`, `x/2 <= arctan x` on `[0, 1]` | `arctan` (the two fixed lemmas, inlined) |

## Statement family

One family, two faces.

**The tree face.** For an expression tree `E` over `{+, -, *, /, ^, sqrt, log, exp, pi, arctan,
rational constants}` whose `log` and `exp` arguments are rational constants:

```
theorem nm : (lo : R) <₁ E ∧ E <₂ (hi : R)          -- each <ᵢ is `<` or `≤`, decided per side
theorem nm_rate (n : ℕ) (hn : n ≤ cap) : (n + 1 : R) ≤ E      -- optional, the D-audit pi face
```

The tree is written with the `node_*` constructors (`node_pi`, `node_sqrt`, `node_log`, `node_exp`,
`node_arctan`, `node_add`, `node_sub`, `node_mul`, `node_div`, `node_neg`, `node_pow`, `node_rat`).
Any node may carry its own claimed bracket and a Lean name; parents consume the CLAIM (what the child's
theorem states), never a tighter private value.

**The log/sqrt face** (C 4.7): `theorem nm {y : R} (hy : (y0 : R) ≤ y) : Real.log (y + a) ≤ c *
Real.sqrt y`, for rationals `a >= 0`, `y0 > 0`, `k >= 1` with `(k^2 - 1) y0 >= a` and `c >= 2k`
(`a = 0` needs no `k`). Defaults reproduce the island constants: `(a, y0) = (4, 1)` gives the least
integer `k = 3` and `c = 6` (`E6Bridge23.log_add_four_le`); `a = 0` gives `c = 2` (`E6Bridge16`).

## The certificate

`EnclosureTreeCert(root, order, rate_cap, pi_digits, order_level)`; the root is a tree of
`ResolvedNode`s. Untrusted Python computes, in exact rationals (`sympy.Rational` / `Fraction`; floats
refused at the door):

1. **Per atom, one Mathlib fact.** `pi`: the rung `d0` (`pi_gt_three`, `pi_lt_four`), `d2`, `d4`,
   `d6` or `d20` (`pi_gt_dN`, `pi_lt_dN`); an unpinned rung is searched ASCENDING and the least rung
   that carries every claim and the rate cap is recorded. `log 2`: `log_two_{gt,lt}_d9`. `log r`
   with `|1 - r| < 1`: the exact order-`n` box `[-S - rad, -S + rad]` of
   `abs_log_sub_add_sum_range_le` at `x = 1 - r`, `S = sum_(i<n) x^(i+1)/(i+1)`,
   `rad = |x|^(n+1)/(1 - |x|)`; a claimed atom takes the LEAST order whose box carries the claim.
   `log r` elsewhere: a FOLD `r = prod f_i^c_i` into atoms, box `sum c_i [lo_i, hi_i]`. `exp x`,
   `0 < |x| <= 1`: the `Real.exp_bound` box (the `emit_exp_enclosure` arithmetic, re-derived; a test
   asserts the two agree). `sqrt X`: a claimed side is checked EXACTLY by rational squares
   (`lo^2 <= X.lo`, `X.hi <= hi^2`; a claim tighter than any grid is fine when its square is right);
   an unclaimed side is derived by exact integer square roots on a `10^-12` grid, rounded outward.
   `arctan X`: `[-m, m]` with `m = max |X|` (`abs` route), or `[X.lo/2, X.hi]` when `X` lies in
   `[0, 1]` (`half` route), the cheaper route when both carry the claim.
2. **Per operation, the exact interval fold** from the children's stated brackets: `+`, `-`,
   negation and constant scaling are exact affine maps; a product of two non-constants takes the
   min/max of the four corner products; a quotient needs a denominator interval `> 0`; `x^k` needs a
   base interval `>= 0`.
3. **Strictness, per side.** A side may be stated `<` iff the fold gives slack there or the endpoint
   is OPEN. Openness starts at the strict Mathlib atoms (`pi`, `log 2`) and propagates through `+`,
   `-`, negation, constant scaling and the fold; every other operation is treated as closed, which can
   only cause a refusal, never an unsound acceptance. `strict=None` (default) states each side as
   strongly as it is provable; `strict=True` demands both and refuses otherwise; `strict=False`
   states both with `<=`.
4. **The order-level search.** An unpinned, unclaimed Taylor atom takes the default order (24 for
   `log`, 14 for `exp`); when the root claim or the rate cap needs more, the levels 32, 48, 64 are
   tried (jointly with the pi ladder) and the first that works is recorded.
5. **Which nodes emit a theorem.** The root; every named or claimed node; every atom, `sqrt`,
   `arctan` and `^`; every product of two non-constants and every quotient by a non-constant. A
   LINEAR node (`+`, `-`, negation, product with a constant, quotient by a constant) emits nothing:
   its parent's `linarith` sees through it to the nearest emitting descendants (the proof "frontier").
   Rational-constant subtrees never emit; `norm_num`/`linarith` evaluate them inline. Structurally
   equal nodes (same op, parameters, bracket, strictness and name) are proved ONCE per family and
   consumed by name, across instances.

The emitted proof term is fully determined by the certificate: every tactic is `linarith` on named
hypotheses, `norm_num` on rational literals, or a named rewrite, except the `sqrt` atom, which keeps
the hand proofs' `nlinarith [h2, hn, <frontier bounds>]` (a degree-2 product search over at most a
handful of named facts).

## Tactic skeleton (the hand proofs' own lines)

```
-- pi atom (rung dN)
constructor <;> linarith [Real.pi_gt_dN, Real.pi_lt_dN]
-- log 2 atom (LeakageDictionary.log_two_bounds)
have h1 := Real.log_two_gt_d9; have h2 := Real.log_two_lt_d9; norm_num at h1 h2
constructor <;> linarith
-- Taylor log at order n (LeakageDictionary.log_three_halves_bounds, + one hardening line)
have hx : |(x : R)| < 1 := by rw [abs_lt]; constructor <;> norm_num
have h := Real.abs_log_sub_add_sum_range_le hx n
rw [show (1 : R) - x = r by norm_num] at h
generalize Real.log r = L at h ⊢          -- norm_num below can no longer rewrite log r
rw [abs_le] at h
norm_num [Finset.sum_range_succ] at h
constructor <;> linarith [h.1, h.2]
-- fold (LeakageDictionary.log_three_bounds: backwards, so `3` inside `3/2` is never rewritten)
have hfold : Real.log 6 = Real.log 2 + Real.log 2 + Real.log (3 / 2) := by
  rw [← Real.log_mul (by norm_num : (2 : R) ≠ 0) (by norm_num : (2 : R) ≠ 0)]
  rw [← Real.log_mul (by norm_num : (2 * 2 : R) ≠ 0) (by norm_num : ((3 / 2) : R) ≠ 0)]
  norm_num
rw [hfold]; constructor <;> linarith
-- sqrt (LeakageDictionary.sqrt_five_bounds / sqrt_inner_bounds)
have harg : (0 : R) ≤ X := by linarith
have h2 : Real.sqrt X ^ 2 = X := Real.sq_sqrt harg
have hn : (0 : R) ≤ Real.sqrt X := Real.sqrt_nonneg _
constructor <;> nlinarith [h2, hn, h0lo, h0hi]
-- quotient by a non-constant (LeakageDictionary.dhKappa_gt / _lt)
have hden : (0 : R) < B := by linarith
constructor
· rw [lt_div_iff₀ hden]; linarith          -- le_div_iff₀ on a non-strict side
· rw [div_lt_iff₀ hden]; linarith
-- product of two non-constants: the four McCormick corner facts (a linear program, no search)
have hm1 : (0 : R) ≤ (A - alo) * (B - blo) := mul_nonneg (by linarith) (by linarith)
... hm2, hm3, hm4 ...
constructor <;> linarith [hm1, hm2, hm3, hm4]
-- power on a nonnegative base
have hl : (clo : R) ^ k ≤ C ^ k := pow_le_pow_left₀ hnn (by linarith) k
have hh : C ^ k ≤ (chi : R) ^ k := pow_le_pow_left₀ hup (by linarith) k
constructor <;> linarith
-- exp (the emit_exp_enclosure route), arctan (abs_arctan_le_abs, half_le_arctan inlined),
-- linear nodes (constructor <;> linarith), the rate corollary:
obtain ⟨hlo, _hhi⟩ := nm
have hn' : (n : R) ≤ (cap : R) := by exact_mod_cast hn
linarith
```

The only departure from the hand proofs is the `generalize` line in the Taylor route: it stops
`norm_num` from normalizing `Real.log r` in `h` (for instance `Real.log (1/2)` into `-Real.log 2`)
while the goal keeps the original atom. It is a hardening, kernel-checked on `log (1/2)`.

## Refusals (the forge face)

| phantom | why it is refused |
|---|---|
| a claimed bracket the exact fold does not imply, at ANY node | the forge case: a child's claim is what its theorem states; the kernel would reject it (the negative control) |
| a strict side with neither slack nor an open endpoint | `<` needs room the fold does not give |
| an inverted bracket `lo > hi` | ill-formed |
| a radicand interval not `>= 0` | `Real.sqrt` of a negative is `0` in Mathlib: an enclosure would be a phantom |
| a denominator interval containing `0`, or strictly negative | unbounded quotient / the `le_div_iff0` route needs `0 < den` (negate both instead) |
| `log r` with `r <= 0`, or `r = 1` | out of domain / `log 1 = 0` carries no transcendental content |
| `log r` with `|1 - r| >= 1` and no factorisation | outside the Taylor radius (A N3 d) |
| Taylor orders outside `1..64`; a Taylor order on `log 2` | the `Finset.sum_range_succ` cost cliff; `log 2` is Mathlib's atom |
| a fold whose factors do not multiply to `r`; a multiplicity `<= 0` or `> 8`; a factor `<= 0`; a one-log fold; more than 8 factors | the fold identity would be false / the repeated `log_mul` cost cliff |
| `exp` at `|x| > 1`, or at `x = 0` | outside `Real.exp_bound` (the halving identity is a follow-on) / no content |
| a base interval not `>= 0` under a power; an exponent outside `2..8` | the monotone route needs `0 <= base` (split the sign case; the audit's "atom straddling 0 under a power") |
| a `pi` rung off Mathlib's ladder; a claim no rung up to d20 carries | there is no such Mathlib fact |
| a rate cap the certified lower bound does not reach (`cap + 1 > lo`) | the ladder stops short; the emitter never rounds up |
| a rational-only tree; a claim or name on a rational-constant subtree; a constant factor 0 | a reflexive `q <= q` stub is the decorative shape the lint refuses |
| floats, sympy Floats, bools, non-rationals, non-identifier names, trees above 64 nodes, unknown spec keys, a root named differently from its instance | exactness and hygiene |
| (log/sqrt) `alpha != 1/2`, `a < 0`, `y0 <= 0`, `k < 1`, `(k^2 - 1) y0 < a`, `c < 2k` | outside the one route the face proves |

Every refusal has its own test in `tests/test_emit_enclosure_tree.py`.

## Negative control (`negctrl_adapters/adapter_enclosure_tree.py`)

FALSE twin: the dogfood `pi`-face certificate with its root lower bound moved from 18849 to 18850
and its cap from 18848 to 18849, hand-minted past Layer 1 (`dataclasses.replace` on the honest root,
emission order recomputed). `6000 pi = 18849.5559...` (decided exactly in the test against Mathlib's
own `pi_lt_d20`), so `18850 < 3 * pi * 4000 / 2` is FALSE and so is the rate statement at `n = 18849`.
The kernel rejects it: the root `linarith` from `6283/2000 < Real.pi` fails. TRUE twin: the honest
certificate, compiles over `import Mathlib` alone with `[propext, Classical.choice, Quot.sound]`.
The two texts differ only in those literals and the header comments that quote them
(`tests/test_negctrl_enclosure_tree.py` pins this). Run by hand on the li_positivity island: FALSE
twin `exit 1` (`linarith failed`, declarations fall back to `sorryAx`), TRUE twin `exit 0`, clean.

## Dogfood

Generated by `examples/li_positivity/dogfood_enclosure_tree.py` (`--check` for drift; the test
`test_dogfood_files_are_regenerable_byte_for_byte` pins the bytes of both files).

**`examples/li_positivity/lean/Probes/Dogfood_enclosure_tree.lean`** (imports `LiLadderHeight`,
`LiLadderSharp`; compiled on the island, 40 theorems, every one
`[propext, Classical.choice, Quot.sound]`).  It is registered as the `DogfoodEnclosureTree`
`lean_lib` and imported by `AxiomGuardLiPositivity.lean`, which anchors 19 of its theorems, so the
island's CI `lake build` compiles it and the guard step checks it:

| emitted | regenerates | kernel cross-check appended |
|---|---|---|
| `li_height_rate_4000_n0`, `li_height_rate_4000`, `li_height_rate_4000_rate` | the `pi_gt_d4` step of `li_rungs_of_bands_4000_upto` (rung d4 found by the search) | `LiLadderHeight.li_rungs_of_bands_4000 hall n (li_height_rate_4000_rate n hn)` proves the original statement |
| `li_sharp_rate_4000_n0`, `li_sharp_rate_4000`, `li_sharp_rate_4000_rate` | the `pi_gt_d6` step of `li_rungs_of_bands_4000_upto_sharp` (rung d6 found by the search; d4 is one rung short, a test pins this) | `LiLadderHeight.li_rungs_of_bands_4000_sharp hall n (li_sharp_rate_4000_rate n hn)` |
| `qc_*` (7 theorems) | the nine `LeakageDictionary` bracket lemmas, original claims, compiled on this island's Mathlib | see the quasicrystal probe |
| `rt_*` (route coverage) | every skeleton the sites above do not exercise: `exp` (positive and negative point), both `arctan` routes, McCormick product, power, negation with an open endpoint, a Taylor `log (1/2)`, the order-level search (level 32), a shared-root alias, a named linear node, a general non-strict quotient, the B C2 / C 2.10 numerics `sqrt (2 pi) <= 2.51`, `sqrt (32 pi) <= 11`, `sqrt 2 <= 1.5`, `pi^2 / 6 <= 2`, `1.648 <= e^(1/2)`, and the C 4.7 log/sqrt face at both island shapes | none needed (Mathlib-only statements) |

**`examples/quasicrystal/lean/Probes/Dogfood_enclosure_tree.lean`** (imports `LeakageDictionary`):
the nine lemmas as seven emitted theorems (`dhKappa_gt`/`_lt`/`_bounds` are one two-sided enclosure
of the unfolded constant), chained like the hand proofs (`sqrt 5` consumed by name by the inner
radical and the DH quotient; `log 2` and `log (3/2)` by both folds), then cross-checks BOTH ways:
each of the nine ORIGINAL statements (verbatim; a test re-reads the island source) proved from the
emitted theorems, and each emitted statement proved from the originals. The quasicrystal island
(v4.32.0) has no built `.lake` in this lane, so the file was compiled as a SHADOW on the li island's
Mathlib: the original `LeakageDictionary` section 5 copied verbatim into `namespace Quasicrystal` in
place of the import; `exit 0`, the seven theorems axiom-clean, all sixteen cross-checks green. Every
Mathlib name the emitted Lean uses was checked present in both the v4.32.0 and v4.34 pins. The lead
should still compile it on its own island:

```
cd telperion/examples/quasicrystal/lean && lake env lean Probes/Dogfood_enclosure_tree.lean
```

## What it does NOT do

* It proves nothing about zeros or about RH; every dogfood instance is already kernel-checked by hand
  on its island. The value is regeneration, the kernel gate on the next island, and the refusals.
* It does not bracket `log` or `exp` of a NON-rational argument: `log pi <= 1.3863`
  (`E6Bridge11.lean:1066-1073`, `E6Bridge16.lean:783-790`) needs the monotone route through
  `log 4 = 2 log 2`, which stays with `log_combination`; the audit's statement family fixes `log`
  arguments to positive rationals.
* It refuses `exp` at `|x| > 1`: `e^-6 <= 1/400` and `e^-16 <= 1/8000000` (`E6Bridge16.lean:341-347,
  776-782`) need the halving identity `exp x = (exp (x/2))^2`, a deliberate follow-on (as in
  `emit_exp_enclosure`).
* It has no symbolic parameters: `sqrt lam <= 1/3000` and `sqrt (32 pi lam) <= 11/3000`
  (`E6Bridge11.lean:1063-1065, 1077-1083`) carry `lam`; only constant trees are enclosed.
* Endpoints of general products, quotients, powers, square roots (grid side) and arctangents are
  treated as CLOSED even when the true value is interior; a strict claim there needs slack. Even
  powers of a sign-straddling base are refused, not split (write the product with `mul`, whose
  McCormick bound is valid for any signs, or split the case).
* With only ONE side claimed on a Taylor atom, the least-fitting order is the least one whose box
  carries that side, and the other side adopts that order's (possibly weak) bound: pin `order` or
  claim both sides for a tight two-sided bracket (a test pins this rule).
* The `arctan` half route covers `[0, 1]` only (no mirrored `[-1, 0]` route; the `abs` route covers
  it loosely), and the monotone half lemma is inlined per node, about 20 lines each.
* The log/sqrt face is `alpha = 1/2` only (the only exponent with island instances).
* It does not touch `LiLadderHeight`, `LiLadderSharp` or `LeakageDictionary`; replacing the hand
  steps by the emitted lemmas (the standing-order REGEN of section 3, rows 1 and 3) is the lead's
  call once the probes are green on CI. The A N4 polynomial consumer `LeakageInstances.lean:173-188`
  (`leak_dh_enclosure`) is the next dogfood target; it was not regenerated here.
