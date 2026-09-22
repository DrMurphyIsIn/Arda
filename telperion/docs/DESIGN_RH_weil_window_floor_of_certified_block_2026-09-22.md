# DESIGN MEMO: RH_weil_window_floor_of_certified_block (rh campaign)

Date: 2026-09-22. Worktree `arda-goal-weil`, branch `mm/gauss-window`.
Node: `missions/rh/nodes/RH_weil_window_floor_of_certified_block.toml`
(created 2026-09-19, `kind = "lemma"`, `status = "draft"`, no `[proof]` block, zero attempts).
Statement: `missions/rh/lean/Statements/RH_weil_window_floor_of_certified_block.lean`.
Vocabulary: `missions/rh/lean/Statements/RHDefs.lean`, namespace `WeilWindow`.
Prior memo: `docs/ZHU_WINDOW_POSITIVITY_IMPORT_2026-09-19.md` (the 43 KB import memo; its
section 4.4 is the seam verdict this memo builds on and does not repeat).

**conjecture1_proved = False. Nothing in this memo, in the node, or in either option below proves,
approaches, weakens or reduces the Riemann Hypothesis.** The RH-equivalent clause
`forall L, WindowFloor L 0` (Weil 1952; Bombieri 2000) is out of scope and untouched. The
RH-equivalent registry nodes (`RH_conjecture`, `MM_zeta_comb_membership`) are out of scope.

---

## 0. Verdict in one paragraph

This node is **design, not provable**, and the design decision it needs is the lead's, not a Lean
agent's. The theorem is unprovable *by construction*: all four analytic inputs are declared
`opaque ... : Prop` with no axiomatised content (RHDefs.lean, the `WeilWindow` block), so a proof
would have to derive `WindowFloor L (min lam0 (beta - epsD) - epsB)` from `hbpos`, `hcut`, `hpos`
alone, and that is false in general (section 2). No Lean session can move it; no artifact exists to
grant (`WindowFormFloorInstances.lean` proves only the rounding lemma `windowFloor_of_le`, a
different statement that is already CI-guarded); there is no compute to plan (Zhu's Arb
certification is external and finished at `L = 0.8`); and it is not a nogo, because
`WindowFloor L lam` at fixed `L` with `lam > 0` is a legitimate finite fragment. What is missing is
a **lead decision between two honest options** (section 3): freeze the node as a documentary
conditional record, or authorise a short addendum that registers the ONLY two kernel-provable
pieces of Zhu Thm 1.1 as new island-side nodes (section 4, with exact statements, route, Mathlib
inventory verified against the island's v4.32.0 pin, and line estimates). `effort_lines = 400` in
the triage refers to option (2); the node as stated has effort 0.

---

## 1. The node as it stands (facts, all re-verified today)

| item | state |
|---|---|
| toml | `status = "draft"`, `depends_on = ["RH_limit_explicit_formula"]`, no `[proof]`, `updated = 2026-09-19` |
| statement module | header says STATED ONLY; body ends in a `sorry` placeholder; `import Mathlib` + `Statements.RHDefs` |
| attempts | `grep -c RH_weil_window_floor_of_certified_block missions/rh/attempts.jsonl` = 0 |
| registry status | `mission status rh` lists it under draft leaves; `mission open-leaves rh` currently prints nothing at all for the campaign, so the node is not being counted as an open leaf today |
| island | none hosts it. `weil_form_enclosure` (Mathlib v4.32.0) has no `.lake` in this worktree |
| sibling build | `~/arda-mm-tool-weil-form-enclosure/.../weil_form_enclosure/lean/.lake` exists, BUT it is a **symlink** to `~/arda-million/telperion/examples/quasicrystal/lean/.lake` (shared cache; Mathlib oleans present at rev `81a5d257`). `lake-manifest.json` and `lean-toolchain` are byte-identical to ours; the sibling `lakefile.toml` predates the `WindowFormFloorInstances` and `AxiomGuardWindowFormFloor` libs (diff: two `[[lean_lib]]` blocks and the `defaultTargets` line) |
| existing Lean for eq. (13) / Lemma 5.2 | none. grep over `examples/*/lean/*.lean`, `examples/*/*.lean`, `missions/*/lean/Statements/*.lean` for `fromBlocks`, `Cholesky`, `IsHermitian.eigenvalues`, `lambda_min`, `two-block`: zero hits |
| emitter | `src/telperion/emit_window_form_floor.py` and `examples/window_form_floor/generate.py` exist; they emit only `windowFloor_of_le` instances (`zhu_window_floor_L08_T200`, `_T150`) |

The statement, verbatim in shape:

```lean
theorem weil_window_floor_of_certified_block
    (L Tsharp A beta lam0 epsD epsB : ℝ) (N : ℕ)
    (hA : A = WeilWindow.combMass L)
    (hbeta : beta = WeilWindow.betaStar L Tsharp)
    (hbpos : 0 < beta)
    (hcut : Real.exp 1 * L * Tsharp / 2 ≤ 2 * (N : ℝ))
    (hQrep : WeilWindow.SymbolRepresentation L)                     -- opaque
    (henv : WeilWindow.EnvelopeBound)                                -- opaque
    (hloc : WeilWindow.LegendreLocalization L Tsharp N epsD epsB)   -- opaque
    (hhead : WeilWindow.ReducedHeadFloor L Tsharp lam0 N)           -- opaque
    (hepsD : 0 ≤ epsD) (hepsB : 0 ≤ epsB)
    (hpos : 0 < min lam0 (beta - epsD) - epsB) :
    WeilWindow.WindowFloor L (min lam0 (beta - epsD) - epsB)
```

with, in `RHDefs.lean`:

```lean
opaque SymbolRepresentation (L : ℝ) : Prop
opaque EnvelopeBound : Prop
opaque LegendreLocalization (L Tsharp : ℝ) (N : ℕ) (epsD epsB : ℝ) : Prop
opaque ReducedHeadFloor (L Tsharp lam0 : ℝ) (N : ℕ) : Prop
```

---

## 2. Why the node is unprovable as stated (and why that is deliberate)

An `opaque` Prop has no definitional content: nothing unfolds, no lemma about it exists, and it
cannot be shown false (it is consistent to instantiate each of the four as `True`). So any proof
term of the theorem is uniform in the four opaques, and would therefore also prove the statement
with all four hypotheses replaced by `True`, i.e.

```
forall L lam, 0 < lam -> (finite side conditions) -> WindowFloor L lam
```

with `lam = min lam0 (beta - epsD) - epsB` and `lam0` unconstrained. That is false: pick any
nonzero smooth bump `f` supported in `[-L, L]` (they exist; import memo sec 5.3 probe 1); the right
side `(weilForm (autocorr f)).re` is one fixed real, `∫ ‖f‖²` is strictly positive, so
`lam * ∫ ‖f‖² ≤ Q(f)` fails once `lam0` (hence `lam`) is large. Therefore the theorem has no proof,
and it has no proof for a structural reason, not for lack of effort.

This is exactly what the import memo intended (sec 4.4: "cannot be proved with what is available";
sec 5.1: "giving them fake definitions would let the node be closed for the wrong reason. A
certified NUMBER must not masquerade as a proved THEOREM"). The node is a **conditional record**:
it fixes, in the registry's own vocabulary, what Zhu Theorem 1.1 assumes and what it concludes, so
that no later node can cite "Zhu's 8.9e-18" as if it were a theorem on `main`.

Consequences for orchestration:

- Do not dispatch a Lean agent to this node in any session. It will either fail, or (worse) be
  tempted to replace an opaque with a definition, which is forbidden by the memo's design.
- Do not count it as an open leaf. It is not a leaf that can close.
- A change of `status` to `proved` is unreachable **even in principle** without a registry
  trust-seam policy, because `ReducedHeadFloor` is an Arb interval-Cholesky enclosure of a
  200 x 200 matrix whose entries are quadratures of the Weil symbol; the kernel can never own the
  enclosure, only its consequences (the same discipline as the `henc` seam in
  `emit_weil_form_enclosure.py` and the Li ladder).

---

## 3. The lead decision: two honest options

### Option (1): freeze as a documentary conditional node

Leave `status = "draft"`, no `[proof]`, no attempts. Add nothing. Treat it as a permanent
conditional/documentary node excluded from open-leaves counting (it already is not listed).

- Cost: zero.
- What it buys: the registry keeps a precise, vocabulary-mirrored record of the Zhu reduction and
  its four undischarged inputs, plus the barrier (Thm 1.4) that closes the route past support ~3.2.
  The emitter's anti-`A_eff` re-derivation discipline is already live and CI-guarded.
- What it forgoes: two small, genuinely kernel-ownable linear-algebra theorems remain unformalised,
  and the seam diagram keeps two arrows marked "provable" rather than "proved".
- Recommended if the lead's priority is the Li ladder / Weil dictionary threads. Nothing here is
  on the critical path of any proved node.

### Option (2): a short addendum registering the two elementary pieces

Authorise two new nodes on the `weil_form_enclosure` island (section 4). They are pure finite
linear algebra, no analysis, no zeta, no `WindowFloor`; they consume only `Matrix` vocabulary and
would be the first kernel theorems in the seam chain other than the rounding lemma.

- Cost: one reflink copy + one incremental lake build (minutes), then roughly 350-450 Lean lines
  by a Lean agent, plus the lead's registry ops (add, link, lakefile edit, AxiomGuard lines).
- What it buys: the two "[PROVABLE]" arrows in the sec 4.4 diagram become "[PROVED, island]",
  and any future certificate that ships a PSD block (not only Zhu's) can consume them.
- What it does NOT buy: any change to this node's status; any statement about Zhu's actual matrix
  (its entries are non-rational quadratures; the instantiation stays behind the trust seam); any
  RH content whatsoever.
- Recommended only if the lead wants the seam's kernel-ownable fraction maximised for its own
  sake, or wants reusable PSD-certificate lemmas for other emitters (`weil_form_enclosure`'s 2x2
  Gram block is the obvious second customer).

Either option is defensible. The one thing this memo argues against is a third, dishonest option:
proving the node by weakening it (e.g. replacing an opaque with `True`-like content, or restating
the conclusion so that it follows from `hpos` alone). That would close a node for the wrong reason
and is exactly the failure mode the import memo was written to prevent.

---

## 4. Option (2) design: the two kernel-provable pieces

### 4.1 Vocabulary decision: Loewner form, not eigenvalues

Zhu states eq. (13) as `lambda_min(M) >= min(lambda_min A, lambda_min D) - ||B||` and Lemma 5.2 as
`lambda_min(M') >= -(r + s)`. The natural Lean form is **not** `Matrix.IsHermitian.eigenvalues`
but the Loewner (shifted-PSD) form

```
(M - c • 1).PosSemidef        equivalently   forall x, c * ‖x‖² ≤ Re (star x ⬝ᵥ (M *ᵥ x))
```

Reasons, all verified against the island's Mathlib rev `81a5d257` (v4.32.0):

- `Matrix.IsHermitian.posSemidef_iff_eigenvalues_nonneg` exists (`Mathlib/Analysis/Matrix/PosDef.lean:34`),
  so the eigenvalue reading `forall i, c ≤ hM.eigenvalues i` follows from `(M - c • 1).PosSemidef`
  *only if* one also has an eigenvalue-shift lemma (`eigenvalues (M - c • 1) = eigenvalues M - c`
  up to permutation). grep finds no such lemma in this Mathlib; writing it costs ~150 lines and
  buys nothing the certificate consumes. Skip it; record it as an optional obligation O5.
- The Rayleigh machinery Mathlib does have is on `LinearMap.IsSymmetric` over `EuclideanSpace`
  (`Mathlib/Analysis/InnerProductSpace/Rayleigh.lean`: `hasEigenvalue_iInf_of_finiteDimensional`,
  `iInf_rayleigh_eq_iInf_rayleigh_sphere`), bridged by `Matrix.isHermitian_iff_isSymmetric`
  (`Mathlib/Analysis/Matrix/Hermitian.lean:62`). Using it means converting every matrix statement
  through `toEuclideanLin`; the quadratic-form route below avoids that entirely.
- The certificate side already speaks Loewner: Zhu's Cholesky is run on `A~ - (lam0 + c_err) I`.

Norm decision: Zhu's `||B||` is the l2 operator norm bounded by the Schur test
`sqrt(||B||_1 ||B||_inf)`. Mathlib has `linfty_opNorm_*` and `frobenius_*` as *local instances*
(`Mathlib/Analysis/Matrix/Normed.lean`) and no ready-made l2-operator-norm-of-a-matrix lemma. To
stay instance-free, state the coupling hypothesis **entrywise**:

```
hrow : forall i, ∑ j, ‖B i j‖ ≤ b        hcol : forall j, ∑ i, ‖B i j‖ ≤ b
```

and conclude with `- b`. This is the Schur test with `t = 1` (slightly weaker than
`sqrt(b1 * binf)` when the row and column sums differ; equal when they agree). Since `epsB` is a
`1e-100` overestimate in the certified run, the loss is irrelevant, and the emitter can supply
`b = max(||B||_1, ||B||_inf)` from the same data it already bounds.

### 4.2 The shared helper (Schur test on the quadratic form)

```lean
namespace BlockFloor
open Matrix Complex

/-- Schur test on the quadratic form: if every row and every column of `E` has absolute sum
    at most `r`, then `|star x ⬝ᵥ (E *ᵥ x)| ≤ r * ‖x‖²` with `‖x‖² = ∑ i, ‖x i‖ ^ 2`. -/
theorem abs_quadForm_le_of_rowcol {n : Type*} [Fintype n] (E : Matrix n n ℂ) (r : ℝ)
    (hrow : ∀ i, ∑ j, ‖E i j‖ ≤ r) (hcol : ∀ j, ∑ i, ‖E i j‖ ≤ r) (x : n → ℂ) :
    ‖star x ⬝ᵥ (E *ᵥ x)‖ ≤ r * ∑ i, ‖x i‖ ^ 2
```

Route: `star x ⬝ᵥ (E *ᵥ x) = ∑ i, ∑ j, conj (x i) * E i j * x j`; triangle inequality;
`‖x i‖ ‖x j‖ ≤ (‖x i‖² + ‖x j‖²) / 2`; split the double sum into the two halves and bound each by
`r * ∑ ‖x‖²` using `hrow` resp. `hcol` (with `Finset.sum_comm` for the second). Mathlib pieces:
`Matrix.dotProduct`, `Matrix.mulVec`, `Finset.sum_mul_sum`, `norm_sum_le`, `norm_mul`,
`Finset.sum_comm`, `Finset.sum_le_sum`, `two_mul_le_add_sq`. Purely finite, `ℂ` only through
`‖·‖`. **Estimate: 120-180 lines.** This is the piece with the real bookkeeping.

A bilinear variant (different `x`, `y`, rectangular `B : Matrix m n ℂ`) is what the two-block
bound needs:

```lean
theorem abs_bilin_le_of_rowcol {m n : Type*} [Fintype m] [Fintype n] (B : Matrix m n ℂ) (b : ℝ)
    (hrow : ∀ i, ∑ j, ‖B i j‖ ≤ b) (hcol : ∀ j, ∑ i, ‖B i j‖ ≤ b) (x : m → ℂ) (y : n → ℂ) :
    ‖star x ⬝ᵥ (B *ᵥ y)‖ ≤ b * ((∑ i, ‖x i‖ ^ 2 + ∑ j, ‖y j‖ ^ 2) / 2)
```

Same proof; prove this one first and derive the square case by `y := x`. **Estimate for the pair:
150-220 lines total.**

### 4.3 Node (a): the two-block least-eigenvalue bound, Zhu eq. (13)

Exact theorem in island vocabulary:

```lean
/-- Zhu arXiv:2608.24827 eq. (13), Loewner form.  For the Hermitian block matrix
    `M = fromBlocks A B Bᴴ D` with `A - a • 1` and `D - d • 1` positive semidefinite and the
    coupling `B` Schur-bounded by `b`, the whole matrix is bounded below by `min a d - b`.
    Pure finite linear algebra; says nothing about zeta.  conjecture1_proved = False. -/
theorem fromBlocks_loewner_floor {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (A : Matrix m m ℂ) (B : Matrix m n ℂ) (D : Matrix n n ℂ) (a d b : ℝ)
    (hA : (A - (a : ℂ) • 1).PosSemidef) (hD : (D - (d : ℂ) • 1).PosSemidef)
    (hrow : ∀ i, ∑ j, ‖B i j‖ ≤ b) (hcol : ∀ j, ∑ i, ‖B i j‖ ≤ b) :
    (fromBlocks A B Bᴴ D - ((min a d - b : ℝ) : ℂ) • 1).PosSemidef
```

Route (Zhu sec. 4, four lines on paper): for `x = Sum.elim u v`,
`star x ⬝ᵥ (M *ᵥ x) = star u ⬝ᵥ (A *ᵥ u) + 2 Re (star u ⬝ᵥ (B *ᵥ v)) + star v ⬝ᵥ (D *ᵥ v)`;
first and third terms are `≥ a ‖u‖²` and `≥ d ‖v‖²` by `hA`, `hD`; the cross term is
`≥ - b (‖u‖² + ‖v‖²)` by `abs_bilin_le_of_rowcol`; so the total is
`≥ (min a d - b)(‖u‖² + ‖v‖²) = (min a d - b) ‖x‖²`.

Named obligations:

| id | obligation | Mathlib support (verified names) | est. lines |
|---|---|---|---|
| O1 | quadratic form of `fromBlocks` on `Sum.elim u v` splits into the three terms | `Matrix.fromBlocks_mulVec`, `Matrix.dotProduct` over `Sum` via `Fintype.sum_sum_type` (the `to_additive` of `Fintype.prod_sum_type`, `Data/Fintype/BigOperators.lean:265`), `Sum.elim_inl/inr`, `Matrix.conjTranspose_apply`; the `2 Re` collapse uses `Complex.add_conj` | 60-100 |
| O2 | Hermitian-ness of `M - c • 1` | `Matrix.IsHermitian.fromBlocks` (`LinearAlgebra/Matrix/Hermitian.lean:146`), `isHermitian_sub`, `isHermitian_smul`-style lemmas, `isHermitian_one`; `hA.1`, `hD.1` give `A`, `D` Hermitian after cancelling the shift | 20-40 |
| O3 | PSD from the quadratic form | `Matrix.PosSemidef.of_dotProduct_mulVec_nonneg` (`LinearAlgebra/Matrix/PosDef.lean:308`), `posSemidef_iff_dotProduct_mulVec`; the real-part reading via `IsHermitian.im_star_dotProduct_mulVec_self` (`Analysis/Matrix/Hermitian.lean:65`) | 30-60 |
| O4 | shifted-PSD hypotheses unpack to `a ‖u‖² ≤ Re(star u ⬝ᵥ (A *ᵥ u))` | `PosSemidef.dotProduct_mulVec_nonneg` (`:305`) on `A - a • 1`, plus `sub_mulVec`, `smul_mulVec`, `one_mulVec`, `dotProduct_smul` | 30-50 |
| O5 (optional, skip) | eigenvalue reading `forall i, min a d - b ≤ hM.eigenvalues i` | needs an eigenvalue-shift lemma absent from this Mathlib; `posSemidef_iff_eigenvalues_nonneg` covers only the unshifted case | 0 (or ~150) |

**Total for node (a), including its share of 4.2: 150-250 lines**, which matches the triage.

### 4.4 Node (b): the Cholesky residual floor, Zhu Lemma 5.2

Zhu: if a floating-point Cholesky produces `L~` with `||M' - L~ L~^T||_inf ≤ r`, then
`lambda_min(M') ≥ -(r + s)`, where `s` is the product-rounding slack. In exact Lean arithmetic there
is no rounding, so `s` disappears from the abstract lemma and reappears only in how the emitter
chooses `r` (it must bound the residual of the *exact* product `L~ L~ᴴ` for the rational `L~` it
ships). Exact theorem:

```lean
/-- Zhu arXiv:2608.24827 Lemma 5.2, exact-arithmetic form.  If `E = M - Lt * Ltᴴ` has every row
    and column absolute sum at most `r`, then `M + r • 1` is positive semidefinite, i.e. `M` is
    bounded below by `-r` in Loewner order.  `Lt` is arbitrary (any approximate Cholesky factor);
    no property of `Lt` is trusted.  conjecture1_proved = False. -/
theorem loewner_floor_of_cholesky_residual {n : Type*} [Fintype n] [DecidableEq n]
    (M Lt : Matrix n n ℂ) (r : ℝ) (hM : M.IsHermitian)
    (hrow : ∀ i, ∑ j, ‖(M - Lt * Ltᴴ) i j‖ ≤ r) (hcol : ∀ j, ∑ i, ‖(M - Lt * Ltᴴ) i j‖ ≤ r) :
    (M + (r : ℂ) • 1).PosSemidef
```

Route: `M = Lt * Ltᴴ + E`; `Lt * Ltᴴ` is PSD by `Matrix.posSemidef_self_mul_conjTranspose`
(`LinearAlgebra/Matrix/PosDef.lean:365`); `Re(star x ⬝ᵥ (E *ᵥ x)) ≥ - r ‖x‖²` by
`abs_quadForm_le_of_rowcol`; add. (The `hcol` hypothesis is redundant when `hM` holds, since `E` is
then Hermitian and column sums equal row sums; keeping it costs nothing and drops the need to prove
that.) Named obligations:

| id | obligation | Mathlib support | est. lines |
|---|---|---|---|
| O6 | `Lt * Ltᴴ` PSD and the split `M = Lt * Ltᴴ + (M - Lt * Ltᴴ)` | `posSemidef_self_mul_conjTranspose`, `sub_add_cancel` | 10-20 |
| O7 | assembly with `PosSemidef.add` (`:102`) and the Schur helper | `PosSemidef.add`, `of_dotProduct_mulVec_nonneg`, helper from 4.2 | 40-80 |

**Total for node (b), reusing 4.2: 50-100 lines on top of the helper; 200-300 lines if the helper
is charged here instead.** Either way the two nodes together are **350-450 lines**, consistent with
`effort_lines = 400`.

What Mathlib's `LDL` file (`Mathlib/Analysis/Matrix/LDL.lean`: `LDL.lower`, `LDL.diag`,
`LDL.lower_conj_diag`) offers is the *exact* factorisation of a PosDef matrix; it is not needed and
should not be used, because Lemma 5.2's whole point is that `Lt` is an untrusted approximate factor.

### 4.5 What the two nodes would and would NOT establish

Would establish (kernel, axiom-clean expected `[propext, Classical.choice, Quot.sound]`):

- Two abstract finite-dimensional theorems about arbitrary complex Hermitian matrices. They are
  exactly the "[PROVABLE]" arrows of the sec 4.4 seam diagram.
- A reusable Schur-test quadratic-form helper, usable by the `weil_form_enclosure` 2x2 Gram
  certificates and by any future PSD-certificate emitter.

Would NOT establish:

- Anything about `WindowFloor`, `weilForm`, zeta, or Zhu's specific 200 x 200 matrix. The
  instantiation `M := A~ - (lam0 + c_err) I` has entries that are Gauss-Legendre quadratures of
  the Weil symbol `Psi_L` (Lemma 5.1, Bernstein ellipse), not rationals; the hypotheses `hrow`,
  `hcol` for that matrix can only be supplied by Arb, so **`ReducedHeadFloor` stays a trust seam
  after both nodes are proved.** The kernel would own the *shape* of the argument, never the number.
- Any change to `RH_weil_window_floor_of_certified_block` itself, whose four opaques (symbol
  representation, digamma envelope, Legendre localization, head floor) are untouched. Its status
  stays `draft`. The lead may optionally record a `uses`-style link from it to the two new nodes for
  documentation; it must not be recorded as a dependency that could ever let it close.
- Any RH content. A positive window floor at fixed `L` is what RH predicts and confirms nothing;
  the `forall L` clause is RH-equivalent and is not approached. conjecture1_proved = False.

### 4.6 Registry and island mechanics (lead operations; not performed by this agent)

1. **Reflink the cache, carefully.** The sibling `.lake` is a symlink into
   `~/arda-million/telperion/examples/quasicrystal/lean/.lake`. `cp -Rc` of the sibling path would
   copy the *symlink*, and building through it would mutate `arda-million`'s shared quasicrystal
   cache. Copy the target instead:
   `cp -Rc ~/arda-million/telperion/examples/quasicrystal/lean/.lake examples/weil_form_enclosure/lean/.lake`
   (or `cp -RcL` on the sibling path). Manifest and toolchain are already byte-identical, so lake
   will accept the package tree; the extra quasicrystal oleans in `build/lib` are inert.
2. **One incremental build** (the orchestrator serialises per island; never a second one):
   `lake build WindowFormFloorInstances AxiomGuardWindowFormFloor` from
   `examples/weil_form_enclosure/lean`. Mathlib oleans reuse; expect minutes, not the ~16 min
   Mathlib rebuild. Confirm `AxiomGuardWindowFormFloor` prints the three standard axioms for
   `windowFloor_of_le` and the two instances before trusting the copy.
3. **New lib**: add `[[lean_lib]] name = "BlockFloor" roots = ["BlockFloor"]` to `lakefile.toml`
   and to `defaultTargets`, plus `#print axioms` lines for the two theorems in a new
   `AxiomGuardBlockFloor.lean` (or appended to `AxiomGuardWindowFormFloor.lean`). The file header
   must state conjecture1_proved = False and that nothing in it concerns RH.
4. **Registry nodes** (lead adds; suggested names in the island namespace):
   `RH_block_floor_two_block` -> `BlockFloor.fromBlocks_loewner_floor`,
   `RH_block_floor_cholesky_residual` -> `BlockFloor.loewner_floor_of_cholesky_residual`,
   `kind = "lemma"`, island `weil_form_enclosure`, `depends_on = []`. Statements use only
   `Matrix`/`Finset`/`Complex` vocabulary, so the `statement_matches` gate is insensitive to the
   Statements-package pin (`de5ce8a9`) vs island pin (`v4.32.0`) mismatch; the `WeilWindow.*` vs
   `WindowFormFloorInstances.WindowFloor` naming question does not arise because neither theorem
   mentions `WindowFloor`.
5. **Then** a Lean agent writes `BlockFloor.lean` (sections 4.2-4.4), builds it as the island's
   single running build, and the lead grants against the axiom guard.

---

## 5. Blockers, restated for the ledger

1. Four hypotheses are `opaque` Props with zero content (`RHDefs.lean`, `WeilWindow` block). The
   theorem is unprovable as stated, deliberately; closing it would require replacing the opaques
   with real definitions, which is the forbidden move.
2. Missing Mathlib support for the analytic chain: `Re psi(1/4 + it/2) - log pi ≥ log(t/2pi) - 1/t`
   (Zhu Lemma 3.1, Binet's second formula; `Complex.digamma` exists but no Binet); half-line Parseval
   for the Weil symbol (eq. 2); spherical Bessel `|j_n(x)| ≤ x^n/(2n+1)!!` and the Legendre
   localization (eqs. 6, 12; spherical Bessel functions absent from Mathlib); Bernstein-ellipse
   Gauss-Legendre error (Lemma 5.1). Multi-week formalisation, not on any critical path.
3. `ReducedHeadFloor (lam0, epsD, epsB)` is an Arb/mpmath interval-Cholesky enclosure: a permanent
   non-kernel trust seam, so `status = proved` is unreachable without a registry trust-seam policy.
4. No Lean island hosts this theorem; `weil_form_enclosure` is unbuilt here; the one sibling build
   is a symlink into `arda-million`'s quasicrystal cache and its lakefile predates the two Zhu libs.
5. The two elementary lemmas are not registered and have no Lean anywhere (grep: zero hits).
6. Cross-package pin mismatch (`de5ce8a9` vs `v4.32.0`) means any artifact is island-side; harmless
   for pure-`Matrix` statements.
7. No attempts, no `[proof]`, nothing to blind-audit.

---

## 6. Recommendation

Default to **option (1)** unless the lead specifically wants reusable PSD-certificate lemmas on the
island. If option (2) is taken, do steps 4.6.1-4.6.2 first and gate the Lean agent on a green
`AxiomGuardWindowFormFloor` from the copied cache; write the Schur helper first, the two-block bound
second, the Cholesky residual third. Under no circumstances should any agent touch the four opaques
or the node's statement.

conjecture1_proved = False. No RH progress is claimed or implied.
