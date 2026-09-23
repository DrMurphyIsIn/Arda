# Audit testimony: RH_dbn_H0_eq_xi (rh campaign), blind auditor A2, 2026-09-22

- pass: true
- axioms_clean: true
- statement_byte_identical: true (modulo whitespace)
- conjecture1_proved = False

I audited blind. I did not read the design memo, the A1 testimony, or any author notes. My
inputs were the node TOML, the registry statement, RHDefs.lean, DBNDefs.lean, the artifact
DBNXi.lean and the modules it imports on the island.

## 1. Read-back of the registry statement (written before I opened the artifact)

Node `RH.dbn_H0_eq_xi` (kind lemma, status draft, no dependencies) has the statement module
`Statements.RH_dbn_H0_eq_xi`:

```
theorem dbn_H0_eq_xi (z : ℂ) :
    DBN.H 0 z = (1 / 8 : ℂ) * LiCriterion.riemannXi (1 / 2 + Complex.I * z / 2)
```

My reading: for every complex number z, the de Bruijn-Newman heat-flow function at time zero,
H_0(z) = ∫ over (0, ∞) of Φ(u) cos(zu) du, equals one eighth of the Riemann xi function at
s = 1/2 + iz/2. The definitions behind it are these.

- `Φ(u) = Σ_{n ∈ ℕ+} (2π²n⁴e^{9u} − 3πn²e^{5u}) exp(−πn²e^{4u})` (a real `tsum`).
- `HIntegrand t z u = e^{tu²} · Φ(u) · cos(zu)`. At t = 0 the first factor is 1.
- `H t z` is the Bochner integral of `HIntegrand t z` over `Ioi 0`. If the integrand were not
  integrable, Lean would return 0. DBNDefs proves it is integrable for every t and z, so the
  statement has real content.
- `riemannXi s = (1/2)·s·(s−1)·Λ₀(s) + 1/2`, where Λ₀ is Mathlib's entire
  `completedRiemannZeta₀`. Mathlib's `completedRiemannZeta_eq` (checked in my probe) gives
  Λ = Λ₀ − 1/s − 1/(1−s). For s not 0 or 1 this means
  riemannXi(s) = (1/2)s(s−1)Λ(s) + (1/2)[(s−1) − s] + 1/2 = (1/2)s(s−1)π^{−s/2}Γ(s/2)ζ(s).
  That is the classical ξ, and here it is total and entire, with riemannXi(0) = 1/2.

This is the classical Riemann/Titchmarsh 10.1 representation, in the Polymath15 eq. (3)
normalisation. It is an identity between two entire functions. It is not RH-equivalent and
says nothing about where zeros lie. The node title says "STATED ONLY, not proved". That
describes the registry node (draft), not the artifact.

I confirmed that the RHDefs.lean DBN block matches the island programmatically. `diff` of
DBNDefs.lean lines 40-41, 211-214, 408-409 and 413 against RHDefs.lean lines 100-101, 104-107,
110-111 and 114 came back empty. `LiCriterion.riemannXi` in RHDefs matches the pinned upstream
`.lake/packages/LiCriterion/Lc/LiCriterion/Basic.lean:1236-1237` exactly. `#print` in my probe
shows that the elaborated `DBN.H`, `DBN.HIntegrand`, `DBN.Φ` and `LiCriterion.riemannXi` used by
the artifact are these same definitions.

## 2. Statement comparison and the hardened gate

The artifact is `telperion/examples/dbn/lean/DBNXi.lean`, theorem `dbn_H0_eq_xi` at top level,
with no namespace:

```
theorem dbn_H0_eq_xi (z : ℂ) :
    DBN.H 0 z = (1 / 8 : ℂ) * LiCriterion.riemannXi (1 / 2 + Complex.I * z / 2) := by
```

Modulo whitespace it is identical to the registry body. The whitespace-collapsed registry body
is contained in the whitespace-collapsed artifact (True).

Hardened gate, run with `PYTHONPATH=telperion/src /usr/bin/python3`:
- `V._normalized_statement(node, root)` gave
  `'theorem dbn_H0_eq_xi (z : ℂ) : DBN.H 0 z = (1 / 8 : ℂ) * LiCriterion.riemannXi (1 / 2 + Complex.I * z / 2)'`.
- `V.statement_matches(DBNXi.lean text, normalized)` returned **True**.
- Negative control: the same artifact with the conclusion weakened to `... ∨ True := by` returns
  **False**, so the gate rejects a continued conclusion.
- `V.artifact_incompleteness_markers` returned `[]` for every island module in the import
  closure: DBNXi, DBNXiCos, DBNXiIBP, DBNXiRiemann, DBNGKernel and DBNDefs. The closure is
  DBNXi → {DBNXiCos, DBNXiIBP}; DBNXiCos → {DBNXiRiemann, DBNGKernel}; DBNXiIBP → DBNGKernel;
  DBNXiRiemann and DBNGKernel → DBNDefs; DBNDefs → Mathlib and the pinned LiCriterion.
- Positive control: the markers function returns `['sorry']` on `theorem x : True := by sorry`.
- A separate grep of those six files found no `axiom`, `opaque`, `unsafe`, `implemented_by`,
  `extern`, `native_decide`, `ofReduceBool` or kernel-skipping `set_option`.
- `telperion mission verify rh` reported `verify [rh]: OK`. The dbn island is not in the
  "no CI workflow builds" warning list. `mission status rh` shows `RH_dbn_H0_eq_xi (lemma,
  draft)`.

## 3. Axiom probe

- `leanlock.sh lake build --no-build` in `telperion/examples/dbn/lean` reported
  `All targets up-to-date (8747 jobs).` with exit 0. I did not run a full build.
- My probe `Probes/AuditProbe_RH_dbn_H0_eq_xi_A2.lean` was run with `leanlock.sh lake env lean`
  and deleted afterwards. It imports DBNXi and printed:
  - `'dbn_H0_eq_xi' depends on axioms: [propext, Classical.choice, Quot.sound]`
  - `'DBN.H_zero_I' depends on axioms: [propext, Classical.choice, Quot.sound]`
- The probe also contained
  `example (z : ℂ) : DBN.H 0 z = (1 / 8 : ℂ) * LiCriterion.riemannXi (1 / 2 + Complex.I * z / 2) := dbn_H0_eq_xi z`.
  It elaborated without error, so the proved type is exactly the registry proposition.

The result is exactly [propext, Classical.choice, Quot.sound], with no `sorryAx` and no custom
axioms.

## 4. Hand re-derivation of the main steps

In this section, g(u) = e^u ψ(e^{4u}), where ψ(x) = Σ_{n≥1} e^{−πn²x}, and
J(z) = ∫_0^∞ g(u) cos(zu) du.

1. **Riemann's symmetric integral (module A).** For all s,
   Λ₀(s) = ∫_1^∞ ψ(x)(x^{s/2−1} + x^{(1−s)/2−1}) dx. Classically,
   Λ(s) = 1/(s(s−1)) + that integral, and 1/(s(s−1)) = −1/s − 1/(1−s), so
   Λ₀ = Λ + 1/s + 1/(1−s) equals the integral. The integral is entire because ψ decays
   exponentially. Correct.
2. **Change of variables x = e^{4u} (module B).** Here dx = 4e^{4u} du. Take
   s = 1/2 + iz/2.
   - x^{s/2−1} · 4e^{4u} = 4e^{(1+iz)u}.
   - x^{(1−s)/2−1} · 4e^{4u} = 4e^{(1−iz)u}.
   - The two sum to 8e^u cos(zu).
   So Λ₀(1/2 + iz/2) = 8J(z). This matches the artifact's `hB`. Correct.
3. **Kernel ODE (module C).**
   - Differentiating: g' = e^uψ + 4e^{5u}ψ' and g'' = e^uψ + 24e^{5u}ψ' + 16e^{9u}ψ''.
   - So g'' − g = Σ(16π²n⁴e^{9u} − 24πn²e^{5u})e^{−πn²e^{4u}} = 8Φ.
   - Next, g'(0) = ψ(1) + 4ψ'(1). Write θ = 1 + 2ψ; the theta functional equation is
     θ(1/x) = √x θ(x). Differentiating at x = 1 gives −θ'(1) = θ(1)/2 + θ'(1), so
     4ψ'(1) + ψ(1) = −1/2, that is, g'(0) = −1/2.
   Both correct.
4. **Two integrations by parts (module D).** g and g' decay super-exponentially, which beats
   |cos(zu)| ≤ e^{|z|u}, so the boundary terms at ∞ vanish for every complex z.
   - ∫_0^∞ g'' cos(zu) = −g'(0) − z²J.
   - Hence 8H_0 = ∫(g'' − g)cos = −g'(0) − (z² + 1)J, that is, (z² + 1)J = 1/2 − 8H_0.
   This matches the artifact's `hD` (`DBN.integral_g_cos_eq`). Correct.
5. **Assembly (DBNXi).**
   - s(s−1) = (iz/2)² − 1/4 = −(z² + 1)/4.
   - So ξ(s) = (1/2)(−(z² + 1)/4)(8J) + 1/2 = −(z² + 1)J + 1/2 = 8H_0.
   - The artifact closes this with `linear_combination (1/8)·hD − (J z²/8)·I_sq`, which is
     consistent with that algebra.
   - At z = i: s = 0, riemannXi(0) = 1/2, and H_0(i) = 1/16 (`DBN.H_zero_I`).

I found nothing that looks wrong. Using the entire Λ₀-based xi means no s ≠ 0, 1 side condition
is needed, and the statement holds for every z.

## 5. Numerical check (mpmath 1.3.0, reimplemented from the Lean definitions)

The script is at `scratchpad/num_A2.py`. It reimplements:
- Φ as the ℕ+ sum truncated at n ≤ 12. For u ≥ 0 the first omitted term is below e^{−π·169}.
- H_0 as the integral of Φ(u)cos(zu) over [0, 2] at 25 digits. Φ(3) ≈ 1.7e−222046, and Φ(2)
  is of order e^{−πe^8}, so the truncated tail is negligible.
- riemannXi(s) = (1/2)s(s−1)(Λ(s) + 1/s + 1/(1−s)) + 1/2, with
  Λ = π^{−s/2}Γ(s/2)ζ(s) from mpmath. At s = 0 I used the definition's value 1/2 directly.
  Λ₀ is finite at 0: Λ₀(1e−15) ≈ 0.0230957.

| z | H_0(z) (quadrature) | riemannXi(1/2+iz/2)/8 | abs. diff |
|---|---|---|---|
| i | 0.0625 + 0i | 0.0625 | 0 at 25 digits |
| 0.7+0.4i | 0.0620214512049945498411 − 0.000200648057276215501244i | same to 27 digits | 3.2e−28 |
| 5−1.2i | 0.0540750261148107615995 + 0.00379067672937971224903i | same to 27 digits | 1.8e−27 |
| 0 | 0.0621400972735392637391 | same | 8.1e−28 |
| 2γ₁ = 28.26945... | −1.453e−19 | −1.453e−19 | 2.9e−28 |

The last row is at twice the first zeta-zero ordinate. Both sides vanish there to the working
precision, as expected. In particular H_0(i) = 1/16 is confirmed. A consistency check,
riemannXi(s) = s(s−1)Λ(s)/2 at s = 0.3 + 0.9i, agrees to 7e−27.

## 6. Establishes / does not establish

**Establishes**, with a kernel-checked proof that uses only [propext, Classical.choice,
Quot.sound], contains no `sorry` and passes the hardened containment gate:
- For every complex z, H_0(z) = ∫_0^∞ Φ(u)cos(zu) du equals (1/8)·ξ(1/2 + iz/2), with ξ the
  entire Riemann xi of the pinned LiCriterion vocabulary. This is the C2 representation
  theorem, exactly as the registry states it.
- The corollary H_0(i) = 1/16.

**Does not establish:**
- RH, or anything about where zeros of ξ, H_0 or H_t lie.
- Anything about the de Bruijn-Newman constant, which is not defined on the island.
- de Bruijn's t ≥ 1/2 real-zeros theorem (a separate node).
- The C4 equivalence node `RH_dbn_rh_iff_H0_real_zeros` or the strip node.

It does not flip any registry status. The node is still `draft`; promotion and grant are
separate registry steps that I did not perform. The identity is classical (Riemann 1859;
Titchmarsh 10.1). The contribution is the formalisation, not new mathematics.

## Issues

- None blocking.
- Note: the node title says "STATED ONLY, not proved". Once this node is linked and granted,
  that wording will be stale, because the island artifact does prove it. This is an editorial
  note for whoever does the registry update. I made no registry edits.

conjecture1_proved = False
