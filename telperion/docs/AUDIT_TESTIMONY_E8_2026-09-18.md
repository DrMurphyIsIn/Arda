# Blind read-back audit: `RH_limit_explicit_formula` (routes-roadmap E8)

Auditor: independent, no author context before section 7. Worktree `/Users/peterwmurphy/arda-e8`,
branch `rh/e8-statement` @ `6a3aad254`. Island pin `leanprover/lean4:v4.34.0-rc1`,
Mathlib `de5ce8a9a66a4aa68a9bdbb35b63a06d34d9ca11`. `lake build`: success (8728 jobs, only the
by-design `sorry` warnings). No registry file was modified. Nothing here is a proof of the node.
`conjecture1_proved = False`.

## Verdict: CLEAN

The registered statement is the classical Weil (1952) / Guinand (1948) explicit formula for
`ζ` on the class `C_c^∞(ℝ, ℂ)`, with every term carrying the correct sign, factor and
multiplicity; it is non-vacuous and non-trivial in Lean; it is well-formed for a later proof.
No Lean edit is required. Three non-blocking notes are in section 6.

Files audited (read as checked out on the branch):

* `telperion/missions/rh/lean/Statements/RH_limit_explicit_formula.lean`
* `telperion/missions/rh/lean/Statements/RHDefs.lean`, namespace `WeilExplicit` (lines 98-147)
* `telperion/missions/rh/nodes/RH_limit_explicit_formula.toml`
* dependency statements `RH_corridor_bound.lean`, `RH_rvm_unconditional.lean` (shape only)

Mathlib primitives verified at the pin: `Complex.digamma := logDeriv Gamma`
(`Gamma/Digamma.lean:39`), `MeromorphicOn.divisor f U z = if MeromorphicOn f U ∧ z ∈ U then
(meromorphicOrderAt f z).untop₀ else 0` (`Meromorphic/Divisor.lean:39-47`),
`ContDiff` index `ℕ∞ω = WithTop ℕ∞` with `ω = ⊤` (analytic) and `∞ = ((⊤ : ℕ∞) : WithTop ℕ∞)`
(smooth) (`ContDiff/FTaylorSeries.lean:116-120`).

## 1. The derivation I compared against (done before reading the memo)

Let `Λ(s) = π^{-s/2} Γ(s/2) ζ(s)`, entire except for simple poles at `s = 0, 1`, with
`Λ(s) = Λ(1-s)`; its zeros are exactly the nontrivial zeros of `ζ` with the same orders
(the poles of `Γ(s/2)` at `-2k` cancel the trivial zeros). For `g ∈ C_c^∞(ℝ, ℂ)` put

    H(s) := ∫_ℝ g(u) e^{(s-1/2)u} du,      h(r) := H(1/2 + ir) = ∫ g(u) e^{iru} du.

`H` is entire; integrating by parts `N` times gives `|H(s)| ≤ C_N e^{R/2} |s - 1/2|^{-N}`
uniformly on `|Re s - 1/2| ≤ 1` (`supp g ⊂ [-R, R]`), so all horizontal edge integrals below
vanish and all vertical integrals converge absolutely.

**Contour.** For `c = 2`, `c' = -1`,

    (1/2πi) [ ∫_{(2)} - ∫_{(-1)} ] (Λ'/Λ)(s) H(s) ds  =  Σ_ρ m(ρ) H(ρ)  -  H(0)  -  H(1),

since `Λ'/Λ` has residue `+m(ρ)` at a zero of order `m(ρ)` and `-1` at each simple pole.

**Reflect the left line.** `(Λ'/Λ)(s) = -(Λ'/Λ)(1-s)`. With `s = 1 - w` the line `Re s = -1`
(upward) becomes `Re w = 2` traversed downward, `ds = -dw`, so
`∫_{(-1)} (Λ'/Λ)(s) H(s) ds = -∫_{(2)} (Λ'/Λ)(w) H(1-w) dw`. And
`H(1-w) = ∫ g(u) e^{-(w-1/2)u} du = ∫ g(-u) e^{(w-1/2)u} du = H_{g̃}(w)`, `g̃(u) := g(-u)`. Hence

    Σ_ρ m(ρ) H(ρ) - H(0) - H(1)  =  (1/2πi) ∫_{(2)} (Λ'/Λ)(w) H_G(w) dw,     G := g + g̃.

**Split `Λ'/Λ` on `Re w = 2`:** `(Λ'/Λ)(w) = -½ log π + ½ ψ(w/2) + (ζ'/ζ)(w)`,
`(ζ'/ζ)(w) = -Σ_n Λ(n) n^{-w}`.

* Prime term. `(1/2πi) ∫_{(2)} n^{-w} H_G(w) dw = (1/2π) ∫ n^{-2-it} ∫ G(u) e^{(3/2)u} e^{itu} du dt
  = n^{-2} · (G e^{3u/2})(log n) = G(log n)/√n` (Fourier inversion at `u = log n`). So the
  prime term is `-Σ_n Λ(n) n^{-1/2} (g(log n) + g(-log n))`.
* `log π` term. Same inversion with `n = 1`: `(1/2πi) ∫_{(2)} H_G = G(0) = 2 g(0)`, so the
  term is `-½ log π · 2 g(0) = -g(0) log π`.
* Archimedean term. `ψ(w/2)` has poles at `w = 0, -2, …`, none in `1/2 ≤ Re w ≤ 2`, so shift to
  `Re w = 1/2`: `½ (1/2π) ∫ ψ(1/4 + ir/2) (h(r) + h(-r)) dr`. Substituting `r → -r` in the
  second half and using `ψ(z̄) = conj ψ(z)` gives
  `(1/4π) ∫ h(r) [ψ(1/4+ir/2) + ψ(1/4-ir/2)] dr = (1/2π) ∫ h(r) Re ψ(1/4 + ir/2) dr`.

**Result (no parity hypothesis on `g`):**

    Σ_ρ m(ρ) H(ρ) = H(0) + H(1) - g(0) log π + (1/2π) ∫ h(r) Re ψ(1/4 + ir/2) dr
                    - Σ_n Λ(n)/√n (g(log n) + g(-log n)),

with `H(0) = ∫ g e^{-u/2} = h(i/2)` and `H(1) = ∫ g e^{u/2} = h(-i/2)`. The zero sum is over all
nontrivial zeros, each counted once with its order (so `ρ`, `ρ̄`, `1-ρ` are separate terms);
correspondingly the prime side must carry both `g(log n)` and `g(-log n)` (for even `g` this is
the familiar `2 g(log n)`, and `H(0) + H(1) = 2 h(i/2)`).

Literature forms. Iwaniec-Kowalski Thm 5.12 (conductor 1, `γ(s) = π^{-s/2}Γ(s/2)`,
`h(r) = ∫ g(u) e^{iru} du`) is this display; their prime side
`-Σ_n [λ(n) g(log n) + conj λ(n) g(-log n)] Λ(n)/√n` is self-dual for `ζ`. Weil 1952 and Bombieri
("Remarks on Weil's quadratic functional", 2000) use `x = e^u`, `f(x) = g(log x)/√x`, and the
Mellin transform `∫_0^∞ f(x) x^{s-1} dx = H(s)`. Guinand 1948 and Montgomery-Vaughan §12.1 /
Thm 12.13 write the archimedean term as the `Re ψ` (equivalently `Re Γ'/Γ`) integral. I did not
have the printed texts open; the evidentiary weight here is the self-contained derivation above
plus the numerical check in section 2, which distinguishes every sign and factor.

## 2. Independent numerical check (mpmath 1.3.0, my own script, before reading the memo)

Scripts: `scratchpad/e8/numcheck.py`, `scratchpad/e8/numcheck2.py`. Test functions are
shifted Gaussians `g(u) = exp(-(u-a)²/(2σ²))`, deliberately not even (`a ≠ 0`); Gaussians are
outside the registered class but inside the Guinand class on which the identity also holds, and
the registered class is a subclass, so the normalisation test is valid. Zero side over the first
59 or 119 zeros with both signs of `γ` (all simple), prime side to `n ≤ 20000` / `3000`,
archimedean integral by `quad` against `mpmath.digamma`.

| σ | a | zero side | RHS (archSide - primeSide) | abs diff |
|---|---|---|---|---|
| 1/√2 | 0 | 7.2050e-22 | 7.2050e-22 | 3.6e-27 |
| 1/√2 | 0.7 | -6.4253e-22 | -6.4236e-22 | 1.7e-25 |
| 0.22 | 0 | 8.79044900808790331e-3 | 8.79044900808790331e-3 | 5.2e-22 |
| 0.22 | 0.5 | 6.19411125340489075e-3 | 6.19411125340489075e-3 | 1.0e-21 |
| 0.22 | -1.1 | -8.66433653095922191e-3 | -8.66433653095922191e-3 | 5.4e-22 |

Every wrong variant is off at order one (σ = 1/√2, a = 0.7 row): pole terms negated 8.01, prime
sign flipped 3.96, archimedean term halved 0.66, `log π` sign flipped 1.40, `ψ` used without
`Re` 1.14; zero side negated 0.0124 and halved 0.0031 (σ = 0.22 rows). The registered
normalisation is the only one consistent with the zeros.

## 3. Sign-by-sign comparison with the Lean definitions

| classical term | Lean (`WeilExplicit`) | match |
|---|---|---|
| `H(s) = ∫ g(u) e^{(s-1/2)u} du` | `weilKernel g s = ∫ u, g u * exp ((s - 1/2) * u)`, `1/2 : ℂ` (checked with `pp.numericTypes`) | yes |
| `m(ρ)`, order of `ζ` at a nontrivial zero, `0` elsewhere | `zeroMult ρ = (divisor riemannZeta {0<re<1} ρ).toNat` | yes (section 4) |
| `h(r) Re ψ(1/4 + ir/2)` | `archIntegrand g r = weilKernel g (1/2 + r I) * ((digamma (1/4 + (r/2) I)).re : ℂ)`, all numerals `ℂ`, `↑r / 2 * I = (r/2)·I` | yes |
| `H(0) + H(1) - g(0) log π + (1/2π) ∫ …` | `archSide g = weilKernel g 0 + weilKernel g 1 - g 0 * log π + (1/(2π)) * ∫ r, archIntegrand g r` | yes |
| `Σ_n Λ(n)/√n (g(log n) + g(-log n))` | `primeSide g = ∑' n, ((Λ n / √n : ℝ) : ℂ) * (g (log n) + g (-log n))` | yes |
| `Σ_ρ m(ρ) H(ρ) = arch - prime` | `HasSum (fun ρ => (zeroMult ρ : ℂ) * weilKernel g ρ) (archSide g - primeSide g)` | yes |

Transform direction (check 2). With the kernel `e^{(s-1/2)u}`, the residue computation pairs the
right-line `ζ'/ζ` with `g(log n)` and the reflected line with `g(-log n)`. The opposite
convention `e^{-(s-1/2)u}` swaps the two, and every other term is invariant under `g ↦ g̃`
(`H(0)+H(1)`, `g(0)`, the `Re ψ` integral because `Re ψ(1/4+ir/2)` is even in `r`, and the
zero sum because the zero set is `ρ ↦ 1-ρ` symmetric with equal orders). So the statement is
internally consistent and convention-independent. Lean confirmation (probe G, elaborates):
`weilKernel g (1 - s) = weilKernel (fun u => g (-u)) s`.

## 4. Multiplicity, index set, vacuity (checks 3, 4)

* `MeromorphicOn riemannZeta {0 < re < 1}` is a theorem (probe D', elaborates), so the divisor is
  not the junk value `0`. `ζ` is nowhere locally zero, so `meromorphicOrderAt` is never `⊤` and
  `untop₀` never truncates. On the strip `zeroMult ρ = (meromorphicOrderAt riemannZeta ρ).untop₀.toNat`
  (probe D, elaborates), which is the order of the zero, `0` at non-zeros.
* Off the open strip `zeroMult ρ = 0` by `simp [zeroMult, h]` (probe D); in particular
  `zeroMult (-2) = 0` (trivial zero) and `zeroMult 1 = 0` (pole; the divisor never sees the
  negative order because `1 ∉ U`, and `.toNat` is not doing any hiding). `ζ` has no zeros on
  `Re s ∈ {0, 1}`, so open versus closed strip changes nothing.
* `HasSum` over `ρ : ℂ` is the `Finset ℂ` partial-sum net; the family vanishes outside the
  countable zero set, so it is unconditional summation over the nontrivial zeros, each once with
  its order, `ρ` and `ρ̄` as separate terms. That is exactly the classical index set, and the
  prime side carries both `g(±log n)` as it must.
* Direction of risk: if the family were not absolutely summable the `HasSum` conjunct would be
  **false**, not vacuous (a `tsum` would silently be `0`; `HasSum` cannot). It is summable:
  `|H(ρ)| ≤ C_g/|γ|²` from two integrations by parts and `N(T) = O(T log T)`, so
  `Σ m(ρ)|H(ρ)| ≤ C Σ_{γ>0} 1/γ² < ∞` (Stieltjes: `2∫_1^∞ N(t) t^{-3} dt`). Absolute summability in
  `ℂ` is summability. True and nontrivial.
* `Integrable (archIntegrand g)`: `h(r) = O(1/r²)` (same bound on the line `Re = 1/2`),
  `|Re ψ(1/4 + ir/2)| = O(log(2+|r|))` (Stirling), and `1/4 + ir/2` is never a pole or zero of
  `Γ`, so `digamma` is the genuine `Γ'/Γ` there and the integrand is continuous. Integrable, so
  the conjunct is true-but-nontrivial; the `(1/2π) ∫` in `archSide` is then not the junk `0`.
* `weilKernel g s`: integrand continuous with compact support for every `s`, integrable, no junk.
* `primeSide`: finite support. Probe F' proves in Lean, from `IsWeilTest g`, that the summand is
  zero for `n ≥ e^R` (`HasCompactSupport.exists_pos_le_norm`), hence `Summable`; the `n = 0`
  term (`√0 = 0`, `log 0 = 0`) is killed by `Λ(0) = 0` and `Λ(1) = 0`. No junk `tsum`.

## 5. The class (check 5) and trivial-close probes (check 6)

* `IsWeilTest g = ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g ∧ HasCompactSupport g`, `g : ℝ → ℂ`.
  The index prints as `↑⊤` and `((⊤ : ℕ∞) : WithTop ℕ∞) ≠ (⊤ : WithTop ℕ∞)` elaborates by
  `WithTop.coe_ne_top` (probe C): this is `C^∞`, not analytic (`ω` would collapse the class to
  `{0}` and make the theorem vacuous). Nonempty and not a singleton: probe E' builds a
  `ContDiffBump` cast to `ℂ` and proves `∃ g, IsWeilTest g ∧ g ≠ 0` and
  `∃ g₁ g₂, IsWeilTest g₁ ∧ IsWeilTest g₂ ∧ g₁ ≠ g₂` (elaborate).
* Evenness is not needed: the derivation in section 1 uses only the functional equation, and the
  `g(log n) + g(-log n)`, `H(0) + H(1)`, `Re ψ` pairs are precisely the symmetrisation that makes
  the identity hold for arbitrary (complex, non-even) `g`. Dropping `Re` (using `ψ` alone) would
  make the formula false for non-even `g` (numerically off by 1.14). Numerics in section 2 with
  `a ≠ 0` confirm.

Trivial-close probes (`scratchpad/e8/Probe.lean`, `Probe2.lean`, `lake env lean` against the
built island):

| probe | result |
|---|---|
| full statement, `simp` | "simp made no progress" |
| full statement, `simp_all` | "simp_all made no progress" |
| full statement, `aesop` | "failed to prove the goal after exhaustive search", both conjuncts open |
| full statement, `norm_num` | unsolved goals, both conjuncts |
| full statement, `simp_all [IsWeilTest, all five defs]` | unsolved; goal displays the unfolded Bochner integrals and `tsum` |
| full statement, `unfold IsWeilTest; aesop (add simp [defs])` | fails, both conjuncts open |
| `g = 0` instance, `simp [defs]` | HasSum conjunct closes; `Integrable (archIntegrand 0)` left open |
| `g = 0` instance, with `archIntegrand 0 = 0` by `funext; simp` then `integrable_zero` | **proved** (expected: the zero function is a contentless true instance, not a witness for the class) |
| `((⊤ : ℕ∞) : WithTop ℕ∞) ≠ ⊤` | proved |
| `zeroMult ρ = 0` off strip; `zeroMult (-2) = 0`; `zeroMult 1 = 0` | proved by `simp [zeroMult, h]` |
| `MeromorphicOn riemannZeta {0<re<1}` | proved |
| class nonempty / not singleton | proved |
| `primeSide` summand finitely supported for `IsWeilTest g` | proved |
| `weilKernel g (1 - s) = weilKernel (g ∘ neg) s` | proved |

Nothing closes the registered statement or either of its conjuncts in general. `decide` is not
applicable (no `Decidable` instance).

## 6. Author's memo (`E8_LIMIT_EXPLICIT_FORMULA_DESIGN_2026-09-18.md`), read afterwards

It does not change the verdict. Its section 3.1 derivation is the same contour argument as my
section 1, term for term, and its section 4 numerics (shifted Gaussians, `1e-22`) agree with mine.
Non-blocking notes:

1. Memo probe 8 says `E8 0` by `constructor <;> simp` closes the first conjunct and leaves the
   second; in my run the opposite happens (`simp [defs]` closes the `HasSum` conjunct and leaves
   `Integrable (archIntegrand 0)`). Either way the zero instance is trivially true and contentless;
   cosmetic only.
2. All numerical checks (memo's and mine) use Gaussians, which are outside `IsWeilTest`. This is
   sound (the identity holds on the larger Guinand class and the registered class is a subclass),
   but a future numerics run with an actual bump function would remove even that indirection.
3. The proof route in memo section 8 step 3 (the pole at `s = 1` inside the box versus the
   `rect_explicit_formula` hypotheses) is correctly identified as the place the finite brick does
   not fit verbatim. That is a proof concern, not a statement concern.

Dependencies in the TOML (`RH_rvm_unconditional`, `RH_corridor_bound`) are the right inputs for
the sketched proof (absolute convergence of the zero side; vanishing horizontal edges). Both are
themselves `draft` with `sorry`, as the registry records.

## 7. Summary of what was checked and how

Read: statement, vocabulary, node TOML, three Mathlib definition sites, two dependency
statements. Built: the island (`lake build`, success). Derived: the explicit formula from the
contour argument, independently, before reading the memo. Computed: five mpmath runs with
non-even test functions, agreement to 20+ digits, every wrong variant rejected at order one.
Elaborated: 20 Lean probes (trivial-close attempts fail as required; structural facts about the
divisor, the index, the class, the prime side and the reflection identity prove). Verdict CLEAN.
`conjecture1_proved = False`.
