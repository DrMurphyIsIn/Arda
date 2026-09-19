# WALL BACKLOG MAP — every unproved node, mapped onto the facets of the assault

Date: 2026-09-18 · Branch `wall/backlogmap` · Base `origin/main` @ `1179d9ea3`
Author: backlog-map agent (ultrathink faceted-assault team)

**conjecture1_proved = False.** No RH progress is claimed anywhere in this document.
Nothing here proves, or contributes a proof step toward, the Riemann Hypothesis.
This is a registry cartography pass: it moves no node's status and writes no Lean.

Method: `mission status` / `open-leaves` / `verify` on all four campaigns at the pinned
commit, plus a direct read of all 44 node TOMLs and of the closure logic in
`telperion/src/telperion/missions/`. `verify` reports **OK** on all four campaigns —
which, as section B(c) shows, is a weaker statement than it reads as.

---

## 0. The facets of this run

The seed observation from the brief — *every wall clause is a uniformity /
order-of-quantifiers statement, while every instrument the program builds produces
instances* — is what the facets are cut along. A node's facet is decided by **which side
of the quantifier it works on**, not by which route it was authored for.

| Facet | Name | What it does to the wall | Exemplar already in hand |
|---|---|---|---|
| **F0** | THE WALL | The RH-equivalent clause itself. Never workable; held as `draft` goals by charter. | `RH_conjecture`, `MM_zeta_comb_membership` |
| **F1** | UNIFORMITY HARVEST | Names, as a registered node, the exact quantity a route needs bounded **uniformly in its truncation parameter** — converting "the wall" into a finite list of missing uniform bounds. | the B7 seam (n depends on T) |
| **F2** | EFFECTIVE CONSTANTS | Turns the existential `∃C` of the three new bridges into a named numeral. Existential constants cannot be composed across a limit; effective ones can. This is F1's prerequisite, not a polish item. | `RH_corridor_bound` (O-form; effective queued) |
| **F3** | BLINDNESS THEOREMS | Proves an instrument **cannot** see off-line-ness — fencing the wall from the outside so effort is not spent on a blind instrument. The WALL CAMPAIGN half that already landed. | `OrdinateInsensitivity.lean`, `MM_euler_factor_section_offline` |
| **F4** | INSTANCE FACTORY | Produces certified instances (heights, boxes, rungs). Honest, finite, and by construction **on the wrong side of the quantifier**. Kept for falsifiability and calibration, not for reach. | anduril ladder, Li rungs |
| **F5** | REGISTRY INTEGRITY | Keeps the bookkeeping from manufacturing a result the corpus does not hold. Section B(c) makes this the run's highest-priority facet. | this document |

---

## 1. Backlog map — one row per node that is not `proved`

25 rows: 23 on `origin/main`, plus 2 mirrormere drafts that live only on unmerged
`mm/*` branches (marked *off-main*). Refuted and deprecated nodes are included because
their precedents are load-bearing for the wall argument.

### 1.1 rh (1 open, 4 draft)

| Node | Status / kind | Deps | Facet | Verdict |
|---|---|---|---|---|
| `RH_conjecture` | draft / goal | 17 proved nodes | **F0** | **IS-THE-WALL.** Mathlib `RiemannHypothesis`. Stays `draft` permanently by charter. Its 17 deps are a *provenance manifest*, not a reduction — no combination of them implies the goal, and the DAG does not claim otherwise. Leave exactly as is. |
| `RH_bl_explicit_formula` | open / milestone | `RH_limit_explicit_formula`, `RH_bl_finite_multiset` | **F1** | **BLOCKED-ON — and MIS-FILED on both edges.** Node's own title states Li's kernel "is in neither the E8 nor the Guinand class", so `RH_limit_explicit_formula` (smooth compactly supported tests) does not reach it; and the B7 seam means `RH_bl_finite_multiset` composes only in the easy direction. Blocked on an unauthored node: *uniform-in-T truncation bound for the Li kernel*. See §2 op **R1**. |
| `RH_li_rung0_kernel` | open / lemma | `RH_li_rung_certificates` | **F4** | **WORKABLE-NOW, but the dep is wrong.** Route (from CONSUMER_SWEEP): Mathlib `riemannZeta_one` gives `taylorCoeff riemannXi 0 = 1 + γ/2 − log(4π)/2`; discharge reduces to the numeric `2 + γ > log 4π`. That route consumes **nothing** from `RH_li_rung_certificates` (which are Arb-hypothesis-conditional, and this node is by definition hypothesis-free). See §2 op **R2**. |
| `RH_dbn_H0_eq_xi` | draft / lemma | — | **F1** | **BLOCKED-ON (authoring).** Route C2, `H_0 = ξ/8`. No readback recorded, so `promote_to_open` will refuse. Not stale (authored 2026-09-17). Needs an audit pass, not new math. |
| `RH_dbn_debruijn_real_zeros` | draft / milestone | `RH_dbn_H0_eq_xi` | **F2** | **BLOCKED-ON `RH_dbn_H0_eq_xi`.** de Bruijn 1950, `t ≥ 1/2`. Note this is the *unconditional* half of Λ ≤ 1/2 — genuine F2 content (an effective bound), not wall content. No readback. |
| `RH_dbn_rh_iff_H0_real_zeros` | draft / milestone | `RH_dbn_H0_eq_xi` | **F0** | **IS-THE-WALL** (route C's C10 in disguise: RH ⟺ all zeros of `H_0` real). Correctly filed as a bridge, but it should be marked wall-grade so no one schedules it as workable. See §2 op **R3**. |

### 1.2 mirrormere (5 open, 2 draft on main; 2 drafts off-main)

| Node | Status / kind | Deps | Facet | Verdict |
|---|---|---|---|---|
| `MM_zeta_comb_membership` | draft / goal | 17 nodes | **F0** | **IS-THE-WALL** (RH-equivalent via Weil 1952 / Bombieri 2000). Its own title admits the statement is a **placeholder** that "MUST replace" before leaving draft. Un-touched since 2026-09-14 → see stale list, §2 op **R7**. |
| `MM_euler_factor_section_offline` | open / lemma | `MM_twofreq_realrooted_iff` (proved) | **F3** | **WORKABLE-NOW.** Open leaf. Route: `twoFreq_realRooted_iff` + `‖1‖ ≠ 2^(−1/2)`. **Proof exists on `origin/mm/mm-euler-factor-offline` — do not re-derive.** Conflict C4 (two branches link it to different modules) must be settled before `link`. This is the purest F3 asset in the corpus: a kernel-certified negative control. |
| `MM_offline_disjoint_discs` | open / lemma | — | **F3** | **WORKABLE-NOW.** Open leaf, pure metric topology. **Proof exists on `origin/mm/offline-disjoint-discs`.** Merge rather than restart. |
| `MM_recurrence_deficit_eq_excess` | open / lemma | `MM_bragg_defect_witness` (proved) | **F3** | **WORKABLE-NOW.** Open leaf; `Real.exp` ring algebra + strict monotonicity. **Proof exists on `origin/mm/recurrence-deficit`.** Dep is defensible (the certified δ = 1/10 excess value comes from `BraggDefect.lean`), though the *strict-positivity-for-every-δ* conjunct needs nothing from it. |
| `MM_speiser_box_probe` | open / milestone | — | **F4** | **BLOCKED-ON missing machinery.** Open leaf in the DAG but not workable: needs the second-derivative winding integrand (derivative variant of the A2 EM evaluator), which no node owns. The E9 "hidden cost" caveat is real. Author the machinery node before staffing this. See §2 op **R4**. |
| `MM_torus_section_n2_rigidity` | open / milestone | `MM_torus_section_dictionary` (**draft**), `MM_twofreq_realrooted_iff` | **F3** | **BLOCKED-ON `MM_torus_section_dictionary`.** Not an open leaf — a draft dep. Work on `origin/mm/torus-ladder-t1` exists. The blocker is an *audit*, not a proof. |
| `MM_torus_section_dictionary` | draft / lemma | — | **F3** | **BLOCKED-ON audit (STALE).** Original statement was flagged **TRIVIAL (definitionally `rfl`)** by the 2026-09-14 blind read-back and replaced; the replacement has sat un-audited since. Longest-stale draft in the registry and it blocks an open node. See §2 op **R5**. |
| `MM_weil_gram_trace` *(off-main, `mm/d2-weil-gram-trace`)* | draft / lemma | `MM_rect_trace_reading`, `MM_bragg_bridge`, `MM_offline_pairs_le_defect` | **F1** | **MIS-FILED (cross-campaign).** Title states discharge is "E8 (`RH_limit_explicit_formula`) applied to `crossCorr`" — an **rh-campaign** node that cannot appear in a mirrormere `depends_on` (see §2(a)). The listed deps are the MM-local proxies, not the real consumers. Otherwise well-authored: it explicitly disclaims inertia ("posIndex = k for ALL families IS Weil = RH; for one family it is data"), which is the correct wall-hygiene. |
| `MM_weil_form_certified_height` *(off-main, `mm/mm-d3-certified-height-weil-bound`)* | draft / lemma | `MM_rvm_unbounded_mean_density`, `MM_rect_trace_reading` | **F1** | **MIS-FILED — this is the D3 exemplar, and it is STILL UNFIXED on its branch.** Title says "the tail bound comes from **`RH_rvm_unconditional`**"; `depends_on` names `MM_rvm_unbounded_mean_density` (mean density — a strictly weaker statement). Corrected edges in §2 op **R6**. Substantively the strongest F1 node authored so far: its `C log T / T^3` tail bound is a genuine uniformity statement, and its escape-proof shape (summability conjuncts outside the ladder implication) is exactly the discipline F1 needs. |

### 1.3 anduril (3 open, 1 draft)

| Node | Status / kind | Deps | Facet | Verdict |
|---|---|---|---|---|
| `AND_ladder_h280000` | open / milestone | — | **F4** | **BLOCKED-ON the StripClear two-box capstone + branch reconcile.** The artifact exists but carries per-segment `BandHyp` binders; the node's registered form is hypothesis-free. This is a *hypothesis-discharge* blocker, not a compute blocker. |
| `AND_ladder_1e6` | open / milestone | `AND_ladder_h280000` | **F4** | **BLOCKED-ON `AND_ladder_h280000`.** Roadmap states nothing structural remains — wall-clock only. Correctly filed. |
| `AND_ladder_1e9` | open / milestone | `AND_ladder_1e6`, `AND_checkline_correct` | **F4** | **MIS-FILED.** Title says the charter gates this on the **A3 Riemann–Siegel era** (theta branch + RS main sum + Gabcke C0 remainder), "nodes to be authored" — but `depends_on` names only the ladder predecessor and the band checker. The DAG therefore shows this as two hops from workable when it is gated on three unbuilt bricks. Same defect class as D3. See §2 op **R8**. |
| `AND_ladder_1e13` | draft / goal | 8 nodes | **F4** | **ORPHANED-as-scheduled → keep, retitle.** Not the wall (it is finite), but at `native_decide`-era scale it is not on any 12–24-month path either. **Do not retire** — it is the campaign's declared goal and a useful honesty marker that the ladder is finite. Recommend leaving `draft` indefinitely, exactly as `RH_conjecture` is held. |

### 1.4 bg (3 open, 1 draft, 1 refuted, 1 deprecated)

BG is a **different conjecture** (Brualdi–Goldwasser Laplacian ratio), included per the
brief only where its machinery or its refutation precedents inform the RH wall.

| Node | Status / kind | Deps | Facet | Verdict |
|---|---|---|---|---|
| `BG_conjecture1` | draft / goal | 12 nodes | — | **MIS-FILED (incomplete deps).** The capstone genuinely reduces to the open `Hnorm` / `Hdom` obligations, and `Obligation A` was **kernel-refuted** (`deephub_obligationA_false`). The real frontier obligations — `RealObligationA`, `SharpRateNF` — are **not registered at all**, so the DAG shows 12 deps of which 9 are proved, implying far more completeness than exists. See §2 op **R9**. |
| `BG_master_inequality` | open / lemma | — | — | **WORKABLE-NOW (in-campaign).** Open leaf. Title self-labels "PROVISIONAL rendering" — the statement should be re-audited before proof effort, since a provisional rendering is exactly what the `MM_torus_section_dictionary` triviality incident came from. |
| `BG_r2_double_near_star` | open / lemma | — | — | **WORKABLE-NOW.** Open leaf; `logΦ(DN(a,b)) < 0` for `a,b ≥ 2`, rooted rendering. |
| `BG_r2_multihub_ceiling` | open / milestone | — | — | **WORKABLE-NOW.** Open leaf; the reformulation that survived the refutation of fixed-n DN-maximality. |
| `BG_hnorm_capstone` | **refuted** / lemma | — | **F3 (precedent)** | **KEEP AS PRECEDENT.** Correctly refuted at n=52 with a kernel artifact. Cite in wall docs: this plus Obligation A are the house's proof that a registry can and does record negative results. Its exclusion from `BG_conjecture1.depends_on` is correct. |
| `BG_r2_multihub_maximality` | **deprecated** / lemma | — | — | **CORRECTLY DEPRECATED** (superseded by `BG_r2_multihub_ceiling`); reason recorded. No action. |

### 1.5 Facet tallies

| Facet | Nodes | Note |
|---|---|---|
| F0 THE WALL | 4 | `RH_conjecture`, `MM_zeta_comb_membership`, `RH_dbn_rh_iff_H0_real_zeros`, (+`BG_conjecture1` for its own conjecture) |
| F1 UNIFORMITY HARVEST | 4 | `RH_bl_explicit_formula`, `RH_dbn_H0_eq_xi`, `MM_weil_gram_trace`, `MM_weil_form_certified_height` |
| F2 EFFECTIVE CONSTANTS | 1 registered | `RH_dbn_debruijn_real_zeros`. **This is the finding**: the facet that F1 depends on has almost no registered surface. See §2 op **R10**. |
| F3 BLINDNESS | 5 | 3 of them have proofs sitting on unmerged branches |
| F4 INSTANCE FACTORY | 6 | the healthiest facet, and the one furthest from the wall |
| F5 REGISTRY INTEGRITY | 0 registered | §2 ops **R11–R14** |

**The map's one structural reading.** F4 (instances) is well-staffed and well-proved.
F3 (blindness) has four proofs already written and merely unmerged. F1 — the only facet
that works on the *uniform* side of the quantifier, i.e. the only facet whose completion
would change anything about the wall — has four nodes, **two of which are mis-filed and
two of which have no readback**, and it rests on F2, which has **one** registered node.
The program's instrument-building capacity and its wall-relevant capacity are not the
same size, and the registry currently does not show that gap. Making it visible is the
cheapest real deliverable of this run.

---

## 2. Concrete registry operations

Exact commands. Run inside `telperion/` with the py3.9 shim:

```
PYTHONPATH=src python3 -c "import sys,tomli; sys.modules['tomllib']=tomli; from telperion.cli import main; sys.argv=['telperion','mission',<SUBCMD>,...]; sys.exit(main())"
```

No statement-file header is hand-edited by any operation below. New rh vocabulary goes
through `telperion/missions/rh/build_rhdefs.py` (add the literal, regenerate) — never a
hand-append to `RHDefs.lean`.

**R1 — author the B7 uniformity node** (F1; the seam found 2026-09-18).
`mission add RH_bl_uniform_truncation --campaign rh --kind lemma --deps RH_bl_finite_multiset --statement-file <f>`
Statement shape: *there exist `C ≥ 0` and `T_0` such that for every `n ≥ 1` and every
`T ≥ T_0`, the finite-multiset index witness for the height-`T` truncation is bounded by
`C` independently of `T`* — i.e. the negation of the seam. Author it **`draft`**, and in
the title record the in-house evidence that no bounded universal `n` exists
(`RH_bl_finite_multiset`'s own non-vacuity note: "worst first-negative n grows without
bound as points approach the line"). This node is expected to be **hard or false**; it is
registered so the B10 route's blocker has a name rather than living in a doc.
Then `mission add`-edit `RH_bl_explicit_formula` to depend on it.

**R2 — correct `RH_li_rung0_kernel`'s dep.**
Remove `RH_li_rung_certificates` from `depends_on` (the Arb-conditional rungs supply
nothing to a hypothesis-free statement), leaving it dep-free and a genuine open leaf.
Record the correction as a new ledger entry — `mission attempt RH_li_rung0_kernel
--verdict note` — rather than rewriting history. Then it is **WORKABLE-NOW** via
`riemannZeta_one` + the `2 + γ > log 4π` bracket.

**R3 — mark route-C's wall node.** Retitle `RH_dbn_rh_iff_H0_real_zeros` to carry the
explicit prefix `WALL-GRADE (C10):` so `open-leaves` consumers never schedule it.

**R4 — author the missing E9 machinery node** (F4), then re-dep `MM_speiser_box_probe`:
`mission add MM_winding_second_derivative --campaign mirrormere --kind lemma` — the
second-derivative EM evaluator variant for the winding integrand. Then
`MM_speiser_box_probe --deps MM_winding_second_derivative`. Today the node is a DAG open
leaf that is not actually workable; this makes the DAG honest.

**R5 — audit the stale dictionary (highest-value cheap op).**
`mission audit MM_torus_section_dictionary` with a blind read-back that explicitly tests
the 2026-09-14 triviality finding — *is `twoFreq = linearTorusForm 2 ∘ torusOrbit 2`
definitionally `rfl`?* If it is again trivial, deprecate rather than promote. Promoting it
unblocks `MM_torus_section_n2_rigidity`.

**R6 — fix the D3 exemplar** (on `mm/mm-d3-certified-height-weil-bound`, before merge).
Current `depends_on = ["MM_rvm_unbounded_mean_density", "MM_rect_trace_reading"]`.
Corrected: `depends_on = ["MM_rect_trace_reading"]`, **plus** a new mirrormere-local
proxy `MM_rvm_cumulative_local` whose statement is the cumulative RvM bound the title
actually credits (mean density is strictly weaker and does not give `C log T / T^3`).
Cross-campaign edges are structurally impossible (§3a), so the proxy is the only correct
encoding — and its node body must name `RH_rvm_unconditional` / `E6Bridge2.lean` as its
source so the laundering is documented rather than silent.

**R7 — replace the `MM_zeta_comb_membership` placeholder.** Its title already mandates
this. Until done, the mirrormere goal node's registered statement is Mathlib
`RiemannHypothesis` via the island dictionary, which is *correct but uninformative*; the
W3c concrete log-density FQ membership statement is the authoring item.

**R8 — correct `AND_ladder_1e9`.** Author the three A3 bricks as `draft` nodes
(`AND_theta_branch`, `AND_rs_main_sum`, `AND_gabcke_c0`) and add them to
`AND_ladder_1e9.depends_on`. Until then the DAG understates the gate by three bricks.

**R9 — correct `BG_conjecture1`.** Author `BG_real_obligation_a` and `BG_sharp_rate_nf`
as `draft` lemmas and add both to `BG_conjecture1.depends_on`, with the title of the
former recording that the *original* Obligation A was kernel-refuted and that this is the
degree-equalizing SPR re-encoding, not a retry.

**R10 — open the F2 surface (the structural gap).** Author three `draft` nodes making
the new bridges' existential constants effective — this is the facet F1 is waiting on:
- `RH_rvm_unconditional_effective` (deps `RH_rvm_unconditional`) — a numeral for `C` in `|N(T) − main(T)| ≤ C log T`.
- `RH_corridor_bound_effective` (deps `RH_corridor_bound`) — a numeral for `C` in `‖ζ′/ζ‖ ≤ C log² T`.
- `RH_limit_explicit_formula_effective` (deps `RH_limit_explicit_formula`) — an effective modulus for the `HasSum` convergence.
Existential constants do not compose across a limit; every F1 node above silently assumes
effective ones. Registering them turns a hidden assumption into three tracked nodes.

**R11–R14 — the gate hardening.** See §3(c); these are code changes in
`telperion/src/telperion/missions/`, not `mission` subcommands, and they are the highest
priority item in this document.

---

## 3. Registry-health answers

### (a) Do any nodes' deps claim something the corpus does not support?

**Yes — five, and the defect has a single structural root cause.**

**Root cause first.** `load_campaign` (`registry.py`) raises `SchemaError` for any
`depends_on` target not present in the *same campaign's* node set, and nodes are loaded
per-campaign-root. **There is no cross-campaign edge mechanism at all.** But the corpus
is emphatically cross-campaign: mirrormere's D-route consumes rh's `E6Bridge*` results on
the `rvm_bridge` island. Authors therefore reach for the nearest same-campaign proxy, and
the title — written honestly — names the real source. That divergence *is* the D3 defect
class. It is a design gap, not carelessness.

The five instances:

1. **`MM_weil_form_certified_height` (the named D3 exemplar) — still unfixed on its
   branch.** `depends_on` names `MM_rvm_unbounded_mean_density`; the title credits
   `RH_rvm_unconditional`. These are not interchangeable: mean density is unbounded-growth
   only, while the `C log T / T^3` tail bound needs the *cumulative* `|N(T) − main(T)| ≤
   C log T`. The dep as written does not support the statement. Fix: op **R6**.
2. **`RH_bl_explicit_formula` — both edges unsupported.** `RH_limit_explicit_formula` is
   E8 on smooth compactly supported tests; the node's own title says Li's kernel "is in
   neither the E8 nor the Guinand class". And `RH_bl_finite_multiset` composes only in the
   easy direction (the B7 seam: its index `n` depends on the truncation window `T`). A node
   whose title refutes its own dependency edges is the clearest case in the registry.
3. **`RH_li_rung0_kernel` → `RH_li_rung_certificates`.** The rungs are conditional on Arb
   enclosure hypotheses; this node is *defined* as the hypothesis-free anchor. The dep
   cannot contribute. Fix: op **R2**.
4. **`AND_ladder_1e9`.** Title: gated on the A3 Riemann–Siegel era, "nodes to be
   authored". Deps: only `AND_ladder_1e6` + `AND_checkline_correct`. Fix: op **R8**.
5. **`BG_conjecture1`.** Deps list 12 nodes, 9 proved; the actual frontier
   (`RealObligationA`, `SharpRateNF`) is unregistered. The omission makes the goal look
   75% closed. Fix: op **R9**.

One near-miss cleared: `MM_recurrence_deficit_eq_excess → MM_bragg_defect_witness` is
**defensible** — the certified δ = 1/10 excess numeral does come from `BraggDefect.lean`
— though the strict-positivity-for-all-δ conjunct is independent of it.

One **stale title** worth correcting separately: `MM_rvm_unbounded_mean_density` is now
`proved` (artifact `E6Bridge.lean`), but its title still reads "NO unconditional kernel
proof exists in corpus or Mathlib … Discharge = a FUTURE BRICK". That survey verdict was
overtaken by the rvm_bridge work. A reader trusting the title would conclude the node is
open. Recommend retitling with the discharge recorded.

### (b) Which draft nodes are stale?

Eight drafts exist (7 on main, plus 2 off-main, minus overlap). They split three ways:

**Charter-permanent — never to be promoted, not stale by definition:**
`RH_conjecture`, `MM_zeta_comb_membership`, `AND_ladder_1e13`, `BG_conjecture1`. These are
goal nodes held at `draft` deliberately. Any future "staleness" sweep must exempt
`kind = "goal"` or it will generate permanent false positives — worth encoding as a rule
now rather than rediscovering it.

**Genuinely stale (2), both mirrormere, both 2026-09-14, both un-touched for 4 days:**

1. **`MM_torus_section_dictionary` — the worst case, and the only stale draft that blocks
   an open node.** Its predecessor statement was flagged **TRIVIAL (definitionally `rfl`)**
   by a blind read-back on 2026-09-14; the replacement was written the same day "awaiting
   re-audit" and has had none since. It gates `MM_torus_section_n2_rigidity` (open). A
   draft that (i) replaced a statement caught as vacuous, (ii) has never been audited, and
   (iii) blocks live work is the highest-risk draft in the registry — a second triviality
   would propagate into the rigidity node. Op **R5**.
2. **`MM_zeta_comb_membership`** is charter-permanent as a *goal* but carries a
   **self-declared defect**: its title states the placeholder statement "MUST replace"
   before leaving draft. Untouched since 2026-09-14. Listed here because the defect is
   acknowledged in-node and still open. Op **R7**.

**Fresh but un-promotable (3):** the route-C trio `RH_dbn_H0_eq_xi`,
`RH_dbn_debruijn_real_zeros`, `RH_dbn_rh_iff_H0_real_zeros`, all authored 2026-09-17.
One day old, so not stale — but **none has a `readback`**, and `promote_to_open` refuses
without one. They are inert until audited. Route C currently has *zero* workable nodes.

### (c) Can a grant cascade mark something proved on a false premise?

**Yes. Demonstrated, not inferred.** This is the most important finding in this document,
and the answer is worse than the question anticipates: the failure does not require a
cascade at all, because **the gate never consults the DAG in the first place.**

I read the closure logic in `telperion/src/telperion/missions/` and then built a throwaway
probe campaign in the scratchpad to execute it. The probe:

- node `P_dep`, status **`draft`** (unproved);
- node `P_top`, status `open`, `depends_on = ["P_dep"]`, registered statement
  `theorem p_top : RiemannHypothesis`;
- artifact a WIP file whose entire content is `theorem p_top : RiemannHypothesis := by sorry`;
- `set_proof` with `via = "direct"`, then `grant_status`.

Result:

```
P_top status        = proved
P_top closure_clean = True
P_dep status        = draft
verify ok = True   errors = []   warnings = []
```

**A node asserting `RiemannHypothesis` was granted `proved`, flagged `closure_clean =
true`, off an artifact proved by `sorry`, while its declared dependency sat at `draft` —
and `mission verify` reported OK with zero errors and zero warnings.**

Three independent defects compose:

- **G1 — no kernel authority at the gate.** `grant_status` decides by *normalized text
  containment only*. `normalize_lean` strips `:= by sorry` with a `$`-anchored regex, i.e.
  only at end-of-string; the node's statement file (which ends in `:= by sorry` by
  construction, per `statements._build_body`) normalizes to `theorem p_top :
  RiemannHypothesis`, which is a **substring** of the artifact's `theorem p_top :
  RiemannHypothesis := by sorry`. A sorry-carrying artifact therefore matches *by design of
  the normalizer*. Nothing in `grant_status` or `verify_campaign` greps for `sorry`,
  `admit`, `native_decide`, or `axiom`. Note the sharp irony: the codebase **already has**
  the right checker — `telperion audit <file>` (`cli.py:635`, "audit external Lean for
  sorry/axiom/stub/vacuity, exit 1 if any error finding") — and the gate simply never calls
  it.
- **G2 — no dependency check at the gate.** `grant_status` never inspects `depends_on`.
  Dependency-status awareness lives **only** in `open_leaves`, which is a *scheduling
  query*, not a gate. A node may be granted with every dependency in `draft`.
- **G3 — the cascade guard is inert on 100% of the live corpus.** `closure_clean` is the
  one mechanism intended to catch a false premise. But `grant_status` writes
  `closure_clean = (new_status == "proved")` — unconditionally `True` — and
  `_compute_closures` seeds every node from its stored flag and **only recomputes nodes
  with `via == "reduction"`**. `verify_campaign` check 2c likewise compares stored vs.
  recomputed **only for `via == "reduction"`**. Across all four campaigns: **44 of 44
  proof links are `via = "direct"`. Zero are `via = "reduction"`.** The closure fixpoint
  has never executed against a single real node in this registry.

A second probe isolates G3 cleanly: the *identical* setup with `via = "reduction"` yields
`status = proved`, `closure_clean = **False**` — the fixpoint correctly detects the
unproved dep. So the machinery works; it is simply bypassed by the `via` value that every
node in the corpus uses. And even then `verify ok = True`: **nothing anywhere errors on a
`proved` node with `closure_clean = false`.** `closure_clean` is a label, not a gate.

**What is genuinely holding the line today.** Kernel authority is real, but it lives
entirely in per-island CI (`proof-lean.yml` axiom guards, `telperion-lean-e2e.yml`
`sorryAx` greps) keyed to **named anchor theorems in specific islands**. Nothing joins a
node's `proof.artifact` field to any CI guard — the coupling is convention plus reviewer
attention. `mission-statements-compile` compiles only the *statement* files, never the
artifacts. And the registry already documents one artifact
(`RH_dlvp_zero_free_region`, the sole legitimate `closure_clean = false`) as living on an
island "not yet wired into this campaign's CI". The discipline has held so far because the
humans and auditors have been careful, not because the gate enforces it.

**Recommended fixes, in priority order:**

- **R11 (do first).** In `grant_status`, call `audit.audit_lean_file(artifact_path)` before
  the flip and raise `GateError` on any error finding. This closes G1 using code that
  already exists and is already tested.
- **R12.** In `grant_status`, refuse when any `depends_on` target is not `proved`. Provide
  an explicit escape (`--allow-open-deps`) that is *only* honoured by forcing
  `closure_clean = False` and recording the override on the node. Closes G2.
- **R13.** Extend `_compute_closures` to recompute `via = "direct"` nodes on the same rule
  (all deps `proved` **and** clean). To preserve the one deliberate `False`
  (`RH_dlvp_zero_free_region`, cross-island), add an explicit `closure_override_reason`
  field rather than relying on a bare stored `False` that the fixpoint must not touch —
  the current "seed from stored flag" comment shows this override was intended, but a
  silent bare boolean cannot be distinguished from a stale one. Closes G3.
- **R14.** Make `verify_campaign` **error** (not pass silently) on any node with
  `status = "proved"` and `closure_clean = false` lacking a `closure_override_reason`.
  Today such a node is invisible to `verify`.

Applied together, the probe above fails at R11 on the `sorry`, and at R12 on the draft
dependency, instead of printing `proved`.

**Scope honesty.** None of this means any currently-`proved` node is wrong. I checked no
artifact's kernel status, and the per-island CI guards give real assurance for the islands
they cover. The finding is that **the registry's own gate would not have stopped it**, and
that `mission verify: OK` — the phrase this program quotes as evidence — certifies
considerably less than it appears to. Given that the registry is described as "the backbone
of the assault, not a scoreboard", a backbone that reports OK for a `sorry`-proved
`RiemannHypothesis` node is the single highest-value repair available this run. It is also
the cheapest: R11 is a three-line call into an existing, tested checker.

---

## 4. What this run should do next

1. **R11–R14** — harden the gate. Cheapest, highest-value, blocks nothing else.
2. **R5** — audit `MM_torus_section_dictionary`; unblocks an open node for the cost of a read.
3. **Merge the four mm/* branches** (euler-factor-offline, offline-disjoint-discs,
   recurrence-deficit, torus-ladder-t1) after settling conflicts C4/C5/C6. Four F3 proofs
   are written and unmerged; re-deriving any of them is pure waste.
4. **R10** — open the F2 effective-constants surface. Every F1 node silently assumes it.
5. **R1, R6, R2, R8, R9** — the mis-filed edges, so the DAG stops overstating closeness.

conjecture1_proved = False.
