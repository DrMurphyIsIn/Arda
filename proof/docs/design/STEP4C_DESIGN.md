# Step 4c porting design: the raw-amplitude seam in Lean

Companion to `raw_amplitude_seam.py` (all statements verified there in exact Fraction
arithmetic; certificates S1/S2/V3/S3/limit all green).  This note maps those statements onto
the existing `R3Cert` namespace with ready-to-paste Lean statements, in dependency order, so
the port can be written from correct statements on the first CI pass.  Written by the fork
session (branch `review/step4c-raw-seam`, MR !68); no shared file touched.

## What changed vs BRIDGE_DESIGN.md's Step 4c roadmap

The roadmap's item (3) -- "the cherry-folding AT AMPLITUDE LEVEL ... this is where the
measured non-clean `log_rhoB(pi/Phi)` offsets live" -- **collapses**.  The offsets were an
artifact of comparing `pi` of finite trees whose ROOT lacks the phantom parent edge against
the DEC amplitude (whose every node has `d = k + c + 1`).  Working on the *branch* side (every
vertex phantom-consistent), the amplitude identity is **finite and local**: there is no second
limit, and no per-`p` offset bookkeeping.  Two exact rational identities plus the (already
CI-green) telescoping and one squeeze do the whole job.

## The four items, in dependency order

### (i) The literal realization and the raw-cavity lemma  [new file, ~150 lines]

The DEC-dressed `BridgeStep2.realize` folds cherries into `zc`/`ac`.  Step 4c needs the
LITERAL realization: cherries expanded as 2-paths, raw weights `1/(deg u * deg v)`, parent
edge counted in the root degree.  All of it fits the existing `RTree` (weights are per-edge
reals; degrees only enter through the weights, so they can be computed during construction):

```lean
/-- Root degree of a branch in the literal tree, phantom parent edge included:
    `d = n_ch + 1 + c`.  (The `+1` is the hub/parent edge; matches the DEC `d`.) -/
def dB : Branch → ℕ
  | .node c ch => ch.length + 1 + c

/-- The literal cherry gadget hanging off a degree-`d` root: mid (degree 2), leaf (degree 1);
    root-mid weight `1/(d*2)`, mid-leaf weight `1/(2*1)`. -/
noncomputable def litCherry (d : ℕ) : ℝ × RTree :=
  (1 / ((d : ℝ) * 2), RTree.node [(1 / 2, RTree.node [])])

mutual
/-- The literal (cherry-expanded, raw-weight) realization of a branch. -/
noncomputable def litRealize : Branch → RTree
  | .node c ch =>
      RTree.node (List.replicate c (litCherry (dB (.node c ch))) ++
        litChildren (dB (.node c ch)) ch)
noncomputable def litChildren : ℕ → List Branch → List (ℝ × RTree)
  | _, [] => []
  | d, K :: rest => (1 / ((d : ℝ) * (dB K : ℝ)), litRealize K) :: litChildren d rest
end
```

**(S1) the raw-cavity lemma** (the cherry-folding, one line of algebra; the raw analogue of
`q_realize_eq_rho0`):

```lean
/-- Raw matching cavity of the literal tree = degree * DEC cavity. -/
theorem q_litRealize_eq_d_cav (b : Branch) :
    Zopen (litRealize b) / Ztot (litRealize b) = (dB b : ℝ) * cav b
```

Proof shape: induction via `RTree.tree_cavity_recursion` (CavityTree.lean).  The cherry
child is a closed computation -- `Zopen (mid) = 1`, `Ztot (mid) = 3/2` (so `Q_mid = 2/3`),
each cherry term contributes `(1/(2d)) * (2/3) = 1/(3d)`; each branch-child term contributes
`(1/(d * dB K)) * (dB K * cav K) = cav K / d` by the inductive hypothesis.  Then

    Q = 1 / (1 + c/(3d) + cavSum ch / d) = 3d / (3d + c + 3 * cavSum ch) = d * cav.

The last step is `field_simp; ring` against `Reach.cav` (`cav = 3/(3+3k+4c+3S)` and
`3d + c = 3+3k+4c` by `dB` arithmetic).  Positivity side conditions mirror
`Ztot_realize_pos` (all literal weights are positive).
Python witness: `raw_amplitude_seam.certify_raw_cavity_lemma` (486/486 branches, every node).

### (ii) The local amplitude identity  [same file, ~120 lines]

Define the `rhoB`-free DEC amplitude and the literal vertex count:

```lean
/-- Literal vertex count `V(b) = 1 + 2c + Σ V(child)`. -/
def Vb : Branch → ℕ
  | .node c ch => 1 + 2 * c + VbSum ch     -- with the obvious VbSum

mutual
/-- `W(b) = Φ(b) · rhoB^{V(b)}` -- the rhoB-free DEC amplitude (exact node recursion:
    `ac * rhoB^(1+2c) = (3/2)^c (1 + c/(3d))`). -/
noncomputable def Wb : Branch → ℝ
  | .node c ch =>
      (3 / 2) ^ c * (1 + (c : ℝ) / (3 * (dB (.node c ch) : ℝ)))
        * (1 + zc c ch.length * cavSum ch) * WbProd ch
noncomputable def WbProd : List Branch → ℝ
  | [] => 1
  | K :: rest => Wb K * WbProd rest
end
```

**(S2) the amplitude identity, NO LIMIT** -- two lemmas:

```lean
/-- The literal partition function IS the DEC amplitude (rational identity, no logs). -/
theorem Ztot_litRealize_eq_Wb (b : Branch) : Ztot (litRealize b) = Wb b

/-- The log-side link to `logPhi` (connects to the capstone `phi_le_one`). -/
theorem logPhi_eq_log_Wb (b : Branch) :
    logPhi b = Real.log (Wb b) - (Vb b : ℝ) * Real.log rhoB
```

Proof shapes.  First lemma: induction.  `Ztot (litRealize (node c ch))
= Popen * (1 + Σ w·Q)` (the `hfac` step inside `tree_cavity_recursion`); `Popen` splits as
`(Ztot cherry)^c * Π Ztot (litRealize K) = (3/2)^c * Π Wb K` (IH), and
`1 + Σ w·Q = 1 + c/(3d) + cavSum/d` by (S1); finally
`(1 + c/(3d) + S/d) = (1 + c/(3d)) * (1 + zc * S)` via the exact identity
`(1 + c/(3d)) * zc c k = 1/d` (this is `field_simp; ring`; it is the same identity that powers
`ac`'s shape).  Second lemma: induction on `eroot = Real.log (ac ..) + Real.log (1 + zc*S)`
with `ac * rhoB ^ (1+2c) = (3/2)^c * (1 + c/(3d))` (from `Reach.ac`, `rhoB_pos`) and
`Real.log_mul`/`log_pow` bookkeeping; vertex counts add by `Vb`.
Python witness: `certify_local_amplitude` (486/486 exact; ground-truth cross-check error 0.0).

### (iii) The literal edge list / SimpleGraph glue  [mostly free]

`BridgeStep3.Ztot_eq_msum : Ztot t = msum (realize t)` is generic in the weights, so it
applies to `litRealize b` AS-IS -- the literal `msum` form is free.  What remains is the
`litEdges` instantiation of `BridgeStep3d.IsEdgeEnum` for the FULL finite competitor tree
(hub + arms + gadget): each edge listed once with weight `1/(deg u * deg v)` where `deg` is
the `SimpleGraph.degree` of the realized tree.  This is the one genuinely new mechanical
piece: build the graph by DFS addressing (as `BridgeStep3.realize` already does), prove
acyclicity + the degree computation (root degree `p + cH (+1)`, branch-node degrees `dB`,
cherry mid/leaf degrees 2/1).  Then `pi_eq_msum` (3d) turns `per L / Π deg` into the same
`msum` that (i)+(ii) evaluate.

### (iv) The hub seam and the squeeze  [~100 lines]

Define the literal hub (true root degree, no phantom):

```lean
/-- Literal competitor: hub with `cH` cherries, `p` arms, and optionally the gadget `b`.
    Hub degree `D = cH + p` (or `D+1` with the gadget); every hub-incident weight uses it. -/
noncomputable def litHub (cH p : ℕ) (arm : Branch) (g : Option Branch) : RTree := ...
```

**(S3) the exact finite-`p` factorization** (verified as exact rationals at `p ∈ {3,7,20,50}`):

    Ztot (litHub cH p arm (some b)) / Ztot (litHub cH p arm none)
      = Wb b * (1 + S'_p) / (1 + S_p)

with `S_p` the base hub cavity load and `S'_p = (D/(D+1)) S_p + (dB b * cav b)/((D+1) * dB b)
= (D/(D+1)) S_p + cav b/(D+1)` (note: by (S1) the gadget's raw cavity is `dB b * cav b`, and
the weight is `1/((D+1) dB b)`, so the added term is JUST `cav b/(D+1)` -- even simpler than
the Python module states it).  Proof: both sides factor through `tree_cavity_recursion` at the
hub; all non-hub factors are shared (arms) or `Wb b` (the gadget, by (ii)).

**The envelope** (replaces `branch_multiplicativity.py`'s "missing uniform O(1/p^2) constant";
`O(1/p)` suffices for the limit):

```lean
theorem hub_factor_envelope (cH p : ℕ) (arm b : Branch) :
    |(1 + S' cH p arm b) / (1 + S cH p arm) - 1| ≤ 2 / (p + 1)
```

from `S_p ≤ 1` term-by-term (`Q ≤ 1` -- i.e. `Zopen ≤ Ztot`, which is `Matched ≥ 0`;
child degree ≥ 1; `D ≥ p` terms each `≤ 1/D`) and `|S' - S| ≤ (S + cav b)/(D+1) ≤ 2/(D+1)`.
Then the bridge-completing statement is a squeeze, simpler than 4b's seam:

```lean
/-- THE AMPLITUDE BRIDGE: the raw hub ratio converges to the DEC amplitude. -/
theorem amplitude_bridge (cH : ℕ) (arm b : Branch) :
    Filter.Tendsto
      (fun p => Ztot (litHub cH p arm (some b)) / Ztot (litHub cH p arm none))
      Filter.atTop (𝓝 (Wb b))
```

and, composed with (iii)'s `pi_eq_msum` + `Ztot_eq_msum` and (ii)'s `logPhi_eq_log_Wb`:
`exp (logPhi b) = lim_p pi(T(hub_p + b)) / pi(T(hub_p)) * rhoB^(-V b)` -- the Step 4c target.
Python witnesses: `certify_hub_seam` (exact identity + envelope, 0 fails) and
`certify_limit_statement` (deviations inside `Phi * 2/(p+1)` at `p = 10, 40, 160`).

Bonus structural fact usable as a sanity lemma: for `b = arm` the hub factor is EXACTLY 1 at
every `p` (`S' = S` identically -- the added arm term equals the rescaling loss), so
`amplitude_bridge` for the arm is definitionally exact, not just limiting.

## After the bridge: the remaining distance to Conjecture 1 (gap audit)

Per `conjecture1_status.py` (R1-R7): R1, R2, R4 (Kelmans + strictness), R5 (single hub wins),
R6 (arm balancing / hub de-loading / level 5) are PROVEN at Python/paper level; R3 (Phi<=1)
is now the Lean capstone `phi_le_one`; R7 (global assembly) is "unconditional GIVEN R3"
(terminating confluent rewrite, `global_assembly.py` + `kelmans_confluence.tex`).  So once
(i)-(iv) land:

1. **Machine-checked core** = `phi_le_one` + the full bridge (Branch amplitude == raw
   permanent-ratio hub limit).  This is the crux R3 as a theorem about the REAL object --
   the right scope for the paper's formal claim.
2. **R7 + R4-R6 formalization** is a separate, larger campaign (rewrite systems, Kelmans
   moves); recommend the paper claims these at proof level with the Python certificates, as
   the ledger already does honestly.
3. **Independent review** of the potential-proof lemma STATEMENTS (the kernel checks proofs,
   not intent).  The fork session's review so far: no sorry/axiom/native_decide/placeholder
   anywhere on the branch; `Reach.cav`/`eroot`/`logPhi` match the DEC ground truth
   (`BRIDGE_DESIGN.md` validated identity + `general_children_crux` cross-check to 0.0 in
   `raw_amplitude_seam.py`); capstone chain CI-green at `1b554c14`/`aba6cd08`; 4b green at
   `575ffcae`.

## Suggested file layout

`BridgeStep4c.lean` -- items (i)+(ii) (pure `RTree`/rational, no analysis; fastest win).
`BridgeStep4d.lean` -- item (iv) (the hub seam + squeeze; needs only `Tendsto` algebra
already used in 4/4b).  Item (iii)'s `litEdges` can land last; (i)+(ii)+(iv) already give
the amplitude bridge at the `RTree`/`msum` level, with (iii) upgrading `msum` to
`per L / Π deg` via the existing `pi_eq_msum`.

## Item (iii) Lean decomposition (added by the bridge session, 2026-08-13)

Chunk (iii-a) -- the address graph and the `IsEdgeEnum` master lemma (generic in `E`):

```lean
abbrev AEdge := List ℕ × List ℕ × ℝ
def vertsOf (E : List AEdge) : List (List ℕ) := E.map Prod.fst ++ E.map (fun e => e.2.1)
def HasKey (E : List AEdge) (a b : List ℕ) : Prop :=
  ∃ e ∈ E, (e.1 = a ∧ e.2.1 = b) ∨ (e.1 = b ∧ e.2.1 = a)

/-- Adjacency `u ≠ v ∧ HasKey` makes looplessness FREE (no no-self-edge hypothesis needed
    for well-formedness; the ≠ is redundant on well-formed lists but harmless). -/
def aGraph (E : List AEdge) : SimpleGraph {a // a ∈ (vertsOf E).toFinset} where
  Adj u v := u ≠ v ∧ HasKey E u.val v.val
  symm := ...   -- Or.symm + Ne.symm
  loopless := fun u h => h.1 rfl

instance : DecidableRel (aGraph E).Adj :=   -- inferInstanceAs via List.decidableBEx
def liftEdges (E : List AEdge) : List (V × V × ℝ) :=   -- V the subtype
  E.attach.map (fun x => (⟨x.val.1, fst_mem_verts x.2⟩, ⟨x.val.2.1, snd_mem_verts x.2⟩, x.val.2.2))

theorem isEdgeEnum_liftEdges (E : List AEdge)
    (hnodup : E.Nodup)
    (hloop : ∀ e ∈ E, e.1 ≠ e.2.1)
    (hkeys : ∀ e ∈ E, ∀ f ∈ E,
      (f.1 = e.1 ∧ f.2.1 = e.2.1) ∨ (f.1 = e.2.1 ∧ f.2.1 = e.1) → f = e)
    (hw : ∀ e' ∈ liftEdges E, e'.2.2
      = 1 / (((aGraph E).degree e'.1 : ℝ) * ((aGraph E).degree e'.2.1 : ℝ))) :
    IsEdgeEnum (aGraph E) (liftEdges E)
```

Field proofs: `nodup` = `hnodup` through the injective attach-map (Subtype/Prod ext);
`adj` = `hloop` (Subtype.ext contrapositive) + `HasKey` by `Or.inl ⟨rfl, rfl⟩`; `weight` = `hw`
verbatim; `complete` = unpack `HasKey`, return the lift of the witness (mem_attach); `unique` =
push keyEq down to values (`Subtype.val` congr), apply `hkeys`, lift back (attach elements with
equal values are equal by proof irrelevance).  NOTE `msum (liftEdges E) = msum E` (weights and
conflict pattern are preserved by the lift -- a small induction; conflict on subtypes matches
conflict on values since Subtype.ext) -- needed to connect back to `Ztot_eq_msum`.

Chunk (iii-b) -- discharge the hypotheses for `realize (litHub ...)`-shaped edge lists:
`hloop`/`hnodup`/`hkeys` from the address-suffix machinery already in BridgeStep3
(`rEdges_allSuffix`, `suffix_eq_of_length`: an edge's child endpoint is strictly longer, keys
determine the child address); `hw` = the degree computation: `(aGraph E).degree ⟨a, _⟩` equals
the number of `E`-edges touching `a` (neighborFinset via the key filter), which for
`realize (litHub cH ch)` is `cH + #ch` at the root (true root), `dB K` at branch roots (parent
edge + children + cherries), `2` at cherry mids, `1` at leaves -- matching the constructed
weights by definition of `litCherry`/`litChildren`/`litHub`.  Then `pi_eq_msum` +
`msum (liftEdges E) = msum E` + `Ztot_eq_msum` + `Ztot_litHub`/`amplitude_bridge` complete:
`per L(T_p)/prod deg = Ztot (litHub ...)` and the hub ratio of the REAL graphs -> `Wb b`.

## Item (iii-b) sharpened decomposition (bridge session, 2026-08-13)

KEY INVARIANT (makes the combinatorial hypotheses one lemma): every edge emitted by
`rEdges b t` has the shape `e.2.1 = j :: e.1` for some `j` (`rRoot` emits `(a, i::a, w)`;
`rSub` recurses).  Call it `EdgeShape`.  Consequences:
* `hloop`: `e.1 ≠ j :: e.1` (length).
* `hkeys` cross-orientation is IMPOSSIBLE: `f.1 = e.2.1 ∧ f.2.1 = e.1` gives
  `e.1 = j' :: j :: e.1` (length).  Same-orientation reduces to the child endpoint.
* So ALL of `hnodup`/`hloop`/`hkeys` follow from `EdgeShape` + **`childNodup`**: the child
  endpoints `(realize t).map (·.2.1)` are pairwise distinct (address uniqueness -- mutual
  induction with the existing `rEdges_allSuffix`/`suffix_eq_of_length`/`subtree_disj`
  machinery; `hnodup` via `List.Nodup.of_map`).
* `hw` decomposes into (a) the generic degree-count lemma:
  `(aGraph E).degree u = (E.filter (fun e => e.1 = u.val ∨ e.2.1 = u.val)).length`
  (given `EdgeShape`-style key uniqueness; bijection touching-edges <-> neighbors, distinct
  other-endpoints else keyEq) and (b) the per-construction count: at address `a` of a node
  with children `cs`, touching edges = `#cs` + (1 if non-root), tied to `litRealize`'s
  construction degrees by induction: root `cH + p (+1)`, branch `dB K`, mid `2`, leaf `1` --
  exactly the constructed weights `litCherry d` / `litChildren d`.
Estimated ~350-450 lines over 2 files: `BridgeStep3f` (EdgeShape + childNodup + the three
hypotheses, generic in `t`), `BridgeStep4e` (degree-count + litHub weights + the composed
REAL-graph statement `per L / prod deg = Ztot (litHub ...)` via `pi_eq_msum` +
`msum_liftEdges` + `Ztot_eq_msum`).

## 4e part 2 spec (bridge session): touching-count = construction degree

Bridge `#(toFinset.filter touch)` to list counting once: for Nodup `E`,
`#(E.toFinset.filter p) = E.countP p` (via `List.countP_eq_length_filter` +
filter-toFinset-card).  Then a mutual induction over `rEdges/rRoot/rSub` computes, for each
vertex address, `countP (touch x)`:
* `rRoot a i cs` edges all have `e.1 = a`: contribute `cs.length` to `x = a`, exactly `1` to
  each `x = k :: a` (`k ∈ [i, i+cs.length)`, via `rRoot_child_eq`), `0` elsewhere;
* `rSub` contributions split by `countP_append`; cross-subtree addresses never touch
  (existing `subtree_disj`/suffix machinery);
* combined: for a node at address `y` with children list `cs` in the FULL realized list,
  `count y = cs.length + (1 if y is itself a child endpoint, i.e. y ≠ root)`.
Then the per-shape instantiation for `litRealize`/`litHub` (root `cH + p (+1)`, branch root
`dB K = #children + 1 + c`... note `litRealize`'s children INCLUDE the expanded cherries, so
`#cs = c + #ch` and `+1` is the parent edge -- exactly `dB`; cherry-mid `1 + 1 = 2`; leaf
`0 + 1 = 1`), discharging `hw` for `liftEdges (realize (litHub ...))` with the weights built
by `litCherry`/`litChildren`.  Finally compose:
`per L (aGraph E) / prod deg = msum (liftEdges E) = msum E = Ztot (litHub ...)` (3d + 3e + 3),
and `amplitude_bridge` (4d) turns the hub ratio of the REAL graphs into
`Wb b = exp (logPhi b) * rhoB^(Vb b)` -- the completed Step 4c target.
