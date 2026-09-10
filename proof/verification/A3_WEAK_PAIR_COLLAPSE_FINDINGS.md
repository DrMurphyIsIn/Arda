# A3 de-risk — the WEAK-pair collapse route to Hdom length>=3 (GREEN)

Branch `bg/multihub-hnorm`, 2026-09-08. Exact `fractions.Fraction` throughout. conjecture1_proved = False.

## The route

Collapse the DEEPEST two hubs of a Balanced+Capped backbone into a same-size Balanced+Capped single
hub; propagate the gain through the remaining hubs via the (move-agnostic, kernel-proven) B-track
G-machinery; iterate to a single hub; finish with the COMPLETED single-hub envelope (all residues,
all sizes) to the tie. If the per-collapse gain pair holds, Hdom length>=3 closes with NO new
global machinery.

## Finding 1 — the STRONG pair (B2's G1/G2) FAILS for the collapse

G2 (`Zopen/udeg <=`) fails badly when udeg jumps (pair udeg ~6 vs single-hub udeg ~15): e.g.
pair (4^5,0)::(4^5,0), size 92: pair Zopen/udeg = 1.90e7 vs best single 0.93e7. 6084 pairs tested,
strong pair FAILS on both general and stuck-only classes. ROOT-level Hdom still holds (best single
hub beats the pair by 10.5%) -- the failure is an artifact of the too-strong invariant, not a
threat to the chain.

## Finding 2 — the WEAK pair works and self-propagates

The replaced child enters every ancestor LINEARLY in the weight w = 1/(len+1) in (0,1]:
contribution = Ztot_c*(1+w*Q0) + w*(Zopen_c/udeg_c). By endpoint linearity in w, the sufficient
self-propagating invariant is:

    W1 : Ztot(dtSub c) <= Ztot(dtSub c')                       (w=0 endpoint)
    W2 : Ztot(dtSub c) + Zopen(dtSub c)/udeg c
           <= Ztot(dtSub c') + Zopen(dtSub c')/udeg c'          (w=1 endpoint)

Propagation algebra (verified symbolically by hand, to be formalized):
  parent Ztot   = PP*[ (1+w*Q0-w)*Ztot_c + w*(Ztot_c + Oc/uc) ]   -- positive combo of W1,W2
  parent W2-sum = PP*[ (1+w*Q0)*Ztot_c   + w*(Ztot_c + Oc/uc) ]   -- positive combo of W1,W2
  root Aobj     = PP*[ (1-1/L+Q0/L)*Ztot_c + (1/L)*(Ztot_c+Oc/uc) ] -- positive combo (L>=1)
(1+w*Q0-w >= 0 since w <= 1; strong pair G1+G2 implies W1+W2, so all B-track FLP results remain
instances.)

## Finding 3 — the collapse satisfies the weak pair UNIVERSALLY (measured)

Grid: armsA,armsB in {4,5}-multisets, 5 <= len <= 7; cA,cb in 0..5 -- 15,876 pairs. For EVERY pair
there is a Balanced+Capped single hub (a,b,c) of the same size with W1 AND W2 -- including all-4-arm
and de-loaded shapes. Witness pattern: the canonical target is c = 0, b = residue-minimal
(maximal five-arms). STUCKNESS IS NOT NEEDED: any Balanced+Capped m-hub state telescopes.

## Remaining work (Lean)

1. Weak-pair propagation lemmas (`dtSub_wpair_lift` + root closure) -- mechanical mirror of
   BGSCLFlpDeepLift's proofs via the positive-combination identities above.
2. The collapse certificate: W1 AND W2 for the canonical c=0 maximal-five target, as a symbolic
   polynomial family in (a5,a4,cA,b5,b4,cb) -- the researchy half; fully de-risked numerically.
3. Telescoping induction on hub count + wiring into SharpRateNF length>=3 with the DONE
   single-hub envelope (all residues, all sizes).

If (2) lands, Hdom closes for ALL lengths. Honest risk: the 6-parameter symbolic cert may need
residue-class case splits and could be heavy; numeric grid is bounded-range (len <= 7) -- the
symbolic cert must cover all lengths (expect a monotone tail argument as in the two-hub certs).

## Addendum (same day) — the THREE-clause collapse (telescope-ready)

The telescope's LAST collapse (length 2 -> 1) happens at the ROOT, where the dtSub weak pair does
not directly apply (root weight 1/L vs subtree 1/(L+1)).  So the collapse certificate needs a THIRD
clause: root-level `Aobj(pair) <= Aobj(target)`.  Re-measured on the full 15,876-pair grid: W1, W2
AND the root clause hold SIMULTANEOUSLY with a COMMON canonical target for every pair (0 fails).

Stage-1 Lean rail LANDED (R47WPairLift.lean, kernel-clean): dtSub_wpair_lift,
Aobj_child_replace_of_wpair, plugFrames_wpair, wpair_of_gains.

Pinned telescoping design (stage 3, conditional on the stage-2 cert):
  PairCollapse : Prop := for every Balanced+Capped pair, EXISTS a Balanced+Capped single hub of
    summed hubSize with (W1, W2, root-Aobj) -- exactly the three de-risked clauses.
  Transport: backboneU tail replacement through `init` hubs = inner dtSub_wpair_lift induction +
    root Aobj_child_replace_of_wpair (machinery all proven).
  Induction: strong induction on s.length, decomposing s = init ++ [h1, h2] via s.reverse;
    collapse the DEEPEST pair (a clean subtree; the first pair is not); stateSize conserved by the
    hubSize clause; result: any Balanced+Capped state is Aobj-dominated by a SINGLE Balanced+Capped
    hub of the same size.  Downstream: single hub <= tie = the DONE envelope + the tie-definition
    layer (non-aligned-n tie : N -> UTree selection -- separate, known-open assembly).

## Addendum 2 (2026-09-08) — PairCollapse v1 FALSIFIED and CORRECTED

The de-risk loop caught a genuine falsifier before the cert campaign: the Balanced+Capped pair
`(0,5,1 | 47,1,1)` admits NO single-hub target satisfying the w=1 W2 clause (best deficit 0.2%,
W1 and ROOT hold). PairCollapse as stated in R47MHubTelescope.lean is FALSE (harmless — it is an
explicit hypothesis, so the telescope is merely conditional-on-false there — but must be corrected).

THE FIX — sharpen the weight: Capped hubs give every backbone frame >= 6 children, so ancestor
weights obey w <= 1/7 (interior) / w <= 1/6 (root). Endpoint linearity then needs only
`W2' : Ztot + (1/6)·Zopen/udeg <=`. Positive combinations re-derived (coefficients X−6w >= 0 at
w <= 1/6; parent-W2' needs w <= 6/35 > 1/7 OK). Under (W1, W2', ROOT):
- all previously-dead shapes pass;
- d<=2 dense sweep 11853/11853; general sweep 3953/3953;
- NEAR-COLLAPSE ALONE IS UNIVERSAL — no swap phase, no chains.

Final architecture: ONE bounded case-table cert (per-d = cA+cb candidates: (−1,2,d−3) universal for
d=3..8, (0,1,5) at d=9, (1,0,5) at d=10, small candidate sets at d<=2 e.g. (−4,5,0)/(−3,4,0)/
(−2,3,0) + rare-shape alternates) with constant V-prefactor per cell => POLYNOMIAL clauses.
Lean v2 TODO: 1/6-weighted W-pair lift lemmas + corrected PairCollapse/transport with len>=6.
conjecture1_proved = False.

## Addendum 3 (2026-09-09) — the PairCollapse6 cert pipeline VALIDATED end-to-end

First cell executed completely:
- d=5 candidate (1,0,0) re-verified UNIVERSAL on a dense grid: 146,267/146,267 (exhaustive to
  len 12 + random to len 60), under the corrected 1/6-weighted triple.
- Symbolic emission (sympy, exact rationals): per-(d, cA) sub-cell, each clause clears to a
  DEGREE-3 polynomial in (a5,a4,b5,b4) with 21-27 terms over a denominator that factors into
  three positive linear forms. Constant prefactor for the (1,0,0) cell: V5/Vc^5 = 23/18.
- Sign structure (d=5): cA=0 -> ALL THREE clauses all-nonnegative (free certs); cA=5 -> W2'/ROOT
  free, W1 3 negs; cA=1..4 -> 3-5 negative monomials each (only linear terms + the constant).
- Lean closure test: the cA=1 W1 numerator (27 terms, negs -3346983 a4, -3960531 a5, -11649109)
  closes with plain `nlinarith` + Capped slack hints (products with b5+b4-5, a-slacks) in 2.8 s.

Campaign shape: ~11 d-values x 6 cA sub-cells x 3 clauses ~ 200 polynomial lemmas (many free),
plus per-cell bridge lemmas in the twoHub_reduced_cN style, plus the d<=2 candidate-selection
splits. The target (a5+b5+x, a4+b4+y, c') is ALWAYS Balanced+Capped (arms >= 11, c' <= 5) -- no
small-corner cases. Mechanical from here; same execution pattern as the residue-envelope campaign.
conjecture1_proved = False.

## Addendum 4 (2026-09-09) — bridge stage 2 status + the pilot reduction identity

Stage 2(i) LANDED (R47PC6Transport.lean, kernel-clean): dtSub_stats_child_congr, hub_stats_perm/
hub_stats_count, pair_stats_count -- arbitrary BalancedArms = count form for all four statistics.

Stage 2(ii) PILOT (d=5 primary cell (0,1,1), cA=1, W1) -- the reduction identity is CONFIRMED in
exact sympy (opaque power atoms pA5=V5^a5 etc., mirroring Lean's `ring` treatment):

    (RHS_closed - LHS_closed) / (pA5·pA4·pB5·pB4)
        = 27 · cellpoly / (30555040·(a4+a5+3)·(b4+b5+5)·(a4+a5+b4+b5+3))

(cellpoly = the emitted pc6_d5p_c1_W1 polynomial, exactly; the 27 and den come from cancel() in
lowest terms.)  LEAN TACTIC LESSONS from the pilot run:
  * scratch files MUST live inside proof/formalization AND wrap in namespace R3Cert/Step3 +
    open RTree PC6 (RTree is not a root-resolvable namespace from outside);
  * the reduction file must import BOTH R47PC6Transport and R47PC6Cells;
  * the one-shot route (rw closed forms; push_cast; pow_add; field_simp; nlinarith [atom-product
    x cell hint]) FAILS at the final linarith -- the cleared goal's shape does not align with the
    single product hint;
  * the ROBUST route (next session): factor the four power atoms FIRST --
      have hL : LHS = A * X := by field_simp; ring     (A = pA5·pA4·pB5·pB4; X,Y atom-free)
      have hR : RHS = A * Y := by field_simp; ring
      exact mul_le_mul_of_nonneg_left (X<=Y proof) A.nonneg
    with X<=Y a pure rational-function inequality in the four cast counts, closed by
    cross-multiplication + nlinarith [cellpoly lemma, den positives] -- the cleared difference is
    LITERALLY 27·k·cellpoly, a linear certificate.  X/Y transcriptions to be EMITTED by the
    generator (sympy knows them exactly), not hand-written.

Remaining: emit the 138 reduction lemmas via the atom-factored route, then the exists-assembly
(by_cases on the selection hypotheses, Balanced/Capped/hubSize of the target = arithmetic).
conjecture1_proved = False.

## Addendum 5 (2026-09-09) — the reduction TEMPLATE fully validated (all three layers green)

Pilot cell d=5p cA=1 W1, all layers compile with 0 errors:

  Layer 1 (hXY, atom-free X <= Y):
      rw [<- sub_nonneg]; have key : Y - X = (m*POLY)/(mden*DEN) := by field_simp; ring
      rw [key]; apply div_nonneg; . nlinarith [hcell]; . positivity
    -- X, Y = sympy cancel(stat/(pA5*pA4*pB5*pB4)) printed as (num)/(den) polys in the casts;
    -- m, DEN from cancel(Y-X) with numerator verified = m * cellpoly.
  Layer 2 (hL : pairstat = A * X, hR : targetstat = A * Y):
      rw [pairU_Ztot, hubU_Ztot, hubU_Zopen, hubU_udeg]; push_cast; field_simp; ring     (hL)
      rw [hubU_Ztot]; push_cast; rw [pow_add, pow_add, pow_succ]; field_simp; ring        (hR)
    -- A = (621/64)^a5*(513/80)^a4*(621/64)^b5*(513/80)^b4; bare field_simp suffices
    -- (no ne-battery needed on the pilot). MUST `open RTree` inside namespace Step3/PC6.
  Layer 3 (compose): calc pairstat = A*X := hL  _ <= A*Y := mul_le_mul_of_nonneg_left hXY
    (by positivity)  _ = targetstat := hR.symm

Remaining engineering for the batch (fresh session): generalize the emitter over all 46 cells x 3
clauses -- clause-variant rewrite lists (W2 adds pairU_Zopen/pairU_udeg + hubU_Zopen/hubU_udeg;
RT uses pairU_Aobj / hubU_Aobj with its `hpos` via (by omega)), Nat-subtraction cast handling for
negative (x,y) candidates (push_cast [Nat.cast_sub (by omega)]), selection-hypothesis casts, and
pow_add/pow_succ splits keyed to (x,y,cp). Then the exists-assembly. No open mathematics remains.
conjecture1_proved = False.
