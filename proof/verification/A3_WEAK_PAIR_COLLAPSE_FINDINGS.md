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
