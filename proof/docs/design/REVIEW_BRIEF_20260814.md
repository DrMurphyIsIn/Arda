# Independent review brief -- the 2026-08-14 arc (MR !69)

You are an independent, adversarial reviewer of a chain of exact-arithmetic and symbolic
certificates claiming to close Stage II of the R7' architecture for the Brualdi--Goldwasser
Laplacian-ratio maximizer.  The certificates are self-verifying (run_all() asserts), so your
job is the STATEMENTS, the MODELS, and the COMPOSITION: do the theorems say what the
architecture needs, and do the stages actually chain?  Work from the sources fresh; do not
trust docstrings.  A "pass" you cannot defend is worse than a fail.

Repo: proof/verification/ on branch review/kelmans-boundary (MR !69).
Start from formalization/R7_ARCHITECTURE.md, then formalization/HANDOFF_20260814.md.
Run: `python3 proof/verify.py` (venv py3.14).

## The claimed chain (verify each link's SEMANTICS)

1. RATE IDENTITY (rate_bound_fixed_n.py): pi(T) = Z(T^r) * R(r) for every tree at every
   leaf root, Z = the phantom-root matching sum == the Lean bridge object.  CHECK: the
   phantom convention against BridgeStep4c's litRealize (the tie N(5,0) must give exactly
   621/64); the A0/A1 linearity argument; S <= 1 (the injection); R formula.
2. LEDGER IDENTITY (slack_ledger_dichotomy.py): logPhi = -phi(root) - SUM slack, slack >= 0.
   CHECK: chi/eroot formulas against proof_via_explicit_potential; that (SS) with c = 0.22 is
   the CI-green Lean DeficitNonneg (quantifiers: nl arbitrary!); the folded-ARM exclusion.
3. THE MERGE LAYER (kelmans_mixed_load -> kelmans_unified_merge): the exact bilinear identity
   (verify against literal permanents); the box/marginal bounds (psi_close piece (2) import);
   the 36-cell table's environment condition (3deg+4load >= 16, later 15); the topped-up
   merge's vertex accounting (donor lands as a load-5 arm, k arms downgraded -- SAME n).
4. DOMINATIONS (kelmans_vertex_budget, g34_residual_domination, g34_multi_starofhubs,
   g34_deep, interpolation_lemma): every stuck family strictly below a same-n single-hub
   comparator.  CHECK ESPECIALLY:
   a. COMPARATOR SOUNDNESS: the searched comparators are genuine trees at the SAME n
      (vertex accounting per defect type: leaf 1, arm1 3, arm2 5, arm(c) 1+2c); the
      defect-carrying template's F_D^j cancellation; the per-residue search's n-matching
      (rem % 11 arithmetic).
   b. THE INTERPOLATION LEMMA'S TWO IDENTITIES: cav(q) = 23/(26q+23) and B*rhoB =
      26/(23+3cav) (uses F(1,5) = rhoB^11 EXACTLY -- check); the sign polynomial
      23z - 3 - 3Tz derivation (does the bound's cavity-dependence really factor this way?
      re-derive d/dc of log[prod 26/(23+3c_i) * (1 + z(sigma+SUM c))] yourself).
   c. STUCKNESS COVERAGE: do the dominated families actually cover every configuration on
      which NO certified move fires?  (The claimed cover: two-hub + depth-2 stars, top- or
      sub-defected + depth-3 finite + depth>=4 generic + theta-generic.  Look for shapes
      outside: e.g. mixed top-AND-sub defects on depth-2; defected DEEP trees below theta;
      donors with 4 <= arms < 5-cb; loads cB in 1..4 on sub-hubs in the star certs.)
5. THE GENERIC THETA-LEMMA (g34_deep): theta = log(6/(5C1)) + DELTA.  CHECK: R <= 6/5 needs
   a cherry-tip root -- verify the "every survivor contains a cherry" claim; DELTA = 0.015
   vs the measured deficit AND the G5 tail claim; the n >= 421 vs n < 421 split.
6. THE DE-LOADING SCHEDULE (gap_discharges): the four shedding lemmas' shared-Sigma trick --
   is linearity in the profile sum s correct, and are the endpoints [K z16, K z14] valid
   bounds for {4,5,6}-load arm profiles?  The c0 <= 7 / j-range caps and their tails.
7. AMORTIZED HUB BOUND: the charging scheme's no-double-counting argument; the window's
   exclusions (5-bundle at 0.130, 3-bundle at 0.200) vs EPS = 0.029.

## Mandatory adversarial checks

A. Re-run verify_20260814.py yourself; confirm every module's asserts fire on perturbation
   (flip one constant, confirm failure, restore).
B. Hand-recompute: the two-hub dichotomy at (cA,cb,pA,pB) = (0,1,3,2) from the closed form;
   one interpolation-lemma curve point (q = 4); one heavy-top endpoint value.
C. Hunt REAL counterexamples where certificates are interval-float (heavy-top endpoints,
   ledger floors): push adversarial configs numerically-exactly against the claimed margins.
D. The composition audit: walk one concrete stuck configuration of each family through the
   architecture (which stage kills it, with what margin) -- including one you construct to
   be as adversarial as possible.
E. Scope honesty: list every place the rigor is grid/interval rather than symbolic, and
   check each is flagged in-module (G1 targets).  Any UNFLAGGED numeric step is a finding.

## Report format

Write formalization/REVIEW_20260814_ARC.md: verdict per numbered item (PASS/FAIL/CONCERN);
the hand computations; counterexample hunts attempted and their outcomes; a section "what
the certificates do NOT establish"; overall verdict = the strongest claim the arc supports,
one sentence.  conjecture1_proved must remain False regardless of verdict (G1/G7/review).
