export const meta = {
  name: 'bg-hwh-refutation',
  description: 'Resolve hwh/Hnorm truth status: verify T(6,6,6,6) > tieArgmax(52) under repo exact Aobj, characterize, prep Lean refutation',
  phases: [
    { title: 'Verify+Skeptic', detail: '4 independent exact-Fraction engines + adversarial skeptic (barrier)' },
    { title: 'Characterize', detail: 'sweep aligned n, reconcile with repo broadened-tie knowledge' },
    { title: 'FormalizePrep', detail: 'draft exact Lean counterexample skeleton' },
  ],
}

const WT = '/Users/peterwmurphy/repos/Arda-wt-armrate'
const BASE = [
  'Repo worktree: ' + WT + ' (branch bg/multihub-hnorm). Use exact fractions.Fraction ONLY (no floats). Python3.',
  'Run scripts from the directory that makes relative imports work (a3_derisk lives in telperion/scratch; verification scripts in proof/verification insert that path).',
  'Known baseline (fast cavity engine a3_derisk.Aobj_node): Aobj(T(6,6,6,6)) = 1180837892027061/26306674688; tieArgmax(52) = 4695479375868117/104857600000 at (a,b,c)=(0,5,3); diff = +8862581903961897/82208358400000 (POSITIVE).',
  'T(6,6,6,6) = 4 core vertices in a path, each with 6 length-2 pendant paths (cherries), n=52.',
  'A hub(a,b,c) = single vertex with a load-5 arms + b load-4 arms + c cherries, where armU(j)=node(j cherries), cherryU=node[leaf]. Constraint for a size-52 single hub: 11a+9b+2c=51, a+b>=5, c<=5.',
  'Your job is INDEPENDENT verification, so do NOT just trust the baseline; recompute from the repo own definitions.',
].join(' ')

const VERIFY_SCHEMA = {
  type: 'object',
  additionalProperties: false,
  required: ['engine_description', 'aobj_T_exact', 'tie_exact', 'sign', 'agrees_with_baseline', 'method_notes'],
  properties: {
    engine_description: { type: 'string', description: 'What engine/route you used' },
    aobj_T_exact: { type: 'string', description: 'Exact rational for Aobj(T(6,6,6,6)) as num/den' },
    tie_exact: { type: 'string', description: 'Exact rational for tieArgmax(52) (max Balanced+Capped state of size 52) as num/den' },
    sign: { type: 'string', enum: ['T>tie', 'T<tie', 'T=tie', 'inconclusive'], description: 'Sign of Aobj(T) - tie' },
    agrees_with_baseline: { type: 'boolean', description: 'Do BOTH your exact rationals match the baseline exactly?' },
    method_notes: { type: 'string', description: 'Key findings, any divergence, subtleties (rooting, size, class membership)' },
  },
}

phase('Verify+Skeptic')

const verifiers = [
  {
    label: 'verifyA-ztot-cavity',
    prompt: BASE + '\n\nENGINE A - REPO Ztot CAVITY (ground truth = Lean). Port the repo EXACT recursion VERBATIM and compute Aobj = Ztot(dtRealize .).\n'
      + 'CavityTree.lean 38-49: Zopen(node cs)=Popen cs; Ztot(node cs)=Popen cs + Matched cs; Popen []=1, Popen((_,c)::rest)=Ztot c * Popen rest; Matched []=0, Matched((w,c)::rest)= w*Zopen c*Popen rest + Ztot c*Matched rest.\n'
      + 'R47Tree.lean 33-57: udeg(node cs)=cs.length+1; dtSub(node cs)=RTree.node(dtChildren (cs.length+1) cs); dtChildren _ []=[]; dtChildren d (K::rest)=(1/(d*udeg K), dtSub K)::dtChildren d rest; dtRealize(node cs)=RTree.node(dtChildren cs.length cs). Aobj(t)=Ztot(dtRealize t).\n'
      + 'Read these files in ' + WT + '/proof/formalization/R3Cert/ to confirm. Write a SELF-CONTAINED Python script (exact Fraction, NO external imports) so it is a truly independent oracle. Encode T(6,6,6,6) as the UTree (node with 6 cherryU + nested node 4 deep) and each size-52 hub(a,b,c). Compute Aobj(T(6,6,6,6)) and tieArgmax(52)=max over valid (a,b,c). Report exact rationals, whether they match baseline, and the argmax (a,b,c). This is the decisive oracle - it must reproduce the repo exact rooted Aobj.',
  },
  {
    label: 'verifyB-unrooted-perL',
    prompt: BASE + '\n\nENGINE B - UNROOTED per(L)/prod(deg), independent permanent/matching engine. Compute Aobj as sum over matchings M of prod 1/(deg u * deg v) (monomer-dimer partition function). Reuse perL_tree from proof/verification/exhaustive_maximizer_check.py as ONE method, and write a SECOND independent linear tree-DP over matchings (NOT exponential all-subsets). Build T(6,6,6,6) and size-52 hubs as adjacency graphs, compute per(L)/prod(deg) exactly.\n'
      + 'CRITICAL: confirm ROOT-INVARIANCE - the repo Lean Aobj is rooted (root-dependent by definition), so verify that for these trees the value is the SAME across ALL rootings (call a3_derisk.Aobj_node on several rerootings) and equals unrooted per(L)/prod(deg). This is the linchpin making the rooted-Lean counterexample valid for the forall-t quantifier. WARNING: a3_derisk.unrooted_Aobj is EXPONENTIAL and HANGS on n=52 - do NOT call it; use a polynomial tree-DP. Report exact rationals, whether root-invariant, agreement with baseline.',
  },
  {
    label: 'verifyC-broadened-closedform',
    prompt: BASE + '\n\nENGINE C - CLOSED-FORM / BROADENED FAMILY. Confirm tieArgmax(52) is the argmax over hubTriples(52) using the repo broadened-tie machinery. Read proof/verification/broadened_tie_family.py (V(K,m) closed form) and telperion/scratch/c1_nearstar.py. For n=52: enumerate all (a,b,c) with 11a+9b+2c=51, a+b>=5, c<=5; compute each hub Aobj via BOTH a closed-form V-style expression AND a direct cavity call, confirm agreement, report the argmax triple and its exact Aobj. Separately recompute Aobj(T(6,6,6,6)) via a matching-polynomial / transfer-matrix expansion along the 4-core caterpillar spine (independent of the generic cavity). Report exact rationals, argmax (a,b,c), agreement with baseline. Also: does the broadened-tie doc acknowledge a NON-hub tree beating the best hub at aligned n, or only hub-vs-hub (near-star vs broadened) trades?',
  },
  {
    label: 'verifyD-balcap-envelope',
    prompt: BASE + '\n\nENGINE D - BALANCED+CAPPED ENVELOPE. Establish tieArgmax(52) is the max over the ENTIRE Balanced+Capped class (single AND multi-hub) of size 52. Read R47Step.lean:41-45 (Balanced/BalancedArms), R47Capped.lean:39 (Capped), R47StepSize.lean:83-86 (stateSize/hubSize), R47WPair6.lean:336-352 (mhub_le_single_of_pairCollapse6), R47HubState.lean (backboneU/hubState), R47AlignedMinSize.lean:32 (capped_state_size_ge_46).\n'
      + 'Tasks: (1) Confirm T(6,6,6,6) is NOT Balanced+Capped (hubs have 0 arms + 6 cherries; Balanced needs arms in {4,5}, Capped needs >=5 arms, c<=5 fails). (2) Since each Balanced+Capped hub has stateSize >=46, TWO hubs >=92 > 52, so verify there is NO multi-hub Balanced+Capped state of size 52 - the class at size 52 is EXACTLY the single hubs (a,b,c). (3) Compute usize(T(6,6,6,6)) and stateSize of the tie hub, confirm both =52. Report the exact tie rational, aobj_T rational, and whether the Balanced+Capped-max at 52 equals tieArgmax(52).',
  },
]

const SKEPTIC_SCHEMA = {
  type: 'object',
  additionalProperties: false,
  required: ['rooting_verdict', 'size_verdict', 'class_verdict', 'aobj_def_verdict', 'scoping_verdict', 'overall', 'hole_description'],
  properties: {
    rooting_verdict: { type: 'string' },
    size_verdict: { type: 'string' },
    class_verdict: { type: 'string' },
    aobj_def_verdict: { type: 'string' },
    scoping_verdict: { type: 'string' },
    overall: { type: 'string', enum: ['AIRTIGHT', 'REAL_HOLE', 'UNCERTAIN'] },
    hole_description: { type: 'string', description: 'If REAL_HOLE or UNCERTAIN, describe precisely; else empty' },
  },
}

const skepticPrompt = BASE + '\n\nYou are the ADVERSARIAL SKEPTIC. BREAK the claim "Aobj(T(6,6,6,6)) > tieArgmax(52) implies Hnorm is FALSE at n=52". Try every failure mode, report whether any is a REAL hole:\n'
  + '1. ROOTING: Aobj := Ztot(dtRealize t) is root-DEPENDENT (R47Tree.lean scope note line 17). Conjecture is forall t, Aobj t <= Aobj(tie(usize t)). Does the counterexample survive for the SPECIFIC rooting T is written with? Is T Aobj root-invariant? Is tieArgmax Aobj at the SAME rooting convention (backboneU roots at first hub)?\n'
  + '2. SIZE: does usize(T(6,6,6,6)) equal stateSize(tie hub)=52? Any off-by-one between usize (R47StepSize.lean:32) and stateSize/hubSize (R47StepSize.lean:83)?\n'
  + '3. CLASS: any Balanced+Capped hub-state of size 52 NOT of the form single hub(a,b,c)? Does hubTriples(52) enumerate ALL of them? Is min-size-46 correct so no multi-hub state fits in 52?\n'
  + '4. Aobj DEFINITION: could the repo Aobj differ from per(L)/prod(deg) so the inequality flips (memory phi11_not_classical_bg)? Verify the tie closed-form (26/23)(621/64)^K matches Aobj on hubs at K=1,2,3 in the repo OWN cavity.\n'
  + '5. SCOPING: is the conjecture maybe NOT forall-t but restricted so T is excluded? Read R47TopCapstoneFixedN.lean:48 and R47TieArgmax.lean:119.\n'
  + 'Read the actual Lean files in ' + WT + '/proof/formalization/R3Cert/. Run your own exact-Fraction checks. Report each failure mode with a verdict and an overall verdict: AIRTIGHT or REAL_HOLE or UNCERTAIN.'

const skeptic = agent(skepticPrompt, { label: 'skeptic-break-counterexample', phase: 'Verify+Skeptic', effort: 'high', schema: SKEPTIC_SCHEMA })

const verifyResults = await parallel([
  ...verifiers.map(v => () => agent(v.prompt, { label: v.label, phase: 'Verify+Skeptic', schema: VERIFY_SCHEMA })),
  () => skeptic,
])

const engines = verifyResults.slice(0, 4).filter(Boolean)
const skepticResult = verifyResults[4]

const positives = engines.filter(e => e.sign === 'T>tie')
const agreeing = engines.filter(e => e.agrees_with_baseline && e.sign === 'T>tie')
const consensus = agreeing.length >= 3 && skepticResult && skepticResult.overall === 'AIRTIGHT'
const dissolved = engines.some(e => e.sign === 'T<tie' || e.sign === 'T=tie') || (skepticResult && skepticResult.overall === 'REAL_HOLE')

log('Verification: ' + positives.length + '/4 engines say T>tie; ' + agreeing.length + '/4 agree exactly with baseline; skeptic=' + (skepticResult ? skepticResult.overall : 'null'))

let characterization = null
let formalizePrep = null

if (consensus && !dissolved) {
  phase('Characterize')
  const charPrompt = BASE + '\n\nCONSENSUS REACHED: 4 engines confirm Aobj(T(6,6,6,6)) > tieArgmax(52) exactly; skeptic AIRTIGHT. CHARACTERIZE and RECONCILE.\n'
    + '1. SWEEP: for aligned sizes n in {46,52,56,68,79,84,90,101,112,123} and all 1+11K near them, and for multi-hub caterpillar families (T(t,t,t,t), T(t,t,t), T(t,t), cherry-spiders single-hub-with-c-cherries, mixed), compute max Aobj per family vs tieArgmax(n) (exact Fraction, fast cavity a3_derisk.Aobj_node - NOT exponential unrooted_Aobj). Find the EXACT set of aligned n where SOME non-Balanced+Capped tree beats tieArgmax(n). Hint: T(6,6,6,6)@52 beats but T(8,8,8,8)@68, T(10,10,10,10)@84 may LOSE - the window may be finite. Nail boundaries and the winning family at each n.\n'
    + '2. RECONCILE: read proof/docs/BG_TIE_CORRECTION_RELAY_2026-09-05.md, BG_BROADENED_TIE_FAMILY_2026-09-05.md, BG_CLOSURE_PROGRAM_STATUS_2026-09-06.md, proof/verification/exhaustive_maximizer_check.py. Does the repo already know a NON-hub tree beats the best hub at aligned n>=46? (Its exhaustive check is n<=20; broadened-tie is hub-vs-hub only.) Is T(6,6,6,6)@52 genuinely NEW?\n'
    + '3. ARCHITECTURE VERDICT: is conjecture1 salvageable with a CORRECTED per-size tie family (multi-hub caterpillars), or is the Balanced+Capped hub normal-form Hnorm fundamentally wrong at aligned n (=> the whole reduction refuted)? What is the true maximizer at n=52 (search broadly)? Report exact rationals for boundary cases, winning family per n, crisp architecture verdict.'
  characterization = await agent(charPrompt, { label: 'characterize-and-reconcile', phase: 'Characterize', effort: 'high' })

  phase('FormalizePrep')
  const prepPrompt = BASE + '\n\nCounterexample CONFIRMED and AIRTIGHT. Draft the EXACT Lean formalization skeleton for a kernel-checked refutation lemma, following flp_context_lift_book_false + Aobj_factor in ' + WT + '/proof/formalization/R3Cert/BGSCLRealOblACaseALift.lean:207-252. Read that file to copy the exact pattern (Aobj_factor, qSum_cons, Ztot_dtSub_*, Zopen_dtSub_*, udeg_*).\n'
    + 'DELIVERABLE (text, no build needed):\n'
    + '1. The explicit Lean UTree literal for T52 = T(6,6,6,6). Give the exact term.\n'
    + '2. Confirm from R47HubState.lean the hubState signature/arg order and that the argmax (a,b,c)=(0,5,3) means 0 load-5 + 5 load-4 + 3 cherries; give the exact backboneU/hubState term for the tie and its Aobj = 4695479375868117/104857600000. Aobj(T52) = 1180837892027061/26306674688.\n'
    + '3. Proof strategy for: theorem r47_hnorm_false_at_52 : Not (exists s : List Hub, Balanced s and Capped s and stateSize s = 52 and Aobj T52 <= Aobj (backboneU s)). Use tie_ge_of_mem (R47TieArgmax.lean:64) to bound single-hub states <= tieArgmax 52, capped_state_size_ge_46 to rule out multi-hub states at 52, compute Aobj T52 > Aobj(tieArgmax 52) via norm_num, contradiction.\n'
    + '4. List exact helper lemmas needed (which Ztot_dtSub_*/Zopen_dtSub_* exist vs must be created; whether Aobj(T52) needs new cavity-value lemmas for the 6-cherry hub and the 4-deep backbone). Identify the HARDEST part (likely computing Aobj(T52) closed-form in Lean).\n'
    + '5. Which files to add to AxiomGuard.lean + proof-lean.yml. Be concrete and exact.'
  formalizePrep = await agent(prepPrompt, { label: 'draft-lean-skeleton', phase: 'FormalizePrep', effort: 'high' })
}

return {
  verdict: consensus && !dissolved ? 'CONFIRMED' : (dissolved ? 'DISSOLVED' : 'INCONCLUSIVE'),
  engines,
  skeptic: skepticResult,
  characterization,
  formalizePrep,
}
