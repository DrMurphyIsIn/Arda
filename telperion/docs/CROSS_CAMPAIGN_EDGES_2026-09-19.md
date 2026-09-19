# Cross-campaign dependency edges in the missions registry (2026-09-19)

*`conjecture1_proved = False`. This is registry plumbing, not mathematics.*

## The problem

`load_campaign` rejected any `depends_on` target outside its own campaign. The
corpus is emphatically cross-campaign: mirrormere's Route-D nodes consume rh's
`E6Bridge*` results on the `rvm_bridge` island. With no way to say so, authors
reached for the nearest same-campaign proxy while the node title named the real
source, and the 2026-09-18 registry audit found **five nodes whose dependency
edges the corpus does not support**. The audit also found that all 44 live proof
links are `via = direct`: the `reduction` mechanism, the one that actually
consumes dependency edges, had never been used once.

So the registry has been recording a chain of reductions toward a conjecture
while in fact holding a collection of independent direct proofs. The edges were
decorative. This change makes them mean something, which is also what makes it
dangerous, hence the emphasis below.

## The mechanism

A `depends_on` entry is now one of:

| form | meaning |
|---|---|
| `RH_corridor_bound` | a node in the same campaign (unchanged, still the default) |
| `rh:RH_corridor_bound` | the node `RH_corridor_bound` in the campaign whose **directory** is `rh` |

The campaign part is the directory name, not `manifest.name`: the directory is
what `--campaign` takes and what a reference must resolve against (`rh`, not
`RH.conjecture`).

Three layers, deliberately separated:

1. **`load_campaign(root)`** validates internal references exactly as before. An
   external reference is checked for *syntax* and *file existence* only
   (`<root>/../<campaign>/nodes/<slug>.toml`). It does not load the other
   campaign, so there is no recursion and no load-order coupling.
2. **`load_universe(missions_root)`** loads every campaign, resolves every
   external reference for real, and asserts **global** acyclicity. A cycle like
   `rh:A -> mm:B -> rh:A` is invisible to any per-campaign check by
   construction; this is the layer that sees it.
3. **`compute_universe_closures(universe)`** runs one global closure fixpoint
   keyed by `(campaign, slug)`.

`verify_campaign` auto-loads the sibling universe when it can, and falls back to
`None` when it cannot, which leaves every external edge dirty.

## The anti-cascade rule

A cross-campaign edge is a new path for an unverified premise to reach a
`proved` node. The 2026-09-18 audit *demonstrated*, on a throwaway campaign,
that the gate could mark a node proved from a stub. So the rule here is stated
as a single invariant and tested from the negative side:

> An edge counts toward a clean closure only when its target genuinely
> resolves, has status `proved`, **and** is itself closure-clean under the
> global fixpoint. Every other case is dirty. There is no code path that turns
> an unresolved, unproved, or dirty edge clean.

Two specific traps, both of which bit during implementation and are now tests:

- **No universe, external edge.** Returns dirty. A caller who forgets to pass
  the universe gets a conservative answer, never an optimistic one.
- **Never trust the target's stored flag.** The first implementation fell back
  to the external node's stored `closure_clean` when no global pass was
  available. That is exactly how transitive dirt launders across a boundary: a
  reduction node's stored flag can read `True` while its own chain is dirty.
  `test_transitive_dirt_propagates_across_campaigns` caught it. The fallback is
  gone; the global fixpoint is computed instead.

Note that a **direct** proof is unaffected by its dependency edges, by design:
it stands on its artifact and the gate that checked it. Edges constrain
`reduction` proofs. That asymmetry is why the registry could accumulate
unsupported edges without any node becoming falsely clean.

## What this does not do

- It does not fix the five unsupported edges. Only one of them
  (`MM_weil_form_certified_height`, which needs `rh:RH_rvm_unconditional`) is a
  genuine cross-campaign case, and it lives on an unmerged branch. The other
  four are dependency-correctness questions the mechanism cannot settle: a node
  whose title refutes its own edges needs an author's judgement, not a syntax.
- It does not make anything proved, and no node's status changes here.
- It does not retro-fit `via = reduction` anywhere. The reduction relation is
  now usable across campaigns; whether a given proof is a reduction remains a
  claim its author must make and the gate must check.

## Tests

`tests/test_missions_cross_campaign.py`, 19 tests, most of them negative:
malformed references, missing target, missing campaign, internal validation
unchanged, global cycle detection, and six closure cases covering unproved,
proved-but-dirty, no-universe, transitive dirt, and the direct-proof asymmetry.
The full mission subset stays green at 331 passed, and all four real campaigns
load as a universe and verify OK.

## Follow-up landed with this mechanism: the reduction premise precondition

Ascent-plan op **F1-2**. `grant_status` now refuses to flip a node whose proof
is `via = "reduction"` when any `depends_on` target is not already `proved`, or
does not resolve at all. Cross-campaign targets resolve through the universe.

A `direct` proof is deliberately exempt, for the same reason its closure is
exempt: it stands on its artifact and the gate that checked it, and its edges
are documentary. Enforcing the precondition on direct proofs would have blocked
legitimate grants whose edges merely record context, and would not have caught
the demonstrated exploit, which was a stub artifact rather than a bad edge.

With this, a reduction node cannot be granted over a draft, open, or
unresolvable premise, and cannot be *closure-clean* unless the whole chain is
clean under the global fixpoint. Those are two different checks and both are
now present: the first at the moment of granting, the second continuously.

**Not done, and why.** Ops F1-3 and F1-4 would extend the closure fixpoint to
`direct` proofs behind a `closure_override_reason` field. That is a semantic
change to what `closure_clean` means for 43 already-clean nodes, so it needs an
owner's decision rather than an implementer's; it is left queued.

