# Self-hosting the reusable lemmas

Telperion's emitters lean on three lemmas proven **once** in Lean and reused:

| Lemma | Ships in | What it consumes |
|---|---|---|
| `Telperion.unimodal_peak` | `UNIMODAL_PRELUDE` (`emit_unimodal.py`) | an up→down (unimodal) sequence |
| `RTree.telescope` | telescope prelude (`emit_telescope.py`) | per-node super-solution margins |
| `Telperion.wz_row_invariant` | `WZ_PRELUDE` (`emit_wz.py`) | the telescoping row identity |

Until now those lemmas were **hand-authored Lean that the emitters trust**.
Self-hosting closes the loop: the concrete hypotheses each lemma consumes are
certified by the same exact-arithmetic discipline as everything else.

## The two halves

1. **Exact-tier certification (local, verified).**
   `src/telperion/self_hosting.py` certifies one concrete instance of each
   lemma's hypotheses in exact rational arithmetic, and asserts each is
   **load-bearing** — a corruption of the instance breaks the certified property,
   so the lemma's conclusion is earned, not vacuous.
   Verified by `tests/test_self_hosting.py` (runs anywhere, no Lean).

   ```python
   from telperion.self_hosting import certify_all
   for r in certify_all():
       print(r.lemma, "certified" if r.certified else "FAILED",
             "load-bearing" if r.load_bearing else "vacuous")
   ```

2. **Kernel compilation (cloud-gated).**
   The prelude lemma + the instance that invokes it compile against pinned
   Mathlib via `lake build` in CI. This machine does **not** build Lean (SoC
   watchdog), so this half runs only in cloud CI — the honest completion gate.
   The emitters already emit these preludes; CI's `telperion-lean-e2e` /
   `telperion-production` jobs are where the kernel check happens.

Together: the reusable-lemma layer is no longer merely trusted — its hypotheses
are certified locally and its Lean is kernel-checked in CI.
