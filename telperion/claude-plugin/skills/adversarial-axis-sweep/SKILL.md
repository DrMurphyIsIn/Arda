---
name: adversarial-axis-sweep
description: Use when a hard conjecture (RH, a BG bound, any "wall") has resisted direct attack and you want to MAP why — an honest multi-agent sweep that searches one named axis/direction for an unconditional PARTIAL foothold, adversarially refutes each candidate, and reports where the wall actually is. Produces a diagnostic map + kernel-probe shapes, never a proof. Use for "is there any partial handle on X from direction D?" and for building a completeness argument that a family of approaches cannot reach the wall.
---

# Adversarial axis-sweep — mapping a wall by honest elimination

A research methodology (a `Workflow`) for hard conjectures. It does **not** try to
prove the conjecture. It picks one **axis/direction** (a coordinate of the problem —
e.g. for RH: weight/multiplicativity, ordinate statistics, real-part, joint
real-part×ordinate) and asks: *is there an unconditional PARTIAL foothold here that
does real work without being equivalent to the conjecture?* Then it kills each
candidate adversarially and reports the honest verdict. Run once per axis; the union
of sweeps is a **wall map**.

**Standing invariant: `conjecture1_proved = False`.** Nothing a sweep produces proves
the target. Overclaiming is the cardinal sin. Every survivor must be reduced to a
kernel-probe *shape* that the main session builds and verifies separately.

## The three-phase shape (Workflow pipeline)

1. **Analyze** — one agent per candidate object on the axis. Each answers, honestly:
   does it break the wall's defining symmetry *unconditionally*? does its infinite/
   uniform form *collapse to the conjecture*? is there a partial foothold that is
   unconditional AND reaches beyond finite/almost-all? State the foothold's **honest
   limitation in its own voice** (the prize is a real structure disclosing its own
   reach). Web-verify every literature claim or mark it unverified.
2. **Refute** — per surviving foothold, N adversarial skeptics with *distinct lenses*
   (e.g. "secretly symmetry-invariant", "actually conjecture-equivalent", "finite-only").
   Majority-refute kills it. Default each skeptic to `survives=false` if it can.
3. **Synthesize** — one high-effort agent: is the axis reachable or irreducible? do the
   finite footholds occupy the "landmark-not-lever" slot? does this axis reduce to the
   same single clause as the others (wall-map completeness)?

Use `schema` on analyze/refute for structured output. Use `pipeline` (refutation of a
candidate starts as soon as its analysis completes), barrier only before synthesis.

## Non-negotiable honesty gates (learned the hard way)

- **A throttled verifier is NOT a refutation.** If the Refute phase rate-limits (it
  will, at scale — 15–18 agents), the "0 survivors" verdict is **analyze-grade, not
  adversarially-confirmed**. Report it as such. Resume once or twice; if it keeps
  throttling, STOP and label the verdict honestly rather than chase a false negative.
- **Analyze-grade ≠ kernel.** The whole sweep is a research narrative. The only thing
  that *counts* is a kernel brick built + `#print axioms`-verified by the main session
  from a survivor's probe shape (see the `reflection-insensitivity` / no-go-certificate
  emitters). The sweep points; the kernel certifies.
- **Verify citations.** Fetch arXiv/DOI; a plausible-sounding lemma is not evidence.

## Precedent (RH campaign, 2026-09)

Four sweeps mapped RH's wall from every coordinate axis: **weight = free**,
**ordinate = orthogonal** (Selberg S(t) 2nd moment, reflection-blind), **horizontal =
free-or-RH**, **joint real-part×ordinate = RH-irreducible** — all reducing to the one
temperedness/growth clause. Each axis's kernel core was a reflection-invariance no-go
certificate (`OrdinateInsensitivity`, `same_ordinate_partner`). The finite Turing
ladder + PRZZ occupy the "landmark-not-lever" slot on the joint axis. The map is the
result — a verified statement of which way the summit is *not*, and the single
direction it must be. `conjecture1_proved = False`.
