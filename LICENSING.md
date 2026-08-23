# Licensing

This repository uses a split licensing model, effective 2026-08-21.

## The mathematics: Apache-2.0 / CC-BY-4.0

Everything OUTSIDE `telperion/` — the Brualdi–Goldwasser proof campaign
(`proof/`), all Lean 4 formalizations and their example workspaces
(including the knapsack/3XOR proof-complexity results under
`telperion/examples/g1_floors/lean/`), write-ups, and documentation — is
and remains:

- **Code and Lean proofs:** [Apache License 2.0](LICENSE)
- **Documents, notes, figures:** [CC-BY-4.0](https://creativecommons.org/licenses/by/4.0/)

The mathematical content is unconditionally open. Lemmas suitable for
mathlib can be upstreamed without friction (mathlib requires Apache-2.0).

Note on scope: the `telperion/examples/` directories contain *research
artifacts and emitted certificates* — these are part of the open
mathematical record and are Apache-2.0, not BSL. The BSL covers the
Telperion *engine* (`telperion/src/`, `telperion/cli`, the MCP server,
and tooling).

## The Telperion engine: Business Source License 1.1

`telperion/src/` and associated tooling are licensed under the
[Business Source License 1.1](telperion/LICENSE):

- **Free for research.** Academic research, teaching, scholarly
  publication, personal experimentation, and evaluation are permitted
  outright by the Additional Use Grant.
- **Commercial production use requires a commercial license** from the
  Licensor until the Change Date.
- **Every version becomes Apache-2.0 three years after its release.**
  The engine is source-available today and open source on a rolling
  schedule.
- **Emitted certificates are yours.** Lean files produced by running
  Telperion are explicitly excluded from the Licensed Work; no rights
  are claimed over your outputs.

## History

Versions of this repository published before 2026-08-21 were released
entirely under Apache-2.0; that grant is irrevocable for those
snapshots. The BSL applies to subsequent versions of the Telperion
engine.

## Contributing

To keep the dual-licensing model legally sound, the Licensor must retain
full copyright in the Telperion engine. Contributions to `telperion/src/`
require the [Contributor License Agreement](telperion/CLA.md).
Contributions to the mathematical content (everything Apache-2.0) require
only the standard Apache-2.0 inbound=outbound understanding — no CLA.

*This document describes intent and is not legal advice; consult counsel
before relying on it for commercial decisions.*
