# Left to Solve proofs for Palomar

Seven [Palomar](https://palomar-registry.org/)-ready Lean 4 projects, one per result, for statements of
[formal-conjectures](https://github.com/google-deepmind/formal-conjectures) (commit `9097e2f`) whose
proofs Ming-Chih Kao (GitHub `koolkao`, Stanford University) first merged on
[Left to Solve](https://github.com/GuillaumeBAUD-coder/open-math-agents). The merged files themselves,
exactly as checked by Left to Solve (Lean v4.33.1), are archived in the companion repository
**left-to-solve-proofs** (`lefttosolve/complete/`); each entry here is a port of them to Lean v4.36.0,
Mathlib `fc4f59e577feb1a4956671bc04ac18aaaf8cd842` and the module system. The two repositories are
separate because Palomar checks every `.lean` file of a submitted repository for a `module` header,
which the archived v4.33.1 files do not have.

The MathOverflow 10799 proof (Left to Solve PR #1352, weak Kahn–Kalai) is withheld for now: it
contains about 75 lines from Genbox's Left to Solve PR #341, which has no licence, so it cannot be
relicensed here. PR #1352 credited that reuse.

## Entries

| Entry (`palomar/…`) | formal-conjectures declaration | Left to Solve PRs |
| --- | --- | --- |
| `erdos-1166-erdos-taylor` | `Erdos1166.erdos_1166.variants.erdos_taylor` | #750, #909, #1067, #1157 |
| `hadamard-first-cases` | `Hadamard.HadamardConjecture.variants.first_cases` | #3464 |
| `erdos-70-erdos-rado` | `Erdos70.erdos_70.variants.erdos_rado` | #4934 |
| `erdos-1129-chebyshev-upper-bound` | `Erdos1129.erdos_1129.variants.chebyshev_upper_bound` | #767 |
| `erdos-1129-free-nodes-not-unique` | `Erdos1129.erdos_1129.variants.free_nodes_not_unique` | #1047 |
| `erdos-1130-erdos-sqrt` | `Erdos1130.erdos_1130.variants.erdos_sqrt` | #981 |
| `erdos-1044-fixed-degree-of-le-two` | `Erdos1044.erdos_1044.variants.fixed_degree_of_le_two` | #3188 |

Each entry follows [PalomarTemplate](https://github.com/PalomarRegistry/PalomarTemplate): `Challenge.lean`
(the formal-conjectures statement with its definitions copied in, importing only Mathlib, one deliberate
`sorry`; its header lists every change), `Solution.lean` (proves the same declaration), the proof
development in a library folder, `comparator.json`, `formalization.yaml` (v0.4; fields marked `[DRAFT-OWNER]` or `[OWNER-DECIDE]`
need the maintainer's own words), `lean-toolchain`, `lakefile.toml` and `lake-manifest.json`.

## Checks (27 Nov 2026)

- `python3 scripts/check-lean-sources.py`: every `.lean` file in the repository starts with `module` and
  has at most 10,000 lines (largest: 1,550); every Challenge is under 300 lines.
- Each entry builds with `lake build`, and `lake comparator` accepted Solution against Challenge with the
  Lean kernel, NanoDa and con-ron, using only `propext`, `Classical.choice` and `Quot.sound`. The run was
  on macOS, without Comparator's `bwrap` sandbox (`--inadvisably-no-sandbox`); Palomar reruns it
  sandboxed. The Hadamard entry needs about 12 GB of memory and 20 minutes for the external kernels.

To check an entry: `scripts/verify-entry.sh <entry>` (Linux with `bwrap`), or with `--no-sandbox`.

## Submitting

Each entry is a separate Palomar submission through the
[Palomar submission form](https://submit.palomar-registry.org/): this repository at a full commit SHA,
project path `palomar/<entry>`, Comparator path `palomar/<entry>/comparator.json`. The licence is the
root `LICENSE`.

## Use of AI

Apart from the formal-conjectures statements and the material named in `NOTICE`, the Lean proofs, the
ports, the metadata and this documentation were written by Claude Code agents (Anthropic's Claude Opus
5.5) directed by Ming-Chih Kao, who chose the problems, reviewed the work and is responsible for it.
Other models were consulted for brainstorming (recorded in the relevant `formalization.yaml`) and for
read-only reviews of the licensing text and of two Challenge files (OpenAI Astra 6.2, Google Gemini 4
Neon).

## Licence

Apache License 2.0, copyright 2026 Ming-Chih Kao, except as stated in `NOTICE`.
