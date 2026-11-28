# Lean 4 proofs for Palomar: Left to Solve proofs and other results by Ming-Chih Kao

[Palomar](https://palomar-registry.org/)-ready Lean 4 projects (Lean v4.36.0, Mathlib
`fc4f59e577feb1a4956671bc04ac18aaaf8cd842`, module system), one per result, by Ming-Chih Kao (GitHub
`koolkao`, Stanford University). There are two groups.

- **Left to Solve proofs** (eight entries): proofs of statements of
  [formal-conjectures](https://github.com/google-deepmind/formal-conjectures) (commit `9097e2f`) first merged on
  [Left to Solve](https://github.com/GuillaumeBAUD-coder/open-math-agents). The merged files themselves, exactly
  as checked by Left to Solve (Lean v4.33.1), are archived in the companion repository
  **left-to-solve-proofs** (`lefttosolve/complete/`); each entry here is a port of them to Lean v4.36.0 and the
  module system. The two repositories are separate because Palomar checks every `.lean` file of a submitted
  repository for a `module` header, which the archived v4.33.1 files do not have.
- **Entries ported from the owner's own repositories** (six entries added 27 Nov 2026, four on 28 Nov 2026): answers to
  MathOverflow questions and to recent conjectures, and one formalization of a recent published proof. Each
  entry ports the Lean development of a public `koolkao/*` repository, named at a full commit in its README and
  `formalization.yaml`, to the module system. Those repositories are recorded as sources and related
  formalizations, not as `repository.substantive_formalization`: each entry contains the whole proof, and
  Palomar would apply its module-header check to a declared substantive repository, which those repositories
  (not in the module system) would fail.

The MathOverflow 10799 proof (Left to Solve PR #1352, weak Kahn–Kalai) is withheld for now: it
contains about 75 lines from Genbox's Left to Solve PR #341, which has no licence, so it cannot be
relicensed here. PR #1352 credited that reuse.

## Entries

### Left to Solve proofs

| Entry (`palomar/…`) | formal-conjectures declaration | Left to Solve PRs |
| --- | --- | --- |
| `erdos-1166-erdos-taylor` | `Erdos1166.erdos_1166.variants.erdos_taylor` | #750, #909, #1067, #1157 |
| `hadamard-first-cases` | `Hadamard.HadamardConjecture.variants.first_cases` | #3464 |
| `erdos-70-erdos-rado` | `Erdos70.erdos_70.variants.erdos_rado` | #4934 |
| `erdos-1129-chebyshev-upper-bound` | `Erdos1129.erdos_1129.variants.chebyshev_upper_bound` | #767 |
| `erdos-1129-free-nodes-not-unique` | `Erdos1129.erdos_1129.variants.free_nodes_not_unique` | #1047 |
| `erdos-1130-erdos-sqrt` | `Erdos1130.erdos_1130.variants.erdos_sqrt` | #981 |
| `erdos-1044-fixed-degree-of-le-two` | `Erdos1044.erdos_1044.variants.fixed_degree_of_le_two` | #3188 |
| `erdos-521-real-roots` | `Erdos521.erdos_521` (+ `Erdos521.erdos_521_with_multiplicity`, added) | #12504 (ported from v4.33.1; split into 7 modules) |

### Entries ported from `koolkao/*` repositories

| Entry (`palomar/…`) | Result | Compared declarations | Source repository (commit) | Origin |
| --- | --- | --- | --- | --- |
| `mo505921-tanh-dominance` | tanh Y · tanh Z and tanh X are never stochastically ordered (MathOverflow 505921) | `MO505921.mo505921_Ioo`, `.mo505921`, `.mo505921_iIndep`, `.no_gX_Ioo` | `mo505921-tanh-dominance` (`25c3c91`) | original |
| `friedan-classical` | Friedan's generalized entropy inequality for all n and α, m distributions (Theorem M), and the positive part of R2 (MathOverflow 138395) | `Friedan138395.friedan_two`, `.friedan_multi`, `.friedan_renyi_two_point` | `friedan-entropy-inequality` (`0f4ba65`) | original |
| `friedan-quantum` | Friedan's quantum question (MathOverflow 138395), plus the α-z, Kubo–Ando and m-state forms | `FriedanQuantum.friedan_question`, `.alphaZ_psd`, `.kuboAndo`, `.hamiltonians_multi`, `.logEuclidean_multi`, `.product_multi` | `friedan-entropy-inequality` (`0f4ba65`, `quantum-lean/`) | original |
| `feige-general-delta` | Feige's inequality for every δ > 0 and the lower bound of Samuels' conjecture, following Ling (arXiv:2608.18392) | `FeigeSamuels.feige_general_delta`, `.samuels_lower` | `feige-lean` (`7da24ab`) | source-based (`formalizes` Ling) |
| `gillibert-equal-halves` | Gillibert's Equal Halves conjecture is false (a vertex-transitive graph on 28 vertices) | `GillibertEqualHalves.not_equal_halves`, `.exists_counterexample_28` | `gillibert-equal-halves-counterexample` (`72a8411`) | original |
| `kimberling-copula` | Kimberling's inequality for Archimedean copulas (MathOverflow 195959) | `MO195959.kimberling_inequality` | `kimberling-copula-inequality` (`18d5fd4`) | original |
| `mo451543-jensen-slack` | Only quadratics compare the two Jensen slacks; x⁴ refutes the asker's conjecture (MathOverflow 451543) | `MO451543.pow_four_in_class`, `.not_comparison_pow_four`, `.comparison_iff_of_convex`, `.comparison_iff_of_continuous`, `.indepComparison_iff_of_convex`, `.indepComparison_iff_of_continuous` | `mo451543-jensen-slack` (`8be6d34`) | original |
| `mo478827-binomial-monotone` | P((1+g)X + lY > k) is strictly decreasing in p when 2l ≤ 1+g, but not for all g, l ∈ (0,1) (MathOverflow 478827) | `MO478827.theorem1`, `.answer`, `.prop2_not_antitone`, `.fact1_fails`, `.prob_of_indep`, `.theorem1_measure`, `.answer_measure` | `mo478827-binomial-monotone` (`3d17061`) | original |
| `mo184460-hellinger-tv` | Hellinger ≤ total variation for truncated Gaussians, and the log-concave cosh/sinh inequality behind it (MathOverflow 184460) | `MO184460.answer`, `.answer_strict`, `.chain_interval`, `.thm3`, `.thm3_strict` | `mo184460-hellinger-tv` (`b2b49dc`) | original |
| `mo503314-two-primes` | The odd-d conjecture of MathOverflow 503314: the product identity forces ⟨r₁⟩ = ⟨r₂⟩ in (ℤ/m)^× | `MO503314.mo503314` | `mo503314-two-primes` (`566defa`, ported from Lean v4.33.1) | original |

In these entries `Challenge.lean` states the result itself (importing only Mathlib, with any definitions it
needs written out and documented), not a formal-conjectures statement.

Each entry follows [PalomarTemplate](https://github.com/PalomarRegistry/PalomarTemplate): `Challenge.lean`
(importing only Mathlib, with deliberate `sorry`s; for the Left to Solve entries, the formal-conjectures
statement with its definitions copied in, and its header lists every change), `Solution.lean` (proves the
same declarations), the proof
development in a library folder, `comparator.json`, `formalization.yaml` (v0.4), `lean-toolchain`, `lakefile.toml` and `lake-manifest.json`.

## Checks (27 Nov 2026)

- `python3 scripts/check-lean-sources.py`: every `.lean` file in the repository starts with `module` and
  has at most 10,000 lines (largest: 2,054); every Challenge is under 300 lines (largest: 147).
- Each entry builds with `lake build`, and `lake comparator` accepted Solution against Challenge with the
  Lean kernel, NanoDa and con-ron, using only `propext`, `Classical.choice` and `Quot.sound`. The run was
  on macOS, without Comparator's `bwrap` sandbox (`--inadvisably-no-sandbox`); Palomar reruns it
  sandboxed. The Hadamard entry needs about 12 GB of memory and 20 minutes for the external kernels.
- The six entries added on 27 Nov 2026 were checked the same way the same day. Comparator wall time and peak
  memory: `mo505921-tanh-dominance` 2–5 min, 6.0 GB; `friedan-classical` 4 min, 6.0 GB; `friedan-quantum`
  8 min, 6.1 GB; `feige-general-delta` 3–4 min, 5.9 GB; `gillibert-equal-halves` 4–5 min, 8.4 GB;
  `kimberling-copula` 4–5 min, 6.1 GB. `friedan-quantum` also needs its pinned
  [physlib](https://github.com/leanprover-community/physlib) dependency (proof only; its Challenge imports only
  Mathlib).
- Each new Challenge was reviewed for faithfulness to the published statement by two separate model reviews
  (OpenAI Astra 6.2, Google Gemini 4 Neon); their findings were fixed (see each `formalization.yaml`).

- `erdos-521-real-roots` (added 28 Nov 2026) was checked the same way: comparator about 4 min; its Challenge is the
  formal-conjectures statement copied line by line, plus one added variant.

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
read-only reviews of the licensing text and of Challenge files (OpenAI Astra 6.2, Google Gemini 4 Neon). For
the six entries added on 27 Nov 2026 the owner gave goal-level direction only and no mathematical hints, and
there has been no independent human mathematical review. The owner reviewed and approved the metadata of every
entry (the account of authorship, AI use and review status) on 27 Nov 2026; that was not a mathematical review.

## Licence

Apache License 2.0, copyright 2026 Ming-Chih Kao, except as stated in `NOTICE`.
