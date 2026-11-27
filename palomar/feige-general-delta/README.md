# Feige's inequality for every δ > 0, and the lower bound in Samuels' conjecture

A Palomar-ready Lean project for two theorems proved by following Zhi Ling, *On Samuels' Conjecture*
([arXiv:2608.18392](https://arxiv.org/abs/2608.18392)):

- `FeigeSamuels.feige_general_delta`: for independent, nonnegative, integrable X₁, …, Xₙ with E[Xᵢ] ≤ μ
  (μ > 0) and every δ > 0, P(∑ Xᵢ − E[∑ Xᵢ] < δμ) ≥ min(δ/(1+δ), e⁻¹) (Feige's conjecture, SIAM J. Comput.
  35 (2006); Feige proved it with 1/13 in place of e⁻¹).
- `FeigeSamuels.samuels_lower`: for 0 ≤ m₁ ≤ … ≤ mₙ, λ > ∑ mᵢ and independent nonnegative Xᵢ with E[Xᵢ] = mᵢ,
  P(∑ Xᵢ < λ) ≥ minᵢ ∏_{j ≥ i} (1 − mⱼ/(λ − ∑_{k<i} mₖ)) (the lower-bound half of Ling's Theorem 1.1). The
  sharpness and attainment half is not formalized.

The Lean development was first published in [koolkao/feige-lean](https://github.com/koolkao/feige-lean)
(v1.1.0, commit `7da24abf1619706bf4f705bb24aa4d00bc63b49f`, Zenodo doi:10.5281/zenodo.24573988).

- `Challenge.lean`: the two statements in Mathlib vocabulary, with the bound qᵢ written out. It imports only
  Mathlib and defines nothing; each `sorry` is deliberate.
- `Solution.lean`: proves the same declarations from the proof development in `Feige/`.
- `Feige/`: the source repository's `Feige/` tree, put into the module system (`module` headers, public
  imports, public sections; one explicit-argument fix in `Feige/Calculus/Prop51.lean`, marked `Port`). The
  proofs are otherwise unchanged. `Feige/MainUniv.lean` is new: `main` with Ω in any universe.
- `Feige/Vendor/LeanPool/`: thirteen files vendored from [LeanPool/lean-pool](https://github.com/LeanPool/lean-pool)
  (`LeanPool/Feige/`, commit `9decab6341e6b0fd82bd7f9763a5dd7a9ce8778d`; Zhengqing Zhou and contributors,
  Apache-2.0, see the `LICENSE` in that folder and each file's header): the two-point mixture decomposition.
- `comparator.json`, `formalization.yaml`: Palomar metadata.

Lean `v4.36.0`, Mathlib `fc4f59e577feb1a4956671bc04ac18aaaf8cd842` (the `v4.36.0` tag).

## Check

```text
lake exe cache get
lake build
lake comparator --config comparator.json     # needs bwrap (Linux); see the template's scripts/verify-comparator.sh
```

Licence: Apache-2.0 (the repository's root `LICENSE`), with the attributions in its `NOTICE`.

Submit through the [Palomar submission form](https://submit.palomar-registry.org/): the
`left-to-solve-palomar` repository at a full commit SHA, project path `palomar/feige-general-delta`,
Comparator path `palomar/feige-general-delta/comparator.json`.
