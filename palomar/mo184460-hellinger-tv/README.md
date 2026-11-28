# Hellinger distance ≤ total variation for truncated Gaussians (MathOverflow 184460)

A Palomar-ready Lean project for an original result: for N(−μ, 1) and N(μ, 1) truncated to [a, b] (or any interval of positive length), d_H² ≤ d_H ≤ d_TV, strictly d_H < d_TV for μ ≠ 0, which answers [MathOverflow 184460](https://mathoverflow.net/questions/184460); and the log-concave cosh/sinh inequality behind it (Theorem 3). The result, its paper proof and the Lean proof were
first published in [koolkao/mo184460-hellinger-tv](https://github.com/koolkao/mo184460-hellinger-tv) (commit `b2b49dcf336bcab5835d78cab9686f7ba9ee4b79`, v1.0.0).

- `Challenge.lean`: the compared statements (`MO184460.answer`, `MO184460.answer_strict`, `MO184460.chain_interval`, `MO184460.thm3`, `MO184460.thm3_strict`) in Mathlib vocabulary with
  every notion written out, and the question quoted. It imports only Mathlib and defines nothing; each `sorry` is
  deliberate.
- `Solution.lean`: proves the same declarations from the proof development in `HellingerTV/`.
- `HellingerTV/Proof.lean`, `HellingerTV/Check.lean`: `MO184460.lean` and `Check.lean` of the source repository, put into the module system (header, public section, namespaces renamed); the proofs are unchanged.
- `comparator.json`, `formalization.yaml`: Palomar metadata.

Lean `v4.36.0`, Mathlib `fc4f59e577feb1a4956671bc04ac18aaaf8cd842` (the `v4.36.0` tag).

## Check

```text
lake exe cache get
lake build
lake comparator --config comparator.json     # needs bwrap (Linux); see the template's scripts/verify-comparator.sh
```

Licence: Apache-2.0 (the repository's root `LICENSE`), with the attributions in its `NOTICE`. The question
quoted in `Challenge.lean` is by Alexander on MathOverflow (CC BY-SA 3.0).

Submit through the [Palomar submission form](https://submit.palomar-registry.org/): the
`left-to-solve-palomar` repository at a full commit SHA, project path `palomar/mo184460-hellinger-tv`,
Comparator path `palomar/mo184460-hellinger-tv/comparator.json`.
