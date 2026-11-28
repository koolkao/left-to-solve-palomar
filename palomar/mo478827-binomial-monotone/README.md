# P((1+g)X + lY > k) is strictly decreasing in p when 2l ≤ 1+g (MathOverflow 478827)

A Palomar-ready Lean project for an original result: for independent X ~ Bin(k, 1−p), Y ~ Bin(k, p), k ≥ 1, 0 < g < 1, 0 < l ≤ (1+g)/2, f_k(p) = P((1+g)X + lY > k) is strictly decreasing on [0, 1], which answers [MathOverflow 478827](https://mathoverflow.net/questions/478827); and the unrestricted claim fails (k = 10, g = 1/7, l = 99/100). The result, its paper proof and the Lean proof were
first published in [koolkao/mo478827-binomial-monotone](https://github.com/koolkao/mo478827-binomial-monotone) (commit `3d17061d300988d21b3b1f23cf4bf91b6129dc62`, v1.0.0).

- `Challenge.lean`: the compared statements (`MO478827.theorem1`, `MO478827.answer`, `MO478827.prop2_not_antitone`, `MO478827.fact1_fails`, `MO478827.prob_of_indep`, `MO478827.theorem1_measure`, `MO478827.answer_measure`) in Mathlib vocabulary with
  every notion written out, and the question quoted. It imports only Mathlib and defines nothing; each `sorry` is
  deliberate.
- `Solution.lean`: proves the same declarations from the proof development in `BinomialMonotone/`.
- `BinomialMonotone/Proof.lean`, `BinomialMonotone/Check.lean`: `MO478827.lean` and `Check.lean` of the source repository, put into the module system (header, public section, namespaces renamed); the proofs are unchanged.
- `comparator.json`, `formalization.yaml`: Palomar metadata.

Lean `v4.36.0`, Mathlib `fc4f59e577feb1a4956671bc04ac18aaaf8cd842` (the `v4.36.0` tag).

## Check

```text
lake exe cache get
lake build
lake comparator --config comparator.json     # needs bwrap (Linux); see the template's scripts/verify-comparator.sh
```

Licence: Apache-2.0 (the repository's root `LICENSE`), with the attributions in its `NOTICE`. The question
quoted in `Challenge.lean` is by EGT on MathOverflow (CC BY-SA 4.0).

Submit through the [Palomar submission form](https://submit.palomar-registry.org/): the
`left-to-solve-palomar` repository at a full commit SHA, project path `palomar/mo478827-binomial-monotone`,
Comparator path `palomar/mo478827-binomial-monotone/comparator.json`.
