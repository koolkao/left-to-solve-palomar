# Only quadratics compare the two Jensen slacks (MathOverflow 451543)

A Palomar-ready Lean project for an original result: for finitely supported couplings (X, Y) with E[Y | X] = X, a convex or continuous f satisfies E[f(X) − f(E[X | Y])] ≤ E[f(Y) − f(X)] for every coupling iff f is a convex quadratic (Theorem 1), also for independent additive noise (Theorem 2); x⁴ refutes the asker's conjecture. Answers [MathOverflow 451543](https://mathoverflow.net/questions/451543). The result, its paper proof and the Lean proof were
first published in [koolkao/mo451543-jensen-slack](https://github.com/koolkao/mo451543-jensen-slack) (commit `8be6d3435985e8b331e45e9e666a0c61c8cbf172`, v1.1.0).

- `Challenge.lean`: the compared statements (`MO451543.pow_four_in_class`, `MO451543.not_comparison_pow_four`, `MO451543.comparison_iff_of_convex`, `MO451543.comparison_iff_of_continuous`, `MO451543.indepComparison_iff_of_convex`, `MO451543.indepComparison_iff_of_continuous`) in Mathlib vocabulary with
  every notion written out, and the question quoted. It imports only Mathlib and defines nothing; each `sorry` is
  deliberate.
- `Solution.lean`: proves the same declarations from the proof development in `JensenSlack/`.
- `JensenSlack/Proof.lean`: `MO451543.lean` of the source repository, put into the module system (header, public section, namespaces renamed); the proofs are unchanged.
- `comparator.json`, `formalization.yaml`: Palomar metadata.

Lean `v4.36.0`, Mathlib `fc4f59e577feb1a4956671bc04ac18aaaf8cd842` (the `v4.36.0` tag).

## Check

```text
lake exe cache get
lake build
lake comparator --config comparator.json     # needs bwrap (Linux); see the template's scripts/verify-comparator.sh
```

Licence: Apache-2.0 (the repository's root `LICENSE`), with the attributions in its `NOTICE`. The question
quoted in `Challenge.lean` is by Guy Blanc on MathOverflow (CC BY-SA 4.0).

Submit through the [Palomar submission form](https://submit.palomar-registry.org/): the
`left-to-solve-palomar` repository at a full commit SHA, project path `palomar/mo451543-jensen-slack`,
Comparator path `palomar/mo451543-jensen-slack/comparator.json`.
