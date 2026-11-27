# Gillibert's Equal Halves conjecture is false

A Palomar-ready Lean project for an original result: graph 2659 of the Holt–Royle census of vertex-transitive
graphs on 28 vertices (9-regular, automorphism group of order 504, not a Cayley graph) is connected and
vertex-transitive, and for no vertex set A are the induced subgraphs G[A] and G[Aᶜ] isomorphic. So the Equal
Halves conjecture of L. Gillibert (note dated 17 November 2026,
[source](https://github.com/Gillibert/ConjecturesGillibert/blob/main/equal_halves_conjecture.tex); formal
statement in Left to Solve PR [#337](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/337)) is false.
The counterexamples and the Lean certificate were first published in
[koolkao/gillibert-equal-halves-counterexample](https://github.com/koolkao/gillibert-equal-halves-counterexample)
(commit `72a841163f6258ef0a3e4ca608bc85eaf8892543`).

- `Challenge.lean`: the two compared statements in Mathlib vocabulary (`SimpleGraph`, `Connected`, `induce`,
  `≃g`), with vertex-transitivity written out. It imports only Mathlib and defines nothing; each `sorry` is
  deliberate. PR #337's file is not copied (it has no licence); `not_equal_halves` is the negation of the same
  proposition.
- `Solution.lean`: proves the same declarations from `EqualHalves/Proof.lean`.
- `EqualHalves/Proof.lean`: `lean/GillibertDisproof.lean` of the source repository, ported to Lean v4.36.0 and the
  module system (comments marked `Port`); the kernel computation (46 `decide +kernel` chunks of 2^18 colourings)
  is unchanged. The adjacency lists are the census graph (Holt–Royle data, CC BY 4.0).
- `comparator.json`, `formalization.yaml`: Palomar metadata.

Lean `v4.36.0`, Mathlib `fc4f59e577feb1a4956671bc04ac18aaaf8cd842` (the `v4.36.0` tag). `lake build` took about
1 minute and 5 GB on our machine; `lake comparator` (three kernels) about 4–5 minutes and up to 8.4 GB.

## Check

```text
lake exe cache get
lake build
lake comparator --config comparator.json     # needs bwrap (Linux); see the template's scripts/verify-comparator.sh
```

Licence: Apache-2.0 (the repository's root `LICENSE`), with the attributions in its `NOTICE`.

Submit through the [Palomar submission form](https://submit.palomar-registry.org/): the
`left-to-solve-palomar` repository at a full commit SHA, project path `palomar/gillibert-equal-halves`,
Comparator path `palomar/gillibert-equal-halves/comparator.json`.
