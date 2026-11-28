# Erdős Problem 521 is false: almost surely R_n / log n does not tend to 2/π

A Palomar-ready Lean project for `Erdos521.erdos_521` from
[formal-conjectures](https://github.com/google-deepmind/formal-conjectures) (commit `9097e2f`): for the random
Littlewood polynomial f_n = ε₀ + ε₁ z + ⋯ + ε_n zⁿ with independent uniform signs, it is **not** true that almost
surely R_n / log n → 2/π, where R_n is the number of distinct real roots. A variant counting the real roots with
multiplicity (`Erdos521.erdos_521_with_multiplicity`, the reading of the Left to Solve statement the proof was
written for) is proved as well.

That the almost-sure limit fails was known before this proof: formal-conjectures marks the problem solved and links
an independent Lean disproof by Star Fleet Math
([williamjblair/lean-proofs](https://github.com/williamjblair/lean-proofs/tree/4f915a323443bfb1709a6805a013812016dca88a/starfleet/erdos-521),
same overall strategy: a cone event for the top coefficients, then Descartes' rule of signs). Only its top-level
reduction was read; no code, lemma statements or proofs were taken from it. The ~8.5k-line proof here was written
from scratch and first merged on Left to Solve
([PR #12504](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/12504), 28 Nov 2026).

- `Challenge.lean`: the formal-conjectures statement, with the definitions it uses copied in, plus the
  with-multiplicity variant. It imports only Mathlib; its `sorry`s are deliberate.
- `Solution.lean`: proves both declarations from `E521/Main.lean`.
- `E521/Defs.lean`: the same definitions, used by the proof development.
- `E521/Part1.lean` … `E521/Part7.lean`: the merged Left to Solve file `proofs/erdos-521.lean` (Lean v4.33.1),
  split into seven modules at its section boundaries and ported to Lean v4.36.0 and the module system (the port
  notes are in `E521/Part1.lean`). The final theorem is generalized to any root count bounded by the count with
  multiplicity (`E521.erdos521_false_le`).
- `E521/Main.lean`: identifies `littlewoodPolynomial` and `rademacherMeasure` with the proof's objects and
  bounds the distinct-root count by the count with multiplicity.
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
`left-to-solve-palomar` repository at a full commit SHA, project path `palomar/erdos-521-real-roots`, Comparator path
`palomar/erdos-521-real-roots/comparator.json`.
