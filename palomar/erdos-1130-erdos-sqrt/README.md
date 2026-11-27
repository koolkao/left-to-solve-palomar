# Erdős's bound Υ(x) < √n (Erdős Problem 1130, variant)

A Palomar-ready Lean project for `Erdos1130.erdos_1130.variants.erdos_sqrt` from
[formal-conjectures](https://github.com/google-deepmind/formal-conjectures) (commit `9097e2f`).

- `Challenge.lean`: the statement, with the formal-conjectures definitions it uses copied in. It imports
  only Mathlib, and its one `sorry` is deliberate.
- `Solution.lean`: proves the same declaration from the proof development in `ErdosSqrt/`.
- `ErdosSqrt/Defs.lean`: the same definitions, used by the proof development.
- `ErdosSqrt/Proof.lean` (and siblings): the proof, ported from the archived Left to Solve file(s) in
  `lefttosolve/complete/erdos-1130-erdos-sqrt/` of the companion archive repository `left-to-solve-proofs` (Lean v4.33.1, merged in Left
  to Solve PR [#981](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/981)) to Lean v4.36.0 and
  the module system. Comments marked `Port` explain each change; the mathematics is unchanged.
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
`left-to-solve-palomar` repository at a full commit SHA, project path `palomar/erdos-1130-erdos-sqrt`, Comparator path
`palomar/erdos-1130-erdos-sqrt/comparator.json`. Every `.lean` file of that repository uses the module system
(`scripts/check-lean-sources.py`).
