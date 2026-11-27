# Erdős–Taylor theorem for the planar random walk (Erdős Problem 1166, variant)

A Palomar-ready Lean project for `Erdos1166.erdos_1166.variants.erdos_taylor` from
[formal-conjectures](https://github.com/google-deepmind/formal-conjectures) (commit `9097e2f`).

- `Challenge.lean`: the statement, with the formal-conjectures definitions it uses copied in. It imports
  only Mathlib, and its one `sorry` is deliberate.
- `Solution.lean`: proves the same declaration from the proof development in `ErdosTaylor/`.
- `ErdosTaylor/Defs.lean`: the same definitions, used by the proof development.
- `ErdosTaylor/Proof.lean` (and siblings): the proof, ported from the archived Left to Solve file(s) in
  `lefttosolve/complete/erdos-1166-erdos-taylor/` of the companion archive repository `left-to-solve-proofs` (Lean v4.33.1, merged in Left
  to Solve PR [#750](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/750), [#909](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/909), [#1067](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/1067), [#1157](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/1157)) to Lean v4.36.0 and
  the module system. Comments marked `Port` explain each change; the mathematics is unchanged.
- `comparator.json`, `formalization.yaml`: Palomar metadata.

Lean `v4.36.0`, Mathlib `fc4f59e577feb1a4956671bc04ac18aaaf8cd842` (the `v4.36.0` tag).

`ErdosTaylor/Reduction.lean` is the reduction (PR #750); `H2.lean` is PR #909; `H1H3.lean` is PR #1157, whose file begins with a verbatim copy of PR #1067 (the proof of H1).

## Check

```text
lake exe cache get
lake build
lake comparator --config comparator.json     # needs bwrap (Linux); see the template's scripts/verify-comparator.sh
```

Licence: Apache-2.0 (the repository's root `LICENSE`), with the attributions in its `NOTICE`.

Submit through the [Palomar submission form](https://submit.palomar-registry.org/): the
`left-to-solve-palomar` repository at a full commit SHA, project path `palomar/erdos-1166-erdos-taylor`, Comparator path
`palomar/erdos-1166-erdos-taylor/comparator.json`. Every `.lean` file of that repository uses the module system
(`scripts/check-lean-sources.py`).
