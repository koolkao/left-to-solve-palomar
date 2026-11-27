# Weak Kahn–Kalai theorem (MathOverflow 10799, variant)

A Palomar-ready Lean project for `Mathoverflow10799.mathoverflow_10799.variants.weak_kahn_kalai` from
[formal-conjectures](https://github.com/google-deepmind/formal-conjectures) (commit `9097e2f`).

- `Challenge.lean`: the statement, with the formal-conjectures definitions it uses copied in. It imports
  only Mathlib, and its one `sorry` is deliberate.
- `Solution.lean`: proves the same declaration from the proof development in `WeakKahnKalai/`.
- `WeakKahnKalai/Defs.lean`: the same definitions, used by the proof development.
- `WeakKahnKalai/Proof.lean` (and siblings): the proof, ported from the archived Left to Solve file(s) in
  `lefttosolve/complete/mo-10799-weak-kahn-kalai/` of the companion archive repository `left-to-solve-proofs` (Lean v4.33.1, merged in Left
  to Solve PR [#1352](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/1352)) to Lean v4.36.0 and
  the module system. Comments marked `Port` explain each change; the mathematics is unchanged.
- `comparator.json`, `formalization.yaml`: Palomar metadata.

Lean `v4.36.0`, Mathlib `fc4f59e577feb1a4956671bc04ac18aaaf8cd842` (the `v4.36.0` tag).

**Not ready to publish:** about 75 lines of `WeakKahnKalai/Proof.lean` (the definitions `mu`, `M`, `I` and the lemmas `sd1` … `I_insert`) come from Left to Solve PR #341 by Genbox, which has no licence. Get Genbox's permission, or replace those lines, before this entry is made public.

## Check

```text
lake exe cache get
lake build
lake comparator --config comparator.json     # needs bwrap (Linux); see the template's scripts/verify-comparator.sh
```

Licence: Apache-2.0 (the repository's root `LICENSE`), with the attributions in its `NOTICE`.

Submit through the [Palomar submission form](https://submit.palomar-registry.org/): the
`left-to-solve-palomar` repository at a full commit SHA, project path `palomar/mo-10799-weak-kahn-kalai`, Comparator path
`palomar/mo-10799-weak-kahn-kalai/comparator.json`. Every `.lean` file of that repository uses the module system
(`scripts/check-lean-sources.py`).
