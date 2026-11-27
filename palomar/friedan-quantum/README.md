# Friedan's entropy inequality for non-commuting Hamiltonians (MathOverflow 138395, quantum question)

A Palomar-ready Lean project for original results. Friedan's inequality (1 − a) S(H₀) + a S(H₁) ≥ K² S(H_a)
holds for all Hermitian H₀, H₁, commuting or not, which answers the quantum question at the end of
[MathOverflow 138395](https://mathoverflow.net/q/138395). The same holds for m Hamiltonians, and
a S(ρ) + (1 − a) S(σ) ≥ K² S(M/K) holds for several weighted geometric means M of density matrices. The results,
their paper proofs and the Lean proofs were first published in
[koolkao/friedan-entropy-inequality](https://github.com/koolkao/friedan-entropy-inequality) (commit
`0f4ba65dc126f59e7158fbcbc01548baa78cf21d`, v1.3.0; `QUANTUM.md`, `quantum-lean/`). The classical inequality is the
separate entry `palomar/friedan-classical`.

- `Challenge.lean`: six compared statements in namespace `FriedanQuantum`, stated with Mathlib vocabulary only
  (`cfc`, `Matrix.trace`, `PosDef`, `PosSemidef`, `Real.exp`, `Real.log`, real powers), with the question quoted.
  It imports only Mathlib and defines nothing; each `sorry` is deliberate.
- `Solution.lean`: proves the same declarations; its proofs are the source repository's statement checks
  (`FriedanQ/Check.lean`, `FriedanQM/Check.lean`) under new names.
- `FriedanQ/`, `FriedanMulti/`, `FriedanQM/`: the source repository's `quantum-lean/` libraries put into the module
  system; the proofs are unchanged. `FriedanQ/Classical.lean` and `FriedanMulti/` contain the classical results the
  reduction ends in.
- `FriedanQ/Vendor/KyFan.lean`: a modified copy of atlas-lean's Ky Fan file (Apache-2.0, Meta Platforms), with its
  upstream header, a list of changes and the verbatim upstream licence `FriedanQ/Vendor/LICENSE-atlas-lean`. **That
  licence begins with the notice "Codebase is not intended for use to train, fine-tune, distill, evaluate, or
  otherwise develop ML models".** `FriedanQ/Vendor/LICENSE-physlib` is physlib's licence.
- `comparator.json`, `formalization.yaml`: Palomar metadata.

Lean `v4.36.0`, Mathlib `fc4f59e577feb1a4956671bc04ac18aaaf8cd842` (the `v4.36.0` tag) and, for the proof only,
[physlib](https://github.com/leanprover-community/physlib) at `edc607c2e6cbcc2f9c40c750e5c10a8490d32470`
(Apache-2.0), pinned in `lakefile.toml` and `lake-manifest.json`.

## Check

```text
lake exe cache get
lake build                                   # also builds the physlib modules the proof imports
lake comparator --config comparator.json     # needs bwrap (Linux); see the template's scripts/verify-comparator.sh
```

Licence: Apache-2.0 (the repository's root `LICENSE`), with the attributions in its `NOTICE`; the vendored file
keeps its own licence. The question quoted in `Challenge.lean` is by Daniel Friedan on MathOverflow (CC BY-SA 3.0).

Submit through the [Palomar submission form](https://submit.palomar-registry.org/): the `left-to-solve-palomar`
repository at a full commit SHA, project path `palomar/friedan-quantum`, Comparator path
`palomar/friedan-quantum/comparator.json`.
