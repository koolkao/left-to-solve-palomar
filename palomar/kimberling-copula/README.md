# Kimberling's inequality for Archimedean copulas (MathOverflow 195959)

A Palomar-ready Lean project for an original result: if f is continuous on [0, ∞), f(0) = 1, f(x) → 0 as
x → ∞ and f is completely monotone on (0, ∞), then the Archimedean copula C(u, v) = f(g(u) + g(v)) (g the
inverse of f) satisfies C(a, a) − a² ≥ C(u, v) − uv with a = (u + v)/2, for all u, v ∈ [0, 1]. This answers
Clark Kimberling's question [MathOverflow 195959](https://mathoverflow.net/questions/195959) (2015). The proof
and its Lean formalization were first published in
[koolkao/kimberling-copula-inequality](https://github.com/koolkao/kimberling-copula-inequality) (commit
`18d5fd4ab3dedd0645b425f96ddac6d21d18a599`).

- `Challenge.lean`: the statement, with its two definitions (`CompletelyMonotoneOn`, `archC`). It is the
  owner's Left to Solve statement `mo-195959` (PR #1260) with the namespace renamed; it imports only Mathlib,
  and its one `sorry` is deliberate.
- `Solution.lean`: proves the same declaration from `Kimberling.main_proof`.
- `KimberlingCopula/Defs.lean`: the same two definitions, used by the proof development.
- `KimberlingCopula/TauCeti.lean`: Bernstein's theorem on [0, ∞) and its dependency closure, vendored from
  [TauCeti](https://github.com/TauCetiProject/TauCeti) (commit `ac8801f6`, Apache-2.0, copyright The Tau Ceti
  contributors; changes listed in the file).
- `KimberlingCopula/Proof.lean`: the proof. Lines 40–318 of the source repository's `Kimberling/Basic.lean`
  unchanged, then the shift-and-limit argument of the owner's Left to Solve version, which needs only Bernstein's
  theorem on [0, ∞) instead of the full Hausdorff–Bernstein–Widder theorem used by the source repository.
- `comparator.json`, `formalization.yaml`: Palomar metadata.

Lean `v4.36.0`, Mathlib `fc4f59e577feb1a4956671bc04ac18aaaf8cd842` (the `v4.36.0` tag). No TauCeti dependency.

## Check

```text
lake exe cache get
lake build
lake comparator --config comparator.json     # needs bwrap (Linux); see the template's scripts/verify-comparator.sh
```

Licence: Apache-2.0 (the repository's root `LICENSE`), with the attributions in its `NOTICE`.
`KimberlingCopula/TauCeti.lean` is Copyright (c) 2026 The Tau Ceti contributors (Apache-2.0).

Submit through the [Palomar submission form](https://submit.palomar-registry.org/): the
`left-to-solve-palomar` repository at a full commit SHA, project path `palomar/kimberling-copula`,
Comparator path `palomar/kimberling-copula/comparator.json`.
