# tanh Y · tanh Z and tanh X are never stochastically ordered (MathOverflow 505921)

A Palomar-ready Lean project for an original result: for all g_X, g_Y, g_Z > 0, with X ~ N(g_X, g_X),
Y ~ N(g_Y, g_Y), Z ~ N(g_Z, g_Z) and Y, Z independent, neither tanh Y · tanh Z nor tanh X stochastically
dominates the other. This is a complete negative answer to
[MathOverflow 505921](https://mathoverflow.net/questions/505921). The result, its paper proof and the Lean
proof were first published in [koolkao/mo505921-tanh-dominance](https://github.com/koolkao/mo505921-tanh-dominance)
(commit `25c3c9124f47df41a312f283451699a36b73a2df`).

- `Challenge.lean`: the four compared statements in Mathlib vocabulary (`gaussianReal`, `HasLaw`, `IndepFun`,
  `iIndepFun`, `cdf`), with the question quoted. It imports only Mathlib and defines nothing; each `sorry` is
  deliberate.
- `Solution.lean`: proves the same declarations from the proof development in `TanhDominance/`.
- `TanhDominance/Proof.lean`, `TanhDominance/Check.lean`: `MO505921.lean` and `Check.lean` of the source
  repository, put into the module system (header, public section, namespace `MO505921` renamed
  `TanhDominance`); the proofs are unchanged.
- `TanhDominance/Ioo.lean`: new for this entry; restricts the comparison of c.d.f.s to t ∈ (−1, 1), the
  question's range (`mo505921_Ioo`, `no_gX_Ioo`).
- `comparator.json`, `formalization.yaml`: Palomar metadata.

Lean `v4.36.0`, Mathlib `fc4f59e577feb1a4956671bc04ac18aaaf8cd842` (the `v4.36.0` tag).

## Check

```text
lake exe cache get
lake build
lake comparator --config comparator.json     # needs bwrap (Linux); see the template's scripts/verify-comparator.sh
```

Licence: Apache-2.0 (the repository's root `LICENSE`), with the attributions in its `NOTICE`. The question
quoted in `Challenge.lean` is by tituf on MathOverflow (CC BY-SA 4.0).

Submit through the [Palomar submission form](https://submit.palomar-registry.org/): the
`left-to-solve-palomar` repository at a full commit SHA, project path `palomar/mo505921-tanh-dominance`,
Comparator path `palomar/mo505921-tanh-dominance/comparator.json`.
