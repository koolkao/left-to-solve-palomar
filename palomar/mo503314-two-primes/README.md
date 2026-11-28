# The odd-d conjecture of MathOverflow 503314 (products over powers of a root of unity)

A Palomar-ready Lean project for an original result: for coprime m, d with d odd and integers r₁, r₂ of order
exactly d modulo m with gcd(rᵢ − 1, m) = 1, the product identity of
[MathOverflow 503314](https://mathoverflow.net/questions/503314) for all k forces ⟨r₁⟩ = ⟨r₂⟩ in (ℤ/m)^×. The
result, its paper proof and the Lean proof were first published in
[koolkao/mo503314-two-primes](https://github.com/koolkao/mo503314-two-primes) (commit
`566defa273f1d35900318d07e35f92f6c8fad04a`, v1.0.0). Known before: d an odd prime (Ikeda 1980) and (ℤ/m)^× cyclic
(Colantonio–Lauret, arXiv:2602.12939).

- `Challenge.lean`: the compared statement `MO503314.mo503314` in Mathlib vocabulary (`cexp`, `Real.pi`, `orderOf`
  in `ZMod m`, `Int.gcd`), with the question paraphrased. It imports only Mathlib and defines nothing; the `sorry`
  is deliberate.
- `Solution.lean`: proves it from `TwoPrimes/Proof.lean`.
- `TwoPrimes/Proof.lean`: `lean/MO503314Full.lean` of the source repository (Lean v4.33.1), ported to Lean v4.36.0
  and the module system; the header lists the three small proof repairs the newer Mathlib needed.
- `comparator.json`, `formalization.yaml`: Palomar metadata.

Lean `v4.36.0`, Mathlib `fc4f59e577feb1a4956671bc04ac18aaaf8cd842` (the `v4.36.0` tag).

## Check

```text
lake exe cache get
lake build
lake comparator --config comparator.json     # needs bwrap (Linux); see the template's scripts/verify-comparator.sh
```

Licence: Apache-2.0 (the repository's root `LICENSE`), with the attributions in its `NOTICE`. The question
paraphrased in `Challenge.lean` is by emiliocba on MathOverflow (CC BY-SA 4.0).

Submit through the [Palomar submission form](https://submit.palomar-registry.org/): the
`left-to-solve-palomar` repository at a full commit SHA, project path `palomar/mo503314-two-primes`,
Comparator path `palomar/mo503314-two-primes/comparator.json`.
