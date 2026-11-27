# Friedan's generalized entropy inequality (MathOverflow 138395), Theorem M and Theorem R2

A Palomar-ready Lean project for original results: for probability vectors X, Y on n points and 0 ≤ α ≤ 1,
with zᵢ = Xᵢ^α Yᵢ^{1−α}, K = Σ zᵢ > 0 and Z = z/K, the Shannon entropies satisfy
α H(X) + (1 − α) H(Y) ≥ K² H(Z), the inequality asked about by Daniel Friedan on
[MathOverflow 138395](https://mathoverflow.net/q/138395); its extension to m distributions (Theorem M); and the
two-point Rényi version for 0 < γ ≤ 2 log 2 (Theorem R2). The results, their paper proofs and the Lean proofs
were first published in
[koolkao/friedan-entropy-inequality](https://github.com/koolkao/friedan-entropy-inequality) (commit
`0f4ba65dc126f59e7158fbcbc01548baa78cf21d`, v1.3.0). The quantum (non-commuting) version is the separate entry
`palomar/friedan-quantum`.

- `Challenge.lean`: the three compared statements (`Friedan138395.friedan_two`, `friedan_multi`,
  `friedan_renyi_two_point`) with entropies written out in Mathlib vocabulary (`Real.negMulLog`, `Real.rpow`).
  It imports only Mathlib and defines nothing; each `sorry` is deliberate.
- `Solution.lean`: proves the same declarations from `OMA.S_mo_138395.main`, `FriedanMulti.theoremM` and
  `FriedanR2.theoremR2`.
- `FriedanEntropy/`, `FriedanMulti/`: the source repository's root Lean project (Lean v4.33.1) put into the module
  system. `Statement.lean` and `Proof.lean` (two distributions), `Statement`/`Calc`/`Induction`/`Main` (Theorem M)
  and `R2*.lean` (Theorem R2) are copied unchanged apart from the header; `Induction.lean` and `Main.lean` are
  taken from the repository's own Lean v4.36 port (`quantum-lean/FriedanMulti/`). Each file says where it comes
  from.
- `comparator.json`, `formalization.yaml`: Palomar metadata.

Lean `v4.36.0`, Mathlib `fc4f59e577feb1a4956671bc04ac18aaaf8cd842` (the `v4.36.0` tag).

## Check

```text
lake exe cache get
lake build
lake comparator --config comparator.json     # needs bwrap (Linux); see the template's scripts/verify-comparator.sh
```

Licence: Apache-2.0 (the repository's root `LICENSE`), with the attributions in its `NOTICE`. The question quoted
in `Challenge.lean` is by Daniel Friedan on MathOverflow (CC BY-SA 3.0).

Submit through the [Palomar submission form](https://submit.palomar-registry.org/): the `left-to-solve-palomar`
repository at a full commit SHA, project path `palomar/friedan-classical`, Comparator path
`palomar/friedan-classical/comparator.json`.
