# Fair Traversal and Geodesic Deletion: partial results on two conjectures of Gillibert

A Palomar-ready Lean project for original partial results on two open conjectures of Luc Gillibert about
finite connected vertex-transitive graphs. **Fair Traversal** (with GPT 6 Astra; Left to Solve statement #339):
the graph has a nonempty finite multiset of Hamiltonian paths covering every edge equally often. **Geodesic
Deletion** (Left to Solve statement #334): deleting the vertices of any geodesic leaves a connected graph. Both
conjectures remain open and are not claimed here.

Proved (statements in `Challenge.lean`): Fair Traversal for every connected Cayley graph of a finite abelian group
(Theorem 1), for Cartesian products (Theorem 3), for Cayley graphs of dihedral, dicyclic, generalized dihedral and
generalized dicyclic groups (Theorem 7) and of the index-2 power-map extensions Γ(A, k, z) under condition (O)
(Theorem 8), and for every generalized Petersen graph GP(m, k) with k² ≡ 1 (mod m), or k² ≡ −1 (mod m) with m even,
or GP(10, 2) (Theorem 9; GP(10, 2) by kernel `decide`); Geodesic Deletion for Cartesian products (Theorem 2), for
every connected Cayley graph of a finite abelian group (Theorem 5) and for abelian Cayley graphs of degree at least
six (Theorem 6). Not covered in Lean (paper only, in the source repository): Propositions 9.4 and 9.5 (the open case
k² ≡ −1 (mod m) with m odd) and other paper-only results.

The results, their paper proofs (`NOTE.md`) and the Lean proofs were first published in
[koolkao/gillibert-fair-traversal-abelian](https://github.com/koolkao/gillibert-fair-traversal-abelian)
(v1.7.0, commit `06c3a8732759afca38331762b76113135e475ac6`; concept DOI 10.5281/zenodo.24605477), which credits the
known ingredients (Weber 1988, Witte 1982, Frucht–Graver–Watkins 1971, and others) and concurrent work on Left to
Solve (PR #14143 by amcolex: Geodesic Deletion for finite abelian Cayley graphs by a different method, concurrent
with and independent of Theorem 5; PR #13005 by MattGaiser: a product rule, the same as Theorem 2, which was public
earlier).

- `Challenge.lean`: the twelve compared statements, with the definitions they use written out (vertex-transitivity
  and the two conclusions as in the Left to Solve statements, abelian labellings, `Cay(A, S)`, `GP(m, k)`, the
  group law of Γ(A, k, z) on `A × Bool`). It imports only Mathlib; its `sorry`s are deliberate. The statements follow
  the source repository's independent check file `Check.lean`.
- `Solution.lean`: proves them from the proof development.
- `FairTraversal/Defs.lean`: the same definitions, used by `Solution.lean`.
- `FairTraversal/FTAbelian.lean`, `GDProduct.lean`, `FTProduct.lean`, `GDAbelian.lean`, `FTDihedral.lean`,
  `FTPower.lean`, `FTGP.lean`, `FTGPNeg.lean`, `FTGP102.lean`: the nine proof modules of the source repository
  (Lean v4.33.1), ported to Lean v4.36.0 and the module system (see each header).
- `FairTraversal/Main.lean`: `gpGraph_eq` (from `Check.lean`) and the identification of `A × Bool` with the group
  `FTDih.Pw A k z`.
- `comparator.json`, `formalization.yaml`: Palomar metadata.

Lean `v4.36.0`, Mathlib `fc4f59e577feb1a4956671bc04ac18aaaf8cd842` (the `v4.36.0` tag).

## Check

```text
lake exe cache get
lake build
lake comparator --config comparator.json     # needs bwrap (Linux); see the template's scripts/verify-comparator.sh
```

Licence: Apache-2.0 (the repository's root `LICENSE`), with the attributions in its `NOTICE`. The conjectures and
their Left to Solve statements are Gillibert's; the definitions restating them are reproduced for reference (see
`NOTICE`).

Submit through the [Palomar submission form](https://submit.palomar-registry.org/): the
`left-to-solve-palomar` repository at a full commit SHA, project path `palomar/gillibert-fair-traversal`,
Comparator path `palomar/gillibert-fair-traversal/comparator.json`.
