/-
Copyright 2026 Ming-Chih Kao. Licensed under the Apache License, Version 2.0;
see the LICENSE file at the root of this repository.
-/
module

public import Mathlib

/-!
# Gillibert's Equal Halves conjecture is false

**Conjecture** (Luc Gillibert and GPT 6 Astra, note dated 17 November 2026,
<https://github.com/Gillibert/ConjecturesGillibert/blob/main/equal_halves_conjecture.tex>).
Every finite connected vertex-transitive graph `G` of even order admits a partition
`V(G) = A ⊔ B` into two nonempty sets such that the induced subgraphs `G[A]` and `G[B]` are
connected and isomorphic.

The note proves this when `G` has a fixed-point-free involutive automorphism (so for all connected
Cayley graphs of even order) and leaves the general case open. A formal statement by Gillibert is in
Left to Solve PR #337 (`OMA.S_gillibert_equal_halves.main`,
<https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/337>, merged 27 November 2026 as
commit `07d0431`, file unchanged from the PR head `e99f9f1`). `not_equal_halves` below negates
exactly that proposition, written out here with the definition
`IsVertexTransitive G := ∀ u v, ∃ φ : G ≃g G, φ u = v` of that file unfolded. The partition is
`A` and its complement `Aᶜ`; `G[A]` is `G.induce A`; `G ≃g G` is a graph automorphism.

The counterexample (Ming-Chih Kao, 2026,
<https://github.com/koolkao/gillibert-equal-halves-counterexample>) is graph 2659 of the
Holt–Royle census of vertex-transitive graphs on 28 vertices (9-regular, automorphism group of
order 504, not a Cayley graph).

* `not_equal_halves`: the conjecture, as stated, is false.
* `exists_counterexample_28`: more precisely, there is a connected vertex-transitive graph on
  28 vertices for which no set `A` of vertices has `G[A] ≅ G[Aᶜ]` at all (with or without the
  connectivity and nonemptiness conditions).
-/

@[expose] public section

namespace GillibertEqualHalves

open SimpleGraph

/-- **Gillibert's Equal Halves conjecture is false.** It is not the case that every finite
connected vertex-transitive graph of even order has a vertex set `A` with `A` and `Aᶜ` nonempty,
`G[A]` and `G[Aᶜ]` connected, and `G[A] ≅ G[Aᶜ]`. -/
theorem not_equal_halves : ¬ ∀ {V : Type} [Fintype V] (G : SimpleGraph V),
      G.Connected → (∀ u v : V, ∃ φ : G ≃g G, φ u = v) → Even (Fintype.card V) →
      ∃ A : Set V, A.Nonempty ∧ Aᶜ.Nonempty ∧
        (G.induce A).Connected ∧ (G.induce Aᶜ).Connected ∧
        Nonempty (G.induce A ≃g G.induce Aᶜ) := by
  sorry

/-- There is a connected vertex-transitive graph on 28 vertices such that for no vertex set `A`
are the induced subgraphs on `A` and on its complement isomorphic. -/
theorem exists_counterexample_28 : ∃ G : SimpleGraph (Fin 28),
    G.Connected ∧ (∀ u v : Fin 28, ∃ φ : G ≃g G, φ u = v) ∧
      ¬ ∃ A : Set (Fin 28), Nonempty (G.induce A ≃g G.induce Aᶜ) := by
  sorry

end GillibertEqualHalves
