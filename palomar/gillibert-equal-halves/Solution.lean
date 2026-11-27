/-
Copyright 2026 Ming-Chih Kao. Licensed under the Apache License, Version 2.0;
see the LICENSE file at the root of this repository.
-/
module

public import EqualHalves

/-!
# Solution

Proves the two declarations stated in `Challenge.lean` from the certificate in
`EqualHalves/Proof.lean` (`EH.disproof`, `EH.exists_counterexample_28`).
-/

@[expose] public section

namespace GillibertEqualHalves

open SimpleGraph

theorem not_equal_halves : ¬ ∀ {V : Type} [Fintype V] (G : SimpleGraph V),
      G.Connected → (∀ u v : V, ∃ φ : G ≃g G, φ u = v) → Even (Fintype.card V) →
      ∃ A : Set V, A.Nonempty ∧ Aᶜ.Nonempty ∧
        (G.induce A).Connected ∧ (G.induce Aᶜ).Connected ∧
        Nonempty (G.induce A ≃g G.induce Aᶜ) :=
  EH.disproof

theorem exists_counterexample_28 : ∃ G : SimpleGraph (Fin 28),
    G.Connected ∧ (∀ u v : Fin 28, ∃ φ : G ≃g G, φ u = v) ∧
      ¬ ∃ A : Set (Fin 28), Nonempty (G.induce A ≃g G.induce Aᶜ) :=
  EH.exists_counterexample_28

end GillibertEqualHalves
