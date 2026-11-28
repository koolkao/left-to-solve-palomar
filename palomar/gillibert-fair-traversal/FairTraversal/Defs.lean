/-
Copyright 2026 Ming-Chih Kao. Licensed under the Apache License, Version 2.0;
see the LICENSE file at the root of this repository.
-/
module

public import Mathlib

/-!
# Definitions used by the statements

A verbatim copy of the definitions in `Challenge.lean`, so that the proof development and `Solution.lean`
use the same declarations. Comparator checks that they agree with the Challenge.
-/

@[expose] public section

namespace FairTraversal

open SimpleGraph

/-- Vertex-transitivity (the standard definition): for all vertices `u, v` some graph automorphism
maps `u` to `v`. -/
def IsVertexTransitive {V : Type*} (G : SimpleGraph V) : Prop :=
  ∀ u v : V, ∃ φ : G ≃g G, φ u = v

/-- A fair family of walks: `r` walks `P i`, the `i`-th from `(ends i).1` to `(ends i).2`, each of them
Hamiltonian, such that each edge of `G` is an edge of exactly `k` of them. -/
def IsFairFamily {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) {r : ℕ}
    (ends : Fin r → V × V) (P : ∀ i, G.Walk (ends i).1 (ends i).2) (k : ℕ) : Prop :=
  (∀ i, (P i).IsHamiltonian) ∧
    ∀ e ∈ G.edgeSet, (Finset.univ.filter fun i => e ∈ (P i).edges).card = k

/-- Fair Traversal holds for `G`: some nonempty finite family of Hamiltonian paths (repetitions allowed)
covers every edge the same positive number of times. -/
def HasFairTraversal {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) : Prop :=
  ∃ (r : ℕ) (ends : Fin r → V × V) (P : ∀ i, G.Walk (ends i).1 (ends i).2) (k : ℕ),
    0 < r ∧ 0 < k ∧ IsFairFamily G ends P k

/-- A geodesic path: a path whose length is the distance between its ends. -/
def IsGeodesicPath {V : Type*} {G : SimpleGraph V} {u v : V} (p : G.Walk u v) : Prop :=
  p.IsPath ∧ p.length = G.dist u v

/-- Geodesic Deletion holds for `G`: for every geodesic path `p`, the subgraph induced on the vertices
not on `p` is connected. -/
def HasGeodesicDeletion {V : Type*} (G : SimpleGraph V) : Prop :=
  ∀ (u v : V) (p : G.Walk u v), IsGeodesicPath p → (G.induce {x | x ∈ p.support}ᶜ).Connected

/-- An abelian labelling: the vertices can be labelled by a finite abelian group `A` so that
`u ~ v` iff the label difference lies in a fixed set `S` (that is, `G` is a Cayley graph of `A`). -/
def HasAbelianLabelling {V : Type} (G : SimpleGraph V) : Prop :=
  ∃ (A : Type) (_ : AddCommGroup A) (_ : Fintype A) (_ : DecidableEq A) (e : V ≃ A)
    (S : Finset A), ∀ u v, G.Adj u v ↔ e v - e u ∈ S

/-- The Cayley graph `Cay(A, S)` of an abelian group: `a ~ b` iff `b - a ∈ S`. -/
def cay (A : Type) [AddCommGroup A] (S : Finset A) (h0 : (0 : A) ∉ S)
    (hneg : ∀ s ∈ S, -s ∈ S) : SimpleGraph A where
  Adj a b := b - a ∈ S
  symm := ⟨fun a b h => by simpa [neg_sub] using hneg _ h⟩
  loopless := ⟨fun a h => h0 (by simpa using h)⟩

/-- The multiplication of the group `Γ(A, k, z) = A ∪ Aτ` (`τ a τ⁻¹ = k • a`, `τ² = z`), written on
`A × Bool` (`(a, false)` is `a`, `(a, true)` is `a τ`):
`(a, i) (b, j) = (a + kⁱ b + (z if i ∧ j), i xor j)`. -/
def pwMul {A : Type} [AddCommGroup A] (k : ℤ) (z : A) (x y : A × Bool) : A × Bool :=
  (x.1 + (if x.2 then k • y.1 else y.1) + (if x.2 && y.2 then z else 0), xor x.2 y.2)

/-- The inverse in `Γ(A, k, z)`: `(a, false)⁻¹ = (-a, false)`, `(a, true)⁻¹ = (-(k • a) - z, true)`. -/
def pwInv {A : Type} [AddCommGroup A] (k : ℤ) (z : A) (x : A × Bool) : A × Bool :=
  if x.2 then (-(k • x.1) - z, true) else (-x.1, false)

/-- The generalized Petersen graph `GP(m, k)` on `ZMod m × Bool` (`(x, false)` the outer vertex `O_x`,
`(x, true)` the inner vertex `I_x`): outer rim `O_x O_{x+1}`, inner rim `I_x I_{x+k}`, spokes `O_x I_x`. -/
def gpGraph (m : ℕ) (k : ℤ) : SimpleGraph (ZMod m × Bool) where
  Adj u v := u ≠ v ∧
    ((u.2 = false ∧ v.2 = false ∧ (v.1 = u.1 + 1 ∨ u.1 = v.1 + 1)) ∨
      (u.2 = true ∧ v.2 = true ∧ (v.1 = u.1 + k ∨ u.1 = v.1 + k)) ∨
      (u.1 = v.1 ∧ u.2 ≠ v.2))
  symm := ⟨fun u v ⟨h, h'⟩ => ⟨h.symm, by
    rcases h' with ⟨a, b, c | c⟩ | ⟨a, b, c | c⟩ | ⟨a, b⟩
    · exact Or.inl ⟨b, a, Or.inr c⟩
    · exact Or.inl ⟨b, a, Or.inl c⟩
    · exact Or.inr (Or.inl ⟨b, a, Or.inr c⟩)
    · exact Or.inr (Or.inl ⟨b, a, Or.inl c⟩)
    · exact Or.inr (Or.inr ⟨a.symm, Ne.symm b⟩)⟩⟩
  loopless := ⟨fun u h => h.1 rfl⟩

end FairTraversal
