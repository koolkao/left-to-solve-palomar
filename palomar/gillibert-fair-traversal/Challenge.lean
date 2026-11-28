/-
Copyright 2026 Ming-Chih Kao. Licensed under the Apache License, Version 2.0;
see the LICENSE file at the root of this repository.
-/
module

public import Mathlib

/-!
# Fair Traversal and Geodesic Deletion: partial results on two conjectures of Gillibert

**Fair Traversal Conjecture** (Luc Gillibert and GPT 6 Astra, note dated 17 November 2026,
<https://github.com/Gillibert/ConjecturesGillibert/blob/main/fair_traversal_conjecture.tex>; Left to Solve
statement `statements/gillibert-fair-traversal.lean` by Gillibert, PR #339). Every connected
vertex-transitive graph with at least two vertices has a nonempty finite multiset of Hamiltonian paths in
which every edge occurs equally often (`FairFamily` below is that conclusion for one graph).

**Geodesic Deletion Conjecture** (Gillibert; Left to Solve statement `statements/gillibert-geodesic-deletion.lean`,
PR #334). In every connected vertex-transitive graph with at least three vertices, deleting the vertices of
any geodesic path leaves a connected graph (`GeodesicDeletion` below is that conclusion for one graph).

Both conjectures are open; they are **not** claimed here. The theorems below prove them for classes of graphs,
following the source repository (Ming-Chih Kao, 2026,
<https://github.com/koolkao/gillibert-fair-traversal-abelian>, v1.7.0, concept DOI 10.5281/zenodo.24605477),
whose `Check.lean` restates its results independently; the statements here follow that file.

* Fair Traversal: every connected Cayley graph of a finite abelian group (Theorem 1); Cartesian products of
  fair vertex-transitive graphs (Theorem 3); Cayley graphs of dihedral, dicyclic, generalized dihedral and
  generalized dicyclic groups (Theorem 7) and of the index-2 extensions `Γ(A, k, z)` of a finite abelian group
  by a power map under condition (O) (Theorem 8); every generalized Petersen graph `GP(m, k)` with
  `k² ≡ 1 (mod m)`, or `k² ≡ -1 (mod m)` with `m` even, or `GP(10, 2)` (Theorem 9). By Frucht, Graver and
  Watkins (1971), the only vertex-transitive generalized Petersen graphs left out are those with
  `k² ≡ -1 (mod m)` and `m` odd.
* Geodesic Deletion: Cartesian products `G₁ □ G₂` with `G₂` satisfying it (Theorem 2); every connected
  Cayley graph of a finite abelian group with at least three vertices (Theorem 5); every connected Cayley
  graph of an abelian group with at least six generators, finite or not (Theorem 6).

Vocabulary: `IsVertexTransitive`, the conclusion `FairFamily` and the conclusion `GeodesicDeletion` are
the definitions of the Left to Solve statements (#339, #334), restated. A labelling of `G` by a group `Γ` is a
bijection `e : V ≃ Γ` and a set `S` with `u ~ v ↔ (e u)⁻¹ * e v ∈ S` (written additively, `e v - e u ∈ S`,
for abelian groups); `Γ(A, k, z)` is written on `A × Bool` with its multiplication `pwMul` and inverse `pwInv`
spelled out. The vertex-transitivity hypothesis of #339/#334 is kept in the labelled forms, although a group
labelling already implies it.
-/

@[expose] public section

namespace FairTraversal

open SimpleGraph

/-- Vertex-transitivity, as in the Left to Solve statements #339 and #334: every vertex is mapped to
every other vertex by a graph automorphism. -/
def IsVertexTransitive {V : Type*} (G : SimpleGraph V) : Prop :=
  ∀ u v : V, ∃ φ : G ≃g G, φ u = v

/-- The conclusion of the Fair Traversal Conjecture (Left to Solve #339) for a fixed graph `G`: there
are positive integers `r, k` and Hamiltonian paths `P_1, …, P_r` (not necessarily distinct) such that
every edge lies on exactly `k` of them. -/
def FairFamily {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) : Prop :=
  ∃ (r k : ℕ), 0 < r ∧ 0 < k ∧
    ∃ (a b : Fin r → V) (P : ∀ i, G.Walk (a i) (b i)),
      (∀ i, (P i).IsHamiltonian) ∧
      ∀ e ∈ G.edgeSet, (Finset.univ.filter fun i => e ∈ (P i).edges).card = k

/-- The conclusion of the Geodesic Deletion Conjecture (Left to Solve #334) for a fixed graph `G`:
deleting the vertices of any geodesic path leaves a connected induced subgraph. -/
def GeodesicDeletion {V : Type*} (G : SimpleGraph V) : Prop :=
  ∀ (u v : V) (p : G.Walk u v), p.IsPath → p.length = G.dist u v →
    (G.induce {x | x ∉ p.support}).Connected

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

namespace FairTraversal

open SimpleGraph

/-- **Theorem 1 (Fair Traversal for abelian Cayley graphs), in the form of #339.** Every connected graph
on at least two vertices with an abelian labelling (every connected Cayley graph of a finite abelian
group) satisfies the conclusion of the Fair Traversal Conjecture. #339's vertex-transitivity hypothesis
is kept, although an abelian labelling already implies it. -/
theorem fair_traversal_of_abelian_labelling :
    ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V),
      G.Connected → IsVertexTransitive G → 2 ≤ Fintype.card V →
      HasAbelianLabelling G → FairFamily G := by
  sorry

/-- **Theorem 1 in the paper's form**: for a finite abelian group `A` with `|A| ≥ 2` and `S ⊆ A` with
`0 ∉ S`, `S = -S` and `⟨S⟩ = A`, the Cayley graph `Cay(A, S)` has a fair family of Hamiltonian paths. -/
theorem fair_traversal_cay (A : Type) [AddCommGroup A] [Fintype A] [DecidableEq A] (S : Finset A)
    (h0 : (0 : A) ∉ S) (hneg : ∀ s ∈ S, -s ∈ S)
    (hgen : AddSubgroup.closure (S : Set A) = ⊤) (hn : 2 ≤ Fintype.card A) :
    FairFamily (cay A S h0 hneg) := by
  sorry

/-- **Theorem 3 (Cartesian products)**: if `G` and `H` are finite vertex-transitive graphs with at least
two vertices that satisfy the conclusion of #339, then so does `G □ H`. -/
theorem fair_traversal_boxProd :
    ∀ {V W : Type} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
      (G : SimpleGraph V) (H : SimpleGraph W),
      IsVertexTransitive G → IsVertexTransitive H → 2 ≤ Fintype.card V → 2 ≤ Fintype.card W →
      FairFamily G → FairFamily H → FairFamily (G □ H) := by
  sorry

/-- **Theorem 7 for the dihedral groups** (Mathlib's `DihedralGroup n`, order `2n`), in the form of #339:
a labelling `u ~ v ↔ (e u)⁻¹ * e v ∈ S` by `DihedralGroup n` (any `S`) is added. -/
theorem fair_traversal_dihedralGroup (n : ℕ) [NeZero n] :
    ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V),
      G.Connected → IsVertexTransitive G → 2 ≤ Fintype.card V →
      (∃ (e : V ≃ DihedralGroup n) (S : Finset (DihedralGroup n)),
        ∀ u v, G.Adj u v ↔ (e u)⁻¹ * e v ∈ S) → FairFamily G := by
  sorry

/-- **Theorem 7 for the dicyclic groups** (Mathlib's `QuaternionGroup n`, order `4n`), in the form of #339. -/
theorem fair_traversal_quaternionGroup (n : ℕ) [NeZero n] :
    ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V),
      G.Connected → IsVertexTransitive G → 2 ≤ Fintype.card V →
      (∃ (e : V ≃ QuaternionGroup n) (S : Finset (QuaternionGroup n)),
        ∀ u v, G.Adj u v ↔ (e u)⁻¹ * e v ∈ S) → FairFamily G := by
  sorry

/-- **Theorem 8 (index-2 extensions by a power map)**, in the form of #339: a labelling `e : V ≃ A × Bool`
by the group `Γ(A, k, z)` (multiplication `pwMul k z`, inverse `pwInv k z`; `A` a finite abelian group,
`k • k • a = a`, `k • z = z`, and condition (O): `k` acts as a fixed sign `ε = ±1` on the elements of odd
order), `u ~ v ↔ (e u)⁻¹ (e v) ∈ S`, is added. -/
theorem fair_traversal_power_extension :
    ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V),
      G.Connected → IsVertexTransitive G → 2 ≤ Fintype.card V →
      (∃ (A : Type) (_ : AddCommGroup A) (_ : Fintype A) (_ : DecidableEq A) (k : ℤ) (z : A),
        (∀ a : A, k • k • a = a) ∧ k • z = z ∧
        (∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ ∀ a : A, Odd (addOrderOf a) → k • a = ε • a) ∧
        ∃ (e : V ≃ A × Bool) (S : Finset (A × Bool)),
          ∀ u v, G.Adj u v ↔ pwMul k z (pwInv k z (e u)) (e v) ∈ S) → FairFamily G := by
  sorry

/-- **Theorem 7 for the generalized dihedral and generalized dicyclic groups** (the case `k = -1` of
Theorem 8): `Γ(A, -1, z)` with `z + z = 0` is `Dic(A, z) = ⟨A, τ⟩`, `τ² = z`, `τ a τ⁻¹ = -a`; for `z = 0`
it is the generalized dihedral group `Dih(A)`. -/
theorem fair_traversal_dicyclic :
    ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V),
      G.Connected → IsVertexTransitive G → 2 ≤ Fintype.card V →
      (∃ (A : Type) (_ : AddCommGroup A) (_ : Fintype A) (_ : DecidableEq A) (z : A), z + z = 0 ∧
        ∃ (e : V ≃ A × Bool) (S : Finset (A × Bool)),
          ∀ u v, G.Adj u v ↔ pwMul (-1) z (pwInv (-1) z (e u)) (e v) ∈ S) → FairFamily G := by
  sorry

/-- **Theorem 9 (generalized Petersen graphs)**: `GP(m, k)` with `m ≥ 3` has a fair family of Hamiltonian
paths whenever `k² ≡ 1 (mod m)`, or `k² ≡ -1 (mod m)` with `m` even, or `m = 10` and `k ≡ ±2 (mod 10)`.
These are all the vertex-transitive generalized Petersen graphs except `k² ≡ -1 (mod m)` with `m` odd. -/
theorem fair_traversal_gpGraph (m : ℕ) [NeZero m] (k : ℤ) (hm : 3 ≤ m)
    (H : (m : ℤ) ∣ k * k - 1 ∨ (Even m ∧ (m : ℤ) ∣ k * k + 1) ∨
      (m = 10 ∧ (((k : ℤ) : ZMod m) = 2 ∨ ((k : ℤ) : ZMod m) = -2))) :
    FairFamily (gpGraph m k) := by
  sorry

/-- **Theorem 2 (Geodesic Deletion and Cartesian products)**: if `G₁` and `G₂` are connected and `G₂`
satisfies the conclusion of #334, then so does `G₁ □ G₂`. -/
theorem geodesicDeletion_boxProd {α β : Type*} (G₁ : SimpleGraph α) (G₂ : SimpleGraph β)
    (h₁ : G₁.Connected) (h₂ : G₂.Connected) (hgd : GeodesicDeletion G₂) :
    GeodesicDeletion (G₁ □ G₂) := by
  sorry

/-- **Theorem 5 (Geodesic Deletion for abelian Cayley graphs), in the form of #334**: all of #334's
hypotheses kept, an abelian labelling added. -/
theorem geodesicDeletion_of_abelian_labelling :
    ∀ {V : Type} [Fintype V] (G : SimpleGraph V),
      G.Connected → IsVertexTransitive G → 3 ≤ Fintype.card V →
      HasAbelianLabelling G → GeodesicDeletion G := by
  sorry

/-- **Theorem 5 in the paper's form**: every connected `Cay(A, S)` of a finite abelian group with
`|A| ≥ 3` satisfies the conclusion of #334. -/
theorem geodesicDeletion_cay (A : Type) [AddCommGroup A] [Fintype A] [DecidableEq A] (S : Finset A)
    (h0 : (0 : A) ∉ S) (hneg : ∀ s ∈ S, -s ∈ S) (hc : (cay A S h0 hneg).Connected)
    (hn : 3 ≤ Fintype.card A) :
    GeodesicDeletion (cay A S h0 hneg) := by
  sorry

/-- **Theorem 6 (degree at least 6)**: every connected `Cay(A, S)` of an abelian group (finite or not)
with `|S| ≥ 6` satisfies the conclusion of #334. -/
theorem geodesicDeletion_cay_of_six_le (A : Type) [AddCommGroup A] [DecidableEq A] (S : Finset A)
    (h0 : (0 : A) ∉ S) (hneg : ∀ s ∈ S, -s ∈ S) (hc : (cay A S h0 hneg).Connected)
    (h6 : 6 ≤ S.card) :
    GeodesicDeletion (cay A S h0 hneg) := by
  sorry

end FairTraversal
