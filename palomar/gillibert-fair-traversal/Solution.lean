/-
Copyright 2026 Ming-Chih Kao. Licensed under the Apache License, Version 2.0;
see the LICENSE file at the root of this repository.
-/
module

public import FairTraversal

/-!
# Solution

Proves the declarations stated in `Challenge.lean` from the ported proof development (`FairTraversal/*.lean`),
following `Check.lean` of the source repository.
-/

@[expose] public section

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
  exact fun G hc _ hn hlab => FTAbelian.main_abelian_cayley G hc hlab hn

/-- **Theorem 1 in the paper's form**: for a finite abelian group `A` with `|A| ≥ 2` and `S ⊆ A` with
`0 ∉ S`, `S = -S` and `⟨S⟩ = A`, the Cayley graph `Cay(A, S)` has a fair family of Hamiltonian paths. -/
theorem fair_traversal_cay (A : Type) [AddCommGroup A] [Fintype A] [DecidableEq A] (S : Finset A)
    (h0 : (0 : A) ∉ S) (hneg : ∀ s ∈ S, -s ∈ S)
    (hgen : AddSubgroup.closure (S : Set A) = ⊤) (hn : 2 ≤ Fintype.card A) :
    FairFamily (cay A S h0 hneg) := by
  exact FTAbelian.fair_traversal_cayley S (cay A S h0 hneg) (fun _ _ => Iff.rfl) hgen hn

/-- **Theorem 3 (Cartesian products)**: if `G` and `H` are finite vertex-transitive graphs with at least
two vertices that satisfy the conclusion of #339, then so does `G □ H`. -/
theorem fair_traversal_boxProd :
    ∀ {V W : Type} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
      (G : SimpleGraph V) (H : SimpleGraph W),
      IsVertexTransitive G → IsVertexTransitive H → 2 ≤ Fintype.card V → 2 ≤ Fintype.card W →
      FairFamily G → FairFamily H → FairFamily (G □ H) := by
  exact fun G H hGv hHv hV hW hG hH => FTProduct.ft_boxProd G H hGv hHv hV hW hG hH

/-- **Theorem 7 for the dihedral groups** (Mathlib's `DihedralGroup n`, order `2n`), in the form of #339:
a labelling `u ~ v ↔ (e u)⁻¹ * e v ∈ S` by `DihedralGroup n` (any `S`) is added. -/
theorem fair_traversal_dihedralGroup (n : ℕ) [NeZero n] :
    ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V),
      G.Connected → IsVertexTransitive G → 2 ≤ Fintype.card V →
      (∃ (e : V ≃ DihedralGroup n) (S : Finset (DihedralGroup n)),
        ∀ u v, G.Adj u v ↔ (e u)⁻¹ * e v ∈ S) → FairFamily G := by
  exact fun G hc _ hn hlab => FTDih.main_dihedralGroup_cayley n G hc hlab hn

/-- **Theorem 7 for the dicyclic groups** (Mathlib's `QuaternionGroup n`, order `4n`), in the form of #339. -/
theorem fair_traversal_quaternionGroup (n : ℕ) [NeZero n] :
    ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V),
      G.Connected → IsVertexTransitive G → 2 ≤ Fintype.card V →
      (∃ (e : V ≃ QuaternionGroup n) (S : Finset (QuaternionGroup n)),
        ∀ u v, G.Adj u v ↔ (e u)⁻¹ * e v ∈ S) → FairFamily G := by
  exact fun G hc _ hn hlab => FTDih.main_quaternionGroup_cayley n G hc hlab hn

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
  intro V _ _ G hc _ hn hlab
  obtain ⟨A, i1, i2, i3, k, z, hk, hz, hO, e, S, hG⟩ := hlab
  exact FTDih.main_pow_cayley G hc ⟨A, i1, i2, i3, k, z, hk, hz, hO, e.trans (pwEquiv A k z),
    S.map (pwEquiv A k z).toEmbedding, fun u v => by rw [hG, pw_mem]⟩ hn

/-- **Theorem 7 for the generalized dihedral and generalized dicyclic groups** (the case `k = -1` of
Theorem 8): `Γ(A, -1, z)` with `z + z = 0` is `Dic(A, z) = ⟨A, τ⟩`, `τ² = z`, `τ a τ⁻¹ = -a`; for `z = 0`
it is the generalized dihedral group `Dih(A)`. -/
theorem fair_traversal_dicyclic :
    ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V),
      G.Connected → IsVertexTransitive G → 2 ≤ Fintype.card V →
      (∃ (A : Type) (_ : AddCommGroup A) (_ : Fintype A) (_ : DecidableEq A) (z : A), z + z = 0 ∧
        ∃ (e : V ≃ A × Bool) (S : Finset (A × Bool)),
          ∀ u v, G.Adj u v ↔ pwMul (-1) z (pwInv (-1) z (e u)) (e v) ∈ S) → FairFamily G := by
  intro V _ _ G hc hvt hn hlab
  obtain ⟨A, i1, i2, i3, z, hz, e, S, hG⟩ := hlab
  exact fair_traversal_power_extension G hc hvt hn ⟨A, i1, i2, i3, -1, z, fun a => by simp [neg_one_zsmul],
    by rw [neg_one_zsmul]; exact neg_eq_of_add_eq_zero_left hz, ⟨-1, Or.inr rfl, fun _ _ => rfl⟩, e, S, hG⟩

/-- **Theorem 9 (generalized Petersen graphs)**: `GP(m, k)` with `m ≥ 3` has a fair family of Hamiltonian
paths whenever `k² ≡ 1 (mod m)`, or `k² ≡ -1 (mod m)` with `m` even, or `m = 10` and `k ≡ ±2 (mod 10)`.
These are all the vertex-transitive generalized Petersen graphs except `k² ≡ -1 (mod m)` with `m` odd. -/
theorem fair_traversal_gpGraph (m : ℕ) [NeZero m] (k : ℤ) (hm : 3 ≤ m)
    (H : (m : ℤ) ∣ k * k - 1 ∨ (Even m ∧ (m : ℤ) ∣ k * k + 1) ∨
      (m = 10 ∧ (((k : ℤ) : ZMod m) = 2 ∨ ((k : ℤ) : ZMod m) = -2))) :
    FairFamily (gpGraph m k) := by
  rw [gpGraph_eq]; exact FTGP102.ft_gp_all m k hm H

/-- **Theorem 2 (Geodesic Deletion and Cartesian products)**: if `G₁` and `G₂` are connected and `G₂`
satisfies the conclusion of #334, then so does `G₁ □ G₂`. -/
theorem geodesicDeletion_boxProd {α β : Type*} (G₁ : SimpleGraph α) (G₂ : SimpleGraph β)
    (h₁ : G₁.Connected) (h₂ : G₂.Connected) (hgd : GeodesicDeletion G₂) :
    GeodesicDeletion (G₁ □ G₂) := by
  exact GDProduct.gdPlus_boxProd h₁ h₂ hgd

/-- **Theorem 5 (Geodesic Deletion for abelian Cayley graphs), in the form of #334**: all of #334's
hypotheses kept, an abelian labelling added. -/
theorem geodesicDeletion_of_abelian_labelling :
    ∀ {V : Type} [Fintype V] (G : SimpleGraph V),
      G.Connected → IsVertexTransitive G → 3 ≤ Fintype.card V →
      HasAbelianLabelling G → GeodesicDeletion G := by
  intro V _ G hc hvt hn hlab
  obtain ⟨A, _, _, _, e, S, hG⟩ := hlab
  exact GDAbelian.main_abelian_cayley G hc hvt hn ⟨A, inferInstance, inferInstance, e, S, hG⟩

/-- **Theorem 5 in the paper's form**: every connected `Cay(A, S)` of a finite abelian group with
`|A| ≥ 3` satisfies the conclusion of #334. -/
theorem geodesicDeletion_cay (A : Type) [AddCommGroup A] [Fintype A] [DecidableEq A] (S : Finset A)
    (h0 : (0 : A) ∉ S) (hneg : ∀ s ∈ S, -s ∈ S) (hc : (cay A S h0 hneg).Connected)
    (hn : 3 ≤ Fintype.card A) :
    GeodesicDeletion (cay A S h0 hneg) := by
  exact GDAbelian.gd_abelian S (cay A S h0 hneg) (fun _ _ => Iff.rfl) hc hn

/-- **Theorem 6 (degree at least 6)**: every connected `Cay(A, S)` of an abelian group (finite or not)
with `|S| ≥ 6` satisfies the conclusion of #334. -/
theorem geodesicDeletion_cay_of_six_le (A : Type) [AddCommGroup A] [DecidableEq A] (S : Finset A)
    (h0 : (0 : A) ∉ S) (hneg : ∀ s ∈ S, -s ∈ S) (hc : (cay A S h0 hneg).Connected)
    (h6 : 6 ≤ S.card) :
    GeodesicDeletion (cay A S h0 hneg) := by
  exact GDAbelian.gd_abelian_card_ge_six S (cay A S h0 hneg) (fun _ _ => Iff.rfl) hc h6

end FairTraversal
