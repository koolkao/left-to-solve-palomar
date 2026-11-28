/-
Copyright 2026 Ming-Chih Kao. Licensed under the Apache License, Version 2.0;
see the LICENSE file at the root of this repository.
-/
module

public import FairTraversal.Defs
public import FairTraversal.FTGP102
public import FairTraversal.FTProduct
public import FairTraversal.GDProduct
public import FairTraversal.GDAbelian

/-!
# Bridges between the Challenge vocabulary and the proof development

`gpGraph_eq` is `FTCheck.gpGraph_eq` of the source repository's `Check.lean`. `pwEquiv` identifies `A × Bool`
with the group `FTDih.Pw A k z` of `FTPower.lean`; `pw_mem` says that the labelling condition written with
`pwMul`/`pwInv` is the group-labelling condition of `FTDih.main_pow_cayley`.
-/

@[expose] public section

namespace FairTraversal

/-- The from-scratch graph is `FTGP.gp`. -/
theorem gpGraph_eq (m : ℕ) (k : ℤ) : gpGraph m k = FTGP.gp m k := by
  ext ⟨x, i⟩ ⟨y, j⟩
  simp only [gpGraph, FTGP.gp, SimpleGraph.fromRel_adj, FTGP.gpRel]
  cases i <;> cases j <;> simp [eq_comm]

/-- `A × Bool ≃ Γ(A, k, z)`. -/
def pwEquiv (A : Type) [AddCommGroup A] (k : ℤ) (z : A) : A × Bool ≃ FTDih.Pw A k z where
  toFun x := ⟨x.1, x.2⟩
  invFun p := (p.r, p.s)
  left_inv _ := rfl
  right_inv _ := rfl

lemma pwEquiv_mul {A : Type} [AddCommGroup A] (k : ℤ) (z : A) (x y : A × Bool) :
    (pwEquiv A k z x)⁻¹ * pwEquiv A k z y = pwEquiv A k z (pwMul k z (pwInv k z x) y) := by
  obtain ⟨a, i⟩ := x
  obtain ⟨b, j⟩ := y
  cases i <;> cases j <;> rfl

lemma pw_mem {V A : Type} [AddCommGroup A] [DecidableEq A] (k : ℤ) (z : A) (e : V ≃ A × Bool)
    (S : Finset (A × Bool)) (u v : V) :
    pwMul k z (pwInv k z (e u)) (e v) ∈ S ↔
      ((e.trans (pwEquiv A k z)) u)⁻¹ * (e.trans (pwEquiv A k z)) v ∈ S.map (pwEquiv A k z).toEmbedding := by
  rw [Equiv.trans_apply, Equiv.trans_apply, pwEquiv_mul, Finset.mem_map_equiv, Equiv.symm_apply_apply]

/-- `HasFairTraversal` in the form used by the proof modules (`FTProduct.FTConcl` and the conclusions of
`FTAbelian`, `FTDih`, `FTGP`, `FTGP102`). -/
lemma hasFairTraversal_iff {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) :
    HasFairTraversal G ↔ ∃ (r k : ℕ), 0 < r ∧ 0 < k ∧
      ∃ (a b : Fin r → V) (P : ∀ i, G.Walk (a i) (b i)),
        (∀ i, (P i).IsHamiltonian) ∧
        ∀ e ∈ G.edgeSet, (Finset.univ.filter fun i => e ∈ (P i).edges).card = k := by
  constructor
  · rintro ⟨r, ends, P, k, hr, hk, hP, hc⟩
    exact ⟨r, k, hr, hk, fun i => (ends i).1, fun i => (ends i).2, P, hP, hc⟩
  · rintro ⟨r, k, hr, hk, a, b, P, hP, hc⟩
    exact ⟨r, fun i => (a i, b i), P, k, hr, hk, hP, hc⟩

/-- `HasGeodesicDeletion` is `GDProduct.GDPlus`. -/
lemma hasGeodesicDeletion_iff {V : Type*} (G : SimpleGraph V) :
    HasGeodesicDeletion G ↔ GDProduct.GDPlus G := by
  unfold HasGeodesicDeletion IsGeodesicPath GDProduct.GDPlus
  constructor
  · intro h u v p hp hl
    have := h u v p ⟨hp, hl⟩
    convert this using 2
  · intro h u v p ⟨hp, hl⟩
    have := h u v p hp hl
    convert this using 2

end FairTraversal
