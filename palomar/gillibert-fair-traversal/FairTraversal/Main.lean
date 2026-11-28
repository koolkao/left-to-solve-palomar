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

end FairTraversal
