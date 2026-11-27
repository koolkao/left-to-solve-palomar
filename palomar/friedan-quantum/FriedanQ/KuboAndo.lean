/-
Copyright 2026 Ming-Chih Kao. Licensed under the Apache License, Version 2.0;
see the LICENSE file at the root of this repository.
-/
module

public import FriedanQ.PSD
public import QuantumInfo.ForMathlib.HermitianMat.CompoundMatrix
public import QuantumInfo.ForMathlib.Isometry
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Order

/-! Port: copied from `quantum-lean/FriedanQ/KuboAndo.lean` of github.com/koolkao/friedan-entropy-inequality (commit 0f4ba65dc126f59e7158fbcbc01548baa78cf21d, Lean v4.36.0, Mathlib fc4f59e, physlib edc607c) and put into the module system (`module` header, `public import`, public section). The proofs are unchanged unless a comment marked `Port` says otherwise. -/

@[expose] public section

/-!
# Friedan's quantum inequality for the Kubo–Ando geometric mean

`σ #ₐ ρ = σ^{1/2} (σ^{-1/2} ρ σ^{-1/2})^a σ^{1/2}` (faithful `ρ, σ`, `0 ≤ a ≤ 1`).

Ando–Hiai route:
1. `ka_le`: if `ρ ≤ cρ`, `σ ≤ cσ` then `σ #ₐ ρ ≤ cρ^a cσ^{1-a}` (Löwner–Heinz: Mathlib
   `CFC.rpow_le_rpow`), so `λ₁(σ #ₐ ρ) ≤ λ₁(ρ)^a λ₁(σ)^{1-a}`.
2. `compound_cfc`: the compound (antisymmetric power) commutes with `x ↦ x^r` on Hermitian
   matrices with nonnegative spectrum (physlib `compoundMatrix_*`, `Matrix.cfc_conj_isometry`,
   `Matrix.cfc_diagonal`), so `Λᵏ(σ #ₐ ρ) = Λᵏσ #ₐ Λᵏρ`.
3. Eigenvalues of `Λᵏ X` are the `k`-subset products of eigenvalues of `X` (physlib
   `HermitianMat.compoundHermitian_eigenvalues`); so 1 applied to `Λᵏ` gives the weak
   log-majorization, and `vecQ` finishes.
-/

open Real Finset Matrix
open scoped ComplexOrder AllOrdered

namespace FriedanQ

section general

variable {e : Type*} [Fintype e] [DecidableEq e]

/-- Kubo–Ando weighted geometric mean `σ #ₐ ρ` (weight `a` on `ρ`). -/
noncomputable def kaM (a : ℝ) (σ ρ : Matrix e e ℂ) : Matrix e e ℂ :=
  cfc (fun x : ℝ => x ^ (1 / 2 : ℝ)) σ *
    cfc (fun x : ℝ => x ^ a)
      (cfc (fun x : ℝ => x ^ (-(1 / 2) : ℝ)) σ * ρ * cfc (fun x : ℝ => x ^ (-(1 / 2) : ℝ)) σ) *
    cfc (fun x : ℝ => x ^ (1 / 2 : ℝ)) σ

lemma ka_inner_posDef {σ ρ : Matrix e e ℂ} (hσ : σ.PosDef) (hρ : ρ.PosDef) :
    (cfc (fun x : ℝ => x ^ (-(1 / 2) : ℝ)) σ * ρ * cfc (fun x : ℝ => x ^ (-(1 / 2) : ℝ)) σ).PosDef := by
  have hs : (cfc (fun x : ℝ => x ^ (-(1 / 2) : ℝ)) σ).PosDef :=
    cfc_posDef hσ (fun t ht => rpow_pos_of_pos ht _)
  have h := hρ.conjTranspose_mul_mul_same (B := cfc (fun x : ℝ => x ^ (-(1 / 2) : ℝ)) σ)
    (mulVec_injective_iff_isUnit.2 hs.isUnit)
  rwa [conjT_cfc] at h

lemma kaM_posDef {σ ρ : Matrix e e ℂ} (hσ : σ.PosDef) (hρ : ρ.PosDef) (a : ℝ) :
    (kaM a σ ρ).PosDef := by
  have hC := ka_inner_posDef hσ hρ
  have hCa : (cfc (fun x : ℝ => x ^ a)
      (cfc (fun x : ℝ => x ^ (-(1 / 2) : ℝ)) σ * ρ * cfc (fun x : ℝ => x ^ (-(1 / 2) : ℝ)) σ)).PosDef :=
    cfc_posDef hC (fun t ht => rpow_pos_of_pos ht _)
  have hs : (cfc (fun x : ℝ => x ^ (1 / 2 : ℝ)) σ).PosDef :=
    cfc_posDef hσ (fun t ht => rpow_pos_of_pos ht _)
  have h := hCa.conjTranspose_mul_mul_same (B := cfc (fun x : ℝ => x ^ (1 / 2 : ℝ)) σ)
    (mulVec_injective_iff_isUnit.2 hs.isUnit)
  rw [conjT_cfc] at h
  exact h

section order

open scoped MatrixOrder Matrix.Norms.L2Operator

lemma smul_le_smul' {X Y : Matrix e e ℂ} (h : X ≤ Y) {c : ℝ} (hc : 0 ≤ c) : c • X ≤ c • Y := by
  rw [Matrix.le_iff] at h ⊢
  rw [← smul_sub]
  exact h.smul hc

/-- Löwner–Heinz for matrices (from Mathlib's `CFC.rpow_le_rpow`). -/
lemma lowner_heinz {A B : Matrix e e ℂ} (hA : 0 ≤ A) (hAB : A ≤ B) {p : ℝ}
    (hp : p ∈ Set.Icc (0 : ℝ) 1) :
    cfc (fun x : ℝ => x ^ p) A ≤ cfc (fun x : ℝ => x ^ p) B := by
  have h := CFC.rpow_le_rpow hp hAB
  rwa [CFC.rpow_eq_cfc_real hA, CFC.rpow_eq_cfc_real (hA.trans hAB)] at h

lemma scalar_conj (s : Matrix e e ℂ) (c : ℝ) :
    s * algebraMap ℝ (Matrix e e ℂ) c * s = c • (s * s) := by
  rw [Algebra.algebraMap_eq_smul_one, mul_smul_comm, mul_one, smul_mul_assoc]

/-- **λ₁ bound** (Ando–Hiai): `ρ ≤ cρ`, `σ ≤ cσ` ⇒ `σ #ₐ ρ ≤ cρ^a cσ^{1-a}`. -/
lemma ka_le {σ ρ : Matrix e e ℂ} (hσ : σ.PosDef) (hρ : ρ.PosDef) {a : ℝ} (ha0 : 0 ≤ a)
    (ha1 : a ≤ 1) {cσ cρ : ℝ} (hcρ : 0 ≤ cρ)
    (hσc : σ ≤ algebraMap ℝ (Matrix e e ℂ) cσ) (hρc : ρ ≤ algebraMap ℝ (Matrix e e ℂ) cρ) :
    kaM a σ ρ ≤ algebraMap ℝ (Matrix e e ℂ) (cρ ^ a * cσ ^ (1 - a)) := by
  set sh := cfc (fun x : ℝ => x ^ (1 / 2 : ℝ)) σ
  set si := cfc (fun x : ℝ => x ^ (-(1 / 2) : ℝ)) σ
  set C := si * ρ * si
  have hsi : star si = si := conjT_cfc _ _
  have hsh : star sh = sh := conjT_cfc _ _
  -- step 1: `C ≤ cρ σ⁻¹`
  have hsisi : si * si = cfc (fun x : ℝ => x ^ (-1 : ℝ)) σ := by
    rw [rpow_mul_rpow hσ]; norm_num
  have h1 : C ≤ cρ • cfc (fun x : ℝ => x ^ (-1 : ℝ)) σ := by
    have := star_left_conjugate_le_conjugate hρc si
    rw [hsi, scalar_conj, hsisi] at this
    exact this
  -- step 2: Löwner–Heinz
  have hC0 : 0 ≤ C := Matrix.nonneg_iff_posSemidef.2 (ka_inner_posDef hσ hρ).posSemidef
  have h2 := lowner_heinz hC0 h1 ⟨ha0, ha1⟩
  have e2 : cfc (fun x : ℝ => x ^ a) (cρ • cfc (fun x : ℝ => x ^ (-1 : ℝ)) σ) =
      cρ ^ a • cfc (fun x : ℝ => x ^ (-a)) σ := by
    have i1 : cρ • cfc (fun x : ℝ => x ^ (-1 : ℝ)) σ = cfc (fun x : ℝ => cρ * x ^ (-1 : ℝ)) σ :=
      (cfc_const_mul cρ _ σ (fin_cont _ _)).symm
    rw [i1]
    refine (cfc_comp (fun x : ℝ => x ^ a) (fun x : ℝ => cρ * x ^ (-1 : ℝ)) σ hσ.1
      (((Matrix.finite_real_spectrum (A := σ)).image _).continuousOn _)
      (fin_cont _ _)).symm.trans ?_
    refine (cfc_congr (fun t ht => ?_)).trans (cfc_const_mul (cρ ^ a) _ σ (fin_cont _ _))
    have htp := spec_pos hσ ht
    simp only [Function.comp_apply]
    rw [mul_rpow hcρ (rpow_nonneg htp.le _), ← rpow_mul htp.le]
    ring_nf
  rw [e2] at h2
  -- step 3: conjugate by `σ^{1/2}`
  have h3 := star_left_conjugate_le_conjugate h2 sh
  rw [hsh] at h3
  have e3 : sh * (cρ ^ a • cfc (fun x : ℝ => x ^ (-a)) σ) * sh =
      cρ ^ a • cfc (fun x : ℝ => x ^ (1 - a)) σ := by
    rw [mul_smul_comm, smul_mul_assoc, rpow_mul_rpow hσ, rpow_mul_rpow hσ]
    congr 3; ring
  rw [e3] at h3
  -- step 4: `σ^{1-a} ≤ cσ^{1-a}`
  have hσ0 : 0 ≤ σ := Matrix.nonneg_iff_posSemidef.2 hσ.posSemidef
  have h4 := lowner_heinz hσ0 hσc ⟨by linarith, by linarith⟩ (p := 1 - a)
  rw [cfc_algebraMap] at h4
  have h5 := smul_le_smul' h4 (rpow_nonneg hcρ a)
  have e5 : cρ ^ a • algebraMap ℝ (Matrix e e ℂ) (cσ ^ (1 - a)) =
      algebraMap ℝ (Matrix e e ℂ) (cρ ^ a * cσ ^ (1 - a)) := by
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, smul_smul]
  rw [e5] at h5
  exact h3.trans h5

lemma le_max_eig {X : Matrix e e ℂ} (hX : X.IsHermitian) [Nonempty e] :
    X ≤ algebraMap ℝ (Matrix e e ℂ) (univ.sup' univ_nonempty hX.eigenvalues) := by
  rw [le_algebraMap_iff_spectrum_le hX, hX.spectrum_real_eq_range_eigenvalues]
  rintro x ⟨i, rfl⟩
  exact le_sup' _ (mem_univ i)

lemma eig_le_of_le {X : Matrix e e ℂ} (hX : X.IsHermitian) {c : ℝ}
    (h : X ≤ algebraMap ℝ (Matrix e e ℂ) c) (i : e) : hX.eigenvalues i ≤ c :=
  (le_algebraMap_iff_spectrum_le hX).1 h _ (hX.eigenvalues_mem_spectrum_real i)

end order

end general

end FriedanQ

end
