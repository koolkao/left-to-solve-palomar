/-
Copyright 2026 Ming-Chih Kao. Licensed under the Apache License, Version 2.0;
see the LICENSE file at the root of this repository.
-/
module

public import FriedanQ.KuboAndo

/-! Port: copied from `quantum-lean/FriedanQ/KAMain.lean` of github.com/koolkao/friedan-entropy-inequality (commit 0f4ba65dc126f59e7158fbcbc01548baa78cf21d, Lean v4.36.0, Mathlib fc4f59e, physlib edc607c) and put into the module system (`module` header, `public import`, public section). The proofs are unchanged unless a comment marked `Port` says otherwise. -/

@[expose] public section

/-!
# Kubo–Ando version: compound matrices and assembly
-/

open Real Finset Matrix
open scoped ComplexOrder AllOrdered

namespace FriedanQ

variable {d : Type*} [Fintype d] [DecidableEq d]

/-- `cfc f (U D Uᴴ) = U f(D) Uᴴ` for unitary `U` and real diagonal `D` (physlib lemmas). -/
lemma cfc_unitary_diag {e : Type*} [Fintype e] [DecidableEq e] {U : Matrix e e ℂ}
    (hU : U ∈ unitaryGroup e ℂ) (g : e → ℝ) (f : ℝ → ℝ) :
    cfc f (U * diagonal (fun i => (g i : ℂ)) * Uᴴ) =
      U * diagonal (fun i => ((f (g i) : ℝ) : ℂ)) * Uᴴ := by
  rw [mem_unitaryGroup_iff_isometry] at hU
  refine (Matrix.cfc_conj_isometry f hU.1 hU.2).trans ?_
  have h := Matrix.cfc_diagonal (𝕜 := ℂ) g f
  exact congrArg (fun Y => U * Y * Uᴴ) h

lemma compound_herm {X : Matrix d d ℂ} (hX : X.IsHermitian) (k : ℕ) :
    (compoundMatrix X k).IsHermitian :=
  (compoundMatrix_conjTranspose X k).symm.trans (congrArg (compoundMatrix · k) hX)

/-- The compound matrix commutes with a functional calculus that is multiplicative on the
`k`-subset products of eigenvalues. -/
lemma compound_cfc {X : Matrix d d ℂ} (hX : X.IsHermitian) (f : ℝ → ℝ) (k : ℕ)
    (hf : ∀ S : {S : Finset d // S.card = k},
      f (∏ i : Fin k, hX.eigenvalues (S.1.orderEmbOfFin S.2 i)) =
        ∏ i : Fin k, f (hX.eigenvalues (S.1.orderEmbOfFin S.2 i))) :
    compoundMatrix (cfc f X) k = cfc f (compoundMatrix X k) := by
  set U : Matrix d d ℂ := (hX.eigenvectorUnitary : Matrix d d ℂ)
  have hU : U ∈ unitaryGroup d ℂ := hX.eigenvectorUnitary.2
  have hXs : X = U * diagonal (fun i => (hX.eigenvalues i : ℂ)) * Uᴴ := by
    have h := hX.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at h
    exact h
  have hcf : cfc f X = U * diagonal (fun i => ((f (hX.eigenvalues i) : ℝ) : ℂ)) * Uᴴ := by
    rw [hX.cfc_eq f, Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply]
    rfl
  set V := compoundMatrix U k
  have hV : V ∈ unitaryGroup _ ℂ := compoundMatrix_unitary U hU k
  have hcomp : ∀ g : d → ℝ, compoundMatrix (U * diagonal (fun i => (g i : ℂ)) * Uᴴ) k =
      V * diagonal (fun S : {S : Finset d // S.card = k} =>
        ((∏ i : Fin k, g (S.1.orderEmbOfFin S.2 i) : ℝ) : ℂ)) * Vᴴ := by
    intro g
    rw [compoundMatrix_mul, compoundMatrix_mul, compoundMatrix_conjTranspose,
      compoundMatrix_diagonal]
    push_cast
    rfl
  rw [hcf, hcomp, show compoundMatrix X k = _ from congrArg (compoundMatrix · k) hXs, hcomp,
    cfc_unitary_diag hV]
  congr 3
  funext S
  rw [hf S]

lemma rpow_prod_hf {X : Matrix d d ℂ} (hX : X.IsHermitian) (h0 : ∀ i, 0 ≤ hX.eigenvalues i)
    (r : ℝ) (k : ℕ) (S : {S : Finset d // S.card = k}) :
    (∏ i : Fin k, hX.eigenvalues (S.1.orderEmbOfFin S.2 i)) ^ r =
      ∏ i : Fin k, hX.eigenvalues (S.1.orderEmbOfFin S.2 i) ^ r :=
  (Real.finsetProd_rpow univ _ (fun i _ => h0 _) r).symm

lemma compound_rpow {X : Matrix d d ℂ} (hX : X.PosDef) (r : ℝ) (k : ℕ) :
    compoundMatrix (cfc (fun x : ℝ => x ^ r) X) k =
      cfc (fun x : ℝ => x ^ r) (compoundMatrix X k) :=
  compound_cfc hX.1 _ k (rpow_prod_hf hX.1 (fun i => (hX.eigenvalues_pos i).le) r k)

lemma compound_eig {X : Matrix d d ℂ} (hX : X.IsHermitian) (k : ℕ) :
    ∃ τ : {S : Finset d // S.card = k} ≃ {S : Finset d // S.card = k},
      (compound_herm hX k).eigenvalues ∘ τ =
        fun S => ∏ i : Fin k, hX.eigenvalues (S.1.orderEmbOfFin S.2 i) :=
  HermitianMat.compoundHermitian_eigenvalues ⟨X, hX⟩ k

lemma compound_posDef {X : Matrix d d ℂ} (hX : X.PosDef) (k : ℕ) :
    (compoundMatrix X k).PosDef := by
  rw [(compound_herm hX.1 k).posDef_iff_eigenvalues_pos]
  obtain ⟨τ, hτ⟩ := compound_eig hX.1 k
  intro S
  have := congrFun hτ (τ.symm S)
  simp only [Function.comp_apply, Equiv.apply_symm_apply] at this
  rw [this]
  exact prod_pos fun i _ => hX.eigenvalues_pos _

lemma compound_kaM {σ ρ : Matrix d d ℂ} (hσ : σ.PosDef) (hρ : ρ.PosDef) (a : ℝ) (k : ℕ) :
    compoundMatrix (kaM a σ ρ) k = kaM a (compoundMatrix σ k) (compoundMatrix ρ k) := by
  unfold kaM
  rw [compoundMatrix_mul, compoundMatrix_mul,
    compound_cfc (ka_inner_posDef hσ hρ).1 _ k
      (rpow_prod_hf _ (fun i => ((ka_inner_posDef hσ hρ).eigenvalues_pos i).le) a k),
    compoundMatrix_mul, compoundMatrix_mul, compound_rpow hσ, compound_rpow hσ]

/-- product of eigenvalues over a set = some eigenvalue of the compound -/
lemma prod_eq_compound_eig {X : Matrix d d ℂ} (hX : X.IsHermitian) (S : Finset d) :
    ∃ j, ∏ i ∈ S, hX.eigenvalues i = (compound_herm hX S.card).eigenvalues j := by
  obtain ⟨τ, hτ⟩ := compound_eig hX S.card
  refine ⟨τ ⟨S, rfl⟩, ?_⟩
  have := congrFun hτ ⟨S, rfl⟩
  simp only [Function.comp_apply] at this
  rw [this, prod_oe]

/-- every eigenvalue of the compound is a product over a `k`-subset -/
lemma compound_eig_eq_prod {X : Matrix d d ℂ} (hX : X.IsHermitian) (k : ℕ)
    (j : {S : Finset d // S.card = k}) :
    ∃ T : Finset d, T.card = k ∧ (compound_herm hX k).eigenvalues j = ∏ i ∈ T, hX.eigenvalues i := by
  obtain ⟨τ, hτ⟩ := compound_eig hX k
  refine ⟨(τ.symm j).1, (τ.symm j).2, ?_⟩
  have := congrFun hτ (τ.symm j)
  simp only [Function.comp_apply, Equiv.apply_symm_apply] at this
  rw [this, prod_oe]

/-- **Friedan's quantum inequality, Kubo–Ando version (faithful states).**
`M = σ #ₐ ρ = σ^{1/2} (σ^{-1/2} ρ σ^{-1/2})^a σ^{1/2}`. -/
theorem friedan_KA (ρ σ : Matrix d d ℂ) (hρ : ρ.PosDef) (hσ : σ.PosDef)
    (hρ1 : ρ.trace = 1) (hσ1 : σ.trace = 1) {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    (trace (kaM a σ ρ)).re ^ 2 * vN ((trace (kaM a σ ρ)).re⁻¹ • kaM a σ ρ) ≤
      a * vN ρ + (1 - a) * vN σ := by
  have hMpd := kaM_posDef hσ hρ a
  set M := kaM a σ ρ
  have hM : M.IsHermitian := hMpd.1
  set μ := hM.eigenvalues
  have hμ : ∀ i, 0 < μ i := hMpd.eigenvalues_pos
  have hHρ : ρ.IsHermitian := hρ.1
  have hHσ : σ.IsHermitian := hσ.1
  set p := hHρ.eigenvalues
  set q := hHσ.eigenvalues
  have hp : ∀ i, 0 < p i := hρ.eigenvalues_pos
  have hq : ∀ i, 0 < q i := hσ.eigenvalues_pos
  have hps : ∑ i, p i = 1 := by
    have h := congrArg Complex.re (hHρ.trace_eq_sum_eigenvalues.symm.trans hρ1)
    simpa [Complex.re_sum] using h
  have hqs : ∑ i, q i = 1 := by
    have h := congrArg Complex.re (hHσ.trace_eq_sum_eigenvalues.symm.trans hσ1)
    simpa [Complex.re_sum] using h
  set x : d → ℝ := fun i => log (μ i)
  have hx : ∀ i, exp (x i) = μ i := fun i => exp_log (hμ i)
  have hW : ∀ S : Finset d, ∃ T U : Finset d, T.card = S.card ∧ U.card = S.card ∧
      ∑ i ∈ S, x i ≤ a * ∑ i ∈ T, log (p i) + (1 - a) * ∑ i ∈ U, log (q i) := by
    intro S
    set k := S.card
    haveI : Nonempty {S : Finset d // S.card = k} := ⟨⟨S, rfl⟩⟩
    have hΛσ := compound_posDef hσ k
    have hΛρ := compound_posDef hρ k
    set cσ := univ.sup' univ_nonempty (compound_herm hHσ k).eigenvalues
    set cρ := univ.sup' univ_nonempty (compound_herm hHρ k).eigenvalues
    obtain ⟨jσ, -, hjσ⟩ := exists_mem_eq_sup' univ_nonempty (compound_herm hHσ k).eigenvalues
    obtain ⟨jρ, -, hjρ⟩ := exists_mem_eq_sup' univ_nonempty (compound_herm hHρ k).eigenvalues
    obtain ⟨U, hU, hUq⟩ := compound_eig_eq_prod hHσ k jσ
    obtain ⟨T, hT, hTp⟩ := compound_eig_eq_prod hHρ k jρ
    have hcσ : cσ = ∏ i ∈ U, q i := hjσ.trans hUq
    have hcρ : cρ = ∏ i ∈ T, p i := hjρ.trans hTp
    have hcρ0 : 0 ≤ cρ := by rw [hcρ]; exact prod_nonneg fun i _ => (hp i).le
    have hle := ka_le (cσ := cσ) (cρ := cρ) hΛσ hΛρ ha0 ha1 hcρ0
      (le_max_eig (compound_herm hHσ k)) (le_max_eig (compound_herm hHρ k))
    rw [← compound_kaM hσ hρ a k] at hle
    obtain ⟨j, hj⟩ := prod_eq_compound_eig hM S
    have hb := eig_le_of_le (compound_herm hM k) hle j
    rw [← hj, hcρ, hcσ] at hb
    refine ⟨T, U, hT, hU, ?_⟩
    have hP : 0 < ∏ i ∈ S, μ i := prod_pos fun i _ => hμ i
    have hTP : 0 < ∏ i ∈ T, p i := prod_pos fun i _ => hp i
    have hUQ : 0 < ∏ i ∈ U, q i := prod_pos fun i _ => hq i
    have hl := log_le_log hP hb
    rw [log_mul (rpow_pos_of_pos hTP _).ne' (rpow_pos_of_pos hUQ _).ne', log_rpow hTP,
      log_rpow hUQ, log_prod (fun i _ => (hμ i).ne'), log_prod (fun i _ => (hp i).ne'),
      log_prod (fun i _ => (hq i).ne')] at hl
    exact hl
  have hQ := vecQ x p q hp hq hps hqs ha0 ha1 hW
  simp only [hx] at hQ
  -- identify the left side
  have hK : (trace M).re = ∑ i, μ i := by
    rw [hM.trace_eq_sum_eigenvalues]; simp [Complex.re_sum, μ]
  rw [hK]
  set K := ∑ i, μ i
  have hZ : K⁻¹ • M = cfc (fun t : ℝ => K⁻¹ * t) M :=
    ((congrArg (K⁻¹ • ·) (cfc_id' ℝ M hM)).symm).trans
      (cfc_const_mul K⁻¹ (fun t : ℝ => t) M (fin_cont _ _)).symm
  have hS : vN (K⁻¹ • M) = ∑ i, negMulLog (μ i / K) := by
    have hZh : (cfc (fun t : ℝ => K⁻¹ * t) M).IsHermitian := cfc_predicate _ _
    rw [hZ, vN, trace_cfc_re hZh]
    obtain ⟨e, he⟩ := hM.cfc_eigenvalues (fun t : ℝ => K⁻¹ * t)
    rw [he]
    simp only [Function.comp_apply, inv_mul_eq_div]
    exact Equiv.sum_comp e (fun i => negMulLog (μ i / K))
  rw [hS, vN, vN, trace_cfc_re hHρ, trace_cfc_re hHσ]
  exact hQ

end FriedanQ

end
