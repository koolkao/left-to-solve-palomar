/-
Copyright 2026 Ming-Chih Kao. Licensed under the Apache License, Version 2.0;
see the LICENSE file at the root of this repository.
-/
module

public import FriedanQ.Hamiltonian
public import QuantumInfo.ForMathlib.Majorization

/-! Port: copied from `quantum-lean/FriedanQ/MatrixAZ.lean` of github.com/koolkao/friedan-entropy-inequality (commit 0f4ba65dc126f59e7158fbcbc01548baa78cf21d, Lean v4.36.0, Mathlib fc4f59e, physlib edc607c) and put into the module system (`module` header, `public import`, public section). The proofs are unchanged unless a comment marked `Port` says otherwise. -/

@[expose] public section

/-!
# Friedan's quantum inequality for the α-z means (Petz `z = 1`, sandwiched `z = a`)

`M = (ρ^{a/2z} σ^{(1-a)/z} ρ^{a/2z})^z`, `z > 0`, faithful `ρ, σ`, `0 ≤ a ≤ 1`:
`K² S(M/K) ≤ a S(ρ) + (1-a) S(σ)`, `K = tr M`.

Proof: with `R = ρ^{a/2z}`, `T = σ^{(1-a)/2z}`, `X = T R`, `XᴴX = R T² R`, so
`spec(M) = s(X)^{2z}`; Horn's inequality (physlib `horn_weak_log_majorization`) gives the weak
log-majorization, and `vecQ` finishes.
-/

open Real Finset Matrix
open scoped ComplexOrder AllOrdered

namespace FriedanQ

variable {d : Type*} [Fintype d] [DecidableEq d]

lemma eig_congr {A B : Matrix d d ℂ} (h : A = B) (hA : A.IsHermitian) (hB : B.IsHermitian) :
    hA.eigenvalues = hB.eigenvalues := by subst h; rfl

lemma spec_pos {ρ : Matrix d d ℂ} (hρ : ρ.PosDef) {t : ℝ} (ht : t ∈ spectrum ℝ ρ) : 0 < t := by
  rw [hρ.1.spectrum_real_eq_range_eigenvalues] at ht
  obtain ⟨i, rfl⟩ := ht
  exact hρ.eigenvalues_pos i

lemma cfc_posDef {ρ : Matrix d d ℂ} (hρ : ρ.PosDef) {f : ℝ → ℝ} (hf : ∀ t, 0 < t → 0 < f t) :
    (cfc f ρ).PosDef := by
  have hh : (cfc f ρ).IsHermitian := cfc_predicate _ _
  rw [hh.posDef_iff_eigenvalues_pos]
  obtain ⟨e, he⟩ := hρ.1.cfc_eigenvalues f
  intro i
  rw [he]
  exact hf _ (hρ.eigenvalues_pos _)

lemma rpow_mul_rpow {ρ : Matrix d d ℂ} (hρ : ρ.PosDef) (r s : ℝ) :
    cfc (fun x : ℝ => x ^ r) ρ * cfc (fun x : ℝ => x ^ s) ρ = cfc (fun x : ℝ => x ^ (r + s)) ρ :=
  (cfc_mul (fun x : ℝ => x ^ r) (fun x : ℝ => x ^ s) ρ (fin_cont _ _) (fin_cont _ _)).symm.trans
    (cfc_congr (fun t ht => (rpow_add (spec_pos hρ ht) r s).symm))

lemma conjT_cfc (f : ℝ → ℝ) (A : Matrix d d ℂ) : (cfc f A)ᴴ = cfc f A :=
  (cfc_predicate f A : IsSelfAdjoint (cfc f A))

/-- singular values of `ρ^r` are `p^r` up to a permutation -/
lemma sv_rpow {ρ : Matrix d d ℂ} (hρ : ρ.PosDef) (r : ℝ) :
    ∃ e : d ≃ d, ∀ i, singularValues (cfc (fun x : ℝ => x ^ r) ρ) i =
      hρ.1.eigenvalues (e i) ^ r := by
  set R := cfc (fun x : ℝ => x ^ r) ρ
  have hRR : Rᴴ * Rᴴᴴ = cfc (fun x : ℝ => x ^ (r + r)) ρ := by
    rw [conjTranspose_conjTranspose, conjT_cfc]; exact rpow_mul_rpow hρ r r
  obtain ⟨e, he⟩ := hρ.1.cfc_eigenvalues (fun x : ℝ => x ^ (r + r))
  refine ⟨e, fun i => ?_⟩
  unfold singularValues
  rw [eig_congr hRR _ (cfc_predicate _ _), he]
  simp only [Function.comp_apply]
  have hp := hρ.eigenvalues_pos (e i)
  rw [rpow_add hp, ← sq, sqrt_sq (rpow_nonneg hp.le _)]

/-- `s(X)² = eig(XᴴX)` -/
lemma sv_sq (X : Matrix d d ℂ) (h : (Xᴴ * X).IsHermitian) (i : d) :
    singularValues X i ^ 2 = h.eigenvalues i := by
  unfold singularValues
  have hc : Xᴴ * Xᴴᴴ = Xᴴ * X := by rw [conjTranspose_conjTranspose]
  rw [eig_congr hc _ h]
  exact sq_sqrt ((posSemidef_conjTranspose_mul_self X).eigenvalues_nonneg i)

lemma prod_oe {k : ℕ} (S : Finset d) (h : S.card = k) (f : d → ℝ) :
    ∏ i : Fin k, f (S.orderEmbOfFin h i) = ∏ j ∈ S, f j := by
  conv_rhs => rw [← map_orderEmbOfFin_univ S h, prod_map]
  rfl

/-- **Horn, sorting-free form** (from physlib). -/
lemma horn_subset (A B : Matrix d d ℂ) (S : Finset d) :
    ∃ T U : Finset d, T.card = S.card ∧ U.card = S.card ∧
      ∏ i ∈ S, singularValues (A * B) i ≤
        (∏ i ∈ T, singularValues A i) * ∏ i ∈ U, singularValues B i := by
  set k := S.card
  have hk : k ≤ Fintype.card d := card_le_univ S
  obtain ⟨⟨T, hT⟩, hTe⟩ := exists_subset_prod_eq_sorted_prod A k hk
  obtain ⟨⟨U, hU⟩, hUe⟩ := exists_subset_prod_eq_sorted_prod B k hk
  refine ⟨T, U, hT, hU, ?_⟩
  have h1 := prod_singularValues_subset_le_sorted_prod (A * B) k hk ⟨S, rfl⟩
  have h2 := horn_weak_log_majorization A B k hk
  rw [prod_mul_distrib] at h2
  rw [prod_oe] at h1 hTe hUe
  rw [hTe, hUe]
  exact h1.trans h2

/-- **Friedan's quantum inequality for the α-z mean (faithful states), any `z > 0`.**
`z = 1`: Petz; `z = a`: sandwiched. -/
theorem friedan_alphaZ (ρ σ : Matrix d d ℂ) (hρ : ρ.PosDef) (hσ : σ.PosDef)
    (hρ1 : ρ.trace = 1) (hσ1 : σ.trace = 1) {a z : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hz : 0 < z) :
    let M := cfc (fun x : ℝ => x ^ z)
      (cfc (fun x : ℝ => x ^ (a / (2 * z))) ρ * cfc (fun x : ℝ => x ^ ((1 - a) / z)) σ *
        cfc (fun x : ℝ => x ^ (a / (2 * z))) ρ)
    (trace M).re ^ 2 * vN ((trace M).re⁻¹ • M) ≤ a * vN ρ + (1 - a) * vN σ := by
  intro M
  set R := cfc (fun x : ℝ => x ^ (a / (2 * z))) ρ
  set T := cfc (fun x : ℝ => x ^ ((1 - a) / (2 * z))) σ
  set T2 := cfc (fun x : ℝ => x ^ ((1 - a) / z)) σ
  have hT2 : T2 = T * T := by
    have h1 : T * T = cfc (fun x : ℝ => x ^ ((1 - a) / (2 * z) + (1 - a) / (2 * z))) σ :=
      rpow_mul_rpow hσ _ _
    have hexp : (1 - a) / (2 * z) + (1 - a) / (2 * z) = (1 - a) / z := by
      field_simp; ring
    rw [h1, hexp]
  set N := R * T2 * R
  have hN_eq : N = (T * R)ᴴ * (T * R) := by
    have hTh : Tᴴ = T := conjT_cfc _ _
    have hRh : Rᴴ = R := conjT_cfc _ _
    rw [conjTranspose_mul, hTh, hRh]
    simp only [N, hT2, mul_assoc]
  have hRpd : R.PosDef := cfc_posDef hρ (fun t ht => rpow_pos_of_pos ht _)
  have hT2pd : T2.PosDef := cfc_posDef hσ (fun t ht => rpow_pos_of_pos ht _)
  have hNpd : N.PosDef := by
    have h := hT2pd.conjTranspose_mul_mul_same (B := R)
      (mulVec_injective_iff_isUnit.2 hRpd.isUnit)
    rwa [conjT_cfc] at h
  have hN : N.IsHermitian := hNpd.1
  set ν := hN.eigenvalues
  have hν : ∀ i, 0 < ν i := hNpd.eigenvalues_pos
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
  -- `ν = s(TR)²`
  have hsv : ∀ i, singularValues (T * R) i ^ 2 = ν i := by
    intro i
    rw [sv_sq (T * R) (hN_eq ▸ hN) i]
    exact congrFun (eig_congr hN_eq.symm _ hN) i
  have hsvpos : ∀ i, 0 < singularValues (T * R) i := by
    intro i
    have h2 : 0 < singularValues (T * R) i ^ 2 := (hsv i).symm ▸ hν i
    exact lt_of_le_of_ne (singularValues_nonneg _ _) (fun h => by rw [← h] at h2; simp at h2)
  set x : d → ℝ := fun i => z * log (ν i)
  have hx : ∀ i, exp (x i) = ν i ^ z := by
    intro i; simp only [x]; rw [rpow_def_of_pos (hν i), mul_comm]
  obtain ⟨eR, heR⟩ := sv_rpow hρ (a / (2 * z))
  obtain ⟨eT, heT⟩ := sv_rpow hσ ((1 - a) / (2 * z))
  have hW : ∀ S : Finset d, ∃ T' U' : Finset d, T'.card = S.card ∧ U'.card = S.card ∧
      ∑ i ∈ S, x i ≤ a * ∑ i ∈ T', log (p i) + (1 - a) * ∑ i ∈ U', log (q i) := by
    intro S
    obtain ⟨T1, U1, hT1, hU1, hle⟩ := horn_subset T R S
    refine ⟨U1.map eR.toEmbedding, T1.map eT.toEmbedding, by simp [hU1], by simp [hT1], ?_⟩
    have hlog : ∑ i ∈ S, log (singularValues (T * R) i) ≤
        ∑ i ∈ T1, log (singularValues T i) + ∑ i ∈ U1, log (singularValues R i) := by
      have hposT : ∀ i, 0 < singularValues T i := fun i => by
        rw [heT]; exact rpow_pos_of_pos (hq _) _
      have hposR : ∀ i, 0 < singularValues R i := fun i => by
        rw [heR]; exact rpow_pos_of_pos (hp _) _
      rw [← log_prod (fun i _ => (hsvpos i).ne'), ← log_prod (fun i _ => (hposT i).ne'),
        ← log_prod (fun i _ => (hposR i).ne'), ← log_mul (prod_pos fun i _ => hposT i).ne'
          (prod_pos fun i _ => hposR i).ne']
      exact log_le_log (prod_pos fun i _ => hsvpos i) hle
    have e1 : ∑ i ∈ S, x i = 2 * z * ∑ i ∈ S, log (singularValues (T * R) i) := by
      simp only [x, mul_sum]
      refine sum_congr rfl (fun i _ => ?_)
      rw [← hsv i, log_pow]; push_cast; ring
    have e2 : ∑ i ∈ T1, log (singularValues T i) =
        (1 - a) / (2 * z) * ∑ i ∈ T1.map eT.toEmbedding, log (q i) := by
      rw [sum_map, mul_sum]
      refine sum_congr rfl (fun i _ => ?_)
      rw [heT, log_rpow (hq _)]; rfl
    have e3 : ∑ i ∈ U1, log (singularValues R i) =
        a / (2 * z) * ∑ i ∈ U1.map eR.toEmbedding, log (p i) := by
      rw [sum_map, mul_sum]
      refine sum_congr rfl (fun i _ => ?_)
      rw [heR, log_rpow (hp _)]; rfl
    rw [e1]
    rw [e2, e3] at hlog
    have h2z : 0 < 2 * z := by positivity
    have := mul_le_mul_of_nonneg_left hlog h2z.le
    have e4 : 2 * z * ((1 - a) / (2 * z) * ∑ i ∈ T1.map eT.toEmbedding, log (q i) +
        a / (2 * z) * ∑ i ∈ U1.map eR.toEmbedding, log (p i)) =
        a * ∑ i ∈ U1.map eR.toEmbedding, log (p i) +
          (1 - a) * ∑ i ∈ T1.map eT.toEmbedding, log (q i) := by
      field_simp; ring
    linarith
  have hQ := vecQ x p q hp hq hps hqs ha0 ha1 hW
  simp only [hx] at hQ
  -- identify the left side
  have hMN : M = cfc (fun t : ℝ => t ^ z) N := rfl
  have hK : (trace M).re = ∑ i, ν i ^ z := by rw [hMN]; exact trace_cfc_re hN _
  rw [hK]
  set K := ∑ i, ν i ^ z
  have hZ : K⁻¹ • M = cfc (fun t : ℝ => K⁻¹ * t ^ z) N :=
    (cfc_const_mul K⁻¹ (fun t : ℝ => t ^ z) N (fin_cont _ _)).symm
  have hS : vN (K⁻¹ • M) = ∑ i, negMulLog (ν i ^ z / K) := by
    have hZh : (cfc (fun t : ℝ => K⁻¹ * t ^ z) N).IsHermitian := cfc_predicate _ _
    rw [hZ, vN, trace_cfc_re hZh]
    obtain ⟨e, he⟩ := hN.cfc_eigenvalues (fun t : ℝ => K⁻¹ * t ^ z)
    rw [he]
    simp only [Function.comp_apply, inv_mul_eq_div]
    exact Equiv.sum_comp e (fun i => negMulLog (ν i ^ z / K))
  rw [hS, vN, vN, trace_cfc_re hHρ, trace_cfc_re hHσ]
  exact hQ

end FriedanQ

end
