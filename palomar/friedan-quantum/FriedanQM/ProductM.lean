/-
Copyright 2026 Ming-Chih Kao. Licensed under the Apache License, Version 2.0;
see the LICENSE file at the root of this repository.
-/
module

public import FriedanQM.MatrixLEM
public import FriedanQ.MatrixAZ

/-! Port: copied from `quantum-lean/FriedanQM/ProductM.lean` of github.com/koolkao/friedan-entropy-inequality (commit 0f4ba65dc126f59e7158fbcbc01548baa78cf21d, Lean v4.36.0, Mathlib fc4f59e, physlib edc607c) and put into the module system (`module` header, `public import`, public section). The proofs are unchanged unless a comment marked `Port` says otherwise. -/

@[expose] public section

/-!
# Quantum Theorem M for multivariate product means

`X = ρ₀^{a₀/2z} ρ₁^{a₁/2z} ⋯ ρ_m^{a_m/2z}` (any fixed ordering; `m + 1` states), `M = (Xᴴ X)^z`,
`z > 0`: `K² S(M/K) ≤ ∑ⱼ aⱼ S(ρⱼ)`. For two states this is the α-z family (Petz, sandwiched).
Horn's inequality for `m + 1` factors (`horn_log_multi`, by induction from physlib's two-factor
Horn via `horn_subset` of `FriedanQ/MatrixAZ.lean`), then `vecQM`.
-/

open Real Finset Matrix
open scoped ComplexOrder AllOrdered

namespace FriedanQ

variable {d : Type*} [Fintype d] [DecidableEq d]

/-- ordered product `R 0 * R 1 * ⋯ * R m` -/
def prodF : (m : ℕ) → (Fin (m + 1) → Matrix d d ℂ) → Matrix d d ℂ
  | 0, R => R 0
  | m + 1, R => prodF m (fun j => R j.castSucc) * R (Fin.last (m + 1))

lemma sv_pos_of_isUnit {X : Matrix d d ℂ} (hX : IsUnit X) (i : d) : 0 < singularValues X i := by
  have hN : (Xᴴ * X).PosDef := by
    have h := (Matrix.PosDef.one (n := d) (R := ℂ)).conjTranspose_mul_mul_same
      (B := X) (mulVec_injective_iff_isUnit.2 hX)
    rwa [Matrix.mul_one] at h
  have h2 := sv_sq X hN.1 i
  have h3 := hN.eigenvalues_pos i
  rw [← h2] at h3
  exact lt_of_le_of_ne (singularValues_nonneg _ _) (fun h => by rw [← h] at h3; simp at h3)

lemma prodF_isUnit : ∀ (m : ℕ) (R : Fin (m + 1) → Matrix d d ℂ), (∀ j, IsUnit (R j)) →
    IsUnit (prodF m R)
  | 0, R, h => h 0
  | m + 1, R, h => (prodF_isUnit m _ (fun j => h _)).mul (h _)

/-- **Horn for `m + 1` factors, sorting-free log form.** -/
lemma horn_log_multi : ∀ (m : ℕ) (R : Fin (m + 1) → Matrix d d ℂ), (∀ j, IsUnit (R j)) →
    ∀ S : Finset d, ∃ T : Fin (m + 1) → Finset d, (∀ j, (T j).card = S.card) ∧
      ∑ i ∈ S, log (singularValues (prodF m R) i) ≤
        ∑ j, ∑ i ∈ T j, log (singularValues (R j) i)
  | 0, R, _, S => ⟨fun _ => S, fun _ => rfl, by simp [prodF]⟩
  | m + 1, R, hR, S => by
    set Y := prodF m (fun j => R j.castSucc)
    have hY : IsUnit Y := prodF_isUnit m _ (fun j => hR _)
    obtain ⟨T, U, hT, hU, hle⟩ := horn_subset Y (R (Fin.last (m + 1))) S
    obtain ⟨T', hT', hle'⟩ := horn_log_multi m (fun j => R j.castSucc) (fun j => hR _) T
    refine ⟨Fin.lastCases U T', fun j => ?_, ?_⟩
    · induction j using Fin.lastCases with
      | last => simp [hU]
      | cast j => simp [hT', hT]
    have hposY := sv_pos_of_isUnit hY
    have hposL := sv_pos_of_isUnit (hR (Fin.last (m + 1)))
    have hposP := sv_pos_of_isUnit (hY.mul (hR (Fin.last (m + 1))))
    have hlog : ∑ i ∈ S, log (singularValues (Y * R (Fin.last (m + 1))) i) ≤
        ∑ i ∈ T, log (singularValues Y i) +
          ∑ i ∈ U, log (singularValues (R (Fin.last (m + 1))) i) := by
      rw [← log_prod (fun i _ => (hposP i).ne'), ← log_prod (fun i _ => (hposY i).ne'),
        ← log_prod (fun i _ => (hposL i).ne'), ← log_mul (prod_pos fun i _ => hposY i).ne'
          (prod_pos fun i _ => hposL i).ne']
      exact log_le_log (prod_pos fun i _ => hposP i) hle
    show ∑ i ∈ S, log (singularValues (Y * R (Fin.last (m + 1))) i) ≤ _
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.lastCases_last, Fin.lastCases_castSucc]
    linarith

/-- **Quantum Theorem M for multivariate product means (faithful states), any `z > 0`.** -/
theorem friedan_product_multi {m : ℕ} (ρ : Fin (m + 1) → Matrix d d ℂ) (hρ : ∀ j, (ρ j).PosDef)
    (hρ1 : ∀ j, (ρ j).trace = 1) (a : Fin (m + 1) → ℝ) (ha0 : ∀ j, 0 ≤ a j)
    (has : ∑ j, a j = 1) {z : ℝ} (hz : 0 < z) :
    let X := prodF m (fun j => cfc (fun x : ℝ => x ^ (a j / (2 * z))) (ρ j))
    let M := cfc (fun x : ℝ => x ^ z) (Xᴴ * X)
    (trace M).re ^ 2 * vN ((trace M).re⁻¹ • M) ≤ ∑ j, a j * vN (ρ j) := by
  intro X M
  set R : Fin (m + 1) → Matrix d d ℂ := fun j => cfc (fun x : ℝ => x ^ (a j / (2 * z))) (ρ j)
  have hRpd : ∀ j, (R j).PosDef := fun j => cfc_posDef (hρ j) (fun t ht => rpow_pos_of_pos ht _)
  have hRu : ∀ j, IsUnit (R j) := fun j => (hRpd j).isUnit
  have hXu : IsUnit X := prodF_isUnit m R hRu
  set N := Xᴴ * X
  have hNpd : N.PosDef := by
    have h := (Matrix.PosDef.one (n := d) (R := ℂ)).conjTranspose_mul_mul_same
      (B := X) (mulVec_injective_iff_isUnit.2 hXu)
    rwa [Matrix.mul_one] at h
  have hN : N.IsHermitian := hNpd.1
  set ν := hN.eigenvalues
  have hν : ∀ i, 0 < ν i := hNpd.eigenvalues_pos
  set p : Fin (m + 1) → d → ℝ := fun j => (hρ j).1.eigenvalues
  have hp : ∀ j i, 0 < p j i := fun j => (hρ j).eigenvalues_pos
  have hps : ∀ j, ∑ i, p j i = 1 := by
    intro j
    have h := congrArg Complex.re ((hρ j).1.trace_eq_sum_eigenvalues.symm.trans (hρ1 j))
    simpa [Complex.re_sum] using h
  have hsv : ∀ i, singularValues X i ^ 2 = ν i := fun i => sv_sq X hN i
  have hsvpos : ∀ i, 0 < singularValues X i := sv_pos_of_isUnit hXu
  set x : d → ℝ := fun i => z * log (ν i)
  have hx : ∀ i, exp (x i) = ν i ^ z := by
    intro i; simp only [x]; rw [rpow_def_of_pos (hν i), mul_comm]
  choose e he using fun j => sv_rpow (hρ j) (a j / (2 * z))
  have hW : ∀ S : Finset d, ∃ T : Fin (m + 1) → Finset d, (∀ j, (T j).card = S.card) ∧
      ∑ i ∈ S, x i ≤ ∑ j, a j * ∑ i ∈ T j, log (p j i) := by
    intro S
    obtain ⟨T, hT, hle⟩ := horn_log_multi m R hRu S
    refine ⟨fun j => (T j).map (e j).toEmbedding, fun j => by simp [hT j], ?_⟩
    have e1 : ∑ i ∈ S, x i = 2 * z * ∑ i ∈ S, log (singularValues X i) := by
      simp only [x, mul_sum]
      refine sum_congr rfl (fun i _ => ?_)
      rw [← hsv i, log_pow]; push_cast; ring
    have e2 : ∀ j, ∑ i ∈ T j, log (singularValues (R j) i) =
        a j / (2 * z) * ∑ i ∈ (T j).map (e j).toEmbedding, log (p j i) := by
      intro j
      rw [sum_map, mul_sum]
      refine sum_congr rfl (fun i _ => ?_)
      rw [he j, log_rpow (hp j _)]; rfl
    rw [Finset.sum_congr rfl (fun j _ => e2 j)] at hle
    rw [e1]
    have h2z : 0 < 2 * z := by positivity
    have := mul_le_mul_of_nonneg_left hle h2z.le
    have e3 : 2 * z * ∑ j, a j / (2 * z) * ∑ i ∈ (T j).map (e j).toEmbedding, log (p j i) =
        ∑ j, a j * ∑ i ∈ (T j).map (e j).toEmbedding, log (p j i) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun j _ => by field_simp)
    linarith
  have hQ := vecQM x p hp hps a ha0 has hW
  simp only [hx] at hQ
  have hMN : M = cfc (fun t : ℝ => t ^ z) N := rfl
  have hK : (trace M).re = ∑ i, ν i ^ z := by rw [hMN]; exact trace_cfc_re hN _
  rw [hK]
  set K := ∑ i, ν i ^ z
  have hZ : K⁻¹ • M = cfc (fun t : ℝ => K⁻¹ * t ^ z) N :=
    (cfc_const_mul K⁻¹ (fun t : ℝ => t ^ z) N (fin_cont _ _)).symm
  have hS : vN (K⁻¹ • M) = ∑ i, negMulLog (ν i ^ z / K) := by
    have hZh : (cfc (fun t : ℝ => K⁻¹ * t ^ z) N).IsHermitian := cfc_predicate _ _
    rw [hZ, vN, trace_cfc_re hZh]
    obtain ⟨e', he'⟩ := hN.cfc_eigenvalues (fun t : ℝ => K⁻¹ * t ^ z)
    rw [he']
    simp only [Function.comp_apply, inv_mul_eq_div]
    exact Equiv.sum_comp e' (fun i => negMulLog (ν i ^ z / K))
  rw [hS]
  have hR : ∀ j, vN (ρ j) = ∑ i, negMulLog (p j i) := fun j => by
    rw [vN, trace_cfc_re (hρ j).1]
  simp only [hR]
  exact hQ

end FriedanQ

end
