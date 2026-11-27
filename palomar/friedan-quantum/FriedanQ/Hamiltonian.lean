/-
Copyright 2026 Ming-Chih Kao. Licensed under the Apache License, Version 2.0;
see the LICENSE file at the root of this repository.
-/
module

public import FriedanQ.MatrixLE

/-! Port: copied from `quantum-lean/FriedanQ/Hamiltonian.lean` of github.com/koolkao/friedan-entropy-inequality (commit 0f4ba65dc126f59e7158fbcbc01548baa78cf21d, Lean v4.36.0, Mathlib fc4f59e, physlib edc607c) and put into the module system (`module` header, `public import`, public section). The proofs are unchanged unless a comment marked `Port` says otherwise. -/

@[expose] public section

/-!
# Friedan's question in his own (Hamiltonian) form

MO 138395: `H₀, H₁` Hermitian, `Z(H) = tr e^{-H}`, `ρ_H = e^{-H}/Z(H)`, `S(H) = -tr ρ_H log ρ_H`,
`H_a = (1-a) H₀ + a H₁`, `K = Z(H_a) / (Z(H₀)^{1-a} Z(H₁)^a)`. Then
`(1-a) S(H₀) + a S(H₁) ≥ K² S(H_a)`, with no commutation assumption.
-/

open Real Finset Matrix
open scoped ComplexOrder

namespace FriedanQ

variable {d : Type*} [Fintype d] [DecidableEq d]

/-- partition function `Z(H) = tr e^{-H}` -/
noncomputable def Zf (H : Matrix d d ℂ) : ℝ := (trace (cfc exp (-H))).re
/-- Gibbs state `ρ_H = e^{-H} / Z(H)` -/
noncomputable def gibbs (H : Matrix d d ℂ) : Matrix d d ℂ := (Zf H)⁻¹ • cfc exp (-H)

lemma fin_cont (X : Matrix d d ℂ) (f : ℝ → ℝ) : ContinuousOn f (spectrum ℝ X) :=
  (Matrix.finite_real_spectrum (A := X)).continuousOn f

lemma Zf_pos [Nonempty d] {H : Matrix d d ℂ} (hH : H.IsHermitian) : 0 < Zf H := by
  rw [Zf, trace_cfc_re hH.neg]
  exact sum_pos (fun i _ => exp_pos _) univ_nonempty

lemma gibbs_eq {H : Matrix d d ℂ} : gibbs H = cfc (fun t => (Zf H)⁻¹ * exp t) (-H) :=
  (cfc_const_mul _ exp (-H) (fin_cont _ _)).symm

lemma gibbs_posDef [Nonempty d] {H : Matrix d d ℂ} (hH : H.IsHermitian) : (gibbs H).PosDef := by
  have hZ := Zf_pos hH
  rw [gibbs_eq]
  have hh : (cfc (fun t => (Zf H)⁻¹ * exp t) (-H)).IsHermitian := cfc_predicate _ _
  rw [hh.posDef_iff_eigenvalues_pos]
  obtain ⟨e, he⟩ := hH.neg.cfc_eigenvalues (fun t => (Zf H)⁻¹ * exp t)
  intro i
  rw [he]
  exact mul_pos (inv_pos.2 hZ) (exp_pos _)

lemma gibbs_trace [Nonempty d] {H : Matrix d d ℂ} (hH : H.IsHermitian) : (gibbs H).trace = 1 := by
  have hZ := Zf_pos hH
  have hh : (cfc exp (-H)).IsHermitian := cfc_predicate _ _
  have hre : (trace (cfc exp (-H))) = ((Zf H : ℝ) : ℂ) := by
    rw [hh.trace_eq_sum_eigenvalues, Zf, hh.trace_eq_sum_eigenvalues]
    simp [Complex.re_sum, Complex.ofReal_sum]
  rw [gibbs, trace_smul, hre, Complex.real_smul, ← Complex.ofReal_mul, inv_mul_cancel₀ hZ.ne',
    Complex.ofReal_one]

/-- `log ρ_H = -H - log Z(H)` -/
lemma log_gibbs [Nonempty d] {H : Matrix d d ℂ} (hH : H.IsHermitian) :
    cfc log (gibbs H) = cfc (fun t => t - log (Zf H)) (-H) := by
  have hZ := Zf_pos hH
  rw [gibbs_eq]
  refine (cfc_comp log (fun t => (Zf H)⁻¹ * exp t) (-H) hH.neg (fin_cont' _ _)
    (fin_cont _ _)).symm.trans ?_
  · apply cfc_congr
    intro t _
    simp only [Function.comp_apply]
    rw [log_mul (inv_pos.2 hZ).ne' (exp_pos t).ne', log_exp, log_inv]
    ring
where
  fin_cont' (g : ℝ → ℝ) (s : ℝ → ℝ) : ContinuousOn g (s '' spectrum ℝ (-H)) :=
    ((Matrix.finite_real_spectrum (A := -H)).image s).continuousOn g

lemma cfc_sub_c {X : Matrix d d ℂ} (hX : X.IsHermitian) (l : ℝ) :
    cfc (fun t => t - l) X = X - l • (1 : Matrix d d ℂ) := by
  refine (cfc_sub (fun t => t) (fun _ => l) X (fin_cont _ _) (fin_cont _ _)).trans ?_
  exact congrArg₂ (fun A B => A - B) (cfc_id' ℝ X hX)
    ((cfc_const l X hX).trans (Algebra.algebraMap_eq_smul_one l))

/-- **Friedan's question (MO 138395), quantum case: YES.** For Hermitian `H₀, H₁` (not
necessarily commuting) and `0 ≤ a ≤ 1`, with `H_a = (1-a) H₀ + a H₁` and
`K = Z(H_a) / (Z(H₀)^{1-a} Z(H₁)^a)`: `K² S(H_a) ≤ (1-a) S(H₀) + a S(H₁)`. -/
theorem friedan_hamiltonian [Nonempty d] (H₀ H₁ : Matrix d d ℂ) (h₀ : H₀.IsHermitian)
    (h₁ : H₁.IsHermitian) {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    (Zf ((1 - a) • H₀ + a • H₁) / (Zf H₀ ^ (1 - a) * Zf H₁ ^ a)) ^ 2 *
        vN (gibbs ((1 - a) • H₀ + a • H₁)) ≤
      (1 - a) * vN (gibbs H₀) + a * vN (gibbs H₁) := by
  set Ha := (1 - a) • H₀ + a • H₁ with hHadef
  have hHa : Ha.IsHermitian := (h₀.smul_real _).add (h₁.smul_real _)
  have hL := friedan_LE (gibbs H₁) (gibbs H₀) (gibbs_posDef h₁) (gibbs_posDef h₀)
    (gibbs_trace h₁) (gibbs_trace h₀) ha0 ha1
  rw [log_gibbs h₁, log_gibbs h₀] at hL
  set l₁ := log (Zf H₁)
  set l₀ := log (Zf H₀)
  set c := a * l₁ + (1 - a) * l₀
  have hX : a • cfc (fun t => t - l₁) (-H₁) + (1 - a) • cfc (fun t => t - l₀) (-H₀) =
      cfc (fun t => t - c) (-Ha) := by
    rw [cfc_sub_c h₁.neg, cfc_sub_c h₀.neg, cfc_sub_c hHa.neg, hHadef]
    simp only [c]
    module
  rw [hX] at hL
  have hM : cfc exp (cfc (fun t => t - c) (-Ha)) = exp (-c) • cfc exp (-Ha) := by
    refine (cfc_comp exp (fun t => t - c) (-Ha) hHa.neg
      (((Matrix.finite_real_spectrum (A := -Ha)).image _).continuousOn _)
      (fin_cont _ _)).symm.trans ?_
    refine (cfc_congr (fun t _ => ?_)).trans (cfc_const_mul (exp (-c)) exp (-Ha) (fin_cont _ _))
    simp only [Function.comp_apply]
    rw [sub_eq_add_neg, exp_add, mul_comm]
  rw [hM] at hL
  have hZa := Zf_pos hHa
  have hK : (trace (exp (-c) • cfc exp (-Ha))).re = exp (-c) * Zf Ha := by
    rw [trace_smul, Complex.smul_re, smul_eq_mul, Zf]
  rw [hK, smul_smul, mul_inv, mul_assoc] at hL
  have e : (exp (-c))⁻¹ * ((Zf Ha)⁻¹ * exp (-c)) = (Zf Ha)⁻¹ := by
    have := (exp_pos (-c)).ne'; field_simp
  rw [e] at hL
  have hc : exp (-c) * Zf Ha = Zf Ha / (Zf H₀ ^ (1 - a) * Zf H₁ ^ a) := by
    rw [rpow_def_of_pos (Zf_pos h₀), rpow_def_of_pos (Zf_pos h₁), ← exp_add, div_eq_mul_inv,
      ← exp_neg, mul_comm (Zf Ha)]
    congr 2
    simp only [c, l₀, l₁]; ring
  rw [hc] at hL
  have hg : (Zf Ha)⁻¹ • cfc exp (-Ha) = gibbs Ha := rfl
  rw [hg] at hL
  linarith

end FriedanQ

end
