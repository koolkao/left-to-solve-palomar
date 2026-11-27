/-
Copyright 2026 Ming-Chih Kao. Licensed under the Apache License, Version 2.0;
see the LICENSE file at the root of this repository.
-/
module

public import FriedanQM.MatrixLEM
public import FriedanQ.Hamiltonian

/-! Port: copied from `quantum-lean/FriedanQM/HamiltonianM.lean` of github.com/koolkao/friedan-entropy-inequality (commit 0f4ba65dc126f59e7158fbcbc01548baa78cf21d, Lean v4.36.0, Mathlib fc4f59e, physlib edc607c) and put into the module system (`module` header, `public import`, public section). The proofs are unchanged unless a comment marked `Port` says otherwise. -/

@[expose] public section

/-!
# Friedan's inequality for `m` Hamiltonians

`H₁, …, H_m` Hermitian (not necessarily commuting), weights `a`, `H_a = ∑ⱼ aⱼ Hⱼ`,
`K = Z(H_a) / ∏ⱼ Z(Hⱼ)^{aⱼ}`: `K² S(H_a) ≤ ∑ⱼ aⱼ S(Hⱼ)`.
-/

open Real Finset Matrix
open scoped ComplexOrder

namespace FriedanQ

variable {d : Type*} [Fintype d] [DecidableEq d]

theorem friedan_hamiltonian_multi [Nonempty d] {m : ℕ} (H : Fin m → Matrix d d ℂ)
    (hH : ∀ j, (H j).IsHermitian) (a : Fin m → ℝ) (ha0 : ∀ j, 0 ≤ a j) (has : ∑ j, a j = 1) :
    (Zf (∑ j, a j • H j) / ∏ j, Zf (H j) ^ a j) ^ 2 * vN (gibbs (∑ j, a j • H j)) ≤
      ∑ j, a j * vN (gibbs (H j)) := by
  set Ha := ∑ j, a j • H j with hHadef
  have hHa : Ha.IsHermitian := herm_sum univ (fun j => a j • H j) (fun j => (hH j).smul_real _)
  have hL := friedan_LE_multi (fun j => gibbs (H j)) (fun j => gibbs_posDef (hH j))
    (fun j => gibbs_trace (hH j)) a ha0 has
  simp only [log_gibbs (hH _)] at hL
  set l : Fin m → ℝ := fun j => log (Zf (H j))
  set c := ∑ j, a j * l j
  have hX : ∑ j, a j • cfc (fun t => t - log (Zf (H j))) (-H j) = cfc (fun t => t - c) (-Ha) := by
    rw [cfc_sub_c hHa.neg]
    rw [Finset.sum_congr rfl (fun j _ => by rw [cfc_sub_c (hH j).neg])]
    simp only [smul_sub, smul_neg, Finset.sum_sub_distrib, Finset.sum_neg_distrib, smul_smul,
      ← Finset.sum_smul, hHadef, c, l]
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
  have hc : exp (-c) * Zf Ha = Zf Ha / ∏ j, Zf (H j) ^ a j := by
    have : ∏ j, Zf (H j) ^ a j = exp c := by
      rw [exp_sum]
      refine Finset.prod_congr rfl (fun j _ => ?_)
      rw [rpow_def_of_pos (Zf_pos (hH j)), mul_comm]
    rw [this, div_eq_mul_inv, ← exp_neg, mul_comm]
  rw [hc] at hL
  have hg : (Zf Ha)⁻¹ • cfc exp (-Ha) = gibbs Ha := rfl
  rw [hg] at hL
  exact hL

end FriedanQ

end
