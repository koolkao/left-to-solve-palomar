/-
Copyright 2026 Ming-Chih Kao. Licensed under the Apache License, Version 2.0;
see the LICENSE file at the root of this repository.
-/
module

public import FriedanQ
public import FriedanQM

/-!
# Solution

Proves the six declarations stated in `Challenge.lean` from the proof development (`FriedanQ`,
`FriedanQM`). The proofs are those of the source repository's statement checks
`quantum-lean/FriedanQ/Check.lean` (`friedan_question_check`, `alphaZ_psd_check`, `kuboAndo_check`) and
`quantum-lean/FriedanQM/Check.lean` (`hamiltonians_check`, `logEuclidean_check`, `product_check`),
under new names; the statements are unchanged.
-/

@[expose] public section

open Real Matrix
open scoped ComplexOrder

namespace FriedanQuantum

open FriedanQ

/-- `-tr(A log A)` equals the library's `vN A` for Hermitian `A`. -/
lemma vN_eq {d : Type*} [Fintype d] [DecidableEq d] {A : Matrix d d ℂ} (hA : A.IsHermitian) :
    vN A = -(trace (A * cfc log A)).re := by
  have h1 : A * cfc log A = cfc (fun x => x * log x) A :=
    (congrArg (· * cfc log A) (cfc_id' ℝ A hA).symm).trans
      (cfc_mul (fun x => x) log A (fin_cont _ _) (fin_cont _ _)).symm
  have h2 : cfc negMulLog A = -cfc (fun x => x * log x) A :=
    (cfc_congr (fun x _ => by simp [negMulLog])).trans (cfc_neg (fun x => x * log x) A)
  rw [vN, h1, h2, trace_neg, Complex.neg_re]

/-- The ordered product of `FriedanQ.prodF` is the list product `R 0 * R 1 * ⋯ * R m`. -/
lemma prodF_eq_prod {d : Type*} [Fintype d] [DecidableEq d] :
    ∀ (m : ℕ) (R : Fin (m + 1) → Matrix d d ℂ), prodF m R = (List.ofFn R).prod
  | 0, R => by simp [prodF]
  | m + 1, R => by
    rw [prodF, prodF_eq_prod m]
    conv_rhs => rw [List.ofFn_succ', List.concat_eq_append, List.prod_append, List.prod_singleton]

theorem friedan_question (n : ℕ) [NeZero n] (H₀ H₁ : Matrix (Fin n) (Fin n) ℂ)
    (h₀ : H₀.IsHermitian) (h₁ : H₁.IsHermitian) (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    let Z : Matrix (Fin n) (Fin n) ℂ → ℝ := fun H => (trace (cfc Real.exp (-H))).re
    let ρ : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ :=
      fun H => (Z H)⁻¹ • cfc Real.exp (-H)
    let S : Matrix (Fin n) (Fin n) ℂ → ℝ := fun H => -(trace (ρ H * cfc Real.log (ρ H))).re
    let Ha := (1 - a) • H₀ + a • H₁
    let K := Z Ha / (Z H₀ ^ (1 - a) * Z H₁ ^ a)
    K ^ 2 * S Ha ≤ (1 - a) * S H₀ + a * S H₁ := by
  intro Z ρ S Ha K
  have hHa : Ha.IsHermitian := (h₀.smul_real _).add (h₁.smul_real _)
  have hS : ∀ H : Matrix (Fin n) (Fin n) ℂ, H.IsHermitian → S H = vN (gibbs H) := by
    intro H hH
    rw [vN_eq (gibbs_posDef hH).1]
    rfl
  rw [hS Ha hHa, hS H₀ h₀, hS H₁ h₁]
  exact friedan_hamiltonian H₀ H₁ h₀ h₁ ha0 ha1

theorem alphaZ_psd {n : ℕ} (ρ σ : Matrix (Fin n) (Fin n) ℂ) (hρ : ρ.PosSemidef)
    (hσ : σ.PosSemidef) (hρ1 : ρ.trace = 1) (hσ1 : σ.trace = 1) (a z : ℝ) (ha0 : 0 ≤ a)
    (ha1 : a ≤ 1) (hz : 0 < z) :
    let M := cfc (fun x : ℝ => x ^ z)
      (cfc (fun x : ℝ => x ^ (a / (2 * z))) ρ * cfc (fun x : ℝ => x ^ ((1 - a) / z)) σ *
        cfc (fun x : ℝ => x ^ (a / (2 * z))) ρ)
    let S : Matrix (Fin n) (Fin n) ℂ → ℝ := fun A => -(trace (A * cfc Real.log A)).re
    let K := (trace M).re
    K ^ 2 * S (K⁻¹ • M) ≤ a * S ρ + (1 - a) * S σ := by
  intro M S K
  have hM0 : M.IsHermitian := cfc_predicate _ _
  have hM : (K⁻¹ • M).IsHermitian := hM0.smul_real _
  simp only [S]
  rw [← vN_eq hM, ← vN_eq hρ.1, ← vN_eq hσ.1]
  exact friedan_alphaZ_psd ρ σ hρ hσ hρ1 hσ1 ha0 ha1 hz

theorem kuboAndo {n : ℕ} (ρ σ : Matrix (Fin n) (Fin n) ℂ) (hρ : ρ.PosDef)
    (hσ : σ.PosDef) (hρ1 : ρ.trace = 1) (hσ1 : σ.trace = 1) (a : ℝ) (ha0 : 0 ≤ a)
    (ha1 : a ≤ 1) :
    let sq := cfc (fun x : ℝ => x ^ (1 / 2 : ℝ)) σ
    let isq := cfc (fun x : ℝ => x ^ (-(1 / 2) : ℝ)) σ
    let M := sq * cfc (fun x : ℝ => x ^ a) (isq * ρ * isq) * sq
    let S : Matrix (Fin n) (Fin n) ℂ → ℝ := fun A => -(trace (A * cfc Real.log A)).re
    let K := (trace M).re
    K ^ 2 * S (K⁻¹ • M) ≤ a * S ρ + (1 - a) * S σ := by
  intro sq isq M S K
  have hM : (K⁻¹ • M).IsHermitian := (kaM_posDef hσ hρ a).1.smul_real _
  simp only [S]
  rw [← vN_eq hM, ← vN_eq hρ.1, ← vN_eq hσ.1]
  exact friedan_KA ρ σ hρ hσ hρ1 hσ1 ha0 ha1

theorem hamiltonians_multi (n m : ℕ) [NeZero n] (H : Fin m → Matrix (Fin n) (Fin n) ℂ)
    (hH : ∀ j, (H j).IsHermitian) (a : Fin m → ℝ) (ha0 : ∀ j, 0 ≤ a j) (has : ∑ j, a j = 1) :
    let Z : Matrix (Fin n) (Fin n) ℂ → ℝ := fun H => (trace (cfc Real.exp (-H))).re
    let ρ : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ :=
      fun H => (Z H)⁻¹ • cfc Real.exp (-H)
    let S : Matrix (Fin n) (Fin n) ℂ → ℝ := fun H => -(trace (ρ H * cfc Real.log (ρ H))).re
    let Ha := ∑ j, a j • H j
    let K := Z Ha / ∏ j, Z (H j) ^ a j
    K ^ 2 * S Ha ≤ ∑ j, a j * S (H j) := by
  intro Z ρ S Ha K
  have hHa : Ha.IsHermitian :=
    herm_sum Finset.univ (fun j => a j • H j) (fun j => (hH j).smul_real _)
  have hS : ∀ H : Matrix (Fin n) (Fin n) ℂ, H.IsHermitian → S H = vN (gibbs H) := by
    intro H hH
    rw [vN_eq (gibbs_posDef hH).1]
    rfl
  rw [hS Ha hHa]
  simp only [hS _ (hH _)]
  exact friedan_hamiltonian_multi H hH a ha0 has

theorem logEuclidean_multi (n m : ℕ) (ρ : Fin m → Matrix (Fin n) (Fin n) ℂ)
    (hρ : ∀ j, (ρ j).PosDef) (hρ1 : ∀ j, (ρ j).trace = 1) (a : Fin m → ℝ) (ha0 : ∀ j, 0 ≤ a j)
    (has : ∑ j, a j = 1) :
    let M := cfc Real.exp (∑ j, a j • cfc Real.log (ρ j))
    let S : Matrix (Fin n) (Fin n) ℂ → ℝ := fun A => -(trace (A * cfc Real.log A)).re
    let K := (trace M).re
    K ^ 2 * S (K⁻¹ • M) ≤ ∑ j, a j * S (ρ j) := by
  intro M S K
  have hM0 : M.IsHermitian := cfc_predicate _ _
  have hM : (K⁻¹ • M).IsHermitian := hM0.smul_real _
  simp only [S]
  rw [← vN_eq hM]
  simp only [← vN_eq (hρ _).1]
  exact friedan_LE_multi ρ hρ hρ1 a ha0 has

theorem product_multi (n m : ℕ) (ρ : Fin (m + 1) → Matrix (Fin n) (Fin n) ℂ)
    (hρ : ∀ j, (ρ j).PosDef) (hρ1 : ∀ j, (ρ j).trace = 1) (a : Fin (m + 1) → ℝ)
    (ha0 : ∀ j, 0 ≤ a j) (has : ∑ j, a j = 1) (z : ℝ) (hz : 0 < z) :
    let X := (List.ofFn fun j => cfc (fun x : ℝ => x ^ (a j / (2 * z))) (ρ j)).prod
    let M := cfc (fun x : ℝ => x ^ z) (Xᴴ * X)
    let S : Matrix (Fin n) (Fin n) ℂ → ℝ := fun A => -(trace (A * cfc Real.log A)).re
    let K := (trace M).re
    K ^ 2 * S (K⁻¹ • M) ≤ ∑ j, a j * S (ρ j) := by
  intro X M S K
  have hM0 : M.IsHermitian := cfc_predicate _ _
  have hM : (K⁻¹ • M).IsHermitian := hM0.smul_real _
  simp only [S]
  rw [← vN_eq hM]
  simp only [← vN_eq (hρ _).1]
  have h := friedan_product_multi ρ hρ hρ1 a ha0 has hz
  dsimp only at h
  rw [prodF_eq_prod] at h
  exact h

end FriedanQuantum
