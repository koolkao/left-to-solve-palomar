/-
Copyright 2026 Ming-Chih Kao. Licensed under the Apache License, Version 2.0;
see the LICENSE file at the root of this repository.
-/
module

public import FriedanQM.VecQM
public import FriedanQ.MatrixLE

/-! Port: copied from `quantum-lean/FriedanQM/MatrixLEM.lean` of github.com/koolkao/friedan-entropy-inequality (commit 0f4ba65dc126f59e7158fbcbc01548baa78cf21d, Lean v4.36.0, Mathlib fc4f59e, physlib edc607c) and put into the module system (`module` header, `public import`, public section). The proofs are unchanged unless a comment marked `Port` says otherwise. -/

@[expose] public section

/-!
# Quantum Theorem M, log-Euclidean version: `m` density matrices

For faithful density matrices `ρ₁, …, ρ_m` and weights `a` (`aⱼ ≥ 0`, `∑ aⱼ = 1`), with
`M = exp(∑ⱼ aⱼ log ρⱼ)` and `K = tr M`: `K² S(M/K) ≤ ∑ⱼ aⱼ S(ρⱼ)`.
Ky Fan for `m` Hermitian summands (`kyfan_pref_multi`, by induction from the vendored two-term
`ky_fan_eigenvalues₀`), then `vecQM`.
-/

open Real Finset Matrix
open scoped ComplexOrder

namespace FriedanQ

open MathlibExt.Analysis.InnerProductSpace.KyFanWanted

variable {d : Type*} [Fintype d] [DecidableEq d]

lemma herm_sum {ι : Type*} (s : Finset ι) (A : ι → Matrix d d ℂ) (hA : ∀ j, (A j).IsHermitian) :
    (∑ j ∈ s, A j).IsHermitian := by
  unfold Matrix.IsHermitian
  rw [Matrix.conjTranspose_sum]
  exact Finset.sum_congr rfl (fun j _ => hA j)

lemma eig₀_congr {A B : Matrix d d ℂ} (h : A = B) (hA : A.IsHermitian) (hB : B.IsHermitian) :
    hA.eigenvalues₀ = hB.eigenvalues₀ := by subst h; rfl

/-- **Ky Fan for `m` summands** (prefix sums of sorted eigenvalues). -/
lemma kyfan_pref_multi {ι : Type*} [DecidableEq ι] (A : ι → Matrix d d ℂ)
    (hA : ∀ j, (A j).IsHermitian) (k : ℕ) (hk : k ≤ Fintype.card d) :
    ∀ s : Finset ι, eigPrefSum (herm_sum s A hA).eigenvalues₀ k hk ≤
      ∑ j ∈ s, eigPrefSum (hA j).eigenvalues₀ k hk := by
  intro s
  induction s using Finset.induction_on with
  | empty =>
    have h0 : (herm_sum ∅ A hA).eigenvalues = 0 :=
      (herm_sum ∅ A hA).eigenvalues_eq_zero_iff.2 (Finset.sum_empty)
    have h0' : (herm_sum ∅ A hA).eigenvalues₀ = 0 := by
      funext i
      rw [← eig_e]
      exact congrFun h0 _
    rw [h0']
    simp [eigPrefSum]
  | insert j0 s hj0 IH =>
    have hsum : ∑ j ∈ insert j0 s, A j = A j0 + ∑ j ∈ s, A j := Finset.sum_insert hj0
    rw [eig₀_congr hsum _ ((hA j0).add (herm_sum s A hA)), Finset.sum_insert hj0]
    have := ky_fan_eigenvalues₀ (A j0) (∑ j ∈ s, A j) (hA j0) (herm_sum s A hA) k hk
    linarith

/-- **Ky Fan for `m` summands, sorting-free form**: one prefix set works for all summands. -/
lemma kyfan_subset_multi {m : ℕ} (A : Fin m → Matrix d d ℂ) (hA : ∀ j, (A j).IsHermitian)
    (S : Finset d) : ∃ P : Finset d, P.card = S.card ∧
      ∑ i ∈ S, (herm_sum univ A hA).eigenvalues i ≤ ∑ j, ∑ i ∈ P, (hA j).eigenvalues i := by
  set e : Fin (Fintype.card d) ≃ d := Fintype.equivOfCardEq (Fintype.card_fin _)
  set k := S.card
  have hk : k ≤ Fintype.card d := card_le_univ S
  have anti : ∀ {X : Matrix d d ℂ} (hX : X.IsHermitian),
      ∀ i j, i ≤ j → j < Fintype.card d → ext e hX.eigenvalues j ≤ ext e hX.eigenvalues i := by
    intro X hX i j hij hj
    rw [ext_lt e _ hj, ext_lt e _ (by omega), eig_e, eig_e]
    exact hX.eigenvalues₀_antitone (show (⟨i, by omega⟩ : Fin _) ≤ ⟨j, hj⟩ from hij)
  set P := (univ.filter (fun i : Fin (Fintype.card d) => i.val < k)).map e.toEmbedding
  have hP : P.card = k := by simp only [P, card_map]; rw [Fin.card_filter_val_lt]; omega
  have hPs : ∀ {X : Matrix d d ℂ} (hX : X.IsHermitian),
      ∑ i ∈ P, hX.eigenvalues i = ∑ i ∈ range k, ext e hX.eigenvalues i := by
    intro X hX
    have h := sum_toNat e hX.eigenvalues id P
    simp only [id] at h
    rw [h, toNat_prefix e hk]
  refine ⟨P, hP, ?_⟩
  have h1 : ∑ i ∈ S, (herm_sum univ A hA).eigenvalues i ≤
      ∑ i ∈ range k, ext e (herm_sum univ A hA).eigenvalues i := by
    have h := sum_toNat e (herm_sum univ A hA).eigenvalues id S
    simp only [id] at h
    rw [h]
    have := sum_subset_le_prefix _ (anti (herm_sum univ A hA)) _ (toNat_sub e S)
    rwa [toNat_card] at this
  have h2 := kyfan_pref_multi A hA k hk univ
  rw [prefSum_eq] at h2
  rw [Finset.sum_congr rfl (fun j _ => prefSum_eq (hA j) hk)] at h2
  rw [Finset.sum_congr rfl (fun j _ => hPs (hA j))]
  linarith

/-- **Quantum Theorem M, log-Euclidean version (faithful states).** -/
theorem friedan_LE_multi {m : ℕ} (ρ : Fin m → Matrix d d ℂ) (hρ : ∀ j, (ρ j).PosDef)
    (hρ1 : ∀ j, (ρ j).trace = 1) (a : Fin m → ℝ) (ha0 : ∀ j, 0 ≤ a j) (has : ∑ j, a j = 1) :
    (trace (cfc exp (∑ j, a j • cfc log (ρ j)))).re ^ 2 *
        vN ((trace (cfc exp (∑ j, a j • cfc log (ρ j)))).re⁻¹ •
          cfc exp (∑ j, a j • cfc log (ρ j))) ≤
      ∑ j, a j * vN (ρ j) := by
  have hfin : ∀ (X : Matrix d d ℂ) (f : ℝ → ℝ), ContinuousOn f (spectrum ℝ X) :=
    fun X f => (Matrix.finite_real_spectrum (A := X)).continuousOn f
  have hA1 : ∑ j, a j • cfc log (ρ j) = ∑ j, cfc (fun x => a j * log x) (ρ j) :=
    Finset.sum_congr rfl (fun j _ => (cfc_const_mul (a j) log (ρ j) (hfin (ρ j) log)).symm)
  rw [hA1]
  set A : Fin m → Matrix d d ℂ := fun j => cfc (fun x => a j * log x) (ρ j) with hAdef
  have hA : ∀ j, (A j).IsHermitian := fun j => cfc_predicate _ (ρ j)
  have hH : (∑ j, A j).IsHermitian := herm_sum univ A hA
  set x := hH.eigenvalues
  set p : Fin m → d → ℝ := fun j => (hρ j).1.eigenvalues
  have hp : ∀ j i, 0 < p j i := fun j => (hρ j).eigenvalues_pos
  have hps : ∀ j, ∑ i, p j i = 1 := by
    intro j
    have h := congrArg Complex.re ((hρ j).1.trace_eq_sum_eigenvalues.symm.trans (hρ1 j))
    simpa [Complex.re_sum] using h
  have hW : ∀ S : Finset d, ∃ T : Fin m → Finset d, (∀ j, (T j).card = S.card) ∧
      ∑ i ∈ S, x i ≤ ∑ j, a j * ∑ i ∈ T j, log (p j i) := by
    intro S
    obtain ⟨P, hP, hle⟩ := kyfan_subset_multi A hA S
    choose T hT hTs using fun j => sum_eig_cfc (hρ j).1 (fun x => a j * log x) P
    refine ⟨T, fun j => (hT j).trans hP, ?_⟩
    have e : ∀ j, a j * ∑ i ∈ T j, log (p j i) = ∑ i ∈ P, (hA j).eigenvalues i := by
      intro j; rw [mul_sum, hTs j]
    rw [Finset.sum_congr rfl (fun j _ => e j)]
    exact hle
  have hQ := vecQM x p hp hps a ha0 has hW
  have hK : (trace (cfc exp (∑ j, A j))).re = ∑ i, exp (x i) := trace_cfc_re hH exp
  rw [hK]
  set K := ∑ i, exp (x i)
  have hZ : K⁻¹ • cfc exp (∑ j, A j) = cfc (fun t => K⁻¹ * exp t) (∑ j, A j) :=
    (cfc_const_mul K⁻¹ exp (∑ j, A j) (hfin _ exp)).symm
  have hS : vN (K⁻¹ • cfc exp (∑ j, A j)) = ∑ i, negMulLog (exp (x i) / K) := by
    have hZh : (cfc (fun t => K⁻¹ * exp t) (∑ j, A j)).IsHermitian := cfc_predicate _ _
    rw [hZ, vN, trace_cfc_re hZh]
    obtain ⟨e, he⟩ := hH.cfc_eigenvalues (fun t => K⁻¹ * exp t)
    rw [he]
    simp only [Function.comp_apply, inv_mul_eq_div]
    exact Equiv.sum_comp e (fun i => negMulLog (exp (x i) / K))
  rw [hS]
  have hR : ∀ j, vN (ρ j) = ∑ i, negMulLog (p j i) := fun j => by
    rw [vN, trace_cfc_re (hρ j).1]
  simp only [hR]
  exact hQ

end FriedanQ

end
