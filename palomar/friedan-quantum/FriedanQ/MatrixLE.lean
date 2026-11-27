/-
Copyright 2026 Ming-Chih Kao. Licensed under the Apache License, Version 2.0;
see the LICENSE file at the root of this repository.
-/
module

public import FriedanQ.VecQ
public import FriedanQ.Vendor.KyFan
public import QuantumInfo.ForMathlib.Matrix

/-! Port: copied from `quantum-lean/FriedanQ/MatrixLE.lean` of github.com/koolkao/friedan-entropy-inequality (commit 0f4ba65dc126f59e7158fbcbc01548baa78cf21d, Lean v4.36.0, Mathlib fc4f59e, physlib edc607c) and put into the module system (`module` header, `public import`, public section). The proofs are unchanged unless a comment marked `Port` says otherwise. -/

@[expose] public section

/-!
# Friedan's quantum inequality, log-Euclidean (Friedan's own) version

For faithful density matrices `ρ, σ` and `0 ≤ a ≤ 1`, with `M = exp(a log ρ + (1-a) log σ)`,
`K = tr M`: `K² S(M/K) ≤ a S(ρ) + (1-a) S(σ)`, `S(A) = -tr A log A`.

Reused: Ky Fan's inequality (atlas-lean, vendored in `Vendor/KyFan.lean`) and
`Matrix.IsHermitian.cfc_eigenvalues` (physlib, `QuantumInfo.ForMathlib.Matrix`, Apache-2.0).
-/

open Real Finset Matrix
open scoped ComplexOrder

namespace FriedanQ

variable {d : Type*} [Fintype d] [DecidableEq d]

/-- von Neumann entropy `S(A) = -tr (A log A)` (real part), via the real functional calculus. -/
noncomputable def vN (A : Matrix d d ℂ) : ℝ := (trace (cfc negMulLog A)).re

lemma trace_cfc_re {A : Matrix d d ℂ} (hA : A.IsHermitian) (f : ℝ → ℝ) :
    (trace (cfc f A)).re = ∑ i, f (hA.eigenvalues i) := by
  obtain ⟨e, he⟩ := hA.cfc_eigenvalues f
  have hf : (cfc f A).IsHermitian := cfc_predicate f A
  rw [hf.trace_eq_sum_eigenvalues, he]
  simp only [Function.comp_apply, Complex.re_sum, Complex.ofReal_re]
  exact Equiv.sum_comp e (fun i => f (hA.eigenvalues i))

/-- Sums of eigenvalues of `cfc g A` over a set are sums of `g ∘ eig A` over a set of equal size. -/
lemma sum_eig_cfc {A : Matrix d d ℂ} (hA : A.IsHermitian) (g : ℝ → ℝ) (T : Finset d) :
    ∃ T' : Finset d, T'.card = T.card ∧
      ∑ i ∈ T, Matrix.IsHermitian.eigenvalues (A := cfc g A) (cfc_predicate g A) i =
        ∑ i ∈ T', g (hA.eigenvalues i) := by
  obtain ⟨e, he⟩ := hA.cfc_eigenvalues g
  refine ⟨T.map e.toEmbedding, by simp, ?_⟩
  rw [sum_map, he]
  rfl

/-- `eigenvalues ∘ e = eigenvalues₀` for Mathlib's reindexing equiv. -/
lemma eig_e {A : Matrix d d ℂ} (hA : A.IsHermitian) (i : Fin (Fintype.card d)) :
    hA.eigenvalues ((Fintype.equivOfCardEq (Fintype.card_fin _)) i) = hA.eigenvalues₀ i := by
  simp [Matrix.IsHermitian.eigenvalues]

lemma prefSum_eq {A : Matrix d d ℂ} (hA : A.IsHermitian) {k : ℕ} (hk : k ≤ Fintype.card d) :
    MathlibExt.Analysis.InnerProductSpace.KyFanWanted.eigPrefSum hA.eigenvalues₀ k hk =
      ∑ i ∈ range k, ext (Fintype.equivOfCardEq (Fintype.card_fin _)) hA.eigenvalues i := by
  rw [MathlibExt.Analysis.InnerProductSpace.KyFanWanted.eigPrefSum]
  refine sum_congr rfl (fun i hi => ?_)
  have hi' := mem_range.1 hi
  rw [dif_pos hi', ext_lt _ _ (by omega), eig_e]
  rfl

/-- **Ky Fan, sorting-free form.** -/
lemma kyfan_subset {A B : Matrix d d ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian)
    (S : Finset d) : ∃ T U : Finset d, T.card = S.card ∧ U.card = S.card ∧
      ∑ i ∈ S, (hA.add hB).eigenvalues i ≤
        ∑ i ∈ T, hA.eigenvalues i + ∑ i ∈ U, hB.eigenvalues i := by
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
  refine ⟨P, P, hP, hP, ?_⟩
  have h1 : ∑ i ∈ S, (hA.add hB).eigenvalues i ≤
      ∑ i ∈ range k, ext e (hA.add hB).eigenvalues i := by
    have h := sum_toNat e (hA.add hB).eigenvalues id S
    simp only [id] at h
    rw [h]
    have := sum_subset_le_prefix _ (anti (hA.add hB)) _ (toNat_sub e S)
    rwa [toNat_card] at this
  have h2 := MathlibExt.Analysis.InnerProductSpace.KyFanWanted.ky_fan_eigenvalues₀ A B hA hB k hk
  rw [prefSum_eq, prefSum_eq, prefSum_eq] at h2
  rw [hPs, hPs]
  linarith

/-- **Friedan's quantum inequality, log-Euclidean version (faithful states).** -/
theorem friedan_LE (ρ σ : Matrix d d ℂ) (hρ : ρ.PosDef) (hσ : σ.PosDef)
    (hρ1 : ρ.trace = 1) (hσ1 : σ.trace = 1) {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    (trace (cfc exp (a • cfc log ρ + (1 - a) • cfc log σ))).re ^ 2 *
        vN ((trace (cfc exp (a • cfc log ρ + (1 - a) • cfc log σ))).re⁻¹ •
          cfc exp (a • cfc log ρ + (1 - a) • cfc log σ)) ≤
      a * vN ρ + (1 - a) * vN σ := by
  have hHρ : ρ.IsHermitian := hρ.1
  have hHσ : σ.IsHermitian := hσ.1
  have hfin : ∀ (X : Matrix d d ℂ) (f : ℝ → ℝ), ContinuousOn f (spectrum ℝ X) :=
    fun X f => (Matrix.finite_real_spectrum (A := X)).continuousOn f
  -- `H = A₁ + B₁` with `A₁ = cfc (a log) ρ`, `B₁ = cfc ((1-a) log) σ`
  have hA1 : a • cfc log ρ = cfc (fun x => a * log x) ρ :=
    (cfc_const_mul a log ρ (hfin ρ log)).symm
  have hB1 : (1 - a) • cfc log σ = cfc (fun x => (1 - a) * log x) σ :=
    (cfc_const_mul (1 - a) log σ (hfin σ log)).symm
  rw [hA1, hB1]
  set A1 := cfc (fun x => a * log x) ρ
  set B1 := cfc (fun x => (1 - a) * log x) σ
  have hA : A1.IsHermitian := cfc_predicate _ ρ
  have hB : B1.IsHermitian := cfc_predicate _ σ
  have hH : (A1 + B1).IsHermitian := hA.add hB
  set x := hH.eigenvalues
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
  have hW : ∀ S : Finset d, ∃ T U : Finset d, T.card = S.card ∧ U.card = S.card ∧
      ∑ i ∈ S, x i ≤ a * ∑ i ∈ T, log (p i) + (1 - a) * ∑ i ∈ U, log (q i) := by
    intro S
    obtain ⟨T0, U0, hT0, hU0, hle⟩ := kyfan_subset hA hB S
    obtain ⟨T, hT, hTs⟩ := sum_eig_cfc hHρ (fun x => a * log x) T0
    obtain ⟨U, hU, hUs⟩ := sum_eig_cfc hHσ (fun x => (1 - a) * log x) U0
    refine ⟨T, U, hT.trans hT0, hU.trans hU0, ?_⟩
    rw [mul_sum, mul_sum, ← hTs, ← hUs]
    exact hle
  have hQ := vecQ x p q hp hq hps hqs ha0 ha1 hW
  -- identify both sides
  have hK : (trace (cfc exp (A1 + B1))).re = ∑ i, exp (x i) := trace_cfc_re hH exp
  rw [hK]
  set K := ∑ i, exp (x i)
  have hZ : K⁻¹ • cfc exp (A1 + B1) = cfc (fun t => K⁻¹ * exp t) (A1 + B1) :=
    (cfc_const_mul K⁻¹ exp (A1 + B1) (hfin _ exp)).symm
  have hS : vN (K⁻¹ • cfc exp (A1 + B1)) = ∑ i, negMulLog (exp (x i) / K) := by
    have hZh : (cfc (fun t => K⁻¹ * exp t) (A1 + B1)).IsHermitian := cfc_predicate _ _
    rw [hZ, vN, trace_cfc_re hZh]
    obtain ⟨e, he⟩ := hH.cfc_eigenvalues (fun t => K⁻¹ * exp t)
    rw [he]
    simp only [Function.comp_apply, inv_mul_eq_div]
    exact Equiv.sum_comp e (fun i => negMulLog (exp (x i) / K))
  rw [hS, vN, vN, trace_cfc_re hHρ, trace_cfc_re hHσ]
  exact hQ

end FriedanQ

end
