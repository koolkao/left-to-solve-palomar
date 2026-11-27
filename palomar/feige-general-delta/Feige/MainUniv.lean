/-
Copyright 2026 Ming-Chih Kao. Licensed under the Apache License, Version 2.0;
see the LICENSE file at the root of this repository.
-/
module

public import Feige.Main

/-! Added for this Palomar entry (not in the source repository): `main` with the sample space in
an arbitrary universe (`Ω : Type*` instead of `Ω : Type`) and the hypotheses as named binders. The
proof is the proof of `main` in `Feige/Main.lean`, copied unchanged. -/

@[expose] public section

namespace OMA.S_opg_sums_of_independent_random_variables_with_unbounded_variance

open MeasureTheory ProbabilityTheory

theorem main_univ {n : ℕ} {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    (X : Fin n → Ω → ℝ) (μ δ : ℝ) (hμ : 0 < μ) (hδ : 0 < δ) (hind : iIndepFun X ℙ)
    (hnn : ∀ i ω, 0 ≤ X i ω) (hint : ∀ i, Integrable (X i)) (hmean : ∀ i, 𝔼[X i] ≤ μ) :
    min (δ / (1 + δ)) (Real.exp (-1)) ≤
      (ℙ {ω | ∑ i, X i ω - 𝔼[fun ω' => ∑ i, X i ω'] < δ * μ}).toReal := by
  set m : Fin n → ℝ := fun i => ∫ ω, X i ω with hm
  let g : Fin n → ℝ → ℝ := fun i x => (x + (μ - m i)) / μ
  have hg : ∀ i, Measurable (g i) := fun i => by fun_prop
  let Y : Fin n → Ω → ℝ := fun i ω => g i (X i ω)
  have hindY : iIndepFun Y ℙ := hind.comp g hg
  have haeX : ∀ i, AEMeasurable (X i) ℙ := fun i => (hint i).aemeasurable
  have haeY : ∀ i, AEMeasurable (Y i) ℙ := fun i => (hg i).comp_aemeasurable (haeX i)
  have hYnn : ∀ i ω, 0 ≤ Y i ω := fun i ω => by
    have := hmean i
    exact div_nonneg (by linarith [hnn i ω]) hμ.le
  have hintY : ∀ i, Integrable (Y i) ℙ := fun i =>
    ((hint i).add (integrable_const (μ - m i))).div_const μ
  have hmeanY : ∀ i, ∫ ω, Y i ω = 1 := fun i => by
    simp only [Y, g]
    rw [integral_div, integral_add (hint i) (integrable_const _), integral_const]
    simp [m, hμ.ne']
  -- marginals
  let ν : Fin n → Measure ℝ := fun i => (ℙ : Measure Ω).map (Y i)
  have : ∀ i, IsProbabilityMeasure (ν i) := fun i =>
    (Measure.isProbabilityMeasure_map_iff (haeY i)).mpr inferInstance
  have hνint : ∀ i, Integrable (fun x : ℝ => x) (ν i) := fun i => by
    exact (integrable_map_measure (g := id) aestronglyMeasurable_id (haeY i)).mpr (hintY i)
  have hνmean : ∀ i, ∫ x, x ∂(ν i) = 1 := fun i => by
    exact (integral_map (φ := Y i) (f := id) (haeY i) aestronglyMeasurable_id).trans (hmeanY i)
  have hνsupp : ∀ i, ν i (Set.Iio 0) = 0 := fun i => by
    rw [Measure.map_apply_of_aemeasurable (haeY i) measurableSet_Iio]
    have : Y i ⁻¹' Set.Iio 0 = ∅ := by
      ext ω; simp only [Set.mem_preimage, Set.mem_Iio, Set.mem_empty_iff_false, iff_false, not_lt]
      exact hYnn i ω
    rw [this, measure_empty]
  have hjoint : (ℙ : Measure Ω).map (fun ω i => Y i ω) = Measure.pi ν :=
    (iIndepFun_iff_map_fun_eq_pi_map haeY).mp hindY
  have hbound := Samuels.pi_meanOne_bound hδ ν hνint hνmean hνsupp
  -- the event
  have hE : 𝔼[fun ω' => ∑ i, X i ω'] = ∑ i, m i := by
    simp only [m]
    exact integral_finsetSum _ (fun i _ => hint i)
  have hevent : {ω | ∑ i, X i ω - 𝔼[fun ω' => ∑ i, X i ω'] < δ * μ} =
      (fun ω i => Y i ω) ⁻¹' Samuels.evt n δ := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_preimage, Samuels.evt, hE, Y, g]
    rw [← Finset.sum_div, div_lt_iff₀ hμ, Finset.sum_add_distrib, Finset.sum_sub_distrib]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    constructor <;> intro h <;> nlinarith
  have haevec : AEMeasurable (fun ω i => Y i ω) ℙ := by
    first
    | exact AEMeasurable.of_eval haeY
    | exact aemeasurable_pi_lambda _ haeY
  rw [hevent, ← Measure.map_apply_of_aemeasurable haevec (Samuels.measurableSet_evt δ), hjoint]
  exact (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)).mp hbound

end OMA.S_opg_sums_of_independent_random_variables_with_unbounded_variance

end
