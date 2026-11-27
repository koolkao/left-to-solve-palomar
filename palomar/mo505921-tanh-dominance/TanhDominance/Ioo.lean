/-
Copyright 2026 Ming-Chih Kao. Licensed under the Apache License, Version 2.0;
see the LICENSE file at the root of this repository.
-/
module

public import TanhDominance.Proof

/-! Added for this Palomar entry (not in the source repository): the answer with the comparison of
c.d.f.s restricted to `t ∈ (-1, 1)`, the range the question uses. Both variables take values in
`(-1, 1)`, so outside that range the comparison holds trivially and the two forms are equivalent;
`mo505921_Ioo` derives the restricted form from `TanhDominance.mo505921`. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Real
open scoped ENNReal NNReal

namespace TanhDominance

/-- For laws on `ℝ` carried by `(-1, 1)` (no mass on `(-∞, -1]` for the first and on `[1, ∞)`
for the second), a comparison of their c.d.f.s on `(-1, 1)` extends to all of `ℝ`. -/
lemma cdf_le_of_Ioo {μ ν : Measure ℝ} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : μ (Iic (-1)) = 0) (hν : ν (Ici 1) = 0)
    (h : ∀ t ∈ Ioo (-1 : ℝ) 1, cdf μ t ≤ cdf ν t) (t : ℝ) : cdf μ t ≤ cdf ν t := by
  by_cases h1 : t ≤ -1
  · have : cdf μ t = 0 := by
      rw [cdf_eq_real, measureReal_def, measure_mono_null (Iic_subset_Iic.2 h1) hμ,
        ENNReal.toReal_zero]
    rw [this]; exact cdf_nonneg _ _
  by_cases h2 : 1 ≤ t
  · have : cdf ν t = 1 := by
      have hc : ν (Iic t)ᶜ = 0 := by
        rw [compl_Iic]; exact measure_mono_null (fun x hx => le_of_lt (lt_of_le_of_lt h2 hx)) hν
      rw [cdf_eq_real, measureReal_def, (prob_compl_eq_zero_iff measurableSet_Iic).1 hc,
        ENNReal.toReal_one]
    rw [this]; exact cdf_le_one _ _
  exact h t ⟨by linarith, by linarith⟩

/-- The law of a random variable with values in `(-1, 1)` has no mass on `(-∞, -1]` or `[1, ∞)`. -/
lemma map_Iic_Ici {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {A : Ω → ℝ}
    (hAm : AEMeasurable A P) (hA : ∀ ω, A ω ∈ Ioo (-1 : ℝ) 1) :
    P.map A (Iic (-1)) = 0 ∧ P.map A (Ici 1) = 0 := by
  have e1 : A ⁻¹' Iic (-1) = ∅ := by
    ext ω; simp only [mem_preimage, mem_Iic, mem_empty_iff_false, iff_false, not_le]
    exact (hA ω).1
  have e2 : A ⁻¹' Ici 1 = ∅ := by
    ext ω; simp only [mem_preimage, mem_Ici, mem_empty_iff_false, iff_false, not_le]
    exact (hA ω).2
  rw [Measure.map_apply_of_aemeasurable hAm measurableSet_Iic,
    Measure.map_apply_of_aemeasurable hAm measurableSet_Ici, e1, e2, measure_empty]
  exact ⟨rfl, rfl⟩

/-- **MO 505921 on the question's range.** As `mo505921`, with the c.d.f.s compared only at
`t ∈ (-1, 1)`. -/
theorem mo505921_Ioo {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {gX gY gZ : ℝ≥0} (hgX : gX ≠ 0) (hgY : gY ≠ 0) (hgZ : gZ ≠ 0) {X Y Z : Ω → ℝ}
    (hX : HasLaw X (gaussianReal gX gX) P) (hY : HasLaw Y (gaussianReal gY gY) P)
    (hZ : HasLaw Z (gaussianReal gZ gZ) P) (hYZ : IndepFun Y Z P) :
    (¬ ∀ t ∈ Ioo (-1 : ℝ) 1,
        cdf (P.map fun ω => tanh (Y ω) * tanh (Z ω)) t ≤ cdf (P.map fun ω => tanh (X ω)) t) ∧
      (¬ ∀ t ∈ Ioo (-1 : ℝ) 1,
        cdf (P.map fun ω => tanh (X ω)) t ≤ cdf (P.map fun ω => tanh (Y ω) * tanh (Z ω)) t) := by
  have main := mo505921 hgX hgY hgZ hX hY hZ hYZ
  have mU : AEMeasurable (fun ω => tanh (X ω)) P := measurable_tanh.comp_aemeasurable hX.aemeasurable
  have mV : AEMeasurable (fun ω => tanh (Y ω) * tanh (Z ω)) P :=
    (measurable_tanh.comp_aemeasurable hY.aemeasurable).mul
      (measurable_tanh.comp_aemeasurable hZ.aemeasurable)
  have rU : ∀ ω, tanh (X ω) ∈ Ioo (-1 : ℝ) 1 := fun ω => tanh_mem _
  have rV : ∀ ω, tanh (Y ω) * tanh (Z ω) ∈ Ioo (-1 : ℝ) 1 := fun ω => mul_tanh_mem _ _
  exact ⟨fun h => main.1 (cdf_le_of_Ioo (map_Iic_Ici mV rV).1 (map_Iic_Ici mU rU).2 h),
    fun h => main.2 (cdf_le_of_Ioo (map_Iic_Ici mU rU).1 (map_Iic_Ici mV rV).2 h)⟩

/-- **The question as asked, law form, on the question's range.** Given `gY, gZ > 0`, no `gX > 0`
gives `F_U(t) ≥ F_V(t)` for every `t ∈ (-1, 1)`, where `U = tanh X` with `X ~ N(gX, gX)` and
`V = tanh Y * tanh Z` with `(Y, Z) ~ N(gY, gY) ⊗ N(gZ, gZ)`. -/
theorem no_gX_Ioo (gY gZ : ℝ≥0) (hY : gY ≠ 0) (hZ : gZ ≠ 0) :
    ¬ ∃ gX : ℝ≥0, gX ≠ 0 ∧ ∀ t ∈ Ioo (-1 : ℝ) 1,
      cdf (((gaussianReal gY gY).prod (gaussianReal gZ gZ)).map fun p => tanh p.1 * tanh p.2) t ≤
        cdf ((gaussianReal gX gX).map tanh) t := by
  rintro ⟨gX, hX, h⟩
  have hV := map_Iic_Ici (P := (gaussianReal gY gY).prod (gaussianReal gZ gZ))
    (A := fun p : ℝ × ℝ => tanh p.1 * tanh p.2) (by fun_prop) fun p => mul_tanh_mem _ _
  have hU := map_Iic_Ici (P := gaussianReal gX gX) (A := tanh) measurable_tanh.aemeasurable tanh_mem
  refine (not_stochastic_order hX hY hZ).1 fun t => ?_
  rw [lawV_eq, lawU]
  exact cdf_le_of_Ioo hV.1 hU.2 h t

end TanhDominance

end
