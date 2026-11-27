module

public import Feige.Bridge.MeanOne

/- Port (Palomar entry): `module` header, `public import`s and a public section added for the module system; otherwise unchanged from github.com/koolkao/feige-lean at commit 7da24abf1619706bf4f705bb24aa4d00bc63b49f. -/

@[expose] public section

/-!
# Sums of independent random variables with unbounded variance

Source: https://www.openproblemgarden.org/op/sums_of_independent_random_variables_with_unbounded_variance

Feige's conjecture for every `δ > 0`, with the sharp constant `min (δ/(1+δ)) e⁻¹`, following
Z. Ling, *On Samuels' Conjecture* (arXiv:2608.18392v2). The statement of `main` is copied
verbatim from `feige-manuscript/inputs/feige-statement.lean`.

Reduction (manuscript M1): `Yᵢ = (Xᵢ + (μ - E Xᵢ))/μ` are independent, nonnegative, of mean one,
and `∑ Xᵢ - E[∑ Xᵢ] < δ μ ↔ ∑ Yᵢ < n + δ`. The joint law of `Y` is the product of its marginals
(`iIndepFun_iff_map_fun_eq_pi_map`, which only needs `AEMeasurable`), and
`Samuels.pi_meanOne_bound` bounds the product measure.
-/

namespace OMA.S_opg_sums_of_independent_random_variables_with_unbounded_variance

open MeasureTheory ProbabilityTheory

theorem main :
    ∀ (n : ℕ) (Ω : Type) [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
      (X : Fin n → Ω → ℝ) (μ δ : ℝ), 0 < μ → 0 < δ →
      iIndepFun X ℙ → (∀ i ω, 0 ≤ X i ω) → (∀ i, Integrable (X i)) → (∀ i, 𝔼[X i] ≤ μ) →
      min (δ / (1 + δ)) (Real.exp (-1)) ≤
        (ℙ {ω | ∑ i, X i ω - 𝔼[fun ω' => ∑ i, X i ω'] < δ * μ}).toReal := by
  intro n Ω _ _ X μ δ hμ hδ hind hnn hint hmean
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
