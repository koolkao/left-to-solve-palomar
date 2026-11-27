module

public import Feige.Bridge.MeanOne
public import Feige.Bernoulli.Thm21General

/- Port (Palomar entry): `module` header, `public import`s and a public section added for the module system; otherwise unchanged from github.com/koolkao/feige-lean at commit 7da24abf1619706bf4f705bb24aa4d00bc63b49f. -/

@[expose] public section

/-!
# Samuels' conjecture: Ling's Theorem 1.1, lower bound

For `0 ≤ m₁ ≤ ⋯ ≤ mₙ`, `λ > ∑ mᵢ` and independent nonnegative `Xᵢ` with `E Xᵢ = mᵢ`,
`P(∑ Xᵢ < λ) ≥ min_i qᵢ`, `qᵢ = ∏_{j ≥ i} (1 - mⱼ / (λ - ∑_{k < i} mₖ))`.

* `pi_meanOne_lower`: the LeanPool mixture reduces any lower bound for mean-one product laws to
  the conditional two-point products (Ling Prop. 2.3, Lemma 2.4).
* `weighted_twoPoint_bound`: Bernoullification (Ling §2.2) with `wᵢ = mᵢ(yᵢ - xᵢ)/Λ`,
  `aᵢ = mᵢ/Λ`, `d = δ/Λ`, and `thm21` on `s = {i | mᵢ > 0}`.
* `samuels_lower`: zero-mean coordinates are replaced by the constant `1`
  (as in LeanPool's `meanOneNormalize`), positive ones by `Xᵢ/mᵢ`.
-/

open MeasureTheory ProbabilityTheory Finset Real

namespace Samuels

noncomputable section

open scoped Classical

open Feige

variable {n : ℕ}

/-- Mixture reduction for an arbitrary measurable event. -/
theorem pi_meanOne_lower (ν : Fin n → Measure ℝ) [∀ i, IsProbabilityMeasure (ν i)]
    (hint : ∀ i, Integrable (fun x : ℝ => x) (ν i)) (hmean : ∀ i, (∫ x, x ∂ν i) = 1)
    (hsupp : ∀ i, ν i (Set.Iio 0) = 0) {A : Set (Fin n → ℝ)} (hA : MeasurableSet A) {q : ℝ}
    (hq : ∀ p : Fin n → AugmentedTwoPointParams, AugmentedParamsNonnegative p →
      q ≤ Ex (fun i => cp (p i)) univ
        (fun S => if vecOf (fun i => cx (p i)) (fun i => cy (p i)) S ∈ A then 1 else 0)) :
    ENNReal.ofReal q ≤ Measure.pi ν A := by
  haveI : ∀ i, IsProbabilityMeasure (meanOneAugmentedLatent (ν i)) :=
    fun i => meanOneAugmentedLatent_isProbability (hint i) (hmean i)
  rw [← pi_eq_recursiveMeanOneAugmented_mixture n ν hint hmean,
    Measure.bind_apply hA (Kernel.aemeasurable _)]
  have hae := ae_recursiveAugmentedLatent_nonnegative n ν hint hmean hsupp
  calc ENNReal.ofReal q
      = ∫⁻ _, ENNReal.ofReal q
          ∂recursiveAugmentedLatent n (fun i => meanOneAugmentedLatent (ν i)) := by
        rw [lintegral_const, measure_univ, mul_one]
    _ ≤ _ := by
        apply lintegral_mono_ae
        filter_upwards [hae] with p hp
        rw [recursiveAugmentedKernel_apply_eq_conditionalProduct, augmentedConditionalProduct]
        have hfun : (fun i => augmentedTwoPointKernel (p i)) =
            fun i => twoPt (cp (p i)) (cx (p i)) (cy (p i)) :=
          funext fun i => kernel_eq_twoPt (p i)
        rw [hfun]
        have hp0 : ∀ i, 0 ≤ cp (p i) := fun i => cp_nonneg _
        have hp1 : ∀ i, cp (p i) ≤ 1 := fun i => cp_le_one _
        haveI := fun i => twoPt_isProbability (x := cx (p i)) (y := cy (p i)) (hp0 i) (hp1 i)
        rw [ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _),
          pi_twoPt_apply _ _ _ hp0 hp1 hA]
        exact hq p hp

/-- Samuels' candidate bounds `qᵢ`. -/
def qS (m : Fin n → ℝ) (lam : ℝ) (i : Fin n) : ℝ :=
  ∏ j ∈ univ.filter (i ≤ ·), (1 - m j / (lam - ∑ k ∈ univ.filter (· < i), m k))

/-- `Ex` ignores coordinates on which `F` does not depend. -/
lemma Ex_union_irrelevant {ι : Type*} [DecidableEq ι] (p : ι → ℝ) (s : Finset ι)
    (F : Finset ι → ℝ) (u : Finset ι) (hsu : Disjoint u s)
    (hF : ∀ i ∈ u, ∀ S, F (insert i S) = F S) : Ex p (u ∪ s) F = Ex p s F := by
  induction u using Finset.induction_on with
  | empty => simp
  | insert i u hi ih =>
    have hiu : i ∉ u ∪ s := by
      simp only [mem_union, not_or]
      exact ⟨hi, fun h => disjoint_left.mp hsu (mem_insert_self i u) h⟩
    rw [insert_union, Ex_insert hiu]
    have h1 : Ex p (u ∪ s) (fun S => F (insert i S)) = Ex p (u ∪ s) F :=
      Ex_congr fun S _ => hF i (mem_insert_self i u) S
    rw [h1, ih (disjoint_of_subset_left (subset_insert i u) hsu)
      (fun j hj S => hF j (mem_insert_of_mem hj) S)]
    ring

/-- **Bernoullification** with unequal means (Ling §2.2). -/
theorem weighted_twoPoint_bound (hn : 0 < n) (x y p m : Fin n → ℝ) {lam : ℝ}
    (hx0 : ∀ i, 0 ≤ x i) (hxy : ∀ i, x i ≤ y i) (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i < 1)
    (hpxy : ∀ i, p i * (y i - x i) = 1 - x i) (hm0 : ∀ i, 0 ≤ m i) (hmono : Monotone m)
    (hlam : ∑ i, m i < lam) :
    ∃ i, qS m lam i ≤
      Ex p univ (fun S => if vecOf x y S ∈ {z : Fin n → ℝ | ∑ i, m i * z i < lam} then 1 else 0) := by
  have hx1 : ∀ i, 0 ≤ 1 - x i := fun i => by
    rw [← hpxy i]; exact mul_nonneg (hp0 i) (sub_nonneg.mpr (hxy i))
  set δ := lam - ∑ i, m i with hδ
  have hδpos : 0 < δ := by rw [hδ]; linarith
  set Λ := δ + ∑ i, m i * (1 - x i) with hΛ
  have hΛpos : 0 < Λ := by
    have : 0 ≤ ∑ i, m i * (1 - x i) := sum_nonneg fun i _ => mul_nonneg (hm0 i) (hx1 i)
    linarith
  set w : Fin n → ℝ := fun i => m i * (y i - x i) / Λ with hw
  set a : Fin n → ℝ := fun i => m i / Λ with ha
  set s := univ.filter (fun i => 0 < m i) with hs
  -- the event in terms of `T`
  have hevt : ∀ S : Finset (Fin n), (vecOf x y S ∈ {z : Fin n → ℝ | ∑ i, m i * z i < lam} ↔
      T w S < 1) := by
    intro S
    have : ∑ i, m i * vecOf x y S i = ∑ i, m i * x i + ∑ i ∈ S, m i * (y i - x i) := by
      have : ∀ i, m i * vecOf x y S i = m i * x i + (if i ∈ S then m i * (y i - x i) else 0) := by
        intro i; simp only [vecOf]; split_ifs <;> ring
      simp only [this, sum_add_distrib]
      rw [sum_ite_mem, univ_inter]
    simp only [Set.mem_setOf_eq, this, T, hw, ← sum_div]
    rw [div_lt_one hΛpos, hΛ, hδ]
    have : ∑ i, m i * (1 - x i) = ∑ i, m i - ∑ i, m i * x i := by
      rw [← sum_sub_distrib]; apply sum_congr rfl; intro i _; ring
    rw [this]
    constructor <;> intro h <;> linarith
  have hF : Ex p univ (fun S => if vecOf x y S ∈ {z : Fin n → ℝ | ∑ i, m i * z i < lam} then 1 else 0)
      = Z p w s 1 := by
    have h1 : Ex p univ (fun S => if vecOf x y S ∈ {z : Fin n → ℝ | ∑ i, m i * z i < lam}
        then 1 else 0) = Ex p univ (fun S => if T w S < 1 then 1 else 0) :=
      Ex_congr fun S _ => by simp only [hevt S]
    rw [h1, Z, ← Ex_union_irrelevant p s _ (univ \ s) disjoint_sdiff_self_left, sdiff_union_of_subset
      (subset_univ s)]
    intro i hi S
    have hmi : m i = 0 := by
      have : ¬ 0 < m i := by simpa [hs] using hi
      linarith [hm0 i]
    have hwi : w i = 0 := by simp [hw, hmi]
    by_cases hiS : i ∈ S
    · rw [insert_eq_of_mem hiS]
    · rw [T_insert hiS, hwi, zero_add]
  rw [hF]
  rcases s.eq_empty_or_nonempty with hse | hsne
  · -- all means are zero
    refine ⟨⟨0, hn⟩, ?_⟩
    have hm : ∀ i, m i = 0 := fun i => by
      have : i ∉ s := by rw [hse]; simp
      have : ¬ 0 < m i := by simpa [hs] using this
      linarith [hm0 i]
    rw [hse]
    simp [Z, T, qS, hm]
  -- apply Theorem 2.1 on `s`
  have hEs : E p w s = (∑ i, m i * (1 - x i)) / Λ := by
    rw [E, sum_div]
    rw [← sum_subset (subset_univ s)]
    · apply sum_congr rfl; intro i _; simp only [hw]; rw [← hpxy i]; ring
    · intro i _ hi
      have hmi : m i = 0 := by
        have : ¬ 0 < m i := by simpa [hs] using hi
        linarith [hm0 i]
      simp [hmi]
  have hd : 1 - E p w s = δ / Λ := by
    rw [hEs]; field_simp; rw [hΛ]; ring
  have hmemS : ∀ i ∈ s, 0 < m i := fun i hi => (mem_filter.mp hi).2
  obtain ⟨i, his, hi⟩ := thm21 p w a s hsne (fun i _ => hp0 i) (fun i _ => hp1 i)
    (fun i _ => div_nonneg (mul_nonneg (hm0 i) (sub_nonneg.mpr (hxy i))) hΛpos.le)
    (fun i _ => by
      simp only [hw, ha]
      rw [div_mul_eq_mul_div, mul_assoc, mul_comm (y i - x i), hpxy i]
      apply div_le_div_of_nonneg_right _ hΛpos.le
      nlinarith [hm0 i, hx0 i])
    (fun i hi => div_pos (hmemS i hi) hΛpos)
    (fun i _ j _ hij => div_le_div_of_nonneg_right (hmono hij) hΛpos.le)
    (by rw [hd]; exact div_pos hδpos hΛpos)
  refine ⟨i, le_trans (le_of_eq ?_) hi⟩
  -- identify `qᵢ` with `term`
  rw [hd]
  unfold term qS Cge
  have hoff : ∀ j, j ∉ s → m j = 0 := fun j hj => by
    have : ¬ 0 < m j := by simpa [hs] using hj
    linarith [hm0 j]
  have hsumC : ∑ j ∈ s.filter (i ≤ ·), a j = (∑ j ∈ univ.filter (i ≤ ·), m j) / Λ := by
    rw [sum_div]
    apply sum_subset (filter_subset_filter _ (subset_univ s))
    intro j hj hj'
    have : j ∉ s := fun h => hj' (mem_filter.mpr ⟨h, (mem_filter.mp hj).2⟩)
    simp [ha, hoff j this]
  have hsplit : lam - ∑ k ∈ univ.filter (· < i), m k = δ + ∑ j ∈ univ.filter (i ≤ ·), m j := by
    rw [hδ]
    have := sum_filter_add_sum_filter_not univ (· < i) m
    have e : univ.filter (fun j => ¬ j < i) = univ.filter (i ≤ ·) := by
      ext j; simp
    rw [e] at this
    linarith
  rw [hsumC, hsplit]
  set C := ∑ j ∈ univ.filter (i ≤ ·), m j with hC
  have hC0 : 0 ≤ C := sum_nonneg fun j _ => hm0 j
  have hfac : ∀ j, 1 - a j / (δ / Λ + C / Λ) = 1 - m j / (δ + C) := by
    intro j
    simp only [ha]
    congr 1
    have : 0 < δ + C := by linarith
    field_simp
  rw [prod_congr rfl (fun j _ => hfac j)]
  refine (prod_subset (filter_subset_filter _ (subset_univ s)) ?_).symm
  intro j hj hj'
  have : j ∉ s := fun h => hj' (mem_filter.mpr ⟨h, (mem_filter.mp hj).2⟩)
  simp [hoff j this]

/-- **Ling's Theorem 1.1, lower bound (Samuels' conjecture).** For `0 ≤ m₁ ≤ ⋯ ≤ mₙ`,
`λ > ∑ mᵢ` and independent nonnegative integrable `Xᵢ` with `E Xᵢ = mᵢ`,
`min_i qᵢ ≤ P(∑ Xᵢ < λ)` with `qᵢ = ∏_{j ≥ i} (1 - mⱼ/(λ - ∑_{k<i} mₖ))`. -/
theorem samuels_lower (hn : 0 < n) {Ω : Type*} [MeasureSpace Ω]
    [IsProbabilityMeasure (ℙ : Measure Ω)] (X : Fin n → Ω → ℝ) (m : Fin n → ℝ) (lam : ℝ)
    (hmono : Monotone m) (hm0 : ∀ i, 0 ≤ m i) (hlam : ∑ i, m i < lam)
    (hind : iIndepFun X ℙ) (hnn : ∀ i ω, 0 ≤ X i ω) (hint : ∀ i, Integrable (X i))
    (hmean : ∀ i, 𝔼[X i] = m i) :
    univ.inf' ⟨⟨0, hn⟩, mem_univ _⟩ (qS m lam) ≤ (ℙ {ω | ∑ i, X i ω < lam}).toReal := by
  let g : Fin n → ℝ → ℝ := fun i => if m i = 0 then (fun _ => 1) else (fun x => x / m i)
  have hg : ∀ i, Measurable (g i) := fun i => by
    simp only [g]; split_ifs
    · exact measurable_const
    · exact measurable_id.div_const _
  let Y : Fin n → Ω → ℝ := fun i ω => g i (X i ω)
  have hindY : iIndepFun Y ℙ := hind.comp g hg
  have haeY : ∀ i, AEMeasurable (Y i) ℙ := fun i => (hg i).comp_aemeasurable (hint i).aemeasurable
  have hYnn : ∀ i ω, 0 ≤ Y i ω := fun i ω => by
    simp only [Y, g]; split_ifs with h
    · norm_num
    · exact div_nonneg (hnn i ω) (hm0 i)
  have hintY : ∀ i, Integrable (Y i) ℙ := fun i => by
    simp only [Y, g]; split_ifs
    · exact integrable_const 1
    · exact (hint i).div_const _
  have hmeanY : ∀ i, ∫ ω, Y i ω = 1 := fun i => by
    simp only [Y, g]; split_ifs with h
    · simp
    · rw [integral_div, show (∫ ω, X i ω) = m i from hmean i, div_self h]
  -- `∑ Xᵢ = ∑ mᵢ Yᵢ` almost surely
  have hae : ∀ᵐ ω ∂(ℙ : Measure Ω), ∑ i, X i ω = ∑ i, m i * Y i ω := by
    have : ∀ i, ∀ᵐ ω ∂(ℙ : Measure Ω), X i ω = m i * Y i ω := by
      intro i
      by_cases h : m i = 0
      · have hz : X i =ᵐ[ℙ] 0 :=
          (integral_eq_zero_iff_of_nonneg (hnn i) (hint i)).mp (by rw [← h]; exact hmean i)
        filter_upwards [hz] with ω hω
        simp [Y, g, h, hω]
      · exact Filter.Eventually.of_forall fun ω => by
          simp only [Y, g, if_neg h]; field_simp
    filter_upwards [ae_all_iff.mpr this] with ω hω
    exact sum_congr rfl fun i _ => hω i
  -- marginals
  let ν : Fin n → Measure ℝ := fun i => (ℙ : Measure Ω).map (Y i)
  have : ∀ i, IsProbabilityMeasure (ν i) := fun i =>
    (Measure.isProbabilityMeasure_map_iff (haeY i)).mpr inferInstance
  have hνint : ∀ i, Integrable (fun x : ℝ => x) (ν i) := fun i =>
    (integrable_map_measure (g := id) aestronglyMeasurable_id (haeY i)).mpr (hintY i)
  have hνmean : ∀ i, ∫ x, x ∂(ν i) = 1 := fun i =>
    (integral_map (φ := Y i) (f := id) (haeY i) aestronglyMeasurable_id).trans (hmeanY i)
  have hνsupp : ∀ i, ν i (Set.Iio 0) = 0 := fun i => by
    rw [Measure.map_apply_of_aemeasurable (haeY i) measurableSet_Iio]
    have : Y i ⁻¹' Set.Iio 0 = ∅ := by
      ext ω; simp only [Set.mem_preimage, Set.mem_Iio, Set.mem_empty_iff_false, iff_false, not_lt]
      exact hYnn i ω
    rw [this, measure_empty]
  have hjoint : (ℙ : Measure Ω).map (fun ω i => Y i ω) = Measure.pi ν :=
    (iIndepFun_iff_map_fun_eq_pi_map haeY).mp hindY
  set A : Set (Fin n → ℝ) := {z | ∑ i, m i * z i < lam} with hA
  have hAm : MeasurableSet A :=
    measurableSet_lt (by fun_prop) measurable_const
  set q := univ.inf' ⟨⟨0, hn⟩, mem_univ _⟩ (qS m lam)
  have hbound : ENNReal.ofReal q ≤ Measure.pi ν A := by
    apply pi_meanOne_lower ν hνint hνmean hνsupp hAm
    intro p hp
    obtain ⟨i, hi⟩ := weighted_twoPoint_bound hn (fun i => cx (p i)) (fun i => cy (p i))
      (fun i => cp (p i)) m (fun i => (props_of_nonneg (hp i)).1)
      (fun i => (props_of_nonneg (hp i)).2.1) (fun i => cp_nonneg _)
      (fun i => (props_of_nonneg (hp i)).2.2.1) (fun i => (props_of_nonneg (hp i)).2.2.2)
      hm0 hmono hlam
    exact (inf'_le _ (mem_univ i)).trans hi
  have hevent : (ℙ : Measure Ω) {ω | ∑ i, X i ω < lam} = (ℙ : Measure Ω) ((fun ω i => Y i ω) ⁻¹' A) := by
    apply measure_congr
    filter_upwards [hae] with ω hω
    change (∑ i, X i ω < lam) ↔ (∑ i, m i * Y i ω < lam)
    rw [hω]
  have haevec : AEMeasurable (fun ω i => Y i ω) ℙ := by
    first
    | exact AEMeasurable.of_eval haeY
    | exact aemeasurable_pi_lambda _ haeY
  rw [hevent, ← Measure.map_apply_of_aemeasurable haevec hAm, hjoint]
  exact (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)).mp hbound

/-- Equivalent form: some candidate `qᵢ` is a lower bound. -/
theorem samuels_lower_exists (hn : 0 < n) {Ω : Type*} [MeasureSpace Ω]
    [IsProbabilityMeasure (ℙ : Measure Ω)] (X : Fin n → Ω → ℝ) (m : Fin n → ℝ) (lam : ℝ)
    (hmono : Monotone m) (hm0 : ∀ i, 0 ≤ m i) (hlam : ∑ i, m i < lam)
    (hind : iIndepFun X ℙ) (hnn : ∀ i ω, 0 ≤ X i ω) (hint : ∀ i, Integrable (X i))
    (hmean : ∀ i, 𝔼[X i] = m i) :
    ∃ i, qS m lam i ≤ (ℙ {ω | ∑ i, X i ω < lam}).toReal := by
  obtain ⟨i, -, hi⟩ := exists_mem_eq_inf' (s := univ) ⟨⟨0, hn⟩, mem_univ _⟩ (qS m lam)
  exact ⟨i, hi ▸ samuels_lower hn X m lam hmono hm0 hlam hind hnn hint hmean⟩

end

end Samuels

end
