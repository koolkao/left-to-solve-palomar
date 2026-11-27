module

public import Feige.Bridge.PiDirac
public import Feige.Bernoulli.TwoPointBound
public import Feige.Vendor

/- Port (Palomar entry): `module` header, `public import`s and a public section added for the module system; otherwise unchanged from github.com/koolkao/feige-lean at commit 7da24abf1619706bf4f705bb24aa4d00bc63b49f. -/

@[expose] public section

/-!
# Mean-one product laws (Ling Prop. 2.3, Lemma 2.4, §2.2 for equal means)

For probability measures `νᵢ` on `ℝ` with `νᵢ (-∞, 0) = 0` and mean one,
`(⊗ νᵢ) {z | ∑ zᵢ < n + δ} ≥ min (δ/(1+δ)) e⁻¹`.

The two-point decomposition (Prop. 2.3) and the product mixture (Lemma 2.4) come from the
vendored LeanPool files (`pi_eq_recursiveMeanOneAugmented_mixture`,
`ae_recursiveAugmentedLatent_nonnegative`, `recursiveAugmentedKernel_apply_eq_conditionalProduct`).
For each fixed latent parameter vector, the conditional law is a product of two-point laws,
which `pi_twoPt_apply` turns into a finite Bernoulli sum, bounded by `twoPoint_bound`.
-/

open MeasureTheory ProbabilityTheory Finset Real

namespace Samuels

noncomputable section

open Feige

/-- Bernoulli parameter of an augmented latent coordinate (`0` for the atom at one). -/
def cp : AugmentedTwoPointParams → ℝ
  | Sum.inl _ => 0
  | Sum.inr q => (1 - q.1.1) / (q.1.2 - q.1.1)

/-- Low point of an augmented latent coordinate. -/
def cx : AugmentedTwoPointParams → ℝ
  | Sum.inl _ => 1
  | Sum.inr q => q.1.1

/-- High point of an augmented latent coordinate. -/
def cy : AugmentedTwoPointParams → ℝ
  | Sum.inl _ => 1
  | Sum.inr q => q.1.2

lemma cp_nonneg (a : AugmentedTwoPointParams) : 0 ≤ cp a := by
  cases a with
  | inl _ => simp [cp]
  | inr q =>
    simp only [cp]
    exact div_nonneg (by linarith [q.2.1]) (by linarith [q.2.2.2])

lemma cp_le_one (a : AugmentedTwoPointParams) : cp a ≤ 1 := by
  cases a with
  | inl _ => simp [cp]
  | inr q =>
    simp only [cp]
    rw [div_le_one (by linarith [q.2.2.2])]
    linarith [q.2.2.1]

lemma kernel_eq_twoPt (a : AugmentedTwoPointParams) :
    augmentedTwoPointKernel a = twoPt (cp a) (cx a) (cy a) := by
  cases a with
  | inl u =>
    cases u
    rw [augmentedTwoPointKernel_atom]
    simp [twoPt, cp, cx, cy]
  | inr q =>
    rw [augmentedTwoPointKernel_pair]
    have hxy : q.1.1 < q.1.2 := q.2.2.2
    have hne : q.1.2 - q.1.1 ≠ 0 := by linarith
    simp only [twoPointMeasure, twoPointLowerWeight, twoPointUpperWeight, twoPt, cp, cx, cy]
    congr 3
    field_simp
    ring

lemma props_of_nonneg {a : AugmentedTwoPointParams} (ha : AugmentedParamNonnegative a) :
    0 ≤ cx a ∧ cx a ≤ cy a ∧ cp a < 1 ∧ cp a * (cy a - cx a) = 1 - cx a := by
  cases a with
  | inl _ => simp [cp, cx, cy]
  | inr q =>
    simp only [AugmentedParamNonnegative] at ha
    have hxy : q.1.1 < q.1.2 := q.2.2.2
    have hne : q.1.2 - q.1.1 ≠ 0 := by linarith
    simp only [cp, cx, cy]
    refine ⟨ha.1, hxy.le, ?_, ?_⟩
    · rw [div_lt_one (by linarith)]; linarith [ha.2]
    · field_simp

variable {n : ℕ}

/-- The target event. -/
def evt (n : ℕ) (δ : ℝ) : Set (Fin n → ℝ) := {z | ∑ i, z i < n + δ}

lemma measurableSet_evt (δ : ℝ) : MeasurableSet (evt n δ) :=
  measurableSet_lt (Finset.measurable_sum _ fun i _ => measurable_pi_apply i) measurable_const

/-- The bound for a fixed latent parameter vector. -/
theorem conditional_bound {δ : ℝ} (hδ : 0 < δ) (p : Fin n → AugmentedTwoPointParams)
    (hp : AugmentedParamsNonnegative p) :
    ENNReal.ofReal (min (δ / (1 + δ)) (exp (-1))) ≤ recursiveAugmentedKernel n p (evt n δ) := by
  rw [recursiveAugmentedKernel_apply_eq_conditionalProduct, augmentedConditionalProduct]
  have hfun : (fun i => augmentedTwoPointKernel (p i)) =
      fun i => twoPt (cp (p i)) (cx (p i)) (cy (p i)) := funext fun i => kernel_eq_twoPt (p i)
  rw [hfun]
  have hp0 : ∀ i, 0 ≤ cp (p i) := fun i => cp_nonneg _
  have hp1 : ∀ i, cp (p i) ≤ 1 := fun i => cp_le_one _
  have hval := pi_twoPt_apply (fun i => cp (p i)) (fun i => cx (p i)) (fun i => cy (p i))
    hp0 hp1 (measurableSet_evt (n := n) δ)
  haveI := fun i => twoPt_isProbability (x := cx (p i)) (y := cy (p i)) (hp0 i) (hp1 i)
  rw [ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)]
  refine le_of_le_of_eq ?_ hval.symm
  have hb := twoPoint_bound (fun i => cx (p i)) (fun i => cy (p i)) (fun i => cp (p i)) hδ
    (fun i => (props_of_nonneg (hp i)).1) (fun i => (props_of_nonneg (hp i)).2.1) hp0
    (fun i => (props_of_nonneg (hp i)).2.2.1) (fun i => (props_of_nonneg (hp i)).2.2.2)
  refine hb.trans (le_of_eq ?_)
  apply Ex_congr
  intro S _
  have hsum : ∑ i, vecOf (fun i => cx (p i)) (fun i => cy (p i)) S i =
      ∑ i, cx (p i) + ∑ i ∈ S, (cy (p i) - cx (p i)) := by
    have : ∀ i, vecOf (fun i => cx (p i)) (fun i => cy (p i)) S i =
        cx (p i) + (if i ∈ S then cy (p i) - cx (p i) else 0) := by
      intro i; simp only [vecOf]; split_ifs <;> ring
    simp only [this, Finset.sum_add_distrib]
    rw [Finset.sum_ite_mem, Finset.univ_inter]
  simp only [evt, Set.mem_setOf_eq, hsum]

/-- **Mean-one product bound.** -/
theorem pi_meanOne_bound {δ : ℝ} (hδ : 0 < δ) (ν : Fin n → Measure ℝ)
    [∀ i, IsProbabilityMeasure (ν i)]
    (hint : ∀ i, Integrable (fun x : ℝ => x) (ν i)) (hmean : ∀ i, (∫ x, x ∂ν i) = 1)
    (hsupp : ∀ i, ν i (Set.Iio 0) = 0) :
    ENNReal.ofReal (min (δ / (1 + δ)) (exp (-1))) ≤ Measure.pi ν (evt n δ) := by
  haveI : ∀ i, IsProbabilityMeasure (meanOneAugmentedLatent (ν i)) :=
    fun i => meanOneAugmentedLatent_isProbability (hint i) (hmean i)
  rw [← pi_eq_recursiveMeanOneAugmented_mixture n ν hint hmean,
    Measure.bind_apply (measurableSet_evt δ) (Kernel.aemeasurable _)]
  have hae := ae_recursiveAugmentedLatent_nonnegative n ν hint hmean hsupp
  calc ENNReal.ofReal (min (δ / (1 + δ)) (exp (-1)))
      = ∫⁻ _, ENNReal.ofReal (min (δ / (1 + δ)) (exp (-1)))
          ∂recursiveAugmentedLatent n (fun i => meanOneAugmentedLatent (ν i)) := by
        rw [lintegral_const, measure_univ, mul_one]
    _ ≤ _ := by
        apply lintegral_mono_ae
        filter_upwards [hae] with p hp
        exact conditional_bound hδ p hp

end

end Samuels

end
