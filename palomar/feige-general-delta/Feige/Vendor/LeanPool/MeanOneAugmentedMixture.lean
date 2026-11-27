/-
Copyright (c) 2026 Zhengqing Zhou and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhengqing Zhou, GPT-5.6 Pro
-/
-- Vendored from LeanPool/lean-pool (https://github.com/LeanPool/lean-pool),
-- file LeanPool/Feige/MeanOneAugmentedMixture.lean at commit 9decab6341e6b0fd82bd7f9763a5dd7a9ce8778d, Apache-2.0 (see LICENSE in this folder).
-- Changes: import paths renamed from `LeanPool.Feige.*` to `Feige.Vendor.LeanPool.*`.
-- Portability (Left to Solve CI, Lean v4.33.1): `add_apply`/`smul_apply` qualified as `Measure.*`,
-- `ite_eq_left/right` replaced by `if_pos/if_neg`, and small elaboration fixes where needed.

module

public import Feige.Vendor.LeanPool.ProductTwoPointKernel
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic

/-!
# A total augmented mixture for mean-one laws

The positive-moment branch uses the latent two-point measure from Lemma
4.6.  When the lower moment vanishes, the original law is `δ₁`, so the
latent law is simply the atom branch.  This removes the artificial
coordinatewise strict-moment assumption from the finite product mixture.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace Feige

noncomputable section

/-- The augmented latent law, including the degenerate zero-below-moment case. -/
def meanOneAugmentedLatent (μ : Measure ℝ) :
    Measure AugmentedTwoPointParams :=
  if belowMoment μ = 0 then
    Measure.dirac (Sum.inl ())
  else
    augmentedLatentMeasure μ (belowMoment μ)

theorem meanOneAugmentedLatent_isProbability
    {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hμ : Integrable (fun x : ℝ ↦ x) μ)
    (hmean : (∫ x : ℝ, x ∂μ) = 1) :
    IsProbabilityMeasure (meanOneAugmentedLatent μ) := by
  by_cases hM : belowMoment μ = 0
  · rw [meanOneAugmentedLatent, if_pos hM]
    infer_instance
  · rw [meanOneAugmentedLatent, if_neg hM]
    exact augmentedLatentMeasure_isProbability hμ hmean
      (lt_of_le_of_ne belowMoment_nonneg (Ne.symm hM))

theorem augmentedTwoPointKernel_comp_meanOneLatent
    {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hμ : Integrable (fun x : ℝ ↦ x) μ)
    (hmean : (∫ x : ℝ, x ∂μ) = 1) :
    augmentedTwoPointKernel ∘ₘ meanOneAugmentedLatent μ = μ := by
  by_cases hM : belowMoment μ = 0
  · rw [meanOneAugmentedLatent, if_pos hM]
    rw [Measure.dirac_bind augmentedTwoPointKernel.measurable]
    rw [augmentedTwoPointKernel_atom]
    exact (eq_dirac_one_of_belowMoment_eq_zero
      hμ hmean hM).symm
  · rw [meanOneAugmentedLatent, if_neg hM,
      augmentedTwoPointKernel_comp_latent,
      fullKernelMixture_eq hμ hmean
        (lt_of_le_of_ne belowMoment_nonneg (Ne.symm hM))]

/-- Every finite product of mean-one laws is a mixture of the conditionally
independent augmented two-point systems, including all degenerate `δ₁`
coordinates. -/
theorem pi_eq_recursiveMeanOneAugmented_mixture
    (n : ℕ) (μ : Fin n → Measure ℝ)
    [∀ i, IsProbabilityMeasure (μ i)]
    (hμ : ∀ i, Integrable (fun x : ℝ ↦ x) (μ i))
    (hmean : ∀ i, (∫ x : ℝ, x ∂μ i) = 1) :
    recursiveAugmentedKernel n ∘ₘ
        recursiveAugmentedLatent n
          (fun i ↦ meanOneAugmentedLatent (μ i)) =
      Measure.pi μ := by
  let hlatent : ∀ i, IsProbabilityMeasure
      (meanOneAugmentedLatent (μ i)) :=
    fun i ↦ meanOneAugmentedLatent_isProbability
      (hμ i) (hmean i)
  rw [recursiveAugmentedKernel_comp_latent]
  have hcoord :
      (fun i => augmentedTwoPointKernel ∘ₘ
          meanOneAugmentedLatent (μ i)) = μ := by
    funext i
    exact augmentedTwoPointKernel_comp_meanOneLatent
      (hμ i) (hmean i)
  rw [hcoord, recursiveRealProduct_eq_pi]

end

end Feige
