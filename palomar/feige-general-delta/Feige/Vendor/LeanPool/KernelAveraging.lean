/-
Copyright (c) 2026 Zhengqing Zhou and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhengqing Zhou, GPT-5.6 Pro
-/
-- Vendored from LeanPool/lean-pool (https://github.com/LeanPool/lean-pool),
-- file LeanPool/Feige/KernelAveraging.lean at commit 9decab6341e6b0fd82bd7f9763a5dd7a9ce8778d, Apache-2.0 (see LICENSE in this folder).
-- Changes: import paths renamed from `LeanPool.Feige.*` to `Feige.Vendor.LeanPool.*`.
-- Portability (Left to Solve CI, Lean v4.33.1): `add_apply`/`smul_apply` qualified as `Measure.*`,
-- `ite_eq_left/right` replaced by `if_pos/if_neg`, and small elaboration fixes where needed.

module

public import Mathlib.Probability.Kernel.Composition.CompNotation
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Averaging conditional probability bounds

This file records the elementary final step used after the latent
two-point decomposition: an almost-everywhere event bound for the
conditional Markov kernel survives averaging over a probability law.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace Feige

noncomputable section

/-- An almost-everywhere real-valued probability bound for the fibres of a
Markov kernel is inherited by the mixture measure. -/
theorem measureReal_bind_apply_le
    {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (κ : Kernel A B) [IsMarkovKernel κ]
    (ν : Measure A) [IsProbabilityMeasure ν]
    {s : Set B} (hs : MeasurableSet s)
    {c : ℝ} (hc0 : 0 ≤ c)
    (hc : ∀ᵐ a ∂ν, (κ a).real s ≤ c) :
    (κ ∘ₘ ν).real s ≤ c := by
  rw [measureReal_def, Measure.bind_apply hs κ.aemeasurable]
  have hfibres :
      ∀ᵐ a ∂ν, κ a s ≤ ENNReal.ofReal c := by
    filter_upwards [hc] with a ha
    rw [← ofReal_measureReal (μ := κ a) (s := s)]
    exact ENNReal.ofReal_le_ofReal ha
  have hint :
      (∫⁻ a, κ a s ∂ν) ≤ ∫⁻ _a, ENNReal.ofReal c ∂ν :=
    lintegral_mono_ae hfibres
  rw [lintegral_const, measure_univ, mul_one] at hint
  calc
    (∫⁻ a, κ a s ∂ν).toReal ≤ (ENNReal.ofReal c).toReal :=
      ENNReal.toReal_mono ENNReal.ofReal_ne_top hint
    _ = c := ENNReal.toReal_ofReal hc0

end

end Feige
