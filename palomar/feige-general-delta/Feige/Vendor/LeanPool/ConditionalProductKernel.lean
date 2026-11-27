/-
Copyright (c) 2026 Zhengqing Zhou and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhengqing Zhou, GPT-5.6 Pro
-/
-- Vendored from LeanPool/lean-pool (https://github.com/LeanPool/lean-pool),
-- file LeanPool/Feige/ConditionalProductKernel.lean at commit 9decab6341e6b0fd82bd7f9763a5dd7a9ce8778d, Apache-2.0 (see LICENSE in this folder).
-- Changes: import paths renamed from `LeanPool.Feige.*` to `Feige.Vendor.LeanPool.*`.
-- Portability (Left to Solve CI, Lean v4.33.1): `add_apply`/`smul_apply` qualified as `Measure.*`,
-- `ite_eq_left/right` replaced by `if_pos/if_neg`, and small elaboration fixes where needed.

module

public import Feige.Vendor.LeanPool.ProductTwoPointKernel

/-!
# Conditional product law of the recursive augmented kernel

The recursively measurable kernel used for the finite mixture construction
has, at every fixed latent parameter vector, exactly the ordinary finite
product of the selected one-coordinate laws.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace Feige

noncomputable section

theorem recursiveAugmentedKernel_apply_eq_conditionalProduct
    (n : ℕ) (p : Fin n → AugmentedTwoPointParams) :
    recursiveAugmentedKernel n p = augmentedConditionalProduct p := by
  induction n with
  | zero =>
      unfold recursiveAugmentedKernel augmentedConditionalProduct
      rw [Measure.pi_of_empty]
      congr
  | succ n ih =>
      unfold recursiveAugmentedKernel augmentedConditionalProduct
      rw [Kernel.map_apply _ (finHeadTailEquiv ℝ n).symm.measurable]
      rw [Kernel.comap_apply]
      rw [Kernel.parallelComp_apply]
      change
        Measure.map (finHeadTailEquiv ℝ n).symm
          ((augmentedTwoPointKernel (p 0)).prod
            (recursiveAugmentedKernel n
              (fun i : Fin n ↦ p (Fin.succ i)))) =
          Measure.pi (fun i : Fin (n + 1) ↦ augmentedTwoPointKernel (p i))
      rw [ih (fun i : Fin n ↦ p (Fin.succ i))]
      unfold augmentedConditionalProduct
      exact
        (measurePreserving_piFinSuccAbove
          (fun i : Fin (n + 1) ↦ augmentedTwoPointKernel (p i)) 0).symm.map_eq

end

end Feige
