/-
Copyright (c) 2026 Zhengqing Zhou and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhengqing Zhou, GPT-5.6 Pro
-/
-- Vendored from LeanPool/lean-pool (https://github.com/LeanPool/lean-pool),
-- file LeanPool/Feige/TwoPoint.lean at commit 9decab6341e6b0fd82bd7f9763a5dd7a9ce8778d, Apache-2.0 (see LICENSE in this folder).
-- Changes: only the `Parameters` section is kept (the Boolean-lattice / Dirichlet-statistic part
-- is not needed here), so the import of `LeanPool.Feige.KStatistic` is replaced by Mathlib.
-- Portability (Left to Solve CI, Lean v4.33.1): `add_apply`/`smul_apply` qualified as `Measure.*`,
-- `ite_eq_left/right` replaced by `if_pos/if_neg`, and small elaboration fixes where needed.
module

public import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Mean-one two-point parameters (excerpt of LeanPool's `TwoPoint.lean`)
-/

@[expose] public section

namespace Feige

section Parameters

/-- Probability of the high value in a mean-one two-point law. -/
noncomputable def highProbability (γ β : ℝ) : ℝ :=
  γ / (γ + β)

/-- The low value in the mean-one two-point parametrization. -/
def lowValue (γ : ℝ) : ℝ := 1 - γ

/-- The high value in the mean-one two-point parametrization. -/
def highValue (β : ℝ) : ℝ := 1 + β

theorem highProbability_nonneg {γ β : ℝ} (hγ : 0 ≤ γ) (hβ : 0 < β) :
    0 ≤ highProbability γ β := by
  exact div_nonneg hγ (add_pos_of_nonneg_of_pos hγ hβ).le

theorem highProbability_le_one {γ β : ℝ} (hγ : 0 ≤ γ) (hβ : 0 < β) :
    highProbability γ β ≤ 1 := by
  rw [highProbability, div_le_one (add_pos_of_nonneg_of_pos hγ hβ)]
  linarith

/-- The complementary probability in symmetric form. -/
theorem one_sub_highProbability {γ β : ℝ} (h : γ + β ≠ 0) :
    1 - highProbability γ β = β / (γ + β) := by
  rw [highProbability]
  field_simp
  ring

/-- The parametrized two-point law has mean exactly one. -/
theorem twoPoint_mean_one {γ β : ℝ} (h : γ + β ≠ 0) :
    highProbability γ β * highValue β +
        (1 - highProbability γ β) * lowValue γ = 1 := by
  rw [one_sub_highProbability h]
  simp only [highProbability, highValue, lowValue]
  field_simp
  ring

end Parameters

end Feige
