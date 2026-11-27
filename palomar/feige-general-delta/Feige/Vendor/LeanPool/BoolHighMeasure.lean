/-
Copyright (c) 2026 Zhengqing Zhou and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhengqing Zhou, GPT-5.6 Pro
-/
-- Vendored from LeanPool/lean-pool (https://github.com/LeanPool/lean-pool),
-- file LeanPool/Feige/TwoPointProductLaw.lean at commit 9decab6341e6b0fd82bd7f9763a5dd7a9ce8778d, Apache-2.0 (see LICENSE in this folder).
-- Changes: only `boolHighMeasure`, `boolHighMeasure_isProbability`, `boolHighMeasure_singleton`
-- and `map_boolHighMeasure_twoPoint` are kept; imports adjusted accordingly.
-- Portability (Left to Solve CI, Lean v4.33.1): `add_apply`/`smul_apply` qualified as `Measure.*`,
-- `ite_eq_left/right` replaced by `if_pos/if_neg`, and small elaboration fixes where needed.
module

public import Feige.Vendor.LeanPool.TwoPointMixture
public import Feige.Vendor.LeanPool.TwoPointParameters

/-!
# Bernoulli laws on `Bool` (excerpt of LeanPool's `TwoPointProductLaw.lean`)
-/

@[expose] public section

open scoped BigOperators ENNReal
open Set MeasureTheory ProbabilityTheory

namespace Feige

noncomputable section

/-- The Bernoulli law assigning mass `p` to `true`. -/
def boolHighMeasure (p : ℝ) : Measure Bool :=
  ENNReal.ofReal (1 - p) • Measure.dirac false +
    ENNReal.ofReal p • Measure.dirac true

theorem boolHighMeasure_isProbability {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    IsProbabilityMeasure (boolHighMeasure p) := by
  constructor
  simp [boolHighMeasure, ← ENNReal.ofReal_add (sub_nonneg.mpr hp1) hp0]

theorem boolHighMeasure_singleton (p : ℝ) (b : Bool) :
    boolHighMeasure p {b} =
      ENNReal.ofReal (if b then p else 1 - p) := by
  cases b <;> simp [boolHighMeasure]

theorem map_boolHighMeasure_twoPoint
    {γ β : ℝ} (hγ : 0 ≤ γ) (hβ : 0 < β) :
    Measure.map
        (fun b : Bool ↦ if b then highValue β else lowValue γ)
        (boolHighMeasure (highProbability γ β)) =
      twoPointMeasure (lowValue γ) (highValue β) := by
  have hsum : γ + β ≠ 0 :=
    (add_pos_of_nonneg_of_pos hγ hβ).ne'
  have hlo :
      twoPointLowerWeight (lowValue γ) (highValue β) =
        1 - highProbability γ β := by
    rw [show twoPointLowerWeight (lowValue γ) (highValue β) =
        β / (γ + β) by
      unfold twoPointLowerWeight lowValue highValue
      congr 1 <;> ring]
    exact (one_sub_highProbability hsum).symm
  have hhi :
      twoPointUpperWeight (lowValue γ) (highValue β) =
        highProbability γ β := by
    unfold twoPointUpperWeight lowValue highValue highProbability
    congr 1 <;> ring
  rw [boolHighMeasure, Measure.map_add, Measure.map_smul,
    Measure.map_smul, Measure.map_dirac, Measure.map_dirac]
  · simp [twoPointMeasure, hlo, hhi]
  all_goals fun_prop


end

end Feige
