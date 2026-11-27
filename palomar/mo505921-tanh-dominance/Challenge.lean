/-
Copyright 2026 Ming-Chih Kao. Licensed under the Apache License, Version 2.0;
see the LICENSE file at the root of this repository.
-/
module

public import Mathlib

/-!
# MathOverflow 505921: `tanh Y · tanh Z` and `tanh X` are never stochastically ordered

MathOverflow question 505921 (tituf, 14 December 2025, <https://mathoverflow.net/questions/505921>,
CC BY-SA 4.0) asks:

> Let `X, Y, Z` be independent Gaussian r.v.'s with mean = variance. Let's denote these
> mean/variance parameters by `g_X, g_Y, g_Z > 0` respectively. Set `U := tanh X`,
> `V := tanh Y tanh Z`. **Question.** Given `g_Y, g_Z > 0`, is there `g_X > 0` (dependent on
> `g_Y, g_Z`) such that `tanh Y tanh Z ⪰_st tanh X`? Here `⪰_st` denotes stochastic dominance.
> That is `F_U(t) ≥ F_V(t)` for every `t ∈ (-1, 1)` (note the reversed inequality) where
> `F_T(t) := P(T ≤ t)` denotes the c.d.f. of `T`.

The answer, proved in `Solution.lean`, is **no**, for every `g_Y, g_Z > 0`, and moreover the two variables are
never stochastically ordered in either direction (Ming-Chih Kao, 2026,
<https://github.com/koolkao/mo505921-tanh-dominance>).

Vocabulary (all from Mathlib): `gaussianReal m v` is the normal law with mean `m` and variance
`v`, so `gaussianReal g g` is the law "mean = variance = `g`"; the parameters are `ℝ≥0` and
`g ≠ 0` means `g > 0`. `HasLaw X μ P` says that `X` is a.e.-measurable and its law under `P` is
`μ`. `cdf (P.map T) t` is `F_T(t) = P(T ≤ t)`. Mathlib has no definition of the usual stochastic
order, so dominance is written out as the pointwise comparison of c.d.f.s, which is the question's
own definition.

* `mo505921_Ioo`: for any realization (`Y`, `Z` independent; `X` has its Gaussian law but
  may be coupled with `(Y, Z)` in any way),
  neither `F_V ≤ F_U` on `(-1, 1)` nor `F_U ≤ F_V` on `(-1, 1)`.
* `mo505921`, `mo505921_iIndep`: the same with the c.d.f.s compared on all of `ℝ` (equivalent,
  since `U` and `V` take values in `(-1, 1)`), with `Y, Z` independent, respectively with `X, Y, Z`
  jointly independent as in the question.
* `no_gX_Ioo`: the question exactly as asked, at the level of laws: given `g_Y, g_Z > 0` there is
  no `g_X > 0` with `F_U(t) ≥ F_V(t)` for all `t ∈ (-1, 1)`, where `V` has the law of
  `tanh Y · tanh Z` under the product law `N(g_Y, g_Y) ⊗ N(g_Z, g_Z)`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Real
open scoped NNReal

namespace MO505921

/-- **MO 505921, on the question's range.** Let `X ~ N(gX, gX)`, `Y ~ N(gY, gY)`,
`Z ~ N(gZ, gZ)` (mean = variance > 0) on one probability space, with `Y` and `Z` independent.
Then `V = tanh Y · tanh Z` does not dominate `U = tanh X` (`F_V(t) ≤ F_U(t)` fails for some
`t ∈ (-1, 1)`), and `U` does not dominate `V` either. -/
theorem mo505921_Ioo {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {gX gY gZ : ℝ≥0} (hgX : gX ≠ 0) (hgY : gY ≠ 0) (hgZ : gZ ≠ 0) {X Y Z : Ω → ℝ}
    (hX : HasLaw X (gaussianReal gX gX) P) (hY : HasLaw Y (gaussianReal gY gY) P)
    (hZ : HasLaw Z (gaussianReal gZ gZ) P) (hYZ : IndepFun Y Z P) :
    (¬ ∀ t ∈ Ioo (-1 : ℝ) 1,
        cdf (P.map fun ω => tanh (Y ω) * tanh (Z ω)) t ≤ cdf (P.map fun ω => tanh (X ω)) t) ∧
      (¬ ∀ t ∈ Ioo (-1 : ℝ) 1,
        cdf (P.map fun ω => tanh (X ω)) t ≤ cdf (P.map fun ω => tanh (Y ω) * tanh (Z ω)) t) := by
  sorry

/-- **MO 505921, c.d.f.s compared on all of `ℝ`.** Same hypotheses as `mo505921_Ioo`. -/
theorem mo505921 {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {gX gY gZ : ℝ≥0} (hgX : gX ≠ 0) (hgY : gY ≠ 0) (hgZ : gZ ≠ 0) {X Y Z : Ω → ℝ}
    (hX : HasLaw X (gaussianReal gX gX) P) (hY : HasLaw Y (gaussianReal gY gY) P)
    (hZ : HasLaw Z (gaussianReal gZ gZ) P) (hYZ : IndepFun Y Z P) :
    (¬ ∀ t, cdf (P.map fun ω => tanh (Y ω) * tanh (Z ω)) t ≤ cdf (P.map fun ω => tanh (X ω)) t) ∧
      (¬ ∀ t, cdf (P.map fun ω => tanh (X ω)) t ≤
        cdf (P.map fun ω => tanh (Y ω) * tanh (Z ω)) t) := by
  sorry

/-- The same with `X, Y, Z` jointly independent, as in the question. -/
theorem mo505921_iIndep {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {gX gY gZ : ℝ≥0} (hgX : gX ≠ 0) (hgY : gY ≠ 0) (hgZ : gZ ≠ 0) {X Y Z : Ω → ℝ}
    (hX : HasLaw X (gaussianReal gX gX) P) (hY : HasLaw Y (gaussianReal gY gY) P)
    (hZ : HasLaw Z (gaussianReal gZ gZ) P) (hXYZ : iIndepFun ![X, Y, Z] P) :
    (¬ ∀ t, cdf (P.map fun ω => tanh (Y ω) * tanh (Z ω)) t ≤ cdf (P.map fun ω => tanh (X ω)) t) ∧
      (¬ ∀ t, cdf (P.map fun ω => tanh (X ω)) t ≤
        cdf (P.map fun ω => tanh (Y ω) * tanh (Z ω)) t) := by
  sorry

/-- **The question as asked.** Given `gY, gZ > 0`, there is no `gX > 0` such that
`F_U(t) ≥ F_V(t)` for every `t ∈ (-1, 1)`, where `U = tanh X` with `X ~ N(gX, gX)` and
`V = tanh Y · tanh Z` with `(Y, Z) ~ N(gY, gY) ⊗ N(gZ, gZ)` (independent). -/
theorem no_gX_Ioo (gY gZ : ℝ≥0) (hY : gY ≠ 0) (hZ : gZ ≠ 0) :
    ¬ ∃ gX : ℝ≥0, gX ≠ 0 ∧ ∀ t ∈ Ioo (-1 : ℝ) 1,
      cdf (((gaussianReal gY gY).prod (gaussianReal gZ gZ)).map fun p => tanh p.1 * tanh p.2) t ≤
        cdf ((gaussianReal gX gX).map tanh) t := by
  sorry

end MO505921
