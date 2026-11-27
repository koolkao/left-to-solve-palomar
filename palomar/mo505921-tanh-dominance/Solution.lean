/-
Copyright 2026 Ming-Chih Kao. Licensed under the Apache License, Version 2.0;
see the LICENSE file at the root of this repository.
-/
module

public import TanhDominance

/-!
# Solution

Proves the four declarations stated in `Challenge.lean` from the proof development in
`TanhDominance/` (`Proof.lean`: the source repository's proof; `Ioo.lean`: the restriction of the
comparison to `t ∈ (-1, 1)`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Real
open scoped ENNReal NNReal

namespace MO505921

theorem mo505921_Ioo {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {gX gY gZ : ℝ≥0} (hgX : gX ≠ 0) (hgY : gY ≠ 0) (hgZ : gZ ≠ 0) {X Y Z : Ω → ℝ}
    (hX : HasLaw X (gaussianReal gX gX) P) (hY : HasLaw Y (gaussianReal gY gY) P)
    (hZ : HasLaw Z (gaussianReal gZ gZ) P) (hYZ : IndepFun Y Z P) :
    (¬ ∀ t ∈ Ioo (-1 : ℝ) 1,
        cdf (P.map fun ω => tanh (Y ω) * tanh (Z ω)) t ≤ cdf (P.map fun ω => tanh (X ω)) t) ∧
      (¬ ∀ t ∈ Ioo (-1 : ℝ) 1,
        cdf (P.map fun ω => tanh (X ω)) t ≤ cdf (P.map fun ω => tanh (Y ω) * tanh (Z ω)) t) :=
  TanhDominance.mo505921_Ioo hgX hgY hgZ hX hY hZ hYZ

theorem mo505921 {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {gX gY gZ : ℝ≥0} (hgX : gX ≠ 0) (hgY : gY ≠ 0) (hgZ : gZ ≠ 0) {X Y Z : Ω → ℝ}
    (hX : HasLaw X (gaussianReal gX gX) P) (hY : HasLaw Y (gaussianReal gY gY) P)
    (hZ : HasLaw Z (gaussianReal gZ gZ) P) (hYZ : IndepFun Y Z P) :
    (¬ ∀ t, cdf (P.map fun ω => tanh (Y ω) * tanh (Z ω)) t ≤ cdf (P.map fun ω => tanh (X ω)) t) ∧
      (¬ ∀ t, cdf (P.map fun ω => tanh (X ω)) t ≤
        cdf (P.map fun ω => tanh (Y ω) * tanh (Z ω)) t) :=
  TanhDominance.mo505921 hgX hgY hgZ hX hY hZ hYZ

theorem mo505921_iIndep {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {gX gY gZ : ℝ≥0} (hgX : gX ≠ 0) (hgY : gY ≠ 0) (hgZ : gZ ≠ 0) {X Y Z : Ω → ℝ}
    (hX : HasLaw X (gaussianReal gX gX) P) (hY : HasLaw Y (gaussianReal gY gY) P)
    (hZ : HasLaw Z (gaussianReal gZ gZ) P) (hXYZ : iIndepFun ![X, Y, Z] P) :
    (¬ ∀ t, cdf (P.map fun ω => tanh (Y ω) * tanh (Z ω)) t ≤ cdf (P.map fun ω => tanh (X ω)) t) ∧
      (¬ ∀ t, cdf (P.map fun ω => tanh (X ω)) t ≤
        cdf (P.map fun ω => tanh (Y ω) * tanh (Z ω)) t) :=
  TanhDominance.mo505921_iIndep hgX hgY hgZ hX hY hZ hXYZ

theorem no_gX_Ioo (gY gZ : ℝ≥0) (hY : gY ≠ 0) (hZ : gZ ≠ 0) :
    ¬ ∃ gX : ℝ≥0, gX ≠ 0 ∧ ∀ t ∈ Ioo (-1 : ℝ) 1,
      cdf (((gaussianReal gY gY).prod (gaussianReal gZ gZ)).map fun p => tanh p.1 * tanh p.2) t ≤
        cdf ((gaussianReal gX gX).map tanh) t :=
  TanhDominance.no_gX_Ioo gY gZ hY hZ

end MO505921

