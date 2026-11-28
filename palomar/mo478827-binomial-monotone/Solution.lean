/-
Copyright 2026 Ming-Chih Kao. Licensed under the Apache License, Version 2.0;
see the LICENSE file at the root of this repository.
-/
module

public import BinomialMonotone

/-!
# Solution

Proves the declarations stated in `Challenge.lean` from `BinomialMonotone/` (the source repository's
`MO478827.lean` and `Check.lean`), whose definitions `binPMF`, `f`, `event` and `prob` unfold to the
written-out statements.
-/

@[expose] public section

open Finset MeasureTheory ProbabilityTheory unitInterval

namespace MO478827

/-- **Theorem 1.** For `k ≥ 1`, `0 < g < 1` and `0 < l ≤ (1+g)/2`, `f_k` is strictly decreasing on `[0,1]`. -/
theorem theorem1 (k : ℕ) (hk : 1 ≤ k) (g l : ℝ) (hg0 : 0 < g) (hg1 : g < 1) (hl0 : 0 < l)
    (hl2 : 2 * l ≤ 1 + g) :
    StrictAntiOn (fun p : ℝ => ∑ x ∈ range (k + 1), ∑ y ∈ range (k + 1),
      if (1 + g) * (x : ℝ) + l * (y : ℝ) > (k : ℝ) then
        (((k).choose x : ℝ) * (1 - p) ^ x * (1 - (1 - p)) ^ (k - x)) *
          (((k).choose y : ℝ) * p ^ y * (1 - p) ^ (k - y))
      else 0) (Set.Icc 0 1) :=
  BinomialMonotoneCheck.theorem1 k hk g l hg0 hg1 hl0 hl2

/-- **The question, as asked** (`g, l ∈ (0,1)`, `g ≥ l`): `f_k` is strictly decreasing on `[0,1]`. -/
theorem answer (k : ℕ) (hk : 1 ≤ k) (g l : ℝ) (hg0 : 0 < g) (hg1 : g < 1) (hl0 : 0 < l)
    (hl1 : l < 1) (hlg : g ≥ l) :
    StrictAntiOn (fun p : ℝ => ∑ x ∈ range (k + 1), ∑ y ∈ range (k + 1),
      if (1 + g) * (x : ℝ) + l * (y : ℝ) > (k : ℝ) then
        (((k).choose x : ℝ) * (1 - p) ^ x * (1 - (1 - p)) ^ (k - x)) *
          (((k).choose y : ℝ) * p ^ y * (1 - p) ^ (k - y))
      else 0) (Set.Icc 0 1) :=
  BinomialMonotoneCheck.answer k hk g l hg0 hg1 hl0 hl1 hlg

/-- **Proposition 2.** For `k = 10`, `g = 1/7`, `l = 99/100`, `f_k` is not even non-increasing on `[0,1]`. -/
theorem prop2_not_antitone :
    ¬ AntitoneOn (fun p : ℝ => ∑ x ∈ range ((10 : ℕ) + 1), ∑ y ∈ range ((10 : ℕ) + 1),
      if (1 + (1 / 7 : ℝ)) * (x : ℝ) + (99 / 100 : ℝ) * (y : ℝ) > ((10 : ℕ) : ℝ) then
        ((((10 : ℕ)).choose x : ℝ) * (1 - p) ^ x * (1 - (1 - p)) ^ ((10 : ℕ) - x)) *
          ((((10 : ℕ)).choose y : ℝ) * p ^ y * (1 - p) ^ ((10 : ℕ) - y))
      else 0) (Set.Icc 0 1) :=
  BinomialMonotoneCheck.prop2_not_antitone

/-- Strict (or even weak) decrease does not hold for all `g, l ∈ (0,1)` and all `k ≥ 1`. -/
theorem fact1_fails :
    ¬ ∀ k : ℕ, 1 ≤ k → ∀ g l : ℝ, 0 < g → g < 1 → 0 < l → l < 1 →
      AntitoneOn (fun p : ℝ => ∑ x ∈ range (k + 1), ∑ y ∈ range (k + 1),
      if (1 + g) * (x : ℝ) + l * (y : ℝ) > (k : ℝ) then
        (((k).choose x : ℝ) * (1 - p) ^ x * (1 - (1 - p)) ^ (k - x)) *
          (((k).choose y : ℝ) * p ^ y * (1 - p) ^ (k - y))
      else 0) (Set.Icc 0 1) :=
  BinomialMonotoneCheck.fact1_fails

/-- For any independent random variables `X ~ Bin(k, 1-p)` and `Y ~ Bin(k, p)` on a probability space, `P((1+g) X + l Y > k)` is the product-measure probability used below. -/
theorem prob_of_indep {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X Y : Ω → ℕ) (k : ℕ) (p : I) (hX : HasLaw X (binomial k (σ p)) P) (hY : HasLaw Y (binomial k p) P)
    (hXY : IndepFun X Y P) (g l : ℝ) :
    P.real {ω | (1 + g) * (X ω : ℝ) + l * (Y ω : ℝ) > (k : ℝ)} =
      ((binomial k (σ p)).prod (binomial k p)).real
        {z : ℕ × ℕ | (1 + g) * (z.1 : ℝ) + l * (z.2 : ℝ) > (k : ℝ)} :=
  BinomialMonotoneCheck.prob_of_indep P X Y k p hX hY hXY g l

/-- **Theorem 1, measure form** (Mathlib's binomial measure, `p : unitInterval`, `σ p = 1 - p`). -/
theorem theorem1_measure (k : ℕ) (hk : 1 ≤ k) (g l : ℝ) (hg0 : 0 < g) (hg1 : g < 1) (hl0 : 0 < l)
    (hl2 : 2 * l ≤ 1 + g) :
    StrictAnti (fun p : I => ((binomial k (σ p)).prod (binomial k p)).real
      {z : ℕ × ℕ | (1 + g) * (z.1 : ℝ) + l * (z.2 : ℝ) > (k : ℝ)}) :=
  BinomialMonotoneCheck.theorem1_measure k hk g l hg0 hg1 hl0 hl2

/-- **The question, measure form.** -/
theorem answer_measure (k : ℕ) (hk : 1 ≤ k) (g l : ℝ) (hg0 : 0 < g) (hg1 : g < 1) (hl0 : 0 < l)
    (hl1 : l < 1) (hlg : g ≥ l) :
    StrictAnti (fun p : I => ((binomial k (σ p)).prod (binomial k p)).real
      {z : ℕ × ℕ | (1 + g) * (z.1 : ℝ) + l * (z.2 : ℝ) > (k : ℝ)}) :=
  BinomialMonotoneCheck.answer_measure k hk g l hg0 hg1 hl0 hl1 hlg

end MO478827
