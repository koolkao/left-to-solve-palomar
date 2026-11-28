/-
Copyright 2026 Ming-Chih Kao. Licensed under the Apache License, Version 2.0;
see the LICENSE file at the root of this repository.
-/
module

public import Mathlib

/-!
# MathOverflow 478827: `P((1+g) X + l Y > k)` is strictly decreasing in `p` when `2l ≤ 1+g`

MathOverflow question 478827 ("Probability of sum of i.i.d. random variables being positive", EGT,
14 September 2024, <https://mathoverflow.net/questions/478827>, CC BY-SA 4.0) asks:

> Let g, l ∈ (0,1), g ≥ l, and p ∈ [0,1]. Let X(k,1-p) be a random variable with binomial distribution with
> parameters k and 1-p. Let Y(k,p) be a random variable with binomial distribution with parameters k and p. It is
> given that X(k,1-p) and Y(k,p) are independent. Consider the function given by
> f_k(p) = P((1+g) X(k,1-p) + l Y(k,p) > k).
> Can we say that the function f_k(p) is strictly decreasing in p? Even if we can show this for g = l that would
> be great.

The answer, proved in `Solution.lean` (Ming-Chih Kao, 2026, <https://github.com/koolkao/mo478827-binomial-monotone>):
yes, for every `k ≥ 1` and all `0 < g < 1`, `0 < l ≤ (1+g)/2` (which covers the question's `l ≤ g`); but not for
all `g, l ∈ (0,1)` (Proposition 2: `k = 10`, `g = 1/7`, `l = 99/100`).

Vocabulary: `f_k(p)` is written out as the double sum of the product of the two binomial probability mass
functions `C(k,x) (1-p)^x p^(k-x)` (written `(1 - (1 - p))^(k - x)`) and `C(k,y) p^y (1-p)^(k-y)` over the
event `(1+g) x + l y > k`. The measure forms use Mathlib's `ProbabilityTheory.binomial k p` (the law of the
number of successes in `k` independent Bernoulli(p) trials, `p : unitInterval`, `σ p = 1 - p`) and the product
measure, which is the joint law of independent `X, Y` by `prob_of_indep`.
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
  sorry

/-- **The question, as asked** (`g, l ∈ (0,1)`, `g ≥ l`): `f_k` is strictly decreasing on `[0,1]`. -/
theorem answer (k : ℕ) (hk : 1 ≤ k) (g l : ℝ) (hg0 : 0 < g) (hg1 : g < 1) (hl0 : 0 < l)
    (hl1 : l < 1) (hlg : g ≥ l) :
    StrictAntiOn (fun p : ℝ => ∑ x ∈ range (k + 1), ∑ y ∈ range (k + 1),
      if (1 + g) * (x : ℝ) + l * (y : ℝ) > (k : ℝ) then
        (((k).choose x : ℝ) * (1 - p) ^ x * (1 - (1 - p)) ^ (k - x)) *
          (((k).choose y : ℝ) * p ^ y * (1 - p) ^ (k - y))
      else 0) (Set.Icc 0 1) :=
  sorry

/-- **Proposition 2.** For `k = 10`, `g = 1/7`, `l = 99/100`, `f_k` is not even non-increasing on `[0,1]`. -/
theorem prop2_not_antitone :
    ¬ AntitoneOn (fun p : ℝ => ∑ x ∈ range ((10 : ℕ) + 1), ∑ y ∈ range ((10 : ℕ) + 1),
      if (1 + (1 / 7 : ℝ)) * (x : ℝ) + (99 / 100 : ℝ) * (y : ℝ) > ((10 : ℕ) : ℝ) then
        ((((10 : ℕ)).choose x : ℝ) * (1 - p) ^ x * (1 - (1 - p)) ^ ((10 : ℕ) - x)) *
          ((((10 : ℕ)).choose y : ℝ) * p ^ y * (1 - p) ^ ((10 : ℕ) - y))
      else 0) (Set.Icc 0 1) :=
  sorry

/-- Strict (or even weak) decrease does not hold for all `g, l ∈ (0,1)` and all `k ≥ 1`. -/
theorem fact1_fails :
    ¬ ∀ k : ℕ, 1 ≤ k → ∀ g l : ℝ, 0 < g → g < 1 → 0 < l → l < 1 →
      AntitoneOn (fun p : ℝ => ∑ x ∈ range (k + 1), ∑ y ∈ range (k + 1),
      if (1 + g) * (x : ℝ) + l * (y : ℝ) > (k : ℝ) then
        (((k).choose x : ℝ) * (1 - p) ^ x * (1 - (1 - p)) ^ (k - x)) *
          (((k).choose y : ℝ) * p ^ y * (1 - p) ^ (k - y))
      else 0) (Set.Icc 0 1) :=
  sorry

/-- For any independent random variables `X ~ Bin(k, 1-p)` and `Y ~ Bin(k, p)` on a probability space, `P((1+g) X + l Y > k)` is the product-measure probability used below. -/
theorem prob_of_indep {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X Y : Ω → ℕ) (k : ℕ) (p : I) (hX : HasLaw X (binomial k (σ p)) P) (hY : HasLaw Y (binomial k p) P)
    (hXY : IndepFun X Y P) (g l : ℝ) :
    P.real {ω | (1 + g) * (X ω : ℝ) + l * (Y ω : ℝ) > (k : ℝ)} =
      ((binomial k (σ p)).prod (binomial k p)).real
        {z : ℕ × ℕ | (1 + g) * (z.1 : ℝ) + l * (z.2 : ℝ) > (k : ℝ)} :=
  sorry

/-- **Theorem 1, measure form** (Mathlib's binomial measure, `p : unitInterval`, `σ p = 1 - p`). -/
theorem theorem1_measure (k : ℕ) (hk : 1 ≤ k) (g l : ℝ) (hg0 : 0 < g) (hg1 : g < 1) (hl0 : 0 < l)
    (hl2 : 2 * l ≤ 1 + g) :
    StrictAnti (fun p : I => ((binomial k (σ p)).prod (binomial k p)).real
      {z : ℕ × ℕ | (1 + g) * (z.1 : ℝ) + l * (z.2 : ℝ) > (k : ℝ)}) :=
  sorry

/-- **The question, measure form.** -/
theorem answer_measure (k : ℕ) (hk : 1 ≤ k) (g l : ℝ) (hg0 : 0 < g) (hg1 : g < 1) (hl0 : 0 < l)
    (hl1 : l < 1) (hlg : g ≥ l) :
    StrictAnti (fun p : I => ((binomial k (σ p)).prod (binomial k p)).real
      {z : ℕ × ℕ | (1 + g) * (z.1 : ℝ) + l * (z.2 : ℝ) > (k : ℝ)}) :=
  sorry

end MO478827
