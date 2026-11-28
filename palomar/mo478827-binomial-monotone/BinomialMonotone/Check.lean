/-
Copyright 2026 Ming-Chih Kao. Licensed under the Apache License, Version 2.0;
see the LICENSE file at the root of this repository.
-/
module

public import BinomialMonotone.Proof

/-! Port: copied from `Check.lean` of github.com/koolkao/mo478827-binomial-monotone (commit
3d17061d300988d21b3b1f23cf4bf91b6129dc62, v1.0.0, Lean v4.36.0, same Mathlib) and put into the module system:
the `module` header, `public import`, a public section, and the namespaces `MO478827` and `MO478827Check`
renamed `BinomialMonotone` and `BinomialMonotoneCheck` so that `Solution.lean` can state the compared
theorems under the names `MO478827.*`; the `#print axioms` report is dropped. The mathematics and the
proofs are unchanged. -/

@[expose] public section

/-!
# Independent check: MathOverflow 478827 restated from the question text

Question (MathOverflow 478827, "Probability of sum of i.i.d. random variables being positive", asked by EGT
(MathOverflow user 151054) on 14 September 2024; CC BY-SA 4.0):

> Let g, l ∈ (0,1), g ≥ l, and p ∈ [0,1]. Let X(k,1-p) be a random variable with binomial distribution with
> parameters k and 1-p. Let Y(k,p) be a random variable with binomial distribution with parameters k and p. It is
> given that X(k,1-p) and Y(k,p) are independent. Consider the function given by
> f_k(p) = P((1+g) X(k,1-p) + l Y(k,p) > k).
> Can we say that the function f_k(p) is strictly decreasing in p? Even if we can show this for g = l that would
> be great.

This file restates the question twice, without the vocabulary of `BinomialMonotone.lean`:

1. `binPMF` and `f` write the binomial probabilities and the probability of the event out by hand
   (independence = product of the two probability mass functions). `f_eq_fk` proves that `f` is the function
   `BinomialMonotone.fk` of the proof, and the theorems below are then stated for `f`.
2. `prob` is the same probability computed from Mathlib's binomial *measure* `ProbabilityTheory.binomial`
   (`Bin(k, p)`, the law of the number of successes among `k` independent Bernoulli(p) trials), and
   `prob_of_indep` evaluates it for any independent random variables `X, Y` with these laws on any
   probability space. `prob_eq_f` proves that it agrees with `f`.

Theorem 1 (`theorem1`, `theorem1_measure`), the answer to the question (`answer`, `answer_measure`) and
Proposition 2 (`prop2_values`, `prop2_not_antitone`, `fact1_fails`) are stated against these definitions.
-/

open Finset

noncomputable section

namespace BinomialMonotoneCheck

/-! ## 1. The explicit binomial form -/

/-- `P(B = j)` for `B ~ Bin(k, q)`: `C(k,j) q^j (1-q)^(k-j)`. -/
def binPMF (k : ℕ) (q : ℝ) (j : ℕ) : ℝ := (k.choose j : ℝ) * q ^ j * (1 - q) ^ (k - j)

/-- `f_k(p) = P((1+g) X + l Y > k)` for independent `X ~ Bin(k, 1-p)` and `Y ~ Bin(k, p)`. -/
def f (k : ℕ) (g l p : ℝ) : ℝ :=
  ∑ x ∈ range (k + 1), ∑ y ∈ range (k + 1),
    if (1 + g) * (x : ℝ) + l * (y : ℝ) > (k : ℝ) then binPMF k (1 - p) x * binPMF k p y else 0

/-- `binPMF k q` is a probability mass function on `{0, …, k}` when `0 ≤ q ≤ 1` (so `f` is a genuine
probability, not a junk value). -/
theorem binPMF_isPMF (k : ℕ) (q : ℝ) (h0 : 0 ≤ q) (h1 : q ≤ 1) :
    (∀ j, 0 ≤ binPMF k q j) ∧ ∑ j ∈ range (k + 1), binPMF k q j = 1 := by
  refine ⟨fun j => ?_, ?_⟩
  · unfold binPMF
    have : 0 ≤ 1 - q := by linarith
    positivity
  · have h := (add_pow q (1 - q) k).symm
    rw [add_sub_cancel, one_pow] at h
    rw [← h]
    exact sum_congr rfl fun j _ => by unfold binPMF; ring

/-- The equivalence with the function used in the proof. -/
theorem f_eq_fk (k : ℕ) (g l : ℝ) : f k g l = BinomialMonotone.fk k g l := by
  funext p
  unfold f BinomialMonotone.fk binPMF
  refine sum_congr rfl fun x _ => sum_congr rfl fun y _ => ?_
  rw [sub_sub_cancel]

/-- **Theorem 1.** For `k ≥ 1`, `0 < g < 1` and `0 < l ≤ (1+g)/2`, `f_k` is strictly decreasing on `[0,1]`. -/
theorem theorem1 (k : ℕ) (hk : 1 ≤ k) (g l : ℝ) (hg0 : 0 < g) (hg1 : g < 1) (hl0 : 0 < l)
    (hl2 : 2 * l ≤ 1 + g) : StrictAntiOn (f k g l) (Set.Icc 0 1) := by
  rw [f_eq_fk]
  exact BinomialMonotone.fk_strictAnti k hk g l hg0 hg1 hl0 hl2

/-- **The question, as asked** (`g, l ∈ (0,1)`, `g ≥ l`): yes, `f_k` is strictly decreasing on `[0,1]`. -/
theorem answer (k : ℕ) (hk : 1 ≤ k) (g l : ℝ) (hg0 : 0 < g) (hg1 : g < 1) (hl0 : 0 < l) (hl1 : l < 1)
    (hlg : g ≥ l) : StrictAntiOn (f k g l) (Set.Icc 0 1) :=
  theorem1 k hk g l hg0 hg1 hl0 (by linarith)

/-! ## 2. Proposition 2: the hypothesis `2l ≤ 1+g` cannot simply be dropped

`k = 10`, `g = 1/7`, `l = 99/100` (both in `(0,1)`, but `l > g` and `2l > 1+g`). -/

theorem prop2_half : f 10 (1 / 7) (99 / 100) (1 / 2) = 617125 / 1048576 := by
  simp only [f, binPMF, sum_range_succ, sum_range_zero]
  norm_num [Nat.choose]

theorem prop2_three_quarters : f 10 (1 / 7) (99 / 100) (3 / 4) = 659148839341 / 1099511627776 := by
  simp only [f, binPMF, sum_range_succ, sum_range_zero]
  norm_num [Nat.choose]

theorem prop2_values : f 10 (1 / 7) (99 / 100) (1 / 2) < f 10 (1 / 7) (99 / 100) (3 / 4) := by
  rw [prop2_half, prop2_three_quarters]; norm_num

theorem prop2_not_antitone : ¬ AntitoneOn (f 10 (1 / 7) (99 / 100)) (Set.Icc 0 1) := by
  intro h
  have := h (a := 1 / 2) (b := 3 / 4) ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩ (by norm_num)
  linarith [prop2_values]

/-- Strict (or even weak) decrease does **not** hold for all `g, l ∈ (0,1)` and all `k ≥ 1`. -/
theorem fact1_fails : ¬ ∀ k : ℕ, 1 ≤ k → ∀ g l : ℝ, 0 < g → g < 1 → 0 < l → l < 1 →
    AntitoneOn (f k g l) (Set.Icc 0 1) := fun h =>
  prop2_not_antitone (h 10 (by norm_num) (1 / 7) (99 / 100) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num))

/-! ## 3. The same probability from Mathlib's binomial distribution

`p : unitInterval` is a parameter in `[0,1]`, and `unitInterval.symm p = σ p` is `1 - p`.
`prob k g l p` is the probability of the event `(1+g) x + l y > k` under the product (independent coupling)
of `Bin(k, 1-p)` and `Bin(k, p)`. -/

open MeasureTheory ProbabilityTheory unitInterval

/-- The event `(1+g) x + l y > k` in `ℕ × ℕ`. -/
def event (k : ℕ) (g l : ℝ) : Set (ℕ × ℕ) := {z | (1 + g) * (z.1 : ℝ) + l * (z.2 : ℝ) > (k : ℝ)}

/-- `P((1+g) X + l Y > k)` for independent `X ~ Bin(k, 1-p)`, `Y ~ Bin(k, p)`, as a product measure. -/
def prob (k : ℕ) (g l : ℝ) (p : I) : ℝ := ((binomial k (σ p)).prod (binomial k p)).real (event k g l)

/-- For **any** independent random variables `X ~ Bin(k, 1-p)` and `Y ~ Bin(k, p)` on a probability space,
`P((1+g) X + l Y > k) = prob k g l p`. -/
theorem prob_of_indep {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X Y : Ω → ℕ) (k : ℕ) (p : I) (hX : HasLaw X (binomial k (σ p)) P) (hY : HasLaw Y (binomial k p) P)
    (hXY : IndepFun X Y P) (g l : ℝ) :
    P.real {ω | (1 + g) * (X ω : ℝ) + l * (Y ω : ℝ) > (k : ℝ)} = prob k g l p := by
  have hmap := (indepFun_iff_map_prod_eq_prod_map_map hX.aemeasurable hY.aemeasurable).1 hXY
  rw [hX.map_eq, hY.map_eq] at hmap
  have hm : AEMeasurable (fun ω => (X ω, Y ω)) P := hX.aemeasurable.prodMk hY.aemeasurable
  have hS : MeasurableSet (event k g l) := (Set.to_countable _).measurableSet
  rw [prob, ← hmap, map_measureReal_apply_of_aemeasurable hm hS]
  rfl

theorem prob_eq_f (k : ℕ) (g l : ℝ) (p : I) : prob k g l p = f k g l p := by
  have hS : MeasurableSet (event k g l) := (Set.to_countable _).measurableSet
  have hint : Integrable ((event k g l).indicator (1 : ℕ × ℕ → ℝ))
      ((binomial k (σ p)).prod (binomial k p)) := (integrable_const (1 : ℝ)).indicator hS
  rw [prob, ← integral_indicator_one hS, integral_prod _ hint]
  simp only [integral_binomial, smul_eq_mul, f, binPMF, coe_symm_eq, sub_sub_cancel]
  rw [← Nat.range_succ_eq_Iic]
  refine sum_congr rfl fun x _ => ?_
  rw [mul_sum]
  refine sum_congr rfl fun y _ => ?_
  by_cases h : (1 + g) * (x : ℝ) + l * (y : ℝ) > (k : ℝ)
  · have hm : (x, y) ∈ event k g l := h
    rw [Set.indicator_of_mem hm, ite_eq_left h]
    simp only [Pi.one_apply]
    ring
  · have hm : (x, y) ∉ event k g l := h
    rw [Set.indicator_of_notMem hm, ite_eq_right h]
    simp

/-- **Theorem 1, measure form.** -/
theorem theorem1_measure (k : ℕ) (hk : 1 ≤ k) (g l : ℝ) (hg0 : 0 < g) (hg1 : g < 1) (hl0 : 0 < l)
    (hl2 : 2 * l ≤ 1 + g) : StrictAnti (prob k g l) := by
  intro a b hab
  rw [prob_eq_f, prob_eq_f]
  exact theorem1 k hk g l hg0 hg1 hl0 hl2 ⟨a.2.1, a.2.2⟩ ⟨b.2.1, b.2.2⟩ (Subtype.coe_lt_coe.mpr hab)

/-- **The question, measure form**: for independent `X ~ Bin(k, 1-p)` and `Y ~ Bin(k, p)`, the probability
`P((1+g) X + l Y > k)` is strictly decreasing in `p ∈ [0,1]` when `g, l ∈ (0,1)` and `g ≥ l`. -/
theorem answer_measure (k : ℕ) (hk : 1 ≤ k) (g l : ℝ) (hg0 : 0 < g) (hg1 : g < 1) (hl0 : 0 < l)
    (hl1 : l < 1) (hlg : g ≥ l) : StrictAnti (prob k g l) :=
  theorem1_measure k hk g l hg0 hg1 hl0 (by linarith)

end BinomialMonotoneCheck


