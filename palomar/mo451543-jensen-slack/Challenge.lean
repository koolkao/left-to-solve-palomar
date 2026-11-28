/-
Copyright 2026 Ming-Chih Kao. Licensed under the Apache License, Version 2.0;
see the LICENSE file at the root of this repository.
-/
module

public import Mathlib

/-!
# MathOverflow 451543: only quadratics compare the two Jensen slacks

MathOverflow question 451543 ("Comparing the slackness of Jensen's inequality for some coupled random
variables", Guy Blanc, 27 July 2023, <https://mathoverflow.net/questions/451543>, CC BY-SA 4.0) asks:

> Let `f : ℝ → ℝ` be convex and let `X, Y` be random variables with a coupling such that `E[Y | X = x] = x`.
> Put `μ(y) := E[X | Y = y]`. What conditions on `f` guarantee `E[f(X) - f(μ(Y))] ≤ E[f(Y) - f(X)]`?

(The asker conjectures that `f` convex with `f''` convex suffices.) The answer, proved in `Solution.lean`
(Ming-Chih Kao, 2026, <https://github.com/koolkao/mo451543-jensen-slack>): for finitely supported couplings,
a convex (or merely continuous) `f` satisfies the inequality for every coupling iff `f` is a quadratic
`α t² + β t + γ` with `α ≥ 0`; the same holds for the smaller class of couplings `Y = X + Z` with `Z`
independent of `X` and `E Z = 0`; and `x ^ 4` (convex with `f'' = 12 x²` convex) is a counterexample to the
asker's conjecture.

Vocabulary (written out, no definitions): a finite coupling is a list of `n` atoms `(x i, y i)` with weights
`w i ≥ 0`, `∑ w = 1` (atoms may repeat). `E[Y | X] = X` is imposed on every fibre `{X = x₀}`:
`∑_{x i = x₀} w i * y i = x₀ * ∑_{x i = x₀} w i`. `μ (y i)` is the fibrewise conditional mean
`(∑_{y j = y i} w j * x j) / (∑_{y j = y i} w j)` (the denominator is positive whenever `w i > 0`; atoms
with `w i = 0` contribute nothing). Expectations are the weighted sums. The independent-noise class is
`X = a i` with probability `p i`, `Z = z j` with probability `r j`, `E Z = 0`, `Y = X + Z`, indexed by
`Fin n × Fin m` with the product weights `p i * r j`.
-/

@[expose] public section

open Finset

namespace MO451543

/-- `x ^ 4` is convex and its second derivative `12 x²` is convex (it is in the asker's class). -/
theorem pow_four_in_class :
    ConvexOn ℝ Set.univ (fun t : ℝ => t ^ 4) ∧ ConvexOn ℝ Set.univ (fun t : ℝ => 12 * t ^ 2) ∧
    deriv (deriv (fun t : ℝ => t ^ 4)) = fun t => 12 * t ^ 2 :=
  sorry

/-- The inequality fails for `f t = t ^ 4` on some finite coupling: the asker's conjecture is false. -/
theorem not_comparison_pow_four :
    ¬ (∀ (n : ℕ) (x y w : Fin n → ℝ), ((∀ i, 0 ≤ w i) ∧ ∑ i, w i = 1) →
      (∀ x₀ : ℝ, ∑ i ∈ univ.filter (fun i => x i = x₀), w i * y i =
        x₀ * ∑ i ∈ univ.filter (fun i => x i = x₀), w i) →
      ∑ i, w i * ((fun t : ℝ => t ^ 4) (x i) - (fun t : ℝ => t ^ 4) ((∑ j ∈ univ.filter (fun j => y j = y i), w j * x j) /
          (∑ j ∈ univ.filter (fun j => y j = y i), w j))) ≤
        ∑ i, w i * ((fun t : ℝ => t ^ 4) (y i) - (fun t : ℝ => t ^ 4) (x i))) :=
  sorry

/-- **Theorem 1 (convex `f`).** The inequality holds for every finite coupling iff `f` is a convex quadratic. -/
theorem comparison_iff_of_convex (f : ℝ → ℝ) (hf : ConvexOn ℝ Set.univ f) :
    (∀ (n : ℕ) (x y w : Fin n → ℝ), ((∀ i, 0 ≤ w i) ∧ ∑ i, w i = 1) →
      (∀ x₀ : ℝ, ∑ i ∈ univ.filter (fun i => x i = x₀), w i * y i =
        x₀ * ∑ i ∈ univ.filter (fun i => x i = x₀), w i) →
      ∑ i, w i * (f (x i) - f ((∑ j ∈ univ.filter (fun j => y j = y i), w j * x j) /
          (∑ j ∈ univ.filter (fun j => y j = y i), w j))) ≤
        ∑ i, w i * (f (y i) - f (x i)))
    ↔ ∃ α β γ : ℝ, 0 ≤ α ∧ ∀ t, f t = α * t ^ 2 + β * t + γ :=
  sorry

/-- **Theorem 1 (continuous `f`).** -/
theorem comparison_iff_of_continuous (f : ℝ → ℝ) (hf : Continuous f) :
    (∀ (n : ℕ) (x y w : Fin n → ℝ), ((∀ i, 0 ≤ w i) ∧ ∑ i, w i = 1) →
      (∀ x₀ : ℝ, ∑ i ∈ univ.filter (fun i => x i = x₀), w i * y i =
        x₀ * ∑ i ∈ univ.filter (fun i => x i = x₀), w i) →
      ∑ i, w i * (f (x i) - f ((∑ j ∈ univ.filter (fun j => y j = y i), w j * x j) /
          (∑ j ∈ univ.filter (fun j => y j = y i), w j))) ≤
        ∑ i, w i * (f (y i) - f (x i)))
    ↔ ∃ α β γ : ℝ, 0 ≤ α ∧ ∀ t, f t = α * t ^ 2 + β * t + γ :=
  sorry

/-- **Theorem 2 (convex `f`).** The same for independent additive noise `Y = X + Z`, `E Z = 0`. -/
theorem indepComparison_iff_of_convex (f : ℝ → ℝ) (hf : ConvexOn ℝ Set.univ f) :
    (∀ (n m : ℕ) (a p : Fin n → ℝ) (z r : Fin m → ℝ),
      ((∀ i, 0 ≤ p i) ∧ ∑ i, p i = 1) → ((∀ j, 0 ≤ r j) ∧ ∑ j, r j = 1) → ∑ j, r j * z j = 0 →
      ∑ k : Fin n × Fin m, p k.1 * r k.2 * (f (a k.1) -
          f ((∑ l ∈ univ.filter (fun l : Fin n × Fin m => a l.1 + z l.2 = a k.1 + z k.2),
              p l.1 * r l.2 * a l.1) /
            (∑ l ∈ univ.filter (fun l : Fin n × Fin m => a l.1 + z l.2 = a k.1 + z k.2), p l.1 * r l.2))) ≤
        ∑ k : Fin n × Fin m, p k.1 * r k.2 * (f (a k.1 + z k.2) - f (a k.1)))
    ↔ ∃ α β γ : ℝ, 0 ≤ α ∧ ∀ t, f t = α * t ^ 2 + β * t + γ :=
  sorry

/-- **Theorem 2 (continuous `f`).** -/
theorem indepComparison_iff_of_continuous (f : ℝ → ℝ) (hf : Continuous f) :
    (∀ (n m : ℕ) (a p : Fin n → ℝ) (z r : Fin m → ℝ),
      ((∀ i, 0 ≤ p i) ∧ ∑ i, p i = 1) → ((∀ j, 0 ≤ r j) ∧ ∑ j, r j = 1) → ∑ j, r j * z j = 0 →
      ∑ k : Fin n × Fin m, p k.1 * r k.2 * (f (a k.1) -
          f ((∑ l ∈ univ.filter (fun l : Fin n × Fin m => a l.1 + z l.2 = a k.1 + z k.2),
              p l.1 * r l.2 * a l.1) /
            (∑ l ∈ univ.filter (fun l : Fin n × Fin m => a l.1 + z l.2 = a k.1 + z k.2), p l.1 * r l.2))) ≤
        ∑ k : Fin n × Fin m, p k.1 * r k.2 * (f (a k.1 + z k.2) - f (a k.1)))
    ↔ ∃ α β γ : ℝ, 0 ≤ α ∧ ∀ t, f t = α * t ^ 2 + β * t + γ :=
  sorry

end MO451543
