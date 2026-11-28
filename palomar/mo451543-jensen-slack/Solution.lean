/-
Copyright 2026 Ming-Chih Kao. Licensed under the Apache License, Version 2.0;
see the LICENSE file at the root of this repository.
-/
module

public import JensenSlack

/-!
# Solution

Proves the declarations stated in `Challenge.lean` from `JensenSlack/Proof.lean` (the source repository's
`MO451543.lean`), whose definitions `mu`, `IsLaw`, `IsMart`, `lhs`, `rhs`, `Comparison` and
`IndepComparison` unfold to the written-out statements.
-/

@[expose] public section

open Finset

namespace MO451543

/-- `x ^ 4` is convex and its second derivative `12 x²` is convex (it is in the asker's class). -/
theorem pow_four_in_class :
    ConvexOn ℝ Set.univ (fun t : ℝ => t ^ 4) ∧ ConvexOn ℝ Set.univ (fun t : ℝ => 12 * t ^ 2) ∧
    deriv (deriv (fun t : ℝ => t ^ 4)) = fun t => 12 * t ^ 2 :=
  JensenSlack.pow_four_in_class

/-- The inequality fails for `f t = t ^ 4` on some finite coupling: the asker's conjecture is false. -/
theorem not_comparison_pow_four :
    ¬ (∀ (n : ℕ) (x y w : Fin n → ℝ), ((∀ i, 0 ≤ w i) ∧ ∑ i, w i = 1) →
      (∀ x₀ : ℝ, ∑ i ∈ univ.filter (fun i => x i = x₀), w i * y i =
        x₀ * ∑ i ∈ univ.filter (fun i => x i = x₀), w i) →
      ∑ i, w i * ((fun t : ℝ => t ^ 4) (x i) - (fun t : ℝ => t ^ 4) ((∑ j ∈ univ.filter (fun j => y j = y i), w j * x j) /
          (∑ j ∈ univ.filter (fun j => y j = y i), w j))) ≤
        ∑ i, w i * ((fun t : ℝ => t ^ 4) (y i) - (fun t : ℝ => t ^ 4) (x i))) :=
  JensenSlack.not_comparison_pow_four

/-- **Theorem 1 (convex `f`).** The inequality holds for every finite coupling iff `f` is a convex quadratic. -/
theorem comparison_iff_of_convex (f : ℝ → ℝ) (hf : ConvexOn ℝ Set.univ f) :
    (∀ (n : ℕ) (x y w : Fin n → ℝ), ((∀ i, 0 ≤ w i) ∧ ∑ i, w i = 1) →
      (∀ x₀ : ℝ, ∑ i ∈ univ.filter (fun i => x i = x₀), w i * y i =
        x₀ * ∑ i ∈ univ.filter (fun i => x i = x₀), w i) →
      ∑ i, w i * (f (x i) - f ((∑ j ∈ univ.filter (fun j => y j = y i), w j * x j) /
          (∑ j ∈ univ.filter (fun j => y j = y i), w j))) ≤
        ∑ i, w i * (f (y i) - f (x i)))
    ↔ ∃ α β γ : ℝ, 0 ≤ α ∧ ∀ t, f t = α * t ^ 2 + β * t + γ :=
  JensenSlack.comparison_iff_of_convex f hf

/-- **Theorem 1 (continuous `f`).** -/
theorem comparison_iff_of_continuous (f : ℝ → ℝ) (hf : Continuous f) :
    (∀ (n : ℕ) (x y w : Fin n → ℝ), ((∀ i, 0 ≤ w i) ∧ ∑ i, w i = 1) →
      (∀ x₀ : ℝ, ∑ i ∈ univ.filter (fun i => x i = x₀), w i * y i =
        x₀ * ∑ i ∈ univ.filter (fun i => x i = x₀), w i) →
      ∑ i, w i * (f (x i) - f ((∑ j ∈ univ.filter (fun j => y j = y i), w j * x j) /
          (∑ j ∈ univ.filter (fun j => y j = y i), w j))) ≤
        ∑ i, w i * (f (y i) - f (x i)))
    ↔ ∃ α β γ : ℝ, 0 ≤ α ∧ ∀ t, f t = α * t ^ 2 + β * t + γ :=
  JensenSlack.comparison_iff_of_continuous f hf

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
  JensenSlack.indepComparison_iff_of_convex f hf

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
  JensenSlack.indepComparison_iff_of_continuous f hf

end MO451543
