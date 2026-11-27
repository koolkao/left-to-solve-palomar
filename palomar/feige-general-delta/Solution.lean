/-
Copyright 2026 Ming-Chih Kao. Licensed under the Apache License, Version 2.0;
see the LICENSE file at the root of this repository.
-/
module

public import Feige

/-!
# Solution

Proves the two declarations stated in `Challenge.lean` from the proof development in `Feige/`:
`OMA.S_opg_sums_of_independent_random_variables_with_unbounded_variance.main` (`Feige/Main.lean`)
and `Samuels.samuels_lower` (`Feige/Samuels/Theorem11.lean`, where the bound is named `Samuels.qS`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset

namespace FeigeSamuels

theorem feige_general_delta {n : ℕ} {Ω : Type*} [MeasureSpace Ω]
    [IsProbabilityMeasure (ℙ : Measure Ω)] (X : Fin n → Ω → ℝ) (μ δ : ℝ) (hμ : 0 < μ) (hδ : 0 < δ)
    (hind : iIndepFun X ℙ) (hnn : ∀ i ω, 0 ≤ X i ω) (hint : ∀ i, Integrable (X i))
    (hmean : ∀ i, 𝔼[X i] ≤ μ) :
    min (δ / (1 + δ)) (Real.exp (-1)) ≤
      (ℙ {ω | ∑ i, X i ω - 𝔼[fun ω' => ∑ i, X i ω'] < δ * μ}).toReal :=
  OMA.S_opg_sums_of_independent_random_variables_with_unbounded_variance.main_univ X μ δ hμ hδ hind hnn hint
    hmean

theorem samuels_lower {n : ℕ} (hn : 0 < n) {Ω : Type*} [MeasureSpace Ω]
    [IsProbabilityMeasure (ℙ : Measure Ω)] (X : Fin n → Ω → ℝ) (m : Fin n → ℝ) (lam : ℝ)
    (hmono : Monotone m) (hm0 : ∀ i, 0 ≤ m i) (hlam : ∑ i, m i < lam)
    (hind : iIndepFun X ℙ) (hnn : ∀ i ω, 0 ≤ X i ω) (hint : ∀ i, Integrable (X i))
    (hmean : ∀ i, 𝔼[X i] = m i) :
    univ.inf' ⟨⟨0, hn⟩, mem_univ _⟩
        (fun i => ∏ j ∈ univ.filter (i ≤ ·), (1 - m j / (lam - ∑ k ∈ univ.filter (· < i), m k))) ≤
      (ℙ {ω | ∑ i, X i ω < lam}).toReal :=
  Samuels.samuels_lower hn X m lam hmono hm0 hlam hind hnn hint hmean

end FeigeSamuels
