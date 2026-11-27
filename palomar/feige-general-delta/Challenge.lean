/-
Copyright 2026 Ming-Chih Kao. Licensed under the Apache License, Version 2.0;
see the LICENSE file at the root of this repository.
-/
module

public import Mathlib

/-!
# Feige's inequality for every `δ > 0`, and the lower bound in Samuels' conjecture

**Feige's inequality** (the `n`-uniform form of a conjecture of U. Feige, *On sums of independent
random variables with unbounded variance, and estimating the average degree in a graph*, SIAM J.
Comput. 35 (2006) 964–984, who proved it with `1/13` in place of `e⁻¹`; Open Problem Garden,
*Sums of independent random variables with unbounded variance*). Let `X₁, …, Xₙ` be
independent, nonnegative and integrable random variables with `𝔼[Xᵢ] ≤ μ`, where `μ > 0`, and
let `δ > 0`. Then
`P(∑ Xᵢ - 𝔼[∑ Xᵢ] < δ μ) ≥ min(δ / (1 + δ), e⁻¹)`.

**Samuels' conjecture, lower bound** (S. M. Samuels, *On a Chebyshev-type inequality for sums of
independent random variables*, Ann. Math. Statist. 37 (1966) 248–259; proved by Z. Ling, *On
Samuels' Conjecture*, arXiv:2608.18392, Theorem 1.1). For `n ≥ 1`, ordered means
`0 ≤ m₁ ≤ ⋯ ≤ mₙ`, `λ > ∑ mᵢ`, and independent nonnegative `Xᵢ` with `𝔼[Xᵢ] = mᵢ`,
`P(∑ Xᵢ < λ) ≥ min_{1 ≤ i ≤ n} qᵢ`, where `qᵢ = ∏_{j ≥ i} (1 - mⱼ / (λ - ∑_{k < i} mₖ))`.
Ling's Theorem 1.1 also says that this bound is sharp and attained; that half is **not** stated
here.

Both theorems follow Ling's proof. Feige's inequality reduces to the equal-means case by adding
the constant `μ - 𝔼 Xᵢ ≥ 0` to each `Xᵢ` (which changes neither independence, nonnegativity nor
`∑ Xᵢ - 𝔼[∑ Xᵢ]`) and dividing by `μ`. What is stated here is the bound uniform in `n`, the Open
Problem Garden form, which is the `inf_{n ≥ 1} c_{n,δ} = min(δ/(1+δ), e⁻¹)` part of Ling's
Corollary 1.3. Not stated: the sharper fixed-`n` value `c_{n,δ} = min(δ/(1+δ), (1 - 1/(n+δ))ⁿ)` of
Corollary 1.3 (Feige's Conjecture 1, which names the extremal examples for each `n`), or the
attainment of either bound.

Conventions. The random variables live on an arbitrary probability space `Ω` (in any universe;
`ℙ` is its measure, `𝔼` the integral). Nonnegativity is pointwise (`∀ ω, 0 ≤ Xᵢ ω`); replacing
`Xᵢ` by `max Xᵢ 0` shows that this loses no generality against almost-sure nonnegativity.
Integrability is assumed explicitly, because in Lean the integral of a non-integrable function is
`0`; "mean `mᵢ`" (respectively "`𝔼 Xᵢ ≤ μ`") presupposes a finite mean.
Indices are `Fin n = {0, …, n - 1}`; `Monotone m` is `m₀ ≤ ⋯ ≤ m_{n-1}`, and the minimum over `i`
is `Finset.inf'` over all of `Fin n` (nonempty because `0 < n`). Probabilities are real numbers
(`ENNReal.toReal` of a probability, which is finite).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset

namespace FeigeSamuels

/-- **Feige's inequality for every `δ > 0`.** For independent, nonnegative, integrable
`X₀, …, X_{n-1}` with `𝔼[Xᵢ] ≤ μ` (`μ > 0`) and every `δ > 0`,
`min(δ / (1 + δ), e⁻¹) ≤ P(∑ Xᵢ - 𝔼[∑ Xᵢ] < δ μ)`. -/
theorem feige_general_delta {n : ℕ} {Ω : Type*} [MeasureSpace Ω]
    [IsProbabilityMeasure (ℙ : Measure Ω)] (X : Fin n → Ω → ℝ) (μ δ : ℝ) (hμ : 0 < μ) (hδ : 0 < δ)
    (hind : iIndepFun X ℙ) (hnn : ∀ i ω, 0 ≤ X i ω) (hint : ∀ i, Integrable (X i))
    (hmean : ∀ i, 𝔼[X i] ≤ μ) :
    min (δ / (1 + δ)) (Real.exp (-1)) ≤
      (ℙ {ω | ∑ i, X i ω - 𝔼[fun ω' => ∑ i, X i ω'] < δ * μ}).toReal := by
  sorry

/-- **Samuels' conjecture, lower bound (Ling, Theorem 1.1).** For `n ≥ 1`, means
`0 ≤ m₀ ≤ ⋯ ≤ m_{n-1}`, `λ > ∑ mᵢ`, and independent nonnegative integrable `Xᵢ` with
`𝔼[Xᵢ] = mᵢ`, `min_i ∏_{j ≥ i} (1 - mⱼ / (λ - ∑_{k < i} mₖ)) ≤ P(∑ Xᵢ < λ)`. -/
theorem samuels_lower {n : ℕ} (hn : 0 < n) {Ω : Type*} [MeasureSpace Ω]
    [IsProbabilityMeasure (ℙ : Measure Ω)] (X : Fin n → Ω → ℝ) (m : Fin n → ℝ) (lam : ℝ)
    (hmono : Monotone m) (hm0 : ∀ i, 0 ≤ m i) (hlam : ∑ i, m i < lam)
    (hind : iIndepFun X ℙ) (hnn : ∀ i ω, 0 ≤ X i ω) (hint : ∀ i, Integrable (X i))
    (hmean : ∀ i, 𝔼[X i] = m i) :
    univ.inf' ⟨⟨0, hn⟩, mem_univ _⟩
        (fun i => ∏ j ∈ univ.filter (i ≤ ·), (1 - m j / (lam - ∑ k ∈ univ.filter (· < i), m k))) ≤
      (ℙ {ω | ∑ i, X i ω < lam}).toReal := by
  sorry

end FeigeSamuels
