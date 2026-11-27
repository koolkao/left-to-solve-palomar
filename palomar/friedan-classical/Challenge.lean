/-
Copyright 2026 Ming-Chih Kao. Licensed under the Apache License, Version 2.0;
see the LICENSE file at the root of this repository.
-/
module

public import Mathlib

/-!
# Friedan's generalized entropy inequality (MathOverflow 138395), for `m` distributions and for the
two-point Rényi entropy

MathOverflow question 138395 (Daniel Friedan, 2013, <https://mathoverflow.net/q/138395>,
CC BY-SA 3.0) asks:

> Let `X, Y` be probability measures on `{1, 2, …, n}`. For `0 ≤ α ≤ 1`, set
> `K = ∑ᵢ X(i)^α Y(i)^(1-α)`, so that `Z := X^α Y^(1-α) / K` is also a probability measure on
> `{1, 2, …, n}`. Prove the inequality `α H(X) + (1 - α) H(Y) ≥ K² H(Z)`, where
> `H(X) = -∑ᵢ X(i) log X(i)` is the entropy function.

The case `α = 1/2` was proved by fedja (MathOverflow 138275, 2013). Ming-Chih Kao (2026,
<https://github.com/koolkao/friedan-entropy-inequality>) gives proofs of the general case, of its
extension to `m` distributions (Theorem M) and of the positive part of the two-point Rényi version
(Theorem R2); as far as the authors searched, no earlier proof exists for any other interior weight.

Conventions (the same as in the source repository):
* `{1, …, n}` is `Fin n`; a probability vector is written out (nonnegative entries summing to `1`).
* `H(P) = ∑ᵢ Real.negMulLog (P i)`, that is `-∑ᵢ P(i) log P(i)` with the natural logarithm and
  `0 log 0 = 0`. (Any base `> 1` gives an equivalent inequality.)
* The coordinate powers `X(i)^α` are real powers `Real.rpow`, with `0^0 = 1`; this matters only for
  weights equal to `0` (a distribution of weight `0` contributes the factor `1` to `zᵢ`).
* `K > 0` is assumed, since `Z` must be a probability vector. (`K = 0` happens only when the
  distributions of positive weight have no common point of support; there `K² = 0` would make the
  left side `0` anyway.)
* The Rényi entropy of order `γ > 0`, `γ ≠ 1`, is `H_γ(P) = log(∑ᵢ P(i)^γ) / (1 - γ)` (natural
  logarithm; the threshold `2 log 2` below is in the natural logarithm).

Statements:
* `friedan_two`: Friedan's inequality, every `n` and every `α ∈ [0, 1]`.
* `friedan_multi` (Theorem M): for probability vectors `X₀, …, X_{m-1}` and weights `aⱼ ≥ 0` with
  `∑ aⱼ = 1`, with `zᵢ = ∏ⱼ Xⱼ(i)^{aⱼ}`, `K = ∑ᵢ zᵢ > 0` and `Z = z / K`:
  `K² H(Z) ≤ ∑ⱼ aⱼ H(Xⱼ)`.
* `friedan_renyi_two_point` (Theorem R2, positive part): the same with `H` replaced by `H_γ` on
  both sides, for probability vectors on two points and `0 < γ ≤ 2 log 2`, `γ ≠ 1`. The other part of
  Theorem R2 (failure for every `γ > 2 log 2`) and Proposition R1 (failure for every `γ > 1` in high
  dimension) are paper proofs and are not stated here.
-/

@[expose] public section

namespace Friedan138395

/-- **Friedan's inequality (MathOverflow 138395).** For probability vectors `X, Y` on `Fin n`,
`0 ≤ α ≤ 1` and `K = ∑ᵢ X(i)^α Y(i)^(1-α) > 0`, with `Z = X^α Y^(1-α) / K`:
`K² H(Z) ≤ α H(X) + (1 - α) H(Y)`. -/
theorem friedan_two (n : ℕ) (X Y : Fin n → ℝ) (hX0 : ∀ i, 0 ≤ X i) (hX1 : ∑ i, X i = 1)
    (hY0 : ∀ i, 0 ≤ Y i) (hY1 : ∑ i, Y i = 1) (α : ℝ) (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    (hK : 0 < ∑ i, X i ^ α * Y i ^ (1 - α)) :
    (∑ i, X i ^ α * Y i ^ (1 - α)) ^ 2 *
        ∑ i, Real.negMulLog (X i ^ α * Y i ^ (1 - α) / ∑ j, X j ^ α * Y j ^ (1 - α)) ≤
      α * ∑ i, Real.negMulLog (X i) + (1 - α) * ∑ i, Real.negMulLog (Y i) := by
  sorry

/-- **Theorem M (`m` distributions).** For probability vectors `X j` on `Fin n` (`j : Fin m`) and
weights `a j ≥ 0` with `∑ⱼ a j = 1`, put `zᵢ = ∏ⱼ X j i ^ a j` and `K = ∑ᵢ zᵢ > 0`. Then
`K² H(z / K) ≤ ∑ⱼ a j H(X j)`. -/
theorem friedan_multi (n m : ℕ) (X : Fin m → Fin n → ℝ) (hX0 : ∀ j i, 0 ≤ X j i)
    (hX1 : ∀ j, ∑ i, X j i = 1) (a : Fin m → ℝ) (ha0 : ∀ j, 0 ≤ a j) (ha1 : ∑ j, a j = 1)
    (hK : 0 < ∑ i, ∏ j, X j i ^ a j) :
    (∑ i, ∏ j, X j i ^ a j) ^ 2 *
        ∑ i, Real.negMulLog ((∏ j, X j i ^ a j) / ∑ k, ∏ j, X j k ^ a j) ≤
      ∑ j, a j * ∑ i, Real.negMulLog (X j i) := by
  sorry

/-- **Theorem R2, positive part (two-point Rényi version).** For probability vectors `X j` on `Fin 2`
(`j : Fin m`), weights `a j ≥ 0` with `∑ⱼ a j = 1`, an order `0 < γ ≤ 2 log 2` with `γ ≠ 1`, and
`K = ∑ᵢ ∏ⱼ X j i ^ a j > 0`: `K² H_γ(z / K) ≤ ∑ⱼ a j H_γ(X j)`, where
`H_γ(P) = log(∑ᵢ P(i)^γ) / (1 - γ)`. -/
theorem friedan_renyi_two_point (m : ℕ) (X : Fin m → Fin 2 → ℝ) (hX0 : ∀ j i, 0 ≤ X j i)
    (hX1 : ∀ j, ∑ i, X j i = 1) (a : Fin m → ℝ) (ha0 : ∀ j, 0 ≤ a j) (ha1 : ∑ j, a j = 1)
    (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ ≠ 1) (hγ2 : γ ≤ 2 * Real.log 2)
    (hK : 0 < ∑ i, ∏ j, X j i ^ a j) :
    (∑ i, ∏ j, X j i ^ a j) ^ 2 *
        (Real.log (∑ i, ((∏ j, X j i ^ a j) / ∑ k, ∏ j, X j k ^ a j) ^ γ) / (1 - γ)) ≤
      ∑ j, a j * (Real.log (∑ i, X j i ^ γ) / (1 - γ)) := by
  sorry

end Friedan138395
