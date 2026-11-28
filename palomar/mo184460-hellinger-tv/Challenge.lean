/-
Copyright 2026 Ming-Chih Kao. Licensed under the Apache License, Version 2.0;
see the LICENSE file at the root of this repository.
-/
module

public import Mathlib

/-!
# MathOverflow 184460: Hellinger distance ≤ total variation for truncated Gaussians

MathOverflow question 184460 ("Total variation and Hellinger distance inequality between truncated
Gaussians", Alexander, 15 October 2014, <https://mathoverflow.net/questions/184460>, CC BY-SA 3.0) asks, with
`d_TV(P,Q) = (1/2) ‖P - Q‖₁` and `d_H²(P,Q) = (1/2) ‖√P - √Q‖₂²`:

> For `P = N(-μ,1)` and `Q = N(μ,1)`, `μ ∈ ℝ`, truncated to the interval `[a,b]`, `a, b ∈ ℝ`, does
> `d_H²(P,Q) ≤ d_H(P,Q) ≤ d_TV(P,Q)` hold for all `a, b, μ`?

The answer, proved in `Solution.lean` (Ming-Chih Kao, 2026, <https://github.com/koolkao/mo184460-hellinger-tv>),
is yes for every `μ` and every `a < b`, strictly `d_H < d_TV` when `μ ≠ 0`, and also for truncation to any
interval of positive length (`chain_interval`). It rests on Theorem 3 of the source repository's `NOTE.md`
(`thm3`, `thm3_strict`, homogeneous form): for a log-concave `f ≥ 0` on `ℝ` with `f cosh` integrable and
`∫ f sinh = 0`, `(∫ f cosh) (∫ f cosh - ∫ f) ≤ (∫ f |sinh|)²`, strictly when `f` is strictly log-concave
and `∫ f > 0`.

Vocabulary (written out, no definitions): the truncated densities `P`, `Q` are given by equations.
In `answer` and `answer_strict`, `x ↦ 1[a ≤ x ≤ b] e^{-(x-m)²/2} / ∫_{[a,b]} e^{-(y-m)²/2} dy` with `m = ∓μ` (the
factor `(2π)^{-1/2}` cancels); in `chain_interval`, Mathlib's `gaussianPDFReal m 1` restricted to `I` and
normalised. `d_TV = (1/2) ∫ |P - Q|` and `d_H = √((1/2) ∫ (√P - √Q)²)` are written as integrals over `ℝ`.
A log-concave function is the indicator of an interval times `exp` of a concave function on it (strictly
concave for `thm3_strict`).
-/

@[expose] public section

open MeasureTheory Set Real ProbabilityTheory

namespace MO184460

/-- **MO 184460 (answer: yes).** For every `μ ∈ ℝ` and every `a < b`, `d_H² ≤ d_H ≤ d_TV`. -/
theorem answer (μ a b : ℝ) (hab : a < b) (P Q : ℝ → ℝ)
    (hP : P = (fun x => if a ≤ x ∧ x ≤ b then exp (-(x - (-μ)) ^ 2 / 2) / ∫ y in Icc a b, exp (-(y - (-μ)) ^ 2 / 2) else 0))
    (hQ : Q = (fun x => if a ≤ x ∧ x ≤ b then exp (-(x - μ) ^ 2 / 2) / ∫ y in Icc a b, exp (-(y - μ) ^ 2 / 2) else 0)) :
    √((1 / 2) * ∫ x, (√(P x) - √(Q x)) ^ 2) ^ 2 ≤ √((1 / 2) * ∫ x, (√(P x) - √(Q x)) ^ 2) ∧
      √((1 / 2) * ∫ x, (√(P x) - √(Q x)) ^ 2) ≤ (1 / 2) * ∫ x, |P x - Q x| := by
  sorry

/-- **Strict form.** For `μ ≠ 0` and `a < b`, `d_H < d_TV`. -/
theorem answer_strict {μ : ℝ} (hμ : μ ≠ 0) {a b : ℝ} (hab : a < b) (P Q : ℝ → ℝ)
    (hP : P = (fun x => if a ≤ x ∧ x ≤ b then exp (-(x - (-μ)) ^ 2 / 2) / ∫ y in Icc a b, exp (-(y - (-μ)) ^ 2 / 2) else 0))
    (hQ : Q = (fun x => if a ≤ x ∧ x ≤ b then exp (-(x - μ) ^ 2 / 2) / ∫ y in Icc a b, exp (-(y - μ) ^ 2 / 2) else 0)) :
    √((1 / 2) * ∫ x, (√(P x) - √(Q x)) ^ 2) < (1 / 2) * ∫ x, |P x - Q x| := by
  sorry

/-- The full chain for truncation to any interval `I` of positive length (open, half-open, a half-line or `ℝ`). -/
theorem chain_interval (μ : ℝ) {I : Set ℝ} (hI : I.OrdConnected) (hvol : volume I ≠ 0) (P Q : ℝ → ℝ)
    (hP : P = (fun x => I.indicator (gaussianPDFReal (-μ) 1) x / ∫ y in I, gaussianPDFReal (-μ) 1 y))
    (hQ : Q = (fun x => I.indicator (gaussianPDFReal μ 1) x / ∫ y in I, gaussianPDFReal μ 1 y)) :
    √((1 / 2) * ∫ x, (√(P x) - √(Q x)) ^ 2) ^ 2 ≤ √((1 / 2) * ∫ x, (√(P x) - √(Q x)) ^ 2) ∧
      √((1 / 2) * ∫ x, (√(P x) - √(Q x)) ^ 2) ≤ (1 / 2) * ∫ x, |P x - Q x| := by
  sorry

/-- **Theorem 3** (homogeneous form) for a log-concave `f`. -/
theorem thm3 {f : ℝ → ℝ}
    (hf : ∃ J : Set ℝ, ∃ ψ : ℝ → ℝ, J.OrdConnected ∧ ConcaveOn ℝ J ψ ∧ f = J.indicator (fun s => exp (ψ s)))
    (hfc : Integrable (fun s => f s * cosh s)) (hs : ∫ s, f s * sinh s = 0) :
    (∫ s, f s * cosh s) * ((∫ s, f s * cosh s) - ∫ s, f s) ≤ (∫ s, f s * |sinh s|) ^ 2 := by
  sorry

/-- **Theorem 3, strict** for strictly log-concave `f` with `∫ f > 0`. -/
theorem thm3_strict {f : ℝ → ℝ}
    (hf : ∃ J : Set ℝ, ∃ ψ : ℝ → ℝ, J.OrdConnected ∧ StrictConcaveOn ℝ J ψ ∧
      f = J.indicator (fun s => exp (ψ s)))
    (hfc : Integrable (fun s => f s * cosh s)) (hs : ∫ s, f s * sinh s = 0) (hpos : 0 < ∫ s, f s) :
    (∫ s, f s * cosh s) * ((∫ s, f s * cosh s) - ∫ s, f s) < (∫ s, f s * |sinh s|) ^ 2 := by
  sorry

end MO184460
