/-
Copyright 2026 Ming-Chih Kao. Licensed under the Apache License, Version 2.0;
see the LICENSE file at the root of this repository.
-/
module

public import HellingerTV

/-!
# Solution

Proves the declarations stated in `Challenge.lean` from `HellingerTV/` (the source repository's `MO184460.lean`
and `Check.lean`), whose definitions `truncGauss`, `dTV`, `dH`, `tgauss`, `tvDens`, `hellinger`, `LC` and `LCs`
unfold to the written-out statements.
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
  subst hP hQ; exact HellingerTVCheck.answer μ a b hab

/-- **Strict form.** For `μ ≠ 0` and `a < b`, `d_H < d_TV`. -/
theorem answer_strict {μ : ℝ} (hμ : μ ≠ 0) {a b : ℝ} (hab : a < b) (P Q : ℝ → ℝ)
    (hP : P = (fun x => if a ≤ x ∧ x ≤ b then exp (-(x - (-μ)) ^ 2 / 2) / ∫ y in Icc a b, exp (-(y - (-μ)) ^ 2 / 2) else 0))
    (hQ : Q = (fun x => if a ≤ x ∧ x ≤ b then exp (-(x - μ) ^ 2 / 2) / ∫ y in Icc a b, exp (-(y - μ) ^ 2 / 2) else 0)) :
    √((1 / 2) * ∫ x, (√(P x) - √(Q x)) ^ 2) < (1 / 2) * ∫ x, |P x - Q x| := by
  subst hP hQ; exact HellingerTVCheck.answer_strict hμ hab

/-- The full chain for truncation to any interval `I` of positive length (open, half-open, a half-line or `ℝ`). -/
theorem chain_interval (μ : ℝ) {I : Set ℝ} (hI : I.OrdConnected) (hvol : volume I ≠ 0) (P Q : ℝ → ℝ)
    (hP : P = (fun x => I.indicator (gaussianPDFReal (-μ) 1) x / ∫ y in I, gaussianPDFReal (-μ) 1 y))
    (hQ : Q = (fun x => I.indicator (gaussianPDFReal μ 1) x / ∫ y in I, gaussianPDFReal μ 1 y)) :
    √((1 / 2) * ∫ x, (√(P x) - √(Q x)) ^ 2) ^ 2 ≤ √((1 / 2) * ∫ x, (√(P x) - √(Q x)) ^ 2) ∧
      √((1 / 2) * ∫ x, (√(P x) - √(Q x)) ^ 2) ≤ (1 / 2) * ∫ x, |P x - Q x| := by
  subst hP hQ; exact HellingerTVCheck.chain_interval μ hI hvol

/-- **Theorem 3** (homogeneous form) for a log-concave `f`. -/
theorem thm3 {f : ℝ → ℝ}
    (hf : ∃ J : Set ℝ, ∃ ψ : ℝ → ℝ, J.OrdConnected ∧ ConcaveOn ℝ J ψ ∧ f = J.indicator (fun s => exp (ψ s)))
    (hfc : Integrable (fun s => f s * cosh s)) (hs : ∫ s, f s * sinh s = 0) :
    (∫ s, f s * cosh s) * ((∫ s, f s * cosh s) - ∫ s, f s) ≤ (∫ s, f s * |sinh s|) ^ 2 := by
  exact HellingerTV.thm3 hf hfc hs

/-- **Theorem 3, strict** for strictly log-concave `f` with `∫ f > 0`. -/
theorem thm3_strict {f : ℝ → ℝ}
    (hf : ∃ J : Set ℝ, ∃ ψ : ℝ → ℝ, J.OrdConnected ∧ StrictConcaveOn ℝ J ψ ∧
      f = J.indicator (fun s => exp (ψ s)))
    (hfc : Integrable (fun s => f s * cosh s)) (hs : ∫ s, f s * sinh s = 0) (hpos : 0 < ∫ s, f s) :
    (∫ s, f s * cosh s) * ((∫ s, f s * cosh s) - ∫ s, f s) < (∫ s, f s * |sinh s|) ^ 2 := by
  exact HellingerTV.thm3_strict hf hfc hs hpos

end MO184460
