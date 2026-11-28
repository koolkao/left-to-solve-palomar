/-
Copyright 2026 Ming-Chih Kao. Licensed under the Apache License, Version 2.0;
see the LICENSE file at the root of this repository.
-/
module

public import HellingerTV.Proof

/-! Port: copied from `Check.lean` of github.com/koolkao/mo184460-hellinger-tv (commit
b2b49dcf336bcab5835d78cab9686f7ba9ee4b79, v1.0.0, Lean v4.36.0, same Mathlib) and put into the module system:
the `module` header, `public import`, a public section, and the namespaces `MO184460` and `MO184460Check`
renamed `HellingerTV` and `HellingerTVCheck` so that `Solution.lean` can state the compared theorems
under the names `MO184460.*`; the `#print axioms` report is dropped. The mathematics and the proofs are
unchanged. -/

@[expose] public section

/-!
# Independent check: MathOverflow 184460 restated from the question text

Question (MathOverflow 184460, "Total variation and Hellinger distance inequality between truncated
Gaussians", asked by Alexander (MathOverflow user 39824) on 15 October 2014; CC BY-SA 3.0), in its own conventions:
`d_TV(P,Q) = (1/2) ‖P - Q‖₁` and `d_H²(P,Q) = (1/2) ‖√P - √Q‖₂²`. For `P = N(-μ,1)` and `Q = N(μ,1)`,
`μ ∈ ℝ`, truncated to the interval `[a,b]`, `a, b ∈ ℝ`, does

  `d_H²(P,Q) ≤ d_H(P,Q) ≤ d_TV(P,Q)`

hold for all `a, b, μ`?

Here everything is written out by hand, without the vocabulary of `HellingerTV.lean`:
* `truncGauss m a b x = 1[a ≤ x ≤ b] e^{-(x-m)²/2} / ∫_{[a,b]} e^{-(y-m)²/2} dy`, the density of `N(m,1)`
  conditioned on `[a,b]` (the factor `(2π)^{-1/2}` cancels);
* `dTV p q = (1/2) ∫ |p - q|`;
* `dH p q = ((1/2) ∫ (√p - √q)²)^{1/2}`.

`truncGauss_density` checks that `truncGauss m a b` is a probability density when `a < b`, so the statements
are not about junk values. (For `a ≥ b` the truncation is undefined; the question tacitly has `a < b`.)
The proofs translate into the vocabulary of `HellingerTV.lean` and apply `HellingerTV.mo184460_Icc` and
`HellingerTV.mo184460_Icc_strict`.
-/

open MeasureTheory Set Real

namespace HellingerTVCheck

/-- The density of `N(m, 1)` truncated to `[a, b]`, written out. -/
noncomputable def truncGauss (m a b x : ℝ) : ℝ :=
  if a ≤ x ∧ x ≤ b then exp (-(x - m) ^ 2 / 2) / ∫ y in Icc a b, exp (-(y - m) ^ 2 / 2) else 0

/-- Total variation distance in the question's convention: `(1/2) ‖p - q‖₁`. -/
noncomputable def dTV (p q : ℝ → ℝ) : ℝ := (1 / 2) * ∫ x, |p x - q x|

/-- Hellinger distance in the question's convention: `d_H² = (1/2) ‖√p - √q‖₂²`. -/
noncomputable def dH (p q : ℝ → ℝ) : ℝ := √((1 / 2) * ∫ x, (√(p x) - √(q x)) ^ 2)

/-! ## Translation to the vocabulary of `HellingerTV.lean` -/

lemma truncGauss_eq (m a b : ℝ) : truncGauss m a b = HellingerTV.tgauss m (Icc a b) := by
  funext x
  have hc : (√(2 * π))⁻¹ ≠ 0 := by positivity
  simp only [truncGauss, HellingerTV.tgauss, HellingerTV.gauss_one, integral_const_mul, indicator_apply,
    mem_Icc]
  split_ifs with h
  · rw [mul_div_mul_left _ _ hc]
  · rw [zero_div]

lemma vol_Icc {a b : ℝ} (hab : a < b) : volume (Icc a b) ≠ 0 := by
  rw [Real.volume_Icc, ne_eq, ENNReal.ofReal_eq_zero, not_le]; linarith

/-- For `a < b`, `truncGauss m a b` is a probability density. -/
theorem truncGauss_density (m : ℝ) {a b : ℝ} (hab : a < b) :
    (∀ x, 0 ≤ truncGauss m a b x) ∧ Integrable (truncGauss m a b) ∧
      ∫ x, truncGauss m a b x = 1 := by
  refine ⟨fun x => ?_, ?_⟩
  · unfold truncGauss
    split_ifs
    · exact div_nonneg (exp_pos _).le (integral_nonneg fun y => (exp_pos _).le)
    · exact le_rfl
  · rw [truncGauss_eq]
    exact HellingerTV.tgauss_integral m ordConnected_Icc (vol_Icc hab)

lemma dTV_le_one {p q : ℝ → ℝ} (hp0 : ∀ x, 0 ≤ p x) (hq0 : ∀ x, 0 ≤ q x)
    (ip : Integrable p) (iq : Integrable q) (hp1 : ∫ x, p x = 1) (hq1 : ∫ x, q x = 1) :
    dTV p q ≤ 1 := by
  unfold dTV
  have h : ∫ x, |p x - q x| ≤ ∫ x, (p x + q x) :=
    integral_mono (ip.sub iq).abs (ip.add iq) fun x =>
      abs_sub_le_iff.2 ⟨by linarith [hp0 x, hq0 x], by linarith [hp0 x, hq0 x]⟩
  rw [integral_add ip iq, hp1, hq1] at h
  linarith

lemma dH_eq (μ a b : ℝ) :
    dH (truncGauss (-μ) a b) (truncGauss μ a b) =
      HellingerTV.hellinger (HellingerTV.tgauss (-μ) (Icc a b)) (HellingerTV.tgauss μ (Icc a b)) := by
  simp only [truncGauss_eq]; rfl

lemma dTV_eq (μ a b : ℝ) :
    dTV (truncGauss (-μ) a b) (truncGauss μ a b) =
      HellingerTV.tvDens (HellingerTV.tgauss (-μ) (Icc a b)) (HellingerTV.tgauss μ (Icc a b)) := by
  simp only [truncGauss_eq]; rfl

/-- The two integrands are integrable, so `dTV` and `dH` are genuine integrals (not the Bochner
junk value `0`). -/
theorem integrands_integrable (μ : ℝ) {a b : ℝ} (hab : a < b) :
    Integrable (fun x => |truncGauss (-μ) a b x - truncGauss μ a b x|) ∧
      Integrable (fun x => (√(truncGauss (-μ) a b x) - √(truncGauss μ a b x)) ^ 2) := by
  obtain ⟨p0, ip, -⟩ := truncGauss_density (-μ) hab
  obtain ⟨q0, iq, -⟩ := truncGauss_density μ hab
  refine ⟨(ip.sub iq).abs, Integrable.mono' (ip.add iq) ?_ (Filter.Eventually.of_forall fun x => ?_)⟩
  · exact ((Real.continuous_sqrt.comp_aestronglyMeasurable ip.1).sub
      (Real.continuous_sqrt.comp_aestronglyMeasurable iq.1)).pow 2
  · rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have h1 := Real.sq_sqrt (p0 x)
    have h2 := Real.sq_sqrt (q0 x)
    have h3 := mul_nonneg (Real.sqrt_nonneg (truncGauss (-μ) a b x))
      (Real.sqrt_nonneg (truncGauss μ a b x))
    simp only [Pi.add_apply]
    nlinarith

/-! ## The answer -/

/-- **MO 184460 (answer: yes).** For every `μ ∈ ℝ` and every `a < b`, the truncated Gaussians
`P = N(-μ,1)|[a,b]` and `Q = N(μ,1)|[a,b]` satisfy `d_H²(P,Q) ≤ d_H(P,Q) ≤ d_TV(P,Q)`. -/
theorem answer (μ a b : ℝ) (hab : a < b) :
    dH (truncGauss (-μ) a b) (truncGauss μ a b) ^ 2 ≤ dH (truncGauss (-μ) a b) (truncGauss μ a b) ∧
      dH (truncGauss (-μ) a b) (truncGauss μ a b) ≤ dTV (truncGauss (-μ) a b) (truncGauss μ a b) := by
  have main : dH (truncGauss (-μ) a b) (truncGauss μ a b) ≤
      dTV (truncGauss (-μ) a b) (truncGauss μ a b) := by
    rw [dH_eq, dTV_eq]; exact HellingerTV.mo184460_Icc μ a b hab
  obtain ⟨p0, ip, p1⟩ := truncGauss_density (-μ) hab
  obtain ⟨q0, iq, q1⟩ := truncGauss_density μ hab
  have tv1 := dTV_le_one p0 q0 ip iq p1 q1
  have h0 : 0 ≤ dH (truncGauss (-μ) a b) (truncGauss μ a b) := Real.sqrt_nonneg _
  exact ⟨by nlinarith, main⟩

/-- **Strict form.** For `μ ≠ 0` and `a < b`, `d_H(P,Q) < d_TV(P,Q)`. -/
theorem answer_strict {μ : ℝ} (hμ : μ ≠ 0) {a b : ℝ} (hab : a < b) :
    dH (truncGauss (-μ) a b) (truncGauss μ a b) < dTV (truncGauss (-μ) a b) (truncGauss μ a b) := by
  rw [dH_eq, dTV_eq]; exact HellingerTV.mo184460_Icc_strict hμ hab

/-! ## The full chain for any interval (in the vocabulary of `HellingerTV.lean`)

`answer` covers closed intervals `[a, b]`. For truncation to any interval `I` of positive length
(open, half-open, a half-line or `ℝ`), the full chain also holds. -/

theorem chain_interval (μ : ℝ) {I : Set ℝ} (hI : I.OrdConnected) (hvol : volume I ≠ 0) :
    HellingerTV.hellinger (HellingerTV.tgauss (-μ) I) (HellingerTV.tgauss μ I) ^ 2 ≤
        HellingerTV.hellinger (HellingerTV.tgauss (-μ) I) (HellingerTV.tgauss μ I) ∧
      HellingerTV.hellinger (HellingerTV.tgauss (-μ) I) (HellingerTV.tgauss μ I) ≤
        HellingerTV.tvDens (HellingerTV.tgauss (-μ) I) (HellingerTV.tgauss μ I) := by
  have main := HellingerTV.mo184460 μ hI hvol
  obtain ⟨ip, p1⟩ := HellingerTV.tgauss_integral (-μ) hI hvol
  obtain ⟨iq, q1⟩ := HellingerTV.tgauss_integral μ hI hvol
  have nn : ∀ θ x, 0 ≤ HellingerTV.tgauss θ I x := fun θ x => by
    unfold HellingerTV.tgauss
    exact div_nonneg (indicator_nonneg (fun y _ => (ProbabilityTheory.gaussianPDFReal_pos θ 1 y one_ne_zero).le) x)
      (integral_nonneg fun y => (ProbabilityTheory.gaussianPDFReal_pos θ 1 y one_ne_zero).le)
  have tv1 : HellingerTV.tvDens (HellingerTV.tgauss (-μ) I) (HellingerTV.tgauss μ I) ≤ 1 :=
    dTV_le_one (nn (-μ)) (nn μ) ip iq p1 q1
  have h0 := Real.sqrt_nonneg
    ((1 / 2) * ∫ x, (√(HellingerTV.tgauss (-μ) I x) - √(HellingerTV.tgauss μ I x)) ^ 2)
  change 0 ≤ HellingerTV.hellinger (HellingerTV.tgauss (-μ) I) (HellingerTV.tgauss μ I) at h0
  exact ⟨by nlinarith, main⟩

end HellingerTVCheck

