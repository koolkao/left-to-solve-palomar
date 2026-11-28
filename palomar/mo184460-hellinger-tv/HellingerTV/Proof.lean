/-
Copyright 2026 Ming-Chih Kao. Licensed under the Apache License, Version 2.0;
see the LICENSE file at the root of this repository.
-/
module

public import Mathlib

/-! Port: copied from `MO184460.lean` of github.com/koolkao/mo184460-hellinger-tv (commit
b2b49dcf336bcab5835d78cab9686f7ba9ee4b79, v1.0.0, Lean v4.36.0, same Mathlib) and put into the module system:
the `module` header, `public import`, a public section, and the namespaces `MO184460` and `MO184460Check`
renamed `HellingerTV` and `HellingerTVCheck` so that `Solution.lean` can state the compared theorems
under the names `MO184460.*`; the `#print axioms` report is dropped. The mathematics and the proofs are
unchanged. -/

@[expose] public section

/-!
# MathOverflow 184460: Hellinger distance ≤ total variation for truncated Gaussians

Ming-Chih Kao (Stanford University), 27 November 2026. Lean v4.36.0, Mathlib `fc4f59e577`.
The mathematics is in `NOTE.md`; `Check.lean` restates the question independently.

Main results:
* `mo184460_Icc`, `mo184460`: for `P = N(-μ,1)` and `Q = N(μ,1)` truncated to `[a,b]` (`a < b`; more generally
  to any interval of positive length), `d_H(P,Q) ≤ d_TV(P,Q)` with `d_TV = (1/2)∫|p - q|` and
  `d_H² = (1/2)∫(√p - √q)²`, for every real `μ`.
* `mo184460_Icc_strict`, `mo184460_strict`: strict inequality for `μ ≠ 0`.
* `thm3`, `thm3_strict`: Theorem 3 of `NOTE.md` in homogeneous form: for a log-concave `f ≥ 0` on `ℝ` with
  `f cosh` integrable and `∫ f sinh = 0`, `(∫ f cosh) (∫ f cosh - ∫ f) ≤ (∫ f |sinh|)²`; strict when `f` is
  strictly log-concave and `∫ f > 0`.

Not formalized here: Theorem 2 of `NOTE.md` (the measure-level statement for a log-concave likelihood ratio) and
the equality characterisation (the Laplace family). They are proved on paper in `NOTE.md`.
-/

namespace HellingerTV

-- ===== Proposition D (the two-variable inequality) =====

/-!
# Proposition D (two-variable form)

For `0 ≤ A ≤ B`, `0 < B`:
  `cosh A cosh B (cosh A cosh B - 1) ≤ (2 cosh A cosh B sinh B ^ 2 exp (-(B - A) * (cosh B / sinh B)) / sinh (A + B)) ^ 2`.
With `a = coth A`, `b = coth B` this is `(E|sinh S|)^2 ≥ E cosh S (E cosh S - 1)` for the asymmetric Laplace law
with mode `B - A`, left rate `b`, right rate `a` (see `NOTE.md`, Section 4).
-/

open Real

lemma R_nonneg {p q : ℝ} (hp : 1 ≤ p) (hq : 1 ≤ q) :
    0 ≤ p^3*q^3 + p^3*q - 2*p^2*q^2 + 2*p*q - q^2 - 1 := by
  have h1 : 0 ≤ (q-1)^3 := pow_nonneg (by linarith) 3
  have h2 : 0 ≤ (p-1)*q*(p^2*q^2 + p^2 + p*(q-1)^2 + (q-1)^2 + 2) := by
    apply mul_nonneg (mul_nonneg (by linarith) (by linarith))
    have : 0 ≤ p*(q-1)^2 := mul_nonneg (by linarith) (sq_nonneg _)
    positivity
  have e : p^3*q^3 + p^3*q - 2*p^2*q^2 + 2*p*q - q^2 - 1
      = (q-1)^3 + (p-1)*q*(p^2*q^2 + p^2 + p*(q-1)^2 + (q-1)^2 + 2) := by ring
  rw [e]; exact add_nonneg h1 h2

theorem K_nonneg {A B : ℝ} (hA : 0 ≤ A) (hAB : A ≤ B) :
    2 * cosh A * (cosh A * cosh B - 1) ≤ sinh B * sinh (A + B) := by
  set p := exp A with hpdef
  set q := exp B with hqdef
  have hp1 : 1 ≤ p := by rw [hpdef]; exact one_le_exp hA
  have hpq : p ≤ q := by rw [hpdef, hqdef]; exact exp_le_exp.mpr hAB
  have hq1 : 1 ≤ q := le_trans hp1 hpq
  have hp0 : 0 < p := by linarith
  have hq0 : 0 < q := by linarith
  have cA : cosh A = (p + p⁻¹)/2 := by rw [cosh_eq, exp_neg]
  have cB : cosh B = (q + q⁻¹)/2 := by rw [cosh_eq, exp_neg]
  have sB : sinh B = (q - q⁻¹)/2 := by rw [sinh_eq, exp_neg]
  have sAB : sinh (A+B) = (p*q - (p*q)⁻¹)/2 := by rw [sinh_eq, exp_neg, exp_add]
  rw [cA, cB, sB, sAB]
  rw [← sub_nonneg]
  have e : (q - q⁻¹)/2 * ((p*q - (p*q)⁻¹)/2) - 2 * ((p + p⁻¹)/2) * ((p + p⁻¹)/2 * ((q + q⁻¹)/2) - 1)
      = (q - p) * (p^3*q^3 + p^3*q - 2*p^2*q^2 + 2*p*q - q^2 - 1) / (4 * p^2 * q^2) := by
    field_simp
    ring
  rw [e]
  apply div_nonneg (mul_nonneg (by linarith) (R_nonneg hp1 hq1))
  positivity

/-- `cosh A * cosh B - 1 > 0` for `B > 0`. -/
lemma cc_pos {A B : ℝ} (hB : 0 < B) : 0 < cosh A * cosh B - 1 := by
  have h1 : 1 ≤ cosh A := one_le_cosh A
  have h2 : 1 < cosh B := one_lt_cosh.mpr hB.ne'
  nlinarith

/-- The function `G(·, B)` of `NOTE.md`. -/
noncomputable def G (B A : ℝ) : ℝ :=
  log 4 + log (cosh A) + log (cosh B) + 4 * log (sinh B) - 2 * (B - A) * (cosh B / sinh B)
    - 2 * log (sinh (A + B)) - log (cosh A * cosh B - 1)

lemma G_self {B : ℝ} (hB : 0 < B) : G B B = 0 := by
  have hs : 0 < sinh B := sinh_pos_iff.mpr hB
  have hc : 0 < cosh B := cosh_pos B
  unfold G
  have h2 : sinh (B + B) = 2 * sinh B * cosh B := by rw [← two_mul, sinh_two_mul]
  have h3 : cosh B * cosh B - 1 = sinh B ^ 2 := by nlinarith [cosh_sq B]
  rw [h2, h3, sub_self, mul_zero, zero_mul, sub_zero]
  rw [log_mul (by positivity) hc.ne', log_mul (by norm_num) hs.ne', log_pow]
  have : log 4 = 2 * log 2 := by
    rw [show (4:ℝ) = 2^2 by norm_num, log_pow]; norm_num
  rw [this]; push_cast; ring

lemma hasDerivAt_G {A B : ℝ} (hA : 0 ≤ A) (hB : 0 < B) :
    HasDerivAt (G B)
      (sinh A / cosh A + 2 * (cosh B / sinh B) - 2 * (cosh (A + B) / sinh (A + B))
        - sinh A * cosh B / (cosh A * cosh B - 1)) A := by
  have hcA : 0 < cosh A := cosh_pos A
  have hsAB : 0 < sinh (A + B) := sinh_pos_iff.mpr (by linarith)
  have hcc : 0 < cosh A * cosh B - 1 := cc_pos hB
  have d1 : HasDerivAt (fun x => log (cosh x)) (sinh A / cosh A) A := by
    have := (hasDerivAt_cosh A).log hcA.ne'; simpa using this
  have d2 : HasDerivAt (fun x => -2 * (B - x) * (cosh B / sinh B)) (2 * (cosh B / sinh B)) A := by
    have := ((hasDerivAt_id A).const_sub B).const_mul (-2) |>.mul_const (cosh B / sinh B)
    simpa using this
  have d3 : HasDerivAt (fun x => sinh (x + B)) (cosh (A + B)) A := by
    have := ((hasDerivAt_id A).add_const B).sinh; simpa using this
  have d4 : HasDerivAt (fun x => -2 * log (sinh (x + B))) (-2 * (cosh (A + B) / sinh (A + B))) A :=
    (d3.log hsAB.ne').const_mul (-2)
  have d5 : HasDerivAt (fun x => cosh x * cosh B - 1) (sinh A * cosh B) A := by
    have := ((hasDerivAt_cosh A).mul_const (cosh B)).sub_const 1; simpa using this
  have d6 : HasDerivAt (fun x => -log (cosh x * cosh B - 1)) (-(sinh A * cosh B / (cosh A * cosh B - 1))) A :=
    (d5.log hcc.ne').neg
  have := ((((d1.const_add (log 4)).add_const (log (cosh B))).add_const (4 * log (sinh B))).add d2).add d4 |>.add d6
  convert this using 1
  · funext x; simp only [Pi.add_apply]; unfold G; ring
  · ring

lemma deriv_G_nonpos {A B : ℝ} (hA : 0 < A) (hAB : A ≤ B) :
    sinh A / cosh A + 2 * (cosh B / sinh B) - 2 * (cosh (A + B) / sinh (A + B))
      - sinh A * cosh B / (cosh A * cosh B - 1) ≤ 0 := by
  have hB : 0 < B := lt_of_lt_of_le hA hAB
  have hcA : 0 < cosh A := cosh_pos A
  have hsA : 0 < sinh A := sinh_pos_iff.mpr hA
  have hsB : 0 < sinh B := sinh_pos_iff.mpr hB
  have hsAB : 0 < sinh (A + B) := sinh_pos_iff.mpr (by linarith)
  have hcc : 0 < cosh A * cosh B - 1 := cc_pos hB
  have hK := K_nonneg hA.le hAB
  -- cosh B sinh(A+B) - cosh(A+B) sinh B = sinh A
  have hsub : cosh B * sinh (A + B) - cosh (A + B) * sinh B = sinh A := by
    rw [sinh_add, cosh_add]; nlinarith [cosh_sq B]
  have e : sinh A / cosh A + 2 * (cosh B / sinh B) - 2 * (cosh (A + B) / sinh (A + B))
      - sinh A * cosh B / (cosh A * cosh B - 1)
      = - sinh A * (sinh B * sinh (A + B) - 2 * cosh A * (cosh A * cosh B - 1))
          / (sinh B * sinh (A + B) * cosh A * (cosh A * cosh B - 1)) := by
    field_simp
    linear_combination (2 * cosh A * (cosh A * cosh B - 1)) * hsub
  rw [e]
  apply div_nonpos_of_nonpos_of_nonneg
  · have : 0 ≤ sinh A * (sinh B * sinh (A + B) - 2 * cosh A * (cosh A * cosh B - 1)) :=
      mul_nonneg hsA.le (by linarith)
    linarith
  · positivity

lemma G_nonneg {A B : ℝ} (hA : 0 ≤ A) (hAB : A ≤ B) (hB : 0 < B) : 0 ≤ G B A := by
  -- G(·,B) is continuous on [0,B] and has nonpositive derivative on (0,B), so G B A ≥ G B B = 0.
  have hcont : ContinuousOn (G B) (Set.Icc 0 B) := fun x hx =>
    (hasDerivAt_G hx.1 hB).continuousAt.continuousWithinAt
  have hanti : AntitoneOn (G B) (Set.Icc 0 B) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc 0 B) hcont
    · intro x hx
      rw [interior_Icc] at hx
      exact (hasDerivAt_G hx.1.le hB).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      rw [(hasDerivAt_G hx.1.le hB).deriv]
      exact deriv_G_nonpos hx.1 hx.2.le
  have := hanti ⟨hA, hAB⟩ ⟨hB.le, le_refl B⟩ hAB
  rw [G_self hB] at this; exact this

/-- Proposition D, two-variable form. -/
theorem propD {A B : ℝ} (hA : 0 ≤ A) (hAB : A ≤ B) (hB : 0 < B) :
    cosh A * cosh B * (cosh A * cosh B - 1)
      ≤ (2 * cosh A * cosh B * sinh B ^ 2 * exp (-(B - A) * (cosh B / sinh B)) / sinh (A + B)) ^ 2 := by
  have hG := G_nonneg hA hAB hB
  have hsB : 0 < sinh B := sinh_pos_iff.mpr hB
  have hsAB : 0 < sinh (A + B) := sinh_pos_iff.mpr (by linarith)
  have hcA : 0 < cosh A := cosh_pos A
  have hcB : 0 < cosh B := cosh_pos B
  have hcc : 0 < cosh A * cosh B - 1 := cc_pos hB
  set L := cosh A * cosh B * (cosh A * cosh B - 1) with hL
  set R := (2 * cosh A * cosh B * sinh B ^ 2 * exp (-(B - A) * (cosh B / sinh B)) / sinh (A + B)) ^ 2 with hR
  have hLpos : 0 < L := by positivity
  have hRpos : 0 < R := by positivity
  have hR' : log R = 2 * (log 2 + log (cosh A) + log (cosh B) + 2 * log (sinh B)
      + (-(B - A) * (cosh B / sinh B)) - log (sinh (A + B))) := by
    rw [hR, log_pow, log_div (by positivity) hsAB.ne', log_mul (by positivity) (exp_pos _).ne', log_exp,
      log_mul (by positivity) (by positivity), log_mul (by positivity) hcB.ne',
      log_mul (by norm_num) hcA.ne', log_pow]
    push_cast; ring
  have hL' : log L = log (cosh A) + log (cosh B) + log (cosh A * cosh B - 1) := by
    rw [hL, log_mul (by positivity) hcc.ne', log_mul hcA.ne' hcB.ne']
  have h4 : log 4 = 2 * log 2 := by
    rw [show (4:ℝ) = 2^2 by norm_num, log_pow]; norm_num
  have hlog : log R - log L = G B A := by
    rw [hR', hL']; unfold G; rw [h4]; ring
  have : log L ≤ log R := by linarith
  exact (log_le_log_iff hLpos hRpos).mp this



-- ===== Asymmetric Laplace moments =====

/-!
# Asymmetric Laplace computations

`lap c α u m` is the unnormalised asymmetric Laplace density
`c e^{α s}` for `s ≤ m` and `c e^{α m} e^{-(s-m)/u}` for `s > m` (zero for `s > m` when `u = 0`).
Here `α = coth B` is the left rate and `u = tanh A = 1/(right rate)`.
We compute its exponential moments and reduce the inequality
`(E|sinh|)² ≥ E cosh (E cosh - E 1)` (homogeneous Prop. D of `NOTE.md`) to `propD`.
-/

open Real MeasureTheory Set

/-- Right tail `e^{-(s-m)/u}`, with the convention that it vanishes for `u = 0`. -/
noncomputable def tl (u m s : ℝ) : ℝ := if u = 0 then 0 else exp (-(s - m) / u)

/-- The unnormalised asymmetric Laplace density. -/
noncomputable def lap (c α u m s : ℝ) : ℝ :=
  if s ≤ m then c * exp (α * s) else c * exp (α * m) * tl u m s

lemma tl_nonneg (u m s : ℝ) : 0 ≤ tl u m s := by
  unfold tl; split_ifs <;> positivity

lemma lap_nonneg {c : ℝ} (hc : 0 ≤ c) (α u m s : ℝ) : 0 ≤ lap c α u m s := by
  unfold lap; split_ifs
  · positivity
  · have := tl_nonneg u m s; positivity

lemma tl_mom {u m l : ℝ} (hu0 : 0 ≤ u) (hlu : l * u < 1) :
    IntegrableOn (fun s => tl u m s * exp (l * s)) (Ioi m) ∧
      ∫ s in Ioi m, tl u m s * exp (l * s) = exp (l * m) * u / (1 - l * u) := by
  rcases hu0.eq_or_lt with h | hu
  · subst h
    simp [tl]
  · have hk : l - 1 / u < 0 := by
      rw [sub_neg, lt_div_iff₀ hu]; linarith
    have heq : (fun s => tl u m s * exp (l * s)) = fun s => exp (m / u) * exp ((l - 1 / u) * s) := by
      funext s; unfold tl; rw [ite_eq_right hu.ne', ← exp_add, ← exp_add]; congr 1; field_simp; ring
    rw [heq]
    refine ⟨(integrableOn_exp_mul_Ioi hk m).const_mul _, ?_⟩
    rw [integral_const_mul, integral_exp_mul_Ioi hk]
    have h1 : 1 - l * u ≠ 0 := by linarith
    have h2 : l - 1 / u ≠ 0 := hk.ne
    have e : exp (m / u) * exp ((l - 1 / u) * m) = exp (l * m) := by
      rw [← exp_add]; congr 1; field_simp; ring
    calc _ = -(exp (m / u) * exp ((l - 1 / u) * m)) / (l - 1 / u) := by ring
      _ = _ := by
        rw [e]
        have h3 : l * u - 1 ≠ 0 := by intro h; apply h1; linarith
        field_simp
        ring

lemma lap_mom {c α u m l : ℝ} (hαl : 0 < α + l) (hu0 : 0 ≤ u) (hlu : l * u < 1) :
    Integrable (fun s => lap c α u m s * exp (l * s)) ∧
      ∫ s, lap c α u m s * exp (l * s) =
        c * exp ((α + l) * m) * (1 / (α + l) + u / (1 - l * u)) := by
  obtain ⟨hti, htv⟩ := tl_mom (m := m) hu0 hlu
  have hL : EqOn (fun s => lap c α u m s * exp (l * s)) (fun s => c * exp ((α + l) * s)) (Iic m) := by
    intro s hs; simp only [lap, ite_eq_left (show s ≤ m from hs)]; rw [mul_assoc, ← exp_add]; ring_nf
  have hR : EqOn (fun s => lap c α u m s * exp (l * s))
      (fun s => c * exp (α * m) * (tl u m s * exp (l * s))) (Ioi m) := by
    intro s hs; simp only [lap, ite_eq_right (not_le.mpr (show m < s from hs))]; ring
  have iL : IntegrableOn (fun s => lap c α u m s * exp (l * s)) (Iic m) :=
    IntegrableOn.congr_fun ((integrableOn_exp_mul_Iic hαl m).const_mul c) hL.symm measurableSet_Iic
  have iR : IntegrableOn (fun s => lap c α u m s * exp (l * s)) (Ioi m) :=
    IntegrableOn.congr_fun (hti.const_mul (c * exp (α * m))) hR.symm measurableSet_Ioi
  refine ⟨?_, ?_⟩
  · have := iL.union iR; rwa [Iic_union_Ioi, integrableOn_univ] at this
  · rw [← intervalIntegral.integral_Iic_add_Ioi iL iR, setIntegral_congr_fun measurableSet_Iic hL,
      setIntegral_congr_fun measurableSet_Ioi hR, integral_const_mul, integral_const_mul,
      integral_exp_mul_Iic hαl, htv]
    have : exp ((α + l) * m) = exp (α * m) * exp (l * m) := by rw [← exp_add]; ring_nf
    rw [this]; ring

/-- Moments of `lap` over `Ioi 0` (for `m ≥ 0`). -/
lemma lap_mom_Ioi {c α u m l : ℝ} (hm : 0 ≤ m) (hαl : 0 < α + l) (hu0 : 0 ≤ u) (hlu : l * u < 1) :
    IntegrableOn (fun s => lap c α u m s * exp (l * s)) (Ioi 0) ∧
      ∫ s in Ioi 0, lap c α u m s * exp (l * s) =
        c * exp ((α + l) * m) * (1 / (α + l) + u / (1 - l * u)) - c / (α + l) := by
  obtain ⟨hi, hv⟩ := lap_mom (c := c) (m := m) hαl hu0 hlu
  have hL : EqOn (fun s => lap c α u m s * exp (l * s)) (fun s => c * exp ((α + l) * s)) (Iic 0) := by
    intro s hs; simp only [lap, ite_eq_left (le_trans (show s ≤ 0 from hs) hm)]
    rw [mul_assoc, ← exp_add]; ring_nf
  have iL : IntegrableOn (fun s => lap c α u m s * exp (l * s)) (Iic 0) := hi.integrableOn
  refine ⟨hi.integrableOn, ?_⟩
  have := intervalIntegral.integral_Iic_add_Ioi iL hi.integrableOn
  rw [hv, setIntegral_congr_fun measurableSet_Iic hL, integral_const_mul, integral_exp_mul_Iic hαl]
    at this
  simp only [mul_zero, exp_zero] at this
  have h2 : c * (1 / (α + l)) = c / (α + l) := by ring
  linarith

/-! ## Reduction of the homogeneous Proposition D to `propD` -/

set_option maxHeartbeats 1000000 in
/-- Algebraic core: with `C = E cosh = E e^{s}` (when `E sinh = 0`) and `Z = E 1`,
`C (C - Z) ≤ (2 D)²` where `D = c/(α²-1)` is the left `|sinh|`-moment. -/
theorem lap_alg {c α u m : ℝ} (hc : 0 < c) (hα : 1 < α) (hu0 : 0 ≤ u) (hu1 : u < 1) (hm : 0 ≤ m)
    (hE : c * exp ((α + 1) * m) * (1 / (α + 1) + u / (1 - u)) =
      c * exp ((α - 1) * m) * (1 / (α - 1) + u / (1 + u))) :
    c * exp ((α + 1) * m) * (1 / (α + 1) + u / (1 - u)) *
        (c * exp ((α + 1) * m) * (1 / (α + 1) + u / (1 - u)) - c * exp (α * m) * (1 / α + u))
      ≤ (2 * (c / (α ^ 2 - 1))) ^ 2 := by
  -- the parameters A = artanh u, B = arcoth α
  have hα1 : 0 < α - 1 := by linarith
  have hu1' : 0 < 1 - u := by linarith
  set B := log ((α + 1) / (α - 1)) / 2 with hB
  set A := log ((1 + u) / (1 - u)) / 2 with hA
  have hqB : exp B ^ 2 = (α + 1) / (α - 1) := by
    rw [← exp_nat_mul, hB]; push_cast
    rw [show (2:ℝ) * (log ((α + 1) / (α - 1)) / 2) = log ((α + 1) / (α - 1)) by ring,
      exp_log (by positivity)]
  have hqA : exp A ^ 2 = (1 + u) / (1 - u) := by
    rw [← exp_nat_mul, hA]; push_cast
    rw [show (2:ℝ) * (log ((1 + u) / (1 - u)) / 2) = log ((1 + u) / (1 - u)) by ring,
      exp_log (by positivity)]
  have hB0 : 0 < B := by
    rw [hB]; apply div_pos _ two_pos; apply log_pos; rw [one_lt_div hα1]; linarith
  have hA0 : 0 ≤ A := by
    rw [hA]; apply div_nonneg _ two_pos.le; apply log_nonneg; rw [one_le_div hu1']; linarith
  -- coth B = α and tanh A = u
  have hsB : 0 < sinh B := sinh_pos_iff.mpr hB0
  have hcothB : α * sinh B = cosh B := by
    rw [sinh_eq, cosh_eq, exp_neg]
    have hy : 0 < exp B := exp_pos B
    have : exp B ^ 2 * (α - 1) = α + 1 := by rw [hqB]; field_simp
    field_simp
    nlinarith
  have htanhA : u * cosh A = sinh A := by
    rw [sinh_eq, cosh_eq, exp_neg]
    have hy : 0 < exp A := exp_pos A
    have : exp A ^ 2 * (1 - u) = 1 + u := by rw [hqA]; field_simp
    field_simp
    nlinarith
  -- m = B - A from the balance condition
  have hm' : m = B - A := by
    have hP : 0 < 1 / (α + 1) + u / (1 - u) := by positivity
    have h1 : exp (2 * m) * (1 / (α + 1) + u / (1 - u)) = 1 / (α - 1) + u / (1 + u) := by
      have e1 : exp ((α + 1) * m) = exp ((α - 1) * m) * exp (2 * m) := by rw [← exp_add]; ring_nf
      rw [e1] at hE
      have hpos : 0 < c * exp ((α - 1) * m) := by positivity
      have := hE
      field_simp at this ⊢
      nlinarith [this, hpos]
    have h2 : exp (2 * (B - A)) * (1 / (α + 1) + u / (1 - u)) = 1 / (α - 1) + u / (1 + u) := by
      have : exp (2 * (B - A)) = exp B ^ 2 / exp A ^ 2 := by
        rw [← exp_nat_mul, ← exp_nat_mul, ← exp_sub]; push_cast; ring_nf
      rw [this, hqA, hqB]
      field_simp; ring
    have : exp (2 * m) = exp (2 * (B - A)) := by
      have := h1.trans h2.symm
      exact mul_right_cancel₀ hP.ne' this
    have := exp_injective this
    linarith
  have hAB : A ≤ B := by linarith
  have hD := propD hA0 hAB hB0
  -- translate
  set cA := cosh A
  set sA := sinh A
  set cB := cosh B
  set sB := sinh B
  have hcA : 0 < cA := cosh_pos A
  have hcB : 0 < cB := cosh_pos B
  have hsA : 0 ≤ sA := sinh_nonneg_iff.mpr hA0
  have hidA : cA ^ 2 - sA ^ 2 = 1 := by rw [← cosh_sq_sub_sinh_sq A]
  have hidB : cB ^ 2 - sB ^ 2 = 1 := by rw [← cosh_sq_sub_sinh_sq B]
  have hsAB : sinh (A + B) = sA * cB + cA * sB := by rw [sinh_add]
  rw [hsAB] at hD
  have hsABpos : 0 < sA * cB + cA * sB := by positivity
  set E := exp (α * m) with hEdef
  have hEpos : 0 < E := exp_pos _
  have hX : exp (-(B - A) * (cB / sB)) = 1 / E := by
    rw [hEdef, hm', one_div, ← exp_neg, ← hcothB]; congr 1; field_simp
  rw [hX] at hD
  have hem : exp m = (cB + sB) * (cA - sA) := by
    rw [hm', exp_sub, ← cosh_add_sinh B, div_eq_mul_inv, ← exp_neg, ← cosh_sub_sinh A]
  have hp1 : exp ((α + 1) * m) = E * exp m := by rw [hEdef, ← exp_add]; ring_nf
  rw [hp1, hem]
  have hα' : α = cB / sB := by field_simp; linarith
  have hu' : u = sA / cA := by field_simp; linarith
  have hC : (cB + sB) * (cA - sA) * (1 / (α + 1) + u / (1 - u)) = sA * cB + cA * sB := by
    rw [hα', hu']
    have h1 : cB / sB + 1 ≠ 0 := by
      have : 0 < cB / sB + 1 := by positivity
      exact this.ne'
    have h2 : 1 - sA / cA ≠ 0 := by
      have : sA / cA < 1 := by rw [div_lt_one hcA, ← htanhA]; nlinarith
      linarith
    have h3 : cA - sA ≠ 0 := by
      intro h; apply h2; rw [show sA = cA by linarith, div_self hcA.ne']; ring
    field_simp
    ring
  have hZ : 1 / α + u = (sA * cB + cA * sB) / (cA * cB) := by
    rw [hα', hu']; field_simp; ring
  have hDD : c / (α ^ 2 - 1) = c * sB ^ 2 := by
    rw [hα']; field_simp; linear_combination -hidB
  rw [show c * (E * ((cB + sB) * (cA - sA))) * (1 / (α + 1) + u / (1 - u))
      = c * E * ((cB + sB) * (cA - sA) * (1 / (α + 1) + u / (1 - u))) by ring, hC, hZ, hDD]
  -- now: c E S (c E S - c E S/(cA cB)) ≤ (2 c sB²)²  from propD
  set S := sA * cB + cA * sB
  have hP : 0 < cA * cB := by positivity
  have key : cA * cB * (cA * cB - 1) * (S ^ 2 * E ^ 2) ≤ 4 * sB ^ 4 * (cA * cB) ^ 2 := by
    have := mul_le_mul_of_nonneg_right hD (show 0 ≤ S ^ 2 * E ^ 2 by positivity)
    calc cA * cB * (cA * cB - 1) * (S ^ 2 * E ^ 2)
        ≤ (2 * cA * cB * sB ^ 2 * (1 / E) / S) ^ 2 * (S ^ 2 * E ^ 2) := this
      _ = 4 * sB ^ 4 * (cA * cB) ^ 2 := by field_simp; ring
  have goal' : c * E * S * (c * E * S - c * E * (S / (cA * cB))) =
      c ^ 2 * (cA * cB * (cA * cB - 1) * (S ^ 2 * E ^ 2)) / (cA * cB) ^ 2 := by
    field_simp
  rw [goal', div_le_iff₀ (by positivity)]
  nlinarith [key, sq_nonneg c]

-- ===== Crossing lemmas (Lemma A) and the tangent bound =====

/-!
# Crossing lemmas

* `LC f`: `f = J.indicator (exp ∘ ψ)` with `J` an interval and `ψ` concave on `J` (log-concave density).
* `lemA`: Lemma A of `NOTE.md` (non-strict): if `∫ φ = ∫ φ sinh = 0` on `(0,∞)` and `{φ < 0}` is an interval,
  then `∫ φ cosh ≥ 0`. Test functions `cosh (t - m₀) - cosh d` (bounded case) and `e^{-t} - e^{-x₁}`
  (unbounded case), as suggested by an automated referee review.
* `tangent`: the claim of Step 2 of Lemma C: `f s ≤ c e^{α s}` for `s ≥ 0`.
-/

open Real MeasureTheory Set

/-- `f` is a log-concave function: the indicator of an interval times `exp` of a concave function. -/
def LC (f : ℝ → ℝ) : Prop :=
  ∃ J : Set ℝ, ∃ ψ : ℝ → ℝ, J.OrdConnected ∧ ConcaveOn ℝ J ψ ∧ f = J.indicator (fun s => exp (ψ s))

lemma LC.nonneg {f : ℝ → ℝ} (hf : LC f) (s : ℝ) : 0 ≤ f s := by
  obtain ⟨J, ψ, -, -, rfl⟩ := hf
  unfold indicator; split_ifs <;> positivity

/-- Superlevel sets `{K e^{β s} < f s}` (with `K ≥ 0`) of a log-concave `f` are intervals. -/
lemma LC.superlevel {f : ℝ → ℝ} (hf : LC f) {K : ℝ} (hK : 0 ≤ K) (β : ℝ) :
    {s | K * exp (β * s) < f s}.OrdConnected := by
  obtain ⟨J, ψ, hJ, hψ, rfl⟩ := hf
  have mem : ∀ s, K * exp (β * s) < J.indicator (fun s => exp (ψ s)) s → s ∈ J := by
    intro s hs; by_contra h; rw [indicator_of_notMem h] at hs
    have : 0 ≤ K * exp (β * s) := by positivity
    linarith
  rcases hK.eq_or_lt with h0 | hK
  · subst h0
    have : {s | 0 * exp (β * s) < J.indicator (fun s => exp (ψ s)) s} = J := by
      ext s; constructor
      · exact mem s
      · intro hs; simp only [mem_ofPred_eq, zero_mul, indicator_of_mem hs]; positivity
    rw [this]; exact hJ
  · refine ⟨fun x hx y hy z hz => ?_⟩
    have hxJ := mem x hx
    have hyJ := mem y hy
    have hzJ : z ∈ J := hJ.out hxJ hyJ hz
    simp only [mem_ofPred_eq, indicator_of_mem hxJ, indicator_of_mem hyJ, indicator_of_mem hzJ] at hx hy ⊢
    have ek : ∀ s, K * exp (β * s) = exp (log K + β * s) := by
      intro s; rw [exp_add, exp_log hK]
    rw [ek, exp_lt_exp] at hx hy ⊢
    rcases eq_or_lt_of_le (hz.1.trans hz.2) with hxy | hxy
    · have : z = x := le_antisymm (hxy ▸ hz.2) hz.1
      rw [this]; exact hx
    · set a := (y - z) / (y - x)
      set b := (z - x) / (y - x)
      have hyx : 0 < y - x := by linarith
      have ha : 0 ≤ a := div_nonneg (by linarith [hz.2]) hyx.le
      have hb : 0 ≤ b := div_nonneg (by linarith [hz.1]) hyx.le
      have hab : a + b = 1 := by simp only [a, b]; field_simp; ring
      have hcomb : a • x + b • y = z := by simp only [smul_eq_mul, a, b]; field_simp; ring
      have hc := hψ.2 hxJ hyJ ha hb hab
      rw [hcomb] at hc
      simp only [smul_eq_mul] at hc
      have p1 : 0 < ψ x - (log K + β * x) := by linarith
      have p2 : 0 < ψ y - (log K + β * y) := by linarith
      have : 0 < a * (ψ x - (log K + β * x)) + b * (ψ y - (log K + β * y)) := by
        rcases ha.eq_or_lt with ha0 | ha0
        · rw [← ha0] at hab ⊢; rw [show b = 1 by linarith]; linarith
        · nlinarith [mul_pos ha0 p1, mul_nonneg hb p2.le]
      have hz' : β * z = a * (β * x) + b * (β * y) := by rw [← hcomb]; simp only [smul_eq_mul]; ring
      have e : a * (log K + β * x) + b * (log K + β * y) = log K + β * z := by
        rw [hz']; linear_combination (log K) * hab
      linarith

lemma LC.neg {f : ℝ → ℝ} (hf : LC f) : LC (fun s => f (-s)) := by
  obtain ⟨J, ψ, hJ, hψ, rfl⟩ := hf
  refine ⟨(fun s => -s) ⁻¹' J, fun s => ψ (-s), ?_, ?_, ?_⟩
  · refine ⟨fun x hx y hy z hz => ?_⟩
    exact hJ.out hy hx ⟨neg_le_neg hz.2, neg_le_neg hz.1⟩
  · have hJ' : ((fun s : ℝ => -s) ⁻¹' J).OrdConnected :=
      ⟨fun x hx y hy z hz => hJ.out hy hx ⟨neg_le_neg hz.2, neg_le_neg hz.1⟩⟩
    refine ⟨hJ'.convex, fun x hx y hy a b ha hb hab => ?_⟩
    have := hψ.2 hx hy ha hb hab
    simp only [smul_eq_mul] at this ⊢
    rw [show -(a * x + b * y) = a * -x + b * -y by ring]; exact this
  · funext s; simp only [indicator, mem_preimage]; rfl

/-- A nonnegative integrable function that is positive on `(0, τ)` has positive integral over `(0,∞)`. -/
lemma posint {k : ℝ → ℝ} {τ : ℝ} (hτ : 0 < τ) (hi : IntegrableOn k (Ioi 0))
    (hnn : ∀ t ∈ Ioi (0:ℝ), 0 ≤ k t) (hpos : ∀ t ∈ Ioo 0 τ, 0 < k t) : 0 < ∫ t in Ioi 0, k t := by
  have hae : 0 ≤ᵐ[volume.restrict (Ioi 0)] k := by
    rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_Ioi]
    exact Filter.Eventually.of_forall fun t ht => hnn t ht
  rw [setIntegral_pos_iff_support_of_nonneg_ae hae hi]
  have hsub : Ioo 0 τ ⊆ Function.support k ∩ Ioi 0 := fun t ht =>
    ⟨(hpos t ht).ne', ht.1⟩
  calc (0 : ENNReal) < volume (Ioo 0 τ) := by simp [hτ]
    _ ≤ _ := measure_mono hsub

lemma exists_ae {P : ℝ → Prop} (h : ∀ᵐ t ∂(volume.restrict (Ioi (0:ℝ))), P t) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a < b) : ∃ t ∈ Ioo a b, P t := by
  have h' : ∀ᵐ t ∂(volume.restrict (Ioo a b)), P t :=
    ae_restrict_of_ae_restrict_of_subset (fun t ht => lt_of_le_of_lt ha ht.1) h
  have hm : ∀ᵐ t ∂(volume.restrict (Ioo a b)), t ∈ Ioo a b := ae_restrict_mem measurableSet_Ioo
  have : (ae (volume.restrict (Ioo a b))).NeBot := ae_restrict_neBot.2 (by simp [hab])
  obtain ⟨t, ht1, ht2⟩ := (hm.and h').exists
  exact ⟨t, ht1, ht2⟩

/-- Integral of `φ` against a combination `a cosh + b sinh + e`. -/
lemma int_w {φ : ℝ → ℝ} (h0i : IntegrableOn φ (Ioi 0))
    (h1i : IntegrableOn (fun t => φ t * sinh t) (Ioi 0))
    (h2i : IntegrableOn (fun t => φ t * cosh t) (Ioi 0))
    (h0 : ∫ t in Ioi 0, φ t = 0) (h1 : ∫ t in Ioi 0, φ t * sinh t = 0) (a b e : ℝ) :
    IntegrableOn (fun t => φ t * (a * cosh t + b * sinh t + e)) (Ioi 0) ∧
      ∫ t in Ioi 0, φ t * (a * cosh t + b * sinh t + e) = a * ∫ t in Ioi 0, φ t * cosh t := by
  have heq : (fun t => φ t * (a * cosh t + b * sinh t + e)) =
      fun t => (a * (φ t * cosh t) + b * (φ t * sinh t)) + e * φ t := by funext t; ring
  rw [heq]
  refine ⟨((h2i.const_mul a).add (h1i.const_mul b)).add (h0i.const_mul e), ?_⟩
  rw [integral_add (f := fun t => a * (φ t * cosh t) + b * (φ t * sinh t))
      (g := fun t => e * φ t) ((h2i.const_mul a).add (h1i.const_mul b)) (h0i.const_mul e),
    integral_add (f := fun t => a * (φ t * cosh t)) (g := fun t => b * (φ t * sinh t))
      (h2i.const_mul a) (h1i.const_mul b), integral_const_mul, integral_const_mul,
    integral_const_mul, h0, h1]
  ring

lemma test_fn {φ : ℝ → ℝ} (h0i : IntegrableOn φ (Ioi 0))
    (h1i : IntegrableOn (fun t => φ t * sinh t) (Ioi 0))
    (h2i : IntegrableOn (fun t => φ t * cosh t) (Ioi 0))
    (h0 : ∫ t in Ioi 0, φ t = 0) (h1 : ∫ t in Ioi 0, φ t * sinh t = 0) {a b e : ℝ} (ha : 0 < a)
    (hw : ∀ t ∈ Ioi (0:ℝ), 0 ≤ φ t * (a * cosh t + b * sinh t + e)) :
    0 ≤ ∫ t in Ioi 0, φ t * cosh t := by
  have hnn : 0 ≤ ∫ t in Ioi 0, φ t * (a * cosh t + b * sinh t + e) :=
    setIntegral_nonneg measurableSet_Ioi hw
  rw [(int_w h0i h1i h2i h0 h1 a b e).2] at hnn
  by_contra h
  push Not at h
  nlinarith [mul_neg_of_pos_of_neg ha h]

lemma test_fn_strict {φ : ℝ → ℝ} (h0i : IntegrableOn φ (Ioi 0))
    (h1i : IntegrableOn (fun t => φ t * sinh t) (Ioi 0))
    (h2i : IntegrableOn (fun t => φ t * cosh t) (Ioi 0))
    (h0 : ∫ t in Ioi 0, φ t = 0) (h1 : ∫ t in Ioi 0, φ t * sinh t = 0) {a b e : ℝ} (ha : 0 < a)
    (hw : ∀ t ∈ Ioi (0:ℝ), 0 ≤ φ t * (a * cosh t + b * sinh t + e))
    (hnull : volume {t : ℝ | a * cosh t + b * sinh t + e = 0} = 0)
    (hnz : ¬ ∀ᵐ t ∂(volume.restrict (Ioi (0:ℝ))), φ t = 0) :
    0 < ∫ t in Ioi 0, φ t * cosh t := by
  obtain ⟨hint, hval⟩ := int_w h0i h1i h2i h0 h1 a b e
  rcases (test_fn h0i h1i h2i h0 h1 ha hw).lt_or_eq with h | h
  · exact h
  exfalso; apply hnz
  have hz : ∫ t in Ioi 0, φ t * (a * cosh t + b * sinh t + e) = 0 := by rw [hval, ← h, mul_zero]
  have hae : 0 ≤ᵐ[volume.restrict (Ioi 0)] fun t => φ t * (a * cosh t + b * sinh t + e) := by
    rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_Ioi]
    exact Filter.Eventually.of_forall fun t ht => hw t ht
  have hz1 := (setIntegral_eq_zero_iff_of_nonneg_ae hae hint).mp hz
  have hz2 : ∀ᵐ t ∂(volume.restrict (Ioi (0:ℝ))), a * cosh t + b * sinh t + e ≠ 0 := by
    apply ae_restrict_of_ae
    rw [ae_iff]; simpa using hnull
  filter_upwards [hz1, hz2] with t ht1 ht2
  exact (mul_eq_zero.mp ht1).resolve_right ht2

/-- The sign structure of Lemma A gives a test function `w = a cosh + b sinh + e` (`a > 0`) with
`φ w ≥ 0` on `(0,∞)`, vanishing only on a null set. -/
lemma lemA_core {φ : ℝ → ℝ} (hN : {t | 0 < t ∧ φ t < 0}.OrdConnected) :
    ∃ a b e : ℝ, 0 < a ∧ (∀ t ∈ Ioi (0:ℝ), 0 ≤ φ t * (a * cosh t + b * sinh t + e)) ∧
      volume {t : ℝ | a * cosh t + b * sinh t + e = 0} = 0 := by
  set N := {t | 0 < t ∧ φ t < 0} with hNdef
  by_cases hne : N.Nonempty
  swap
  · refine ⟨1, 0, 0, one_pos, fun t ht => ?_, ?_⟩
    swap
    · have : {t : ℝ | 1 * cosh t + 0 * sinh t + 0 = 0} = ∅ := by
        ext t; simp [(cosh_pos t).ne']
      rw [this, measure_empty]
    have : 0 ≤ φ t := by
      by_contra h; exact hne ⟨t, ht, lt_of_not_ge h⟩
    simp only [one_mul, zero_mul, add_zero]
    exact mul_nonneg this (cosh_pos t).le
  have hbb : BddBelow N := ⟨0, fun t ht => ht.1.le⟩
  by_cases hbdd : BddAbove N
  · set x₁ := sInf N
    set x₂ := sSup N
    set m₀ := (x₁ + x₂) / 2 with hm₀
    set d := (x₂ - x₁) / 2 with hd
    have hx12 : x₁ ≤ x₂ := by
      obtain ⟨n, hn⟩ := hne
      exact (csInf_le hbb hn).trans (le_csSup hbdd hn)
    have hw : ∀ t, cosh m₀ * cosh t + -sinh m₀ * sinh t + -cosh d = cosh (t - m₀) - cosh d := by
      intro t; rw [cosh_sub]; ring
    refine ⟨cosh m₀, -sinh m₀, -cosh d, cosh_pos _, fun t ht => ?_, ?_⟩
    swap
    · apply measure_mono_null (t := {m₀ + d, m₀ - d}) _ ((toFinite _).measure_zero _)
      intro t ht
      simp only [mem_ofPred_eq, hw, sub_eq_zero] at ht
      have h1 : |t - m₀| = |d| := le_antisymm (cosh_le_cosh.mp ht.le) (cosh_le_cosh.mp ht.ge)
      simp only [mem_insert_iff, mem_singleton_iff]
      rcases abs_eq_abs.mp h1 with h | h
      · left; linarith
      · right; linarith
    rw [hw]
    by_cases hφ : φ t < 0
    · have htN : t ∈ N := ⟨ht, hφ⟩
      have h1' : x₁ ≤ t := csInf_le hbb htN
      have h2' : t ≤ x₂ := le_csSup hbdd htN
      have : cosh (t - m₀) ≤ cosh d := by
        have hh : |t - m₀| ≤ d := abs_le.mpr ⟨by rw [hm₀, hd]; linarith, by rw [hm₀, hd]; linarith⟩
        exact cosh_le_cosh.mpr (hh.trans (le_abs_self d))
      exact mul_nonneg_of_nonpos_of_nonpos hφ.le (by linarith)
    · have hφ' : 0 ≤ φ t := le_of_not_gt hφ
      apply mul_nonneg hφ'
      have : |d| ≤ |t - m₀| := by
        by_contra hlt
        push Not at hlt
        have hd0 : 0 ≤ d := by rw [hd]; linarith
        rw [abs_of_nonneg hd0, abs_lt] at hlt
        have ht1 : x₁ < t := by rw [hm₀, hd] at hlt; linarith [hlt.1]
        have ht2 : t < x₂ := by rw [hm₀, hd] at hlt; linarith [hlt.2]
        obtain ⟨n₁, hn₁, hn₁t⟩ := exists_lt_of_csInf_lt hne ht1
        obtain ⟨n₂, hn₂, hn₂t⟩ := exists_lt_of_lt_csSup hne ht2
        exact hφ (hN.out hn₁ hn₂ ⟨hn₁t.le, hn₂t.le⟩).2
      have := (cosh_le_cosh (x := d) (y := t - m₀)).mpr this
      linarith
  · set x₁ := sInf N
    have hw : ∀ t, 1 * cosh t + -1 * sinh t + -exp (-x₁) = exp (-t) - exp (-x₁) := by
      intro t; rw [show exp (-t) = cosh t - sinh t from (cosh_sub_sinh t).symm]; ring
    refine ⟨1, -1, -exp (-x₁), one_pos, fun t ht => ?_, ?_⟩
    swap
    · apply measure_mono_null (t := {x₁}) _ (measure_singleton _)
      intro t ht
      simp only [mem_ofPred_eq, hw, sub_eq_zero, exp_eq_exp, neg_inj] at ht
      exact ht
    rw [hw]
    by_cases hφ : φ t < 0
    · have htN : t ∈ N := ⟨ht, hφ⟩
      have h1' : x₁ ≤ t := csInf_le hbb htN
      have : exp (-t) ≤ exp (-x₁) := exp_le_exp.mpr (by linarith)
      exact mul_nonneg_of_nonpos_of_nonpos hφ.le (by linarith)
    · have hφ' : 0 ≤ φ t := le_of_not_gt hφ
      apply mul_nonneg hφ'
      have : t ≤ x₁ := by
        by_contra hlt
        push Not at hlt
        obtain ⟨n₁, hn₁, hn₁t⟩ := exists_lt_of_csInf_lt hne hlt
        obtain ⟨n₂, hn₂, hn₂t⟩ := not_bddAbove_iff.mp hbdd t
        exact hφ (hN.out hn₁ hn₂ ⟨hn₁t.le, hn₂t.le⟩).2
      have : exp (-x₁) ≤ exp (-t) := exp_le_exp.mpr (by linarith)
      linarith


/-- Lemma A (non-strict). -/
theorem lemA {φ : ℝ → ℝ} (h0i : IntegrableOn φ (Ioi 0))
    (h1i : IntegrableOn (fun t => φ t * sinh t) (Ioi 0))
    (h2i : IntegrableOn (fun t => φ t * cosh t) (Ioi 0))
    (h0 : ∫ t in Ioi 0, φ t = 0) (h1 : ∫ t in Ioi 0, φ t * sinh t = 0)
    (hN : {t | 0 < t ∧ φ t < 0}.OrdConnected) :
    0 ≤ ∫ t in Ioi 0, φ t * cosh t := by
  obtain ⟨a, b, e, ha, hw, -⟩ := lemA_core hN
  exact test_fn h0i h1i h2i h0 h1 ha hw

/-- Lemma A (strict): unless `φ = 0` a.e. on `(0,∞)`. -/
theorem lemA_strict {φ : ℝ → ℝ} (h0i : IntegrableOn φ (Ioi 0))
    (h1i : IntegrableOn (fun t => φ t * sinh t) (Ioi 0))
    (h2i : IntegrableOn (fun t => φ t * cosh t) (Ioi 0))
    (h0 : ∫ t in Ioi 0, φ t = 0) (h1 : ∫ t in Ioi 0, φ t * sinh t = 0)
    (hN : {t | 0 < t ∧ φ t < 0}.OrdConnected)
    (hnz : ¬ ∀ᵐ t ∂(volume.restrict (Ioi (0:ℝ))), φ t = 0) :
    0 < ∫ t in Ioi 0, φ t * cosh t := by
  obtain ⟨a, b, e, ha, hw, hnull⟩ := lemA_core hN
  exact test_fn_strict h0i h1i h2i h0 h1 ha hw hnull hnz

/-- Step 2 of Lemma C: the pure exponential `c e^{-α t}` matching the left half of `f` in mass and
`sinh`-moment dominates `f` on the right: `f s ≤ c e^{α s}` for `s ≥ 0`. -/
theorem tangent {f : ℝ → ℝ} (hf : LC f) {c α : ℝ} (hc : 0 < c)
    (hi0 : IntegrableOn (fun t => c * exp (-α * t) - f (-t)) (Ioi 0))
    (hi1 : IntegrableOn (fun t => (c * exp (-α * t) - f (-t)) * sinh t) (Ioi 0))
    (h0 : ∫ t in Ioi 0, (c * exp (-α * t) - f (-t)) = 0)
    (h1 : ∫ t in Ioi 0, (c * exp (-α * t) - f (-t)) * sinh t = 0) :
    ∀ s, 0 ≤ s → f s ≤ c * exp (α * s) := by
  set φ := fun t => c * exp (-α * t) - f (-t) with hφdef
  by_contra hcon
  push Not at hcon
  obtain ⟨s₀, hs₀, hfs₀⟩ := hcon
  have hU := hf.superlevel hc.le α
  set T := {t : ℝ | 0 < t ∧ φ t < 0} with hTdef
  have hmemT : ∀ t, t ∈ T ↔ 0 < t ∧ c * exp (α * -t) < f (-t) := by
    intro t; simp only [hTdef, hφdef, mem_ofPred_eq, sub_neg, neg_mul, mul_neg]
  have hP : ∀ t ∈ T, ∀ t', 0 < t' → t' ≤ t → t' ∈ T := by
    intro t ht t' ht' htt'
    rw [hmemT] at ht ⊢
    refine ⟨ht', ?_⟩
    exact hU.out ht.2 hfs₀ (show -t' ∈ Icc (-t) s₀ from ⟨by linarith, by linarith⟩)
  by_cases hbdd : BddAbove T
  · set τ := sSup T
    have hτ0 : 0 ≤ τ := Real.sSup_nonneg fun x hx => hx.1.le
    have hgt : ∀ t, τ < t → t ∉ T := fun t ht hT => by
      have := le_csSup hbdd hT; linarith
    have hlt : ∀ t, 0 < t → t < τ → t ∈ T := by
      intro t ht htτ
      have hne : T.Nonempty := by
        by_contra hne
        rw [not_nonempty_iff_eq_empty] at hne
        have : τ = 0 := by simp only [τ, hne, Real.sSup_empty]
        linarith
      obtain ⟨y, hy, hty⟩ := exists_lt_of_lt_csSup hne htτ
      exact hP y hy t ht hty.le
    -- ρ = φ (sinh t - sinh τ)
    have hρi : IntegrableOn (fun t => φ t * sinh t - sinh τ * φ t) (Ioi 0) :=
      hi1.sub (hi0.const_mul _)
    have hρ0 : ∫ t in Ioi 0, (φ t * sinh t - sinh τ * φ t) = 0 := by
      rw [integral_sub hi1 (hi0.const_mul _), integral_const_mul]
      simp only [hφdef] at h0 h1 ⊢
      rw [h0, h1]; ring
    have hρnn : ∀ t ∈ Ioi (0:ℝ), 0 ≤ φ t * sinh t - sinh τ * φ t := by
      intro t ht
      rw [show φ t * sinh t - sinh τ * φ t = φ t * (sinh t - sinh τ) by ring]
      rcases lt_trichotomy t τ with h | h | h
      · have h1 := (hlt t ht h).2
        have h2 : sinh t < sinh τ := sinh_lt_sinh.mpr h
        nlinarith
      · rw [h]; simp
      · have h1 : 0 ≤ φ t := le_of_not_gt fun hh => hgt t h ⟨ht, hh⟩
        have h2 : sinh τ < sinh t := sinh_lt_sinh.mpr h
        nlinarith
    rcases hτ0.eq_or_lt with hτ | hτ
    · -- τ = 0: φ ≥ 0, hence φ = 0 a.e., contradiction with concavity
      have hnn : ∀ t ∈ Ioi (0:ℝ), 0 ≤ φ t := fun t ht =>
        le_of_not_gt fun hh => hgt t (by rw [← hτ]; exact ht) ⟨ht, hh⟩
      have hae0 : 0 ≤ᵐ[volume.restrict (Ioi 0)] φ := by
        rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_Ioi]
        exact Filter.Eventually.of_forall fun t ht => hnn t ht
      have hz := (setIntegral_eq_zero_iff_of_nonneg_ae hae0 hi0).mp h0
      have hz' : ∀ᵐ t ∂(volume.restrict (Ioi (0:ℝ))), φ t = 0 := hz
      obtain ⟨t₁, ht₁, hφ₁⟩ := exists_ae hz' (le_refl 0) one_pos
      obtain ⟨t₂, ht₂, hφ₂⟩ := exists_ae hz' zero_le_one one_lt_two
      obtain ⟨J, ψ, hJ, hψ, hfeq⟩ := hf
      have key : ∀ t, 0 < t → φ t = 0 → -t ∈ J ∧ ψ (-t) = log c - α * t := by
        intro t ht hφt
        simp only [hφdef, sub_eq_zero] at hφt
        have hpos : 0 < f (-t) := by rw [← hφt]; positivity
        have hJt : -t ∈ J := by
          by_contra hh; rw [hfeq, indicator_of_notMem hh] at hpos; exact lt_irrefl _ hpos
        refine ⟨hJt, ?_⟩
        rw [hfeq, indicator_of_mem hJt] at hφt
        have := congrArg log hφt
        rw [log_exp, log_mul hc.ne' (exp_pos _).ne', log_exp] at this
        linarith
      obtain ⟨hJ1, hψ1⟩ := key t₁ ht₁.1 hφ₁
      obtain ⟨hJ2, hψ2⟩ := key t₂ (by linarith [ht₂.1]) hφ₂
      have hpos0 : 0 < f s₀ := lt_of_le_of_lt (by positivity) hfs₀
      have hJ0 : s₀ ∈ J := by
        by_contra hh; rw [hfeq, indicator_of_notMem hh] at hpos0; exact lt_irrefl _ hpos0
      have hψ0 : log c + α * s₀ < ψ s₀ := by
        rw [hfeq, indicator_of_mem hJ0] at hfs₀
        have := (log_lt_log (by positivity) hfs₀)
        rwa [log_exp, log_mul hc.ne' (exp_pos _).ne', log_exp] at this
      have ht12 : t₁ < t₂ := lt_trans ht₁.2 ht₂.1
      set a := (s₀ + t₁) / (s₀ + t₂)
      set b := (t₂ - t₁) / (s₀ + t₂)
      have hst : 0 < s₀ + t₂ := by linarith [ht₂.1]
      have ha : 0 ≤ a := div_nonneg (by linarith [ht₁.1]) hst.le
      have hb : 0 < b := div_pos (by linarith) hst
      have hab : a + b = 1 := by simp only [a, b]; field_simp; ring
      have hcomb : a • (-t₂) + b • s₀ = -t₁ := by simp only [smul_eq_mul, a, b]; field_simp; ring
      have hc' := hψ.2 hJ2 hJ0 ha hb.le hab
      rw [hcomb] at hc'
      simp only [smul_eq_mul] at hc' hcomb
      rw [hψ1, hψ2] at hc'
      have : a * (log c - α * t₂) + b * ψ s₀ > log c - α * t₁ := by
        have e1 : log c - α * t₁ = a * (log c - α * t₂) + b * (log c + α * s₀) := by
          have : -t₁ = a * -t₂ + b * s₀ := hcomb.symm
          rw [show log c - α * t₁ = log c * (a + b) + α * (-t₁) by rw [hab]; ring, this]; ring
        rw [e1]; nlinarith
      linarith
    · have := posint hτ hρi hρnn (fun t ht => by
        have h1 := (hlt t ht.1 ht.2).2
        have h2 : sinh t < sinh τ := sinh_lt_sinh.mpr ht.2
        rw [show φ t * sinh t - sinh τ * φ t = φ t * (sinh t - sinh τ) by ring]
        nlinarith)
      linarith
  · -- T unbounded: φ < 0 on (0,∞)
    have hall : ∀ t ∈ Ioi (0:ℝ), φ t < 0 := by
      intro t ht
      obtain ⟨y, hy, hty⟩ := not_bddAbove_iff.mp hbdd t
      exact (hP y hy t ht hty.le).2
    have := posint one_pos hi0.neg (fun t ht => by simp only [Pi.neg_apply]; linarith [hall t ht])
      (fun t ht => by simp only [Pi.neg_apply]; linarith [hall t ht.1])
    simp only [Pi.neg_apply, integral_neg] at this
    simp only [hφdef] at this
    linarith

-- ===== Half-line moments and the matching step =====

/-!
# Half-line moments and the matching step (Step 3 of Lemma C)

The right half of the extremal density is `lap c α u m` on `(0,∞)`, with `m = mfun u` chosen so that its
mass is `P`. The intermediate value theorem (in the variable `u = 1/a ∈ [0,1)`, applied to
`Ntil u = (1-u) (M(u) - D)`, which stays continuous at `u = 1`) gives `u` with `sinh`-moment `D`.
-/

open Real MeasureTheory Set

/-- `∫_{(0,∞)} lap c α u m s · e^{l s} ds` in closed form. -/
noncomputable def Mom (c α u m l : ℝ) : ℝ :=
  c * exp ((α + l) * m) * (1 / (α + l) + u / (1 - l * u)) - c / (α + l)

lemma sinh_split (k : ℝ → ℝ) : (fun s => k s * sinh s) =
    fun s => (k s * exp (1 * s) - k s * exp (-1 * s)) / 2 := by
  funext s; rw [sinh_eq]; simp only [one_mul, neg_one_mul]; ring

lemma cosh_split (k : ℝ → ℝ) : (fun s => k s * cosh s) =
    fun s => (k s * exp (1 * s) + k s * exp (-1 * s)) / 2 := by
  funext s; rw [cosh_eq]; simp only [one_mul, neg_one_mul]; ring

/-- From the two exponential moments to the `sinh` and `cosh` moments. -/
lemma hyp_moms {k : ℝ → ℝ} {S : Set ℝ} {P N : ℝ}
    (hP : IntegrableOn (fun s => k s * exp (1 * s)) S) (hN : IntegrableOn (fun s => k s * exp (-1 * s)) S)
    (hPv : ∫ s in S, k s * exp (1 * s) = P) (hNv : ∫ s in S, k s * exp (-1 * s) = N) :
    IntegrableOn (fun s => k s * sinh s) S ∧ IntegrableOn (fun s => k s * cosh s) S ∧
      ∫ s in S, k s * sinh s = (P - N) / 2 ∧ ∫ s in S, k s * cosh s = (P + N) / 2 := by
  rw [sinh_split, cosh_split]
  refine ⟨(hP.sub hN).div_const 2, (hP.add hN).div_const 2, ?_, ?_⟩
  · rw [integral_div, integral_sub hP hN, hPv, hNv]
  · rw [integral_div, integral_add hP hN, hPv, hNv]

lemma lap_half {c α u m : ℝ} (hm : 0 ≤ m) (hα : 1 < α) (hu0 : 0 ≤ u) (hu1 : u < 1) :
    IntegrableOn (fun s => lap c α u m s) (Ioi 0) ∧
    IntegrableOn (fun s => lap c α u m s * sinh s) (Ioi 0) ∧
    IntegrableOn (fun s => lap c α u m s * cosh s) (Ioi 0) ∧
    ∫ s in Ioi 0, lap c α u m s = Mom c α u m 0 ∧
    ∫ s in Ioi 0, lap c α u m s * sinh s = (Mom c α u m 1 - Mom c α u m (-1)) / 2 ∧
    ∫ s in Ioi 0, lap c α u m s * cosh s = (Mom c α u m 1 + Mom c α u m (-1)) / 2 := by
  obtain ⟨i0, v0⟩ := lap_mom_Ioi (c := c) (α := α) (u := u) (l := 0) hm (by linarith) hu0 (by simp)
  obtain ⟨i1, v1⟩ := lap_mom_Ioi (c := c) (α := α) (u := u) (l := 1) hm (by linarith) hu0 (by linarith)
  obtain ⟨i2, v2⟩ := lap_mom_Ioi (c := c) (α := α) (u := u) (l := -1) hm (by linarith) hu0 (by linarith)
  have e0 : (fun s => lap c α u m s * exp (0 * s)) = fun s => lap c α u m s := by funext s; simp
  rw [e0] at i0 v0
  obtain ⟨a, b, c', d⟩ := hyp_moms i1 i2 v1 v2
  exact ⟨i0, a, b, v0, c', d⟩

/-- Moments of the pure exponential `c e^{-α t}` on `(0,∞)`. -/
lemma gam_half {c α : ℝ} (hα : 1 < α) :
    IntegrableOn (fun t => c * exp (-α * t)) (Ioi 0) ∧
    IntegrableOn (fun t => c * exp (-α * t) * sinh t) (Ioi 0) ∧
    IntegrableOn (fun t => c * exp (-α * t) * cosh t) (Ioi 0) ∧
    ∫ t in Ioi 0, c * exp (-α * t) = c / α ∧
    ∫ t in Ioi 0, c * exp (-α * t) * sinh t = c / (α ^ 2 - 1) ∧
    ∫ t in Ioi 0, c * exp (-α * t) * cosh t = c * α / (α ^ 2 - 1) := by
  have base : ∀ l : ℝ, l < α → IntegrableOn (fun t => c * exp (-α * t) * exp (l * t)) (Ioi 0) ∧
      ∫ t in Ioi 0, c * exp (-α * t) * exp (l * t) = c / (α - l) := by
    intro l hl
    have he : (fun t => c * exp (-α * t) * exp (l * t)) = fun t => c * exp ((l - α) * t) := by
      funext t; rw [mul_assoc, ← exp_add]; ring_nf
    rw [he]
    refine ⟨(integrableOn_exp_mul_Ioi (by linarith) 0).const_mul c, ?_⟩
    rw [integral_const_mul, integral_exp_mul_Ioi (by linarith)]
    simp only [mul_zero, exp_zero]
    have : α - l ≠ 0 := by linarith
    have : l - α ≠ 0 := by linarith
    field_simp; ring
  obtain ⟨i0, v0⟩ := base 0 (by linarith)
  obtain ⟨i1, v1⟩ := base 1 hα
  obtain ⟨i2, v2⟩ := base (-1) (by linarith)
  have e0 : (fun t => c * exp (-α * t) * exp (0 * t)) = fun t => c * exp (-α * t) := by
    funext t; simp
  rw [e0] at i0 v0
  obtain ⟨a, b, c', d⟩ := hyp_moms i1 i2 v1 v2
  refine ⟨i0, a, b, by rw [v0]; simp, ?_, ?_⟩
  · rw [c']
    have : α - 1 ≠ 0 := by linarith
    have : α - -1 ≠ 0 := by linarith
    have : α ^ 2 - 1 ≠ 0 := by nlinarith
    field_simp; ring
  · rw [d]
    have : α - 1 ≠ 0 := by linarith
    have : α - -1 ≠ 0 := by linarith
    have : α ^ 2 - 1 ≠ 0 := by nlinarith
    field_simp; ring

/-! ## The matching step -/

/-- Location `m(u)` making the mass of the right half equal to `P`. -/
noncomputable def mfun (c α P u : ℝ) : ℝ := log ((α * P + c) / (c * (1 + α * u))) / α

lemma exp_mfun {c α P u : ℝ} (hc : 0 < c) (hα : 1 < α) (hP : 0 < P) (hu : 0 ≤ u) :
    exp (α * mfun c α P u) = (α * P + c) / (c * (1 + α * u)) := by
  have hα0 : α ≠ 0 := by linarith
  unfold mfun
  rw [show α * (log ((α * P + c) / (c * (1 + α * u))) / α) = log ((α * P + c) / (c * (1 + α * u))) by
    field_simp]
  have : 0 < 1 + α * u := by nlinarith
  exact exp_log (by positivity)

lemma Mom_zero {c α u m : ℝ} : Mom c α u m 0 = c * exp (α * m) * (1 / α + u) - c / α := by
  simp [Mom]

lemma Mom_one {c α u m : ℝ} :
    Mom c α u m 1 = c * exp ((α + 1) * m) * (1 / (α + 1) + u / (1 - u)) - c / (α + 1) := by
  simp [Mom]

lemma Mom_neg_one {c α u m : ℝ} :
    Mom c α u m (-1) = c * exp ((α - 1) * m) * (1 / (α - 1) + u / (1 + u)) - c / (α - 1) := by
  simp only [Mom, ← sub_eq_add_neg]; ring_nf

lemma mom0_mfun {c α P u : ℝ} (hc : 0 < c) (hα : 1 < α) (hP : 0 < P) (hu : 0 ≤ u) :
    Mom c α u (mfun c α P u) 0 = P := by
  rw [Mom_zero, exp_mfun hc hα hP hu]
  have : 0 < 1 + α * u := by nlinarith
  have hα0 : α ≠ 0 := by linarith
  field_simp; ring

lemma mfun_nonneg {c α P u : ℝ} (hc : 0 < c) (hα : 1 < α) (_hP : 0 < P) (hu : 0 ≤ u)
    (hu' : u ≤ P / c) : 0 ≤ mfun c α P u := by
  unfold mfun
  apply div_nonneg _ (by linarith)
  apply log_nonneg
  have : 0 < 1 + α * u := by nlinarith
  rw [le_div_iff₀ (by positivity), one_mul]
  have : c * u ≤ P := by rw [le_div_iff₀ hc] at hu'; linarith
  nlinarith

/-- The continuous function whose zero gives the matching `u`. -/
noncomputable def Ntil (c α P D u : ℝ) : ℝ :=
  (1 / 2) * (c * exp ((α + 1) * mfun c α P u) * ((1 - u) / (α + 1) + u) - (1 - u) * (c / (α + 1))
    - (1 - u) * (c * exp ((α - 1) * mfun c α P u) * (1 / (α - 1) + u / (1 + u)) - c / (α - 1)))
    - (1 - u) * D

lemma Ntil_eq {c α P D u : ℝ} (hα : 1 < α) (hu0 : 0 ≤ u) (hu1 : u < 1) :
    Ntil c α P D u = (1 - u) * ((Mom c α u (mfun c α P u) 1 - Mom c α u (mfun c α P u) (-1)) / 2 - D) := by
  rw [Mom_one, Mom_neg_one]
  unfold Ntil
  have : 1 - u ≠ 0 := by linarith
  have : α + 1 ≠ 0 := by linarith
  field_simp

theorem exists_match {c α P D : ℝ} (hc : 0 < c) (hα : 1 < α) (hP : 0 < P) (_hD : 0 < D)
    (hW : P / c < 1 → D ≤ P * (P / c) / (1 - (P / c) ^ 2))
    (hbath : (Mom c α 0 (mfun c α P 0) 1 - Mom c α 0 (mfun c α P 0) (-1)) / 2 ≤ D) :
    ∃ u, 0 ≤ u ∧ u < 1 ∧ 0 ≤ mfun c α P u ∧
      (Mom c α u (mfun c α P u) 1 - Mom c α u (mfun c α P u) (-1)) / 2 = D := by
  set u₁ := min (P / c) 1 with hu₁
  have hu₁0 : 0 ≤ u₁ := le_min (by positivity) zero_le_one
  have hu₁1 : u₁ ≤ 1 := min_le_right _ _
  have hu₁c : u₁ ≤ P / c := min_le_left _ _
  have hcont : ContinuousOn (Ntil c α P D) (Icc 0 u₁) := by
    apply continuousOn_of_forall_continuousAt
    intro x hx
    have hx0 : 0 ≤ x := hx.1
    have hA : 0 < 1 + α * x := by nlinarith
    have hB : c * (1 + α * x) ≠ 0 := by positivity
    have hC : (α * P + c) / (c * (1 + α * x)) ≠ 0 := by positivity
    have hE : 1 + x ≠ 0 := by linarith
    unfold Ntil mfun
    fun_prop (disch := first | exact hB | exact hC | exact hE | positivity | linarith)
  have N0 : Ntil c α P D 0 ≤ 0 := by
    rw [Ntil_eq hα le_rfl zero_lt_one]; linarith
  have N1 : 0 ≤ Ntil c α P D u₁ := by
    by_cases h : P / c < 1
    · have hu : u₁ = P / c := min_eq_left h.le
      have hmz : mfun c α P (P / c) = 0 := by
        unfold mfun
        rw [show c * (1 + α * (P / c)) = α * P + c by field_simp; ring, div_self (by positivity), log_one,
          zero_div]
      rw [hu, Ntil_eq hα (by positivity) h, Mom_one, Mom_neg_one, hmz]
      simp only [mul_zero, exp_zero, mul_one]
      apply mul_nonneg (by linarith)
      have h0 : 0 < P / c := by positivity
      have key := hW h
      have gen : ∀ v : ℝ, 1 - v ≠ 0 → 1 + v ≠ 0 →
          (c * (1 / (α + 1) + v / (1 - v)) - c / (α + 1) -
            (c * (1 / (α - 1) + v / (1 + v)) - c / (α - 1))) / 2 = c * v * v / (1 - v ^ 2) := by
        intro v h1 h2
        have : 1 - v ^ 2 ≠ 0 := by
          rw [show 1 - v ^ 2 = (1 - v) * (1 + v) by ring]; exact mul_ne_zero h1 h2
        have : α + 1 ≠ 0 := by linarith
        have : α - 1 ≠ 0 := by linarith
        field_simp; ring
      have e := gen (P / c) (by linarith) (by linarith)
      have e2 : c * (P / c) * (P / c) = P * (P / c) := by field_simp
      rw [e2] at e
      linarith
    · have hu : u₁ = 1 := min_eq_right (le_of_not_gt h)
      rw [hu]; unfold Ntil
      simp only [sub_self, zero_mul, sub_zero, zero_div, zero_add, mul_one]
      positivity
  obtain ⟨u, hu, hNu⟩ := intermediate_value_Icc hu₁0 hcont ⟨N0, N1⟩
  have hu1 : u < 1 := by
    rcases (hu.2.trans hu₁1).lt_or_eq with h | h
    · exact h
    · exfalso
      have : Ntil c α P D 1 = (1 / 2) * (c * exp ((α + 1) * mfun c α P 1)) := by
        unfold Ntil; simp only [sub_self, zero_mul, sub_zero, zero_div, zero_add, mul_one]
      rw [h, this] at hNu
      have : 0 < (1 / 2) * (c * exp ((α + 1) * mfun c α P 1)) := by positivity
      linarith
  refine ⟨u, hu.1, hu1, mfun_nonneg hc hα hP hu.1 (hu.2.trans hu₁c), ?_⟩
  rw [Ntil_eq hα hu.1 hu1] at hNu
  have : 1 - u ≠ 0 := by linarith
  have := (mul_eq_zero.mp hNu).resolve_left this
  linarith

-- ===== Comparison lemma (Lemma C) and Theorem 3 =====

/-!
# Comparison lemma (Lemma C) and Theorem 3 (homogeneous form)

`thm3`: if `f = J.indicator (exp ∘ ψ)` with `J` an interval and `ψ` concave on `J`, `f cosh` integrable and
`∫ f sinh = 0`, then `(∫ f cosh) (∫ f cosh - ∫ f) ≤ (∫ f |sinh|)²`.
-/

open Real MeasureTheory Set

/-- Lemma B: the pure exponential `c e^{-α t}` with mass `P` and `sinh`-moment `D`. -/
noncomputable def alp (P D : ℝ) : ℝ := (P / D + sqrt ((P / D) ^ 2 + 4)) / 2

lemma alp_props {P D : ℝ} (hP : 0 < P) (hD : 0 < D) :
    1 < alp P D ∧ alp P D * P / alp P D = P ∧ alp P D * P / (alp P D ^ 2 - 1) = D := by
  set r := P / D with hr
  have hr0 : 0 < r := by positivity
  have hs : sqrt (r ^ 2 + 4) ^ 2 = r ^ 2 + 4 := sq_sqrt (by positivity)
  have hs2 : 2 < sqrt (r ^ 2 + 4) := by
    rw [show (2:ℝ) = sqrt 4 by rw [show (4:ℝ) = 2 ^ 2 by norm_num, sqrt_sq (by norm_num)]]
    exact sqrt_lt_sqrt (by norm_num) (by nlinarith)
  have h1 : 1 < alp P D := by unfold alp; rw [← hr]; linarith
  have hq : alp P D ^ 2 - 1 = r * alp P D := by unfold alp; rw [← hr]; nlinarith [hs]
  refine ⟨h1, by field_simp, ?_⟩
  rw [hq, hr]
  have : alp P D ≠ 0 := by linarith
  field_simp

lemma kmono {v w : ℝ} (hv : 0 < v) (hvw : v ≤ w) (hw : w < 1) :
    v / (1 - v ^ 2) ≤ w / (1 - w ^ 2) := by
  have h1 : 0 < 1 - v ^ 2 := by nlinarith
  have h2 : 0 < 1 - w ^ 2 := by nlinarith
  rw [div_le_div_iff₀ h1 h2]
  nlinarith [mul_nonneg (sub_nonneg.mpr hvw) (mul_pos hv (by linarith : (0:ℝ) < w)).le]

lemma abs_sinh_le_cosh (x : ℝ) : |sinh x| ≤ cosh x := by
  rw [abs_le]; constructor
  · have := sinh_lt_cosh (-x); rw [sinh_neg, cosh_neg] at this; linarith
  · exact (sinh_lt_cosh x).le

/-- Integrability consequences of `∫ |k| cosh < ∞`. -/
lemma int_of_cosh {k : ℝ → ℝ} (hk : Integrable (fun s => k s * cosh s)) :
    Integrable k ∧ Integrable (fun s => k s * sinh s) := by
  have hm : AEStronglyMeasurable k volume := by
    have := hk.aestronglyMeasurable.mul
      (continuous_cosh.inv₀ (fun x => (cosh_pos x).ne')).aestronglyMeasurable
    refine this.congr (Filter.Eventually.of_forall fun s => ?_)
    simp only [Pi.mul_apply, Pi.inv_apply]; field_simp [(cosh_pos s).ne']
  refine ⟨hk.mono hm (Filter.Eventually.of_forall fun s => ?_),
    hk.mono (hm.mul continuous_sinh.aestronglyMeasurable) (Filter.Eventually.of_forall fun s => ?_)⟩
  · rw [norm_mul, Real.norm_of_nonneg (cosh_pos s).le]
    exact le_mul_of_one_le_right (norm_nonneg _) (one_le_cosh s)
  · rw [norm_mul, norm_mul, Real.norm_of_nonneg (cosh_pos s).le, Real.norm_eq_abs (sinh s)]
    exact mul_le_mul_of_nonneg_left (abs_sinh_le_cosh s) (norm_nonneg _)

/-- A nonnegative function with zero `sinh`-moment on `(0,∞)` vanishes a.e. there. -/
lemma zero_of_sinh_zero {k : ℝ → ℝ} (hk0 : ∀ t ∈ Ioi (0:ℝ), 0 ≤ k t)
    (hks : IntegrableOn (fun t => k t * sinh t) (Ioi 0)) (h : ∫ t in Ioi 0, k t * sinh t = 0) :
    ∫ t in Ioi 0, k t = 0 ∧ ∫ t in Ioi 0, k t * cosh t = 0 := by
  have hae : 0 ≤ᵐ[volume.restrict (Ioi 0)] (fun t => k t * sinh t) := by
    rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_Ioi]
    exact Filter.Eventually.of_forall fun t ht => mul_nonneg (hk0 t ht) (sinh_pos_iff.mpr ht).le
  have hz := (setIntegral_eq_zero_iff_of_nonneg_ae hae hks).mp h
  have hz' : ∀ᵐ t ∂(volume.restrict (Ioi (0:ℝ))), k t = 0 := by
    have hm : ∀ᵐ t ∂(volume.restrict (Ioi (0:ℝ))), t ∈ Ioi (0:ℝ) := ae_restrict_mem measurableSet_Ioi
    filter_upwards [hz, hm] with t ht htm
    simp only [Pi.zero_apply] at ht
    exact (mul_eq_zero.mp ht).resolve_right (sinh_pos_iff.mpr htm).ne'
  constructor
  · rw [integral_congr_ae hz']; simp
  · have : (fun t => k t * cosh t) =ᵐ[volume.restrict (Ioi 0)] 0 := by
      filter_upwards [hz'] with t ht; simp [ht]
    rw [integral_congr_ae this]; simp

lemma pos_of_sinh_pos {k : ℝ → ℝ} (hk0 : ∀ t ∈ Ioi (0:ℝ), 0 ≤ k t) (hki : IntegrableOn k (Ioi 0))
    (_hks : IntegrableOn (fun t => k t * sinh t) (Ioi 0)) (h : 0 < ∫ t in Ioi 0, k t * sinh t) :
    0 < ∫ t in Ioi 0, k t := by
  have hnn : 0 ≤ ∫ t in Ioi 0, k t := setIntegral_nonneg measurableSet_Ioi hk0
  rcases hnn.eq_or_lt with h0 | h0
  · exfalso
    have hae : 0 ≤ᵐ[volume.restrict (Ioi 0)] k := by
      rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_Ioi]
      exact Filter.Eventually.of_forall fun t ht => hk0 t ht
    have hz := (setIntegral_eq_zero_iff_of_nonneg_ae hae hki).mp h0.symm
    have : (fun t => k t * sinh t) =ᵐ[volume.restrict (Ioi 0)] 0 := by
      filter_upwards [hz] with t ht; simp only [Pi.zero_apply] at ht ⊢; simp [ht]
    rw [integral_congr_ae this] at h; simp at h
  · exact h0

/-- The right tail of `lap` is a nonnegative multiple of an exponential. -/
lemma tl_form {c α u m : ℝ} (hc : 0 ≤ c) (hu : 0 ≤ u) :
    ∃ K β : ℝ, 0 ≤ K ∧ ∀ t, c * exp (α * m) * tl u m t = K * exp (β * t) := by
  rcases hu.eq_or_lt with h | h
  · subst h; exact ⟨0, 0, le_rfl, fun t => by simp [tl]⟩
  · refine ⟨c * exp (α * m) * exp (m / u), -1 / u, by positivity, fun t => ?_⟩
    simp only [tl, ite_eq_right h.ne']
    rw [mul_assoc (c * exp (α * m)), ← exp_add]; congr 2; field_simp; ring

/-- Strictly log-concave: the indicator of an interval times `exp` of a strictly concave function. -/
def LCs (f : ℝ → ℝ) : Prop :=
  ∃ J : Set ℝ, ∃ ψ : ℝ → ℝ, J.OrdConnected ∧ StrictConcaveOn ℝ J ψ ∧ f = J.indicator (fun s => exp (ψ s))

lemma LCs.lc {f : ℝ → ℝ} (hf : LCs f) : LC f := by
  obtain ⟨J, ψ, hJ, hψ, he⟩ := hf; exact ⟨J, ψ, hJ, hψ.concaveOn, he⟩

lemma LCs.neg {f : ℝ → ℝ} (hf : LCs f) : LCs (fun s => f (-s)) := by
  obtain ⟨J, ψ, hJ, hψ, rfl⟩ := hf
  have hJ' : ((fun s : ℝ => -s) ⁻¹' J).OrdConnected :=
    ⟨fun x hx y hy z hz => hJ.out hy hx ⟨neg_le_neg hz.2, neg_le_neg hz.1⟩⟩
  refine ⟨(fun s => -s) ⁻¹' J, fun s => ψ (-s), hJ', ⟨hJ'.convex, fun x hx y hy hxy a b ha hb hab => ?_⟩, ?_⟩
  · have := hψ.2 hx hy (fun h => hxy (neg_inj.mp h)) ha hb hab
    simp only [smul_eq_mul] at this ⊢
    rw [show -(a * x + b * y) = a * -x + b * -y by ring]; exact this
  · funext s; simp only [indicator, mem_preimage]; rfl

/-- A strictly log-concave `f` is not a.e. equal to an exponential on a half-line. -/
lemma noaffine {f : ℝ → ℝ} (hf : LCs f) (c α : ℝ) (hc : 0 < c) :
    ¬ ∀ᵐ t ∂(volume.restrict (Ioi (0:ℝ))), c * exp (-α * t) - f (-t) = 0 := by
  intro h
  obtain ⟨J, ψ, hJ, hψ, hfeq⟩ := hf
  have key : ∀ t, 0 < t → c * exp (-α * t) - f (-t) = 0 → -t ∈ J ∧ ψ (-t) = log c - α * t := by
    intro t ht hφt
    rw [sub_eq_zero] at hφt
    have hpos : 0 < f (-t) := by rw [← hφt]; positivity
    have hJt : -t ∈ J := by
      by_contra hh; rw [hfeq, indicator_of_notMem hh] at hpos; exact lt_irrefl _ hpos
    refine ⟨hJt, ?_⟩
    rw [hfeq, indicator_of_mem hJt] at hφt
    have := congrArg log hφt
    rw [log_exp, log_mul hc.ne' (exp_pos _).ne', log_exp] at this
    linarith
  obtain ⟨t₁, ht₁, h₁⟩ := exists_ae h (le_refl 0) one_pos
  obtain ⟨t₂, ht₂, h₂⟩ := exists_ae h zero_le_one one_lt_two
  obtain ⟨t₃, ht₃, h₃⟩ := exists_ae h zero_le_two (by norm_num : (2:ℝ) < 3)
  obtain ⟨hJ1, hψ1⟩ := key t₁ ht₁.1 h₁
  obtain ⟨hJ2, hψ2⟩ := key t₂ (by linarith [ht₂.1]) h₂
  obtain ⟨hJ3, hψ3⟩ := key t₃ (by linarith [ht₃.1]) h₃
  have h12 : t₁ < t₂ := lt_trans ht₁.2 ht₂.1
  have h23 : t₂ < t₃ := lt_trans ht₂.2 ht₃.1
  set a := (t₂ - t₁) / (t₃ - t₁)
  set b := (t₃ - t₂) / (t₃ - t₁)
  have h31 : 0 < t₃ - t₁ := by linarith
  have ha : 0 < a := div_pos (by linarith) h31
  have hb : 0 < b := div_pos (by linarith) h31
  have hab : a + b = 1 := by simp only [a, b]; field_simp; ring
  have hcomb : a * -t₃ + b * -t₁ = -t₂ := by simp only [a, b]; field_simp; ring
  have hlt := hψ.2 hJ3 hJ1 (by intro hh; linarith) ha hb hab
  simp only [smul_eq_mul] at hlt
  rw [hcomb, hψ1, hψ2, hψ3] at hlt
  have e : a * (log c - α * t₃) + b * (log c - α * t₁) = log c - α * t₂ := by
    linear_combination (log c) * hab + α * hcomb
  linarith

set_option maxHeartbeats 4000000 in
/-- Lemma C in the oriented case (the left half carries the pure exponential), combined with
Proposition D: the half-line form of Theorem 3. -/
theorem orient {f : ℝ → ℝ} (hf : LC f) (hfc : Integrable (fun s => f s * cosh s)) {D : ℝ} (hD : 0 < D)
    (hDm : ∫ t in Ioi 0, f (-t) * sinh t = D) (hDp : ∫ t in Ioi 0, f t * sinh t = D)
    (hor : alp (∫ t in Ioi 0, f (-t)) D * (∫ t in Ioi 0, f (-t)) ≤
      alp (∫ t in Ioi 0, f t) D * (∫ t in Ioi 0, f t))
    (strict : Prop)
    (hnz : strict → ∀ c α : ℝ, 0 < c → ¬ ∀ᵐ t ∂(volume.restrict (Ioi (0:ℝ))), c * exp (-α * t) - f (-t) = 0) :
    ((∫ t in Ioi 0, f (-t) * cosh t) + ∫ t in Ioi 0, f t * cosh t) *
        ((∫ t in Ioi 0, f (-t) * cosh t) + (∫ t in Ioi 0, f t * cosh t)
          - (∫ t in Ioi 0, f (-t)) - ∫ t in Ioi 0, f t) ≤ (2 * D) ^ 2 ∧
    (strict → ((∫ t in Ioi 0, f (-t) * cosh t) + ∫ t in Ioi 0, f t * cosh t) *
        ((∫ t in Ioi 0, f (-t) * cosh t) + (∫ t in Ioi 0, f t * cosh t)
          - (∫ t in Ioi 0, f (-t)) - ∫ t in Ioi 0, f t) < (2 * D) ^ 2) := by
  -- integrability
  obtain ⟨iF, iFs⟩ := int_of_cosh hfc
  have hgc : Integrable (fun t => f (-t) * cosh t) := by
    have := hfc.comp_neg; simpa only [cosh_neg] using this
  obtain ⟨iG, iGs⟩ := int_of_cosh hgc
  have fnn := hf.nonneg
  set Pm := ∫ t in Ioi 0, f (-t)
  set Pp := ∫ t in Ioi 0, f t
  set Cm := ∫ t in Ioi 0, f (-t) * cosh t
  set Cp := ∫ t in Ioi 0, f t * cosh t
  have hPm : 0 < Pm := pos_of_sinh_pos (fun t _ => fnn _) iG.integrableOn iGs.integrableOn (by rw [hDm]; exact hD)
  have hPp : 0 < Pp := pos_of_sinh_pos (fun t _ => fnn _) iF.integrableOn iFs.integrableOn (by rw [hDp]; exact hD)
  have hCm : Pm ≤ Cm := setIntegral_mono_on iG.integrableOn hgc.integrableOn measurableSet_Ioi
    fun t _ => le_mul_of_one_le_right (fnn _) (one_le_cosh t)
  have hCp : Pp ≤ Cp := setIntegral_mono_on iF.integrableOn hfc.integrableOn measurableSet_Ioi
    fun t _ => le_mul_of_one_le_right (fnn _) (one_le_cosh t)
  -- Step 1: the left pure exponential
  obtain ⟨hα, hcα, hcD⟩ := alp_props hPm hD
  generalize hαg : alp Pm D = α at hα hcα hcD hor
  set c := α * Pm with hcdef
  have hc : 0 < c := by positivity
  obtain ⟨gi0, gi1, gi2, gv0, gv1, gv2⟩ := gam_half (c := c) hα
  -- Step 2: the left crossing and the tangent claim
  have e0 : (fun t => c * exp (-α * t) - f (-t)) = fun t => c * exp (-α * t) - f (-t) := rfl
  have i0 : IntegrableOn (fun t => c * exp (-α * t) - f (-t)) (Ioi 0) := gi0.sub iG.integrableOn
  have es : (fun t => (c * exp (-α * t) - f (-t)) * sinh t) =
      fun t => c * exp (-α * t) * sinh t - f (-t) * sinh t := by funext t; ring
  have ec : (fun t => (c * exp (-α * t) - f (-t)) * cosh t) =
      fun t => c * exp (-α * t) * cosh t - f (-t) * cosh t := by funext t; ring
  have i1 : IntegrableOn (fun t => (c * exp (-α * t) - f (-t)) * sinh t) (Ioi 0) := by
    rw [es]; exact gi1.sub iGs.integrableOn
  have i2 : IntegrableOn (fun t => (c * exp (-α * t) - f (-t)) * cosh t) (Ioi 0) := by
    rw [ec]; exact gi2.sub hgc.integrableOn
  have v0 : ∫ t in Ioi 0, (c * exp (-α * t) - f (-t)) = 0 := by
    rw [integral_sub gi0 iG.integrableOn, gv0, hcα]; ring
  have v1 : ∫ t in Ioi 0, (c * exp (-α * t) - f (-t)) * sinh t = 0 := by
    rw [es, integral_sub gi1 iGs.integrableOn, gv1, hcD, hDm]; ring
  have htan := tangent hf hc i0 i1 v0 v1
  have hNm : {t | 0 < t ∧ c * exp (-α * t) - f (-t) < 0}.OrdConnected := by
    have : {t | 0 < t ∧ c * exp (-α * t) - f (-t) < 0} = Ioi 0 ∩ {t | c * exp (-α * t) < f (-t)} := by
      ext t; simp [sub_neg]
    rw [this]; exact ordConnected_Ioi.inter (hf.neg.superlevel hc.le (-α))
  have hLm := lemA i0 i1 i2 v0 v1 hNm
  have hLms : strict → 0 < ∫ t in Ioi 0, (c * exp (-α * t) - f (-t)) * cosh t := fun hs =>
    lemA_strict i0 i1 i2 v0 v1 hNm (hnz hs c α hc)
  rw [ec, integral_sub gi2 hgc.integrableOn, gv2] at hLm hLms
  -- Step 3: bathtub at u = 0, then the matching
  have hm0 : 0 ≤ mfun c α Pp 0 := mfun_nonneg hc hα hPp le_rfl (by positivity)
  obtain ⟨hi0, hi1, -, hv0, hv1, -⟩ := lap_half (c := c) hm0 hα le_rfl zero_lt_one
  have hbath : (Mom c α 0 (mfun c α Pp 0) 1 - Mom c α 0 (mfun c α Pp 0) (-1)) / 2 ≤ D := by
    set m₀ := mfun c α Pp 0
    set h₀ := lap c α 0 m₀
    have hpt : ∀ s ∈ Ioi (0:ℝ), 0 ≤ f s * sinh s - h₀ s * sinh s - sinh m₀ * f s + sinh m₀ * h₀ s := by
      intro s hs
      rw [show f s * sinh s - h₀ s * sinh s - sinh m₀ * f s + sinh m₀ * h₀ s
        = (f s - h₀ s) * (sinh s - sinh m₀) by ring]
      by_cases hsm : s ≤ m₀
      · have : h₀ s = c * exp (α * s) := by simp only [h₀, lap, ite_eq_left hsm]
        have h1 : f s - h₀ s ≤ 0 := by rw [this]; linarith [htan s (le_of_lt hs)]
        have h2 : sinh s - sinh m₀ ≤ 0 := by linarith [sinh_le_sinh.mpr hsm]
        exact mul_nonneg_of_nonpos_of_nonpos h1 h2
      · have : h₀ s = 0 := by simp [h₀, lap, hsm, tl]
        rw [this, sub_zero]
        exact mul_nonneg (fnn s) (by linarith [sinh_lt_sinh.mpr (lt_of_not_ge hsm)])
    have hint := setIntegral_nonneg (μ := volume) measurableSet_Ioi hpt
    rw [integral_add (f := fun x => f x * sinh x - h₀ x * sinh x - sinh m₀ * f x)
        (g := fun x => sinh m₀ * h₀ x) ((iFs.integrableOn.sub hi1).sub (iF.integrableOn.const_mul _))
        (hi0.const_mul _),
      integral_sub (f := fun x => f x * sinh x - h₀ x * sinh x) (g := fun x => sinh m₀ * f x)
        (iFs.integrableOn.sub hi1) (iF.integrableOn.const_mul _),
      integral_sub (f := fun x => f x * sinh x) (g := fun x => h₀ x * sinh x) iFs.integrableOn hi1,
      integral_const_mul, integral_const_mul, hv0, hv1, hDp, mom0_mfun hc hα hPp le_rfl,
      show (∫ x in Ioi 0, f x) = Pp from rfl] at hint
    linarith
  have hW : Pp / c < 1 → D ≤ Pp * (Pp / c) / (1 - (Pp / c) ^ 2) := by
    intro h
    obtain ⟨hα', -, hcD'⟩ := alp_props hPp hD
    set α' := alp Pp D
    have hv : 0 < 1 / α' := by positivity
    have hvw : 1 / α' ≤ Pp / c := by
      rw [div_le_div_iff₀ (by linarith) hc]; linarith [hor]
    have := kmono hv hvw h
    have e : Pp * (1 / α' / (1 - (1 / α') ^ 2)) = D := by
      rw [← hcD']; have : α' ≠ 0 := by linarith
      have : α' ^ 2 - 1 ≠ 0 := by nlinarith
      field_simp
    have := mul_le_mul_of_nonneg_left this hPp.le
    rw [e] at this
    calc D ≤ Pp * (Pp / c / (1 - (Pp / c) ^ 2)) := this
      _ = _ := by ring
  obtain ⟨u, hu0, hu1, hm, hM⟩ := exists_match hc hα hPp hD hW hbath
  set m := mfun c α Pp u
  obtain ⟨li0, li1, li2, lv0, lv1, lv2⟩ := lap_half (c := c) hm hα hu0 hu1
  rw [mom0_mfun hc hα hPp hu0] at lv0
  rw [hM] at lv1
  -- Step 4: the right crossing
  have j0 : IntegrableOn (fun t => lap c α u m t - f t) (Ioi 0) := li0.sub iF.integrableOn
  have es' : (fun t => (lap c α u m t - f t) * sinh t) = fun t => lap c α u m t * sinh t - f t * sinh t := by
    funext t; ring
  have ec' : (fun t => (lap c α u m t - f t) * cosh t) = fun t => lap c α u m t * cosh t - f t * cosh t := by
    funext t; ring
  have j1 : IntegrableOn (fun t => (lap c α u m t - f t) * sinh t) (Ioi 0) := by
    rw [es']; exact li1.sub iFs.integrableOn
  have j2 : IntegrableOn (fun t => (lap c α u m t - f t) * cosh t) (Ioi 0) := by
    rw [ec']; exact li2.sub hfc.integrableOn
  have w0 : ∫ t in Ioi 0, (lap c α u m t - f t) = 0 := by
    rw [integral_sub li0 iF.integrableOn, lv0]; ring
  have w1 : ∫ t in Ioi 0, (lap c α u m t - f t) * sinh t = 0 := by
    rw [es', integral_sub li1 iFs.integrableOn, lv1, hDp]; ring
  obtain ⟨K, β, hK, hKβ⟩ := tl_form (α := α) (m := m) hc.le hu0
  have hNp : {t | 0 < t ∧ lap c α u m t - f t < 0}.OrdConnected := by
    have : {t | 0 < t ∧ lap c α u m t - f t < 0} = Ioi m ∩ {t | K * exp (β * t) < f t} := by
      ext t; simp only [mem_ofPred_eq, mem_inter_iff, mem_Ioi, sub_neg]
      constructor
      · rintro ⟨ht, hlt⟩
        by_cases htm : t ≤ m
        · exfalso; simp only [lap, ite_eq_left htm] at hlt; linarith [htan t ht.le]
        · simp only [lap, ite_eq_right htm, hKβ] at hlt; exact ⟨lt_of_not_ge htm, hlt⟩
      · rintro ⟨htm, hlt⟩
        refine ⟨lt_of_le_of_lt hm htm, ?_⟩
        simp only [lap, ite_eq_right (not_le.mpr htm), hKβ]; exact hlt
    rw [this]; exact ordConnected_Ioi.inter (hf.superlevel hK β)
  have hLp := lemA j0 j1 j2 w0 w1 hNp
  rw [ec', integral_sub li2 hfc.integrableOn, lv2] at hLp
  -- Step 5: Proposition D
  have hα1 : α - 1 ≠ 0 := by linarith
  have hα2 : α + 1 ≠ 0 := by linarith
  have hα3 : α ^ 2 - 1 ≠ 0 := by nlinarith
  rw [Mom_one, Mom_neg_one] at hM lv2
  have hmom0 := mom0_mfun hc hα hPp hu0
  rw [Mom_zero] at hmom0
  have hsplit : c / (α - 1) - c / (α + 1) = 2 * (c / (α ^ 2 - 1)) := by field_simp; ring
  have hsplit2 : c / (α - 1) + c / (α + 1) = 2 * (c * α / (α ^ 2 - 1)) := by field_simp; ring
  have hE : c * exp ((α + 1) * m) * (1 / (α + 1) + u / (1 - u)) =
      c * exp ((α - 1) * m) * (1 / (α - 1) + u / (1 + u)) := by
    rw [← hcD] at hM; linarith
  have hPD := lap_alg hc hα hu0 hu1 hm hE
  rw [show (∫ a in Ioi 0, f (-a) * cosh a) = Cm from rfl] at hLm hLms
  rw [show (∫ a in Ioi 0, f a * cosh a) = Cp from rfl, Mom_one, Mom_neg_one] at hLp
  set X := c * exp ((α + 1) * m) * (1 / (α + 1) + u / (1 - u))
  set Z := c * exp (α * m) * (1 / α + u)
  have hZ : Z = Pm + Pp := by
    have : Pm = c / α := by rw [hcα]
    linarith
  have hW' : Cm + Cp ≤ X := by linarith
  have hZW : Z ≤ Cm + Cp := by linarith
  rw [hcD] at hPD
  refine ⟨by nlinarith [mul_nonneg (sub_nonneg.mpr hW') (show 0 ≤ X + (Cm + Cp) - Z by linarith)],
    fun hs => ?_⟩
  have h1 := hLms hs
  have hWX : Cm + Cp < X := by linarith
  have hZ0 : 0 < Z := by linarith
  nlinarith [mul_pos (sub_pos.mpr hWX) (show 0 < X + (Cm + Cp) - Z by linarith)]

/-- Splitting a line integral at `0`. -/
lemma split0 {k : ℝ → ℝ} (hk : Integrable k) :
    ∫ s, k s = (∫ t in Ioi 0, k (-t)) + ∫ t in Ioi 0, k t := by
  rw [integral_comp_neg_Ioi, neg_zero, intervalIntegral.integral_Iic_add_Ioi hk.integrableOn hk.integrableOn]

/-- Theorem 3 (homogeneous form), with an optional strictness clause. -/
theorem thm3_gen {f : ℝ → ℝ} (hf : LC f) (hfc : Integrable (fun s => f s * cosh s))
    (hs : ∫ s, f s * sinh s = 0) (strict : Prop)
    (hnz1 : strict → ∀ c α : ℝ, 0 < c → ¬ ∀ᵐ t ∂(volume.restrict (Ioi (0:ℝ))), c * exp (-α * t) - f (-t) = 0)
    (hnz2 : strict → ∀ c α : ℝ, 0 < c → ¬ ∀ᵐ t ∂(volume.restrict (Ioi (0:ℝ))),
      c * exp (-α * t) - (fun s => f (-s)) (-t) = 0)
    (hpos : strict → 0 < ∫ s, f s) :
    (∫ s, f s * cosh s) * ((∫ s, f s * cosh s) - ∫ s, f s) ≤ (∫ s, f s * |sinh s|) ^ 2 ∧
    (strict → (∫ s, f s * cosh s) * ((∫ s, f s * cosh s) - ∫ s, f s) < (∫ s, f s * |sinh s|) ^ 2) := by
  obtain ⟨iF, iFs⟩ := int_of_cosh hfc
  have fnn := hf.nonneg
  have iFa : Integrable (fun s => f s * |sinh s|) := by
    have := iFs.norm
    refine this.congr (Filter.Eventually.of_forall fun s => ?_)
    simp only [norm_mul, Real.norm_eq_abs, abs_of_nonneg (fnn s)]
  have hgc : Integrable (fun t => f (-t) * cosh t) := by
    have := hfc.comp_neg; simpa only [cosh_neg] using this
  obtain ⟨iG, iGs⟩ := int_of_cosh hgc
  rw [split0 hfc, split0 iF, split0 iFs, split0 iFa] at *
  simp only [cosh_neg, sinh_neg, abs_neg, mul_neg] at hs ⊢
  rw [integral_neg] at hs
  have ha1 : ∫ t in Ioi 0, f (-t) * |sinh t| = ∫ t in Ioi 0, f (-t) * sinh t :=
    setIntegral_congr_fun measurableSet_Ioi fun t ht => by
      rw [abs_of_pos (sinh_pos_iff.mpr ht)]
  have ha2 : ∫ t in Ioi 0, f t * |sinh t| = ∫ t in Ioi 0, f t * sinh t :=
    setIntegral_congr_fun measurableSet_Ioi fun t ht => by
      rw [abs_of_pos (sinh_pos_iff.mpr ht)]
  rw [ha1, ha2]
  set D := ∫ t in Ioi 0, f t * sinh t
  have hDm : ∫ t in Ioi 0, f (-t) * sinh t = D := by linarith
  rw [hDm]
  have hD0 : 0 ≤ D := setIntegral_nonneg measurableSet_Ioi fun t ht =>
    mul_nonneg (fnn t) (sinh_pos_iff.mpr ht).le
  rcases hD0.eq_or_lt with hD | hD
  · obtain ⟨z1, z2⟩ := zero_of_sinh_zero (fun t _ => fnn t) iFs.integrableOn hD.symm
    obtain ⟨z3, z4⟩ := zero_of_sinh_zero (fun t _ => fnn (-t)) iGs.integrableOn (hDm.trans hD.symm)
    rw [z1, z2, z3, z4, ← hD]
    refine ⟨by norm_num, fun hs' => ?_⟩
    have := hpos hs'; rw [z1, z3] at this; norm_num at this
  · rcases le_total (alp (∫ t in Ioi 0, f (-t)) D * (∫ t in Ioi 0, f (-t)))
        (alp (∫ t in Ioi 0, f t) D * (∫ t in Ioi 0, f t)) with h | h
    · obtain ⟨h1, h2⟩ := orient hf hfc hD hDm rfl h strict hnz1
      exact ⟨by nlinarith [h1], fun hs' => by nlinarith [h2 hs']⟩
    · obtain ⟨h1, h2⟩ := orient (f := fun s => f (-s)) hf.neg hgc hD (by simp only [neg_neg]; rfl)
        (by simpa only using hDm) (by simpa only [neg_neg] using h) strict hnz2
      simp only [neg_neg] at h1 h2
      exact ⟨by nlinarith [h1], fun hs' => by nlinarith [h2 hs']⟩

/-- **Theorem 3** (homogeneous form, non-strict). -/
theorem thm3 {f : ℝ → ℝ} (hf : LC f) (hfc : Integrable (fun s => f s * cosh s))
    (hs : ∫ s, f s * sinh s = 0) :
    (∫ s, f s * cosh s) * ((∫ s, f s * cosh s) - ∫ s, f s) ≤ (∫ s, f s * |sinh s|) ^ 2 :=
  (thm3_gen hf hfc hs False False.elim False.elim False.elim).1

/-- **Theorem 3** (homogeneous form, strict for strictly log-concave `f` with `∫ f > 0`). -/
theorem thm3_strict {f : ℝ → ℝ} (hf : LCs f) (hfc : Integrable (fun s => f s * cosh s))
    (hs : ∫ s, f s * sinh s = 0) (hpos : 0 < ∫ s, f s) :
    (∫ s, f s * cosh s) * ((∫ s, f s * cosh s) - ∫ s, f s) < (∫ s, f s * |sinh s|) ^ 2 :=
  (thm3_gen hf.lc hfc hs True (fun _ => noaffine hf) (fun _ => noaffine hf.neg) (fun _ => hpos)).2 trivial

-- ===== Theorem 1 (MathOverflow 184460) =====

/-!
# Theorem 1: MathOverflow 184460

For `P = N(-μ,1)` and `Q = N(μ,1)` truncated to an interval `I` (any `OrdConnected` set of positive length,
e.g. `[a,b]` with `a < b`), the Hellinger distance is at most the total variation distance:
`d_H(P,Q) ≤ d_TV(P,Q)`, with the conventions of the question:
`d_TV = (1/2) ‖p - q‖₁` and `d_H² = (1/2) ‖√p - √q‖₂²`.
-/

open Real MeasureTheory Set ProbabilityTheory

/-- Density of `N(θ, 1)` truncated to `I`. -/
noncomputable def tgauss (θ : ℝ) (I : Set ℝ) (x : ℝ) : ℝ :=
  I.indicator (gaussianPDFReal θ 1) x / ∫ y in I, gaussianPDFReal θ 1 y

/-- Total variation distance between two densities on `ℝ`: `(1/2) ∫ |p - q|`. -/
noncomputable def tvDens (p q : ℝ → ℝ) : ℝ := (1 / 2) * ∫ x, |p x - q x|

/-- Hellinger distance between two densities on `ℝ`: `√((1/2) ∫ (√p - √q)²)`. -/
noncomputable def hellinger (p q : ℝ → ℝ) : ℝ := sqrt ((1 / 2) * ∫ x, (sqrt (p x) - sqrt (q x)) ^ 2)

lemma hellinger_comm (p q : ℝ → ℝ) : hellinger p q = hellinger q p := by
  unfold hellinger; congr 3; funext x; ring

lemma tvDens_comm (p q : ℝ → ℝ) : tvDens p q = tvDens q p := by
  unfold tvDens; congr 2; funext x; rw [abs_sub_comm]

lemma tvDens_nonneg (p q : ℝ → ℝ) : 0 ≤ tvDens p q := by
  unfold tvDens; have := integral_nonneg (μ := volume) (fun x => abs_nonneg (p x - q x)); positivity

lemma gZ_pos (θ : ℝ) {I : Set ℝ} (_hI : I.OrdConnected) (hvol : volume I ≠ 0) :
    0 < ∫ y in I, gaussianPDFReal θ 1 y := by
  have hae : 0 ≤ᵐ[volume.restrict I] gaussianPDFReal θ 1 := by
    exact Filter.Eventually.of_forall fun x => (gaussianPDFReal_pos θ 1 x one_ne_zero).le
  rw [setIntegral_pos_iff_support_of_nonneg_ae hae (integrable_gaussianPDFReal θ 1).integrableOn]
  have : Function.support (gaussianPDFReal θ 1) ∩ I = I := by
    ext x; simp [(gaussianPDFReal_pos θ 1 x one_ne_zero).ne']
  rw [this]; exact pos_iff_ne_zero.mpr hvol

lemma tgauss_integral (θ : ℝ) {I : Set ℝ} (hI : I.OrdConnected) (hvol : volume I ≠ 0) :
    Integrable (tgauss θ I) ∧ ∫ x, tgauss θ I x = 1 := by
  have hm : MeasurableSet I := hI.measurableSet
  have hZ := gZ_pos θ hI hvol
  unfold tgauss
  refine ⟨((integrable_gaussianPDFReal θ 1).indicator hm).div_const _, ?_⟩
  rw [integral_div, integral_indicator hm, div_self hZ.ne']

lemma gauss_one (θ x : ℝ) : gaussianPDFReal θ 1 x = (sqrt (2 * π))⁻¹ * exp (-(x - θ) ^ 2 / 2) := by
  rw [gaussianPDFReal]; push_cast; ring_nf

/-- Change of variables `s = μ x + c`. -/
lemma cov {μ : ℝ} (hμ : 0 < μ) (c : ℝ) (H : ℝ → ℝ) :
    ∫ x, H (μ * x + c) = μ⁻¹ * ∫ s, H s := by
  have := Measure.integral_comp_mul_left (fun y => H (y + c)) μ
  rw [this, integral_add_right_eq_self, abs_of_pos (inv_pos.mpr hμ), smul_eq_mul]

theorem mo184460_pos {μ : ℝ} (hμ : 0 < μ) {I : Set ℝ} (hI : I.OrdConnected) (hvol : volume I ≠ 0) :
    hellinger (tgauss (-μ) I) (tgauss μ I) < tvDens (tgauss (-μ) I) (tgauss μ I) := by
  have hm : MeasurableSet I := hI.measurableSet
  set p := tgauss (-μ) I with hp
  set q := tgauss μ I with hq
  obtain ⟨ip, vp⟩ := tgauss_integral (-μ) hI hvol
  obtain ⟨iq, vq⟩ := tgauss_integral μ hI hvol
  set Zp := ∫ y in I, gaussianPDFReal (-μ) 1 y
  set Zq := ∫ y in I, gaussianPDFReal μ 1 y
  have hZp : 0 < Zp := gZ_pos (-μ) hI hvol
  have hZq : 0 < Zq := gZ_pos μ hI hvol
  set w := sqrt (Zp * Zq)
  have hw : 0 < w := sqrt_pos.mpr (by positivity)
  have hw2 : w ^ 2 = Zp * Zq := sq_sqrt (by positivity)
  set c := log (Zp / w)
  have hec : exp c = Zp / w := exp_log (by positivity)
  have hemc : exp (-c) = w / Zp := by rw [exp_neg, hec, inv_div]
  set κ := exp (-μ ^ 2 / 2) / w
  have hκ : 0 < κ := by positivity
  -- the geometric mean density r = √(pq)
  set r : ℝ → ℝ := fun x => I.indicator (gaussianPDFReal 0 1) x * κ with hr
  have ir : Integrable r := ((integrable_gaussianPDFReal 0 1).indicator hm).mul_const κ
  have rnn : ∀ x, 0 ≤ r x := fun x => by
    simp only [hr]; unfold indicator; split_ifs
    · exact mul_nonneg (gaussianPDFReal_pos 0 1 x one_ne_zero).le hκ.le
    · simp
  have hpx : ∀ x, p x = r x * exp (-(μ * x + c)) := by
    intro x; simp only [hp, hr, tgauss]
    rw [show (∫ y in I, gaussianPDFReal (-μ) 1 y) = Zp from rfl]
    unfold indicator; split_ifs
    · rw [gauss_one, gauss_one]
      rw [show -(μ * x + c) = -(μ * x) + -c by ring, exp_add, hemc]
      have e1 : exp (-(x - -μ) ^ 2 / 2) = exp (-(x - 0) ^ 2 / 2) * exp (-μ ^ 2 / 2) * exp (-(μ * x)) := by
        rw [← exp_add, ← exp_add]; congr 1; ring
      rw [e1]; simp only [κ]; field_simp
    · simp
  have hqx : ∀ x, q x = r x * exp (μ * x + c) := by
    intro x; simp only [hq, hr, tgauss]
    rw [show (∫ y in I, gaussianPDFReal μ 1 y) = Zq from rfl]
    unfold indicator; split_ifs
    · rw [gauss_one, gauss_one]
      rw [exp_add, hec]
      have e1 : exp (-(x - μ) ^ 2 / 2) = exp (-(x - 0) ^ 2 / 2) * exp (-μ ^ 2 / 2) * exp (μ * x) := by
        rw [← exp_add, ← exp_add]; congr 1; ring
      rw [e1]; simp only [κ]
      have : Zq = w ^ 2 / Zp := by rw [hw2]; field_simp
      rw [this]; field_simp
    · simp
  have hsq : ∀ x, sqrt (p x) * sqrt (q x) = r x := by
    intro x
    rw [← sqrt_mul (by rw [hpx]; exact mul_nonneg (rnn x) (exp_pos _).le), hpx, hqx]
    rw [show r x * exp (-(μ * x + c)) * (r x * exp (μ * x + c)) = r x * r x by
      rw [mul_mul_mul_comm, ← exp_add, neg_add_cancel, exp_zero, mul_one]]
    exact sqrt_mul_self (rnn x)
  set S : ℝ → ℝ := fun x => μ * x + c
  have hcoshx : ∀ x, r x * cosh (S x) = (p x + q x) / 2 := by
    intro x; rw [hpx, hqx, cosh_eq]; ring
  have hsinhx : ∀ x, r x * sinh (S x) = (q x - p x) / 2 := by
    intro x; rw [hpx, hqx, sinh_eq]; ring
  have habsx : ∀ x, r x * |sinh (S x)| = |p x - q x| / 2 := by
    intro x
    rw [show |p x - q x| = |2 * (r x * sinh (S x))| by rw [hsinhx]; rw [abs_sub_comm]; congr 1; ring,
      abs_mul, abs_mul, abs_of_nonneg (rnn x)]; norm_num
  -- the density of S under the geometric mean: F(s) = r((s - c)/μ)/μ
  set F : ℝ → ℝ := fun s => r ((s - c) / μ) / μ with hF
  have hFx : ∀ x, F (μ * x + c) = r x / μ := by
    intro x; simp only [hF]; congr 2; field_simp; ring
  have covF : ∀ k : ℝ → ℝ, ∫ s, F s * k s = ∫ x, r x * k (μ * x + c) := by
    intro k
    have := cov hμ c (fun s => F s * k s)
    simp only [hFx] at this
    have e : ∫ x, r x / μ * k (μ * x + c) = μ⁻¹ * ∫ x, r x * k (μ * x + c) := by
      rw [← integral_const_mul]; congr 1; funext x; ring
    rw [e] at this
    have hμ' : μ⁻¹ ≠ 0 := inv_ne_zero hμ.ne'
    exact (mul_left_cancel₀ hμ' this).symm
  -- F is log-concave
  have hLC : LCs F := by
    refine ⟨{s | (s - c) / μ ∈ I}, fun s => log (κ / μ) + (-(((s - c) / μ) - 0) ^ 2 / 2)
      + log (sqrt (2 * π))⁻¹, ?_, ?_, ?_⟩
    · refine ⟨fun x hx y hy z hz => hI.out hx hy ⟨?_, ?_⟩⟩
      · exact div_le_div_of_nonneg_right (by linarith [hz.1]) hμ.le
      · exact div_le_div_of_nonneg_right (by linarith [hz.2]) hμ.le
    · have hc : StrictConcaveOn ℝ univ (fun s : ℝ => log (κ / μ) + (-(((s - c) / μ) - 0) ^ 2 / 2)
          + log (sqrt (2 * π))⁻¹) := by
        refine ⟨convex_univ, fun x _ y _ hxy a b ha hb hab => ?_⟩
        simp only [smul_eq_mul]
        have hb' : b = 1 - a := by linarith
        subst hb'
        have : ((a * x + (1 - a) * y) - c) / μ = a * ((x - c) / μ) + (1 - a) * ((y - c) / μ) := by
          field_simp; ring
        rw [this]
        have hXY : (x - c) / μ - (y - c) / μ ≠ 0 := by
          intro h; apply hxy
          have : (x - c) / μ = (y - c) / μ := by linarith
          rw [div_left_inj₀ hμ.ne'] at this; linarith
        simp only [sub_zero]
        generalize (x - c) / μ = X at hXY ⊢
        generalize (y - c) / μ = Y at hXY ⊢
        have hpos : 0 < a * (1 - a) * (X - Y) ^ 2 := mul_pos (mul_pos ha hb) (pow_pos (abs_pos.mpr hXY) 2 |>.trans_eq (sq_abs _))
        nlinarith [hpos]
      exact hc.subset (subset_univ _) (by
        have : ({s | (s - c) / μ ∈ I} : Set ℝ).OrdConnected :=
          ⟨fun x hx y hy z hz => hI.out hx hy ⟨div_le_div_of_nonneg_right (by linarith [hz.1]) hμ.le,
            div_le_div_of_nonneg_right (by linarith [hz.2]) hμ.le⟩⟩
        exact this.convex)
    · funext s
      by_cases h : (s - c) / μ ∈ I
      · have h' : s ∈ {s | (s - c) / μ ∈ I} := h
        rw [indicator_of_mem h']
        simp only [hF, hr, indicator_of_mem h, gauss_one]
        rw [exp_add, exp_add, exp_log (by positivity), exp_log (by positivity)]
        field_simp
      · have h' : s ∉ {s | (s - c) / μ ∈ I} := h
        rw [indicator_of_notMem h']
        simp only [hF, hr, indicator_of_notMem h]; simp
  -- integrability and the moments
  have iFc : Integrable (fun s => F s * cosh s) := by
    have h1 : Integrable (fun x => r x * cosh (S x)) := by
      have : (fun x => r x * cosh (S x)) = fun x => (p x + q x) / 2 := funext hcoshx
      rw [this]; exact (ip.add iq).div_const 2
    -- (F cosh)(s) = μ⁻¹ * (r cosh S)((s - c)/μ)
    have h2 := ((h1.comp_mul_left' (inv_ne_zero hμ.ne')).comp_sub_right c).const_mul μ⁻¹
    refine h2.congr (Filter.Eventually.of_forall fun s => ?_)
    simp only [S, hF]
    have e1 : μ⁻¹ * (s - c) = (s - c) / μ := by rw [div_eq_inv_mul]
    have e2 : μ * ((s - c) / μ) + c = s := by field_simp; ring
    rw [e1, e2]; ring
  have m1 : ∫ s, F s * cosh s = 1 := by
    rw [covF]
    have : (fun x => r x * cosh (μ * x + c)) = fun x => (p x + q x) / 2 := funext hcoshx
    rw [this, integral_div, integral_add ip iq, vp, vq]; norm_num
  have m0 : ∫ s, F s * sinh s = 0 := by
    rw [covF]
    have : (fun x => r x * sinh (μ * x + c)) = fun x => (q x - p x) / 2 := funext hsinhx
    rw [this, integral_div, integral_sub iq ip, vp, vq]; norm_num
  have mabs : ∫ s, F s * |sinh s| = tvDens p q := by
    rw [covF]
    have : (fun x => r x * |sinh (μ * x + c)|) = fun x => |p x - q x| / 2 := funext habsx
    rw [this, integral_div]; unfold tvDens; ring
  have mone : ∫ s, F s = ∫ x, r x := by
    have := covF (fun _ => 1); simpa using this
  have hrpos : 0 < ∫ x, r x := by
    simp only [hr]
    rw [integral_mul_const, integral_indicator hm]
    exact mul_pos (gZ_pos 0 hI hvol) hκ
  have hT := thm3_strict hLC iFc m0 (by rw [mone]; exact hrpos)
  rw [m1, mabs, mone] at hT
  -- Hellinger² = 1 - ∫ r
  have hH : (1 / 2) * ∫ x, (sqrt (p x) - sqrt (q x)) ^ 2 = 1 - ∫ x, r x := by
    have pnn : ∀ x, 0 ≤ p x := fun x => by rw [hpx]; exact mul_nonneg (rnn x) (exp_pos _).le
    have qnn : ∀ x, 0 ≤ q x := fun x => by rw [hqx]; exact mul_nonneg (rnn x) (exp_pos _).le
    have : (fun x => (sqrt (p x) - sqrt (q x)) ^ 2) = fun x => p x + q x - 2 * r x := by
      funext x; rw [sub_sq, sq_sqrt (pnn x), sq_sqrt (qnn x), mul_assoc, hsq]; ring
    rw [this, integral_sub (f := fun x => p x + q x) (g := fun x => 2 * r x) (ip.add iq) (ir.const_mul 2),
      integral_add ip iq, integral_const_mul, vp, vq]
    ring
  unfold hellinger
  rw [hH]
  have hTV := tvDens_nonneg p q
  have hH0 : 0 ≤ 1 - ∫ x, r x := by
    rw [← hH]; exact mul_nonneg (by norm_num) (integral_nonneg fun x => sq_nonneg _)
  calc sqrt (1 - ∫ x, r x) < sqrt (tvDens p q ^ 2) := sqrt_lt_sqrt hH0 (by linarith)
    _ = tvDens p q := sqrt_sq hTV

/-- **MO 184460** (answer YES): for `N(-μ,1)` and `N(μ,1)` truncated to any interval `I` of positive length,
the Hellinger distance is at most the total variation distance. -/
theorem mo184460 (μ : ℝ) {I : Set ℝ} (hI : I.OrdConnected) (hvol : volume I ≠ 0) :
    hellinger (tgauss (-μ) I) (tgauss μ I) ≤ tvDens (tgauss (-μ) I) (tgauss μ I) := by
  rcases lt_trichotomy μ 0 with h | h | h
  · have := mo184460_pos (neg_pos.mpr h) hI hvol
    rw [neg_neg] at this
    rw [hellinger_comm, tvDens_comm]; exact this.le
  · subst h
    unfold hellinger
    simp only [neg_zero, sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      integral_zero, mul_zero, sqrt_zero]
    exact tvDens_nonneg _ _
  · exact (mo184460_pos h hI hvol).le

/-- **Theorem 1** (strict): for `μ ≠ 0`, `d_H < d_TV`. -/
theorem mo184460_strict {μ : ℝ} (hμ : μ ≠ 0) {I : Set ℝ} (hI : I.OrdConnected) (hvol : volume I ≠ 0) :
    hellinger (tgauss (-μ) I) (tgauss μ I) < tvDens (tgauss (-μ) I) (tgauss μ I) := by
  rcases lt_or_gt_of_ne hμ with h | h
  · have := mo184460_pos (neg_pos.mpr h) hI hvol
    rw [neg_neg] at this
    rw [hellinger_comm, tvDens_comm]; exact this
  · exact mo184460_pos h hI hvol

/-- The question's form: truncation to `[a, b]` with `a < b`. -/
theorem mo184460_Icc (μ a b : ℝ) (hab : a < b) :
    hellinger (tgauss (-μ) (Icc a b)) (tgauss μ (Icc a b)) ≤
      tvDens (tgauss (-μ) (Icc a b)) (tgauss μ (Icc a b)) :=
  mo184460 μ ordConnected_Icc (by rw [Real.volume_Icc, ne_eq, ENNReal.ofReal_eq_zero, not_le]; linarith)

/-- Strict form for `[a, b]`. -/
theorem mo184460_Icc_strict {μ a b : ℝ} (hμ : μ ≠ 0) (hab : a < b) :
    hellinger (tgauss (-μ) (Icc a b)) (tgauss μ (Icc a b)) <
      tvDens (tgauss (-μ) (Icc a b)) (tgauss μ (Icc a b)) :=
  mo184460_strict hμ ordConnected_Icc (by rw [Real.volume_Icc, ne_eq, ENNReal.ofReal_eq_zero, not_le]; linarith)

end HellingerTV

