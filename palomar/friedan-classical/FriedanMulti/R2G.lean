/-
Copyright 2026 Ming-Chih Kao. Licensed under the Apache License, Version 2.0;
see the LICENSE file at the root of this repository.
-/
module

public import FriedanMulti.R2E

/-! Port: copied from `FriedanMulti/R2G.lean` of github.com/koolkao/friedan-entropy-inequality (commit 0f4ba65dc126f59e7158fbcbc01548baa78cf21d, Lean v4.33.1, Mathlib 0df444a) and put into the module system (`module` header, `public import`, public section). No other change was needed for Lean v4.36.0 / Mathlib fc4f59e. -/

@[expose] public section

/-!
# `Gs ≥ 0` on `(0, ∞)` (the case `g = 2 log 2`)
-/

open Real Filter Topology

namespace FriedanR2

noncomputable def Gs (s : ℝ) : ℝ :=
  Real.log (1 + Real.exp (-s)) - Real.log (1 + Real.exp (-(cc * s))) / cc
    - (Real.exp (-s) - Real.exp (-(cc * s))) / ((1 + Real.exp (-(cc * s))) * (1 - Real.exp (-s)))

lemma cc_pos : 0 < cc := by have := cc_gt; linarith

section exps
variable (s : ℝ)
lemma eA : Real.exp (-s) = Real.exp (-(s / 2)) ^ 2 := by
  rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
lemma eB : Real.exp (3 / 2 * s) = (Real.exp (-(s / 2)) ^ 3)⁻¹ := by
  rw [← Real.exp_nat_mul, ← Real.exp_neg]; congr 1; push_cast; ring
lemma eC : Real.exp (-(3 / 2 * s)) = Real.exp (-(s / 2)) ^ 3 := by
  rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
lemma eD : Real.exp (1 / 2 * s) = (Real.exp (-(s / 2)))⁻¹ := by
  rw [← Real.exp_neg]; congr 1; ring
lemma eE : Real.exp (-(1 / 2 * s)) = Real.exp (-(s / 2)) := by congr 1; ring
lemma eF : Real.exp ((cc - 1 / 2) * s) = Real.exp (-(s / 2)) / Real.exp (-(cc * s)) := by
  rw [← Real.exp_sub]; congr 1; ring
lemma eG : Real.exp (-((cc - 1 / 2) * s)) = Real.exp (-(cc * s)) / Real.exp (-(s / 2)) := by
  rw [← Real.exp_sub]; congr 1; ring
lemma eH : Real.exp ((3 / 2 - cc) * s) = Real.exp (-(cc * s)) / Real.exp (-(s / 2)) ^ 3 := by
  rw [← Real.exp_nat_mul, ← Real.exp_sub]; congr 1; push_cast; ring
lemma eI : Real.exp (-((3 / 2 - cc) * s)) = Real.exp (-(s / 2)) ^ 3 / Real.exp (-(cc * s)) := by
  rw [← Real.exp_nat_mul, ← Real.exp_sub]; congr 1; push_cast; ring
lemma eJ : Real.exp (-((cc + 3 / 2) * s)) = Real.exp (-(cc * s)) * Real.exp (-(s / 2)) ^ 3 := by
  rw [← Real.exp_nat_mul, ← Real.exp_add]; congr 1; push_cast; ring
end exps

noncomputable def KG (s : ℝ) : ℝ :=
  2 * Real.exp (-((cc + 3 / 2) * s)) /
    ((1 + Real.exp (-s)) * (1 + Real.exp (-(cc * s))) ^ 2 * (1 - Real.exp (-s)) ^ 2)

lemma KG_pos (s : ℝ) (hs : 0 < s) : 0 < KG s := by
  have h1 : Real.exp (-s) < 1 := by rw [Real.exp_lt_one_iff]; linarith
  unfold KG
  have : 0 < 1 - Real.exp (-s) := by linarith
  positivity

lemma hd_Gs {s : ℝ} (hs : 0 < s) : HasDerivAt Gs (-(KG s * Sk 0 s)) s := by
  have h1 : Real.exp (-s) < 1 := by rw [Real.exp_lt_one_iff]; linarith
  have hD : (1 + Real.exp (-(cc * s))) * (1 - Real.exp (-s)) ≠ 0 := by
    have : 0 < 1 - Real.exp (-s) := by linarith
    positivity
  have hr : HasDerivAt (fun s => Real.exp (-s)) (Real.exp (-s) * (-1)) s := (hasDerivAt_neg s).exp
  have hx : HasDerivAt (fun s => Real.exp (-(cc * s))) (Real.exp (-(cc * s)) * (-(cc * 1))) s :=
    ((hasDerivAt_id' s).const_mul cc).neg.exp
  have l1 := (hr.const_add 1).log (by positivity)
  have l2 := ((hx.const_add 1).log (by positivity)).div_const cc
  have q := (hr.sub hx).div ((hx.const_add 1).mul (hr.const_sub 1)) hD
  unfold Gs
  refine ((l1.sub l2).sub q).congr_deriv ?_
  have h0 : Even 0 := by decide
  simp only [KG, Sk, h0, if_true, pow_zero, mul_one, Real.sinh_eq, Pi.sub_apply, Pi.mul_apply]
  rw [eA, eB, eC, eD, eE, eF, eG, eH, eI, eJ]
  have hw : 0 < Real.exp (-(s / 2)) := Real.exp_pos _
  have hz : 0 < Real.exp (-(cc * s)) := Real.exp_pos _
  have hw1 : Real.exp (-(s / 2)) < 1 := by rw [Real.exp_lt_one_iff]; linarith
  have hw2 : 1 - Real.exp (-(s / 2)) ^ 2 ≠ 0 := by
    have : Real.exp (-(s / 2)) ^ 2 < 1 := by nlinarith
    linarith
  have hc := cc_pos.ne'
  field_simp
  ring

/-! ### Limits -/

lemma Gs_atTop : Tendsto Gs atTop (𝓝 0) := by
  have hr : Tendsto (fun s : ℝ => Real.exp (-s)) atTop (𝓝 0) := Real.tendsto_exp_neg_atTop_nhds_zero
  have hx : Tendsto (fun s : ℝ => Real.exp (-(cc * s))) atTop (𝓝 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_id.const_mul_atTop cc_pos)
  have t1 := (tendsto_const_nhds (x := (1 : ℝ))).add hr
  have t2 := (tendsto_const_nhds (x := (1 : ℝ))).add hx
  have t3 := (tendsto_const_nhds (x := (1 : ℝ))).sub hr
  have := ((t1.log (by norm_num)).sub ((t2.log (by norm_num)).div_const cc)).sub
    ((hr.sub hx).div (t2.mul t3) (by norm_num))
  unfold Gs
  simpa using this

lemma Gs_zero : Tendsto Gs (𝓝[>] 0) (𝓝 0) := by
  have hN : HasDerivAt (fun t => Real.exp (-t) - Real.exp (-(cc * t))) (-1 + cc) 0 := by
    have := ((hasDerivAt_neg (0 : ℝ)).exp).sub (((hasDerivAt_id' (0 : ℝ)).const_mul cc).neg.exp)
    refine this.congr_deriv ?_
    simp
  have hDd : HasDerivAt (fun t => 1 - Real.exp (-t)) 1 0 := by
    have := ((hasDerivAt_neg (0 : ℝ)).exp).const_sub 1
    refine this.congr_deriv ?_
    simp
  have sN := hN.tendsto_slope_zero_right
  have sD := hDd.tendsto_slope_zero_right
  simp only [zero_add, smul_eq_mul, neg_zero, mul_zero, Real.exp_zero, sub_self, sub_zero] at sN sD
  have hratio : Tendsto (fun t => (Real.exp (-t) - Real.exp (-(cc * t))) / (1 - Real.exp (-t)))
      (𝓝[>] 0) (𝓝 ((-1 + cc) / 1)) := by
    refine (sN.div sD one_ne_zero).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    have ht' : t ≠ 0 := ne_of_gt ht
    simp only [Pi.div_apply]
    rw [mul_div_mul_left _ _ (inv_ne_zero ht')]
  have cr : Tendsto (fun t : ℝ => Real.exp (-t)) (𝓝[>] 0) (𝓝 1) := by
    have hc : Continuous (fun t : ℝ => Real.exp (-t)) := by fun_prop
    have := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
    simpa using this
  have cx : Tendsto (fun t : ℝ => Real.exp (-(cc * t))) (𝓝[>] 0) (𝓝 1) := by
    have hc : Continuous (fun t : ℝ => Real.exp (-(cc * t))) := by fun_prop
    have := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
    simpa using this
  have t1 := (tendsto_const_nhds (x := (1 : ℝ))).add cr
  have t2 := (tendsto_const_nhds (x := (1 : ℝ))).add cx
  have lim := ((t1.log (by norm_num)).sub ((t2.log (by norm_num)).div_const cc)).sub
    (hratio.div t2 (by norm_num))
  have hval : Real.log (1 + 1) - Real.log (1 + 1) / cc - (-1 + cc) / 1 / (1 + 1) = 0 := by
    have hc := cc_pos.ne'
    unfold cc at hc ⊢
    norm_num
    field_simp
    ring
  rw [hval] at lim
  refine lim.congr' (Filter.Eventually.of_forall (fun t => ?_))
  simp only [Gs, Pi.div_apply]
  rw [div_div, mul_comm (1 - Real.exp (-t))]

/-! ### Conclusion -/

theorem Gs_nonneg {s0 : ℝ} (hs0 : 0 < s0) : 0 ≤ Gs s0 := by
  by_contra hneg
  push Not at hneg
  -- far out, `Gs` exceeds `Gs s0`
  obtain ⟨s1, hs1, hG1⟩ : ∃ s1, s0 < s1 ∧ Gs s0 < Gs s1 := by
    have ev := (Gs_atTop.eventually (lt_mem_nhds hneg)).and (eventually_gt_atTop s0)
    obtain ⟨s1, h1, h2⟩ := ev.exists
    exact ⟨s1, h2, h1⟩
  have hcont : ∀ t, 0 < t → ContinuousAt Gs t := fun t ht => (hd_Gs ht).continuousAt
  obtain ⟨ξ, hξ, hξd⟩ := exists_hasDerivAt_eq_slope Gs (fun t => -(KG t * Sk 0 t)) hs1
    (fun t ht => (hcont t (by linarith [ht.1])).continuousWithinAt)
    (fun t ht => hd_Gs (by linarith [ht.1]))
  have hξ0 : 0 < ξ := by linarith [hξ.1]
  have hpos : 0 < -(KG ξ * Sk 0 ξ) := by
    rw [hξd]; exact div_pos (by linarith) (by linarith)
  have hSξ : Sk 0 ξ < 0 := by
    have := KG_pos ξ hξ0
    by_contra h; push Not at h
    have := mul_nonneg this.le h
    linarith
  have hS : ∀ t, 0 < t → t ≤ ξ → Sk 0 t < 0 := by
    intro t ht htξ
    by_contra h; push Not at h
    have := S_N t ξ ht htξ h
    linarith
  -- `Gs` is increasing on `(0, ξ]`
  have hmono : MonotoneOn Gs (Set.Ioc 0 ξ) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ioc 0 ξ) (f' := fun t => -(KG t * Sk 0 t))
      (fun t ht => (hcont t ht.1).continuousWithinAt) (fun t ht => ?_) ?_
    · rw [interior_Ioc] at ht; exact (hd_Gs ht.1).hasDerivWithinAt
    · intro t ht
      rw [interior_Ioc] at ht
      nlinarith [hS t ht.1 ht.2.le, KG_pos t ht.1]
  have hle : ∀ t ∈ Set.Ioo 0 s0, Gs t ≤ Gs s0 := fun t ht =>
    hmono ⟨ht.1, by linarith [ht.2, hξ.1]⟩ ⟨hs0, by linarith [hξ.1]⟩ ht.2.le
  have := le_of_tendsto Gs_zero (Filter.mem_of_superset (Ioo_mem_nhdsGT hs0) hle)
  linarith

end FriedanR2

end
