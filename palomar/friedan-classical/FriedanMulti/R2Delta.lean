/-
Copyright 2026 Ming-Chih Kao. Licensed under the Apache License, Version 2.0;
see the LICENSE file at the root of this repository.
-/
module

public import FriedanMulti.R2Basic
public import FriedanMulti.R2Analytic
public import FriedanMulti.R2G

/-! Port: copied from `FriedanMulti/R2Delta.lean` of github.com/koolkao/friedan-entropy-inequality (commit 0f4ba65dc126f59e7158fbcbc01548baa78cf21d, Lean v4.33.1, Mathlib 0df444a) and put into the module system (`module` header, `public import`, public section). No other change was needed for Lean v4.36.0 / Mathlib fc4f59e. -/

@[expose] public section

/-!
# Lemma R4 (MULTI.md §5.2): `Δ_g(A, 0) ≥ 0` for `0 < g < 1` and `1 < g ≤ 2 log 2`

With `r = e^{-A}`, `x = e^{-gA}`: `Δ_g(A,0) = g W_r(x) / ((1-g)(1+r))` (`Dg_eq_W`), where
`W_r(y) = (1-r) A (ff y - ff r) - (y - r)/(1+y)`. For `g < 1`, `W_r` is nondecreasing on `[r, 1)`
(`kk ≥ 0`); for `1 < g ≤ c`, `W_r` is convex, `W_r(r) = 0` and `W_r(e^{-cA}) = -(1-r) Gs(A) ≤ 0`.
-/

open Real Friedan

namespace FriedanR2

lemma lp_eq (t : ℝ) : Friedan.lp t = t / 2 + Real.log (1 + Real.exp (-t)) := by
  unfold Friedan.lp
  rw [show Real.exp (t / 2) + Real.exp (-t / 2) = Real.exp (t / 2) * (1 + Real.exp (-t)) by
    rw [mul_add, mul_one, ← Real.exp_add]; ring_nf]
  rw [Real.log_mul (Real.exp_pos _).ne' (by positivity), Real.log_exp]

lemma sg_eq (t : ℝ) : sg t = 1 / (1 + Real.exp (-t)) := by
  unfold sg
  rw [show Real.exp (t / 2) + Real.exp (-t / 2) = Real.exp (t / 2) * (1 + Real.exp (-t)) by
    rw [mul_add, mul_one, ← Real.exp_add]; ring_nf]
  field_simp

noncomputable def WW (r A y : ℝ) : ℝ := (1 - r) * A * (ff y - ff r) - (y - r) / (1 + y)

lemma Dg_eq_W {g A : ℝ} (hg0 : 0 < g) (hg1' : g ≠ 1) (hA : 0 < A) :
    Dg g A 0 = g * WW (Real.exp (-A)) A (Real.exp (-(g * A))) /
      ((1 - g) * (1 + Real.exp (-A))) := by
  have h1g : 1 - g ≠ 0 := sub_ne_zero.2 (Ne.symm hg1')
  have hA' := hA.ne'
  have hg' := hg0.ne'
  have e1 : 1 + Real.exp (-A) ≠ 0 := by positivity
  have e2 : 1 + Real.exp (-(g * A)) ≠ 0 := by positivity
  unfold Dg
  rw [hg1_zero, sg_zero]
  unfold hg hg1 WW ff
  rw [lp_eq (g * A), lp_eq A, sg_eq (g * A), sg_eq A, Real.log_exp, Real.log_exp]
  field_simp
  ring

lemma hd_WW {r A y : ℝ} (h0 : 0 < y) (h1 : y < 1) :
    HasDerivAt (WW r A) ((1 - r) * A * ff1 y - (1 + r) / (1 + y) ^ 2) y := by
  have hy : 1 + y ≠ 0 := by linarith
  unfold WW
  refine ((((hd_ff h0 h1).sub_const (ff r)).const_mul ((1 - r) * A)).sub
    (((hasDerivAt_id' y).sub_const r).div ((hasDerivAt_id' y).const_add 1) hy)).congr_deriv ?_
  field_simp
  ring

lemma hd_WW1 {r A y : ℝ} (h0 : 0 < y) (h1 : y < 1) :
    HasDerivAt (fun y => (1 - r) * A * ff1 y - (1 + r) / (1 + y) ^ 2)
      ((1 - r) * A * ff2 y + 2 * (1 + r) / (1 + y) ^ 3) y := by
  have hy : 1 + y ≠ 0 := by linarith
  refine (((hd_ff1 h0 h1).const_mul ((1 - r) * A)).sub
    ((hasDerivAt_const y (1 + r)).div (((hasDerivAt_id' y).const_add 1).pow 2)
      (pow_ne_zero 2 hy))).congr_deriv ?_
  simp only [Nat.cast_ofNat, Pi.pow_apply]
  field_simp
  ring

/-- Case `g < 1`. -/
lemma Dg0_lt1 {g A : ℝ} (hg0 : 0 < g) (hg1' : g < 1) (hA : 0 < A) : 0 ≤ Dg g A 0 := by
  set r := Real.exp (-A) with hr
  set x := Real.exp (-(g * A)) with hx
  have hr0 : 0 < r := Real.exp_pos _
  have hr1 : r < 1 := by rw [hr, Real.exp_lt_one_iff]; linarith
  have hx1 : x < 1 := by rw [hx, Real.exp_lt_one_iff]; nlinarith
  have hrx : r ≤ x := by rw [hr, hx]; exact Real.exp_le_exp.2 (by nlinarith)
  have hlogr : -Real.log r = A := by rw [hr, Real.log_exp]; ring
  -- W' (r) ≥ 0
  have hW'r : 0 ≤ (1 - r) * A * ff1 r - (1 + r) / (1 + r) ^ 2 := by
    have hk := kk_nonneg hr0.le hr1.le
    have e : (1 - r) * A * ff1 r - (1 + r) / (1 + r) ^ 2 = kk r / (r * (1 + r) * A) := by
      unfold ff1 kk
      rw [hlogr, show Real.log r = -A by linarith]
      field_simp
      ring
    rw [e]; positivity
  have hmono : MonotoneOn (WW r A) (Set.Icc r x) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc r x)
      (f' := fun y => (1 - r) * A * ff1 y - (1 + r) / (1 + y) ^ 2)
      (fun y hy => (hd_WW (by linarith [hy.1]) (by linarith [hy.2])).continuousAt.continuousWithinAt)
      (fun y hy => by
        rw [interior_Icc] at hy
        exact (hd_WW (by linarith [hy.1]) (by linarith [hy.2])).hasDerivWithinAt) ?_
    intro y hy
    rw [interior_Icc] at hy
    have hy0 : 0 < y := by linarith [hy.1]
    have hy1 : y < 1 := by linarith [hy.2]
    have hf : ff1 r ≤ ff1 y := ff1_mono ⟨hr0, hr1⟩ ⟨hy0, hy1⟩ hy.1.le
    have hq : (1 + r) / (1 + y) ^ 2 ≤ (1 + r) / (1 + r) ^ 2 :=
      div_le_div_of_nonneg_left (by linarith) (by positivity) (by nlinarith [hy.1])
    have hc : 0 ≤ (1 - r) * A := mul_nonneg (by linarith) hA.le
    have := mul_le_mul_of_nonneg_left hf hc
    linarith
  have hWr : WW r A r = 0 := by unfold WW; ring
  have hWx : 0 ≤ WW r A x := hWr ▸ hmono ⟨le_rfl, hrx⟩ ⟨hrx, le_rfl⟩ hrx
  rw [Dg_eq_W hg0 hg1'.ne hA]
  apply div_nonneg (mul_nonneg hg0.le hWx)
  have : 0 < 1 - g := by linarith
  positivity

/-- Case `1 < g ≤ 2 log 2`. -/
lemma Dg0_gt1 {g A : ℝ} (hg1' : 1 < g) (hgc : g ≤ cc) (hA : 0 < A) : 0 ≤ Dg g A 0 := by
  have hg0 : 0 < g := by linarith
  set r := Real.exp (-A) with hr
  set x := Real.exp (-(g * A)) with hx
  set xc := Real.exp (-(cc * A)) with hxc
  have hr0 : 0 < r := Real.exp_pos _
  have hr1 : r < 1 := by rw [hr, Real.exp_lt_one_iff]; linarith
  have hxc0 : 0 < xc := Real.exp_pos _
  have hxr : x ≤ r := by rw [hr, hx]; exact Real.exp_le_exp.2 (by nlinarith)
  have hxcx : xc ≤ x := by rw [hxc, hx]; exact Real.exp_le_exp.2 (by nlinarith)
  have hlogr : Real.log r = -A := by rw [hr, Real.log_exp]
  have hlogxc : Real.log xc = -(cc * A) := by rw [hxc, Real.log_exp]
  -- convexity of W on (0,1)
  have hconv : ConvexOn ℝ (Set.Ioo 0 1) (WW r A) := by
    refine convexOn_of_hasDerivWithinAt2_nonneg (convex_Ioo 0 1)
      (f' := fun y => (1 - r) * A * ff1 y - (1 + r) / (1 + y) ^ 2)
      (f'' := fun y => (1 - r) * A * ff2 y + 2 * (1 + r) / (1 + y) ^ 3)
      (fun y hy => (hd_WW hy.1 hy.2).continuousAt.continuousWithinAt) ?_ ?_ ?_
    · intro y hy; rw [interior_Ioo] at hy; exact (hd_WW hy.1 hy.2).hasDerivWithinAt
    · intro y hy; rw [interior_Ioo] at hy; exact (hd_WW1 hy.1 hy.2).hasDerivWithinAt
    · intro y hy
      rw [interior_Ioo] at hy
      have := ff2_nonneg hy.1 hy.2
      have hc : 0 ≤ (1 - r) * A := mul_nonneg (by linarith) hA.le
      have : 0 ≤ 2 * (1 + r) / (1 + y) ^ 3 := by
        have : 0 < 1 + y := by linarith [hy.1]
        positivity
      have := mul_nonneg hc (ff2_nonneg hy.1 hy.2)
      linarith
  have hWr : WW r A r = 0 := by unfold WW; ring
  have hWxc : WW r A xc = -(1 - r) * Gs A := by
    have hcpos := cc_pos
    unfold WW ff Gs
    rw [hlogr, hlogxc, ← hr, ← hxc]
    have e1 : 1 + xc ≠ 0 := by positivity
    have e2 : 1 - r ≠ 0 := by linarith
    field_simp
    ring
  have hWxc' : WW r A xc ≤ 0 := by
    rw [hWxc]
    have := Gs_nonneg hA
    nlinarith
  -- x is a convex combination of xc and r
  have hWx : WW r A x ≤ 0 := by
    rcases eq_or_lt_of_le hxr with h | h
    · rw [h, hWr]
    have hlt : xc < r := lt_of_le_of_lt hxcx h
    set θ := (r - x) / (r - xc) with hθ
    have hθ0 : 0 ≤ θ := div_nonneg (by linarith) (by linarith)
    have hθ1 : θ ≤ 1 := by rw [hθ, div_le_one (by linarith)]; linarith
    have hne : r - xc ≠ 0 := sub_ne_zero.2 (ne_of_gt hlt)
    have hcomb : θ * xc + (1 - θ) * r = x := by rw [hθ]; field_simp; ring
    have := hconv.2 (show xc ∈ Set.Ioo 0 1 from ⟨hxc0, by linarith⟩)
      (show r ∈ Set.Ioo 0 1 from ⟨hr0, hr1⟩) hθ0 (by linarith : 0 ≤ 1 - θ) (by ring)
    simp only [smul_eq_mul] at this
    rw [hcomb, hWr] at this
    nlinarith
  rw [Dg_eq_W hg0 hg1'.ne' hA]
  apply div_nonneg_of_nonpos
  · exact mul_nonpos_of_nonneg_of_nonpos hg0.le hWx
  · have : 1 - g < 0 := by linarith
    have : 0 < 1 + r := by linarith
    nlinarith

/-- Lemmas R4 and R3 together: `Δ_g(A, B) ≥ 0` for `0 ≤ B ≤ A`. -/
theorem Dg_nonneg {g A B : ℝ} (hg0 : 0 < g) (hg1' : g ≠ 1) (hgc : g ≤ cc) (hB : 0 ≤ B)
    (hAB : B ≤ A) : 0 ≤ Dg g A B := by
  have H0 : ∀ A, 0 ≤ A → 0 ≤ Dg g A 0 := by
    intro A hA
    rcases eq_or_lt_of_le hA with h | h
    · subst h; unfold Dg; ring_nf; exact le_rfl
    rcases lt_or_gt_of_ne hg1' with hg | hg
    · exact Dg0_lt1 hg0 hg h
    · exact Dg0_gt1 hg hgc h
  exact Dg_nonneg_of hg0 hg1' hB hAB (H0 A (hB.trans hAB))

end FriedanR2

end
