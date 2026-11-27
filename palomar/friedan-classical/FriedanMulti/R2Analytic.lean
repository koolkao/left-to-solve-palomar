/-
Copyright 2026 Ming-Chih Kao. Licensed under the Apache License, Version 2.0;
see the LICENSE file at the root of this repository.
-/
module

public import Mathlib

/-! Port: copied from `FriedanMulti/R2Analytic.lean` of github.com/koolkao/friedan-entropy-inequality (commit 0f4ba65dc126f59e7158fbcbc01548baa78cf21d, Lean v4.33.1, Mathlib 0df444a) and put into the module system (`module` header, `public import`, public section). No other change was needed for Lean v4.36.0 / Mathlib fc4f59e. -/

@[expose] public section

/-!
# One-variable lemmas for the binary Rényi case

* `ff y = log(1+y) / (-log y)` is convex on `(0,1)`: `ff2 ≥ 0` (`ff2_nonneg`).
* `kk r = (1 - r²) log(1+r) + r² log r ≥ 0` on `[0,1]`.
* `WW r x = (1-r)(-log r)(ff x - ff r) - (x - r)/(1+x)`: nondecreasing on `[r,1)` and convex on `(0,1)`.
-/

open Real

namespace FriedanR2

noncomputable def ff (y : ℝ) : ℝ := Real.log (1 + y) / -Real.log y
noncomputable def ff1 (y : ℝ) : ℝ := (-Real.log y / (1 + y) + Real.log (1 + y) / y) / (-Real.log y) ^ 2
noncomputable def NN (y : ℝ) : ℝ :=
  -(-Real.log y) ^ 2 * y ^ 2 - (-Real.log y) * Real.log (1 + y) * (1 + y) ^ 2
    + 2 * y * (1 + y) * (-Real.log y) + 2 * (1 + y) ^ 2 * Real.log (1 + y)
noncomputable def ff2 (y : ℝ) : ℝ := NN y / ((-Real.log y) ^ 3 * y ^ 2 * (1 + y) ^ 2)

lemma logpos {y : ℝ} (h0 : 0 < y) (h1 : y < 1) : 0 < -Real.log y := by
  have := Real.log_neg h0 h1; linarith

lemma hd_ff {y : ℝ} (h0 : 0 < y) (h1 : y < 1) : HasDerivAt ff (ff1 y) y := by
  have hL := (logpos h0 h1).ne'
  have hy : 1 + y ≠ 0 := by linarith
  have a1 : HasDerivAt (fun y => Real.log (1 + y)) (1 / (1 + y)) y :=
    ((hasDerivAt_id' y).const_add 1).log hy |>.congr_deriv (by ring)
  have a2 : HasDerivAt (fun y => -Real.log y) (-(1 / y)) y :=
    ((Real.hasDerivAt_log h0.ne').neg).congr_deriv (by ring)
  unfold ff ff1
  refine (a1.div a2 hL).congr_deriv ?_
  field_simp
  ring

lemma hd_ff1 {y : ℝ} (h0 : 0 < y) (h1 : y < 1) : HasDerivAt ff1 (ff2 y) y := by
  have hL := (logpos h0 h1).ne'
  have hy : 1 + y ≠ 0 := by linarith
  have hy0 := h0.ne'
  have a1 : HasDerivAt (fun y => Real.log (1 + y)) (1 / (1 + y)) y :=
    ((hasDerivAt_id' y).const_add 1).log hy |>.congr_deriv (by ring)
  have a2 : HasDerivAt (fun y => -Real.log y) (-(1 / y)) y :=
    ((Real.hasDerivAt_log h0.ne').neg).congr_deriv (by ring)
  have a3 : HasDerivAt (fun y => 1 + y) 1 y := (hasDerivAt_id' y).const_add 1
  have num := (a2.div a3 hy).add (a1.div (hasDerivAt_id' y) hy0)
  have den := a2.pow 2
  unfold ff1 ff2 NN
  refine (num.div den (pow_ne_zero 2 hL)).congr_deriv ?_
  simp only [Nat.cast_ofNat, Pi.add_apply, Pi.div_apply, Pi.pow_apply]
  have hl : Real.log y ≠ 0 := fun h => hL (by rw [h]; ring)
  field_simp
  ring

lemma NN_nonneg {y : ℝ} (h0 : 0 < y) (h1 : y < 1) : 0 ≤ NN y := by
  set L := -Real.log y with hLdef
  set M := Real.log (1 + y) with hMdef
  have hL0 : 0 < L := logpos h0 h1
  have hM0 : 0 < M := Real.log_pos (by linarith)
  have hMy : M ≤ y := by
    have := Real.log_le_sub_one_of_pos (show 0 < 1 + y by linarith); linarith
  -- L ≤ (1 - y)/y, i.e. y L ≤ 1 - y
  have hLu : y * L ≤ 1 - y := by
    have := Real.one_sub_inv_le_log_of_pos h0
    have : 1 - 1 / y ≤ Real.log y := by simpa [one_div] using this
    have e : y * (1 - 1 / y) = y - 1 := by field_simp
    nlinarith
  -- N = γ + L (β - y² L)
  obtain ⟨β, hβ⟩ : ∃ β, β = 2 * y * (1 + y) - M * (1 + y) ^ 2 := ⟨_, rfl⟩
  obtain ⟨γ, hγd⟩ : ∃ γ, γ = 2 * (1 + y) ^ 2 * M := ⟨_, rfl⟩
  have hN : NN y = γ + L * (β - y ^ 2 * L) := by
    unfold NN; rw [← hLdef, ← hMdef, hβ, hγd]; ring
  rw [hN]
  have hγ : 0 ≤ γ := by rw [hγd]; positivity
  -- y times the value at the upper bound Lu = (1-y)/y
  have hNu : 0 ≤ y * γ + (1 - y) * (β - y * (1 - y)) := by
    have : y * γ + (1 - y) * (β - y * (1 - y)) =
        y * ((1 - y) * (1 + 3 * y)) + M * (1 + y) ^ 2 * (3 * y - 1) := by rw [hβ, hγd]; ring
    rw [this]
    by_cases h3 : 1 / 3 ≤ y
    · have : 0 ≤ M * (1 + y) ^ 2 * (3 * y - 1) := by
        apply mul_nonneg (mul_nonneg hM0.le (sq_nonneg _)); linarith
      have : 0 ≤ (1 - y) * (1 + 3 * y) := mul_nonneg (by linarith) (by linarith)
      positivity
    · push Not at h3
      have hneg : M * (1 + y) ^ 2 * (3 * y - 1) ≥ y * (1 + y) ^ 2 * (3 * y - 1) := by
        have := mul_le_mul_of_nonneg_right hMy (sq_nonneg (1 + y))
        nlinarith
      have : y * ((1 - y) * (1 + 3 * y)) + y * (1 + y) ^ 2 * (3 * y - 1) =
          y * (3 * y + 2 * y ^ 2 + 3 * y ^ 3) := by ring
      have : 0 ≤ y * (3 * y + 2 * y ^ 2 + 3 * y ^ 3) := by positivity
      linarith
  by_cases hb : 0 ≤ β - y ^ 2 * L
  · exact add_nonneg hγ (mul_nonneg hL0.le hb)
  · push Not at hb
    have h1' : y ^ 2 * L ≤ y * (1 - y) := by nlinarith
    have h2' : L * (β - y ^ 2 * L) ≥ L * (β - y * (1 - y)) := by nlinarith
    have hb' : β - y * (1 - y) < 0 := by linarith
    have hLle : L ≤ (1 - y) / y := by rw [le_div_iff₀ h0]; linarith
    have h3' : L * (β - y * (1 - y)) ≥ (1 - y) / y * (β - y * (1 - y)) := by nlinarith
    have h4' : 0 ≤ γ + (1 - y) / y * (β - y * (1 - y)) := by
      have e : γ + (1 - y) / y * (β - y * (1 - y)) =
          (y * γ + (1 - y) * (β - y * (1 - y))) / y := by field_simp
      rw [e]; positivity
    linarith

lemma ff2_nonneg {y : ℝ} (h0 : 0 < y) (h1 : y < 1) : 0 ≤ ff2 y := by
  unfold ff2
  have := logpos h0 h1
  exact div_nonneg (NN_nonneg h0 h1) (by positivity)

lemma ff1_mono : MonotoneOn ff1 (Set.Ioo 0 1) := by
  refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ioo 0 1) (f' := ff2)
    (fun y hy => (hd_ff1 hy.1 hy.2).continuousAt.continuousWithinAt)
    (fun y hy => by
      rw [interior_Ioo] at hy; exact (hd_ff1 hy.1 hy.2).hasDerivWithinAt)
    (fun y hy => by rw [interior_Ioo] at hy; exact ff2_nonneg hy.1 hy.2)

/-! ### `kk ≥ 0` -/

noncomputable def kk (r : ℝ) : ℝ := (1 - r ^ 2) * Real.log (1 + r) + r ^ 2 * Real.log r

lemma kk_nonneg {r : ℝ} (h0 : 0 ≤ r) (h1 : r ≤ 1) : 0 ≤ kk r := by
  have hk1 : ∀ t, 0 < t → HasDerivAt kk (1 - 2 * t * (Real.log (1 + t) - Real.log t)) t := by
    intro t ht
    have hy : 1 + t ≠ 0 := by linarith
    have a1 : HasDerivAt (fun y => Real.log (1 + y)) (1 / (1 + t)) t :=
      ((hasDerivAt_id' t).const_add 1).log hy |>.congr_deriv (by ring)
    unfold kk
    refine ((((hasDerivAt_pow 2 t).const_sub 1).mul a1).add
      ((hasDerivAt_pow 2 t).mul (Real.hasDerivAt_log ht.ne'))).congr_deriv ?_
    simp only [Nat.cast_ofNat]
    field_simp
    ring
  have hk2 : ∀ t, 0 < t → HasDerivAt (fun t => 1 - 2 * t * (Real.log (1 + t) - Real.log t))
      (-2 * (Real.log (1 + t) - Real.log t) + 2 / (1 + t)) t := by
    intro t ht
    have hy : 1 + t ≠ 0 := by linarith
    have a1 : HasDerivAt (fun y => Real.log (1 + y)) (1 / (1 + t)) t :=
      ((hasDerivAt_id' t).const_add 1).log hy |>.congr_deriv (by ring)
    refine ((((hasDerivAt_id' t).const_mul 2).mul (a1.sub (Real.hasDerivAt_log ht.ne'))).const_sub 1)
      |>.congr_deriv ?_
    simp only [Pi.sub_apply]
    field_simp
    ring
  have hcont : ContinuousOn kk (Set.Icc 0 1) := by
    have e : kk = fun r : ℝ => (1 - r ^ 2) * Real.log (1 + r) + r * (r * Real.log r) := by
      funext r; unfold kk; ring
    rw [e]
    intro r hr
    apply ContinuousAt.continuousWithinAt
    have hr0 : 1 + r ≠ 0 := by linarith [hr.1]
    exact ((continuousAt_const.sub (continuousAt_id.pow 2)).mul
      ((continuousAt_const.add continuousAt_id).log hr0)).add
      (continuous_id.mul Real.continuous_mul_log).continuousAt
  have hconc : ConcaveOn ℝ (Set.Icc 0 1) kk := by
    refine concaveOn_of_hasDerivWithinAt2_nonpos (convex_Icc 0 1) hcont
      (f' := fun t => 1 - 2 * t * (Real.log (1 + t) - Real.log t))
      (f'' := fun t => -2 * (Real.log (1 + t) - Real.log t) + 2 / (1 + t)) ?_ ?_ ?_
    · intro t ht; rw [interior_Icc] at ht; exact (hk1 t ht.1).hasDerivWithinAt
    · intro t ht; rw [interior_Icc] at ht; exact (hk2 t ht.1).hasDerivWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      have ht0 := ht.1
      have hq : 0 < (1 + t) / t := by positivity
      have h := Real.one_sub_inv_le_log_of_pos hq
      rw [Real.log_div (by linarith) ht0.ne', inv_div] at h
      have e : 1 - t / (1 + t) = 1 / (1 + t) := by field_simp; ring
      rw [e] at h
      have e2 : 2 / (1 + t) = 2 * (1 / (1 + t)) := by ring
      rw [e2]
      linarith
  have k0 : kk 0 = 0 := by simp [kk]
  have k1 : kk 1 = 0 := by simp [kk]
  have := hconc.2 (show (0:ℝ) ∈ Set.Icc 0 1 from ⟨le_rfl, zero_le_one⟩)
    (show (1:ℝ) ∈ Set.Icc 0 1 from ⟨zero_le_one, le_rfl⟩) (show 0 ≤ 1 - r by linarith) h0
    (by ring)
  simp only [smul_eq_mul, mul_zero, zero_add, mul_one, k0, k1] at this
  linarith

end FriedanR2

end
