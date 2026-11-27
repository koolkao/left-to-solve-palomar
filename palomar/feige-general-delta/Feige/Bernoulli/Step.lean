module

public import Mathlib

/- Port (Palomar entry): `module` header, `public import`s and a public section added for the module system; otherwise unchanged from github.com/koolkao/feige-lean at commit 7da24abf1619706bf4f705bb24aa4d00bc63b49f. -/

@[expose] public section

/-!
# The real-number core of one step of Ling's Claim 3.2

With `Z₀ = P(T₋ᵢ < 1)`, `Z₁ = P(T₋ᵢ < 1 - wᵢ)`, `M₀, M₁` the corresponding truncated first
moments, and `m = E[T | T < 1]`, the facts supplied by the finite-sum layer are
* `Z = (1-p) Z₀ + p Z₁`, `m Z = (1-p) M₀ + p (M₁ + w Z₁)`,
* `(1 - w)(Z₀ - Z₁) ≤ M₀ - M₁` (on `{1-w ≤ T₋ᵢ < 1}` we have `T₋ᵢ ≥ 1 - w`),
* `M₀ ≤ m Z₀` (the choice of `i`, i.e. `R₋ᵢ ≥ R`).
From these: `Δ = w p - (m - M₀/Z₀) ∈ [0, a]` and
`-log Z ≤ -log Z₀ + (Δ / a) log (R / (R - a))` with `R = 1 - m`.
-/

open Real

namespace Samuels

/-- Chord bound for the convex function `-log (1 - x)` vanishing at `0`. -/
lemma neg_log_one_sub_le {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) (hy1 : y < 1) (hy0 : 0 < y) :
    -log (1 - x) ≤ x / y * (-log (1 - y)) := by
  have hc := strictConcaveOn_log_Ioi.concaveOn
  have h1 : (1 : ℝ) ∈ Set.Ioi 0 := by norm_num
  have h2 : 1 - y ∈ Set.Ioi (0 : ℝ) := by simp; linarith
  have ht0 : 0 ≤ x / y := div_nonneg hx hy0.le
  have ht1 : x / y ≤ 1 := (div_le_one hy0).mpr hxy
  have := hc.2 h1 h2 (sub_nonneg.mpr ht1) ht0 (by ring)
  simp only [smul_eq_mul, log_one, mul_zero, zero_add] at this
  have harg : (1 - x / y) * 1 + x / y * (1 - y) = 1 - x := by
    field_simp; ring
  rw [harg] at this
  linarith

/-- One step of Claim 3.2, in pure real arithmetic. -/
theorem claim32_step {p w a Z0 Z1 M0 M1 m : ℝ}
    (hZ0 : 0 < Z0) (hZ1 : 0 ≤ Z1) (hZ10 : Z1 ≤ Z0) (hp0 : 0 ≤ p) (hp1 : p < 1)
    (hM : (1 - w) * (Z0 - Z1) ≤ M0 - M1)
    (hmZ : m * ((1 - p) * Z0 + p * Z1) = (1 - p) * M0 + p * (M1 + w * Z1))
    (hm0 : M0 ≤ m * Z0) (hwa : w * p ≤ a) (ha : 0 < a) (haR : a < 1 - m) :
    0 ≤ w * p - (m - M0 / Z0) ∧ w * p - (m - M0 / Z0) ≤ a ∧
      -log ((1 - p) * Z0 + p * Z1) ≤
        -log Z0 + (w * p - (m - M0 / Z0)) / a * log ((1 - m) / ((1 - m) - a)) := by
  set Δ := w * p - (m - M0 / Z0) with hΔ
  set R := 1 - m with hR
  have hRpos : 0 < R := by linarith
  set ρ := p * (Z0 - Z1) / Z0 with hρ
  have hρ0 : 0 ≤ ρ := div_nonneg (mul_nonneg hp0 (sub_nonneg.mpr hZ10)) hZ0.le
  have hZρ : (1 - p) * Z0 + p * Z1 = Z0 * (1 - ρ) := by
    rw [hρ]; field_simp; ring
  have hm0' : M0 / Z0 ≤ m := (div_le_iff₀ hZ0).mpr hm0
  -- `Z₀ Δ = p ((M₀ - M₁) + (w - m)(Z₀ - Z₁))`
  have hkey : Z0 * Δ = p * ((M0 - M1) + (w - m) * (Z0 - Z1)) := by
    rw [hΔ, mul_sub, mul_sub, mul_div_cancel₀ _ hZ0.ne']
    linear_combination -hmZ
  have hρR : ρ * R ≤ Δ := by
    have h1 : p * ((1 - w) * (Z0 - Z1) + (w - m) * (Z0 - Z1)) ≤
        p * ((M0 - M1) + (w - m) * (Z0 - Z1)) :=
      mul_le_mul_of_nonneg_left (by linarith) hp0
    rw [← hkey] at h1
    have h2 : ρ * R * Z0 = p * ((1 - w) * (Z0 - Z1) + (w - m) * (Z0 - Z1)) := by
      rw [hρ, hR]; field_simp; ring
    have h3 : ρ * R * Z0 ≤ Δ * Z0 := by rw [h2]; linarith
    exact le_of_mul_le_mul_right h3 hZ0
  have hΔ0 : 0 ≤ Δ := le_trans (mul_nonneg hρ0 hRpos.le) hρR
  have hΔa : Δ ≤ a := by rw [hΔ]; linarith
  refine ⟨hΔ0, hΔa, ?_⟩
  -- the logarithmic estimate
  have hy0 : 0 < a / R := div_pos ha hRpos
  have hy1 : a / R < 1 := (div_lt_one hRpos).mpr haR
  have hρy : ρ ≤ a / R := by
    rw [le_div_iff₀ hRpos]; linarith
  have hρ1 : ρ < 1 := lt_of_le_of_lt hρy hy1
  have hchord := neg_log_one_sub_le hρ0 hρy hy1 hy0
  have hlogR : -log (1 - a / R) = log (R / (R - a)) := by
    have : 1 - a / R = (R - a) / R := by field_simp
    rw [this, ← log_inv, inv_div]
  rw [hlogR] at hchord
  have hlogpos : 0 ≤ log (R / (R - a)) := by
    apply log_nonneg
    rw [le_div_iff₀ (by linarith)]; linarith
  have hcoef : ρ / (a / R) ≤ Δ / a := by
    rw [div_div_eq_mul_div, div_le_div_iff_of_pos_right ha]; linarith
  have hb : ρ / (a / R) * log (R / (R - a)) ≤ Δ / a * log (R / (R - a)) :=
    mul_le_mul_of_nonneg_right hcoef hlogpos
  rw [hZρ, log_mul hZ0.ne' (by linarith)]
  linarith

end Samuels

end
