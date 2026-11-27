module

public import Feige.Bernoulli.Claim32
public import Feige.Calculus.HDelta

/- Port (Palomar entry): `module` header, `public import`s and a public section added for the module system; otherwise unchanged from github.com/koolkao/feige-lean at commit 7da24abf1619706bf4f705bb24aa4d00bc63b49f. -/

@[expose] public section

/-!
# Theorem 2.1 of Ling, equal-bound case

If `0 ≤ pᵢ < 1`, `wᵢ ≥ 0` and `wᵢ pᵢ ≤ a` for one common `a > 0`, and `d = 1 - E[T] > 0`, then
`P(T < 1) ≥ min (d/(d+a)) e⁻¹`.

This is the specialization of Ling's Theorem 2.1 to `a₁ = ⋯ = aₙ = a`, combined with the real
form of Prop. 5.2: when `L ≤ a`, Claim 3.1 gives `P(T<1) ≥ d/(d+L) ≥ d/(d+a)`; when `L > a`,
Claim 3.2 gives `P(T<1) ≥ (1 - a/R)^{L/a} = (1 - 1/(x + D))^x` with `x = L/a ≥ 1`, `D = d/a`,
which is `≥ min (D/(1+D)) e⁻¹` by `min_le_rpow`.  Claims 3.3–3.4 are not needed here.
-/

open Finset Real

namespace Samuels

variable {ι : Type*} [DecidableEq ι]

theorem bernoulli_equal_bound (p w : ι → ℝ) (s : Finset ι) (hp0 : ∀ i ∈ s, 0 ≤ p i)
    (hp1 : ∀ i ∈ s, p i < 1) (hw : ∀ i ∈ s, 0 ≤ w i) {a : ℝ} (ha : 0 < a)
    (hwa : ∀ i ∈ s, w i * p i ≤ a) (hd : 0 < 1 - E p w s) :
    min ((1 - E p w s) / ((1 - E p w s) + a)) (exp (-1)) ≤ Z p w s 1 := by
  have hp1' : ∀ i ∈ s, p i ≤ 1 := fun i hi => (hp1 i hi).le
  set d := 1 - E p w s with hddef
  have hZ : 0 < Z p w s 1 := Z_pos hp0 hp1 hw one_pos
  have hZM : d ≤ Z p w s 1 - M p w s 1 := one_sub_E_le hp0 hp1'
  set R := Rv p w s with hRdef
  set L := Lv p w s with hLdef
  have hRL : R = d + L := by simp only [hRdef, hLdef, Rv, Lv, hddef]; ring
  have hZR : Z p w s 1 * R = Z p w s 1 - M p w s 1 := by
    simp only [hRdef, Rv]; field_simp
  have hRpos : 0 < R := by
    by_contra h; push Not at h
    have : Z p w s 1 * R ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hZ.le h
    linarith
  rcases le_or_gt L a with hLa | hLa
  · -- Claim 3.1: `P(T<1) ≥ d/R ≥ d/(d+a)`
    apply (min_le_left _ _).trans
    rw [div_le_iff₀ (by linarith)]
    have h1 : d ≤ Z p w s 1 * R := by linarith
    have h2 : Z p w s 1 * R ≤ Z p w s 1 * (d + a) :=
      mul_le_mul_of_nonneg_left (by linarith) hZ.le
    linarith
  · -- Claim 3.2
    have haR : a < R := by linarith
    obtain ⟨ℓ, -, hℓsum, hℓlog⟩ :=
      claim32 p w (fun _ => a) s hp0 hp1 hw hwa (fun _ _ => ha) (fun _ _ => haR)
    rw [← Finset.sum_mul, ← Finset.sum_div, hℓsum] at hℓlog
    -- `Z ≥ (1 - a/R)^(L/a)`
    have hbase : 0 < 1 - a / R := by rw [sub_pos, div_lt_one hRpos]; exact haR
    have hlog1 : log (R / (R - a)) = -log (1 - a / R) := by
      have : 1 - a / R = (R - a) / R := by field_simp
      rw [this, ← log_inv, inv_div]
    have hZge : (1 - a / R) ^ (L / a) ≤ Z p w s 1 := by
      rw [rpow_def_of_pos hbase, ← exp_log hZ]
      apply exp_le_exp.mpr
      rw [hlog1] at hℓlog
      linarith
    have hD : 0 < d / a := div_pos hd ha
    have hx : 1 ≤ L / a := by rw [le_div_iff₀ ha]; linarith
    have hmain := min_le_rpow hD hx
    have he1 : 1 - 1 / (L / a + d / a) = 1 - a / R := by
      rw [hRL]; field_simp; ring
    have he2 : d / a / (1 + d / a) = d / (d + a) := by field_simp; ring
    rw [he1, he2] at hmain
    exact hmain.trans hZge

end Samuels

end
