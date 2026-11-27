/-
Copyright 2026 Ming-Chih Kao. Licensed under the Apache License, Version 2.0;
see the LICENSE file at the root of this repository.
-/
module

public import FriedanEntropy.Proof

/-! Port: copied from `FriedanMulti/R2Basic.lean` of github.com/koolkao/friedan-entropy-inequality (commit 0f4ba65dc126f59e7158fbcbc01548baa78cf21d, Lean v4.33.1, Mathlib 0df444a) and put into the module system (`module` header, `public import`, public section). No other change was needed for Lean v4.36.0 / Mathlib fc4f59e. -/

@[expose] public section

/-!
# Binary Rényi entropy in logit coordinates

`hg g t = (lp (g t) - g lp t) / (1 - g)` is the Rényi entropy of order `g` of `(sg t, 1 - sg t)`.
`Dg g A B = h'(A) - h'(B) + 2 h(A) (l'(A) - l'(B))`. Lemma R3 of MULTI.md §5.2 (`Dg_nonneg_of`): for `0 ≤ B ≤ A`,
`Dg g A B ≥ 0` follows from `Dg g A 0 ≥ 0`. `Omg` (`= e^{2 l} h`) is monotone on `[0, ∞)` given
`Dg g · 0 ≥ 0`.
-/

open Real Friedan

namespace FriedanR2

noncomputable def hg (g t : ℝ) : ℝ := (lp (g * t) - g * lp t) / (1 - g)
noncomputable def hg1 (g t : ℝ) : ℝ := g * (sg (g * t) - sg t) / (1 - g)
noncomputable def sd (t : ℝ) : ℝ := sg t * (1 - sg t)
noncomputable def hg2 (g t : ℝ) : ℝ := g * (g * sd (g * t) - sd t) / (1 - g)
noncomputable def Dg (g A B : ℝ) : ℝ := hg1 g A - hg1 g B + 2 * hg g A * (sg A - sg B)
noncomputable def Omg (g t : ℝ) : ℝ := Real.exp (2 * lp t) * hg g t

lemma sd_pos (t : ℝ) : 0 < sd t := mul_pos (sg_pos t) (sub_pos.2 (sg_lt_one t))

lemma hd_sd (t : ℝ) : HasDerivAt sd (sd t * (1 - 2 * sg t)) t := by
  unfold sd
  exact ((hasDerivAt_sg t).mul ((hasDerivAt_sg t).const_sub 1)).congr_deriv (by ring)

lemma hd_comp {f : ℝ → ℝ} {f' : ℝ} (g t : ℝ) (h : HasDerivAt f f' (g * t)) :
    HasDerivAt (fun t => f (g * t)) (g * f') t :=
  (h.comp t ((hasDerivAt_id' t).const_mul g)).congr_deriv (by ring)

lemma hd_hg (g t : ℝ) : HasDerivAt (hg g) (hg1 g t) t := by
  unfold hg hg1
  exact (((hd_comp g t (hasDerivAt_lp (g * t))).sub ((hasDerivAt_lp t).const_mul g)).div_const
    (1 - g)).congr_deriv (by ring)

lemma hd_hg1 (g t : ℝ) : HasDerivAt (hg1 g) (hg2 g t) t := by
  unfold hg1 hg2
  exact ((((hd_comp g t (hasDerivAt_sg (g * t))).sub (hasDerivAt_sg t)).const_mul g).div_const
    (1 - g)).congr_deriv (by unfold sd; ring)

lemma hd_hg2 (g t : ℝ) :
    HasDerivAt (hg2 g) (g * (g * (g * (sd (g * t) * (1 - 2 * sg (g * t))))
      - sd t * (1 - 2 * sg t)) / (1 - g)) t := by
  unfold hg2
  exact (((((hd_comp g t (hd_sd (g * t))).const_mul g).sub (hd_sd t)).const_mul g).div_const
    (1 - g)).congr_deriv (by ring)

lemma hg_neg (g t : ℝ) : hg g (-t) = hg g t := by
  unfold hg; rw [show g * -t = -(g * t) by ring, lp_neg, lp_neg]

lemma hg_abs (g t : ℝ) : hg g |t| = hg g t := by
  rcases abs_choice t with h | h <;> rw [h]
  exact hg_neg g t

lemma hg1_zero (g : ℝ) : hg1 g 0 = 0 := by unfold hg1; simp

/-- The sign condition `(τ(t) - g τ(gt)) / (1 - g) ≥ 0` with `τ = 2 sg - 1`, for `t ≥ 0`. -/
lemma tau_sign {g t : ℝ} (hg0 : 0 < g) (hg1' : g ≠ 1) (ht : 0 ≤ t) :
    0 ≤ ((2 * sg t - 1) - g * (2 * sg (g * t) - 1)) / (1 - g) := by
  have hgt : 0 ≤ g * t := mul_nonneg hg0.le ht
  have h1 := sg_ge_half hgt
  rcases lt_or_gt_of_ne hg1' with h | h
  · have hle : g * t ≤ t := by nlinarith
    have := sg_mono hle
    apply div_nonneg _ (by linarith)
    nlinarith
  · have hle : t ≤ g * t := by nlinarith
    have := sg_mono hle
    apply div_nonneg_of_nonpos _ (by linarith)
    nlinarith

lemma hg1_nonpos {g t : ℝ} (hg0 : 0 < g) (hg1' : g ≠ 1) (ht : 0 ≤ t) : hg1 g t ≤ 0 := by
  unfold hg1
  rcases lt_or_gt_of_ne hg1' with h | h
  · have := sg_mono (show g * t ≤ t by nlinarith)
    exact div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos hg0.le (by linarith))
      (by linarith)
  · have := sg_mono (show t ≤ g * t by nlinarith)
    exact div_nonpos_of_nonneg_of_nonpos (mul_nonneg hg0.le (by linarith)) (by linarith)

lemma hg_anti {g : ℝ} (hg0 : 0 < g) (hg1' : g ≠ 1) : AntitoneOn (hg g) (Set.Ici 0) := by
  refine antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici 0) (f' := hg1 g)
    (fun t _ => (hd_hg g t).continuousAt.continuousWithinAt)
    (fun t _ => (hd_hg g t).hasDerivWithinAt) ?_
  intro t ht
  rw [interior_Ici] at ht
  exact hg1_nonpos hg0 hg1' (le_of_lt ht)

/-! ### Lemma R3 (MULTI.md §5.2) -/

noncomputable def rho (g t : ℝ) : ℝ := -hg2 g t / sd t

lemma rho_anti {g : ℝ} (hg0 : 0 < g) (hg1' : g ≠ 1) : AntitoneOn (rho g) (Set.Ici 0) := by
  have hden : (1 - g) ≠ 0 := sub_ne_zero.2 (Ne.symm hg1')
  have hd : ∀ t, HasDerivAt (rho g)
      (-(g ^ 2) * (sd (g * t) / sd t) * (((2 * sg t - 1) - g * (2 * sg (g * t) - 1)) / (1 - g))) t := by
    intro t
    have hs := (sd_pos t).ne'
    unfold rho
    refine ((hd_hg2 g t).neg.div (hd_sd t) hs).congr_deriv ?_
    simp only [Pi.neg_apply]
    unfold hg2
    field_simp
    ring
  refine antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici 0) (f' := fun t =>
      -(g ^ 2) * (sd (g * t) / sd t) * (((2 * sg t - 1) - g * (2 * sg (g * t) - 1)) / (1 - g)))
    (fun t _ => (hd t).continuousAt.continuousWithinAt)
    (fun t _ => (hd t).hasDerivWithinAt) ?_
  intro t ht
  rw [interior_Ici] at ht
  have h1 := tau_sign hg0 hg1' (le_of_lt ht)
  have h2 : 0 ≤ sd (g * t) / sd t := div_nonneg (sd_pos _).le (sd_pos _).le
  have h3 : 0 ≤ g ^ 2 := sq_nonneg g
  have := mul_nonneg (mul_nonneg h3 h2) h1
  linarith [show -(g ^ 2) * (sd (g * t) / sd t) * (((2 * sg t - 1) - g * (2 * sg (g * t) - 1)) / (1 - g))
    = -(g ^ 2 * (sd (g * t) / sd t) * (((2 * sg t - 1) - g * (2 * sg (g * t) - 1)) / (1 - g))) by ring]

lemma hd_Dg (g A B : ℝ) :
    HasDerivAt (fun B => Dg g A B) (-hg2 g B - 2 * hg g A * sd B) B := by
  unfold Dg
  exact (((hasDerivAt_const B (hg1 g A)).sub (hd_hg1 g B)).add
    (((hasDerivAt_sg B).const_sub (sg A)).const_mul (2 * hg g A))).congr_deriv (by unfold sd; ring)

/-- Lemma R3: `Δ(A, B) ≥ 0` for `0 ≤ B ≤ A` once `Δ(A, 0) ≥ 0`. -/
lemma Dg_nonneg_of {g A B : ℝ} (hg0 : 0 < g) (hg1' : g ≠ 1) (hB : 0 ≤ B) (hAB : B ≤ A)
    (H0 : 0 ≤ Dg g A 0) : 0 ≤ Dg g A B := by
  have hra := rho_anti hg0 hg1'
  have hcont : ∀ s : Set ℝ, ContinuousOn (fun b => Dg g A b) s :=
    fun s b _ => (hd_Dg g A b).continuousAt.continuousWithinAt
  have hsign : ∀ b, -hg2 g b - 2 * hg g A * sd b = sd b * (rho g b - 2 * hg g A) := by
    intro b; unfold rho; field_simp [(sd_pos b).ne']
  by_cases hc : 2 * hg g A ≤ rho g B
  · have hmono : MonotoneOn (fun b => Dg g A b) (Set.Icc 0 B) := by
      refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 B)
        (f' := fun b => -hg2 g b - 2 * hg g A * sd b) (hcont _)
        (fun b _ => (hd_Dg g A b).hasDerivWithinAt) ?_
      intro b hb
      rw [interior_Icc] at hb
      rw [hsign]
      have : rho g B ≤ rho g b := hra (le_of_lt hb.1) hB hb.2.le
      exact mul_nonneg (sd_pos b).le (by linarith)
    exact H0.trans (hmono ⟨le_rfl, hB⟩ ⟨hB, le_rfl⟩ hB)
  · push Not at hc
    have hanti : AntitoneOn (fun b => Dg g A b) (Set.Icc B A) := by
      refine antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc B A)
        (f' := fun b => -hg2 g b - 2 * hg g A * sd b) (hcont _)
        (fun b _ => (hd_Dg g A b).hasDerivWithinAt) ?_
      intro b hb
      rw [interior_Icc] at hb
      rw [hsign]
      have : rho g b ≤ rho g B := hra hB (show (0:ℝ) ≤ b by linarith [hb.1]) hb.1.le
      exact mul_nonpos_of_nonneg_of_nonpos (sd_pos b).le (by linarith)
    have hAA : Dg g A A = 0 := by unfold Dg; ring
    have := hanti ⟨le_rfl, hAB⟩ ⟨hAB, le_rfl⟩ hAB
    simp only at this
    linarith

lemma hd_Omg (g t : ℝ) : HasDerivAt (Omg g) (Real.exp (2 * lp t) * Dg g t 0) t := by
  have e1 : HasDerivAt (fun t => Real.exp (2 * lp t)) (Real.exp (2 * lp t) * (2 * (sg t - 1 / 2))) t :=
    ((hasDerivAt_lp t).const_mul 2).exp
  refine (e1.mul (hd_hg g t)).congr_deriv ?_
  unfold Dg
  rw [hg1_zero, sg_zero]
  ring

lemma Omg_mono {g : ℝ} (H : ∀ A, 0 ≤ A → 0 ≤ Dg g A 0) : MonotoneOn (Omg g) (Set.Ici 0) := by
  refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0)
    (f' := fun t => Real.exp (2 * lp t) * Dg g t 0)
    (fun t _ => (hd_Omg g t).continuousAt.continuousWithinAt)
    (fun t _ => (hd_Omg g t).hasDerivWithinAt) ?_
  intro t ht
  rw [interior_Ici] at ht
  exact mul_nonneg (Real.exp_pos _).le (H t (le_of_lt ht))

lemma Omg_abs (g t : ℝ) : Omg g |t| = Omg g t := by
  unfold Omg; rw [lp_abs, hg_abs]

end FriedanR2

end
