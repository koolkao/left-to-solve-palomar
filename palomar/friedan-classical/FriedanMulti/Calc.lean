/-
Copyright 2026 Ming-Chih Kao. Licensed under the Apache License, Version 2.0;
see the LICENSE file at the root of this repository.
-/
module

public import Mathlib

/-! Port: copied from `FriedanMulti/Calc.lean` of github.com/koolkao/friedan-entropy-inequality (commit 0f4ba65dc126f59e7158fbcbc01548baa78cf21d, Lean v4.33.1, Mathlib 0df444a) and put into the module system (`module` header, `public import`, public section). No other change was needed for Lean v4.36.0 / Mathlib fc4f59e. -/

@[expose] public section

/-!
# Log coordinates and the index lemma

`gg x = S² log S - S T` with `S = ∑ exp xᵢ`, `T = ∑ xᵢ exp xᵢ` (so `gg (log z) = K² H(z/K)`).
`QQ x y` is the second derivative of `r ↦ gg (x + r y)` at `r = 0`.

Index lemma (`index`): for all `x, y₁, y₂` there is `(σ, τ) ≠ 0` with `QQ x (σ y₁ + τ y₂) ≥ 0`,
i.e. the Hessian of `gg` is negative definite on no 2-dimensional subspace.
-/

open Real Finset

namespace FriedanMulti

variable {n : ℕ}

noncomputable def Sx (x : Fin n → ℝ) : ℝ := ∑ i, exp (x i)
noncomputable def Tx (x : Fin n → ℝ) : ℝ := ∑ i, x i * exp (x i)
noncomputable def gg (x : Fin n → ℝ) : ℝ := Sx x ^ 2 * Real.log (Sx x) - Sx x * Tx x
noncomputable def S1 (x y : Fin n → ℝ) : ℝ := ∑ i, y i * exp (x i)
noncomputable def S2 (x y : Fin n → ℝ) : ℝ := ∑ i, y i ^ 2 * exp (x i)
noncomputable def T1 (x y : Fin n → ℝ) : ℝ := ∑ i, y i * (1 + x i) * exp (x i)
noncomputable def T2 (x y : Fin n → ℝ) : ℝ := ∑ i, y i ^ 2 * (2 + x i) * exp (x i)
noncomputable def g1 (x y : Fin n → ℝ) : ℝ :=
  2 * Sx x * S1 x y * Real.log (Sx x) + Sx x * S1 x y - S1 x y * Tx x - Sx x * T1 x y
noncomputable def QQ (x y : Fin n → ℝ) : ℝ :=
  (2 * Real.log (Sx x) + 3) * S1 x y ^ 2 + S2 x y * (2 * Sx x * Real.log (Sx x) + Sx x - Tx x)
    - 2 * S1 x y * T1 x y - Sx x * T2 x y

/-- The line `r ↦ x + r y`. -/
def ln (x y : Fin n → ℝ) (r : ℝ) : Fin n → ℝ := fun i => x i + r * y i

lemma ln_zero (x y : Fin n → ℝ) : ln x y 0 = x := by funext i; simp [ln]

lemma Sx_pos [NeZero n] (x : Fin n → ℝ) : 0 < Sx x :=
  Finset.sum_pos (fun _ _ => exp_pos _) Finset.univ_nonempty

/-! ### Derivatives along a line -/

lemma hd_exp (x y : Fin n → ℝ) (i : Fin n) (r : ℝ) :
    HasDerivAt (fun r => exp (x i + r * y i)) (y i * exp (x i + r * y i)) r :=
  (((hasDerivAt_id' r).mul_const (y i)).const_add (x i)).exp.congr_deriv (by ring)

lemma hd_Sx (x y : Fin n → ℝ) (r : ℝ) :
    HasDerivAt (fun r => Sx (ln x y r)) (S1 (ln x y r) y) r := by
  unfold Sx S1 ln
  exact HasDerivAt.fun_sum (fun i _ => hd_exp x y i r)

lemma hd_Tx (x y : Fin n → ℝ) (r : ℝ) :
    HasDerivAt (fun r => Tx (ln x y r)) (T1 (ln x y r) y) r := by
  unfold Tx T1 ln
  refine HasDerivAt.fun_sum (fun i _ => ?_)
  have h1 : HasDerivAt (fun r => x i + r * y i) (y i) r :=
    (((hasDerivAt_id' r).mul_const (y i)).const_add (x i)).congr_deriv (by ring)
  exact (h1.mul (hd_exp x y i r)).congr_deriv (by ring)

lemma hd_S1 (x y : Fin n → ℝ) (r : ℝ) :
    HasDerivAt (fun r => S1 (ln x y r) y) (S2 (ln x y r) y) r := by
  unfold S1 S2 ln
  exact HasDerivAt.fun_sum (fun i _ => ((hd_exp x y i r).const_mul (y i)).congr_deriv (by ring))

lemma hd_T1 (x y : Fin n → ℝ) (r : ℝ) :
    HasDerivAt (fun r => T1 (ln x y r) y) (T2 (ln x y r) y) r := by
  unfold T1 T2 ln
  refine HasDerivAt.fun_sum (fun i _ => ?_)
  have h1 : HasDerivAt (fun r => y i * (1 + (x i + r * y i))) (y i * y i) r :=
    ((((hasDerivAt_id' r).mul_const (y i)).const_add (x i)).const_add 1).const_mul (y i)
      |>.congr_deriv (by ring)
  exact (h1.mul (hd_exp x y i r)).congr_deriv (by ring)

lemma hd_gg [NeZero n] (x y : Fin n → ℝ) (r : ℝ) :
    HasDerivAt (fun r => gg (ln x y r)) (g1 (ln x y r) y) r := by
  have hS := hd_Sx x y r
  have hT := hd_Tx x y r
  have hne : Sx (ln x y r) ≠ 0 := (Sx_pos _).ne'
  have h := ((hS.pow 2).mul (hS.log hne)).sub (hS.mul hT)
  unfold gg g1
  refine h.congr_deriv ?_
  simp only [Pi.pow_apply]
  field_simp
  ring

lemma hd_g1 [NeZero n] (x y : Fin n → ℝ) (r : ℝ) :
    HasDerivAt (fun r => g1 (ln x y r) y) (QQ (ln x y r) y) r := by
  have hS := hd_Sx x y r
  have hT := hd_Tx x y r
  have h1 := hd_S1 x y r
  have hT1 := hd_T1 x y r
  have hne : Sx (ln x y r) ≠ 0 := (Sx_pos _).ne'
  have h := ((((hS.const_mul 2).mul h1).mul (hS.log hne)).add (hS.mul h1)).sub (h1.mul hT)
    |>.sub (hS.mul hT1)
  unfold g1 QQ
  refine h.congr_deriv ?_
  simp only [Pi.mul_apply]
  field_simp
  ring

lemma cont_QQ [NeZero n] (x y : Fin n → ℝ) : Continuous (fun r => QQ (ln x y r) y) := by
  have cS : Continuous (fun r => Sx (ln x y r)) := by
    unfold Sx ln; exact continuous_finsetSum _ (fun i _ => by fun_prop)
  have cT : Continuous (fun r => Tx (ln x y r)) := by
    unfold Tx ln; exact continuous_finsetSum _ (fun i _ => by fun_prop)
  have c1 : Continuous (fun r => S1 (ln x y r) y) := by
    unfold S1 ln; exact continuous_finsetSum _ (fun i _ => by fun_prop)
  have c2 : Continuous (fun r => S2 (ln x y r) y) := by
    unfold S2 ln; exact continuous_finsetSum _ (fun i _ => by fun_prop)
  have c3 : Continuous (fun r => T1 (ln x y r) y) := by
    unfold T1 ln; exact continuous_finsetSum _ (fun i _ => by fun_prop)
  have c4 : Continuous (fun r => T2 (ln x y r) y) := by
    unfold T2 ln; exact continuous_finsetSum _ (fun i _ => by fun_prop)
  have cL : Continuous (fun r => Real.log (Sx (ln x y r))) :=
    cS.log (fun r => (Sx_pos _).ne')
  unfold QQ
  fun_prop

/-! ### The quadratic form in normalized coordinates -/

/-- Entropy of `P = exp x / S`. -/
noncomputable def Hx (x : Fin n → ℝ) : ℝ := Real.log (Sx x) - Tx x / Sx x

/-- `d i = H + log(1/Pᵢ) - 1`. -/
noncomputable def dd (x : Fin n → ℝ) (i : Fin n) : ℝ := Hx x + (Real.log (Sx x) - x i) - 1

lemma QQ_eq [NeZero n] (x y : Fin n → ℝ) :
    QQ x y = Sx x * ∑ i, exp (x i) * dd x i * (y i + S1 x y / Sx x) ^ 2
      + 4 * (1 - Hx x) * S1 x y ^ 2 := by
  have hS : (∑ i, exp (x i)) ≠ 0 := (Sx_pos x).ne'
  have key : ∀ i, exp (x i) * dd x i * (y i + S1 x y / Sx x) ^ 2 =
      (Hx x + Real.log (Sx x) - 1) * (y i ^ 2 * exp (x i))
      + 2 * (Hx x + Real.log (Sx x) - 1) * (S1 x y / Sx x) * (y i * exp (x i))
      + (Hx x + Real.log (Sx x) - 1) * (S1 x y / Sx x) ^ 2 * exp (x i)
      - (y i ^ 2 * (2 + x i) * exp (x i) - 2 * (y i ^ 2 * exp (x i)))
      - 2 * (S1 x y / Sx x) * (y i * (1 + x i) * exp (x i) - y i * exp (x i))
      - (S1 x y / Sx x) ^ 2 * (x i * exp (x i)) := by
    intro i; unfold dd; ring
  rw [Finset.sum_congr rfl (fun i _ => key i)]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  unfold QQ Hx S1 S2 T1 T2 Sx Tx
  field_simp
  ring

lemma lam_nonneg [NeZero n] (x : Fin n → ℝ) (i : Fin n) : 0 ≤ Real.log (Sx x) - x i := by
  have : exp (x i) ≤ Sx x :=
    Finset.single_le_sum (f := fun i => exp (x i)) (fun j _ => (exp_pos _).le) (Finset.mem_univ i)
  have := (Real.le_log_iff_exp_le (Sx_pos x)).2 this
  linarith

lemma Hx_sum [NeZero n] (x : Fin n → ℝ) :
    Hx x = ∑ i, exp (x i) / Sx x * (Real.log (Sx x) - x i) := by
  have hS := (Sx_pos x).ne'
  have e : ∀ i, exp (x i) / Sx x * (Real.log (Sx x) - x i) =
      Real.log (Sx x) / Sx x * exp (x i) - 1 / Sx x * (x i * exp (x i)) := by
    intro i; ring
  rw [Finset.sum_congr rfl (fun i _ => e i), Finset.sum_sub_distrib, ← Finset.mul_sum,
    ← Finset.mul_sum]
  unfold Hx
  rw [show (∑ i, exp (x i)) = Sx x from rfl, show (∑ i, x i * exp (x i)) = Tx x from rfl,
    div_mul_cancel₀ _ hS]
  ring

lemma dd_neg_H [NeZero n] (x : Fin n → ℝ) {i : Fin n} (h : dd x i < 0) : Hx x < 1 := by
  have := lam_nonneg x i
  unfold dd at h
  linarith

/-- Algebraic core of "at most one big atom". -/
lemma two_big_alg {p q u v H c : ℝ} (hp : 0 < p) (hq : 0 < q) (hpq : p + q ≤ 1)
    (hu : 0 ≤ u) (hv : 0 ≤ v) (hc : 69 / 100 < c) (hc' : c < 7 / 10)
    (hu' : c + 1 - 2 * p ≤ u) (hv' : c + 1 - 2 * q ≤ v)
    (hH : p * u + q * v ≤ H) (h1 : H + u < 1) (h2 : H + v < 1) : False := by
  have hH0 : 0 ≤ H := le_trans (add_nonneg (mul_nonneg hp.le hu) (mul_nonneg hq.le hv)) hH
  have hpc : c / 2 < p := by linarith
  have hqc : c / 2 < q := by linarith
  have d1 := mul_nonneg (by linarith : (0 : ℝ) ≤ 1 + 2 * p) (by linarith : 0 ≤ u - (c + 1 - 2 * p))
  have d2 := mul_nonneg (by linarith : (0 : ℝ) ≤ 1 + 2 * q) (by linarith : 0 ≤ v - (c + 1 - 2 * q))
  have f1 := mul_nonneg (by linarith : (0 : ℝ) ≤ p - c / 2) (by linarith : (0 : ℝ) ≤ q - c / 2)
  have g1' := mul_nonneg hp.le (by linarith : (0 : ℝ) ≤ 1 - q - p)
  have g2' := mul_nonneg hq.le (by linarith : (0 : ℝ) ≤ 1 - q - p)
  have k1 := mul_nonneg (by linarith : (0 : ℝ) ≤ 6 * c - 4) (by linarith : (0 : ℝ) ≤ p + q - c)
  have k2 := mul_pos (by linarith : (0 : ℝ) < c) (by linarith : (0 : ℝ) < 2 * c - 1)
  have hpu := mul_nonneg hp.le hu
  nlinarith

/-- At most one index has `dd x i < 0`. -/
lemma one_big [NeZero n] (x : Fin n → ℝ) {i j : Fin n} (hij : i ≠ j) (hi : dd x i < 0)
    (hj : dd x j < 0) : False := by
  have hS := Sx_pos x
  have hp : 0 < exp (x i) / Sx x := div_pos (exp_pos _) hS
  have hq : 0 < exp (x j) / Sx x := div_pos (exp_pos _) hS
  have hpq : exp (x i) / Sx x + exp (x j) / Sx x ≤ 1 := by
    have h2 : exp (x i) + exp (x j) ≤ Sx x := by
      have := Finset.sum_le_sum_of_subset_of_nonneg (f := fun k => exp (x k))
        (Finset.subset_univ {i, j}) (fun k _ _ => (exp_pos _).le)
      rwa [Finset.sum_pair hij] at this
    rw [← add_div, div_le_one hS]; exact h2
  have hlog : ∀ k, Real.log (exp (x k) / Sx x) = x k - Real.log (Sx x) := by
    intro k; rw [Real.log_div (exp_pos _).ne' hS.ne', Real.log_exp]
  have tang : ∀ t : ℝ, 0 < t → Real.log 2 + 1 - 2 * t ≤ -Real.log t := by
    intro t ht
    have := Real.log_le_sub_one_of_pos (by positivity : (0 : ℝ) < 2 * t)
    rw [Real.log_mul (by norm_num) ht.ne'] at this
    linarith
  have hH : exp (x i) / Sx x * (Real.log (Sx x) - x i) +
      exp (x j) / Sx x * (Real.log (Sx x) - x j) ≤ Hx x := by
    rw [Hx_sum]
    have := Finset.sum_le_sum_of_subset_of_nonneg
      (f := fun k => exp (x k) / Sx x * (Real.log (Sx x) - x k))
      (Finset.subset_univ {i, j})
      (fun k _ _ => mul_nonneg (div_pos (exp_pos _) hS).le (lam_nonneg x k))
    rw [Finset.sum_pair hij] at this
    exact this
  have l2 : (69 / 100 : ℝ) < Real.log 2 := lt_trans (by norm_num) Real.log_two_gt_d9
  have l2' : Real.log 2 < 7 / 10 := lt_trans Real.log_two_lt_d9 (by norm_num)
  refine two_big_alg hp hq hpq (lam_nonneg x i) (lam_nonneg x j) l2 l2' ?_ ?_ hH
    (by unfold dd at hi; linarith) (by unfold dd at hj; linarith)
  · have := tang _ hp; rw [hlog i] at this; linarith
  · have := tang _ hq; rw [hlog j] at this; linarith

/-! ### The index lemma -/

lemma kill (A B : ℝ) : ∃ σ τ : ℝ, (σ ≠ 0 ∨ τ ≠ 0) ∧ σ * A + τ * B = 0 := by
  by_cases h : A = 0 ∧ B = 0
  · exact ⟨1, 0, Or.inl one_ne_zero, by rw [h.1, h.2]; ring⟩
  · refine ⟨B, -A, ?_, by ring⟩
    by_contra h'
    push Not at h'
    exact h ⟨neg_eq_zero.1 h'.2, h'.1⟩

lemma S1_comb (x y1 y2 : Fin n → ℝ) (σ τ : ℝ) :
    S1 x (fun i => σ * y1 i + τ * y2 i) = σ * S1 x y1 + τ * S1 x y2 := by
  unfold S1
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun i _ => by ring)

theorem index [NeZero n] (x y1 y2 : Fin n → ℝ) :
    ∃ σ τ : ℝ, (σ ≠ 0 ∨ τ ≠ 0) ∧ 0 ≤ QQ x (fun i => σ * y1 i + τ * y2 i) := by
  have hS := Sx_pos x
  by_cases hA : ∀ i, 0 ≤ dd x i
  · obtain ⟨σ, τ, hne, h0⟩ := kill (S1 x y1) (S1 x y2)
    refine ⟨σ, τ, hne, ?_⟩
    rw [QQ_eq, S1_comb, h0]
    simp only [zero_div, add_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      mul_zero]
    exact mul_nonneg hS.le (Finset.sum_nonneg (fun i _ =>
      mul_nonneg (mul_nonneg (exp_pos _).le (hA i)) (sq_nonneg _)))
  · push Not at hA
    obtain ⟨i0, hi0⟩ := hA
    have hH := dd_neg_H x hi0
    obtain ⟨σ, τ, hne, h0⟩ := kill (Sx x * y1 i0 + S1 x y1) (Sx x * y2 i0 + S1 x y2)
    refine ⟨σ, τ, hne, ?_⟩
    rw [QQ_eq]
    refine add_nonneg (mul_nonneg hS.le (Finset.sum_nonneg (fun i _ => ?_)))
      (mul_nonneg (by linarith) (sq_nonneg _))
    by_cases hi : i = i0
    · subst hi
      have : (σ * y1 i + τ * y2 i) + S1 x (fun i => σ * y1 i + τ * y2 i) / Sx x = 0 := by
        rw [S1_comb]
        have e : σ * y1 i + τ * y2 i + (σ * S1 x y1 + τ * S1 x y2) / Sx x =
            (σ * (Sx x * y1 i + S1 x y1) + τ * (Sx x * y2 i + S1 x y2)) / Sx x := by
          field_simp; ring
        rw [e, h0, zero_div]
      rw [this]; simp
    · have hdi : 0 ≤ dd x i := by
        by_contra h
        exact one_big x hi (lt_of_not_ge h) hi0
      exact mul_nonneg (mul_nonneg (exp_pos _).le hdi) (sq_nonneg _)

end FriedanMulti

end
