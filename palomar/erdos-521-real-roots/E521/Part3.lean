/-
Copyright 2026 Ming-Chih Kao. Licensed under the Apache License, Version 2.0;
see the LICENSE file at the root of this repository.
-/
module

public import E521.Part2

/-! Part of the proof of Erdős 521 (see `E521/Part1.lean` for the port notes): sections C5–C11 of the
merged Left to Solve file `proofs/erdos-521.lean`. -/

@[expose] public section

-- ===== C5 =====
section S_C5

/-! A two-point *local* smoothing estimate: the cosine-product kernel is compared with the
Gaussian kernel only on a box `|u|, |v| ≤ R`; outside the box but inside the cell
`|u| ≤ U, |v| ≤ V` both kernels are assumed small, and beyond the cell the Fourier tails of the
test functions are used (original). -/

open Finset Real MeasureTheory FourierTransform ProbabilityTheory

noncomputable section

namespace R522

/-- the cosine kernel -/
def Kc {ι : Type*} [Fintype ι] (a b : ι → ℝ) (u v : ℝ) : ℝ :=
  ∏ i, Real.cos (2 * π * (u * a i + v * b i))

lemma Kc_abs_le_one {ι : Type*} [Fintype ι] (a b : ι → ℝ) (u v : ℝ) : |Kc a b u v| ≤ 1 := by
  unfold Kc; rw [Finset.abs_prod]
  exact Finset.prod_le_one₀ (fun i _ => abs_nonneg _) (fun i _ => Real.abs_cos_le_one _)

/-- Fourier tail mass. -/
def Tail (ψ : SchwartzMap ℝ ℂ) (U : ℝ) : ℝ :=
  ∫ u, Set.indicator {u : ℝ | U < |u|} (fun u => ‖𝓕 (ψ : ℝ → ℂ) u‖) u

lemma integrable_ind_le (c R : ℝ) :
    Integrable (Set.indicator {u : ℝ | |u| ≤ R} (fun _ => c)) := by
  have : {u : ℝ | |u| ≤ R} = Set.Icc (-R) R := by ext u; simp [abs_le]
  rw [this]
  exact (continuous_const.integrableOn_Icc).integrable_indicator measurableSet_Icc

lemma integral_ind_le (c R : ℝ) (hR : 0 ≤ R) :
    ∫ u, Set.indicator {u : ℝ | |u| ≤ R} (fun _ => c) u = c * (2 * R) := by
  have : {u : ℝ | |u| ≤ R} = Set.Icc (-R) R := by ext u; simp [abs_le]
  rw [this, integral_indicator measurableSet_Icc, setIntegral_const]
  simp only [Measure.real, Real.volume_Icc, smul_eq_mul]
  rw [ENNReal.toReal_ofReal (by linarith)]; ring

lemma integrable_ind_gt (ψ : SchwartzMap ℝ ℂ) (U : ℝ) :
    Integrable (Set.indicator {u : ℝ | U < |u|} (fun u => ‖𝓕 (ψ : ℝ → ℂ) u‖)) :=
  (fourier_integrable ψ).norm.indicator (measurableSet_lt measurable_const measurable_abs)

lemma integrable_ind_le_f (ψ : SchwartzMap ℝ ℂ) (U c : ℝ) :
    Integrable (Set.indicator {u : ℝ | |u| ≤ U} (fun _ => c)) := integrable_ind_le c U

/-- **Two-point local estimate.** -/
theorem llt_two {ι : Type*} [Fintype ι] [DecidableEq ι] (ψ₁ ψ₂ : SchwartzMap ℝ ℂ)
    (a b : ι → ℝ) (ρ : ℝ) (ha : ∑ i, a i ^ 2 = 1) (hb : ∑ i, b i ^ 2 = 1)
    (hab : ∑ i, a i * b i = ρ) {R U V η M₁ M₂ : ℝ} (hR : 0 ≤ R) (hU : 0 ≤ U) (hη : 0 ≤ η)
    (hM₁ : ∀ u, ‖𝓕 (ψ₁ : ℝ → ℂ) u‖ ≤ M₁) (hM₂ : ∀ v, ‖𝓕 (ψ₂ : ℝ → ℂ) v‖ ≤ M₂)
    (hdec : ∀ u v, |u| ≤ U → |v| ≤ V → (R < |u| ∨ R < |v|) → |Kc a b u v| + gk ρ u v ≤ η) :
    ‖(∑ ε : ι → ℤˣ, ψ₁ (ssum ε a) * ψ₂ (ssum ε b)) / 2 ^ Fintype.card ι
      - ∫ u : ℝ, ∫ v : ℝ, 𝓕 (ψ₁ : ℝ → ℂ) u * 𝓕 (ψ₂ : ℝ → ℂ) v * (gk ρ u v : ℂ)‖
      ≤ (M₁ * (16 * (2 * π) ^ 4 * R ^ 4 * ((∑ i, a i ^ 4) + ∑ i, b i ^ 4))) * (2 * R) * (M₂ * (2 * R))
        + (M₁ * η) * (2 * U) * Mom 0 ψ₂ + 2 * Tail ψ₁ U * Mom 0 ψ₂ + 2 * Mom 0 ψ₁ * Tail ψ₂ V := by
  rw [avg_two]
  have hρ := abs_rho_le a b ρ ha hb hab
  obtain ⟨KC, hKC⟩ : ∃ K : ℝ → ℝ → ℂ, K = fun u v => ∏ i, (Real.cos (2 * π * (u * a i + v * b i)) : ℂ) :=
    ⟨_, rfl⟩
  obtain ⟨KG, hKG⟩ : ∃ K : ℝ → ℝ → ℂ, K = fun u v => (gk ρ u v : ℂ) := ⟨_, rfl⟩
  have eC : ∀ u v, (∏ i, (Real.cos (2 * π * (u * a i + v * b i)) : ℂ)) = KC u v := by
    intro u v; rw [hKC]
  have eG : ∀ u v, ((gk ρ u v : ℝ) : ℂ) = KG u v := by intro u v; rw [hKG]
  simp_rw [eC, eG]
  have hKC1 : ∀ u v, ‖KC u v‖ ≤ 1 := by
    intro u v; rw [hKC]; simp only [norm_prod]
    exact Finset.prod_le_one₀ (fun i _ => norm_nonneg _) (fun i _ => by
      rw [Complex.norm_real, Real.norm_eq_abs]; exact Real.abs_cos_le_one _)
  have hKG1 : ∀ u v, ‖KG u v‖ ≤ 1 := by
    intro u v; rw [hKG]; simp only [Complex.norm_real, Real.norm_eq_abs]
    exact gk_le_one ρ hρ u v
  have cKC : Continuous (Function.uncurry KC) := by
    rw [hKC]; exact continuous_finsetProd _ (fun i _ => by fun_prop)
  have cKG : Continuous (Function.uncurry KG) := by
    rw [hKG]; simp only [gk]; fun_prop
  have hKCnorm : ∀ u v, ‖KC u v‖ = |Kc a b u v| := by
    intro u v; rw [hKC]; simp only [Kc]
    rw [← Complex.ofReal_prod, Complex.norm_real, Real.norm_eq_abs]
  have hKGnorm : ∀ u v, ‖KG u v‖ = gk ρ u v := by
    intro u v; rw [hKG]; simp only [Complex.norm_real, Real.norm_eq_abs]
    exact abs_of_pos (Real.exp_pos _)
  have hdiff : ∀ u v, ‖KC u v - KG u v‖
      ≤ 16 * (2 * π) ^ 4 * ((∑ i, a i ^ 4) * u ^ 4 + (∑ i, b i ^ 4) * v ^ 4) := by
    intro u v
    rw [hKC, hKG]; simp only
    rw [← Complex.ofReal_prod, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    exact kernel_diff a b ρ ha hb hab u v
  set F₁ := 𝓕 (ψ₁ : ℝ → ℂ)
  set F₂ := 𝓕 (ψ₂ : ℝ → ℂ)
  have iC := int_kernel ψ₁ ψ₂ KC cKC hKC1
  have iG := int_kernel ψ₁ ψ₂ KG cKG hKG1
  have iCu := int_kernel_u ψ₁ ψ₂ KC (fun u => cKC.comp (Continuous.prodMk_right u)) hKC1
  have iGu := int_kernel_u ψ₁ ψ₂ KG (fun u => cKG.comp (Continuous.prodMk_right u)) hKG1
  have iC' : Integrable (fun u => ∫ v, F₁ u * F₂ v * KC u v) := iC.integral_prod_left
  have iG' : Integrable (fun u => ∫ v, F₁ u * F₂ v * KG u v) := iG.integral_prod_left
  rw [← integral_sub iC' iG']
  have : ∀ u, (∫ v, F₁ u * F₂ v * KC u v) - ∫ v, F₁ u * F₂ v * KG u v
      = ∫ v, F₁ u * F₂ v * (KC u v - KG u v) := by
    intro u; rw [← integral_sub (iCu u) (iGu u)]; congr 1; ext v; ring
  simp_rw [this]
  set A4 := ∑ i, a i ^ 4
  set B4 := ∑ i, b i ^ 4
  set E := 16 * (2 * π) ^ 4 * R ^ 4 * (A4 + B4)
  have hA : 0 ≤ A4 := Finset.sum_nonneg (fun i _ => by positivity)
  have hB : 0 ≤ B4 := Finset.sum_nonneg (fun i _ => by positivity)
  have hM₁0 : 0 ≤ M₁ := (norm_nonneg _).trans (hM₁ 0)
  have hM₂0 : 0 ≤ M₂ := (norm_nonneg _).trans (hM₂ 0)
  let SR : Set ℝ := {u | |u| ≤ R}
  let SU : Set ℝ := {u | |u| ≤ U}
  let GU : Set ℝ := {u | U < |u|}
  let GV : Set ℝ := {u | V < |u|}
  let fa : Fin 4 → ℝ → ℝ := ![Set.indicator SR (fun _ => M₁ * E), Set.indicator SU (fun _ => M₁ * η),
    fun u => 2 * Set.indicator GU (fun u => ‖F₁ u‖) u, fun u => 2 * ‖F₁ u‖]
  let fb : Fin 4 → ℝ → ℝ := ![Set.indicator SR (fun _ => M₂), fun v => ‖F₂ v‖, fun v => ‖F₂ v‖,
    Set.indicator GV (fun v => ‖F₂ v‖)]
  have ia : ∀ i, Integrable (fa i) := by
    intro i; fin_cases i
    · exact integrable_ind_le _ _
    · exact integrable_ind_le _ _
    · exact (integrable_ind_gt ψ₁ U).const_mul 2
    · exact (fourier_integrable ψ₁).norm.const_mul 2
  have ib : ∀ i, Integrable (fb i) := by
    intro i; fin_cases i
    · exact integrable_ind_le _ _
    · exact (fourier_integrable ψ₂).norm
    · exact (fourier_integrable ψ₂).norm
    · exact integrable_ind_gt ψ₂ V
  have key := norm_iter_le (k := 4) (fun u v => F₁ u * F₂ v * (KC u v - KG u v)) fa fb ia ib (by
    intro u v
    simp only [fa, fb, Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons, Matrix.head_cons]
    rw [norm_mul, norm_mul]
    have n1 := norm_nonneg (F₁ u)
    have n2 := norm_nonneg (F₂ v)
    have hE0 : 0 ≤ E := by positivity
    have hK2 : ‖KC u v - KG u v‖ ≤ 2 := by
      calc ‖KC u v - KG u v‖ ≤ ‖KC u v‖ + ‖KG u v‖ := norm_sub_le _ _
        _ ≤ 1 + 1 := add_le_add (hKC1 u v) (hKG1 u v)
        _ = 2 := by norm_num
    have T0 : 0 ≤ Set.indicator SR (fun _ => M₁ * E) u * Set.indicator SR (fun _ => M₂) v := by
      apply mul_nonneg <;> apply Set.indicator_nonneg <;> intro _ _ <;> positivity
    have T1 : 0 ≤ Set.indicator SU (fun _ => M₁ * η) u * ‖F₂ v‖ := by
      apply mul_nonneg _ n2; apply Set.indicator_nonneg; intro _ _; positivity
    have T2 : 0 ≤ 2 * Set.indicator GU (fun u => ‖F₁ u‖) u * ‖F₂ v‖ := by
      apply mul_nonneg _ n2; apply mul_nonneg (by norm_num)
      apply Set.indicator_nonneg; intro _ _; positivity
    have T3 : 0 ≤ 2 * ‖F₁ u‖ * Set.indicator GV (fun v => ‖F₂ v‖) v := by
      apply mul_nonneg (by positivity); apply Set.indicator_nonneg; intro _ _; positivity
    by_cases hbox : |u| ≤ R ∧ |v| ≤ R
    · have h1 : Set.indicator SR (fun _ => M₁ * E) u = M₁ * E := Set.indicator_of_mem (show u ∈ SR from hbox.1) _
      have h2 : Set.indicator SR (fun _ => M₂) v = M₂ := Set.indicator_of_mem (show v ∈ SR from hbox.2) _
      have hd := hdiff u v
      have hu4 : u ^ 4 ≤ R ^ 4 := by
        have := pow_le_pow_left₀ (abs_nonneg u) hbox.1 4
        rwa [show |u| ^ 4 = u ^ 4 by rw [← abs_pow]; exact abs_of_nonneg (by positivity)] at this
      have hv4 : v ^ 4 ≤ R ^ 4 := by
        have := pow_le_pow_left₀ (abs_nonneg v) hbox.2 4
        rwa [show |v| ^ 4 = v ^ 4 by rw [← abs_pow]; exact abs_of_nonneg (by positivity)] at this
      have hd' : ‖KC u v - KG u v‖ ≤ E := by
        refine hd.trans ?_
        simp only [E]
        have : A4 * u ^ 4 + B4 * v ^ 4 ≤ R ^ 4 * (A4 + B4) := by nlinarith
        nlinarith [show (0:ℝ) ≤ 16 * (2 * π) ^ 4 by positivity]
      have : ‖F₁ u‖ * ‖F₂ v‖ * ‖KC u v - KG u v‖ ≤ M₁ * E * M₂ := by
        calc ‖F₁ u‖ * ‖F₂ v‖ * ‖KC u v - KG u v‖ ≤ M₁ * M₂ * E := by
              gcongr
              · exact hM₁ u
              · exact hM₂ v
          _ = M₁ * E * M₂ := by ring
      rw [h1, h2]; linarith
    · by_cases hu : |u| ≤ U
      · by_cases hv : |v| ≤ V
        · have hout : R < |u| ∨ R < |v| := by
            by_contra hc; push Not at hc; exact hbox ⟨hc.1, hc.2⟩
          have hd := hdec u v hu hv hout
          have hK : ‖KC u v - KG u v‖ ≤ η := by
            calc ‖KC u v - KG u v‖ ≤ ‖KC u v‖ + ‖KG u v‖ := norm_sub_le _ _
              _ = |Kc a b u v| + gk ρ u v := by rw [hKCnorm, hKGnorm]
              _ ≤ η := hd
          have h1 : Set.indicator SU (fun _ => M₁ * η) u = M₁ * η := Set.indicator_of_mem (show u ∈ SU from hu) _
          have : ‖F₁ u‖ * ‖F₂ v‖ * ‖KC u v - KG u v‖ ≤ M₁ * η * ‖F₂ v‖ := by
            calc ‖F₁ u‖ * ‖F₂ v‖ * ‖KC u v - KG u v‖ ≤ M₁ * ‖F₂ v‖ * η := by
                  gcongr; exact hM₁ u
              _ = M₁ * η * ‖F₂ v‖ := by ring
          rw [h1]; linarith
        · have h3 : Set.indicator GV (fun v => ‖F₂ v‖) v = ‖F₂ v‖ :=
            Set.indicator_of_mem (show v ∈ GV from lt_of_not_ge hv) _
          have : ‖F₁ u‖ * ‖F₂ v‖ * ‖KC u v - KG u v‖ ≤ 2 * ‖F₁ u‖ * ‖F₂ v‖ := by
            calc ‖F₁ u‖ * ‖F₂ v‖ * ‖KC u v - KG u v‖ ≤ ‖F₁ u‖ * ‖F₂ v‖ * 2 := by gcongr
              _ = _ := by ring
          rw [h3]; linarith
      · have h3 : Set.indicator GU (fun u => ‖F₁ u‖) u = ‖F₁ u‖ :=
          Set.indicator_of_mem (show u ∈ GU from lt_of_not_ge hu) _
        have : ‖F₁ u‖ * ‖F₂ v‖ * ‖KC u v - KG u v‖ ≤ 2 * ‖F₁ u‖ * ‖F₂ v‖ := by
          calc ‖F₁ u‖ * ‖F₂ v‖ * ‖KC u v - KG u v‖ ≤ ‖F₁ u‖ * ‖F₂ v‖ * 2 := by gcongr
            _ = _ := by ring
        rw [h3]; linarith)
  refine key.trans (le_of_eq ?_)
  simp only [fa, fb, Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons, Matrix.head_cons]
  rw [integral_ind_le _ _ hR, integral_ind_le _ _ hR, integral_ind_le _ _ hU, integral_const_mul,
    integral_const_mul]
  unfold Tail Mom
  simp only [pow_zero, one_mul]
  ring

end R522
end

end S_C5

-- ===== C6 =====
section S_C6

/-! Decay of cosine products over arithmetic progressions (original). -/

open Finset Real

noncomputable section

namespace R522

lemma abs_cos_le_exp_sin (x : ℝ) : |Real.cos x| ≤ Real.exp (-(Real.sin x ^ 2 / 2)) := by
  have h1 : Real.cos x ^ 2 = 1 - Real.sin x ^ 2 := by rw [← Real.sin_sq_add_cos_sq x]; ring
  have h2 : 1 - Real.sin x ^ 2 ≤ Real.exp (-(Real.sin x ^ 2)) := by
    have := Real.add_one_le_exp (-(Real.sin x ^ 2)); linarith
  have h3 : |Real.cos x| ^ 2 ≤ Real.exp (-(Real.sin x ^ 2 / 2)) ^ 2 := by
    rw [sq_abs, h1, ← Real.exp_nat_mul]; push_cast
    calc 1 - Real.sin x ^ 2 ≤ Real.exp (-(Real.sin x ^ 2)) := h2
      _ = Real.exp (2 * -(Real.sin x ^ 2 / 2)) := by ring_nf
  exact (pow_le_pow_iff_left₀ (abs_nonneg _) (Real.exp_pos _).le two_ne_zero).mp h3

lemma abs_prod_cos_le {n : ℕ} (θ : ℕ → ℝ) :
    |∏ w ∈ range n, Real.cos (θ w)| ≤ Real.exp (-((∑ w ∈ range n, Real.sin (θ w) ^ 2) / 2)) := by
  rw [Finset.abs_prod, Finset.sum_div, ← Finset.sum_neg_distrib, Real.exp_sum]
  exact Finset.prod_le_prod₀ (fun w _ => abs_nonneg _) (fun w _ => abs_cos_le_exp_sin _)

lemma sin_sq_sub_le (x y : ℝ) : Real.sin (x - y) ^ 2 ≤ 2 * (Real.sin x ^ 2 + Real.sin y ^ 2) := by
  rw [Real.sin_sub]
  nlinarith [Real.sin_sq_add_cos_sq x, Real.sin_sq_add_cos_sq y,
    sq_nonneg (Real.sin x * Real.cos y + Real.cos x * Real.sin y),
    sq_nonneg (Real.sin x * Real.cos y), sq_nonneg (Real.cos x * Real.sin y)]

/-- pairing at gap `d` -/
lemma sum_sin_sq_ge_pair (n d : ℕ) (hd : d ≤ n) (s t : ℝ) :
    ((n - d : ℕ) : ℝ) * Real.sin (d * s) ^ 2 ≤ 4 * ∑ w ∈ range n, Real.sin (s * w + t) ^ 2 := by
  have hpair : ∀ w : ℕ, Real.sin (d * s) ^ 2 ≤
      2 * (Real.sin (s * (w + d : ℕ) + t) ^ 2 + Real.sin (s * w + t) ^ 2) := by
    intro w
    have := sin_sq_sub_le (s * (w + d : ℕ) + t) (s * w + t)
    have e : s * ((w + d : ℕ) : ℝ) + t - (s * w + t) = d * s := by push_cast; ring
    rwa [e] at this
  have hsum := Finset.sum_le_sum (s := range (n - d)) (fun w _ => hpair w)
  rw [sum_const, card_range, nsmul_eq_mul] at hsum
  rw [← mul_sum, sum_add_distrib] at hsum
  have h1 : ∑ w ∈ range (n - d), Real.sin (s * ((w + d : ℕ) : ℝ) + t) ^ 2 ≤
      ∑ w ∈ range n, Real.sin (s * w + t) ^ 2 := by
    have e : ∑ w ∈ range (n - d), Real.sin (s * ((w + d : ℕ) : ℝ) + t) ^ 2 =
        ∑ w ∈ Ico d n, Real.sin (s * (w : ℝ) + t) ^ 2 := by
      rw [sum_Ico_eq_sum_range]; apply sum_congr rfl; intro w _; rw [add_comm w d]
    rw [e]
    exact sum_le_sum_of_subset_of_nonneg (fun x hx => by
      rw [mem_Ico] at hx; rw [mem_range]; omega) (fun _ _ _ => by positivity)
  have h2 : ∑ w ∈ range (n - d), Real.sin (s * (w : ℝ) + t) ^ 2 ≤
      ∑ w ∈ range n, Real.sin (s * w + t) ^ 2 :=
    sum_le_sum_of_subset_of_nonneg (fun x hx => by rw [mem_range] at hx ⊢; omega) (fun _ _ _ => by positivity)
  linarith

lemma sin_half_le_sin {x : ℝ} (h1 : 1 / 2 ≤ |x|) (h2 : |x| ≤ 5 / 2) :
    Real.sin (1 / 2) ^ 2 ≤ Real.sin x ^ 2 := by
  have hsa : Real.sin x ^ 2 = Real.sin |x| ^ 2 := by
    rcases abs_cases x with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h]
    rw [Real.sin_neg]; ring
  rw [hsa]
  have hpi := Real.pi_gt_three
  have key : Real.sin (1 / 2) ≤ Real.sin |x| := by
    rcases le_or_gt |x| (π / 2) with h | h
    · exact Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith) h h1
    · rw [← Real.sin_pi_sub |x|]
      apply Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith) (by linarith)
      linarith
  have h0 : 0 ≤ Real.sin (1 / 2) := Real.sin_nonneg_of_nonneg_of_le_pi (by norm_num) (by linarith)
  nlinarith

/-- **Case A**: a non-tiny step gives linear decay. -/
lemma sum_sin_sq_caseA (n : ℕ) (s t : ℝ) (hs1 : 8 / n ≤ |s|) (hs2 : |s| ≤ 2) (hn : 16 ≤ n) :
    (n : ℝ) * Real.sin (1 / 2) ^ 2 ≤ 8 * ∑ w ∈ range n, Real.sin (s * w + t) ^ 2 := by
  have hn0 : (0 : ℝ) < n := by positivity
  have hsp : 0 < |s| := lt_of_lt_of_le (by positivity) hs1
  set d := ⌈1 / (2 * |s|)⌉₊ with hd
  have hd1 : 1 / (2 * |s|) ≤ d := Nat.le_ceil _
  have hd2 : (d : ℝ) < 1 / (2 * |s|) + 1 := Nat.ceil_lt_add_one (by positivity)
  have hdn : (d : ℝ) ≤ n / 2 := by
    have : 1 / (2 * |s|) ≤ n / 16 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      have : 8 ≤ |s| * n := by rwa [div_le_iff₀ hn0] at hs1
      nlinarith
    have : (16 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hdn' : d ≤ n := by
    have : (d : ℝ) ≤ n := by linarith
    exact_mod_cast this
  have hds1 : 1 / 2 ≤ |d * s| := by
    rw [abs_mul, Nat.abs_cast]
    have := mul_le_mul_of_nonneg_right hd1 hsp.le
    rwa [show 1 / (2 * |s|) * |s| = 1 / 2 by field_simp] at this
  have hds2 : |d * s| ≤ 5 / 2 := by
    rw [abs_mul, Nat.abs_cast]
    have := mul_le_mul_of_nonneg_right hd2.le hsp.le
    rw [add_mul, show 1 / (2 * |s|) * |s| = 1 / 2 by field_simp, one_mul] at this
    linarith
  have hsin := sin_half_le_sin hds1 hds2
  have hp := sum_sin_sq_ge_pair n d hdn' s t
  have hnd : (n : ℝ) / 2 ≤ ((n - d : ℕ) : ℝ) := by
    rw [Nat.cast_sub hdn']; linarith
  have h0 : 0 ≤ Real.sin (1 / 2) ^ 2 := by positivity
  nlinarith

lemma sum_sq_range_mul_six (m : ℕ) :
    (∑ w ∈ range m, (w : ℝ) ^ 2) * 6 = (m : ℝ) * (m - 1) * (2 * m - 1) := by
  induction m with
  | zero => simp
  | succ m ih => rw [sum_range_succ, add_mul, ih]; push_cast; ring

/-- the quadratic form of an arithmetic progression is comparable to its diagonal. -/
lemma ap_quad_ge (m : ℕ) (s t : ℝ) :
    ((m : ℝ) * t ^ 2 + (∑ w ∈ range m, (w : ℝ) ^ 2) * s ^ 2) / 8 ≤
      ∑ w ∈ range m, (t + s * w) ^ 2 := by
  have hA : ∑ w ∈ range m, (t + s * w) ^ 2 =
      m * t ^ 2 + 2 * (∑ w ∈ range m, (w : ℝ)) * t * s + (∑ w ∈ range m, (w : ℝ) ^ 2) * s ^ 2 := by
    rw [show (m : ℝ) * t ^ 2 = ∑ w ∈ range m, t ^ 2 by simp]
    rw [mul_sum, sum_mul, sum_mul, sum_mul, ← sum_add_distrib, ← sum_add_distrib]
    apply sum_congr rfl; intro w _; ring
  -- B^2 ≤ (3/4) A C
  have hB : (∑ w ∈ range m, (w : ℝ)) ^ 2 * 4 ≤ 3 * (m : ℝ) * ∑ w ∈ range m, (w : ℝ) ^ 2 := by
    have e1 : (∑ w ∈ range m, (w : ℝ)) * 2 = (m : ℝ) * (m - 1) := by
      have := Finset.sum_range_id_mul_two m
      have h' : ((∑ w ∈ range m, w : ℕ) : ℝ) * 2 = (m : ℝ) * ((m - 1 : ℕ) : ℝ) := by exact_mod_cast this
      rcases Nat.eq_zero_or_pos m with h | h
      · subst h; simp
      · rw [Nat.cast_sub h, Nat.cast_one] at h'; push_cast at h'; linarith
    have e2 := sum_sq_range_mul_six m
    have hm : (0 : ℝ) ≤ m := by positivity
    rcases Nat.eq_zero_or_pos m with h | h
    · subst h; simp
    · have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast h
      nlinarith [mul_nonneg hm (sub_nonneg.mpr hm1), sq_nonneg ((m : ℝ) - 1)]
  rw [hA]
  set A := (m : ℝ)
  set B := ∑ w ∈ range m, (w : ℝ)
  set C := ∑ w ∈ range m, (w : ℝ) ^ 2
  have hA0 : 0 ≤ A := by positivity
  have hC0 : 0 ≤ C := sum_nonneg (fun _ _ => by positivity)
  have key : A * ((7 / 8) * A * t ^ 2 + 2 * B * t * s + (7 / 8) * C * s ^ 2) =
      (7 / 8) * (A * t + 8 / 7 * B * s) ^ 2 + ((7 / 8) * A * C - 8 / 7 * B ^ 2) * s ^ 2 := by ring
  have hpos : 0 ≤ (7 / 8) * A * t ^ 2 + 2 * B * t * s + (7 / 8) * C * s ^ 2 := by
    rcases eq_or_lt_of_le hA0 with h0 | h0
    · have hB0 : B = 0 := by
        have : B ^ 2 * 4 ≤ 0 := by rw [← h0] at hB; simpa using hB
        nlinarith [sq_nonneg B]
      rw [← h0, hB0]; nlinarith [mul_nonneg hC0 (sq_nonneg s)]
    · have : 0 ≤ (7 / 8) * (A * t + 8 / 7 * B * s) ^ 2 + ((7 / 8) * A * C - 8 / 7 * B ^ 2) * s ^ 2 := by
        have : 0 ≤ (7 / 8) * A * C - 8 / 7 * B ^ 2 := by nlinarith
        positivity
      rw [← key] at this
      exact (mul_nonneg_iff_of_pos_left h0).mp this
  nlinarith

lemma sin_sq_ge_of_le {x : ℝ} (hx : |x| ≤ 2) : x ^ 2 / 8 ≤ Real.sin x ^ 2 := by
  have hsa : Real.sin x ^ 2 = Real.sin |x| ^ 2 := by
    rcases abs_cases x with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h]; rw [Real.sin_neg]; ring
  rw [hsa, ← sq_abs x]
  set y := |x|
  have hy0 : 0 ≤ y := abs_nonneg x
  -- sin y ≥ y/2 on [0, 2] (concavity on [0, π])
  have hpi := Real.pi_gt_three
  have key : (1 - 2 / π) * y ≤ Real.sin y := by
    have hpi4 : 2 / π ≤ 1 := by rw [div_le_one (by positivity)]; linarith
    have hpi5 : 1 - 2 / π ≤ 2 / π := by
      have : 4 / π ≥ 1 := by rw [ge_iff_le, le_div_iff₀ (by positivity)]; linarith [Real.pi_lt_four]
      have e : 4 / π = 2 * (2 / π) := by ring
      linarith
    rcases le_or_gt y (π / 2) with h | h
    · have := Real.mul_le_sin hy0 h
      nlinarith
    · have h2 : π - y ≤ π / 2 := by linarith
      have h3 : 0 ≤ π - y := by linarith
      have := Real.mul_le_sin h3 h2
      rw [Real.sin_pi_sub] at this
      have e : 2 / π * (π - y) = 2 - 2 / π * y := by field_simp
      nlinarith
  have hc : 1 / 8 ≤ (1 - 2 / π) ^ 2 := by
    have : 2 / π ≤ 0.64 := by rw [div_le_iff₀ (by positivity)]; nlinarith [Real.pi_gt_d2]
    nlinarith
  have h0 : 0 ≤ (1 - 2 / π) * y := by
    apply mul_nonneg _ hy0
    have : 2 / π ≤ 1 := by rw [div_le_one (by positivity)]; linarith
    linarith
  nlinarith

/-- **Case B**: tiny steps; the first `m` terms stay inside `|θ| ≤ 2`. -/
lemma sum_sin_sq_caseB (n m : ℕ) (hm : m ≤ n) (s t : ℝ) (ht : |t| ≤ 8 / 5)
    (hsm : |s| * m ≤ 2 / 5) :
    ((m : ℝ) * t ^ 2 + (∑ w ∈ range m, (w : ℝ) ^ 2) * s ^ 2) / 64 ≤
      ∑ w ∈ range n, Real.sin (s * w + t) ^ 2 := by
  have h1 : ∀ w ∈ range m, (t + s * w) ^ 2 / 8 ≤ Real.sin (s * w + t) ^ 2 := by
    intro w hw
    rw [mem_range] at hw
    have hw' : (w : ℝ) ≤ m := by exact_mod_cast hw.le
    have hsw : |s * w| ≤ 2 / 5 := by
      rw [abs_mul, Nat.abs_cast]
      calc |s| * w ≤ |s| * m := mul_le_mul_of_nonneg_left hw' (abs_nonneg s)
        _ ≤ 2 / 5 := hsm
    have : |s * w + t| ≤ 2 := by
      calc |s * w + t| ≤ |s * w| + |t| := abs_add_le _ _
        _ ≤ 2 := by linarith
    have h := sin_sq_ge_of_le this
    calc (t + s * w) ^ 2 / 8 = (s * w + t) ^ 2 / 8 := by ring
      _ ≤ Real.sin (s * w + t) ^ 2 := h
  have h2 : ∑ w ∈ range m, (t + s * w) ^ 2 / 8 ≤ ∑ w ∈ range m, Real.sin (s * w + t) ^ 2 :=
    sum_le_sum h1
  have h3 : ∑ w ∈ range m, Real.sin (s * w + t) ^ 2 ≤ ∑ w ∈ range n, Real.sin (s * w + t) ^ 2 :=
    sum_le_sum_of_subset_of_nonneg (fun x hx => by rw [mem_range] at hx ⊢; omega) (fun _ _ _ => by positivity)
  have h4 := ap_quad_ge m s t
  rw [← sum_div] at h2
  linarith

end R522
end

end S_C6

-- ===== C7 =====
section S_C7

/-! Affine changes of variable for Fourier transforms, and the test functions (original). -/

open Finset Real MeasureTheory FourierTransform

noncomputable section

namespace R522

lemma integral_affine (F : ℝ → ℂ) {a : ℝ} (b : ℝ) (ha : a ≠ 0) :
    ∫ x, F (a * x + b) = ((|a|⁻¹ : ℝ) : ℂ) * ∫ y, F y := by
  have h1 : (fun x => F (a * x + b)) = fun x => (fun y => F (y + b)) (a * x) := rfl
  rw [h1, Measure.integral_comp_mul_left (fun y => F (y + b)) a, integral_add_right_eq_self F b]
  rw [abs_inv, Complex.real_smul]

lemma integral_affine_real (F : ℝ → ℝ) {a : ℝ} (b : ℝ) (ha : a ≠ 0) :
    ∫ x, F (a * x + b) = |a|⁻¹ * ∫ y, F y := by
  have h1 : (fun x => F (a * x + b)) = fun x => (fun y => F (y + b)) (a * x) := rfl
  rw [h1, Measure.integral_comp_mul_left (fun y => F (y + b)) a, integral_add_right_eq_self F b]
  rw [abs_inv, smul_eq_mul]

lemma norm_fourier_affine (f : ℝ → ℂ) {a : ℝ} (b : ℝ) (ha : a ≠ 0) (u : ℝ) :
    ‖𝓕 (fun x => f (a * x + b)) u‖ = |a|⁻¹ * ‖𝓕 f (u / a)‖ := by
  rw [Real.fourier_real_eq_integral_exp_smul, Real.fourier_real_eq_integral_exp_smul]
  set F : ℝ → ℂ := fun y => Complex.exp (↑(-2 * π * ((y - b) / a) * u) * Complex.I) • f y
  have hF : ∀ x, Complex.exp (↑(-2 * π * x * u) * Complex.I) • f (a * x + b) = F (a * x + b) := by
    intro x; simp only [F]; congr 4; field_simp; ring
  simp_rw [hF]
  rw [integral_affine F b ha]
  have hF' : ∀ y, F y = Complex.exp (↑(2 * π * b * u / a) * Complex.I) *
      (Complex.exp (↑(-2 * π * y * (u / a)) * Complex.I) • f y) := by
    intro y; simp only [F, smul_eq_mul]; rw [← mul_assoc, ← Complex.exp_add]; congr 2; push_cast
    field_simp; ring
  simp_rw [hF']
  rw [integral_const_mul, norm_mul, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]

lemma integral_norm_fourier_affine (f : ℝ → ℂ) {a : ℝ} (b : ℝ) (ha : a ≠ 0) :
    ∫ u, ‖𝓕 (fun x => f (a * x + b)) u‖ = ∫ v, ‖𝓕 f v‖ := by
  simp_rw [norm_fourier_affine f b ha, div_eq_inv_mul]
  rw [integral_const_mul]
  have := integral_affine_real (fun v => ‖𝓕 f v‖) (a := a⁻¹) 0 (inv_ne_zero ha)
  simp only [add_zero] at this
  rw [this, abs_inv, inv_inv, ← mul_assoc, inv_mul_cancel₀ (abs_ne_zero.mpr ha), one_mul]

lemma integral_tail_fourier_affine (f : ℝ → ℂ) {a : ℝ} (b : ℝ) (ha : a ≠ 0) (U : ℝ) :
    ∫ u, Set.indicator {u : ℝ | U < |u|} (fun u => ‖𝓕 (fun x => f (a * x + b)) u‖) u
      = ∫ v, Set.indicator {v : ℝ | U / |a| < |v|} (fun v => ‖𝓕 f v‖) v := by
  have e : ∀ u, Set.indicator {u : ℝ | U < |u|} (fun u => ‖𝓕 (fun x => f (a * x + b)) u‖) u
      = |a|⁻¹ * (fun v => Set.indicator {v : ℝ | U / |a| < |v|} (fun v => ‖𝓕 f v‖) v) (a⁻¹ * u + 0) := by
    intro u
    simp only [add_zero, Set.indicator, Set.mem_setOf_eq]
    have hab : 0 < |a| := abs_pos.mpr ha
    have : (U < |u|) ↔ (U / |a| < |a⁻¹ * u|) := by
      rw [abs_mul, abs_inv, div_lt_iff₀ hab, inv_mul_eq_div, div_mul_cancel₀ _ hab.ne']
    by_cases h : U < |u|
    · rw [if_pos h, if_pos (this.mp h), norm_fourier_affine f b ha, div_eq_inv_mul]
    · rw [if_neg h, if_neg (fun h' => h (this.mpr h'))]; ring
  simp_rw [e]
  rw [integral_const_mul, integral_affine_real _ 0 (inv_ne_zero ha), abs_inv, inv_inv, ← mul_assoc,
    inv_mul_cancel₀ (abs_ne_zero.mpr ha), one_mul]

lemma norm_fourier_le (f : ℝ → ℂ) (u : ℝ) : ‖𝓕 f u‖ ≤ ∫ x, ‖f x‖ := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  congr 1; ext x
  rw [smul_eq_mul, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]

lemma tail_le_mom4 (ψ : SchwartzMap ℝ ℂ) {U : ℝ} (hU : 0 < U) : Tail ψ U ≤ Mom 4 ψ / U ^ 4 := by
  unfold Tail Mom
  rw [le_div_iff₀ (by positivity), ← integral_mul_const]
  apply integral_mono_of_nonneg
  · exact Filter.Eventually.of_forall (fun u =>
      mul_nonneg (Set.indicator_nonneg (fun _ _ => norm_nonneg _) u) (by positivity))
  · exact integrable_mom 4 ψ
  · refine Filter.Eventually.of_forall (fun u => ?_)
    simp only [Set.indicator, Set.mem_setOf_eq]
    split_ifs with h
    · have : U ^ 4 ≤ |u| ^ 4 := pow_le_pow_left₀ hU.le h.le 4
      have hn := norm_nonneg (𝓕 (ψ : ℝ → ℂ) u)
      show ‖𝓕 (ψ : ℝ → ℂ) u‖ * U ^ 4 ≤ |u| ^ 4 * ‖𝓕 (ψ : ℝ → ℂ) u‖
      nlinarith
    · show 0 * U ^ 4 ≤ |u| ^ 4 * ‖𝓕 (ψ : ℝ → ℂ) u‖
      rw [zero_mul]; positivity

/-! ### test functions -/

/-- the `X`-bump at scale `lam`: `1` on `[0, lam]`, supported in `(-lamδ, lam(1+δ))`. -/
def ψX (lam δ : ℝ) (hlam : 0 < lam) (hδ : 0 < δ) : SchwartzMap ℝ ℂ :=
  Sb 0 lam (lam * δ) hlam (mul_pos hlam hδ)

lemma bb_scale {lam δ : ℝ} (hlam : 0 < lam) (hδ : 0 < δ) (x : ℝ) :
    bb 0 lam (lam * δ) hlam (mul_pos hlam hδ) x = bb 0 1 δ one_pos hδ (lam⁻¹ * x + 0) := by
  simp only [bb, ContDiffBump.apply, add_zero]
  have hl : lam ≠ 0 := hlam.ne'
  congr 1
  · simp only [sub_zero]; field_simp
  · simp only [smul_eq_mul, sub_zero]; field_simp; ring

lemma ψX_apply {lam δ : ℝ} (hlam : 0 < lam) (hδ : 0 < δ) (x : ℝ) :
    ψX lam δ hlam hδ x = Sb 0 1 δ one_pos hδ (lam⁻¹ * x + 0) := by
  simp only [ψX, Sb_apply, bb_scale hlam hδ]

lemma ψX_coe {lam δ : ℝ} (hlam : 0 < lam) (hδ : 0 < δ) :
    (ψX lam δ hlam hδ : ℝ → ℂ) = fun x => (Sb 0 1 δ one_pos hδ : ℝ → ℂ) (lam⁻¹ * x + 0) := by
  funext x; exact ψX_apply hlam hδ x

lemma mom0_ψX {lam δ : ℝ} (hlam : 0 < lam) (hδ : 0 < δ) : Mom 0 (ψX lam δ hlam hδ) = Mom 0 (Sb 0 1 δ one_pos hδ) := by
  simp only [Mom, pow_zero, one_mul]
  rw [ψX_coe, integral_norm_fourier_affine _ 0 (inv_ne_zero hlam.ne')]

lemma tail_ψX {lam δ : ℝ} (hlam : 0 < lam) (hδ : 0 < δ) (U : ℝ) :
    Tail (ψX lam δ hlam hδ) U = Tail (Sb 0 1 δ one_pos hδ) (lam * U) := by
  unfold Tail
  rw [ψX_coe, integral_tail_fourier_affine _ 0 (inv_ne_zero hlam.ne'), abs_inv, abs_of_pos hlam,
    div_inv_eq_mul, mul_comm]

lemma sup_ψX {lam δ : ℝ} (hlam : 0 < lam) (hδ : 0 < δ) (u : ℝ) :
    ‖𝓕 (ψX lam δ hlam hδ : ℝ → ℂ) u‖ ≤ lam * (1 + 2 * δ) := by
  refine (norm_fourier_le _ u).trans ?_
  -- the bump is in [0,1] and vanishes outside an interval of length lam(1+2δ)
  have hle : ∀ x, ‖(ψX lam δ hlam hδ : ℝ → ℂ) x‖ ≤
      Set.indicator (Set.Icc (-(lam * δ)) (lam + lam * δ)) (fun _ => (1 : ℝ)) x := by
    intro x
    simp only [ψX, Sb_apply, Complex.norm_real, Real.norm_eq_abs]
    rw [abs_of_nonneg (bb_nonneg _ _ _ _ _ x)]
    by_cases hx : x ∈ Set.Icc (-(lam * δ)) (lam + lam * δ)
    · rw [Set.indicator_of_mem hx]; exact bb_le_one _ _ _ _ _ x
    · rw [Set.indicator_of_notMem hx, bb_zero]
      intro h; apply hx
      simp only [Set.mem_Ioo, zero_sub] at h
      exact ⟨h.1.le, h.2.le⟩
  calc ∫ x, ‖(ψX lam δ hlam hδ : ℝ → ℂ) x‖
      ≤ ∫ x, Set.indicator (Set.Icc (-(lam * δ)) (lam + lam * δ)) (fun _ => (1 : ℝ)) x := by
        apply integral_mono_of_nonneg (Filter.Eventually.of_forall (fun x => norm_nonneg _))
        · exact (continuous_const.integrableOn_Icc).integrable_indicator measurableSet_Icc
        · exact Filter.Eventually.of_forall hle
    _ = lam * (1 + 2 * δ) := by
        rw [integral_indicator measurableSet_Icc, setIntegral_const]
        simp only [Measure.real, Real.volume_Icc, smul_eq_mul, mul_one]
        rw [ENNReal.toReal_ofReal (by nlinarith)]; ring

/-- the base of the partition of unity: `st z - st (z - 1)`, supported in `[0, 2]`. -/
def χ0 (z : ℝ) : ℝ := Real.smoothTransition z - Real.smoothTransition (z - 1)

lemma χ0_nonneg (z : ℝ) : 0 ≤ χ0 z := by
  unfold χ0; have := Real.smoothTransition.monotone (show z - 1 ≤ z by linarith); linarith

lemma χ0_le_one (z : ℝ) : χ0 z ≤ 1 := by
  unfold χ0
  have := Real.smoothTransition.le_one z
  have := Real.smoothTransition.nonneg (z - 1)
  linarith

lemma χ0_zero_of {z : ℝ} (hz : z ≤ 0 ∨ 2 ≤ z) : χ0 z = 0 := by
  unfold χ0
  rcases hz with h | h
  · rw [Real.smoothTransition.zero_of_nonpos h, Real.smoothTransition.zero_of_nonpos (by linarith)]
    ring
  · rw [Real.smoothTransition.one_of_one_le (by linarith), Real.smoothTransition.one_of_one_le (by linarith)]
    ring

lemma χ0_contDiff : ContDiff ℝ (⊤ : ℕ∞) χ0 := by
  unfold χ0
  exact Real.smoothTransition.contDiff.sub (Real.smoothTransition.contDiff.comp (contDiff_id.sub contDiff_const))

lemma χ0_hasCompactSupport : HasCompactSupport χ0 := by
  apply HasCompactSupport.intro (isCompact_Icc (a := (0 : ℝ)) (b := 2))
  intro z hz
  simp only [Set.mem_Icc, not_and_or, not_le] at hz
  exact χ0_zero_of (hz.elim (fun h => Or.inl h.le) (fun h => Or.inr h.le))

/-- the `Y`-weight of shell `j`: `χ0 (-y/h - j + 1)`. -/
def χY (h : ℝ) (j : ℕ) (y : ℝ) : ℝ := χ0 ((-h⁻¹) * y + (1 - j))

lemma χY_contDiff (h : ℝ) (j : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (χY h j) := by
  unfold χY; exact χ0_contDiff.comp ((contDiff_const.mul contDiff_id).add contDiff_const)

lemma χY_hasCompactSupport {h : ℝ} (hh : 0 < h) (j : ℕ) : HasCompactSupport (χY h j) := by
  unfold χY
  have : (fun y => χ0 ((-h⁻¹) * y + (1 - j))) = χ0 ∘ (fun y => (-h⁻¹) * y + (1 - j)) := rfl
  rw [this]
  exact χ0_hasCompactSupport.comp_homeomorph
    ((Homeomorph.mulLeft₀ (-h⁻¹) (by simp [hh.ne'])).trans (Homeomorph.addRight _))

def ψY (h : ℝ) (hh : 0 < h) (j : ℕ) : SchwartzMap ℝ ℂ :=
  ((χY_hasCompactSupport hh j).comp_left Complex.ofReal_zero).toSchwartzMap
    (Complex.ofRealCLM.contDiff.comp (χY_contDiff h j))

lemma ψY_apply {h : ℝ} (hh : 0 < h) (j : ℕ) (y : ℝ) : ψY h hh j y = ((χY h j y : ℝ) : ℂ) := rfl

lemma ψY_coe {h : ℝ} (hh : 0 < h) (j : ℕ) :
    (ψY h hh j : ℝ → ℂ) = fun y => (fun z => ((χ0 z : ℝ) : ℂ)) ((-h⁻¹) * y + (1 - j)) := by
  funext y; rfl

/-- `χ0` as a Schwartz function. -/
def ψ0 : SchwartzMap ℝ ℂ :=
  (χ0_hasCompactSupport.comp_left Complex.ofReal_zero).toSchwartzMap
    (Complex.ofRealCLM.contDiff.comp χ0_contDiff)

lemma ψ0_coe : (ψ0 : ℝ → ℂ) = fun z => ((χ0 z : ℝ) : ℂ) := rfl

lemma mom0_ψY {h : ℝ} (hh : 0 < h) (j : ℕ) : Mom 0 (ψY h hh j) = Mom 0 ψ0 := by
  simp only [Mom, pow_zero, one_mul]
  rw [ψY_coe, ψ0_coe]
  exact integral_norm_fourier_affine (fun z => ((χ0 z : ℝ) : ℂ)) (a := -h⁻¹) (1 - j) (by simp [hh.ne'])

lemma tail_ψY {h : ℝ} (hh : 0 < h) (j : ℕ) (V : ℝ) : Tail (ψY h hh j) V = Tail ψ0 (h * V) := by
  unfold Tail
  rw [ψY_coe, ψ0_coe]
  have := integral_tail_fourier_affine (fun z => ((χ0 z : ℝ) : ℂ)) (a := -h⁻¹) (1 - j)
    (by simp [hh.ne']) V
  rw [abs_neg, abs_inv, abs_of_pos hh, div_inv_eq_mul, mul_comm] at this
  exact this

lemma sup_ψY {h : ℝ} (hh : 0 < h) (j : ℕ) (v : ℝ) : ‖𝓕 (ψY h hh j : ℝ → ℂ) v‖ ≤ 2 * h := by
  rw [ψY_coe]
  have e := norm_fourier_affine (fun z => ((χ0 z : ℝ) : ℂ)) (a := -h⁻¹) (1 - j) (by simp [hh.ne']) v
  rw [show (fun y => (fun z => ((χ0 z : ℝ) : ℂ)) ((-h⁻¹) * y + (1 - j))) =
    (fun x => (fun z => ((χ0 z : ℝ) : ℂ)) ((-h⁻¹) * x + (1 - j))) from rfl, e]
  rw [abs_neg, abs_inv, abs_of_pos hh]
  have : ‖𝓕 (fun z => ((χ0 z : ℝ) : ℂ)) (v / -h⁻¹)‖ ≤ 2 := by
    refine (norm_fourier_le _ _).trans ?_
    have hle : ∀ z, ‖((χ0 z : ℝ) : ℂ)‖ ≤ Set.indicator (Set.Icc (0 : ℝ) 2) (fun _ => (1 : ℝ)) z := by
      intro z
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (χ0_nonneg z)]
      by_cases hz : z ∈ Set.Icc (0 : ℝ) 2
      · rw [Set.indicator_of_mem hz]; exact χ0_le_one z
      · rw [Set.indicator_of_notMem hz, χ0_zero_of]
        simp only [Set.mem_Icc, not_and_or, not_le] at hz
        exact hz.elim (fun h => Or.inl h.le) (fun h => Or.inr h.le)
    calc ∫ z, ‖((χ0 z : ℝ) : ℂ)‖ ≤ ∫ z, Set.indicator (Set.Icc (0 : ℝ) 2) (fun _ => (1 : ℝ)) z := by
          apply integral_mono_of_nonneg (Filter.Eventually.of_forall (fun x => norm_nonneg _))
          · exact (continuous_const.integrableOn_Icc).integrable_indicator measurableSet_Icc
          · exact Filter.Eventually.of_forall hle
      _ = 2 := by
          rw [integral_indicator measurableSet_Icc, setIntegral_const]
          simp only [Measure.real, Real.volume_Icc, smul_eq_mul, mul_one]
          norm_num
  have h0 : (0 : ℝ) < h⁻¹⁻¹ := by positivity
  rw [inv_inv] at h0 ⊢
  nlinarith [norm_nonneg (𝓕 (fun z => ((χ0 z : ℝ) : ℂ)) (v / -h⁻¹))]

end R522
end

end S_C7

-- ===== C8 =====
section S_C8

/-! The sign-change model `(c_k, S_{k+1})` and the decay of its characteristic function (original).
Coordinates `j : Fin n` (`n = k + 2`), weights `w j = n - 1 - j` for `c` and `1` for `S`. -/

open Finset Real

noncomputable section

namespace R522

/-- `c`-weights. -/
def wt (n : ℕ) (j : Fin n) : ℝ := (n : ℝ) - 1 - j

def σa (n : ℕ) : ℝ := √(∑ j : Fin n, wt n j ^ 2)

def aw (n : ℕ) (j : Fin n) : ℝ := wt n j / σa n
def bw (n : ℕ) (_j : Fin n) : ℝ := 1 / √(n : ℝ)
def ρw (n : ℕ) : ℝ := ∑ j : Fin n, aw n j * bw n j

lemma sum_wt_sq (n : ℕ) : ∑ j : Fin n, wt n j ^ 2 = ∑ w ∈ range n, (w : ℝ) ^ 2 := by
  simp only [wt]
  rw [Fin.sum_univ_eq_sum_range (fun j => ((n : ℝ) - 1 - j) ^ 2) n]
  rw [← sum_range_reflect]
  apply sum_congr rfl; intro w hw; rw [mem_range] at hw
  congr 1; rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; push_cast; ring

lemma sum_wt (n : ℕ) : ∑ j : Fin n, wt n j = ∑ w ∈ range n, (w : ℝ) := by
  simp only [wt]
  rw [Fin.sum_univ_eq_sum_range (fun j => ((n : ℝ) - 1 - j)) n]
  rw [← sum_range_reflect]
  apply sum_congr rfl; intro w hw; rw [mem_range] at hw
  rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; push_cast; ring

lemma sum_wt_four (n : ℕ) : ∑ j : Fin n, wt n j ^ 4 = ∑ w ∈ range n, (w : ℝ) ^ 4 := by
  simp only [wt]
  rw [Fin.sum_univ_eq_sum_range (fun j => ((n : ℝ) - 1 - j) ^ 4) n]
  rw [← sum_range_reflect]
  apply sum_congr rfl; intro w hw; rw [mem_range] at hw
  congr 1; rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; push_cast; ring

lemma sq6 (n : ℕ) : (∑ w ∈ range n, (w : ℝ) ^ 2) * 6 = (n : ℝ) * (n - 1) * (2 * n - 1) :=
  sum_sq_range_mul_six n

lemma sum_range_cast (n : ℕ) : (∑ w ∈ range n, (w : ℝ)) * 2 = (n : ℝ) * (n - 1) := by
  induction n with
  | zero => simp
  | succ n ih => rw [sum_range_succ, add_mul, ih]; push_cast; ring

lemma sum_four_le (n : ℕ) : ∑ w ∈ range n, (w : ℝ) ^ 4 ≤ (n : ℝ) ^ 5 := by
  calc ∑ w ∈ range n, (w : ℝ) ^ 4 ≤ ∑ _w ∈ range n, (n : ℝ) ^ 4 := by
        apply sum_le_sum; intro w hw; rw [mem_range] at hw
        exact pow_le_pow_left₀ (by positivity) (by exact_mod_cast hw.le) 4
    _ = (n : ℝ) ^ 5 := by simp; ring

lemma σa_sq (n : ℕ) : σa n ^ 2 = ∑ w ∈ range n, (w : ℝ) ^ 2 := by
  rw [σa, Real.sq_sqrt (sum_nonneg (fun _ _ => by positivity)), sum_wt_sq]

lemma σa_sq_eq (n : ℕ) : σa n ^ 2 * 6 = (n : ℝ) * (n - 1) * (2 * n - 1) := by
  rw [σa_sq, sq6]

lemma σa_pos {n : ℕ} (hn : 2 ≤ n) : 0 < σa n := by
  apply Real.sqrt_pos.mpr
  rw [sum_wt_sq]
  apply sum_pos' (fun _ _ => by positivity) ⟨1, by rw [mem_range]; omega, by norm_num⟩

lemma aw_sq {n : ℕ} (hn : 2 ≤ n) : ∑ j, aw n j ^ 2 = 1 := by
  have h : ∑ j, aw n j ^ 2 = (∑ j, wt n j ^ 2) / σa n ^ 2 := by simp only [aw, div_pow, sum_div]
  rw [h, show (∑ j, wt n j ^ 2) = σa n ^ 2 by rw [σa_sq, sum_wt_sq]]
  exact div_self (by have := σa_pos hn; positivity)

lemma bw_sq {n : ℕ} (hn : 2 ≤ n) : ∑ j, bw n j ^ 2 = 1 := by
  simp only [bw, div_pow, one_pow, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [Real.sq_sqrt (by positivity)]
  field_simp

/-- the cosine kernel along an arithmetic progression. -/
lemma Kc_eq (n : ℕ) (u v : ℝ) :
    Kc (aw n) (bw n) u v = ∏ w ∈ range n,
      Real.cos (2 * π * u / σa n * w + 2 * π * v / √(n : ℝ)) := by
  unfold Kc
  simp only [aw, bw, wt]
  rw [Fin.prod_univ_eq_prod_range (fun j => Real.cos (2 * π * (u * (((n : ℝ) - 1 - j) / σa n) +
    v * (1 / √(n : ℝ))))) n]
  · rw [← prod_range_reflect]
    apply prod_congr rfl; intro w hw; rw [mem_range] at hw
    congr 1; rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; push_cast; ring

lemma pi_div_two_le_two : π / 2 ≤ 2 := by linarith [Real.pi_lt_four]

/-- numeric core of case B -/
lemma caseB_num (n m : ℕ) (σ2 u v s t C : ℝ) (hn0 : (0 : ℝ) < n) (hm1 : (n : ℝ) / 40 ≤ m)
    (hσp : 0 < σ2) (hσ2 : σ2 ≤ (n : ℝ) ^ 3 / 3) (hCm : (m : ℝ) ^ 3 / 12 ≤ C)
    (hss : s ^ 2 = 4 * π ^ 2 * u ^ 2 / σ2) (htt : t ^ 2 = 4 * π ^ 2 * v ^ 2 / n) :
    π ^ 2 * (u ^ 2 + v ^ 2) / 4096000 ≤ ((m : ℝ) * t ^ 2 + C * s ^ 2) / 64 := by
  have hpi : 0 ≤ π ^ 2 := by positivity
  have hv2 : 0 ≤ 4 * π ^ 2 * v ^ 2 := by positivity
  have hu2 : 0 ≤ 4 * π ^ 2 * u ^ 2 := by positivity
  have hmn : (1 : ℝ) / 40 ≤ m / n := by rw [le_div_iff₀ hn0]; linarith
  have hT1 : π ^ 2 * v ^ 2 / 10 ≤ (m : ℝ) * t ^ 2 := by
    rw [htt, show (m : ℝ) * (4 * π ^ 2 * v ^ 2 / n) = 4 * π ^ 2 * v ^ 2 * (m / n) by ring]
    have := mul_le_mul_of_nonneg_left hmn hv2
    linarith
  have hm0 : (0 : ℝ) ≤ m := le_trans (by positivity) hm1
  have h1 : 4 * π ^ 2 * u ^ 2 / ((n : ℝ) ^ 3 / 3) ≤ s ^ 2 := by
    rw [hss]; exact div_le_div_of_nonneg_left hu2 hσp hσ2
  have h2 : (n : ℝ) ^ 3 / 64000 ≤ (m : ℝ) ^ 3 := by
    have := pow_le_pow_left₀ (by positivity) hm1 3
    rw [div_pow] at this
    linarith
  have h3 : π ^ 2 * u ^ 2 / 64000 = ((n : ℝ) ^ 3 / 64000) * (4 * π ^ 2 * u ^ 2 / ((n : ℝ) ^ 3 / 3)) / 12 := by
    field_simp; ring
  have hT2 : π ^ 2 * u ^ 2 / 64000 ≤ C * s ^ 2 := by
    rw [h3]
    have hs0 : 0 ≤ 4 * π ^ 2 * u ^ 2 / ((n : ℝ) ^ 3 / 3) := by positivity
    calc ((n : ℝ) ^ 3 / 64000) * (4 * π ^ 2 * u ^ 2 / ((n : ℝ) ^ 3 / 3)) / 12
        ≤ ((m : ℝ) ^ 3) * (4 * π ^ 2 * u ^ 2 / ((n : ℝ) ^ 3 / 3)) / 12 := by gcongr
      _ = ((m : ℝ) ^ 3 / 12) * (4 * π ^ 2 * u ^ 2 / ((n : ℝ) ^ 3 / 3)) := by ring
      _ ≤ C * s ^ 2 := by
          apply mul_le_mul hCm h1 hs0 (le_trans (by positivity) hCm)
  have : π ^ 2 * (u ^ 2 + v ^ 2) / 4096000 ≤ (π ^ 2 * v ^ 2 / 10 + π ^ 2 * u ^ 2 / 64000) / 64 := by
    have : 0 ≤ π ^ 2 * v ^ 2 := by positivity
    have : 0 ≤ π ^ 2 * u ^ 2 := by positivity
    linarith
  linarith

/-- **Decay on the cell outside the box.** -/
theorem Kc_decay {n : ℕ} (hn : 40 ≤ n) {u v R : ℝ}
    (hu : |u| ≤ σa n / 4) (hv : |v| ≤ √(n : ℝ) / 4) (hout : R ^ 2 ≤ u ^ 2 + v ^ 2) :
    |Kc (aw n) (bw n) u v| ≤
      Real.exp (-((n : ℝ) * Real.sin (1 / 2) ^ 2 / 16)) + Real.exp (-(R ^ 2 * (π ^ 2 / 8192000))) := by
  rw [Kc_eq]
  have hσ := σa_pos (show 2 ≤ n by omega)
  have hn0 : (0 : ℝ) < n := by positivity
  set s := 2 * π * u / σa n with hs
  set t := 2 * π * v / √(n : ℝ) with ht
  have hsn : |s| ≤ π / 2 := by
    rw [hs, abs_div, abs_mul, abs_of_pos (by positivity : (0:ℝ) < 2 * π), abs_of_pos hσ,
      div_le_iff₀ hσ]
    nlinarith [Real.pi_pos]
  have htn : |t| ≤ π / 2 := by
    have hsq : (0 : ℝ) < √(n : ℝ) := Real.sqrt_pos.mpr hn0
    rw [ht, abs_div, abs_mul, abs_of_pos (by positivity : (0:ℝ) < 2 * π), abs_of_pos hsq,
      div_le_iff₀ hsq]
    nlinarith [Real.pi_pos]
  have hprod := abs_prod_cos_le (n := n) (fun w => s * w + t)
  refine hprod.trans ?_
  have e1 := Real.exp_pos (-((n : ℝ) * Real.sin (1 / 2) ^ 2 / 16))
  have e2 := Real.exp_pos (-(R ^ 2 * (π ^ 2 / 8192000)))
  by_cases hA : 8 / (n : ℝ) ≤ |s|
  · have := sum_sin_sq_caseA n s t hA (hsn.trans pi_div_two_le_two) (by omega)
    have : Real.exp (-((∑ w ∈ range n, Real.sin (s * w + t) ^ 2) / 2)) ≤
        Real.exp (-((n : ℝ) * Real.sin (1 / 2) ^ 2 / 16)) := by
      apply Real.exp_le_exp.mpr; linarith
    linarith
  · push Not at hA
    set m := n / 20 with hm
    have hm1 : (n : ℝ) / 40 ≤ m := by
      have : 20 * m + 20 ≥ n + 1 := by omega
      have : (20 : ℝ) * m + 20 ≥ n + 1 := by exact_mod_cast this
      have : (40 : ℝ) ≤ n := by exact_mod_cast hn
      linarith
    have hm2 : (m : ℝ) ≤ n / 20 := by
      have : 20 * m ≤ n := by omega
      have : (20 : ℝ) * m ≤ n := by exact_mod_cast this
      linarith
    have hmn : m ≤ n := by omega
    have hsm : |s| * m ≤ 2 / 5 := by
      calc |s| * m ≤ (8 / n) * (n / 20) := by
            apply mul_le_mul hA.le hm2 (by positivity) (by positivity)
        _ = 2 / 5 := by field_simp; ring
    have hB := sum_sin_sq_caseB n m hmn s t (htn.trans (by linarith [Real.pi_lt_d2])) hsm
    -- lower bounds for the two diagonal terms
    have hm2' : 2 ≤ m := by omega
    have hCm : (m : ℝ) ^ 3 / 12 ≤ ∑ w ∈ range m, (w : ℝ) ^ 2 := by
      have := sq6 m
      have hm2r : (2 : ℝ) ≤ m := by exact_mod_cast hm2'
      have hm0 : (0 : ℝ) ≤ m := by positivity
      have key : (m : ℝ) ^ 3 / 12 * 6 ≤ (m : ℝ) * (m - 1) * (2 * m - 1) := by
        nlinarith [mul_nonneg (mul_nonneg hm0 hm0) (sub_nonneg.mpr hm2r)]
      linarith
    have hσ2 : σa n ^ 2 ≤ (n : ℝ) ^ 3 / 3 := by
      have := σa_sq_eq n
      have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
      nlinarith [mul_nonneg (sub_nonneg.mpr hn1) (sub_nonneg.mpr hn1)]
    have hss : s ^ 2 = 4 * π ^ 2 * u ^ 2 / σa n ^ 2 := by rw [hs]; field_simp; ring
    have htt : t ^ 2 = 4 * π ^ 2 * v ^ 2 / n := by
      rw [ht, div_pow, Real.sq_sqrt hn0.le]; ring
    have hcb := caseB_num n m (σa n ^ 2) u v s t (∑ w ∈ range m, (w : ℝ) ^ 2) hn0 hm1
      (by positivity) hσ2 hCm hss htt
    have hsum : R ^ 2 * (π ^ 2 / 4096000) ≤ ∑ w ∈ range n, Real.sin (s * w + t) ^ 2 := by
      have hR : R ^ 2 * (π ^ 2 / 4096000) ≤ π ^ 2 * (u ^ 2 + v ^ 2) / 4096000 := by
        have := mul_le_mul_of_nonneg_right hout (by positivity : (0:ℝ) ≤ π ^ 2 / 4096000)
        linarith
      linarith
    have : Real.exp (-((∑ w ∈ range n, Real.sin (s * w + t) ^ 2) / 2)) ≤
        Real.exp (-(R ^ 2 * (π ^ 2 / 8192000))) := by
      apply Real.exp_le_exp.mpr; linarith
    linarith

/-- the Gaussian kernel outside the box. -/
lemma gk_decay {ρ R u v : ℝ} (hρ : |ρ| ≤ 1) (hout : R ^ 2 ≤ u ^ 2 + v ^ 2) :
    gk ρ u v ≤ Real.exp (-(2 * π ^ 2 * (1 - |ρ|) * R ^ 2)) := by
  unfold gk
  apply Real.exp_le_exp.mpr
  have h1 : (1 - |ρ|) * (u ^ 2 + v ^ 2) ≤ u ^ 2 + 2 * ρ * u * v + v ^ 2 := by
    have : |2 * ρ * u * v| ≤ |ρ| * (u ^ 2 + v ^ 2) := by
      rw [show 2 * ρ * u * v = ρ * (2 * u * v) by ring, abs_mul]
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      rw [abs_le]; constructor <;> nlinarith [sq_nonneg (u + v), sq_nonneg (u - v)]
    have := neg_abs_le (2 * ρ * u * v)
    nlinarith
  have h2 : (1 - |ρ|) * R ^ 2 ≤ (1 - |ρ|) * (u ^ 2 + v ^ 2) :=
    mul_le_mul_of_nonneg_left hout (by linarith)
  nlinarith [Real.pi_pos, sq_nonneg π]

end R522
end

end S_C8

-- ===== C9 =====
section S_C9

/-! Hoeffding for sign sums, the partition of unity, and the pointwise wedge majorant (original). -/

open Finset Real MeasureTheory

noncomputable section

namespace R522

section hoeff
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma sum_signs_rexp (c : ι → ℝ) :
    ∑ ε : ι → ℤˣ, Real.exp (ssum ε c) = ∏ i, (Real.exp (c i) + Real.exp (-c i)) := by
  have : ∀ ε : ι → ℤˣ, Real.exp (ssum ε c) = ∏ i, Real.exp (((ε i : ℤ) : ℝ) * c i) := by
    intro ε; unfold ssum; rw [Real.exp_sum]
  simp_rw [this]
  rw [← Fintype.prod_sum (fun i (u : ℤˣ) => Real.exp (((u : ℤ) : ℝ) * c i))]
  apply prod_congr rfl; intro i _
  rw [show (Finset.univ : Finset ℤˣ) = {1, -1} from by decide, Finset.sum_pair (by decide)]
  simp

lemma EE_exp_ssum_le (c : ι → ℝ) :
    EE (fun ε => Real.exp (ssum ε c)) ≤ Real.exp ((∑ i, c i ^ 2) / 2) := by
  unfold EE
  rw [sum_signs_rexp, div_le_iff₀ (by positivity)]
  have h2 : (2 : ℝ) ^ Fintype.card ι = ∏ _i : ι, (2 : ℝ) := by simp
  rw [h2]
  rw [show Real.exp ((∑ i, c i ^ 2) / 2) * ∏ _i : ι, (2 : ℝ) = ∏ i, (2 * Real.exp (c i ^ 2 / 2)) by
    rw [sum_div, Real.exp_sum, ← prod_mul_distrib]; apply prod_congr rfl; intro i _; ring]
  apply prod_le_prod₀ (fun i _ => by positivity)
  intro i _
  have := Real.cosh_le_exp_half_sq (c i)
  rw [Real.cosh_eq] at this
  linarith

/-- **Hoeffding.** -/
lemma hoeffding (c : ι → ℝ) {T : ℝ} (hT : 0 < T) :
    PP (fun ε => T ≤ |ssum ε c|) ≤ 2 * Real.exp (-(T ^ 2 / (2 * ∑ i, c i ^ 2))) := by
  classical
  set V := ∑ i, c i ^ 2 with hV
  by_cases hV0 : V = 0
  · -- all weights vanish
    have hc : ∀ i, c i = 0 := by
      intro i
      have : c i ^ 2 = 0 := by
        have := Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg (c j)) |>.mp hV0.symm.symm
        exact this i (mem_univ _)
      exact pow_eq_zero_iff (two_ne_zero) |>.mp this
    have : ∀ ε : ι → ℤˣ, ssum ε c = 0 := by intro ε; simp [ssum, hc]
    have : PP (fun ε => T ≤ |ssum ε c|) = 0 := by
      rw [PP_eq]; unfold EE; simp only [this, abs_zero]
      rw [show (fun _ : ι → ℤˣ => if T ≤ (0:ℝ) then (1:ℝ) else 0) = fun _ => 0 by
        funext _; rw [if_neg (by linarith)]]
      simp
    rw [this]; positivity
  have hVp : 0 < V := lt_of_le_of_ne (sum_nonneg (fun _ _ => sq_nonneg _)) (Ne.symm hV0)
  set lam := T / V
  have one_side : ∀ d : ι → ℝ, ∑ i, d i ^ 2 = V →
      PP (fun ε => T ≤ ssum ε d) ≤ Real.exp (-(T ^ 2 / (2 * V))) := by
    intro d hd
    have hm := markov (f := fun ε => Real.exp (lam * ssum ε d)) (fun ε => (Real.exp_pos _).le)
      (Real.exp_pos (lam * T))
    have hmono : PP (fun ε => T ≤ ssum ε d) ≤
        PP (fun ε => Real.exp (lam * T) ≤ Real.exp (lam * ssum ε d)) := by
      apply PP_mono; intro ε h
      apply Real.exp_le_exp.mpr
      exact mul_le_mul_of_nonneg_left h (by positivity)
    have hE : EE (fun ε => Real.exp (lam * ssum ε d)) ≤ Real.exp (lam ^ 2 * V / 2) := by
      have : ∀ ε : ι → ℤˣ, lam * ssum ε d = ssum ε (fun i => lam * d i) := by
        intro ε; unfold ssum; rw [mul_sum]; apply sum_congr rfl; intro i _; ring
      simp_rw [this]
      refine (EE_exp_ssum_le _).trans (le_of_eq ?_)
      congr 1; rw [← hd]; simp only [mul_pow]; rw [← mul_sum]
    calc PP (fun ε => T ≤ ssum ε d) ≤ _ := hmono
      _ ≤ EE (fun ε => Real.exp (lam * ssum ε d)) / Real.exp (lam * T) := hm
      _ ≤ Real.exp (lam ^ 2 * V / 2) / Real.exp (lam * T) := by gcongr
      _ = Real.exp (-(T ^ 2 / (2 * V))) := by
          rw [← Real.exp_sub]; congr 1; simp only [lam]; field_simp; ring
  have h1 := one_side c rfl
  have h2 := one_side (fun i => -c i) (by simp [hV])
  have hsplit : PP (fun ε => T ≤ |ssum ε c|) ≤
      PP (fun ε => T ≤ ssum ε c) + PP (fun ε => T ≤ ssum ε (fun i => -c i)) := by
    refine le_trans (PP_mono (T := fun ε => T ≤ ssum ε c ∨ T ≤ ssum ε (fun i => -c i))
      (fun ε h => ?_)) (PP_or_le _ _)
    have e : ssum ε (fun i => -c i) = -ssum ε c := by unfold ssum; rw [← sum_neg_distrib]; simp
    rw [e]
    rcases le_abs'.mp h with h' | h'
    · right; linarith
    · left; exact h'
  linarith

end hoeff

/-! ### partition of unity -/

lemma sum_χ0 (x : ℝ) (N : ℕ) :
    ∑ j ∈ range N, χ0 (x - j) = Real.smoothTransition x - Real.smoothTransition (x - N) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [sum_range_succ, ih]; unfold χ0; push_cast; ring_nf

lemma sum_χY_le_one (h y : ℝ) (N : ℕ) : ∑ j ∈ range N, χY h j y ≤ 1 := by
  have := sum_χ0 ((-h⁻¹) * y + 1) N
  unfold χY
  have e : ∀ j ∈ range N, χ0 ((-h⁻¹) * y + (1 - j)) = χ0 ((-h⁻¹) * y + 1 - j) := by
    intro j _; ring_nf
  rw [sum_congr rfl e, this]
  have := Real.smoothTransition.le_one ((-h⁻¹) * y + 1)
  have := Real.smoothTransition.nonneg ((-h⁻¹) * y + 1 - N)
  linarith

lemma sum_χY_eq_one {h y : ℝ} (hh : 0 < h) (N : ℕ) (hy0 : y ≤ 0) (hy1 : -((N - 1 : ℝ) * h) ≤ y) :
    ∑ j ∈ range N, χY h j y = 1 := by
  have := sum_χ0 ((-h⁻¹) * y + 1) N
  unfold χY
  have e : ∀ j ∈ range N, χ0 ((-h⁻¹) * y + (1 - j)) = χ0 ((-h⁻¹) * y + 1 - j) := by
    intro j _; ring_nf
  rw [sum_congr rfl e, this]
  have hz0 : 0 ≤ (-h⁻¹) * y := by
    have : 0 ≤ h⁻¹ := by positivity
    nlinarith
  have hz1 : (-h⁻¹) * y ≤ N - 1 := by
    have e : (-h⁻¹) * y = (-y) / h := by field_simp
    rw [e, div_le_iff₀ hh]; linarith
  rw [Real.smoothTransition.one_of_one_le (by linarith),
    Real.smoothTransition.zero_of_nonpos (by linarith)]
  ring

lemma χY_nonneg (h : ℝ) (j : ℕ) (y : ℝ) : 0 ≤ χY h j y := χ0_nonneg _

lemma χY_supp {h y : ℝ} (hh : 0 < h) (j : ℕ) (hpos : 0 < χY h j y) :
    ((j : ℝ) - 1) * h < -y ∧ -y < ((j : ℝ) + 1) * h := by
  unfold χY at hpos
  have h1 : 0 < (-h⁻¹) * y + (1 - j) ∧ (-h⁻¹) * y + (1 - j) < 2 := by
    by_contra hc
    rw [not_and_or, not_lt, not_lt] at hc
    rw [χ0_zero_of hc] at hpos
    exact lt_irrefl _ hpos
  have e : (-h⁻¹) * y = (-y) / h := by field_simp
  rw [e] at h1
  constructor
  · have := h1.1
    have : ((j : ℝ) - 1) < (-y) / h := by linarith
    rwa [lt_div_iff₀ hh] at this
  · have : (-y) / h < (j : ℝ) + 1 := by linarith [h1.2]
    rwa [div_lt_iff₀ hh] at this

end R522
end

end S_C9

-- ===== C10 =====
section S_C10

/-! The Gaussian side of the thin-wedge bound (original). -/

open Finset Real MeasureTheory ProbabilityTheory Set
open scoped ENNReal

noncomputable section

namespace R522

lemma integral_Ioi_mul_exp : ∫ x in Ioi (0 : ℝ), x * Real.exp (-(x ^ 2 / 2)) = 1 := by
  have hderiv : ∀ x ∈ Ici (0 : ℝ), HasDerivAt (fun x => -Real.exp (-(x ^ 2 / 2)))
      (x * Real.exp (-(x ^ 2 / 2))) x := by
    intro x _
    have h1 : HasDerivAt (fun x : ℝ => -(x ^ 2 / 2)) (-x) x := by
      have := ((hasDerivAt_pow 2 x).div_const 2).neg
      exact this.congr_deriv (by norm_num)
    have h2 := h1.exp.neg
    exact h2.congr_deriv (by ring)
  have hint : IntegrableOn (fun x : ℝ => x * Real.exp (-(x ^ 2 / 2))) (Ioi 0) := by
    have := integrable_mul_exp_neg_mul_sq (show (0:ℝ) < 1 / 2 by norm_num)
    refine (this.congr (Filter.Eventually.of_forall (fun x => ?_))).integrableOn
    simp only; congr 2; ring
  have htend : Filter.Tendsto (fun x : ℝ => -Real.exp (-(x ^ 2 / 2))) Filter.atTop (nhds 0) := by
    have : Filter.Tendsto (fun x : ℝ => -(x ^ 2 / 2)) Filter.atTop Filter.atBot := by
      apply Filter.tendsto_neg_atTop_atBot.comp
      exact (Filter.tendsto_pow_atTop two_ne_zero).atTop_div_const (by norm_num)
    have := (Real.tendsto_exp_atBot.comp this).neg
    rw [neg_zero] at this
    exact this
  have hcont : ContinuousWithinAt (fun x : ℝ => -Real.exp (-(x ^ 2 / 2))) (Ici 0) 0 :=
    (by fun_prop : Continuous (fun x : ℝ => -Real.exp (-(x ^ 2 / 2)))).continuousWithinAt
  rw [integral_Ioi_of_hasDerivAt_of_tendsto hcont (fun x hx => hderiv x (mem_Ici.mpr (le_of_lt hx))) hint htend]
  simp

lemma gaussPDF_eq (x : ℝ) : gaussianPDFReal 0 1 x = (√(2 * π))⁻¹ * Real.exp (-(x ^ 2 / 2)) := by
  simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero]
  congr 2; ring

lemma integral_γ_pos_part : ∫ z, max z 0 ∂γ = 1 / √(2 * π) := by
  rw [integral_gaussianReal_eq_integral_smul one_ne_zero]
  simp only [smul_eq_mul]
  have e : ∀ z : ℝ, gaussianPDFReal 0 1 z * max z 0 =
      Set.indicator (Ioi 0) (fun z => (√(2 * π))⁻¹ * (z * Real.exp (-(z ^ 2 / 2)))) z := by
    intro z
    by_cases hz : 0 < z
    · rw [indicator_of_mem (show z ∈ Ioi (0:ℝ) from hz), max_eq_left hz.le, gaussPDF_eq]; ring
    · rw [indicator_of_notMem (show z ∉ Ioi (0:ℝ) from hz), max_eq_right (not_lt.mp hz)]; ring
  simp_rw [e]
  rw [integral_indicator measurableSet_Ioi, integral_const_mul, integral_Ioi_mul_exp]
  ring

lemma integral_γ_neg_part : ∫ z, max (-z) 0 ∂γ = 1 / √(2 * π) := by
  have := integral_map (μ := γ) (f := fun z : ℝ => max z 0) (φ := fun z => -z)
    (by fun_prop) (by fun_prop)
  rw [map_neg_γ, integral_γ_pos_part] at this
  rw [this]

lemma γ_real_Icc_le (a b : ℝ) : γ.real (Icc a b) ≤ max (b - a) 0 / √(2 * π) := by
  by_cases hab : a ≤ b
  · rw [max_eq_left (by linarith)]; exact gauss_strip a b hab
  · rw [Icc_eq_empty hab]; simp only [measureReal_empty]
    exact div_nonneg (le_max_right _ _) (by positivity)

/-- `E[|Z|; Z ≤ z₀] ≤ (1 + z₀²)/√(2π)` for `z₀ ≥ 0`. -/
lemma integral_abs_le_z0 {z0 : ℝ} (hz0 : 0 ≤ z0) :
    ∫ z, Set.indicator (Iic z0) (fun z => |z|) z ∂γ ≤ (1 + z0 ^ 2) / √(2 * π) := by
  have hpt : ∀ z, Set.indicator (Iic z0) (fun z => |z|) z ≤
      max (-z) 0 + z0 * Set.indicator (Icc 0 z0) (fun _ => (1 : ℝ)) z := by
    intro z
    by_cases h1 : z ≤ z0
    · rw [indicator_of_mem (show z ∈ Iic z0 from h1)]
      by_cases h2 : 0 ≤ z
      · rw [indicator_of_mem (show z ∈ Icc 0 z0 from ⟨h2, h1⟩), abs_of_nonneg h2]
        have : max (-z) 0 = 0 := max_eq_right (by linarith)
        rw [this]; linarith
      · rw [indicator_of_notMem (fun h : z ∈ Icc 0 z0 => h2 h.1), abs_of_neg (not_le.mp h2)]
        rw [max_eq_left (by linarith)]; simp
    · rw [indicator_of_notMem (show z ∉ Iic z0 from h1)]
      have : 0 ≤ max (-z) 0 := le_max_right _ _
      have : 0 ≤ z0 * Set.indicator (Icc 0 z0) (fun _ => (1 : ℝ)) z :=
        mul_nonneg hz0 (indicator_nonneg (fun _ _ => zero_le_one) _)
      linarith
  have i1 : Integrable (fun z : ℝ => max (-z) 0) γ := by
    have hid : Integrable (fun z : ℝ => z) γ := (memLp_id_gaussianReal 1).integrable le_rfl
    have : Integrable (fun z : ℝ => -z) γ := hid.neg
    exact this.sup (integrable_const 0)
  have i2 : Integrable (fun z : ℝ => z0 * Set.indicator (Icc 0 z0) (fun _ => (1 : ℝ)) z) γ :=
    ((integrable_const (1 : ℝ)).indicator measurableSet_Icc).const_mul z0
  have i0 : Integrable (fun z : ℝ => Set.indicator (Iic z0) (fun z => |z|) z) γ := by
    have : Integrable (fun z : ℝ => |z|) γ := by
      have hid : Integrable (fun z : ℝ => z) γ := (memLp_id_gaussianReal 1).integrable le_rfl
      exact hid.abs
    exact this.indicator measurableSet_Iic
  calc ∫ z, Set.indicator (Iic z0) (fun z => |z|) z ∂γ
      ≤ ∫ z, (max (-z) 0 + z0 * Set.indicator (Icc 0 z0) (fun _ => (1 : ℝ)) z) ∂γ :=
        integral_mono i0 (i1.add i2) hpt
    _ = 1 / √(2 * π) + z0 * γ.real (Icc 0 z0) := by
        rw [integral_add i1 i2, integral_γ_neg_part, integral_const_mul,
          integral_indicator measurableSet_Icc, setIntegral_const, smul_eq_mul, mul_one]
    _ ≤ 1 / √(2 * π) + z0 * (z0 / √(2 * π)) := by
        gcongr
        exact gauss_strip 0 z0 hz0 |>.trans (by rw [sub_zero])
    _ = (1 + z0 ^ 2) / √(2 * π) := by ring

end R522
end

end S_C10

-- ===== C11 =====
section S_C11

/-! The thin-wedge estimate: real form of `llt_two`, and the Gaussian main term (original). -/

open Finset Real MeasureTheory ProbabilityTheory Set FourierTransform
open scoped ENNReal

noncomputable section

namespace R522

/-- `llt_two` for real-valued Schwartz functions. -/
theorem llt_real {ι : Type*} [Fintype ι] [DecidableEq ι] (ψ₁ ψ₂ : SchwartzMap ℝ ℂ)
    (f₁ f₂ : ℝ → ℝ) (h₁ : ∀ x, ψ₁ x = ((f₁ x : ℝ) : ℂ)) (h₂ : ∀ x, ψ₂ x = ((f₂ x : ℝ) : ℂ))
    (a b : ι → ℝ) (ρ : ℝ) (ha : ∑ i, a i ^ 2 = 1) (hb : ∑ i, b i ^ 2 = 1)
    (hab : ∑ i, a i * b i = ρ) {R U V η M₁ M₂ : ℝ} (hR : 0 ≤ R) (hU : 0 ≤ U) (hη : 0 ≤ η)
    (hM₁ : ∀ u, ‖𝓕 (ψ₁ : ℝ → ℂ) u‖ ≤ M₁) (hM₂ : ∀ v, ‖𝓕 (ψ₂ : ℝ → ℂ) v‖ ≤ M₂)
    (hdec : ∀ u v, |u| ≤ U → |v| ≤ V → (R < |u| ∨ R < |v|) → |Kc a b u v| + gk ρ u v ≤ η) :
    EE (fun ε => f₁ (ssum ε a) * f₂ (ssum ε b))
      ≤ ∫ z, f₁ z.1 * f₂ (ρ * z.1 + √(1 - ρ ^ 2) * z.2) ∂(γ.prod γ)
        + ((M₁ * (16 * (2 * π) ^ 4 * R ^ 4 * ((∑ i, a i ^ 4) + ∑ i, b i ^ 4))) * (2 * R) * (M₂ * (2 * R))
          + (M₁ * η) * (2 * U) * Mom 0 ψ₂ + 2 * Tail ψ₁ U * Mom 0 ψ₂ + 2 * Mom 0 ψ₁ * Tail ψ₂ V) := by
  have hρ := abs_rho_le a b ρ ha hb hab
  have h := llt_two ψ₁ ψ₂ a b ρ ha hb hab hR hU hη hM₁ hM₂ hdec
  have hσ : √(1 - ρ ^ 2) ^ 2 = 1 - ρ ^ 2 := Real.sq_sqrt (by linarith)
  have hG := gauss_two ψ₁ ψ₂ ρ (√(1 - ρ ^ 2))
  have hk : ∀ u v : ℝ, Complex.exp (-(2 * π ^ 2 * ((u + ρ * v) ^ 2 + √(1 - ρ ^ 2) ^ 2 * v ^ 2) : ℝ))
      = (gk ρ u v : ℂ) := by
    intro u v; unfold gk; rw [hσ, Complex.ofReal_exp]; congr 1; push_cast; ring
  simp_rw [hk] at hG
  rw [← hG] at h
  simp only [h₁, h₂] at h
  have e1 : (∑ ε : ι → ℤˣ, ((f₁ (ssum ε a) : ℝ) : ℂ) * ((f₂ (ssum ε b) : ℝ) : ℂ)) / 2 ^ Fintype.card ι
      = ((EE (fun ε => f₁ (ssum ε a) * f₂ (ssum ε b)) : ℝ) : ℂ) := by
    unfold EE; push_cast; rfl
  have e2 : ∫ z, ((f₁ z.1 : ℝ) : ℂ) * ((f₂ (ρ * z.1 + √(1 - ρ ^ 2) * z.2) : ℝ) : ℂ) ∂(γ.prod γ)
      = ((∫ z, f₁ z.1 * f₂ (ρ * z.1 + √(1 - ρ ^ 2) * z.2) ∂(γ.prod γ) : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]; push_cast; rfl
  rw [e1, e2, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] at h
  linarith [le_abs_self (EE (fun ε => f₁ (ssum ε a) * f₂ (ssum ε b)) -
    ∫ z, f₁ z.1 * f₂ (ρ * z.1 + √(1 - ρ ^ 2) * z.2) ∂(γ.prod γ))]

/-! ### the Gaussian main term -/

/-- the `x`-window function. -/
def Gw (e σ h t : ℝ) : ℝ := e * (1 + 4 * e) * (σ * |t| + 2 * h)

def Bset (e σ h δ z0 : ℝ) : Set (ℝ × ℝ) :=
  {z | z.2 ≤ z0 ∧ -δ * Gw e σ h z.2 ≤ z.1 ∧ z.1 ≤ (1 + δ) * Gw e σ h z.2}

lemma Bset_meas (e σ h δ z0 : ℝ) : MeasurableSet (Bset e σ h δ z0) := by
  unfold Bset Gw
  simp only [Set.setOf_and]
  apply MeasurableSet.inter (measurableSet_le measurable_snd measurable_const)
  apply MeasurableSet.inter
  · exact measurableSet_le (by fun_prop) measurable_fst
  · exact measurableSet_le measurable_fst (by fun_prop)

/-- the product measure of the window set. -/
lemma Bset_measure {e σ h δ z0 : ℝ} (he : 0 ≤ e) (hσ : 0 ≤ σ) (hh : 0 ≤ h) (hδ : 0 ≤ δ)
    (hz0 : 0 ≤ z0) :
    (γ.prod γ).real (Bset e σ h δ z0) ≤
      (1 + 2 * δ) / √(2 * π) * (e * (1 + 4 * e)) * (σ * (1 + z0 ^ 2) / √(2 * π) + 2 * h) := by
  have hm := Bset_meas e σ h δ z0
  set c := (1 + 2 * δ) / √(2 * π) with hc
  have hc0 : 0 ≤ c := by positivity
  -- sections
  have hsec : ∀ t, γ ((fun x => (x, t)) ⁻¹' Bset e σ h δ z0) ≤
      ENNReal.ofReal (Set.indicator (Iic z0) (fun t => c * Gw e σ h t) t) := by
    intro t
    by_cases ht : t ≤ z0
    · have : (fun x => (x, t)) ⁻¹' Bset e σ h δ z0 = Icc (-δ * Gw e σ h t) ((1 + δ) * Gw e σ h t) := by
        ext x; simp [Bset, ht]
      rw [this, indicator_of_mem (show t ∈ Iic z0 from ht)]
      have hG : 0 ≤ Gw e σ h t := by unfold Gw; positivity
      have := γ_real_Icc_le (-δ * Gw e σ h t) ((1 + δ) * Gw e σ h t)
      rw [show (1 + δ) * Gw e σ h t - -δ * Gw e σ h t = (1 + 2 * δ) * Gw e σ h t by ring,
        max_eq_left (by positivity)] at this
      rw [← ENNReal.ofReal_toReal (measure_ne_top γ _)]
      apply ENNReal.ofReal_le_ofReal
      refine this.trans (le_of_eq ?_)
      rw [hc]; ring
    · have : (fun x => (x, t)) ⁻¹' Bset e σ h δ z0 = ∅ := by
        ext x; simp [Bset, ht]
      rw [this, measure_empty]; exact bot_le
  have hint : Integrable (fun t => Set.indicator (Iic z0) (fun t => c * Gw e σ h t) t) γ := by
    have hid : Integrable (fun z : ℝ => z) γ := (memLp_id_gaussianReal 1).integrable le_rfl
    have h2 : Integrable (fun t : ℝ => c * Gw e σ h t) γ := by
      have h3 := ((hid.abs.const_mul σ).add (integrable_const (2 * h))).const_mul (c * (e * (1 + 4 * e)))
      refine h3.congr (Filter.Eventually.of_forall (fun t => ?_))
      simp only [Gw, Pi.add_apply]; ring
    exact h2.indicator measurableSet_Iic
  have hnonneg : ∀ t, 0 ≤ Set.indicator (Iic z0) (fun t => c * Gw e σ h t) t := by
    intro t; apply indicator_nonneg; intro t _; unfold Gw; positivity
  have hmeas : (γ.prod γ) (Bset e σ h δ z0) ≤
      ENNReal.ofReal (∫ t, Set.indicator (Iic z0) (fun t => c * Gw e σ h t) t ∂γ) := by
    rw [Measure.prod_apply_symm hm, ofReal_integral_eq_lintegral_ofReal hint
      (Filter.Eventually.of_forall hnonneg)]
    exact lintegral_mono hsec
  have hreal : (γ.prod γ).real (Bset e σ h δ z0) ≤
      ∫ t, Set.indicator (Iic z0) (fun t => c * Gw e σ h t) t ∂γ := by
    rw [Measure.real]
    exact ENNReal.toReal_le_of_le_ofReal (integral_nonneg hnonneg) hmeas
  refine hreal.trans ?_
  -- integrate
  have e1 : ∀ t, Set.indicator (Iic z0) (fun t => c * Gw e σ h t) t =
      c * (e * (1 + 4 * e)) * (σ * Set.indicator (Iic z0) (fun t => |t|) t +
        2 * h * Set.indicator (Iic z0) (fun _ => (1 : ℝ)) t) := by
    intro t; by_cases ht : t ∈ Iic z0
    · simp only [indicator_of_mem ht, Gw]; ring
    · simp only [indicator_of_notMem ht]; ring
  simp_rw [e1]
  have hid : Integrable (fun z : ℝ => z) γ := (memLp_id_gaussianReal 1).integrable le_rfl
  have i1 : Integrable (fun t => Set.indicator (Iic z0) (fun t => |t|) t) γ :=
    hid.abs.indicator measurableSet_Iic
  have i2 : Integrable (fun t => Set.indicator (Iic z0) (fun _ => (1 : ℝ)) t) γ :=
    (integrable_const _).indicator measurableSet_Iic
  rw [integral_const_mul, integral_add (i1.const_mul σ) (i2.const_mul (2 * h)), integral_const_mul,
    integral_const_mul]
  have hA := integral_abs_le_z0 hz0
  have hB : ∫ t, Set.indicator (Iic z0) (fun _ => (1 : ℝ)) t ∂γ ≤ 1 := by
    rw [integral_indicator measurableSet_Iic, setIntegral_const, smul_eq_mul, mul_one]
    exact measureReal_le_one
  have hE : 0 ≤ c * (e * (1 + 4 * e)) := by positivity
  rw [hc] at hE ⊢
  apply mul_le_mul_of_nonneg_left _ hE
  have : σ * ∫ t, Set.indicator (Iic z0) (fun t => |t|) t ∂γ ≤ σ * ((1 + z0 ^ 2) / √(2 * π)) :=
    mul_le_mul_of_nonneg_left hA hσ
  have : 2 * h * ∫ t, Set.indicator (Iic z0) (fun _ => (1 : ℝ)) t ∂γ ≤ 2 * h * 1 :=
    mul_le_mul_of_nonneg_left hB (by positivity)
  calc σ * ∫ t, Set.indicator (Iic z0) (fun t => |t|) t ∂γ + 2 * h * ∫ t, Set.indicator (Iic z0) (fun _ => (1 : ℝ)) t ∂γ
      ≤ σ * ((1 + z0 ^ 2) / √(2 * π)) + 2 * h * 1 := by linarith
    _ = σ * (1 + z0 ^ 2) / √(2 * π) + 2 * h := by ring

end R522
end

end S_C11


end
