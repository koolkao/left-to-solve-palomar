/-
Copyright 2026 Ming-Chih Kao. Licensed under the Apache License, Version 2.0;
see the LICENSE file at the root of this repository.
-/
module

public import E521.Part3

/-! Part of the proof of Erdős 521 (see `E521/Part1.lean` for the port notes): sections C12–D3 of the
merged Left to Solve file `proofs/erdos-521.lean`. -/

@[expose] public section

-- ===== C12 =====
section S_C12

/-! The thin-wedge bound for the sign-change model, with explicit error terms (original). -/

open Finset Real MeasureTheory ProbabilityTheory Set FourierTransform

noncomputable section

namespace R522

/-- shell scale -/
def lamj (e h : ℝ) (j : ℕ) : ℝ := e * (j + 1) * h

/-- the cell decay constant -/
def ηc (n : ℕ) (R ρ : ℝ) : ℝ :=
  Real.exp (-((n : ℝ) * Real.sin (1 / 2) ^ 2 / 16)) + Real.exp (-(R ^ 2 * (π ^ 2 / 8192000)))
    + Real.exp (-(2 * π ^ 2 * (1 - |ρ|) * R ^ 2))

/-- the error of shell `j`. -/
def Errj (n : ℕ) (e h δ R : ℝ) (j : ℕ) : ℝ :=
  (lamj e h j * (1 + 2 * δ) * (16 * (2 * π) ^ 4 * R ^ 4 *
      ((∑ i : Fin n, aw n i ^ 4) + ∑ i : Fin n, bw n i ^ 4))) * (2 * R) * (2 * h * (2 * R))
    + (lamj e h j * (1 + 2 * δ) * ηc n R (ρw n)) * (2 * (σa n / 4)) * Mom 0 ψ0
    + 2 * (if hδ : 0 < δ then Tail (Sb 0 1 δ one_pos hδ) (lamj e h j * (σa n / 4)) else 0) * Mom 0 ψ0
    + 2 * (if hδ : 0 < δ then Mom 0 (Sb 0 1 δ one_pos hδ) else 0) * Tail ψ0 (h * (√(n : ℝ) / 4))

/-- the Gaussian main term. -/
def GM (e σ h δ : ℝ) : ℝ :=
  (1 + 2 * δ) / √(2 * π) * (e * (1 + 4 * e)) * (σ * (1 + (2 * h / σ) ^ 2) / √(2 * π) + 2 * h)

lemma abs_ρw_le {n : ℕ} (hn : 2 ≤ n) : |ρw n| ≤ 1 := by
  have := abs_rho_le (aw n) (bw n) (ρw n) (aw_sq hn) (bw_sq hn) rfl
  rw [abs_le]; constructor <;> nlinarith [sq_nonneg (ρw n + 1), sq_nonneg (ρw n - 1)]

lemma χY_le_one' (h : ℝ) (j : ℕ) (y : ℝ) : χY h j y ≤ 1 := χ0_le_one _

lemma mem_Bset_of {e σ h δ ρ : ℝ} {j : ℕ} {z : ℝ × ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hh : 0 < h)
    (he0 : 0 < e) (he : e ≤ 1 / 16) (hσ0 : 0 < σ) (hρ1 : |ρ| ≤ 1) (hlam : 0 < lamj e h j)
    (hF : 0 < bb 0 (lamj e h j) (lamj e h j * δ) hlam (mul_pos hlam hδ) z.1)
    (hχ : 0 < χY h j (ρ * z.1 + σ * z.2)) : z ∈ Bset e σ h δ (2 * h / σ) := by
  obtain ⟨x, t⟩ := z
  simp only at hF hχ
  set lam := lamj e h j with hlam_def
  have hs := χY_supp hh j hχ
  have hx : x ∈ Ioo (0 - lam * δ) (lam + lam * δ) := by
    by_contra hc
    rw [bb_zero _ _ hc] at hF; exact lt_irrefl _ hF
  simp only [zero_sub, Set.mem_Ioo] at hx
  set W := σ * |t| + 2 * h with hW
  have hW0 : 0 ≤ W := by positivity
  have hy : |ρ * x + σ * t| ≤ |x| + σ * |t| := by
    calc |ρ * x + σ * t| ≤ |ρ * x| + |σ * t| := abs_add_le _ _
      _ = |ρ| * |x| + σ * |t| := by rw [abs_mul, abs_mul, abs_of_pos hσ0]
      _ ≤ 1 * |x| + σ * |t| := by gcongr
      _ = |x| + σ * |t| := by ring
  have hlam1 : lam ≤ e * (|x| + W) := by
    have h1 : lam = e * (((j : ℝ) + 1) * h) := by rw [hlam_def, lamj]; ring
    have h2 : ((j : ℝ) + 1) * h ≤ -(ρ * x + σ * t) + 2 * h := by linarith [hs.1]
    have h3 : -(ρ * x + σ * t) ≤ |x| + σ * |t| := by
      have := neg_abs_le (ρ * x + σ * t); linarith [neg_le_abs (ρ * x + σ * t)]
    rw [h1]; apply mul_le_mul_of_nonneg_left _ he0.le; linarith
  have hxabs : |x| < 2 * lam := by
    rw [abs_lt]; constructor
    · nlinarith
    · nlinarith
  have hxW : |x| ≤ 4 * e * W := by
    have : |x| < 2 * e * (|x| + W) := by linarith
    have h7 : |x| * (1 - 2 * e) < 2 * e * W := by nlinarith
    have h8 : 0 < 1 - 2 * e := by linarith
    by_contra hc; push Not at hc
    have : 4 * e * W * (1 - 2 * e) ≤ |x| * (1 - 2 * e) := mul_le_mul_of_nonneg_right hc.le h8.le
    nlinarith
  have hlamG : lam ≤ Gw e σ h t := by
    unfold Gw
    rw [← hW]
    calc lam ≤ e * (|x| + W) := hlam1
      _ ≤ e * (4 * e * W + W) := by gcongr
      _ = e * (1 + 4 * e) * W := by ring
  have hG0 : 0 ≤ Gw e σ h t := le_trans hlam.le hlamG
  refine ⟨?_, ?_, ?_⟩
  · -- t ≤ 2h/σ
    simp only
    rw [le_div_iff₀ hσ0]
    have hy1 : ρ * x + σ * t < h := by
      have : ((j : ℝ) - 1) * h ≥ -h := by
        have : (0 : ℝ) ≤ j := by positivity
        nlinarith
      linarith [hs.1]
    have hρx : -(ρ * x) ≤ |x| := by
      have := neg_abs_le (ρ * x)
      have : |ρ * x| ≤ |x| := by rw [abs_mul]; nlinarith [abs_nonneg x]
      linarith [neg_le_abs (ρ * x)]
    by_cases ht : t ≤ 0
    · nlinarith
    · push Not at ht
      have : σ * |t| = σ * t := by rw [abs_of_pos ht]
      have : σ * t < h + 4 * e * (σ * t + 2 * h) := by
        have : σ * t < h + |x| := by linarith
        nlinarith
      nlinarith
  · simp only
    have := mul_le_mul_of_nonneg_right hlamG hδ.le
    linarith [hx.1]
  · simp only
    have := mul_le_mul_of_nonneg_right hlamG (show (0:ℝ) ≤ 1 + δ by linarith)
    linarith [hx.2]

/-- **Thin-wedge bound.** -/
theorem wedge_bound {n : ℕ} (hn : 40 ≤ n) {δ h R : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hh : 0 < h)
    (hR : 0 ≤ R) (N : ℕ) (hN : 1 ≤ N)
    (he : √(n : ℝ) / σa n ≤ 1 / 16) (hσ : 0 < 1 - ρw n ^ 2) :
    PP (fun ε : Fin n → ℤˣ => 0 ≤ ssum ε (aw n) ∧ ssum ε (aw n) < -(√(n : ℝ) / σa n) * ssum ε (bw n))
      ≤ GM (√(n : ℝ) / σa n) (√(1 - ρw n ^ 2)) h δ + ∑ j ∈ range N, Errj n (√(n : ℝ) / σa n) h δ R j
        + 2 * Real.exp (-(((N : ℝ) - 1) * h) ^ 2 / 2) := by
  classical
  set e := √(n : ℝ) / σa n with he_def
  set ρ := ρw n with hρ_def
  set σ := √(1 - ρ ^ 2) with hσ_def
  have hn2 : 2 ≤ n := by omega
  have hσa := σa_pos hn2
  have hn0 : (0 : ℝ) < n := by positivity
  have he0 : 0 < e := by positivity
  have hσ0 : 0 < σ := Real.sqrt_pos.mpr hσ
  have hρ1 := abs_ρw_le hn2
  have hlam : ∀ j : ℕ, 0 < lamj e h j := fun j => by unfold lamj; positivity
  set X := fun ε : Fin n → ℤˣ => ssum ε (aw n)
  set Y := fun ε : Fin n → ℤˣ => ssum ε (bw n)
  let F : ℕ → ℝ → ℝ := fun j x => bb 0 (lamj e h j) (lamj e h j * δ) (hlam j) (mul_pos (hlam j) hδ) x
  -- (1) pointwise majorant
  have hmaj : ∀ ε : Fin n → ℤˣ, (if 0 ≤ X ε ∧ X ε < -e * Y ε then (1 : ℝ) else 0) ≤
      (∑ j ∈ range N, F j (X ε) * χY h j (Y ε)) +
        (if ((N : ℝ) - 1) * h ≤ |Y ε| then (1 : ℝ) else 0) := by
    intro ε
    have hsum0 : 0 ≤ ∑ j ∈ range N, F j (X ε) * χY h j (Y ε) :=
      sum_nonneg (fun j _ => mul_nonneg (bb_nonneg _ _ _ _ _ _) (χY_nonneg _ _ _))
    split_ifs with h1 h2 h2
    · linarith
    · -- in the wedge and not in the tail
      have hY0 : Y ε ≤ 0 := by
        have := h1.1; have := h1.2
        by_contra hc; push Not at hc
        have : -e * Y ε < 0 := by nlinarith
        linarith
      have hYN : -(((N : ℝ) - 1) * h) ≤ Y ε := by
        push Not at h2
        have := neg_abs_le (Y ε)
        linarith
      have hpart := sum_χY_eq_one hh N hY0 hYN
      have : ∑ j ∈ range N, F j (X ε) * χY h j (Y ε) = ∑ j ∈ range N, χY h j (Y ε) := by
        apply sum_congr rfl; intro j _
        by_cases hc : 0 < χY h j (Y ε)
        · have hs := χY_supp hh j hc
          have hX : X ε ∈ Icc 0 (lamj e h j) := by
            constructor
            · exact h1.1
            · have : X ε ≤ e * (-Y ε) := by linarith [h1.2]
              unfold lamj
              have : e * (-Y ε) ≤ e * (((j : ℝ) + 1) * h) := mul_le_mul_of_nonneg_left hs.2.le he0.le
              nlinarith
          have : F j (X ε) = 1 := by
            simp only [F]; exact bb_one _ _ (by simpa using hX)
          rw [this, one_mul]
        · have : χY h j (Y ε) = 0 := le_antisymm (not_lt.mp hc) (χY_nonneg _ _ _)
          rw [this, mul_zero]
      rw [this, hpart]; linarith
    · linarith
    · linarith
  -- (2) to expectations
  have hPP : PP (fun ε : Fin n → ℤˣ => 0 ≤ X ε ∧ X ε < -e * Y ε) ≤
      (∑ j ∈ range N, EE (fun ε => F j (X ε) * χY h j (Y ε))) +
        PP (fun ε : Fin n → ℤˣ => ((N : ℝ) - 1) * h ≤ |Y ε|) := by
    rw [PP_eq, PP_eq, ← EE_sum, ← EE_add]
    exact EE_mono hmaj
  -- (3) each shell
  have hshell : ∀ j ∈ range N, EE (fun ε => F j (X ε) * χY h j (Y ε)) ≤
      (∫ z, F j z.1 * χY h j (ρ * z.1 + σ * z.2) ∂(γ.prod γ)) + Errj n e h δ R j := by
    intro j _
    have hU : (0 : ℝ) ≤ σa n / 4 := by positivity
    have hη : 0 ≤ ηc n R ρ := by unfold ηc; positivity
    have hdec : ∀ u v, |u| ≤ σa n / 4 → |v| ≤ √(n : ℝ) / 4 → (R < |u| ∨ R < |v|) →
        |Kc (aw n) (bw n) u v| + gk ρ u v ≤ ηc n R ρ := by
      intro u v hu hv hout
      have hout' : R ^ 2 ≤ u ^ 2 + v ^ 2 := by
        rcases hout with h' | h'
        · have : R ^ 2 ≤ |u| ^ 2 := pow_le_pow_left₀ hR h'.le 2
          rw [sq_abs] at this; nlinarith [sq_nonneg v]
        · have : R ^ 2 ≤ |v| ^ 2 := pow_le_pow_left₀ hR h'.le 2
          rw [sq_abs] at this; nlinarith [sq_nonneg u]
      have h1 := Kc_decay hn hu hv hout'
      have h2 := gk_decay hρ1 hout'
      unfold ηc; linarith
    have hM1 := sup_ψX (hlam j) hδ
    have hM2 := sup_ψY hh j
    have key := llt_real (ψX (lamj e h j) δ (hlam j) hδ) (ψY h hh j) (F j) (χY h j)
      (fun x => by simp only [ψX, Sb_apply, F]) (fun y => ψY_apply hh j y)
      (aw n) (bw n) ρ (aw_sq hn2) (bw_sq hn2) rfl hR hU hη hM1 hM2 hdec
    refine key.trans (le_of_eq ?_)
    unfold Errj
    rw [mom0_ψY, tail_ψY, tail_ψX, mom0_ψX, dif_pos hδ, dif_pos hδ]
  -- (4) the Gaussian sum
  have hgauss : ∑ j ∈ range N, ∫ z, F j z.1 * χY h j (ρ * z.1 + σ * z.2) ∂(γ.prod γ) ≤
      GM e σ h δ := by
    have hint : ∀ j ∈ range N, Integrable (fun z : ℝ × ℝ => F j z.1 * χY h j (ρ * z.1 + σ * z.2))
        (γ.prod γ) := by
      intro j _
      refine Integrable.mono' (integrable_const (1 : ℝ)) ?_ (Filter.Eventually.of_forall (fun z => ?_))
      · exact (((bb _ _ _ _ _).continuous.comp continuous_fst).mul
          ((χY_contDiff h j).continuous.comp (by fun_prop))).aestronglyMeasurable
      · rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (bb_nonneg _ _ _ _ _ _) (χY_nonneg _ _ _))]
        calc F j z.1 * χY h j (ρ * z.1 + σ * z.2) ≤ 1 * 1 :=
              mul_le_mul (bb_le_one _ _ _ _ _ _) (χY_le_one' h j _) (χY_nonneg _ _ _) zero_le_one
          _ = 1 := by ring
    rw [← integral_finsetSum _ hint]
    set f := fun z : ℝ × ℝ => ∑ j ∈ range N, F j z.1 * χY h j (ρ * z.1 + σ * z.2)
    have hf_cont : Continuous f := by
      apply continuous_finsetSum; intro j _
      exact ((bb _ _ _ _ _).continuous.comp continuous_fst).mul
        ((χY_contDiff h j).continuous.comp (by fun_prop))
    have hf0 : ∀ z, 0 ≤ f z := fun z =>
      sum_nonneg (fun j _ => mul_nonneg (bb_nonneg _ _ _ _ _ _) (χY_nonneg _ _ _))
    have hf1 : ∀ z, f z ≤ 1 := by
      intro z
      calc f z ≤ ∑ j ∈ range N, χY h j (ρ * z.1 + σ * z.2) := by
            apply sum_le_sum; intro j _
            have := bb_le_one 0 (lamj e h j) (lamj e h j * δ) (hlam j) (mul_pos (hlam j) hδ) z.1
            have := χY_nonneg h j (ρ * z.1 + σ * z.2)
            calc F j z.1 * χY h j (ρ * z.1 + σ * z.2) ≤ 1 * χY h j (ρ * z.1 + σ * z.2) := by
                  apply mul_le_mul_of_nonneg_right (bb_le_one _ _ _ _ _ _) this
              _ = _ := one_mul _
        _ ≤ 1 := sum_χY_le_one h _ N
    have hfB : ∀ z, z ∉ Bset e σ h δ (2 * h / σ) → f z = 0 := by
      intro z hz
      apply sum_eq_zero; intro j _
      by_contra hne
      have hpos : 0 < F j z.1 * χY h j (ρ * z.1 + σ * z.2) :=
        lt_of_le_of_ne (mul_nonneg (bb_nonneg _ _ _ _ _ _) (χY_nonneg _ _ _)) (Ne.symm hne)
      have hF : 0 < F j z.1 := lt_of_le_of_ne (bb_nonneg _ _ _ _ _ _) (fun h0 => by
        rw [← h0, zero_mul] at hpos; exact lt_irrefl _ hpos)
      have hχ : 0 < χY h j (ρ * z.1 + σ * z.2) := lt_of_le_of_ne (χY_nonneg _ _ _) (fun h0 => by
        rw [← h0, mul_zero] at hpos; exact lt_irrefl _ hpos)
      apply hz
      exact mem_Bset_of hδ hδ1 hh he0 he hσ0 hρ1 (hlam j) hF hχ
    have := integral_le_of_supp hf_cont hf0 hf1 (Bset_meas e σ h δ (2 * h / σ)) hfB
    refine this.trans ?_
    exact Bset_measure he0.le hσ0.le hh.le hδ.le (by positivity)
  -- (5) tail
  have htail : PP (fun ε : Fin n → ℤˣ => ((N : ℝ) - 1) * h ≤ |Y ε|) ≤
      2 * Real.exp (-(((N : ℝ) - 1) * h) ^ 2 / 2) := by
    rcases eq_or_lt_of_le (show (0 : ℝ) ≤ ((N : ℝ) - 1) * h by
      have : (1 : ℝ) ≤ N := by exact_mod_cast hN
      nlinarith) with h0 | h0
    · rw [← h0]; simp only [zero_pow two_ne_zero, neg_zero, zero_div, Real.exp_zero, mul_one]
      linarith [PP_le_one (fun ε : Fin n → ℤˣ => (0 : ℝ) ≤ |Y ε|)]
    · have := hoeffding (bw n) h0
      rw [bw_sq hn2, mul_one] at this
      refine this.trans (le_of_eq ?_)
      congr 2; ring
  have hsh := sum_le_sum hshell
  rw [sum_add_distrib] at hsh
  have hPP' : PP (fun ε : Fin n → ℤˣ => 0 ≤ X ε ∧ X ε < -e * Y ε) =
      PP (fun ε : Fin n → ℤˣ => 0 ≤ ssum ε (aw n) ∧ ssum ε (aw n) < -(√(n : ℝ) / σa n) * ssum ε (bw n)) :=
    rfl
  rw [← hPP']
  linarith

end R522
end

end S_C12

-- ===== C13 =====
section S_C13

/-! Asymptotics of the thin-wedge bound (original). -/

open Finset Real MeasureTheory Filter Topology

noncomputable section

namespace R522

lemma natpow_neg_tendsto {a : ℝ} (ha : 0 < a) :
    Tendsto (fun n : ℕ => (n : ℝ) ^ (-a)) atTop (𝓝 0) :=
  (tendsto_rpow_neg_atTop ha).comp tendsto_natCast_atTop_atTop

lemma natpow_exp_tendsto (a b c : ℝ) (hb : 0 < b) (hc : 0 < c) :
    Tendsto (fun n : ℕ => (n : ℝ) ^ a * Real.exp (-b * (n : ℝ) ^ c)) atTop (𝓝 0) := by
  have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (a / c) b hb).comp
    ((tendsto_rpow_atTop hc).comp tendsto_natCast_atTop_atTop)
  refine h.congr' (Eventually.of_forall (fun n => ?_))
  simp only [Function.comp]
  rw [← Real.rpow_mul (by positivity), mul_div_cancel₀ _ hc.ne']

/-- `e_n = √n / σa n`. -/
def en (n : ℕ) : ℝ := √(n : ℝ) / σa n
def sn (n : ℕ) : ℝ := √(1 - ρw n ^ 2)

lemma σa_sq_ge {n : ℕ} (hn : 2 ≤ n) : (n : ℝ) ^ 3 / 12 ≤ σa n ^ 2 := by
  have h := σa_sq_eq n
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  nlinarith [mul_nonneg (sub_nonneg.mpr hn2) (sub_nonneg.mpr hn2), sq_nonneg (n : ℝ)]

lemma ne_sq {n : ℕ} (hn : 2 ≤ n) :
    ((n : ℝ) * en n) ^ 2 = 6 * (n : ℝ) ^ 2 / (((n : ℝ) - 1) * (2 * n - 1)) := by
  have hσ := σa_pos hn
  have h := σa_sq_eq n
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have h1 : ((n : ℝ) - 1) * (2 * n - 1) ≠ 0 := by
    apply mul_ne_zero <;> linarith
  rw [en, mul_div_assoc', div_pow, mul_pow, Real.sq_sqrt (by positivity)]
  rw [div_eq_div_iff (by positivity) h1]
  nlinarith

lemma ne_nonneg (n : ℕ) : 0 ≤ (n : ℝ) * en n := by
  unfold en
  rcases Nat.lt_or_ge n 2 with h | h
  · interval_cases n <;> simp [σa]
  · have := σa_pos h; positivity

lemma tendsto_ne : Tendsto (fun n : ℕ => (n : ℝ) * en n) atTop (𝓝 (√3)) := by
  have hsq : Tendsto (fun n : ℕ => ((n : ℝ) * en n) ^ 2) atTop (𝓝 3) := by
    have e : ∀ᶠ n : ℕ in atTop, ((n : ℝ) * en n) ^ 2 =
        6 / ((1 - 1 / (n : ℝ)) * (2 - 1 / (n : ℝ))) := by
      filter_upwards [eventually_ge_atTop 2] with n hn
      rw [ne_sq hn]
      have hn0 : (n : ℝ) ≠ 0 := by positivity
      field_simp
    refine Tendsto.congr' (EventuallyEq.symm e) ?_
    have h1 : Tendsto (fun n : ℕ => 1 / (n : ℝ)) atTop (𝓝 0) :=
      tendsto_const_div_atTop_nhds_zero_nat 1
    have hA : Tendsto (fun n : ℕ => (1 - 1 / (n : ℝ)) * (2 - 1 / (n : ℝ))) atTop
        (𝓝 ((1 - 0) * (2 - 0))) :=
      ((tendsto_const_nhds (x := (1:ℝ))).sub h1).mul ((tendsto_const_nhds (x := (2:ℝ))).sub h1)
    have hB : Tendsto (fun n : ℕ => 6 / ((1 - 1 / (n : ℝ)) * (2 - 1 / (n : ℝ)))) atTop
        (𝓝 (6 / ((1 - 0) * (2 - 0)))) :=
      (tendsto_const_nhds (x := (6:ℝ))).div hA (by norm_num)
    convert hB using 2; norm_num
  have := (Real.continuous_sqrt.tendsto 3).comp hsq
  refine this.congr' (Eventually.of_forall (fun n => ?_))
  simp only [Function.comp]
  exact Real.sqrt_sq (ne_nonneg n)

lemma tendsto_en : Tendsto en atTop (𝓝 0) := by
  have h := tendsto_ne.mul (tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ))
  rw [mul_zero] at h
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have : (n : ℝ) ≠ 0 := by positivity
  field_simp

lemma ρw_eq {n : ℕ} (hn : 2 ≤ n) : ρw n = ((n : ℝ) * (n - 1) / 2) / (σa n * √(n : ℝ)) := by
  unfold ρw aw bw
  have : ∑ j : Fin n, wt n j / σa n * (1 / √(n : ℝ)) = (∑ j : Fin n, wt n j) / (σa n * √(n : ℝ)) := by
    rw [sum_div]; apply sum_congr rfl; intro j _; field_simp
  rw [this, sum_wt]
  congr 1
  have := sum_range_cast n
  linarith

lemma one_sub_ρw_sq {n : ℕ} (hn : 2 ≤ n) : 1 - ρw n ^ 2 = ((n : ℝ) + 1) / (2 * (2 * n - 1)) := by
  rw [ρw_eq hn, div_pow, mul_pow, Real.sq_sqrt (by positivity)]
  have hσ := σa_pos hn
  have h := σa_sq_eq n
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hd : 2 * (2 * (n : ℝ) - 1) ≠ 0 := by
    apply mul_ne_zero (by norm_num); linarith
  rw [sub_eq_iff_eq_add, div_add_div _ _ hd (by positivity), eq_div_iff (by positivity)]
  have hσ2 : σa n ^ 2 = (n : ℝ) * (n - 1) * (2 * n - 1) / 6 := by linarith
  rw [hσ2]
  ring

lemma ρw_sq_lt {n : ℕ} (hn : 2 ≤ n) : ρw n ^ 2 ≤ 3 / 4 := by
  have := one_sub_ρw_sq hn
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have : 1 / 4 ≤ ((n : ℝ) + 1) / (2 * (2 * n - 1)) := by
    rw [div_le_div_iff₀ (by norm_num) (by nlinarith)]; nlinarith
  linarith

lemma tendsto_sn : Tendsto sn atTop (𝓝 (1 / 2)) := by
  have h1 : Tendsto (fun n : ℕ => 1 - ρw n ^ 2) atTop (𝓝 (1 / 4)) := by
    have e : ∀ᶠ n : ℕ in atTop, 1 - ρw n ^ 2 = (1 + 1 / (n : ℝ)) / (2 * (2 - 1 / (n : ℝ))) := by
      filter_upwards [eventually_ge_atTop 2] with n hn
      rw [one_sub_ρw_sq hn]
      have hn0 : (n : ℝ) ≠ 0 := by positivity
      field_simp
    refine Tendsto.congr' (EventuallyEq.symm e) ?_
    have h0 : Tendsto (fun n : ℕ => 1 / (n : ℝ)) atTop (𝓝 0) :=
      tendsto_const_div_atTop_nhds_zero_nat 1
    have hA : Tendsto (fun n : ℕ => 1 + 1 / (n : ℝ)) atTop (𝓝 (1 + 0)) :=
      (tendsto_const_nhds (x := (1:ℝ))).add h0
    have hB : Tendsto (fun n : ℕ => 2 * (2 - 1 / (n : ℝ))) atTop (𝓝 (2 * (2 - 0))) :=
      (tendsto_const_nhds (x := (2:ℝ))).mul ((tendsto_const_nhds (x := (2:ℝ))).sub h0)
    have := hA.div hB (by norm_num)
    rw [show ((1:ℝ) + 0) / (2 * (2 - 0)) = 1 / 4 by norm_num] at this
    exact this
  have := (Real.continuous_sqrt.tendsto (1 / 4)).comp h1
  have hs : √(1 / 4 : ℝ) = 1 / 2 := by
    rw [show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  rw [hs] at this
  exact this

/-- the limit constant of `n · GM`. -/
def GMlim (h δ : ℝ) : ℝ :=
  (1 + 2 * δ) / √(2 * π) * √3 * ((1 / 2) * (1 + (4 * h) ^ 2) / √(2 * π) + 2 * h)

lemma tendsto_GM (h δ : ℝ) :
    Tendsto (fun n : ℕ => (n : ℝ) * GM (en n) (sn n) h δ) atTop (𝓝 (GMlim h δ)) := by
  have hs := tendsto_sn
  have he := tendsto_en
  have hne := tendsto_ne
  have e : ∀ n : ℕ, (n : ℝ) * GM (en n) (sn n) h δ =
      (1 + 2 * δ) / √(2 * π) * ((n : ℝ) * en n) * (1 + 4 * en n) *
        (sn n * (1 + (2 * h / sn n) ^ 2) / √(2 * π) + 2 * h) := by
    intro n; unfold GM; ring
  simp_rw [e]
  unfold GMlim
  have h2 : Tendsto (fun n : ℕ => 2 * h / sn n) atTop (𝓝 (4 * h)) := by
    have := (tendsto_const_nhds (x := 2 * h)).div hs (by norm_num)
    rw [show 2 * h / (1 / 2 : ℝ) = 4 * h by ring] at this
    exact this
  have := ((((tendsto_const_nhds (x := (1 + 2 * δ) / √(2 * π))).mul hne).mul
    ((tendsto_const_nhds (x := (1:ℝ))).add ((tendsto_const_nhds (x := (4:ℝ))).mul he))).mul
    (((hs.mul ((tendsto_const_nhds (x := (1:ℝ))).add (h2.pow 2))).div_const (√(2 * π))).add
      (tendsto_const_nhds (x := 2 * h))))
  rw [show (1 + 2 * δ) / √(2 * π) * √3 * (1 + 4 * 0) * (1 / 2 * (1 + (4 * h) ^ 2) / √(2 * π) + 2 * h)
    = (1 + 2 * δ) / √(2 * π) * √3 * (1 / 2 * (1 + (4 * h) ^ 2) / √(2 * π) + 2 * h) by ring] at this
  exact this

end R522
end

end S_C13

-- ===== C14 =====
section S_C14

/-! The error terms vanish; the sign-change probability bound `p ≤ (√3/(2π) + θ)/n` (original). -/

open Finset Real MeasureTheory Filter Topology

noncomputable section

namespace R522

def Rn (n : ℕ) : ℝ := (n : ℝ) ^ ((1 : ℝ) / 8)
def Nn (n : ℕ) : ℕ := ⌊(n : ℝ) ^ ((1 : ℝ) / 16)⌋₊ + 2

lemma Tail_anti (ψ : SchwartzMap ℝ ℂ) {U U' : ℝ} (h : U' ≤ U) : Tail ψ U ≤ Tail ψ U' := by
  unfold Tail
  apply integral_mono_of_nonneg
  · exact Eventually.of_forall (fun u => Set.indicator_nonneg (fun _ _ => norm_nonneg _) u)
  · exact integrable_ind_gt ψ U'
  · refine Eventually.of_forall (fun u => ?_)
    simp only [Set.indicator, Set.mem_setOf_eq]
    split_ifs with h1 h2 h2
    · exact le_rfl
    · exact absurd (lt_of_le_of_lt h h1) h2
    · exact norm_nonneg _
    · exact le_rfl

lemma Nn_le (n : ℕ) (hn : 1 ≤ n) : (Nn n : ℝ) ≤ 3 * (n : ℝ) ^ ((1 : ℝ) / 16) := by
  unfold Nn
  have h1 : (1 : ℝ) ≤ (n : ℝ) ^ ((1 : ℝ) / 16) :=
    Real.one_le_rpow (by exact_mod_cast hn) (by norm_num)
  have := Nat.floor_le (show 0 ≤ (n : ℝ) ^ ((1 : ℝ) / 16) by positivity)
  push_cast; linarith

lemma Nn_ge (n : ℕ) : (n : ℝ) ^ ((1 : ℝ) / 16) ≤ (Nn n : ℝ) - 1 := by
  unfold Nn
  have := Nat.lt_floor_add_one ((n : ℝ) ^ ((1 : ℝ) / 16))
  push_cast; linarith

lemma Nn_one (n : ℕ) : 1 ≤ Nn n := by unfold Nn; omega

lemma ne_le_two {n : ℕ} (hn : 6 ≤ n) : (n : ℝ) * en n ≤ 2 := by
  have h := ne_sq (show 2 ≤ n by omega)
  have hn6 : (6 : ℝ) ≤ n := by exact_mod_cast hn
  have hpos : 0 < ((n : ℝ) - 1) * (2 * n - 1) := by apply mul_pos <;> linarith
  have : ((n : ℝ) * en n) ^ 2 ≤ 2 ^ 2 := by
    rw [h, div_le_iff₀ hpos]; nlinarith
  exact (pow_le_pow_iff_left₀ (ne_nonneg n) (by norm_num) two_ne_zero).mp this

lemma σa_le {n : ℕ} : σa n ≤ (n : ℝ) ^ ((3 : ℝ) / 2) := by
  have h := σa_sq_eq n
  rcases Nat.lt_or_ge n 1 with hn | hn
  · interval_cases n; simp [σa]
  · have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have e : ((n : ℝ) ^ ((3 : ℝ) / 2)) ^ 2 = (n : ℝ) ^ 3 := by
      rw [← Real.rpow_natCast ((n : ℝ) ^ ((3 : ℝ) / 2)) 2, ← Real.rpow_mul (by positivity)]
      norm_num
    have h2 : σa n ^ 2 ≤ ((n : ℝ) ^ ((3 : ℝ) / 2)) ^ 2 := by
      rw [e]
      nlinarith [mul_nonneg (sub_nonneg.mpr hn1) (sub_nonneg.mpr hn1)]
    have hσ0 : 0 ≤ σa n := Real.sqrt_nonneg _
    exact (pow_le_pow_iff_left₀ hσ0 (by positivity) two_ne_zero).mp h2

lemma A4_le {n : ℕ} (hn : 2 ≤ n) : ∑ i : Fin n, aw n i ^ 4 ≤ 144 / n := by
  have hσ := σa_pos hn
  have h1 : ∑ i : Fin n, aw n i ^ 4 = (∑ w ∈ range n, (w : ℝ) ^ 4) / (σa n ^ 2) ^ 2 := by
    simp only [aw, div_pow]
    rw [← sum_div, sum_wt_four]; ring
  rw [h1]
  have h2 := sum_four_le n
  have h3 := σa_sq_ge hn
  have hn0 : (0 : ℝ) < n := by positivity
  rw [div_le_div_iff₀ (by positivity) hn0]
  have : ((n : ℝ) ^ 3 / 12) ^ 2 ≤ (σa n ^ 2) ^ 2 := pow_le_pow_left₀ (by positivity) h3 2
  nlinarith

lemma B4_eq {n : ℕ} (hn : 1 ≤ n) : ∑ i : Fin n, bw n i ^ 4 = 1 / n := by
  simp only [bw, div_pow, one_pow, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  have : √(n : ℝ) ^ 4 = (n : ℝ) ^ 2 := by
    rw [show (4 : ℕ) = 2 * 2 by rfl, pow_mul, Real.sq_sqrt (by positivity)]
  rw [this]
  have : (n : ℝ) ≠ 0 := by positivity
  field_simp

end R522

namespace R522

lemma Rn_sq (n : ℕ) : Rn n ^ 2 = (n : ℝ) ^ ((1 : ℝ) / 4) := by
  unfold Rn
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]; norm_num

lemma Rn_six (n : ℕ) : Rn n ^ 6 = (n : ℝ) ^ ((3 : ℝ) / 4) := by
  unfold Rn
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]; norm_num

def c1 : ℝ := π ^ 2 / 8192000

lemma ηc_le {n : ℕ} (hn : 2 ≤ n) :
    ηc n (Rn n) (ρw n) ≤ 3 * Real.exp (-(c1 * (n : ℝ) ^ ((1 : ℝ) / 4))) := by
  unfold ηc
  have hR2 := Rn_sq n
  have hpi := Real.pi_lt_d2
  have hpi' := Real.pi_gt_three
  have hc1 : c1 ≤ 1 / 100000 := by unfold c1; rw [div_le_div_iff₀ (by norm_num) (by norm_num)]; nlinarith
  have hc0 : 0 < c1 := by unfold c1; positivity
  have hq : (n : ℝ) ^ ((1 : ℝ) / 4) ≤ n := by
    apply Real.rpow_le_self_of_one_le (by exact_mod_cast (show 1 ≤ n by omega)) (by norm_num)
  have hq0 : 0 ≤ (n : ℝ) ^ ((1 : ℝ) / 4) := by positivity
  -- term 1
  have hs : (1 / 100 : ℝ) ≤ Real.sin (1 / 2) ^ 2 := by
    have := Real.sin_gt_sub_cube (x := 1 / 2) (by norm_num)
    nlinarith
  have t1 : Real.exp (-((n : ℝ) * Real.sin (1 / 2) ^ 2 / 16)) ≤ Real.exp (-(c1 * (n : ℝ) ^ ((1 : ℝ) / 4))) := by
    apply Real.exp_le_exp.mpr
    have : c1 * (n : ℝ) ^ ((1 : ℝ) / 4) ≤ (n : ℝ) * Real.sin (1 / 2) ^ 2 / 16 := by
      have : c1 * (n : ℝ) ^ ((1 : ℝ) / 4) ≤ (1 / 100000) * n := by
        apply mul_le_mul hc1 hq hq0 (by norm_num)
      nlinarith [Nat.cast_nonneg (α := ℝ) n]
    linarith
  have t2 : Real.exp (-(Rn n ^ 2 * (π ^ 2 / 8192000))) = Real.exp (-(c1 * (n : ℝ) ^ ((1 : ℝ) / 4))) := by
    rw [hR2, c1]; ring_nf
  have t3 : Real.exp (-(2 * π ^ 2 * (1 - |ρw n|) * Rn n ^ 2)) ≤ Real.exp (-(c1 * (n : ℝ) ^ ((1 : ℝ) / 4))) := by
    apply Real.exp_le_exp.mpr
    have hρ := ρw_sq_lt hn
    have hρa : |ρw n| ≤ 9 / 10 := by
      have : |ρw n| ^ 2 ≤ (9 / 10) ^ 2 := by rw [sq_abs]; nlinarith
      exact (pow_le_pow_iff_left₀ (abs_nonneg _) (by norm_num) two_ne_zero).mp this
    rw [hR2]
    have : c1 ≤ 2 * π ^ 2 * (1 - |ρw n|) := by nlinarith
    nlinarith
  linarith

end R522
end

end S_C14

-- ===== C15 =====
section S_C15

/-! The error terms of the thin-wedge bound vanish (original). -/

open Finset Real MeasureTheory Filter Topology

noncomputable section

namespace R522

lemma en_σa {n : ℕ} (hn : 2 ≤ n) : en n * σa n = √(n : ℝ) := by
  unfold en; have := σa_pos hn; field_simp

lemma Errj_le {n : ℕ} (hn : 40 ≤ n) {δ h : ℝ} (hδ : 0 < δ) (hh : 0 < h) {j : ℕ} (hj : j < Nn n) :
    Errj n (en n) h δ (Rn n) j ≤
      en n * Nn n * h * (1 + 2 * δ) * (16 * (2 * π) ^ 4 * Rn n ^ 4 * (145 / n)) * (2 * Rn n) * (2 * h * (2 * Rn n))
      + en n * Nn n * h * (1 + 2 * δ) * (3 * Real.exp (-(c1 * (n : ℝ) ^ ((1 : ℝ) / 4)))) * (2 * (σa n / 4)) * Mom 0 ψ0
      + 2 * (Mom 4 (Sb 0 1 δ one_pos hδ) / (h * (√(n : ℝ) / 4)) ^ 4) * Mom 0 ψ0
      + 2 * Mom 0 (Sb 0 1 δ one_pos hδ) * (Mom 4 ψ0 / (h * (√(n : ℝ) / 4)) ^ 4) := by
  simp only [Errj]
  rw [dif_pos hδ, dif_pos hδ]
  have hn2 : 2 ≤ n := by omega
  have hσ := σa_pos hn2
  have he0 : 0 < en n := by unfold en; positivity
  have hn0 : (0 : ℝ) < n := by positivity
  have hR0 : 0 ≤ Rn n := by unfold Rn; positivity
  have hlam : lamj (en n) h j ≤ en n * Nn n * h := by
    unfold lamj
    have : ((j : ℝ) + 1) ≤ Nn n := by exact_mod_cast hj
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left this he0.le) hh.le
  have hlam0 : 0 ≤ lamj (en n) h j := by unfold lamj; positivity
  have hAB : (∑ i : Fin n, aw n i ^ 4) + ∑ i : Fin n, bw n i ^ 4 ≤ 145 / n := by
    have := A4_le hn2
    rw [B4_eq (by omega)]
    have : (144 : ℝ) / n + 1 / n = 145 / n := by ring
    linarith
  have hAB0 : 0 ≤ (∑ i : Fin n, aw n i ^ 4) + ∑ i : Fin n, bw n i ^ 4 :=
    add_nonneg (sum_nonneg (fun _ _ => by positivity)) (sum_nonneg (fun _ _ => by positivity))
  have hη := ηc_le hn2
  have hη0 : 0 ≤ ηc n (Rn n) (ρw n) := by unfold ηc; positivity
  have hthr : h * (√(n : ℝ) / 4) ≤ lamj (en n) h j * (σa n / 4) := by
    have e : lamj (en n) h j * (σa n / 4) = ((j : ℝ) + 1) * h * (en n * σa n) / 4 := by
      unfold lamj; ring
    rw [e, en_σa hn2]
    have : (1 : ℝ) ≤ (j : ℝ) + 1 := by have := Nat.cast_nonneg (α := ℝ) j; linarith
    have hs : 0 ≤ √(n : ℝ) := Real.sqrt_nonneg _
    have : h * √(n : ℝ) ≤ ((j : ℝ) + 1) * h * √(n : ℝ) := by
      have := mul_le_mul_of_nonneg_right this (mul_nonneg hh.le hs)
      linarith
    linarith
  have hthr0 : 0 < h * (√(n : ℝ) / 4) := by positivity
  have hT1 : Tail (Sb 0 1 δ one_pos hδ) (lamj (en n) h j * (σa n / 4)) ≤
      Mom 4 (Sb 0 1 δ one_pos hδ) / (h * (√(n : ℝ) / 4)) ^ 4 :=
    (Tail_anti _ hthr).trans (tail_le_mom4 _ hthr0)
  have hT2 : Tail ψ0 (h * (√(n : ℝ) / 4)) ≤ Mom 4 ψ0 / (h * (√(n : ℝ) / 4)) ^ 4 :=
    tail_le_mom4 _ hthr0
  have hm0 : 0 ≤ Mom 0 ψ0 := mom_nonneg 0 ψ0
  have hmS : 0 ≤ Mom 0 (Sb 0 1 δ one_pos hδ) := mom_nonneg 0 _
  have e1 : lamj (en n) h j * (1 + 2 * δ) * (16 * (2 * π) ^ 4 * Rn n ^ 4 *
      ((∑ i : Fin n, aw n i ^ 4) + ∑ i : Fin n, bw n i ^ 4)) * (2 * Rn n) * (2 * h * (2 * Rn n)) ≤
      en n * Nn n * h * (1 + 2 * δ) * (16 * (2 * π) ^ 4 * Rn n ^ 4 * (145 / n)) * (2 * Rn n) *
        (2 * h * (2 * Rn n)) := by
    gcongr
  have e2 : lamj (en n) h j * (1 + 2 * δ) * ηc n (Rn n) (ρw n) * (2 * (σa n / 4)) * Mom 0 ψ0 ≤
      en n * Nn n * h * (1 + 2 * δ) * (3 * Real.exp (-(c1 * (n : ℝ) ^ ((1 : ℝ) / 4)))) *
        (2 * (σa n / 4)) * Mom 0 ψ0 := by
    gcongr
  have e3 : 2 * Tail (Sb 0 1 δ one_pos hδ) (lamj (en n) h j * (σa n / 4)) * Mom 0 ψ0 ≤
      2 * (Mom 4 (Sb 0 1 δ one_pos hδ) / (h * (√(n : ℝ) / 4)) ^ 4) * Mom 0 ψ0 := by
    gcongr
  have e4 : 2 * Mom 0 (Sb 0 1 δ one_pos hδ) * Tail ψ0 (h * (√(n : ℝ) / 4)) ≤
      2 * Mom 0 (Sb 0 1 δ one_pos hδ) * (Mom 4 ψ0 / (h * (√(n : ℝ) / 4)) ^ 4) := by
    gcongr
  linarith

end R522
end

end S_C15

-- ===== C16 =====
section S_C16

/-! Total error → 0, and the sign-change bound (original). -/

open Finset Real MeasureTheory Filter Topology

noncomputable section

namespace R522

lemma rp_mul (n : ℕ) (a b : ℝ) (hn : 1 ≤ n) : (n : ℝ) ^ a * (n : ℝ) ^ b = (n : ℝ) ^ (a + b) := by
  rw [← Real.rpow_add (by exact_mod_cast (show 0 < n by omega))]

lemma rp_div (n : ℕ) (a : ℝ) (hn : 1 ≤ n) : (n : ℝ) ^ a / n = (n : ℝ) ^ (a - 1) := by
  rw [Real.rpow_sub (by exact_mod_cast (show 0 < n by omega)), Real.rpow_one]

lemma Nn_sq_le (n : ℕ) (hn : 1 ≤ n) : (Nn n : ℝ) ^ 2 ≤ 9 * (n : ℝ) ^ ((1 : ℝ) / 8) := by
  have h := Nn_le n hn
  have h0 : (0 : ℝ) ≤ Nn n := by positivity
  have : (Nn n : ℝ) ^ 2 ≤ (3 * (n : ℝ) ^ ((1 : ℝ) / 16)) ^ 2 := pow_le_pow_left₀ h0 h 2
  rw [mul_pow, ← Real.rpow_natCast ((n : ℝ) ^ ((1 : ℝ) / 16)) 2, ← Real.rpow_mul (by positivity)] at this
  norm_num at this ⊢
  linarith

/-- the explicit total bound -/
def Btot (h δ : ℝ) (hδ : 0 < δ) (n : ℕ) : ℝ :=
  18 * (h * (1 + 2 * δ) * (16 * (2 * π) ^ 4) * 145 * (8 * h)) * (n : ℝ) ^ (-(1 / 8 : ℝ))
  + 27 * h * (1 + 2 * δ) * Mom 0 ψ0 * ((n : ℝ) ^ (13 / 8 : ℝ) * Real.exp (-c1 * (n : ℝ) ^ (1 / 4 : ℝ)))
  + 3 * (256 * (2 * Mom 4 (Sb 0 1 δ one_pos hδ) * Mom 0 ψ0 + 2 * Mom 0 (Sb 0 1 δ one_pos hδ) * Mom 4 ψ0)
      / h ^ 4) * (n : ℝ) ^ (-(15 / 16 : ℝ))
  + 2 * ((n : ℝ) ^ (1 : ℝ) * Real.exp (-(h ^ 2 / 2) * (n : ℝ) ^ (1 / 8 : ℝ)))

lemma tendsto_Btot (h δ : ℝ) (hδ : 0 < δ) (hh : 0 < h) : Tendsto (Btot h δ hδ) atTop (𝓝 0) := by
  have c1p : 0 < c1 := by unfold c1; positivity
  have t1 := natpow_neg_tendsto (a := 1 / 8) (by norm_num)
  have t2 := natpow_exp_tendsto (13 / 8) c1 (1 / 4) c1p (by norm_num)
  have t3 := natpow_neg_tendsto (a := 15 / 16) (by norm_num)
  have t4 := natpow_exp_tendsto 1 (h ^ 2 / 2) (1 / 8) (by positivity) (by norm_num)
  have := (((t1.const_mul (18 * (h * (1 + 2 * δ) * (16 * (2 * π) ^ 4) * 145 * (8 * h)))).add
    (t2.const_mul (27 * h * (1 + 2 * δ) * Mom 0 ψ0))).add
    (t3.const_mul (3 * (256 * (2 * Mom 4 (Sb 0 1 δ one_pos hδ) * Mom 0 ψ0 +
      2 * Mom 0 (Sb 0 1 δ one_pos hδ) * Mom 4 ψ0) / h ^ 4)))).add (t4.const_mul 2)
  simp only [mul_zero, add_zero] at this
  exact this

theorem err_le_Btot {n : ℕ} (hn : 40 ≤ n) {h δ : ℝ} (hδ : 0 < δ) (hh : 0 < h) :
    (n : ℝ) * (∑ j ∈ range (Nn n), Errj n (en n) h δ (Rn n) j
      + 2 * Real.exp (-(((Nn n : ℝ) - 1) * h) ^ 2 / 2)) ≤ Btot h δ hδ n := by
  have hn1 : 1 ≤ n := by omega
  have hn2 : 2 ≤ n := by omega
  have hn0 : (0 : ℝ) < n := by positivity
  have hsum : ∑ j ∈ range (Nn n), Errj n (en n) h δ (Rn n) j ≤ (Nn n) *
      ((en n) * (Nn n) * h * (1 + 2 * δ) * (16 * (2 * π) ^ 4 * (Rn n) ^ 4 * (145 / n)) * (2 * (Rn n)) * (2 * h * (2 * (Rn n)))
      + (en n) * (Nn n) * h * (1 + 2 * δ) * (3 * Real.exp (-(c1 * (n : ℝ) ^ ((1 : ℝ) / 4)))) * (2 * (σa n / 4)) * Mom 0 ψ0
      + 2 * (Mom 4 (Sb 0 1 δ one_pos hδ) / (h * (√(n : ℝ) / 4)) ^ 4) * Mom 0 ψ0
      + 2 * Mom 0 (Sb 0 1 δ one_pos hδ) * (Mom 4 ψ0 / (h * (√(n : ℝ) / 4)) ^ 4)) := by
    have := sum_le_card_nsmul (range (Nn n)) (fun j => Errj n (en n) h δ (Rn n) j) _
      (fun j hj => Errj_le hn hδ hh (mem_range.mp hj))
    rw [card_range, nsmul_eq_mul] at this
    exact this
  have hne := ne_le_two (show 6 ≤ n by omega)
  have hN2 := Nn_sq_le n hn1
  have hR6 := Rn_six n
  have hσ := σa_le (n := n)
  have hNl := Nn_le n hn1
  have hNg := Nn_ge n
  have he0 : 0 ≤ (en n) := by unfold en; have := σa_pos hn2; positivity
  have hm0 := mom_nonneg 0 ψ0
  have hm4 := mom_nonneg 4 ψ0
  have hs0 := mom_nonneg 0 (Sb 0 1 δ one_pos hδ)
  have hs4 := mom_nonneg 4 (Sb 0 1 δ one_pos hδ)
  have hexp0 : 0 ≤ Real.exp (-(c1 * (n : ℝ) ^ ((1 : ℝ) / 4))) := (Real.exp_pos _).le
  -- piece 1
  have p1 : (n : ℝ) * ((Nn n) * ((en n) * (Nn n) * h * (1 + 2 * δ) * (16 * (2 * π) ^ 4 * (Rn n) ^ 4 * (145 / n)) * (2 * (Rn n)) *
      (2 * h * (2 * (Rn n))))) ≤
      18 * (h * (1 + 2 * δ) * (16 * (2 * π) ^ 4) * 145 * (8 * h)) * (n : ℝ) ^ (-(1 / 8 : ℝ)) := by
    have e1 : (n : ℝ) * ((Nn n) * ((en n) * (Nn n) * h * (1 + 2 * δ) * (16 * (2 * π) ^ 4 * (Rn n) ^ 4 * (145 / n)) * (2 * (Rn n)) *
        (2 * h * (2 * (Rn n))))) =
        ((n : ℝ) * (en n)) * ((Nn n) : ℝ) ^ 2 * (h * (1 + 2 * δ) * (16 * (2 * π) ^ 4) * 145 * (8 * h)) * (Rn n) ^ 6 / n := by
      field_simp; ring
    rw [e1, hR6]
    have hK : 0 ≤ h * (1 + 2 * δ) * (16 * (2 * π) ^ 4) * 145 * (8 * h) := by positivity
    have e2 : (n : ℝ) ^ ((1 : ℝ) / 8) * (n : ℝ) ^ ((3 : ℝ) / 4) / n = (n : ℝ) ^ (-(1 / 8 : ℝ)) := by
      rw [rp_mul n _ _ hn1, rp_div n _ hn1]; norm_num
    calc ((n : ℝ) * (en n)) * ((Nn n) : ℝ) ^ 2 * (h * (1 + 2 * δ) * (16 * (2 * π) ^ 4) * 145 * (8 * h)) *
          (n : ℝ) ^ ((3 : ℝ) / 4) / n
        ≤ 2 * (9 * (n : ℝ) ^ ((1 : ℝ) / 8)) * (h * (1 + 2 * δ) * (16 * (2 * π) ^ 4) * 145 * (8 * h)) *
          (n : ℝ) ^ ((3 : ℝ) / 4) / n := by
          gcongr
      _ = 18 * (h * (1 + 2 * δ) * (16 * (2 * π) ^ 4) * 145 * (8 * h)) *
          ((n : ℝ) ^ ((1 : ℝ) / 8) * (n : ℝ) ^ ((3 : ℝ) / 4) / n) := by ring
      _ = _ := by rw [e2]
  -- piece 2
  have p2 : (n : ℝ) * ((Nn n) * ((en n) * (Nn n) * h * (1 + 2 * δ) * (3 * Real.exp (-(c1 * (n : ℝ) ^ ((1 : ℝ) / 4)))) *
      (2 * (σa n / 4)) * Mom 0 ψ0)) ≤
      27 * h * (1 + 2 * δ) * Mom 0 ψ0 * ((n : ℝ) ^ (13 / 8 : ℝ) * Real.exp (-c1 * (n : ℝ) ^ (1 / 4 : ℝ))) := by
    have e1 : (n : ℝ) * ((Nn n) * ((en n) * (Nn n) * h * (1 + 2 * δ) * (3 * Real.exp (-(c1 * (n : ℝ) ^ ((1 : ℝ) / 4)))) *
        (2 * (σa n / 4)) * Mom 0 ψ0)) =
        ((n : ℝ) * (en n)) * ((Nn n) : ℝ) ^ 2 * σa n * (h * (1 + 2 * δ) * Mom 0 ψ0 * (3 / 2)) *
          Real.exp (-(c1 * (n : ℝ) ^ ((1 : ℝ) / 4))) := by ring
    rw [e1]
    have e2 : (n : ℝ) ^ ((1 : ℝ) / 8) * (n : ℝ) ^ ((3 : ℝ) / 2) = (n : ℝ) ^ (13 / 8 : ℝ) := by
      rw [rp_mul n _ _ hn1]; norm_num
    have hK : 0 ≤ h * (1 + 2 * δ) * Mom 0 ψ0 * (3 / 2) := by positivity
    have hσ0 : 0 ≤ σa n := Real.sqrt_nonneg _
    calc ((n : ℝ) * (en n)) * ((Nn n) : ℝ) ^ 2 * σa n * (h * (1 + 2 * δ) * Mom 0 ψ0 * (3 / 2)) *
          Real.exp (-(c1 * (n : ℝ) ^ ((1 : ℝ) / 4)))
        ≤ 2 * (9 * (n : ℝ) ^ ((1 : ℝ) / 8)) * (n : ℝ) ^ ((3 : ℝ) / 2) *
          (h * (1 + 2 * δ) * Mom 0 ψ0 * (3 / 2)) * Real.exp (-(c1 * (n : ℝ) ^ ((1 : ℝ) / 4))) := by
          gcongr
      _ = 27 * h * (1 + 2 * δ) * Mom 0 ψ0 * (((n : ℝ) ^ ((1 : ℝ) / 8) * (n : ℝ) ^ ((3 : ℝ) / 2)) *
          Real.exp (-(c1 * (n : ℝ) ^ ((1 : ℝ) / 4)))) := by ring
      _ = _ := by rw [e2]; congr 3; ring
  -- pieces 3, 4
  have p3 : (n : ℝ) * ((Nn n) * (2 * (Mom 4 (Sb 0 1 δ one_pos hδ) / (h * (√(n : ℝ) / 4)) ^ 4) * Mom 0 ψ0
      + 2 * Mom 0 (Sb 0 1 δ one_pos hδ) * (Mom 4 ψ0 / (h * (√(n : ℝ) / 4)) ^ 4))) ≤
      3 * (256 * (2 * Mom 4 (Sb 0 1 δ one_pos hδ) * Mom 0 ψ0 + 2 * Mom 0 (Sb 0 1 δ one_pos hδ) * Mom 4 ψ0)
        / h ^ 4) * (n : ℝ) ^ (-(15 / 16 : ℝ)) := by
    have hq : (h * (√(n : ℝ) / 4)) ^ 4 = h ^ 4 * (n : ℝ) ^ 2 / 256 := by
      rw [mul_pow, div_pow, show (4 : ℕ) = 2 * 2 by rfl, pow_mul (√(n : ℝ)), Real.sq_sqrt hn0.le]
      norm_num; ring
    rw [hq]
    set K := 256 * (2 * Mom 4 (Sb 0 1 δ one_pos hδ) * Mom 0 ψ0 + 2 * Mom 0 (Sb 0 1 δ one_pos hδ) * Mom 4 ψ0)
      / h ^ 4 with hK
    have hK0 : 0 ≤ K := by rw [hK]; positivity
    have e1 : (n : ℝ) * ((Nn n) * (2 * (Mom 4 (Sb 0 1 δ one_pos hδ) / (h ^ 4 * (n : ℝ) ^ 2 / 256)) * Mom 0 ψ0
        + 2 * Mom 0 (Sb 0 1 δ one_pos hδ) * (Mom 4 ψ0 / (h ^ 4 * (n : ℝ) ^ 2 / 256)))) = K * ((Nn n) / n) := by
      rw [hK]; field_simp
    rw [e1]
    have e2 : (n : ℝ) ^ ((1 : ℝ) / 16) / n = (n : ℝ) ^ (-(15 / 16 : ℝ)) := by
      rw [rp_div n _ hn1]; norm_num
    calc K * ((Nn n) / n) ≤ K * (3 * (n : ℝ) ^ ((1 : ℝ) / 16) / n) := by gcongr
      _ = 3 * K * ((n : ℝ) ^ ((1 : ℝ) / 16) / n) := by ring
      _ = _ := by rw [e2]
  -- tail
  have p4 : (n : ℝ) * (2 * Real.exp (-((((Nn n) : ℝ) - 1) * h) ^ 2 / 2)) ≤
      2 * ((n : ℝ) ^ (1 : ℝ) * Real.exp (-(h ^ 2 / 2) * (n : ℝ) ^ (1 / 8 : ℝ))) := by
    rw [Real.rpow_one]
    have : -((((Nn n) : ℝ) - 1) * h) ^ 2 / 2 ≤ -(h ^ 2 / 2) * (n : ℝ) ^ (1 / 8 : ℝ) := by
      have h1 : (n : ℝ) ^ ((1 : ℝ) / 8) = ((n : ℝ) ^ ((1 : ℝ) / 16)) ^ 2 := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]; norm_num
      have h2 : ((n : ℝ) ^ ((1 : ℝ) / 16)) ^ 2 ≤ (((Nn n) : ℝ) - 1) ^ 2 :=
        pow_le_pow_left₀ (by positivity) hNg 2
      rw [show (1 / 8 : ℝ) = (1 : ℝ) / 8 by norm_num, h1]
      nlinarith [sq_nonneg h]
    have := Real.exp_le_exp.mpr this
    nlinarith
  have hfin := mul_le_mul_of_nonneg_left hsum hn0.le
  unfold Btot
  rw [mul_add]
  have hsplit := congrArg id (rfl : (0:ℝ) = 0)
  linarith [p1, p2, p3, p4, hfin, show ∀ a b c d : ℝ, (n : ℝ) * ((Nn n : ℝ) * (a + b + c + d)) =
    (n : ℝ) * ((Nn n : ℝ) * a) + (n : ℝ) * ((Nn n : ℝ) * b) + (n : ℝ) * ((Nn n : ℝ) * (c + d)) from
    fun a b c d => by ring]

end R522
end

end S_C16

-- ===== C17 =====
section S_C17

/-! **Sign-change bound.** For the sequence `c = ∑ ε_j (n-1-j)`, `S = ∑ ε_j` over `n` signs, the
probability that `c` and `c + S` have a strict/weak sign change is at most `(√3/(2π) + θ)/n`
for large `n` (original). -/

open Finset Real MeasureTheory Filter Topology

noncomputable section

namespace R522

/-- the sign-change event. -/
def SCev (n : ℕ) (ε : Fin n → ℤˣ) : Prop :=
  (0 ≤ ssum ε (wt n) ∧ ssum ε (wt n) + ssum ε (fun _ => (1 : ℝ)) < 0) ∨
  (ssum ε (wt n) ≤ 0 ∧ 0 < ssum ε (wt n) + ssum ε (fun _ => (1 : ℝ)))

lemma ssum_neg {ι : Type*} [Fintype ι] (ε : ι → ℤˣ) (c : ι → ℝ) :
    ssum (fun i => -ε i) c = -ssum ε c := by
  unfold ssum; rw [← sum_neg_distrib]; apply sum_congr rfl; intro i _; push_cast; ring

lemma PP_flip {ι : Type*} [Fintype ι] [DecidableEq ι] (S : (ι → ℤˣ) → Prop) :
    PP (fun ε => S (fun i => -ε i)) = PP S := by
  classical
  rw [PP_eq, PP_eq]
  unfold EE
  congr 1
  exact Fintype.sum_equiv (Equiv.neg (ι → ℤˣ)) _ _ (fun ε => by simp [Pi.neg_def])

lemma ssum_aw {n : ℕ} (ε : Fin n → ℤˣ) : ssum ε (aw n) = ssum ε (wt n) / σa n := by
  unfold ssum aw; rw [sum_div]; apply sum_congr rfl; intro i _; ring

lemma ssum_bw {n : ℕ} (ε : Fin n → ℤˣ) : ssum ε (bw n) = ssum ε (fun _ => (1 : ℝ)) / √(n : ℝ) := by
  unfold ssum bw; rw [sum_div]; apply sum_congr rfl; intro i _; ring

lemma wedge_iff {n : ℕ} (hn : 2 ≤ n) (ε : Fin n → ℤˣ) :
    (0 ≤ ssum ε (wt n) ∧ ssum ε (wt n) + ssum ε (fun _ => (1 : ℝ)) < 0) ↔
    (0 ≤ ssum ε (aw n) ∧ ssum ε (aw n) < -(√(n : ℝ) / σa n) * ssum ε (bw n)) := by
  have hσ := σa_pos hn
  have hs : 0 < √(n : ℝ) := Real.sqrt_pos.mpr (by positivity)
  rw [ssum_aw, ssum_bw]
  have e : -(√(n : ℝ) / σa n) * (ssum ε (fun _ => (1 : ℝ)) / √(n : ℝ)) =
      -ssum ε (fun _ => (1 : ℝ)) / σa n := by field_simp
  rw [e, div_lt_div_iff_of_pos_right hσ]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨div_nonneg h1 hσ.le, by linarith⟩
  · rintro ⟨h1, h2⟩
    have := mul_nonneg h1 hσ.le
    rw [div_mul_cancel₀ _ hσ.ne'] at this
    exact ⟨this, by linarith⟩

lemma GMlim_cont : Tendsto (fun h : ℝ => GMlim h h) (𝓝 0) (𝓝 (√3 / (4 * π))) := by
  have hc : Continuous (fun h : ℝ => GMlim h h) := by unfold GMlim; fun_prop
  have := hc.tendsto 0
  have e : GMlim 0 0 = √3 / (4 * π) := by
    unfold GMlim
    have h2 : √(2 * π) * √(2 * π) = 2 * π := Real.mul_self_sqrt (by positivity)
    have h3 : √(2 * π) ≠ 0 := by positivity
    field_simp
    nlinarith [h2]
  rwa [e] at this

/-- **The sign-change bound.** -/
theorem pk_bound {θ : ℝ} (hθ : 0 < θ) :
    ∀ᶠ n : ℕ in atTop, PP (SCev n) ≤ (√3 / (2 * π) + θ) / n := by
  -- choose the smoothing parameters
  obtain ⟨h, hh0, hh1, hGM⟩ : ∃ h : ℝ, 0 < h ∧ h ≤ 1 ∧ GMlim h h < √3 / (4 * π) + θ / 4 := by
    have := (GMlim_cont.eventually (gt_mem_nhds (show √3 / (4 * π) < √3 / (4 * π) + θ / 4 by linarith)))
    have h2 := this.and (Ioo_mem_nhds (show (-1 : ℝ) < 0 by norm_num) (show (0 : ℝ) < 1 by norm_num))
    obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp h2
    refine ⟨min (ε / 2) (1 / 2), by positivity, by
      have := min_le_right (ε / 2) (1 / 2); linarith, ?_⟩
    have := hball (y := min (ε / 2) (1 / 2)) (by
      rw [Real.dist_eq, sub_zero, abs_of_pos (by positivity)]
      have := min_le_left (ε / 2) (1 / 2); linarith)
    exact this.1
  have hδ : (0 : ℝ) < h := hh0
  have hGMt := tendsto_GM h h
  have hB := tendsto_Btot h h hδ hh0
  have ev1 := hGMt.eventually (gt_mem_nhds (show GMlim h h < GMlim h h + θ / 8 by linarith))
  have ev2 := hB.eventually (gt_mem_nhds (show (0 : ℝ) < θ / 8 by linarith))
  have ev3 := tendsto_en.eventually (gt_mem_nhds (show (0 : ℝ) < 1 / 16 by norm_num))
  filter_upwards [ev1, ev2, ev3, eventually_ge_atTop 40] with n h1 h2 h3 hn
  have hn2 : 2 ≤ n := by omega
  have hn0 : (0 : ℝ) < n := by positivity
  have hσ : 0 < 1 - ρw n ^ 2 := by have := ρw_sq_lt hn2; linarith
  have hw := wedge_bound hn (R := Rn n) hδ hh1 hh0 (by unfold Rn; positivity) (Nn n) (Nn_one n) h3.le hσ
  -- the wedge probability
  have hA : PP (fun ε : Fin n → ℤˣ => 0 ≤ ssum ε (wt n) ∧ ssum ε (wt n) + ssum ε (fun _ => (1 : ℝ)) < 0)
      ≤ (√3 / (4 * π) + θ / 2) / n := by
    have heq : PP (fun ε : Fin n → ℤˣ => 0 ≤ ssum ε (wt n) ∧ ssum ε (wt n) + ssum ε (fun _ => (1 : ℝ)) < 0)
        = PP (fun ε : Fin n → ℤˣ => 0 ≤ ssum ε (aw n) ∧ ssum ε (aw n) < -(√(n : ℝ) / σa n) * ssum ε (bw n)) := by
      congr 1; funext ε; exact propext (wedge_iff hn2 ε)
    rw [heq]
    have hb := err_le_Btot hn hδ hh0 (h := h) (δ := h)
    rw [le_div_iff₀ hn0]
    have : (n : ℝ) * PP (fun ε : Fin n → ℤˣ => 0 ≤ ssum ε (aw n) ∧
        ssum ε (aw n) < -(√(n : ℝ) / σa n) * ssum ε (bw n)) ≤
        (n : ℝ) * GM (en n) (sn n) h h + (n : ℝ) * (∑ j ∈ range (Nn n), Errj n (en n) h h (Rn n) j
          + 2 * Real.exp (-(((Nn n : ℝ) - 1) * h) ^ 2 / 2)) := by
      rw [← mul_add]
      apply mul_le_mul_of_nonneg_left _ hn0.le
      have := hw
      unfold en sn
      linarith
    linarith
  -- the second wedge by symmetry
  have hB' : PP (fun ε : Fin n → ℤˣ => ssum ε (wt n) ≤ 0 ∧ 0 < ssum ε (wt n) + ssum ε (fun _ => (1 : ℝ)))
      = PP (fun ε : Fin n → ℤˣ => 0 ≤ ssum ε (wt n) ∧ ssum ε (wt n) + ssum ε (fun _ => (1 : ℝ)) < 0) := by
    rw [← PP_flip]
    congr 1; funext ε
    simp only [ssum_neg]
    apply propext; constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨by linarith, by linarith⟩
  have hsplit := PP_or_le (fun ε : Fin n → ℤˣ => 0 ≤ ssum ε (wt n) ∧
      ssum ε (wt n) + ssum ε (fun _ => (1 : ℝ)) < 0)
    (fun ε : Fin n → ℤˣ => ssum ε (wt n) ≤ 0 ∧ 0 < ssum ε (wt n) + ssum ε (fun _ => (1 : ℝ)))
  have : PP (SCev n) = PP (fun ε : Fin n → ℤˣ => (0 ≤ ssum ε (wt n) ∧
      ssum ε (wt n) + ssum ε (fun _ => (1 : ℝ)) < 0) ∨
      (ssum ε (wt n) ≤ 0 ∧ 0 < ssum ε (wt n) + ssum ε (fun _ => (1 : ℝ)))) := rfl
  rw [this]
  have e2 : (√3 / (2 * π) + θ) / n = 2 * ((√3 / (4 * π) + θ / 2) / n) := by
    field_simp; ring
  rw [e2]
  linarith

end R522
end

end S_C17

-- ===== D1 =====
section S_D1

/-! Sign variations of truncated coefficient sequences (original). -/

open Polynomial Finset

namespace E521D

/-- truncation `∑_{i<N} c_i X^i`. -/
noncomputable def T (c : ℕ → ℝ) (N : ℕ) : ℝ[X] := ∑ i ∈ range N, C (c i) * X ^ i

/-- the weak sign-change indicator. -/
def Ip (x y : ℝ) : Prop := (0 ≤ x ∧ y < 0) ∨ (x ≤ 0 ∧ 0 < y)

noncomputable instance (x y : ℝ) : Decidable (Ip x y) := by unfold Ip; infer_instance

lemma T_succ (c : ℕ → ℝ) (N : ℕ) : T c (N + 1) = T c N + C (c N) * X ^ N := by
  unfold T; rw [sum_range_succ]

lemma T_coeff (c : ℕ → ℝ) (N i : ℕ) : (T c N).coeff i = if i < N then c i else 0 := by
  unfold T
  rw [finsetSum_coeff]
  simp only [coeff_C_mul_X_pow]
  split_ifs with h
  · rw [sum_eq_single i]
    · simp
    · intro b _ hb; rw [if_neg (Ne.symm hb)]
    · intro h'; exact absurd (mem_range.mpr h) h'
  · apply sum_eq_zero; intro b hb; rw [mem_range] at hb; rw [if_neg (by omega)]

lemma T_degree_lt (c : ℕ → ℝ) (N : ℕ) : (T c N).degree < N := by
  rw [degree_lt_iff_coeff_zero]
  intro m hm; rw [T_coeff, if_neg (by omega)]

lemma T_succ_lead (c : ℕ → ℝ) {N : ℕ} (hc : c N ≠ 0) :
    (T c (N + 1)).leadingCoeff = c N ∧ (T c (N + 1)).eraseLead = T c N := by
  have hdeg : (T c (N + 1)).natDegree = N := by
    rw [T_succ]
    rw [natDegree_add_eq_right_of_degree_lt]
    · exact natDegree_C_mul_X_pow N (c N) hc
    · rw [degree_C_mul_X_pow N hc]; exact T_degree_lt c N
  constructor
  · rw [leadingCoeff, hdeg, T_coeff, if_pos (by omega)]
  · ext i
    rw [eraseLead_coeff, hdeg, T_coeff, T_coeff]
    by_cases hi : i = N
    · rw [if_pos hi, if_neg (by omega)]
    · rw [if_neg hi]
      by_cases hi2 : i < N
      · rw [if_pos (by omega), if_pos hi2]
      · rw [if_neg (by omega), if_neg hi2]

lemma T_succ_zero (c : ℕ → ℝ) {N : ℕ} (hc : c N = 0) : T c (N + 1) = T c N := by
  rw [T_succ, hc, C_0, zero_mul, add_zero]

/-- the leading coefficient of `T c N` is `c (N-1)` when that is nonzero. -/
lemma T_lead_of (c : ℕ → ℝ) {N : ℕ} (hc : c N ≠ 0) : (T c (N + 1)).leadingCoeff = c N :=
  (T_succ_lead c hc).1

/-- one step of the sign-variation count. -/
lemma sv_step (c : ℕ → ℝ) (N : ℕ) :
    signVariations (T c (N + 2)) ≤ signVariations (T c (N + 1)) +
      (if Ip (c N) (c (N + 1)) then 1 else 0) := by
  by_cases h1 : c (N + 1) = 0
  · rw [T_succ_zero c h1]; omega
  · have hne : T c (N + 2) ≠ 0 := by
      intro h0
      have := (T_succ_lead c h1).1
      rw [h0, leadingCoeff_zero] at this; exact h1 this.symm
    rw [signVariations_eq_eraseLead_add_ite hne, (T_succ_lead c h1).2, (T_succ_lead c h1).1]
    apply Nat.add_le_add_left
    split_ifs with hs hI hI
    · exact le_rfl
    · exfalso; apply hI
      by_cases h0 : c N = 0
      · unfold Ip; rw [h0]
        rcases lt_or_gt_of_ne h1 with h | h
        · left; exact ⟨le_rfl, h⟩
        · right; exact ⟨le_rfl, h⟩
      · rw [T_lead_of c h0] at hs
        unfold Ip
        rcases lt_or_gt_of_ne h1 with h | h
        · rw [sign_neg h] at hs
          have : SignType.sign (c N) = 1 := by
            have := congrArg Neg.neg hs; simpa using this.symm
          left; exact ⟨(sign_eq_one_iff.mp this).le, h⟩
        · rw [sign_pos h] at hs
          have : SignType.sign (c N) = -1 := by
            have := congrArg Neg.neg hs; simpa using this.symm
          right; exact ⟨(sign_eq_neg_one_iff.mp this).le, h⟩
    · omega
    · omega

/-- iterate: from `a+1` to `b+1`. -/
lemma sv_range (c : ℕ → ℝ) (a : ℕ) : ∀ b, a ≤ b →
    signVariations (T c (b + 1)) ≤ signVariations (T c (a + 1)) +
      ((Ico a b).filter (fun k => Ip (c k) (c (k + 1)))).card := by
  intro b hab
  induction b, hab using Nat.le_induction with
  | base => simp
  | succ b hab ih =>
    have := sv_step c b
    have hc : ((Ico a (b + 1)).filter (fun k => Ip (c k) (c (k + 1)))).card =
        ((Ico a b).filter (fun k => Ip (c k) (c (k + 1)))).card + (if Ip (c b) (c (b + 1)) then 1 else 0) := by
      rw [Nat.Ico_succ_right_eq_insert_Ico hab, filter_insert]
      split_ifs with h
      · rw [card_insert_of_notMem (by simp)]
      · rfl
    rw [hc]; show signVariations (T c (b + 2)) ≤ _; omega

lemma sv_one (c : ℕ → ℝ) : signVariations (T c 1) = 0 := by
  unfold T; simp only [range_one, sum_singleton, pow_zero, mul_one]
  rw [← monomial_zero_left]; exact signVariations_monomial 0 _

/-- nonnegative continuation with a positive leading coefficient does not add variations. -/
lemma sv_nonneg (c : ℕ → ℝ) (a : ℕ) (ha : 0 < (T c (a + 1)).leadingCoeff) :
    ∀ b, a ≤ b → (∀ k, a < k → k ≤ b → 0 ≤ c k) →
      signVariations (T c (b + 1)) = signVariations (T c (a + 1)) ∧ 0 < (T c (b + 1)).leadingCoeff := by
  intro b hab
  induction b, hab using Nat.le_induction with
  | base => intro _; exact ⟨rfl, ha⟩
  | succ b hab ih =>
    intro hpos
    obtain ⟨h1, h2⟩ := ih (fun k hk1 hk2 => hpos k hk1 (by omega))
    by_cases hz : c (b + 1) = 0
    · rw [T_succ_zero c hz]; exact ⟨h1, h2⟩
    · have hp : 0 < c (b + 1) := lt_of_le_of_ne (hpos (b + 1) (by omega) le_rfl) (Ne.symm hz)
      have hne : T c (b + 2) ≠ 0 := by
        intro h0
        have := (T_succ_lead c hz).1
        rw [h0, leadingCoeff_zero] at this; exact hz this.symm
      rw [signVariations_eq_eraseLead_add_ite hne, (T_succ_lead c hz).2, (T_succ_lead c hz).1]
      rw [if_neg]
      · exact ⟨by rw [h1]; rfl, hp⟩
      · rw [sign_pos hp, sign_pos h2]; decide

/-- an increasing stretch contributes at most one weak sign change. -/
lemma Ip_incr (c : ℕ → ℝ) (a b : ℕ) (hinc : ∀ k, a ≤ k → k < b → c k < c (k + 1)) :
    ((Ico a b).filter (fun k => Ip (c k) (c (k + 1)))).card ≤ 1 := by
  rw [card_le_one]
  intro x hx y hy
  rw [mem_filter, mem_Ico] at hx hy
  -- in an increasing stretch, Ip means `c k ≤ 0 < c (k+1)`, which happens at most once
  have mono : ∀ i j, a ≤ i → i ≤ j → j ≤ b → c i ≤ c j := by
    intro i j hi hij hj
    induction j, hij using Nat.le_induction with
    | base => exact le_rfl
    | succ j hij ih => exact (ih (by omega)).trans (hinc j (by omega) (by omega)).le
  have hx' : c x ≤ 0 ∧ 0 < c (x + 1) := by
    rcases hx.2 with ⟨h1, h2⟩ | h
    · exact absurd (hinc x hx.1.1 hx.1.2) (by linarith)
    · exact h
  have hy' : c y ≤ 0 ∧ 0 < c (y + 1) := by
    rcases hy.2 with ⟨h1, h2⟩ | h
    · exact absurd (hinc y hy.1.1 hy.1.2) (by linarith)
    · exact h
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · have := mono (x + 1) y (by omega) (by omega) (by omega); linarith [hx'.2, hy'.1]
  · have := mono (y + 1) x (by omega) (by omega) (by omega); linarith [hy'.2, hx'.1]

end E521D

end S_D1

-- ===== D2 =====
section S_D2

/-! Coefficients of `f · D_N²` (original). -/

open Polynomial Finset

namespace E521D

/-- `D_N = 1 + X + ... + X^N`. -/
noncomputable def DN (N : ℕ) : ℝ[X] := ∑ a ∈ range (N + 1), X ^ a

/-- the tent `W t = #{(a, b) ∈ [0,N]² : a + b = t}`. -/
def W (N : ℕ) (t : ℤ) : ℕ := ((range (N + 1)).filter (fun a : ℕ => 0 ≤ t - a ∧ t - a ≤ N)).card

lemma DN_sq_coeff (N t : ℕ) : (DN N * DN N).coeff t = W N t := by
  unfold DN W
  rw [sum_mul_sum]
  rw [finsetSum_coeff]
  simp_rw [finsetSum_coeff, ← pow_add, coeff_X_pow]
  rw [card_filter, Nat.cast_sum]
  apply sum_congr rfl
  intro a ha
  rw [mem_range] at ha
  by_cases h : 0 ≤ (t : ℤ) - a ∧ (t : ℤ) - a ≤ N
  · rw [if_pos h]
    rw [sum_eq_single (t - a)]
    · rw [if_pos (by omega)]; simp
    · intro b _ hb; rw [if_neg (by omega)]
    · intro hb; rw [mem_range] at hb; omega
  · rw [if_neg h, Nat.cast_zero]
    apply sum_eq_zero; intro b hb; rw [mem_range] at hb; rw [if_neg (by omega)]

lemma W_low (N : ℕ) {t : ℤ} (h0 : 0 ≤ t) (h1 : t ≤ N) : (W N t : ℤ) = t + 1 := by
  unfold W
  have : (range (N + 1)).filter (fun a : ℕ => 0 ≤ t - a ∧ t - a ≤ N) = range (t.toNat + 1) := by
    ext a; simp only [mem_filter, mem_range]; omega
  rw [this, card_range]; push_cast; omega

lemma W_high (N : ℕ) {t : ℤ} (h0 : (N : ℤ) ≤ t) (h1 : t ≤ 2 * N) : (W N t : ℤ) = 2 * N + 1 - t := by
  unfold W
  have : (range (N + 1)).filter (fun a : ℕ => 0 ≤ t - a ∧ t - a ≤ N) = Ico (t - N).toNat (N + 1) := by
    ext a; simp only [mem_filter, mem_range, mem_Ico]; omega
  rw [this, Nat.card_Ico]; omega

lemma W_neg (N : ℕ) {t : ℤ} (h : t < 0) : W N t = 0 := by
  unfold W; rw [card_eq_zero, filter_eq_empty_iff]; intro a _; omega

/-- coefficients of `f · D²` for `f = ∑_{j ≤ n} e_j X^j`. -/
lemma Q_coeff (e : ℕ → ℝ) (n N k : ℕ) :
    ((T e (n + 1)) * (DN N * DN N)).coeff k = ∑ j ∈ range (n + 1), e j * (W N ((k : ℤ) - j) : ℝ) := by
  rw [coeff_mul]
  unfold T
  have : ∀ x ∈ antidiagonal k, (∑ i ∈ range (n + 1), C (e i) * X ^ i).coeff x.1 * (DN N * DN N).coeff x.2 =
      ∑ i ∈ range (n + 1), (if i = x.1 then e i else 0) * (W N ((k : ℤ) - i) : ℝ) := by
    intro x hx
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
    rw [finsetSum_coeff, sum_mul, DN_sq_coeff]
    apply sum_congr rfl; intro i _
    rw [coeff_C_mul_X_pow]
    by_cases h : x.1 = i
    · rw [if_pos h, if_pos h.symm]
      congr 3; omega
    · rw [if_neg h, if_neg (Ne.symm h)]; simp
  rw [sum_congr rfl this, sum_comm]
  apply sum_congr rfl; intro i hi
  rw [← sum_mul]
  by_cases hik : i ≤ k
  · rw [sum_eq_single (i, k - i)]
    · simp
    · intro x hx hne
      rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
      rw [if_neg]
      intro h; apply hne; ext <;> dsimp only <;> omega
    · intro h; exfalso; apply h; rw [Finset.HasAntidiagonal.mem_antidiagonal]; omega
  · rw [sum_eq_zero, W_neg N (by omega)]
    · simp
    · intro x hx; rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx; rw [if_neg (by omega)]

end E521D

end S_D2

-- ===== D3 =====
section S_D3

/-! Positive roots of `f = ∑_{j≤n} e_j X^j` are at most the weak sign changes of the forward
two-fold sums before `n - t`, plus one, under the tail and backward-positivity conditions
(original). -/

open Polynomial Finset

namespace E521D

/-- forward two-fold sums `c_k = ∑_{j≤k} e_j (k - j + 1)`. -/
def c2 (e : ℕ → ℝ) (k : ℕ) : ℝ := ∑ j ∈ range (k + 1), e j * ((k : ℝ) - j + 1)

/-- forward partial sums. -/
def S1 (e : ℕ → ℝ) (k : ℕ) : ℝ := ∑ j ∈ range (k + 1), e j

/-- backward two-fold sums of `a_i = e_{n-i}`. -/
def b2 (e : ℕ → ℝ) (n k : ℕ) : ℝ := ∑ i ∈ range (k + 1), e (n - i) * ((k : ℝ) - i + 1)

lemma Qc_low (e : ℕ → ℝ) {n N k : ℕ} (hk : k ≤ n) (hN : n ≤ N) :
    ((T e (n + 1)) * (DN N * DN N)).coeff k = c2 e k := by
  rw [Q_coeff]
  unfold c2
  rw [show n + 1 = (k + 1) + (n - k) by omega, sum_range_add]
  have h0 : ∑ j ∈ range (n - k), e (k + 1 + j) * (W N ((k : ℤ) - (k + 1 + j : ℕ)) : ℝ) = 0 := by
    apply sum_eq_zero; intro j _; rw [W_neg N (t := (k : ℤ) - ((k + 1 + j : ℕ) : ℤ)) (by push_cast; omega)]; simp
  rw [h0, add_zero]
  apply sum_congr rfl; intro j hj; rw [mem_range] at hj
  congr 1
  have := W_low N (t := (k : ℤ) - j) (by omega) (by omega)
  have h2 : ((W N ((k : ℤ) - j) : ℕ) : ℝ) = (((W N ((k : ℤ) - j) : ℕ) : ℤ) : ℝ) := by norm_cast
  rw [h2, this]; push_cast; ring

lemma Qc_mid_lin (e : ℕ → ℝ) {n N k : ℕ} (hk1 : n ≤ k) (hk2 : k ≤ N) :
    ((T e (n + 1)) * (DN N * DN N)).coeff k = ∑ j ∈ range (n + 1), e j * ((k : ℝ) - j + 1) := by
  rw [Q_coeff]
  apply sum_congr rfl; intro j hj; rw [mem_range] at hj
  congr 1
  have := W_low N (t := (k : ℤ) - j) (by omega) (by omega)
  have h2 : ((W N ((k : ℤ) - j) : ℕ) : ℝ) = (((W N ((k : ℤ) - j) : ℕ) : ℤ) : ℝ) := by norm_cast
  rw [h2, this]; push_cast; ring

lemma abs_e_le (e : ℕ → ℝ) (he : ∀ j, e j = 1 ∨ e j = -1) (j : ℕ) : |e j| = 1 := by
  rcases he j with h | h <;> rw [h] <;> simp

/-- the middle coefficients are positive. -/
lemma Qc_mid_pos (e : ℕ → ℝ) (he : ∀ j, e j = 1 ∨ e j = -1) {n N k : ℕ} (hN : n * n + n + 1 ≤ N)
    (hS : 1 ≤ S1 e n) (hk1 : N ≤ k) (hk2 : k ≤ N + n) :
    0 < ((T e (n + 1)) * (DN N * DN N)).coeff k := by
  rw [Q_coeff]
  -- c_k = (N+1) S_n - ∑ e_j (N + 1 - W(k-j)), with 0 ≤ N + 1 - W ≤ n
  have hW : ∀ j ∈ range (n + 1), |(N : ℝ) + 1 - (W N ((k : ℤ) - j) : ℝ)| ≤ n := by
    intro j hj; rw [mem_range] at hj
    have h2 : ((W N ((k : ℤ) - j) : ℕ) : ℝ) = (((W N ((k : ℤ) - j) : ℕ) : ℤ) : ℝ) := by norm_cast
    rw [h2]
    rcases le_or_gt ((k : ℤ) - j) N with h | h
    · rw [W_low N (by omega) h]; push_cast
      have hjn : (j : ℝ) ≤ n := by exact_mod_cast (by omega : j ≤ n)
      have hNk : (N : ℝ) ≤ k := by exact_mod_cast hk1
      have hkN : (k : ℝ) ≤ N + n := by exact_mod_cast hk2
      have hj0 : (0 : ℝ) ≤ j := by positivity
      rw [abs_le]; constructor <;> linarith
    · rw [W_high N h.le (by omega)]; push_cast
      have hk2' : (k : ℝ) ≤ N + n := by exact_mod_cast hk2
      have hj' : (0 : ℝ) ≤ j := by positivity
      have hlt : ((N : ℤ) : ℝ) < (k : ℝ) - j := by exact_mod_cast h
      rw [abs_le]; constructor <;> push_cast at hlt <;> linarith
  have e1 : ∑ j ∈ range (n + 1), e j * (W N ((k : ℤ) - j) : ℝ) =
      ((N : ℝ) + 1) * S1 e n - ∑ j ∈ range (n + 1), e j * ((N : ℝ) + 1 - (W N ((k : ℤ) - j) : ℝ)) := by
    unfold S1; rw [mul_sum, ← sum_sub_distrib]; apply sum_congr rfl; intro j _; ring
  rw [e1]
  have hb : ∑ j ∈ range (n + 1), e j * ((N : ℝ) + 1 - (W N ((k : ℤ) - j) : ℝ)) ≤ (n + 1) * n := by
    calc ∑ j ∈ range (n + 1), e j * ((N : ℝ) + 1 - (W N ((k : ℤ) - j) : ℝ))
        ≤ ∑ j ∈ range (n + 1), (n : ℝ) := by
          apply sum_le_sum; intro j hj
          calc e j * ((N : ℝ) + 1 - (W N ((k : ℤ) - j) : ℝ))
              ≤ |e j * ((N : ℝ) + 1 - (W N ((k : ℤ) - j) : ℝ))| := le_abs_self _
            _ = |(N : ℝ) + 1 - (W N ((k : ℤ) - j) : ℝ)| := by rw [abs_mul, abs_e_le e he, one_mul]
            _ ≤ n := hW j hj
      _ = (n + 1) * n := by rw [sum_const, card_range, nsmul_eq_mul]; push_cast; ring
  have hNr : (n : ℝ) * n + n + 1 ≤ N := by exact_mod_cast hN
  nlinarith

/-- the top coefficients are the backward two-fold sums (or their linear continuation). -/
lemma Qc_top (e : ℕ → ℝ) {n N k : ℕ} (hk1 : N + n ≤ k) (hk2 : k ≤ 2 * N + n) (hN : n ≤ N) :
    ((T e (n + 1)) * (DN N * DN N)).coeff k =
      ∑ i ∈ range (n + 1), (if i ≤ 2 * N + n - k then e (n - i) * ((2 * N + n - k : ℕ) - (i : ℝ) + 1) else 0) := by
  rw [Q_coeff]
  rw [← sum_range_reflect]
  simp only [Nat.add_sub_cancel]
  apply sum_congr rfl; intro i hi; rw [mem_range] at hi
  have hj : n - i ≤ n := by omega
  by_cases hik : i ≤ 2 * N + n - k
  · rw [if_pos hik]
    congr 1
    have := W_high N (t := (k : ℤ) - (n - i : ℕ)) (by push_cast; omega) (by push_cast; omega)
    have h2 : ((W N ((k : ℤ) - (n - i : ℕ)) : ℕ) : ℝ) = (((W N ((k : ℤ) - (n - i : ℕ)) : ℕ) : ℤ) : ℝ) := by
      norm_cast
    rw [h2, this]
    push_cast
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
    push_cast; ring
  · rw [if_neg hik]
    have : W N ((k : ℤ) - (n - i : ℕ)) = 0 := by
      unfold W; rw [card_eq_zero, filter_eq_empty_iff]; intro a ha; rw [mem_range] at ha; omega
    rw [this]; simp

end E521D

end S_D3


end
