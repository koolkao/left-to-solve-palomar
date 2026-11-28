/-
Copyright 2026 Ming-Chih Kao. Licensed under the Apache License, Version 2.0;
see the LICENSE file at the root of this repository.
-/
module

public import Mathlib

/-! Port: `lean/MO503314Full.lean` of github.com/koolkao/mo503314-two-primes (commit
566defa273f1d35900318d07e35f92f6c8fad04a, v1.0.0; the concatenation of the modules `Analytic`, `Norms`,
`UnitDFT`, `Lemma3`, `CharDecomp`, `TwoC`, `Kernels`, `Lemma4`, `Fibre`, `Main` of its Lake project), ported from
Lean v4.33.1 / Mathlib 0df444a to Lean v4.36.0 / Mathlib fc4f59e and put into the module system: the `module`
header, `public import Mathlib`, a public section, the namespace `MO503314` renamed `TwoPrimes` and the final
theorem `mo503314` moved into it as `TwoPrimes.mo503314`, so that `Solution.lean` can state the compared theorem as
`MO503314.mo503314`. Changes needed by the newer Mathlib: `tendsto_finset_sum` → `tendsto_finsetSum`; in
`charsum_eq_of_logprod2` two `congr 1` steps replaced by `refine congrArg (ψ⁻¹ u * ·) ?_` (the former timed out);
`set_option maxHeartbeats 1000000` on `charsum_eq_of_logprod2` and `fibre_sym`. The mathematics and the proofs are
otherwise unchanged. -/

@[expose] public section

-- ===== Analytic =====

/-!
# Analytic core for MO 503314

For an even primitive Dirichlet character `ψ ≠ 1` modulo `N`,
`∑ w, ψ⁻¹ w * log ‖1 - e(w)‖ ≠ 0` where `e = ZMod.stdAddChar`.
-/

open Complex Filter Topology Finset ZMod

namespace TwoPrimes

variable {N : ℕ} [NeZero N]

/-- Partial sums of a nontrivial Dirichlet character are bounded. -/
lemma norm_sum_range_le (ψ : DirichletCharacter ℂ N) (hψ : ψ ≠ 1) (n : ℕ) :
    ‖∑ i ∈ range n, ψ (i : ZMod N)‖ ≤ N := by
  have hper : ∀ k, ∑ i ∈ range (k * N), ψ (i : ZMod N) = 0 := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Nat.succ_mul, Finset.sum_range_add, ih, zero_add]
      have : ∑ x ∈ range N, ψ ((k * N + x : ℕ) : ZMod N) = ∑ x ∈ range N, ψ (x : ZMod N) := by
        refine Finset.sum_congr rfl fun x _ => ?_
        congr 1
        push_cast
        simp
      rw [this]
      have h0 : ∑ a : ZMod N, ψ a = 0 := MulChar.sum_eq_zero_of_ne_one hψ
      rw [← h0]
      exact (Finset.sum_bij (fun (x : ℕ) _ => (x : ZMod N))
        (fun _ _ => Finset.mem_univ _)
        (fun a ha b hb hab => by
          simp only [Finset.mem_range] at ha hb
          exact (ZMod.natCast_eq_natCast_iff' a b N).1 hab |> fun h => by
            rwa [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at h)
        (fun b _ => ⟨b.val, by simpa using ZMod.val_lt b, by simp⟩)
        (fun _ _ => rfl))
  have hNpos : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  obtain ⟨k, r, hr, rfl⟩ : ∃ k r, r < N ∧ n = k * N + r :=
    ⟨n / N, n % N, Nat.mod_lt _ hNpos, by rw [mul_comm]; exact (Nat.div_add_mod n N).symm⟩
  rw [Finset.sum_range_add, hper, zero_add]
  calc ‖∑ x ∈ range r, ψ ((k * N + x : ℕ) : ZMod N)‖
      ≤ ∑ x ∈ range r, ‖ψ ((k * N + x : ℕ) : ZMod N)‖ := norm_sum_le _ _
    _ ≤ ∑ _x ∈ range r, (1 : ℝ) := by
        refine Finset.sum_le_sum fun x _ => ?_
        exact DirichletCharacter.norm_le_one ψ _
    _ = r := by simp
    _ ≤ N := by exact_mod_cast hr.le

/-- A nontrivial Dirichlet character vanishes at `0`. -/
lemma apply_zero_of_ne_one (ψ : DirichletCharacter ℂ N) (hψ : ψ ≠ 1) : ψ 0 = 0 := by
  have hN : N ≠ 1 := by
    rintro rfl
    exact hψ (Subsingleton.elim _ _)
  have : ¬ IsUnit (0 : ZMod N) := by
    have : Fact (1 < N) := ⟨by have := NeZero.ne N; omega⟩
    exact not_isUnit_zero
  exact MulChar.map_nonunit ψ this

/-- The partial sums of `ψ n / n` converge. -/
lemma exists_tendsto_sum (ψ : DirichletCharacter ℂ N) (hψ : ψ ≠ 1) :
    ∃ S : ℂ, Tendsto (fun K ↦ ∑ n ∈ range K, ψ (n : ZMod N) / n) atTop (𝓝 S) := by
  set f : ℕ → ℝ := fun n ↦ 1 / (max n 1 : ℕ) with hf
  have hanti : Antitone f := by
    intro a b hab
    simp only [hf]
    exact one_div_le_one_div_of_le (by positivity) (by exact_mod_cast max_le_max hab le_rfl)
  have h0 : Tendsto f atTop (𝓝 0) := by
    refine (tendsto_one_div_atTop_nhds_zero_nat).congr' ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    simp only [hf, max_eq_left hn]
  have hc := hanti.cauchySeq_series_mul_of_tendsto_zero_of_bounded h0
    (z := fun i ↦ ψ (i : ZMod N)) (b := N) (norm_sum_range_le ψ hψ)
  obtain ⟨S, hS⟩ := cauchySeq_tendsto_of_complete hc
  refine ⟨S, hS.congr fun K ↦ Finset.sum_congr rfl fun n _ ↦ ?_⟩
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [apply_zero_of_ne_one ψ hψ]
  · have hn' : 1 ≤ n := hn
    simp only [hf, max_eq_left hn', smul_eq_mul, Complex.real_smul]
    push_cast
    ring

local notation "e" => (ZMod.stdAddChar : AddChar (ZMod N) ℂ)

lemma norm_e (w : ZMod N) : ‖e w‖ = 1 := by
  rw [ZMod.stdAddChar_apply]; exact Circle.norm_coe _

lemma e_neg (w : ZMod N) : e (-w) = (starRingEnd ℂ) (e w) := by
  rw [ZMod.stdAddChar_apply, ZMod.stdAddChar_apply, AddChar.map_neg_eq_inv, Circle.coe_inv_eq_conj]

/-- Gauss sums of primitive characters do not vanish. -/
lemma gaussSum_ne_zero (χ : DirichletCharacter ℂ N) (hχ : χ.IsPrimitive) :
    gaussSum χ e ≠ 0 := by
  intro h
  have hF : 𝓕 (χ : ZMod N → ℂ) = 0 := by
    funext k
    rw [DirichletCharacter.IsPrimitive.fourierTransform_eq_inv_mul_gaussSum hχ, h, mul_zero]
    rfl
  have h0 : (χ : ZMod N → ℂ) = 0 := by
    have := (ZMod.dft (E := ℂ) (N := N)).injective (a₁ := (χ : ZMod N → ℂ)) (a₂ := 0)
    exact this (by rw [map_zero]; exact hF)
  have := congrFun h0 1
  simp at this

lemma isPrimitive_inv (χ : DirichletCharacter ℂ N) (hχ : χ.IsPrimitive) : χ⁻¹.IsPrimitive := by
  unfold DirichletCharacter.IsPrimitive at *
  rw [DirichletCharacter.conductor_inv]; exact hχ

/-- Twisted power-series identity. -/
lemma hasSum_twisted (ψ : DirichletCharacter ℂ N) (hψ : ψ.IsPrimitive) {r : ℝ} (hr0 : 0 ≤ r)
    (hr1 : r < 1) :
    HasSum (fun n : ℕ ↦ gaussSum ψ⁻¹ e * (ψ (n : ZMod N) / n * (r : ℂ) ^ n))
      (∑ w : ZMod N, ψ⁻¹ w * (-log (1 - r * e w))) := by
  have hw : ∀ w : ZMod N, HasSum (fun n : ℕ ↦ ψ⁻¹ w * (((r : ℂ) * e w) ^ n / n))
      (ψ⁻¹ w * (-log (1 - r * e w))) := by
    intro w
    refine (hasSum_taylorSeries_neg_log ?_).mul_left _
    rw [norm_mul, norm_e, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr0]
    exact hr1
  have := hasSum_sum (s := Finset.univ) (fun w _ ↦ hw w)
  refine this.congr_fun ?_
  intro n
  have hg : ∑ w : ZMod N, ψ⁻¹ w * e w ^ n = ψ (n : ZMod N) * gaussSum ψ⁻¹ e := by
    have h1 := gaussSum_mulShift_of_isPrimitive e (isPrimitive_inv ψ hψ) (n : ZMod N)
    rw [inv_inv] at h1
    rw [← h1, gaussSum]
    refine Finset.sum_congr rfl fun w _ ↦ ?_
    rw [AddChar.mulShift_apply, ← nsmul_eq_mul, AddChar.map_nsmul_eq_pow]
  symm
  calc ∑ w : ZMod N, ψ⁻¹ w * (((r : ℂ) * e w) ^ n / n)
      = ((r : ℂ) ^ n / n) * ∑ w : ZMod N, ψ⁻¹ w * e w ^ n := by
        rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun w _ ↦ ?_; rw [mul_pow]; ring
    _ = _ := by rw [hg]; ring

lemma one_sub_e_mem_slitPlane (w : ZMod N) (hw : w ≠ 0) : 1 - e w ∈ slitPlane := by
  have hre : (e w).re ≤ 1 := by
    have := Complex.re_le_norm (e w); rw [norm_e] at this; exact this
  rcases lt_or_eq_of_le hre with h | h
  · left; simp only [sub_re, one_re]; linarith
  · right
    intro him
    apply hw
    have h1 : e w = 1 := by
      have hn := norm_e w
      have him' : (e w).im = 0 := by simpa using him
      apply Complex.ext <;> simp [h, him']
    have : e w = e 0 := by rw [h1, AddChar.map_zero_eq_one]
    exact ZMod.injective_stdAddChar this

/-- Limit of the twisted logarithm sum as `r → 1⁻`. -/
lemma tendsto_twisted_log (ψ : DirichletCharacter ℂ N) (hψ : ψ ≠ 1) :
    Tendsto (fun r : ℝ ↦ ∑ w : ZMod N, ψ⁻¹ w * (-log (1 - r * e w))) (𝓝[<] 1)
      (𝓝 (∑ w : ZMod N, ψ⁻¹ w * (-log (1 - e w)))) := by
  refine tendsto_finsetSum _ fun w _ ↦ ?_
  by_cases hw : w = 0
  · subst hw
    have : ψ⁻¹ 0 = 0 := apply_zero_of_ne_one ψ⁻¹ (inv_ne_one.mpr hψ)
    simp [this]
  · refine Tendsto.const_mul _ (Tendsto.neg ?_)
    have hc : ContinuousAt (fun r : ℝ ↦ log (1 - (r : ℂ) * e w)) 1 := by
      refine ContinuousAt.clog ?_ (by simpa using one_sub_e_mem_slitPlane w hw)
      fun_prop
    simpa using hc.tendsto.mono_left nhdsWithin_le_nhds

/-- The arguments cancel for even characters. -/
lemma sum_log_eq (ψ : DirichletCharacter ℂ N) (hev : ψ.Even) :
    ∑ w : ZMod N, ψ⁻¹ w * log (1 - e w) = ∑ w : ZMod N, ψ⁻¹ w * (Real.log ‖1 - e w‖ : ℂ) := by
  have hev' : ∀ w, ψ⁻¹ (-w) = ψ⁻¹ w := by
    intro w
    rw [MulChar.inv_apply_eq_inv', MulChar.inv_apply_eq_inv', hev.eval_neg]
  have harg : ∀ w : ZMod N, arg (1 - e (-w)) = - arg (1 - e w) := by
    intro w
    rw [e_neg, ← map_one (starRingEnd ℂ), ← map_sub, arg_conj]
    have : arg (1 - e w) ≠ Real.pi := by
      rw [Ne, arg_eq_pi_iff]
      intro h
      have := Complex.re_le_norm (e w); rw [norm_e] at this
      simp only [sub_re, one_re] at h; linarith [h.1]
    simp [this]
  have hsum : ∑ w : ZMod N, ψ⁻¹ w * (arg (1 - e w) : ℂ) = 0 := by
    have h1 : ∑ w : ZMod N, ψ⁻¹ w * (arg (1 - e w) : ℂ)
        = ∑ w : ZMod N, ψ⁻¹ (-w) * (arg (1 - e (-w)) : ℂ) :=
      (Fintype.sum_equiv (Equiv.neg (ZMod N)) _ _ (fun w ↦ rfl)).symm
    have h2 : ∑ w : ZMod N, ψ⁻¹ (-w) * (arg (1 - e (-w)) : ℂ)
        = - ∑ w : ZMod N, ψ⁻¹ w * (arg (1 - e w) : ℂ) := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun w _ ↦ ?_
      rw [hev', harg]; push_cast; ring
    have := h1.trans h2
    linear_combination this / 2
  have hlog : ∀ z : ℂ, log z = (Real.log ‖z‖ : ℂ) + (arg z : ℂ) * I := fun z ↦ rfl
  simp only [hlog, mul_add, Finset.sum_add_distrib]
  rw [show ∑ w : ZMod N, ψ⁻¹ w * ((arg (1 - e w) : ℂ) * I)
      = (∑ w : ZMod N, ψ⁻¹ w * (arg (1 - e w) : ℂ)) * I by
    rw [Finset.sum_mul]; refine Finset.sum_congr rfl fun w _ ↦ ?_; ring]
  rw [hsum, zero_mul, add_zero]

/-- Core identity: `τ(ψ⁻¹) · S = - ∑ ψ⁻¹(w) log ‖1 - e w‖`, where `S = ∑ ψ(n)/n`. -/
lemma gauss_mul_S (ψ : DirichletCharacter ℂ N) (hψ : ψ ≠ 1) (hprim : ψ.IsPrimitive)
    (hev : ψ.Even) {S : ℂ}
    (hS : Tendsto (fun K ↦ ∑ n ∈ range K, ψ (n : ZMod N) / n) atTop (𝓝 S)) :
    gaussSum ψ⁻¹ e * S = - ∑ w : ZMod N, ψ⁻¹ w * (Real.log ‖1 - e w‖ : ℂ) := by
  have habel := Complex.tendsto_tsum_powerSeries_nhdsWithin_lt hS
  have h1 : Tendsto (fun r : ℝ ↦ ∑' n : ℕ, ψ (n : ZMod N) / n * (r : ℂ) ^ n) (𝓝[<] 1) (𝓝 S) :=
    habel.comp tendsto_map
  have h2 : Tendsto (fun r : ℝ ↦ gaussSum ψ⁻¹ e * ∑' n : ℕ, ψ (n : ZMod N) / n * (r : ℂ) ^ n)
      (𝓝[<] 1) (𝓝 (gaussSum ψ⁻¹ e * S)) := h1.const_mul _
  have h3 : ∀ᶠ r : ℝ in 𝓝[<] 1, gaussSum ψ⁻¹ e * ∑' n : ℕ, ψ (n : ZMod N) / n * (r : ℂ) ^ n
      = ∑ w : ZMod N, ψ⁻¹ w * (-log (1 - r * e w)) := by
    have : ∀ᶠ r : ℝ in 𝓝[<] 1, 0 < r := by
      have : Set.Ioo (0:ℝ) 1 ∈ 𝓝[<] (1:ℝ) := Ioo_mem_nhdsLT (by norm_num)
      filter_upwards [this] with r hr using hr.1
    filter_upwards [this, self_mem_nhdsWithin] with r hr0 hr1
    rw [← tsum_mul_left]
    exact (hasSum_twisted ψ hprim hr0.le hr1).tsum_eq
  have h4 := (h2.congr' h3)
  have h5 := tendsto_nhds_unique h4 (tendsto_twisted_log ψ hψ)
  rw [h5]
  simp only [mul_neg, Finset.sum_neg_distrib]
  rw [sum_log_eq ψ hev]

/-- Summation by parts. -/
lemma sum_mul_eq_by_parts (a : ℕ → ℂ) (w : ℕ → ℝ) (K : ℕ) :
    ∑ n ∈ range K, a n * (w n : ℂ) = (w K : ℂ) * ∑ n ∈ range K, a n
      + ∑ j ∈ range K, ((w j - w (j + 1) : ℝ) : ℂ) * ∑ n ∈ range (j + 1), a n := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [Finset.sum_range_succ, ih, Finset.sum_range_succ (fun j ↦ ((w j - w (j + 1) : ℝ) : ℂ) * _),
      Finset.sum_range_succ a K]
    push_cast
    ring

/-- An Abelian theorem for weighted sums. -/
lemma tendsto_tsum_weighted {ι : Type*} {l : Filter ι} (a : ℕ → ℂ) {S : ℂ}
    (hA : Tendsto (fun K ↦ ∑ n ∈ range K, a n) atTop (𝓝 S)) (w : ι → ℕ → ℝ)
    (hanti : ∀ᶠ i in l, Antitone (w i)) (hnn : ∀ᶠ i in l, ∀ n, 0 ≤ w i n)
    (hz : ∀ᶠ i in l, Tendsto (w i) atTop (𝓝 0)) (hpt : ∀ n, Tendsto (fun i ↦ w i n) l (𝓝 1))
    (hsumm : ∀ᶠ i in l, Summable (fun n ↦ a n * (w i n : ℂ))) :
    Tendsto (fun i ↦ ∑' n, a n * (w i n : ℂ)) l (𝓝 S) := by
  set A : ℕ → ℂ := fun K ↦ ∑ n ∈ range K, a n with hAdef
  obtain ⟨C, hC⟩ : ∃ C, ∀ K, ‖A K - S‖ ≤ C := by
    have hb : Bornology.IsBounded (Set.range fun K ↦ A K - S) :=
      Metric.isBounded_range_of_tendsto _ (by simpa using hA.sub_const S)
    obtain ⟨C, hC⟩ := hb.exists_norm_le
    exact ⟨C, fun K ↦ hC _ ⟨K, rfl⟩⟩
  rw [Metric.tendsto_nhds]
  intro ε hε
  set δ : ℝ := ε / 8 with hδ
  have hδpos : 0 < δ := by positivity
  obtain ⟨J, hJ⟩ : ∃ J, ∀ K ≥ J, ‖A K - S‖ ≤ δ := by
    have := (Metric.tendsto_atTop.1 hA) δ hδpos
    obtain ⟨J, hJ⟩ := this
    exact ⟨J, fun K hK ↦ (by simpa [dist_eq_norm] using (hJ K hK).le)⟩
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
  have h0 := hpt 0
  have hJt := hpt J
  -- eventually: w 0 ≤ 2, |w 0 - 1| ‖S‖ ≤ δ, C (w 0 - w J) ≤ δ
  have e1 : ∀ᶠ i in l, w i 0 ≤ 2 := h0.eventually (ge_mem_nhds (by norm_num))
  have e2 : ∀ᶠ i in l, |w i 0 - 1| * ‖S‖ ≤ δ := by
    have : Tendsto (fun i ↦ |w i 0 - 1| * ‖S‖) l (𝓝 (|1 - 1| * ‖S‖)) :=
      ((h0.sub_const 1).abs).mul_const _
    simp only [sub_self, abs_zero, zero_mul] at this
    exact this.eventually (ge_mem_nhds hδpos)
  have e3 : ∀ᶠ i in l, C * (w i 0 - w i J) ≤ δ := by
    have : Tendsto (fun i ↦ C * (w i 0 - w i J)) l (𝓝 (C * (1 - 1))) := (h0.sub hJt).const_mul _
    simp only [sub_self, mul_zero] at this
    exact this.eventually (ge_mem_nhds hδpos)
  filter_upwards [hanti, hnn, hz, hsumm, e1, e2, e3] with i hai hni hzi hsi h1 h2 h3
  -- bound on partial sums
  have hbound : ∀ K ≥ J, ‖∑ n ∈ range K, a n * (w i n : ℂ) - S‖ ≤ 6 * δ := by
    intro K hK
    have hR : ∑ j ∈ range K, ((w i j - w i (j + 1) : ℝ) : ℂ) * A (j + 1)
        = ((w i 0 - w i K : ℝ) : ℂ) * S
          + ∑ j ∈ range K, ((w i j - w i (j + 1) : ℝ) : ℂ) * (A (j + 1) - S) := by
      have ht : ∑ j ∈ range K, (w i j - w i (j + 1)) = w i 0 - w i K := by
        rw [Finset.sum_range_sub' (fun j ↦ w i j)]
      have : ((w i 0 - w i K : ℝ) : ℂ) * S
          = ∑ j ∈ range K, ((w i j - w i (j + 1) : ℝ) : ℂ) * S := by
        rw [← Finset.sum_mul, ← ht]; push_cast; rfl
      rw [this, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ ↦ ?_; ring
    rw [sum_mul_eq_by_parts, hR]
    have hexp : (w i K : ℂ) * A K + (((w i 0 - w i K : ℝ) : ℂ) * S
          + ∑ j ∈ range K, ((w i j - w i (j + 1) : ℝ) : ℂ) * (A (j + 1) - S)) - S
        = (w i K : ℂ) * (A K - S) + ((w i 0 - 1 : ℝ) : ℂ) * S
          + ∑ j ∈ range K, ((w i j - w i (j + 1) : ℝ) : ℂ) * (A (j + 1) - S) := by
      push_cast; ring
    rw [hexp]
    have hwK : 0 ≤ w i K := hni K
    have hwK0 : w i K ≤ w i 0 := hai (Nat.zero_le K)
    have t1 : ‖(w i K : ℂ) * (A K - S)‖ ≤ 2 * δ := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hwK]
      exact mul_le_mul (hwK0.trans h1) (hJ K hK) (norm_nonneg _) (by norm_num)
    have t2 : ‖((w i 0 - 1 : ℝ) : ℂ) * S‖ ≤ δ := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]; exact h2
    have t3 : ‖∑ j ∈ range K, ((w i j - w i (j + 1) : ℝ) : ℂ) * (A (j + 1) - S)‖ ≤ 3 * δ := by
      have hc : ∀ j, 0 ≤ w i j - w i (j + 1) := fun j ↦ sub_nonneg.2 (hai (Nat.le_succ j))
      calc ‖∑ j ∈ range K, ((w i j - w i (j + 1) : ℝ) : ℂ) * (A (j + 1) - S)‖
          ≤ ∑ j ∈ range K, (w i j - w i (j + 1)) * ‖A (j + 1) - S‖ := by
            refine (norm_sum_le _ _).trans (le_of_eq ?_)
            refine Finset.sum_congr rfl fun j _ ↦ ?_
            rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hc j)]
        _ ≤ ∑ j ∈ range K, ((w i j - w i (j + 1)) * (if j < J then C else 0)
              + (w i j - w i (j + 1)) * δ) := by
            refine Finset.sum_le_sum fun j _ ↦ ?_
            rw [← mul_add]
            refine mul_le_mul_of_nonneg_left ?_ (hc j)
            split_ifs with hj
            · linarith [hC (j + 1)]
            · simp only [zero_add]; exact hJ _ (by omega)
        _ = C * (w i 0 - w i J) + δ * (w i 0 - w i K) := by
            rw [Finset.sum_add_distrib]
            congr 1
            · have hsplit : ∑ j ∈ range K, (w i j - w i (j + 1)) * (if j < J then C else 0)
                  = ∑ j ∈ range J, (w i j - w i (j + 1)) * C := by
                rw [← Finset.sum_range_add_sum_Ico _ hK]
                have : ∑ j ∈ Finset.Ico J K, (w i j - w i (j + 1)) * (if j < J then C else 0) = 0 :=
                  Finset.sum_eq_zero fun j hj ↦ by
                    simp only [Finset.mem_Ico] at hj; simp [show ¬ j < J by omega]
                rw [this, add_zero]
                refine Finset.sum_congr rfl fun j hj ↦ ?_
                simp only [Finset.mem_range] at hj; simp [hj]
              rw [hsplit, ← Finset.sum_mul, Finset.sum_range_sub' (fun j ↦ w i j), mul_comm]
            · rw [← Finset.sum_mul, Finset.sum_range_sub' (fun j ↦ w i j), mul_comm]
        _ ≤ δ + δ * 2 := by
            have : δ * (w i 0 - w i K) ≤ δ * 2 :=
              mul_le_mul_of_nonneg_left (by linarith) hδpos.le
            linarith
        _ = 3 * δ := by ring
    calc _ ≤ ‖(w i K : ℂ) * (A K - S) + ((w i 0 - 1 : ℝ) : ℂ) * S‖
          + ‖∑ j ∈ range K, ((w i j - w i (j + 1) : ℝ) : ℂ) * (A (j + 1) - S)‖ := norm_add_le _ _
      _ ≤ (2 * δ + δ) + 3 * δ := add_le_add ((norm_add_le _ _).trans (add_le_add t1 t2)) t3
      _ = 6 * δ := by ring
  have hlim := hsi.hasSum.tendsto_sum_nat
  have : ‖∑' n, a n * (w i n : ℂ) - S‖ ≤ 6 * δ := by
    have ht : Tendsto (fun K ↦ ‖∑ n ∈ range K, a n * (w i n : ℂ) - S‖) atTop
        (𝓝 ‖∑' n, a n * (w i n : ℂ) - S‖) := (hlim.sub_const S).norm
    exact le_of_tendsto ht (eventually_atTop.2 ⟨J, hbound⟩)
  rw [dist_eq_norm]
  calc _ ≤ 6 * δ := this
    _ < ε := by rw [hδ]; linarith

lemma term_succ_eq (ψ : DirichletCharacter ℂ N) {ε : ℝ} (n : ℕ) :
    LSeries.term (fun k ↦ ψ k) (1 + ε) (n + 1)
      = ψ ((n + 1 : ℕ) : ZMod N) / ((n + 1 : ℕ) : ℂ) * ((((n : ℝ) + 1) ^ (-ε) : ℝ) : ℂ) := by
  rw [LSeries.term_of_ne_zero (Nat.succ_ne_zero n)]
  have hx : ((n + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  rw [cpow_add _ _ hx, cpow_one]
  have hpos : (0 : ℝ) ≤ (n : ℝ) + 1 := by positivity
  rw [Real.rpow_neg hpos, Complex.ofReal_inv, Complex.ofReal_cpow hpos]
  push_cast
  field_simp

/-- The value `L(1, ψ)` is the (conditionally convergent) sum `∑ ψ(n)/n`. -/
lemma LFunction_one_eq (ψ : DirichletCharacter ℂ N) (hψ : ψ ≠ 1) {S : ℂ}
    (hS : Tendsto (fun K ↦ ∑ n ∈ range K, ψ (n : ZMod N) / n) atTop (𝓝 S)) :
    ψ.LFunction 1 = S := by
  set a : ℕ → ℂ := fun n ↦ ψ ((n + 1 : ℕ) : ZMod N) / ((n + 1 : ℕ) : ℂ) with ha
  have hA : Tendsto (fun K ↦ ∑ n ∈ range K, a n) atTop (𝓝 S) := by
    have := (tendsto_add_atTop_iff_nat 1).2 hS
    refine this.congr fun K ↦ ?_
    rw [Finset.sum_range_succ']
    simp [ha]
  set w : ℝ → ℕ → ℝ := fun ε n ↦ ((n : ℝ) + 1) ^ (-ε) with hw
  have hpos : ∀ᶠ ε : ℝ in 𝓝[>] 0, 0 < ε := self_mem_nhdsWithin
  have hanti : ∀ᶠ ε in 𝓝[>] (0:ℝ), Antitone (w ε) := by
    filter_upwards [hpos] with ε hε
    intro m n hmn
    simp only [hw]
    have hmn' : (m : ℝ) + 1 ≤ (n : ℝ) + 1 := by
      have : (m : ℝ) ≤ n := by exact_mod_cast hmn
      linarith
    exact Real.rpow_le_rpow_of_nonpos (by positivity) hmn' (by linarith)
  have hnn : ∀ᶠ ε in 𝓝[>] (0:ℝ), ∀ n, 0 ≤ w ε n :=
    Filter.Eventually.of_forall fun ε n ↦ by simp only [hw]; positivity
  have hz : ∀ᶠ ε in 𝓝[>] (0:ℝ), Tendsto (w ε) atTop (𝓝 0) := by
    filter_upwards [hpos] with ε hε
    have h1 := tendsto_rpow_neg_atTop hε
    have h2 : Tendsto (fun n : ℕ ↦ (n : ℝ) + 1) atTop atTop :=
      tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
    exact h1.comp h2
  have hpt : ∀ n, Tendsto (fun ε ↦ w ε n) (𝓝[>] 0) (𝓝 1) := by
    intro n
    have hc : ContinuousAt (fun ε : ℝ ↦ ((n : ℝ) + 1) ^ (-ε)) 0 := by
      refine ContinuousAt.rpow continuousAt_const continuousAt_id.neg (Or.inl (by positivity))
    have := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0:ℝ)))
    simpa [hw] using this
  have hsumm : ∀ᶠ ε in 𝓝[>] (0:ℝ), Summable (fun n ↦ a n * (w ε n : ℂ)) := by
    filter_upwards [hpos] with ε hε
    have hs : LSeriesSummable (fun k ↦ ψ k) (1 + ε) :=
      DirichletCharacter.LSeriesSummable_of_one_lt_re ψ (by simp; linarith)
    have := (summable_nat_add_iff 1).2 hs
    refine this.congr fun n ↦ ?_
    rw [term_succ_eq]
  have hmain := tendsto_tsum_weighted a hA w hanti hnn hz hpt hsumm
  have heq : ∀ᶠ ε in 𝓝[>] (0:ℝ), ∑' n, a n * (w ε n : ℂ) = ψ.LFunction (1 + ε) := by
    filter_upwards [hpos] with ε hε
    rw [DirichletCharacter.LFunction_eq_LSeries ψ (by simp; linarith), LSeries,
      (DirichletCharacter.LSeriesSummable_of_one_lt_re ψ (s := 1 + ε) (by simp; linarith)).tsum_eq_zero_add,
      LSeries.term_zero, zero_add]
    refine tsum_congr fun n ↦ ?_
    rw [term_succ_eq]
  have hcont : Tendsto (fun ε : ℝ ↦ ψ.LFunction (1 + ε)) (𝓝[>] 0) (𝓝 (ψ.LFunction 1)) := by
    have hc : Continuous ψ.LFunction := (DirichletCharacter.differentiable_LFunction hψ).continuous
    have : Tendsto (fun ε : ℝ ↦ (1 : ℂ) + ε) (𝓝[>] 0) (𝓝 1) := by
      have hc1 : Continuous (fun ε : ℝ ↦ (1 : ℂ) + ε) := by fun_prop
      have h := hc1.tendsto (0 : ℝ)
      simpa using h.mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0:ℝ)))
    exact (hc.tendsto 1).comp this
  exact tendsto_nhds_unique (hcont.congr' (heq.mono fun ε h ↦ h.symm)) hmain

/-- **Analytic core.** For an even primitive Dirichlet character `ψ ≠ 1`,
`∑_w ψ⁻¹(w) log ‖1 - e(w)‖ ≠ 0`. -/
theorem sum_inv_mul_log_ne_zero (ψ : DirichletCharacter ℂ N) (hψ : ψ ≠ 1)
    (hprim : ψ.IsPrimitive) (hev : ψ.Even) :
    ∑ w : ZMod N, ψ⁻¹ w * (Real.log ‖1 - e w‖ : ℂ) ≠ 0 := by
  obtain ⟨S, hS⟩ := exists_tendsto_sum ψ hψ
  have h1 := gauss_mul_S ψ hψ hprim hev hS
  have h2 : S ≠ 0 := by
    rw [← LFunction_one_eq ψ hψ hS]; exact DirichletCharacter.LFunction_apply_one_ne_zero hψ
  have h3 := gaussSum_ne_zero ψ⁻¹ (isPrimitive_inv ψ hprim)
  intro h
  rw [h, neg_zero] at h1
  exact mul_ne_zero h3 h2 h1

end TwoPrimes


-- ===== Norms =====

open Complex Finset ZMod


/-!
# Lemma 2(c) for MO 503314: from equal log-products to equal character sums.
-/

namespace TwoPrimes

variable {N : ℕ} [NeZero N]

local notation "e" => (ZMod.stdAddChar : AddChar (ZMod N) ℂ)

/-- For a primitive character, twisted sums of a dilated function vanish at non-units. -/
lemma sum_char_mul_comp_mul_nonunit (χ : DirichletCharacter ℂ N) (hχ : χ.IsPrimitive)
    (F : ZMod N → ℂ) {a : ZMod N} (ha : ¬ IsUnit a) :
    ∑ u : ZMod N, χ u * F (u * a) = 0 := by
  have hF : ∀ y, F y = (N : ℂ)⁻¹ * ∑ j : ZMod N, e (j * y) * 𝓕 F j := by
    intro y
    have := congrFun ((ZMod.dft (E := ℂ) (N := N)).symm_apply_apply F) y
    rw [← this, ZMod.invDFT_apply]
    simp [smul_eq_mul]
  simp_rw [hF, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun j _ ↦ ?_
  have hg : ∑ u : ZMod N, χ u * e (u * (j * a)) = 0 := by
    have h1 := gaussSum_mulShift_of_isPrimitive e hχ (j * a)
    have hnu : ¬ IsUnit (j * a) := fun h ↦ ha (isUnit_of_mul_isUnit_right h)
    rw [MulChar.map_nonunit _ hnu, zero_mul] at h1
    rw [← h1, gaussSum]
    refine Finset.sum_congr rfl fun u _ ↦ ?_
    rw [AddChar.mulShift_apply, mul_comm (j * a) u]
  calc ∑ u : ZMod N, χ u * ((N : ℂ)⁻¹ * (e (j * (u * a)) * 𝓕 F j))
      = (N : ℂ)⁻¹ * 𝓕 F j * ∑ u : ZMod N, χ u * e (u * (j * a)) := by
        rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun u _ ↦ ?_; ring_nf
    _ = 0 := by rw [hg, mul_zero]

/-- At a unit, the twisted sum picks up a character value. -/
lemma sum_char_mul_comp_mul_unit (χ : DirichletCharacter ℂ N) (F : ZMod N → ℂ) (a : (ZMod N)ˣ) :
    ∑ u : ZMod N, χ u * F (u * a) = χ⁻¹ a * ∑ u : ZMod N, χ u * F u := by
  rw [Finset.mul_sum]
  refine Fintype.sum_equiv (Units.mulRight a) _ _ (fun u ↦ ?_)
  simp only [Units.mulRight_apply]
  have h1 : χ⁻¹ (a : ZMod N) * χ a = 1 := by
    rw [← MulChar.mul_apply, inv_mul_cancel, MulChar.one_apply_coe]
  rw [map_mul]
  linear_combination (χ u * F (u * a)) * h1.symm

/-- **Lemma 2(c), character form.** Equal log-products at all units force equal sums of an even
primitive character over the unit exponents. -/
theorem charsum_eq_of_logprod (ψ : DirichletCharacter ℂ N) (hψ : ψ ≠ 1) (hprim : ψ.IsPrimitive)
    (hev : ψ.Even) (X₁ X₂ : Finset (ZMod N))
    (h : ∀ u : (ZMod N)ˣ, ∑ a ∈ X₁, Real.log ‖1 - e (u * a)‖ = ∑ a ∈ X₂, Real.log ‖1 - e (u * a)‖) :
    ∑ a ∈ X₁ with IsUnit a, ψ a = ∑ a ∈ X₂ with IsUnit a, ψ a := by
  set F : ZMod N → ℂ := fun y ↦ (Real.log ‖1 - e y‖ : ℂ) with hFdef
  set T : ℂ := ∑ u : ZMod N, ψ⁻¹ u * F u with hT
  have hT0 : T ≠ 0 := sum_inv_mul_log_ne_zero ψ hψ hprim hev
  have hprim' : (ψ⁻¹).IsPrimitive := isPrimitive_inv ψ hprim
  have key : ∀ X : Finset (ZMod N),
      ∑ u : ZMod N, ψ⁻¹ u * ∑ a ∈ X, F (u * a) = T * ∑ a ∈ X with IsUnit a, ψ a := by
    intro X
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm, Finset.sum_filter]
    refine Finset.sum_congr rfl fun a _ ↦ ?_
    split_ifs with ha
    · have := sum_char_mul_comp_mul_unit ψ⁻¹ F ha.unit
      simp only [IsUnit.unit_spec, inv_inv] at this
      rw [this, mul_comm]
    · exact sum_char_mul_comp_mul_nonunit ψ⁻¹ hprim' F ha
  have hL : ∑ u : ZMod N, ψ⁻¹ u * ∑ a ∈ X₁, F (u * a)
      = ∑ u : ZMod N, ψ⁻¹ u * ∑ a ∈ X₂, F (u * a) := by
    refine Finset.sum_congr rfl fun u _ ↦ ?_
    by_cases hu : IsUnit u
    · refine congrArg (ψ⁻¹ u * ·) ?_
      have := h hu.unit
      simp only [IsUnit.unit_spec] at this
      simp only [hFdef]
      exact_mod_cast this
    · rw [MulChar.map_nonunit _ hu, zero_mul, zero_mul]
  rw [key, key] at hL
  exact mul_left_cancel₀ hT0 hL

/-! ## Fourier lemmas for Lemma 3 -/

/-- A function invariant under translation by `c` has vanishing Fourier coefficients at every `k`
with `e (k * c) ≠ 1`. -/
lemma sum_mul_e_eq_zero_of_periodic (F : ZMod N → ℂ) (c k : ZMod N) (hF : ∀ x, F (x + c) = F x)
    (hk : e (k * c) ≠ 1) : ∑ x : ZMod N, F x * e (k * x) = 0 := by
  have h : ∑ x : ZMod N, F x * e (k * x) = e (k * c) * ∑ x : ZMod N, F x * e (k * x) := by
    rw [Finset.mul_sum]
    refine (Fintype.sum_equiv (Equiv.subRight c) _ _ (fun x ↦ ?_))
    have hx : F (x - c) = F x := by simpa using (hF (x - c)).symm
    simp only [Equiv.subRight_apply, hx, mul_sub, AddChar.map_sub_eq_div]
    have : e (k * c) ≠ 0 := by
      intro h0; have := norm_e (k * c); rw [h0, norm_zero] at this; exact zero_ne_one this
    field_simp
  have h2 : (1 - e (k * c)) * ∑ x : ZMod N, F x * e (k * x) = 0 := by
    rw [sub_mul, one_mul, ← h, sub_self]
  rcases mul_eq_zero.1 h2 with h3 | h3
  · exact absurd (sub_eq_zero.1 h3).symm hk
  · exact h3

/-- A function supported on `{x | c * x = 0}` has `c`-periodic Fourier coefficients. -/
lemma sum_mul_e_periodic_of_support (E : ZMod N → ℂ) (c : ZMod N)
    (hE : ∀ x, c * x ≠ 0 → E x = 0) (k : ZMod N) :
    ∑ x : ZMod N, E x * e ((k + c) * x) = ∑ x : ZMod N, E x * e (k * x) := by
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  by_cases hx : c * x = 0
  · rw [add_mul, hx, add_zero]
  · rw [hE x hx, zero_mul, zero_mul]

/-- Three-point weights: for distinct nonzero `z₁ z₂ z₃`, the Lagrange weights
`wᵢ = zᵢ / ∏_{j ≠ i} (zᵢ - zⱼ)` satisfy `∑ w = 0`, `∑ w z = 1`, `∑ w / z = 0`. -/
lemma three_point_weights {z₁ z₂ z₃ : ℂ} (h₁ : z₁ ≠ 0) (h₂ : z₂ ≠ 0) (h₃ : z₃ ≠ 0)
    (h12 : z₁ ≠ z₂) (h13 : z₁ ≠ z₃) (h23 : z₂ ≠ z₃) :
    let w₁ := z₁ / ((z₁ - z₂) * (z₁ - z₃))
    let w₂ := z₂ / ((z₂ - z₁) * (z₂ - z₃))
    let w₃ := z₃ / ((z₃ - z₁) * (z₃ - z₂))
    w₁ + w₂ + w₃ = 0 ∧ w₁ * z₁ + w₂ * z₂ + w₃ * z₃ = 1 ∧ w₁ / z₁ + w₂ / z₂ + w₃ / z₃ = 0 := by
  intro w₁ w₂ w₃
  have a := sub_ne_zero.2 h12
  have b := sub_ne_zero.2 h13
  have c := sub_ne_zero.2 h23
  have a' := sub_ne_zero.2 h12.symm
  have b' := sub_ne_zero.2 h13.symm
  have c' := sub_ne_zero.2 h23.symm
  refine ⟨?_, ?_, ?_⟩
  · simp only [w₁, w₂, w₃]; field_simp; ring
  · simp only [w₁, w₂, w₃]; field_simp; ring
  · simp only [w₁, w₂, w₃]; field_simp; ring

/-! ## Norms: sums of `log ‖1 - e(u a)‖` over units -/

lemma isPrimitiveRoot_e (a : ZMod N) : IsPrimitiveRoot (e a) (addOrderOf a) := by
  have hinj : Function.Injective (AddChar.toMonoidHom e) := by
    intro x y hxy
    exact Multiplicative.toAdd.injective (ZMod.injective_stdAddChar hxy)
  have h := orderOf_injective (AddChar.toMonoidHom e) hinj (Multiplicative.ofAdd a)
  rw [orderOf_ofAdd_eq_addOrderOf] at h
  have h2 : (AddChar.toMonoidHom e) (Multiplicative.ofAdd a) = e a := rfl
  rw [h2] at h
  rw [← h]
  exact IsPrimitiveRoot.orderOf _

lemma e_mul (u a : ZMod N) : e (u * a) = e a ^ u.val := by
  conv_lhs => rw [← ZMod.natCast_zmod_val u]
  rw [← nsmul_eq_mul, AddChar.map_nsmul_eq_pow]

/-- Sum over a surjective group hom: each fibre has the size of the kernel. -/
lemma sum_comp_surj {G H : Type*} [Group G] [Group H] [Fintype G] [Fintype H] [DecidableEq H]
    (f : G →* H) (hf : Function.Surjective f) (g : H → ℝ) :
    ∑ x : G, g (f x) = (Fintype.card f.ker : ℝ) * ∑ y : H, g y := by
  classical
  rw [← Finset.sum_fiberwise Finset.univ f (fun x ↦ g (f x))]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ ↦ ?_
  have hfib : (Finset.univ.filter fun x ↦ f x = y).card = Fintype.card f.ker := by
    obtain ⟨x0, rfl⟩ := hf y
    have := MonoidHom.card_fiber_eq_of_mem_range f (x := f x0) (y := 1) ⟨x0, rfl⟩ ⟨1, map_one f⟩
    rw [Fintype.card_subtype]
    convert this using 2
    · simp [MonoidHom.mem_ker]
  rw [Finset.sum_congr rfl (g := fun _ ↦ g y) (by intro x hx; simp only [Finset.mem_filter] at hx; rw [hx.2]),
    Finset.sum_const, hfib, nsmul_eq_mul]

/-- Product of `1 - ζ^v` over units `v` mod `o` is the cyclotomic value at `1`. -/
lemma prod_units_one_sub_pow {o : ℕ} [NeZero o] {ζ : ℂ} (hζ : IsPrimitiveRoot ζ o) :
    ∏ v : (ZMod o)ˣ, (1 - ζ ^ (v : ZMod o).val) = (Polynomial.cyclotomic o ℂ).eval 1 := by
  classical
  have ho : 0 < o := Nat.pos_of_ne_zero (NeZero.ne o)
  rw [Polynomial.cyclotomic_eq_prod_X_sub_primitiveRoots hζ, Polynomial.eval_prod]
  simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
  have hinj : Set.InjOn (fun v : (ZMod o)ˣ ↦ ζ ^ (v : ZMod o).val) ↑(Finset.univ : Finset (ZMod o)ˣ) := by
    intro v _ w _ hvw
    have := hζ.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) hvw
    exact Units.ext (ZMod.val_injective o this)
  have hsub : Finset.univ.image (fun v : (ZMod o)ˣ ↦ ζ ^ (v : ZMod o).val) ⊆ primitiveRoots o ℂ := by
    intro μ hμ
    obtain ⟨v, -, rfl⟩ := Finset.mem_image.1 hμ
    rw [mem_primitiveRoots ho]
    refine hζ.pow_of_coprime _ ?_
    have := ZMod.val_coe_unit_coprime v
    exact this
  have hcard : (primitiveRoots o ℂ).card ≤ (Finset.univ.image fun v : (ZMod o)ˣ ↦ ζ ^ (v : ZMod o).val).card := by
    rw [Finset.card_image_of_injOn hinj, hζ.card_primitiveRoots, Finset.card_univ,
      ZMod.card_units_eq_totient]
  have heq := Finset.eq_of_subset_of_card_le hsub hcard
  rw [← heq, Finset.prod_image hinj]

/-- **Norm lemma.** For `a ≠ 0` of additive order `o`, the sum of `log ‖1 - e(u a)‖` over units `u`
is `|ker| · log ‖Φ_o(1)‖`. -/
lemma sum_log_units (a : ZMod N) (ha : a ≠ 0) {o : ℕ} (ho : addOrderOf a = o) (hodvd : o ∣ N) :
    ∑ u : (ZMod N)ˣ, Real.log ‖1 - e (u * a)‖
      = (Fintype.card (ZMod.unitsMap hodvd).ker : ℝ)
        * Real.log ‖(Polynomial.cyclotomic o ℂ).eval 1‖ := by
  classical
  have hopos : 0 < o := ho ▸ addOrderOf_pos a
  haveI : NeZero o := ⟨hopos.ne'⟩
  have ho2 : 2 ≤ o := by
    rcases Nat.lt_or_ge o 2 with h | h
    · have h1 : addOrderOf a = 1 := by omega
      exact absurd (AddMonoid.addOrderOf_eq_one_iff.1 h1) ha
    · exact h
  have hζ : IsPrimitiveRoot (e a) o := ho ▸ isPrimitiveRoot_e a
  set g : (ZMod o)ˣ → ℝ := fun v ↦ Real.log ‖1 - e a ^ (v : ZMod o).val‖ with hg
  have hcomp : ∀ u : (ZMod N)ˣ, Real.log ‖1 - e (u * a)‖ = g (ZMod.unitsMap hodvd u) := by
    intro u
    simp only [hg, ZMod.unitsMap_def, Units.coe_map, MonoidHom.coe_coe, ZMod.castHom_apply]
    rw [e_mul, ZMod.cast_eq_val, ZMod.val_natCast]
    have hmod : ∀ n : ℕ, e a ^ (n % o) = e a ^ n := by
      intro n
      conv_rhs => rw [← Nat.mod_add_div n o]
      rw [pow_add, pow_mul, hζ.pow_eq_one, one_pow, mul_one]
    rw [hmod]
  simp_rw [hcomp]
  rw [sum_comp_surj _ (ZMod.unitsMap_surjective hodvd) g]
  congr 1
  rw [← prod_units_one_sub_pow hζ, norm_prod, Real.log_prod]
  intro v _
  rw [norm_ne_zero_iff, sub_ne_zero]
  intro h
  have h1 := (hζ.pow_eq_one_iff_dvd _).1 h.symm
  have hv : (v : ZMod o).val = 0 := Nat.eq_zero_of_dvd_of_lt h1 (ZMod.val_lt _)
  have : (v : ZMod o) = 0 := (ZMod.val_eq_zero _).1 hv
  have hnu := v.isUnit
  rw [this] at hnu
  have : Fact (1 < o) := ⟨by omega⟩
  exact not_isUnit_zero hnu

/-- For a divisor `o ≥ 2` of a squarefree number, `log ‖Φ_o(1)‖` is `log o` if `o` is prime, else `0`. -/
lemma log_norm_cyclotomic_one {o : ℕ} (hsq : Squarefree o) (ho : 2 ≤ o) :
    Real.log ‖(Polynomial.cyclotomic o ℂ).eval 1‖ = if o.Prime then Real.log o else 0 := by
  split_ifs with hp
  · have : Fact o.Prime := ⟨hp⟩
    rw [Polynomial.eval_one_cyclotomic_prime, Complex.norm_natCast]
  · rw [Polynomial.eval_one_cyclotomic_not_prime_pow, norm_one, Real.log_one]
    intro q hq k hk
    rcases k with _ | _ | k
    · simp at hk; omega
    · simp at hk; exact hp (hk ▸ hq)
    · have : q * q ∣ o := ⟨q ^ k, by rw [← hk]; ring⟩
      have := hsq q this
      exact hq.one_lt.ne' (Nat.isUnit_iff.1 this)

end TwoPrimes

-- ===== UnitDFT =====

/-!
# DFT injectivity relative to a set of primes (MO 503314, replaces `τ(χ) ≠ 0`)

Let `T` be a set of primes `p ∣ N` with `p² ∤ N`.  A function on `ZMod N` vanishing at every `x`
divisible by some `p ∈ T`, whose additive Fourier coefficients vanish at every frequency prime to
all of `T`, is zero.  Proof: the coefficients at the other frequencies vanish too, by induction on
the number of `p ∈ T` dividing the frequency (sum over the fibre `k + (N/p) i`).
-/

open Complex Finset

namespace TwoPrimes

variable {N : ℕ} [NeZero N]

local notation "e" => (ZMod.stdAddChar : AddChar (ZMod N) ℂ)

/-- `x` is prime to every `p ∈ T`. -/
def Cop (T : Finset ℕ) (x : ZMod N) : Prop := ∀ p ∈ T, (ZMod.cast x : ZMod p) ≠ 0

/-- The number of `p ∈ T` dividing `k`. -/
noncomputable def nuT (T : Finset ℕ) (k : ZMod N) : ℕ :=
  (T.filter (fun p ↦ (ZMod.cast k : ZMod p) = 0)).card

lemma cast_eq_zero_iff_dvd_val {p : ℕ} (k : ZMod N) : (ZMod.cast k : ZMod p) = 0 ↔ p ∣ k.val := by
  rw [ZMod.cast_eq_val, ZMod.natCast_eq_zero_iff]

lemma cop_of_nuT_eq_zero {T : Finset ℕ} {k : ZMod N} (h : nuT T k = 0) : Cop T k := by
  intro p hp hpk
  rw [nuT, Finset.card_eq_zero, Finset.filter_eq_empty_iff] at h
  exact h hp hpk

lemma e_eq_one_iff (y : ZMod N) : e y = 1 ↔ y = 0 := by
  constructor
  · intro h
    apply ZMod.injective_stdAddChar
    rw [h, AddChar.map_zero_eq_one]
  · rintro rfl; exact AddChar.map_zero_eq_one _

lemma nat_dvd_div_mul_iff {N p v : ℕ} (hN : 0 < N) (hp : 0 < p) (hpN : p ∣ N) :
    N ∣ N / p * v ↔ p ∣ v := by
  obtain ⟨k, rfl⟩ := hpN
  have hk : 0 < k := Nat.pos_of_mul_pos_left hN
  rw [Nat.mul_div_cancel_left k hp, mul_comm k v]
  exact Nat.mul_dvd_mul_iff_right hk

lemma nat_dvd_mul_iff_div {N q v : ℕ} (hq : 0 < q) (hqN : q ∣ N) :
    N ∣ q * v ↔ N / q ∣ v := by
  obtain ⟨k, rfl⟩ := hqN
  rw [Nat.mul_div_cancel_left k hq]
  exact Nat.mul_dvd_mul_iff_left hq

/-- `(N/p) * y = 0` iff `p ∣ y`. -/
lemma natDiv_mul_eq_zero_iff {p : ℕ} (hp : p.Prime) (hpN : p ∣ N) (y : ZMod N) :
    ((N / p : ℕ) : ZMod N) * y = 0 ↔ (ZMod.cast y : ZMod p) = 0 := by
  rw [cast_eq_zero_iff_dvd_val]
  conv_lhs => rw [← ZMod.natCast_zmod_val y, ← Nat.cast_mul, ZMod.natCast_eq_zero_iff]
  exact nat_dvd_div_mul_iff (Nat.pos_of_ne_zero (NeZero.ne N)) hp.pos hpN

/-- The fibre sum of Fourier coefficients over `k + (N/p) i` vanishes. -/
lemma sum_fibre_dft_eq_zero (A : ZMod N → ℂ) {p : ℕ} (hp : p.Prime) (hpN : p ∣ N)
    (hA : ∀ x, (ZMod.cast x : ZMod p) = 0 → A x = 0) (k : ZMod N) :
    ∑ i ∈ range p, ∑ x : ZMod N, A x * e ((k + ((N / p : ℕ) : ZMod N) * ((i : ℕ) : ZMod N)) * x) = 0 := by
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun x _ ↦ ?_
  by_cases hx : (ZMod.cast x : ZMod p) = 0
  · simp [hA x hx]
  · set z := e (((N / p : ℕ) : ZMod N) * x) with hz
    have hsplit : ∀ i : ℕ, e ((k + ((N / p : ℕ) : ZMod N) * ((i : ℕ) : ZMod N)) * x) = e (k * x) * z ^ i := by
      intro i
      rw [hz, ← AddChar.map_nsmul_eq_pow, ← AddChar.map_add_eq_mul]
      congr 1
      rw [nsmul_eq_mul]; ring
    simp_rw [hsplit]
    rw [← Finset.mul_sum, ← Finset.mul_sum (s := range p) (f := fun i ↦ z ^ i)]
    have hz1 : z ≠ 1 := by
      rw [hz, Ne, e_eq_one_iff, natDiv_mul_eq_zero_iff hp hpN]
      exact hx
    have hzp : z ^ p = 1 := by
      rw [hz, ← AddChar.map_nsmul_eq_pow, nsmul_eq_mul, ← mul_assoc, ← Nat.cast_mul,
        Nat.mul_div_cancel' hpN, ZMod.natCast_self, zero_mul, AddChar.map_zero_eq_one]
    rw [geom_sum_eq hz1, hzp, sub_self, zero_div]; simp

/-- Hypotheses on `T`: primes dividing `N` exactly once. -/
def GoodPrimes (N : ℕ) (T : Finset ℕ) : Prop := ∀ p ∈ T, p.Prime ∧ p ∣ N ∧ ¬ p * p ∣ N

lemma nuT_lt {T : Finset ℕ} (hT : GoodPrimes N T) {p : ℕ} (hpT : p ∈ T) (k : ZMod N)
    (hpk : (ZMod.cast k : ZMod p) = 0) {i : ℕ} (hi0 : 0 < i) (hip : i < p) :
    nuT T (k + ((N / p : ℕ) : ZMod N) * ((i : ℕ) : ZMod N)) < nuT T k := by
  obtain ⟨hp, hpN, hsq⟩ := hT p hpT
  unfold nuT
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset]
  · refine ⟨p, Finset.mem_filter.2 ⟨hpT, hpk⟩, ?_⟩
    rw [Finset.mem_filter, ZMod.cast_add hpN, ZMod.cast_mul hpN, ZMod.cast_natCast hpN,
      ZMod.cast_natCast hpN, hpk, zero_add]
    rintro ⟨-, h⟩
    haveI : Fact p.Prime := ⟨hp⟩
    rcases mul_eq_zero.1 h with h | h
    · rw [ZMod.natCast_eq_zero_iff] at h
      apply hsq
      have := Nat.mul_dvd_mul_left p h
      rwa [Nat.mul_div_cancel' hpN] at this
    · rw [ZMod.natCast_eq_zero_iff] at h
      exact absurd (Nat.le_of_dvd hi0 h) (not_le.2 hip)
  · intro q hq
    rw [Finset.mem_filter] at hq ⊢
    refine ⟨hq.1, ?_⟩
    obtain ⟨hqp', hqN, -⟩ := hT q hq.1
    have hq2 := hq.2
    rw [ZMod.cast_add hqN, ZMod.cast_mul hqN, ZMod.cast_natCast hqN, ZMod.cast_natCast hqN] at hq2
    by_cases hqp : q = p
    · subst hqp; exact hpk
    · have hq' : q ∣ N / p := by
        have hcop : Nat.Coprime q p := (Nat.coprime_primes hqp' hp).2 hqp
        exact hcop.dvd_of_dvd_mul_left (by rwa [Nat.mul_div_cancel' hpN])
      rw [(ZMod.natCast_eq_zero_iff _ _).2 hq', zero_mul, add_zero] at hq2
      exact hq2

/-- All Fourier coefficients vanish once they vanish at frequencies prime to `T`. -/
lemma dft_eq_zero_of_cop {T : Finset ℕ} (hT : GoodPrimes N T) (A : ZMod N → ℂ)
    (hA : ∀ x, ¬ Cop T x → A x = 0)
    (hF : ∀ k : ZMod N, Cop T k → ∑ x, A x * e (k * x) = 0) (k : ZMod N) :
    ∑ x, A x * e (k * x) = 0 := by
  induction hn : nuT T k using Nat.strong_induction_on generalizing k with
  | _ n ih =>
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · exact hF k (cop_of_nuT_eq_zero (hn.trans h0))
    · obtain ⟨p, hp⟩ := Finset.card_pos.1 (hn ▸ hpos : 0 < nuT T k)
      rw [Finset.mem_filter] at hp
      obtain ⟨hpp, hpN, -⟩ := hT p hp.1
      have hA' : ∀ x, (ZMod.cast x : ZMod p) = 0 → A x = 0 :=
        fun x hx ↦ hA x (fun h ↦ h p hp.1 hx)
      have h := sum_fibre_dft_eq_zero A hpp hpN hA' k
      rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot hpp.pos] at h
      have h2 : ∑ i ∈ Ico (0 + 1) p, ∑ x : ZMod N,
          A x * e ((k + ((N / p : ℕ) : ZMod N) * ((i : ℕ) : ZMod N)) * x) = 0 := by
        refine Finset.sum_eq_zero fun i hi ↦ ?_
        rw [Finset.mem_Ico] at hi
        exact ih _ (hn ▸ nuT_lt hT hp.1 k hp.2 (by omega) hi.2) _ rfl
      rw [h2, add_zero] at h
      simpa using h

/-- **DFT injectivity relative to `T`.** -/
theorem eq_zero_of_dft_cop {T : Finset ℕ} (hT : GoodPrimes N T) (A : ZMod N → ℂ)
    (hA : ∀ x, ¬ Cop T x → A x = 0)
    (hF : ∀ k : ZMod N, Cop T k → ∑ x, A x * e (k * x) = 0) : A = 0 := by
  have h : ZMod.dft A = ZMod.dft 0 := by
    ext k
    rw [ZMod.dft_apply, map_zero, Pi.zero_apply]
    have := dft_eq_zero_of_cop hT A hA hF (-k)
    rw [← this]
    refine Finset.sum_congr rfl fun x _ ↦ ?_
    rw [smul_eq_mul, mul_comm]; congr 2; ring
  exact ZMod.dft.injective h

end TwoPrimes

-- ===== Lemma3 =====

/-!
# Lemma 3 (K-invariance vanishing) for MO 503314, coordinate-free

`N` squarefree, `T` a nonempty set of prime factors of `N`, and for `p ∈ T` a unit `t p ≠ 1` with
`t p ^ 2 ≠ 1` and `t p ≡ 1 (mod N/p)`.  If `A, B` are invariant under every `t p` and
`A (x + 1) + B (x - 1) = ∑_{p ∈ T} F p x` whenever `x` is prime to every `p ∈ T`, where each
`F p` is `N/p`-periodic, then `Â` and `B̂` vanish at every unit.  The proof averages over the
three multipliers `1, t p, t p ^ 2` with Lagrange weights, one prime at a time (operator `Om`).
-/

open Complex Finset

namespace TwoPrimes

variable {N : ℕ} [NeZero N]

local notation "e" => (ZMod.stdAddChar : AddChar (ZMod N) ℂ)

/-- `n p = N / p` in `ZMod N`. -/
noncomputable abbrev nn (N p : ℕ) : ZMod N := ((N / p : ℕ) : ZMod N)

/-- `R` is `N/p`-periodic. -/
def Periodic' (p : ℕ) (R : ZMod N → ℂ) : Prop := ∀ k y : ZMod N, R (k + nn N p * y) = R k

lemma nn_mul_nn {p q : ℕ} (hp : p ∈ N.primeFactors) (hq : q ∈ N.primeFactors) (hpq : p ≠ q) :
    nn N p * nn N q = 0 := by
  have hpp := Nat.prime_of_mem_primeFactors hp
  have hqp := Nat.prime_of_mem_primeFactors hq
  have hcop : Nat.Coprime p q := (Nat.coprime_primes hpp hqp).2 hpq
  obtain ⟨r, hr⟩ := hcop.mul_dvd_of_dvd_of_dvd (Nat.dvd_of_mem_primeFactors hp)
    (Nat.dvd_of_mem_primeFactors hq)
  have h1 : N / p = q * r := by
    rw [hr, mul_assoc]; exact Nat.mul_div_cancel_left _ hpp.pos
  have h2 : N / q = p * r := by
    rw [hr, mul_comm p q, mul_assoc]; exact Nat.mul_div_cancel_left _ hqp.pos
  rw [nn, nn, ← Nat.cast_mul, h1, h2, ZMod.natCast_eq_zero_iff]
  exact ⟨r, by rw [hr]; ring⟩

lemma nn_ne_zero {p : ℕ} (hp : p ∈ N.primeFactors) : nn N p ≠ 0 := by
  have hpp := Nat.prime_of_mem_primeFactors hp
  have hpN := Nat.dvd_of_mem_primeFactors hp
  have hN : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  rw [nn, Ne, ZMod.natCast_eq_zero_iff]
  intro h
  have hpos : 0 < N / p := Nat.div_pos (Nat.le_of_dvd hN hpN) hpp.pos
  exact absurd (Nat.le_of_dvd hpos h) (not_le.2 (Nat.div_lt_self hN hpp.one_lt))

lemma nn_mul_eq_zero_iff {p : ℕ} (hp : p ∈ N.primeFactors) (y : ZMod N) :
    nn N p * y = 0 ↔ (ZMod.cast y : ZMod p) = 0 :=
  natDiv_mul_eq_zero_iff (Nat.prime_of_mem_primeFactors hp) (Nat.dvd_of_mem_primeFactors hp) y

lemma nn_mul_ne_zero {p : ℕ} (hp : p ∈ N.primeFactors) {k : ZMod N}
    (hk : (ZMod.cast k : ZMod p) ≠ 0) : nn N p * k ≠ 0 := by
  rw [Ne, nn_mul_eq_zero_iff hp]; exact hk

lemma nn_mul_eq_zero_of_cast {p : ℕ} (hp : p ∈ N.primeFactors) {x : ZMod N}
    (hx : (ZMod.cast x : ZMod p) = 0) : nn N p * x = 0 := (nn_mul_eq_zero_iff hp x).2 hx

lemma cast_ne_zero_of_isUnit {q : ℕ} (hq : q ∈ N.primeFactors) {t : ZMod N} (ht : IsUnit t) :
    (ZMod.cast t : ZMod q) ≠ 0 := by
  have hqp := Nat.prime_of_mem_primeFactors hq
  haveI : Fact q.Prime := ⟨hqp⟩
  have hu : IsUnit (ZMod.cast t : ZMod q) := by
    have := ht.map (ZMod.castHom (Nat.dvd_of_mem_primeFactors hq) (ZMod q))
    simpa using this
  exact hu.ne_zero

lemma cop_mul {T : Finset ℕ} (hT : T ⊆ N.primeFactors) {t k : ZMod N} (ht : IsUnit t)
    (hk : Cop T k) : Cop T (t * k) := by
  intro q hq
  haveI : Fact q.Prime := ⟨Nat.prime_of_mem_primeFactors (hT hq)⟩
  rw [ZMod.cast_mul (Nat.dvd_of_mem_primeFactors (hT hq))]
  exact mul_ne_zero (cast_ne_zero_of_isUnit (hT hq) ht) (hk q hq)

lemma cop_neg {T : Finset ℕ} (hT : T ⊆ N.primeFactors) {k : ZMod N} (hk : Cop T k) :
    Cop T (-k) := by
  intro q hq
  rw [ZMod.cast_neg (Nat.dvd_of_mem_primeFactors (hT hq)), neg_ne_zero]
  exact hk q hq

lemma e_ne_zero (y : ZMod N) : e y ≠ 0 := by
  intro h; have := norm_e y; rw [h, norm_zero] at this; exact zero_ne_one this

/-! ### The averaging operator -/

/-- The three multipliers `1, t, t²`. -/
def tau (t : ZMod N) : Fin 3 → ZMod N := ![1, t, t ^ 2]

/-- Lagrange weights for three points. -/
noncomputable def wt (z₁ z₂ z₃ : ℂ) : Fin 3 → ℂ :=
  ![z₁ / ((z₁ - z₂) * (z₁ - z₃)), z₂ / ((z₂ - z₁) * (z₂ - z₃)), z₃ / ((z₃ - z₁) * (z₃ - z₂))]

/-- The points `e((τ - 1) k)`. -/
noncomputable def zz (t k : ZMod N) (a : Fin 3) : ℂ := e ((tau t a - 1) * k)

noncomputable def ww (t k : ZMod N) : Fin 3 → ℂ := wt (zz t k 0) (zz t k 1) (zz t k 2)

/-- The averaging operator attached to `t`. -/
noncomputable def Om (t : ZMod N) (Q : ZMod N → ℂ) (k : ZMod N) : ℂ :=
  ∑ a : Fin 3, ww t k a * Q (tau t a * k)

/-- Hypotheses on a multiplier for the prime `p`. -/
structure GoodMult (p : ℕ) (t : ZMod N) : Prop where
  isunit : IsUnit t
  ne_one : t ≠ 1
  sq_ne_one : t ^ 2 ≠ 1
  cong : ∃ a : ZMod N, t = 1 + nn N p * a

lemma tau_isUnit {t : ZMod N} (ht : IsUnit t) (a : Fin 3) : IsUnit (tau t a) := by
  fin_cases a <;> simp [tau, ht, ht.pow]

lemma tau_sub_one {p : ℕ} {t : ZMod N} (ht : GoodMult p t) (a : Fin 3) :
    ∃ b, tau t a - 1 = nn N p * b := by
  obtain ⟨c, hc⟩ := ht.cong
  fin_cases a
  · exact ⟨0, by simp [tau]⟩
  · exact ⟨c, by simp [tau, hc]⟩
  · exact ⟨c * (t + 1), by simp only [tau]; simp; rw [hc]; ring⟩

lemma tau_mul_eq {p : ℕ} {t : ZMod N} (ht : GoodMult p t) (a : Fin 3) (k : ZMod N) :
    ∃ b, tau t a * k = k + nn N p * b := by
  obtain ⟨b, hb⟩ := tau_sub_one ht a
  exact ⟨b * k, by rw [← mul_assoc, ← hb]; ring⟩

lemma zz_injective {p : ℕ} (hp : p ∈ N.primeFactors) {t : ZMod N} (ht : GoodMult p t)
    {k : ZMod N} (hk : (ZMod.cast k : ZMod p) ≠ 0) : Function.Injective (zz t k) := by
  intro a b hab
  have h1 := ZMod.injective_stdAddChar hab
  have h2 : tau t a = tau t b := by
    obtain ⟨ba, hba⟩ := tau_sub_one ht a
    obtain ⟨bb, hbb⟩ := tau_sub_one ht b
    have h3 : nn N p * ((ba - bb) * k) = 0 := by
      have : (tau t a - 1) * k - (tau t b - 1) * k = 0 := sub_eq_zero.2 h1
      rw [hba, hbb] at this; rw [← this]; ring
    rw [nn_mul_eq_zero_iff hp] at h3
    haveI : Fact p.Prime := ⟨Nat.prime_of_mem_primeFactors hp⟩
    rw [ZMod.cast_mul (Nat.dvd_of_mem_primeFactors hp)] at h3
    have h4 := (mul_eq_zero.1 h3).resolve_right hk
    rw [← nn_mul_eq_zero_iff hp] at h4
    have : tau t a - 1 - (tau t b - 1) = 0 := by rw [hba, hbb, ← mul_sub, h4]
    exact sub_eq_zero.1 (by rw [← this]; ring)
  have hne1 := ht.ne_one
  have hne2 := ht.sq_ne_one
  have hne3 : t ^ 2 ≠ t := by
    intro h
    apply hne1
    have := congrArg (· * (ht.isunit.unit⁻¹ : (ZMod N)ˣ).1) h
    simpa [pow_two, mul_assoc] using this
  revert h2
  fin_cases a <;> fin_cases b <;> simp [tau] <;> intro h <;> first | exact absurd h hne1 | exact absurd h.symm hne1 | exact absurd h hne2 | exact absurd h.symm hne2 | exact absurd h hne3 | exact absurd h.symm hne3

lemma ww_sums {p : ℕ} (hp : p ∈ N.primeFactors) {t : ZMod N} (ht : GoodMult p t) {k : ZMod N}
    (hk : (ZMod.cast k : ZMod p) ≠ 0) :
    ∑ a, ww t k a = 0 ∧ ∑ a, ww t k a * zz t k a = 1 ∧ ∑ a, ww t k a / zz t k a = 0 := by
  have hinj := zz_injective hp ht hk
  have h := three_point_weights (e_ne_zero _) (e_ne_zero _) (e_ne_zero _)
    (fun h ↦ absurd (hinj h) (by decide : (0 : Fin 3) ≠ 1))
    (fun h ↦ absurd (hinj h) (by decide : (0 : Fin 3) ≠ 2))
    (fun h ↦ absurd (hinj h) (by decide : (1 : Fin 3) ≠ 2))
  simp only [Fin.sum_univ_three, ww, wt, zz]
  simpa [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two] using h

lemma zz_periodic {p q : ℕ} (hp : p ∈ N.primeFactors) (hq : q ∈ N.primeFactors) (hpq : p ≠ q)
    {t : ZMod N} (ht : GoodMult p t) (k y : ZMod N) (a : Fin 3) :
    zz t (k + nn N q * y) a = zz t k a := by
  obtain ⟨b, hb⟩ := tau_sub_one ht a
  simp only [zz]
  congr 1
  rw [hb, mul_add, show nn N p * b * (nn N q * y) = (nn N p * nn N q) * (b * y) by ring,
    nn_mul_nn hp hq hpq, zero_mul, add_zero]

/-- `Om` kills `N/p`-periodic functions. -/
lemma Om_periodic_self {p : ℕ} (hp : p ∈ N.primeFactors) {t : ZMod N} (ht : GoodMult p t)
    {R : ZMod N → ℂ} (hR : Periodic' p R) {k : ZMod N} (hk : (ZMod.cast k : ZMod p) ≠ 0) :
    Om t R k = 0 := by
  have h : ∀ a, R (tau t a * k) = R k := by
    intro a; obtain ⟨b, hb⟩ := tau_mul_eq ht a k; rw [hb, hR]
  simp only [Om, h, ← Finset.sum_mul, (ww_sums hp ht hk).1, zero_mul]

/-- `Om` for `p` preserves `N/q`-periodicity, `q ≠ p`. -/
lemma Om_periodic_other {p q : ℕ} (hp : p ∈ N.primeFactors) (hq : q ∈ N.primeFactors)
    (hpq : p ≠ q) {t : ZMod N} (ht : GoodMult p t) {R : ZMod N → ℂ} (hR : Periodic' q R) :
    Periodic' q (Om t R) := by
  intro k y
  simp only [Om, ww, zz_periodic hp hq hpq ht k y]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  congr 1
  rw [mul_add, show tau t a * (nn N q * y) = nn N q * (tau t a * y) by ring, hR]

lemma e_tau_mul {p : ℕ} {t : ZMod N} (ht : GoodMult p t) (k : ZMod N) (a : Fin 3) :
    e (tau t a * k) = e k * zz t k a := by
  rw [zz, ← AddChar.map_add_eq_mul]; congr 1; ring

/-- `Om` fixes `e · β` for `t`-invariant `β`. -/
lemma Om_e_mul {p : ℕ} (hp : p ∈ N.primeFactors) {t : ZMod N} (ht : GoodMult p t)
    {β : ZMod N → ℂ} (hβ : ∀ a k, β (tau t a * k) = β k) {k : ZMod N}
    (hk : (ZMod.cast k : ZMod p) ≠ 0) :
    Om t (fun k ↦ e k * β k) k = e k * β k := by
  simp only [Om, e_tau_mul ht, hβ]
  have h := (ww_sums hp ht hk).2.1
  calc ∑ a, ww t k a * (e k * zz t k a * β k) = e k * β k * ∑ a, ww t k a * zz t k a := by
        rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun a _ ↦ ?_; ring
    _ = e k * β k := by rw [h, mul_one]

/-- `Om` kills `e(-·) · β` for `t`-invariant `β`. -/
lemma Om_e_neg_mul {p : ℕ} (hp : p ∈ N.primeFactors) {t : ZMod N} (ht : GoodMult p t)
    {β : ZMod N → ℂ} (hβ : ∀ a k, β (tau t a * k) = β k) {k : ZMod N}
    (hk : (ZMod.cast k : ZMod p) ≠ 0) :
    Om t (fun k ↦ e (-k) * β k) k = 0 := by
  simp only [Om, hβ]
  have h := (ww_sums hp ht hk).2.2
  have h2 : ∀ a, e (-(tau t a * k)) = e (-k) / zz t k a := by
    intro a
    rw [AddChar.map_neg_eq_inv, AddChar.map_neg_eq_inv, e_tau_mul ht, mul_inv, div_eq_mul_inv]
  simp only [h2]
  calc ∑ a, ww t k a * (e (-k) / zz t k a * β k) = e (-k) * β k * ∑ a, ww t k a / zz t k a := by
        rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun a _ ↦ ?_; ring
    _ = 0 := by rw [h, mul_zero]

lemma Om_sum {t : ZMod N} {ι : Type*} (S : Finset ι) (R : ι → ZMod N → ℂ) (k : ZMod N) :
    Om t (fun k ↦ ∑ j ∈ S, R j k) k = ∑ j ∈ S, Om t (R j) k := by
  simp only [Om, Finset.mul_sum]; rw [Finset.sum_comm]

lemma Om_congr {T : Finset ℕ} (hT : T ⊆ N.primeFactors) {p : ℕ} {t : ZMod N}
    (ht : GoodMult p t) {Q₁ Q₂ : ZMod N → ℂ}
    (h : ∀ k, Cop T k → Q₁ k = Q₂ k) {k : ZMod N} (hk : Cop T k) : Om t Q₁ k = Om t Q₂ k := by
  simp only [Om]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  rw [h _ (cop_mul hT (tau_isUnit ht.isunit a) hk)]

/-- Peeling primes one at a time. -/
lemma peel (T : Finset ℕ) (hT : T ⊆ N.primeFactors) (t : ℕ → ZMod N)
    (ht : ∀ p ∈ T, GoodMult p (t p)) (β : ZMod N → ℂ)
    (hβ : ∀ p ∈ T, ∀ a k, β (tau (t p) a * k) = β k) :
    ∀ S ⊆ T, ∀ R : ℕ → ZMod N → ℂ, (∀ j ∈ S, Periodic' j (R j)) →
      (∀ k, Cop T k → e k * β k = ∑ j ∈ S, R j k) → ∀ k, Cop T k → β k = 0 := by
  intro S
  induction S using Finset.induction_on with
  | empty =>
    intro _ R _ h k hk
    have := h k hk
    rw [Finset.sum_empty] at this
    exact (mul_eq_zero.1 this).resolve_left (e_ne_zero k)
  | insert i S hi ih =>
    intro hST R hR h
    have hiT : i ∈ T := hST (Finset.mem_insert_self i S)
    have hiP := hT hiT
    have hti := ht i hiT
    refine ih ((Finset.subset_insert i S).trans hST) (fun j ↦ Om (t i) (R j)) ?_ ?_
    · intro j hj
      have hji : i ≠ j := fun h ↦ hi (h ▸ hj)
      exact Om_periodic_other hiP (hT (hST (Finset.mem_insert_of_mem hj))) hji hti
        (hR j (Finset.mem_insert_of_mem hj))
    · intro k hk
      have h1 := Om_congr hT hti (Q₁ := fun k ↦ e k * β k)
        (Q₂ := fun k ↦ ∑ j ∈ insert i S, R j k) h hk
      rw [Om_e_mul hiP hti (hβ i hiT) (hk i hiT), Om_sum, Finset.sum_insert hi,
        Om_periodic_self hiP hti (hR i (Finset.mem_insert_self i S)) (hk i hiT), zero_add] at h1
      exact h1

/-- Removing the `e(-k)` term with one prime, then peeling the rest. -/
lemma vanish_of_identity (T : Finset ℕ) (hT : T ⊆ N.primeFactors) (hne : T.Nonempty)
    (t : ℕ → ZMod N) (ht : ∀ p ∈ T, GoodMult p (t p)) (α β : ZMod N → ℂ)
    (hα : ∀ p ∈ T, ∀ a k, α (tau (t p) a * k) = α k)
    (hβ : ∀ p ∈ T, ∀ a k, β (tau (t p) a * k) = β k)
    (R : ℕ → ZMod N → ℂ) (hR : ∀ j ∈ T, Periodic' j (R j))
    (h : ∀ k, Cop T k → e (-k) * α k + e k * β k = ∑ j ∈ T, R j k) :
    ∀ k, Cop T k → β k = 0 := by
  obtain ⟨i, hiT⟩ := hne
  have hiP := hT hiT
  have hti := ht i hiT
  refine peel T hT t ht β hβ (T.erase i) (Finset.erase_subset i T) (fun j ↦ Om (t i) (R j)) ?_ ?_
  · intro j hj
    have hji : i ≠ j := fun h ↦ (Finset.notMem_erase i T) (h ▸ hj)
    exact Om_periodic_other hiP (hT (Finset.mem_of_mem_erase hj)) hji hti
      (hR j (Finset.mem_of_mem_erase hj))
  · intro k hk
    have h1 := Om_congr hT hti (Q₁ := fun k ↦ e (-k) * α k + e k * β k)
      (Q₂ := fun k ↦ ∑ j ∈ T, R j k) h hk
    have hadd : Om (t i) (fun k ↦ e (-k) * α k + e k * β k) k
        = Om (t i) (fun k ↦ e (-k) * α k) k + Om (t i) (fun k ↦ e k * β k) k := by
      simp only [Om, mul_add, Finset.sum_add_distrib]
    rw [hadd, Om_e_neg_mul hiP hti (hα i hiT) (hk i hiT), Om_e_mul hiP hti (hβ i hiT) (hk i hiT),
      zero_add, Om_sum, ← Finset.add_sum_erase T _ hiT, Om_periodic_self hiP hti (hR i hiT) (hk i hiT),
      zero_add] at h1
    exact h1

/-! ### The Fourier identity -/

/-- Fourier coefficient. -/
noncomputable def fc (A : ZMod N → ℂ) (k : ZMod N) : ℂ := ∑ x, A x * e (k * x)

lemma fc_invariant {A : ZMod N → ℂ} {s : ZMod N} (hs : IsUnit s) (hA : ∀ x, A (s * x) = A x)
    (k : ZMod N) : fc A (s * k) = fc A k := by
  simp only [fc]
  refine Fintype.sum_equiv (Units.mulLeft hs.unit) _ _ (fun x ↦ ?_)
  simp only [Units.mulLeft_apply, IsUnit.unit_spec, hA]
  congr 2; ring

lemma fc_shift_add (A : ZMod N → ℂ) (k : ZMod N) :
    ∑ x, A (x + 1) * e (k * x) = e (-k) * fc A k := by
  simp only [fc, Finset.mul_sum]
  refine Fintype.sum_equiv (Equiv.addRight 1) _ _ (fun x ↦ ?_)
  simp only [Equiv.coe_addRight]
  rw [mul_left_comm, ← AddChar.map_add_eq_mul]; congr 2; ring

lemma fc_shift_sub (B : ZMod N → ℂ) (k : ZMod N) :
    ∑ x, B (x - 1) * e (k * x) = e k * fc B k := by
  simp only [fc, Finset.mul_sum]
  refine Fintype.sum_equiv (Equiv.subRight 1) _ _ (fun x ↦ ?_)
  simp only [Equiv.subRight_apply]
  rw [mul_left_comm, ← AddChar.map_add_eq_mul]; congr 2; ring

lemma fc_periodic_of_support {p : ℕ} (hp : p ∈ N.primeFactors) (E : ZMod N → ℂ)
    (hE : ∀ x, (ZMod.cast x : ZMod p) ≠ 0 → E x = 0) : Periodic' p (fc E) := by
  intro k y
  simp only [fc]
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  by_cases hx : (ZMod.cast x : ZMod p) = 0
  · rw [add_mul, show nn N p * y * x = y * (nn N p * x) by ring, nn_mul_eq_zero_of_cast hp hx,
      mul_zero, add_zero]
  · rw [hE x hx, zero_mul, zero_mul]

lemma fc_eq_zero_of_periodic {p : ℕ} (hp : p ∈ N.primeFactors) (F : ZMod N → ℂ)
    (hF : ∀ x, F (x + nn N p) = F x) {k : ZMod N} (hk : (ZMod.cast k : ZMod p) ≠ 0) :
    fc F k = 0 := by
  refine sum_mul_e_eq_zero_of_periodic F (nn N p) k hF ?_
  rw [Ne, e_eq_one_iff, mul_comm]
  exact nn_mul_ne_zero hp hk

/-- Splitting a function supported on `∪_{p ∈ T} {p ∣ x}` along `T` (least prime). -/
lemma split_support (T : Finset ℕ) (E : ZMod N → ℂ)
    (hE : ∀ x, (∀ p ∈ T, (ZMod.cast x : ZMod p) ≠ 0) → E x = 0) :
    ∃ Es : ℕ → ZMod N → ℂ, (∀ p ∈ T, ∀ x, (ZMod.cast x : ZMod p) ≠ 0 → Es p x = 0) ∧
      ∀ x, E x = ∑ p ∈ T, Es p x := by
  classical
  refine ⟨fun p x ↦ if p = ((T.filter fun q ↦ (ZMod.cast x : ZMod q) = 0).min.getD 0) ∧
      (ZMod.cast x : ZMod p) = 0 then E x else 0, ?_, ?_⟩
  · intro p _ x hx
    simp [hx]
  · intro x
    by_cases h : ∃ p ∈ T, (ZMod.cast x : ZMod p) = 0
    · have hSne : (T.filter fun q ↦ (ZMod.cast x : ZMod q) = 0).Nonempty := by
        obtain ⟨p, hp, hpx⟩ := h; exact ⟨p, Finset.mem_filter.2 ⟨hp, hpx⟩⟩
      obtain ⟨m, hm⟩ := Finset.min_of_nonempty hSne
      have hmS := Finset.mem_filter.1 (Finset.mem_of_min hm)
      have hgd : (T.filter fun q ↦ (ZMod.cast x : ZMod q) = 0).min.getD 0 = m := by rw [hm]; rfl
      rw [Finset.sum_eq_single m]
      · simp [hgd, hmS.2]
      · intro b _ hb; simp [hgd, hb]
      · intro h; exact absurd hmS.1 h
    · push_neg at h
      rw [hE x h]
      symm
      refine Finset.sum_eq_zero fun p hp ↦ ?_
      simp [h p hp]

lemma inv_tau {A : ZMod N → ℂ} {s : ZMod N} (hA : ∀ x, A (s * x) = A x) (a : Fin 3) (x : ZMod N) :
    A (tau s a * x) = A x := by
  fin_cases a
  · simp [tau]
  · simpa [tau] using hA x
  · simp only [tau]; simp; rw [pow_two, mul_assoc, hA, hA]

/-- Lemma 3, `B`-half: `B̂` vanishes at units. -/
lemma lemma3_B (T : Finset ℕ) (hT : T ⊆ N.primeFactors) (hne : T.Nonempty)
    (t : ℕ → ZMod N) (ht : ∀ p ∈ T, GoodMult p (t p)) (A B : ZMod N → ℂ)
    (hA : ∀ p ∈ T, ∀ x, A (t p * x) = A x) (hB : ∀ p ∈ T, ∀ x, B (t p * x) = B x)
    (F : ℕ → ZMod N → ℂ) (hF : ∀ p ∈ T, ∀ x, F p (x + nn N p) = F p x)
    (h : ∀ x, (∀ p ∈ T, (ZMod.cast x : ZMod p) ≠ 0) → A (x + 1) + B (x - 1) = ∑ p ∈ T, F p x) :
    ∀ k, Cop T k → fc B k = 0 := by
  set E : ZMod N → ℂ := fun x ↦ A (x + 1) + B (x - 1) - ∑ p ∈ T, F p x with hEdef
  have hE : ∀ x, (∀ p ∈ T, (ZMod.cast x : ZMod p) ≠ 0) → E x = 0 := by
    intro x hx; simp only [hEdef, h x hx, sub_self]
  obtain ⟨Es, hEs, hsum⟩ := split_support T E hE
  have hinvA : ∀ p ∈ T, ∀ a k, fc A (tau (t p) a * k) = fc A k := fun p hp a k ↦
    fc_invariant (tau_isUnit (ht p hp).isunit a) (inv_tau (hA p hp) a) k
  have hinvB : ∀ p ∈ T, ∀ a k, fc B (tau (t p) a * k) = fc B k := fun p hp a k ↦
    fc_invariant (tau_isUnit (ht p hp).isunit a) (inv_tau (hB p hp) a) k
  refine vanish_of_identity T hT hne t ht (fc A) (fc B) hinvA hinvB (fun p ↦ fc (Es p))
    (fun p hp ↦ fc_periodic_of_support (hT hp) (Es p) (hEs p hp)) ?_
  intro k hk
  have h1 : fc E k = ∑ p ∈ T, fc (Es p) k := by
    simp only [fc, hsum, Finset.sum_mul]; rw [Finset.sum_comm]
  have h2 : fc E k = e (-k) * fc A k + e k * fc B k - ∑ p ∈ T, fc (F p) k := by
    simp only [fc, hEdef, sub_mul, add_mul, Finset.sum_sub_distrib, Finset.sum_add_distrib]
    rw [fc_shift_add, fc_shift_sub]
    simp only [fc, Finset.sum_mul]
    congr 1; rw [Finset.sum_comm]
  have h3 : ∑ p ∈ T, fc (F p) k = 0 :=
    Finset.sum_eq_zero fun p hp ↦ fc_eq_zero_of_periodic (hT hp) (F p) (hF p hp) (hk p hp)
  rw [← h1, h2, h3, sub_zero]

/-- **Lemma 3.** -/
theorem lemma3 (hsq : Squarefree N) (T : Finset ℕ) (hT : T ⊆ N.primeFactors) (hne : T.Nonempty)
    (t : ℕ → ZMod N) (ht : ∀ p ∈ T, GoodMult p (t p)) (A B : ZMod N → ℂ)
    (hA : ∀ p ∈ T, ∀ x, A (t p * x) = A x) (hB : ∀ p ∈ T, ∀ x, B (t p * x) = B x)
    (hAu : ∀ x, ¬ Cop T x → A x = 0) (hBu : ∀ x, ¬ Cop T x → B x = 0)
    (F : ℕ → ZMod N → ℂ) (hF : ∀ p ∈ T, ∀ x, F p (x + nn N p) = F p x)
    (h : ∀ x, (∀ p ∈ T, (ZMod.cast x : ZMod p) ≠ 0) → A (x + 1) + B (x - 1) = ∑ p ∈ T, F p x) :
    A = 0 ∧ B = 0 := by
  have hB0 := lemma3_B T hT hne t ht A B hA hB F hF h
  have hA0 := lemma3_B T hT hne t ht (fun x ↦ B (-x)) (fun x ↦ A (-x))
    (fun p hp x ↦ by rw [← mul_neg, hB p hp])
    (fun p hp x ↦ by rw [← mul_neg, hA p hp])
    (fun p x ↦ F p (-x))
    (fun p hp x ↦ by
      have := hF p hp (-x - nn N p)
      rw [sub_add_cancel] at this
      rw [neg_add, ← sub_eq_add_neg, this])
    (fun x hx ↦ by
      have := h (-x) (cop_neg hT hx)
      rw [show -(x + 1) = -x - 1 by ring, show -(x - 1) = -x + 1 by ring, add_comm]
      exact this)
  have hG : GoodPrimes N T := by
    intro p hp
    have hp' := hT hp
    refine ⟨Nat.prime_of_mem_primeFactors hp', Nat.dvd_of_mem_primeFactors hp', fun h ↦ ?_⟩
    exact (Nat.prime_of_mem_primeFactors hp').one_lt.ne' (Nat.isUnit_iff.1 (hsq p h))
  refine ⟨eq_zero_of_dft_cop hG A hAu fun k hk ↦ ?_, eq_zero_of_dft_cop hG B hBu hB0⟩
  have := hA0 (-k) (cop_neg hT hk)
  simp only [fc] at this
  rw [← this]
  refine Fintype.sum_equiv (Equiv.neg _) _ _ (fun x ↦ ?_)
  simp only [Equiv.neg_apply, neg_neg]
  congr 2; ring

end TwoPrimes

-- ===== CharDecomp =====

/-!
# Character decomposition (MO 503314)

If `c` on `ZMod N` (`N` squarefree) is orthogonal to every Dirichlet character whose conductor is
divisible by all primes of `T`, then on units `c = ∑_{p ∈ T} F p` with `F p` `N/p`-periodic.
-/

open Complex Finset

namespace TwoPrimes

variable {N : ℕ} [NeZero N]

/-- The primitive character evaluated through the conductor level, as a function on `ZMod N`. -/
noncomputable def primFun (χ : DirichletCharacter ℂ N) (x : ZMod N) : ℂ :=
  χ.primitiveCharacter (ZMod.cast x : ZMod χ.conductor)

lemma primFun_unit (χ : DirichletCharacter ℂ N) (x : (ZMod N)ˣ) : primFun χ x = χ x := by
  conv_rhs => rw [← χ.changeLevel_primitiveCharacter]
  rw [DirichletCharacter.changeLevel_eq_cast_of_dvd]
  rfl

lemma primFun_periodic (χ : DirichletCharacter ℂ N) {p : ℕ} (h : χ.conductor ∣ N / p)
    (x : ZMod N) : primFun χ (x + nn N p) = primFun χ x := by
  have hd := χ.conductor_dvd_level
  simp only [primFun]
  rw [ZMod.cast_add hd, nn, ZMod.cast_natCast hd, (ZMod.natCast_eq_zero_iff _ _).2 h, add_zero]

lemma inv_apply_eq {χ : DirichletCharacter ℂ N} {a : ZMod N} (ha : IsUnit a) :
    χ⁻¹ a = χ a⁻¹ := by
  have h1 : χ⁻¹ a * χ a = 1 := by
    rw [← MulChar.mul_apply, inv_mul_cancel]; exact MulChar.one_apply ha
  have h2 : χ a⁻¹ * χ a = 1 := by
    rw [← map_mul, ZMod.inv_mul_of_unit a ha, map_one]
  have h3 : χ a ≠ 0 := fun h ↦ by rw [h, mul_zero] at h1; exact zero_ne_one h1
  exact mul_right_cancel₀ h3 (h1.trans h2.symm)

/-- Fourier inversion on units with characters. -/
lemma totient_mul_eq_sum (c : ZMod N → ℂ) {b : ZMod N} (hb : IsUnit b) :
    (N.totient : ℂ) * c b = ∑ χ : DirichletCharacter ℂ N, χ b * ∑ a, c a * χ⁻¹ a := by
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  have : ∀ a : ZMod N, ∑ χ : DirichletCharacter ℂ N, χ b * (c a * χ⁻¹ a)
      = c a * if a = b then (N.totient : ℂ) else 0 := by
    intro a
    by_cases ha : IsUnit a
    · rw [← DirichletCharacter.sum_char_inv_mul_char_eq ℂ ha b, Finset.mul_sum]
      refine Finset.sum_congr rfl fun χ _ ↦ ?_
      rw [inv_apply_eq ha]; ring
    · have hab : a ≠ b := fun h ↦ ha (h ▸ hb)
      simp only [MulChar.map_nonunit _ ha, mul_zero, Finset.sum_const_zero, if_neg hab]
  simp only [this, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  ring

lemma conductor_dvd_div {χ : DirichletCharacter ℂ N} {p : ℕ} (hp : p ∈ N.primeFactors)
    (h : ¬ p ∣ χ.conductor) : χ.conductor ∣ N / p := by
  have hd := χ.conductor_dvd_level
  have hpp := Nat.prime_of_mem_primeFactors hp
  have hpN := Nat.dvd_of_mem_primeFactors hp
  have hcop : Nat.Coprime p χ.conductor := (Nat.Prime.coprime_iff_not_dvd hpp).2 h
  have := hcop.mul_dvd_of_dvd_of_dvd hpN hd
  obtain ⟨r, hr⟩ := this
  exact ⟨r, Nat.div_eq_of_eq_mul_left hpp.pos (hr.trans (by ring))⟩

/-- **Character decomposition.** -/
theorem char_decomp (T : Finset ℕ) (hT : T ⊆ N.primeFactors) (c : ZMod N → ℂ)
    (h : ∀ χ : DirichletCharacter ℂ N, (∀ p ∈ T, p ∣ χ.conductor) → ∑ x, c x * χ x = 0) :
    ∃ F : ℕ → ZMod N → ℂ, (∀ p ∈ T, ∀ x, F p (x + nn N p) = F p x) ∧
      ∀ x, IsUnit x → c x = ∑ p ∈ T, F p x := by
  classical
  set coef : DirichletCharacter ℂ N → ℂ := fun χ ↦ ∑ a, c a * χ⁻¹ a with hcoef
  set pick : DirichletCharacter ℂ N → ℕ :=
    fun χ ↦ ((T.filter fun p ↦ ¬ p ∣ χ.conductor).min).getD 0 with hpick
  have hpick_spec : ∀ χ, (∃ p ∈ T, ¬ p ∣ χ.conductor) → pick χ ∈ T ∧ ¬ pick χ ∣ χ.conductor := by
    intro χ ⟨p, hp, hpc⟩
    have hne : (T.filter fun p ↦ ¬ p ∣ χ.conductor).Nonempty := ⟨p, Finset.mem_filter.2 ⟨hp, hpc⟩⟩
    obtain ⟨m, hm⟩ := Finset.min_of_nonempty hne
    have hmS := Finset.mem_filter.1 (Finset.mem_of_min hm)
    simp only [hpick, hm, Option.getD_some]
    exact hmS
  have hpick_none : ∀ χ, pick χ ∈ T → ∃ p ∈ T, ¬ p ∣ χ.conductor := by
    intro χ hχ
    by_contra hcon
    push_neg at hcon
    have : (T.filter fun p ↦ ¬ p ∣ χ.conductor) = ∅ := by
      rw [Finset.filter_eq_empty_iff]; intro p hp; exact not_not.2 (hcon p hp)
    simp only [hpick, this, Finset.min_empty] at hχ
    have h0 := Nat.prime_of_mem_primeFactors (hT hχ)
    exact Nat.not_prime_zero h0
  refine ⟨fun p x ↦ ((N.totient : ℂ))⁻¹ *
      ∑ χ : DirichletCharacter ℂ N, if pick χ = p then coef χ * primFun χ x else 0, ?_, ?_⟩
  · intro p hp x
    dsimp only
    congr 1
    refine Finset.sum_congr rfl fun χ _ ↦ ?_
    split_ifs with hχ
    · have hs := hpick_spec χ (hpick_none χ (hχ ▸ hp))
      rw [hχ] at hs
      rw [primFun_periodic χ (conductor_dvd_div (hT hp) hs.2)]
    · rfl
  · intro x hx
    have htot : (N.totient : ℂ) ≠ 0 := by
      exact_mod_cast (Nat.totient_pos.2 (Nat.pos_of_ne_zero (NeZero.ne N))).ne'
    rw [← Finset.mul_sum, eq_inv_mul_iff_mul_eq₀ htot, totient_mul_eq_sum c hx, Finset.sum_comm]
    refine Finset.sum_congr rfl fun χ _ ↦ ?_
    rw [Finset.sum_ite_eq]
    split_ifs with hχ
    · have hpu := primFun_unit χ hx.unit
      rw [IsUnit.unit_spec] at hpu
      rw [hpu]; simp only [hcoef]; ring
    · have : coef χ = 0 := by
        have hall : ∀ p ∈ T, p ∣ χ⁻¹.conductor := by
          intro p hp
          rw [DirichletCharacter.conductor_inv]
          by_contra hpc
          exact hχ (hpick_spec χ ⟨p, hp, hpc⟩).1
        exact h χ⁻¹ hall
      simp only [hcoef] at this
      rw [this, mul_zero]

end TwoPrimes

-- ===== TwoC =====

/-!
# Hypothesis of MO 503314 and Lemma 2(c)

`ind d ρ x` counts `u < d` with `ρ^u = x` plus those with `-ρ^u = x` (the indicator of `G = ±⟨ρ⟩`),
`ff = ind ρ₁ - ind ρ₂`, `cc x = ff (x + 1) + ff (x - 1)`.  Lemma 2(c): `cc` is orthogonal to every
primitive character.
-/

open Complex Finset

namespace TwoPrimes

/-- The hypothesis (*) of MO 503314 at level `m`. -/
def Hyp (m d : ℕ) (r₁ r₂ : ℤ) : Prop :=
  ∀ k : ℤ,
    (∏ u ∈ Finset.Icc 1 (d - 1),
      (cexp (2 * Real.pi * I * k / m) - cexp (2 * Real.pi * I * (k * r₁ ^ u) / m)) *
      (cexp (2 * Real.pi * I * k / m) - cexp (2 * Real.pi * I * (-(k * r₁ ^ u)) / m))) =
    ∏ u ∈ Finset.Icc 1 (d - 1),
      (cexp (2 * Real.pi * I * k / m) - cexp (2 * Real.pi * I * (k * r₂ ^ u) / m)) *
      (cexp (2 * Real.pi * I * k / m) - cexp (2 * Real.pi * I * (-(k * r₂ ^ u)) / m))

/-- The hypothesis descends to divisors. -/
lemma Hyp.descend {m n d : ℕ} {r₁ r₂ : ℤ} (h : Hyp m d r₁ r₂) (hn : n ∣ m) (hm : 0 < m) :
    Hyp n d r₁ r₂ := by
  obtain ⟨a, rfl⟩ := hn
  have ha : (a : ℂ) ≠ 0 := by
    have : a ≠ 0 := by rintro rfl; simp at hm
    exact_mod_cast this
  have hn0 : (n : ℂ) ≠ 0 := by
    have : n ≠ 0 := by rintro rfl; simp at hm
    exact_mod_cast this
  intro k
  have := h (k * a)
  have hc : ∀ z : ℂ, (2 * Real.pi * I * (((k * a : ℤ) : ℂ) * z) / ((n * a : ℕ) : ℂ)) =
      2 * Real.pi * I * ((k : ℂ) * z) / (n : ℂ) := by
    intro z; push_cast; field_simp
  have hc1 : (2 * Real.pi * I * ((k * a : ℤ) : ℂ) / ((n * a : ℕ) : ℂ)) = 2 * Real.pi * I * (k : ℂ) / (n : ℂ) := by
    push_cast; field_simp
  have hc2 : ∀ z : ℂ, (2 * Real.pi * I * (-(((k * a : ℤ) : ℂ) * z)) / ((n * a : ℕ) : ℂ)) =
      2 * Real.pi * I * (-((k : ℂ) * z)) / (n : ℂ) := by
    intro z; push_cast; field_simp
  simp only [hc, hc1, hc2] at this
  exact this

/-- Count indicator of `±⟨ρ⟩`. -/
noncomputable def ind {N : ℕ} (d : ℕ) (ρ x : ZMod N) : ℂ :=
  ∑ u ∈ range d, ((if ρ ^ u = x then 1 else 0) + (if -ρ ^ u = x then 1 else 0))

noncomputable def ff {N : ℕ} (d : ℕ) (ρ₁ ρ₂ x : ZMod N) : ℂ := ind d ρ₁ x - ind d ρ₂ x

noncomputable def cc {N : ℕ} (d : ℕ) (ρ₁ ρ₂ x : ZMod N) : ℂ := ff d ρ₁ ρ₂ (x + 1) + ff d ρ₁ ρ₂ (x - 1)

variable {N : ℕ} [NeZero N]

local notation "e" => (ZMod.stdAddChar : AddChar (ZMod N) ℂ)


lemma ind_neg (d : ℕ) (ρ x : ZMod N) : ind d ρ (-x) = ind d ρ x := by
  simp only [ind]
  refine Finset.sum_congr rfl fun u _ ↦ ?_
  have h1 : (ρ ^ u = -x) ↔ (-ρ ^ u = x) := by
    constructor <;> intro h <;> [rw [h, neg_neg]; rw [← h, neg_neg]]
  have h2 : (-ρ ^ u = -x) ↔ (ρ ^ u = x) := neg_inj
  simp only [h1, h2]; ring

lemma ff_neg (d : ℕ) (ρ₁ ρ₂ x : ZMod N) : ff d ρ₁ ρ₂ (-x) = ff d ρ₁ ρ₂ x := by
  simp only [ff, ind_neg]

lemma cc_neg (d : ℕ) (ρ₁ ρ₂ x : ZMod N) : cc d ρ₁ ρ₂ (-x) = cc d ρ₁ ρ₂ x := by
  simp only [cc]
  rw [show -x + 1 = -(x - 1) by ring, show -x - 1 = -(x + 1) by ring, ff_neg, ff_neg, add_comm]

lemma sum_ind_shift (d : ℕ) (ρ : ZMod N) (φ : ZMod N → ℂ) :
    ∑ x, ind d ρ (x + 1) * φ x = ∑ u ∈ range d, (φ (ρ ^ u - 1) + φ (-ρ ^ u - 1)) := by
  simp only [ind, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun u _ ↦ ?_
  simp only [add_mul, Finset.sum_add_distrib, ite_mul, one_mul, zero_mul]
  have h1 : ∀ a : ZMod N, (∑ x : ZMod N, if a = x + 1 then φ x else 0) = φ (a - 1) := by
    intro a
    rw [Finset.sum_eq_single (a - 1)]
    · simp
    · intro b _ hb; rw [if_neg]; intro h; exact hb (by rw [h]; ring)
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [h1, h1]

/-! ## From (*) to equal log-sums -/

lemma cexp_int (j : ℤ) : cexp (2 * Real.pi * I * (j : ℂ) / N) = e (j : ZMod N) :=
  (ZMod.stdAddChar_coe j).symm

lemma cexp_int_mul (k r : ℤ) (u : ℕ) :
    cexp (2 * Real.pi * I * ((k : ℂ) * (r : ℂ) ^ u) / N) = e ((k : ZMod N) * (r : ZMod N) ^ u) := by
  have := cexp_int (N := N) (k * r ^ u)
  push_cast at this
  exact this

lemma cexp_int_neg_mul (k r : ℤ) (u : ℕ) :
    cexp (2 * Real.pi * I * (-((k : ℂ) * (r : ℂ) ^ u)) / N) =
      e (-((k : ZMod N) * (r : ZMod N) ^ u)) := by
  have := cexp_int (N := N) (-(k * r ^ u))
  push_cast at this
  exact this

lemma norm_e_sub (k a : ZMod N) : ‖e k - e (k * a)‖ = ‖1 - e (k * (a - 1))‖ := by
  have h : e k - e (k * a) = e k * (1 - e (k * (a - 1))) := by
    rw [mul_sub, mul_one, ← AddChar.map_add_eq_mul]; congr 2; ring
  rw [h, norm_mul, norm_e, one_mul]

/-- The normalized product. -/
noncomputable def PP (d : ℕ) (ρ k : ZMod N) : ℝ :=
  ∏ u ∈ Icc 1 (d - 1), (‖1 - e (k * (ρ ^ u - 1))‖ * ‖1 - e (k * (-ρ ^ u - 1))‖)

lemma PP_eq_prod (d : ℕ) (ρ k : ZMod N) :
    PP d ρ k = ∏ u ∈ Icc 1 (d - 1), (‖e k - e (k * ρ ^ u)‖ * ‖e k - e (-(k * ρ ^ u))‖) := by
  refine Finset.prod_congr rfl fun u _ ↦ ?_
  rw [norm_e_sub k (ρ ^ u), show -(k * ρ ^ u) = k * -ρ ^ u by ring, norm_e_sub k (-ρ ^ u)]

lemma PP_eq {d : ℕ} {r₁ r₂ : ℤ} (h : Hyp N d r₁ r₂) (k : ZMod N) :
    PP d (r₁ : ZMod N) k = PP d (r₂ : ZMod N) k := by
  have hk := h (k.val : ℤ)
  simp only [cexp_int, cexp_int_mul, cexp_int_neg_mul] at hk
  have hkk : (((k.val : ℤ)) : ZMod N) = k := by simp
  rw [hkk] at hk
  have := congrArg norm hk
  simp only [norm_prod, norm_mul] at this
  rw [PP_eq_prod, PP_eq_prod]
  exact this

/-- `ρ^u ≠ -1` for `ρ` of odd order in `ZMod N`, `N > 2`. -/
lemma pow_ne_neg_one {ρ : ZMod N} {d : ℕ} (hd : Odd d) (ho : orderOf ρ = d) (hN : 2 < N)
    (u : ℕ) : ρ ^ u ≠ -1 := by
  intro h
  have h1 : (ρ ^ u) ^ d = 1 := by rw [← pow_mul, mul_comm, pow_mul, ← ho, pow_orderOf_eq_one, one_pow]
  rw [h, hd.neg_one_pow] at h1
  haveI : Fact (2 < N) := ⟨hN⟩
  exact ZMod.neg_one_ne_one h1

lemma one_sub_e_ne_zero {y : ZMod N} (hy : y ≠ 0) : ‖1 - e y‖ ≠ 0 := by
  rw [norm_ne_zero_iff, sub_ne_zero, ne_comm, Ne, e_eq_one_iff]; exact hy

lemma log_PP {ρ : ZMod N} {d : ℕ} (hd : Odd d) (ho : orderOf ρ = d) (hN : 2 < N)
    {k : ZMod N} (hk : IsUnit k) :
    Real.log (PP d ρ k) = ∑ u ∈ Icc 1 (d - 1),
      (Real.log ‖1 - e (k * (ρ ^ u - 1))‖ + Real.log ‖1 - e (k * (-ρ ^ u - 1))‖) := by
  have hne : ∀ u ∈ Icc 1 (d - 1), ‖1 - e (k * (ρ ^ u - 1))‖ ≠ 0 ∧ ‖1 - e (k * (-ρ ^ u - 1))‖ ≠ 0 := by
    intro u hu
    rw [Finset.mem_Icc] at hu
    have hu1 : ρ ^ u ≠ 1 := by
      apply pow_ne_one_of_lt_orderOf (by omega); rw [ho]; omega
    have hu2 := pow_ne_neg_one hd ho hN u
    refine ⟨one_sub_e_ne_zero ?_, one_sub_e_ne_zero ?_⟩
    · intro h; apply hu1
      have := (hk.mul_right_eq_zero).1 h
      exact sub_eq_zero.1 this
    · intro h; apply hu2
      have := (hk.mul_right_eq_zero).1 h
      rw [sub_eq_zero] at this
      rw [← neg_neg (ρ ^ u), this]
  rw [PP, Real.log_prod]
  · refine Finset.sum_congr rfl fun u hu ↦ ?_
    rw [Real.log_mul (hne u hu).1 (hne u hu).2]
  · intro u hu; exact mul_ne_zero (hne u hu).1 (hne u hu).2

/-! ## Lemma 2(c) -/

set_option maxHeartbeats 1000000 in
/-- Indexed version of `charsum_eq_of_logprod`. -/
theorem charsum_eq_of_logprod2 (ψ : DirichletCharacter ℂ N) (hψ : ψ ≠ 1) (hprim : ψ.IsPrimitive)
    (hev : ψ.Even) (s : Finset ℕ) (a₁ b₁ a₂ b₂ : ℕ → ZMod N)
    (h : ∀ u : (ZMod N)ˣ, ∑ i ∈ s, (Real.log ‖1 - e (u * a₁ i)‖ + Real.log ‖1 - e (u * b₁ i)‖) =
      ∑ i ∈ s, (Real.log ‖1 - e (u * a₂ i)‖ + Real.log ‖1 - e (u * b₂ i)‖)) :
    ∑ i ∈ s, (ψ (a₁ i) + ψ (b₁ i)) = ∑ i ∈ s, (ψ (a₂ i) + ψ (b₂ i)) := by
  set F : ZMod N → ℂ := fun y ↦ (Real.log ‖1 - e y‖ : ℂ) with hFdef
  set T : ℂ := ∑ u : ZMod N, ψ⁻¹ u * F u with hT
  have hT0 : T ≠ 0 := sum_inv_mul_log_ne_zero ψ hψ hprim hev
  have hprim' : (ψ⁻¹).IsPrimitive := isPrimitive_inv ψ hprim
  have key1 : ∀ a : ZMod N, ∑ u : ZMod N, ψ⁻¹ u * F (u * a) = T * ψ a := by
    intro a
    by_cases ha : IsUnit a
    · have := sum_char_mul_comp_mul_unit ψ⁻¹ F ha.unit
      simp only [IsUnit.unit_spec, inv_inv] at this
      rw [this, mul_comm]
    · rw [sum_char_mul_comp_mul_nonunit ψ⁻¹ hprim' F ha, MulChar.map_nonunit _ ha, mul_zero]
  have key : ∀ a b : ℕ → ZMod N, ∑ u : ZMod N, ψ⁻¹ u * ∑ i ∈ s, (F (u * a i) + F (u * b i))
      = T * ∑ i ∈ s, (ψ (a i) + ψ (b i)) := by
    intro a b
    simp_rw [Finset.mul_sum, mul_add]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [Finset.sum_add_distrib, key1, key1]
  have hL : ∑ u : ZMod N, ψ⁻¹ u * ∑ i ∈ s, (F (u * a₁ i) + F (u * b₁ i))
      = ∑ u : ZMod N, ψ⁻¹ u * ∑ i ∈ s, (F (u * a₂ i) + F (u * b₂ i)) := by
    refine Finset.sum_congr rfl fun u _ ↦ ?_
    by_cases hu : IsUnit u
    · refine congrArg (ψ⁻¹ u * ·) ?_
      have := h hu.unit
      simp only [IsUnit.unit_spec] at this
      simp only [hFdef]
      exact_mod_cast this
    · rw [MulChar.map_nonunit _ hu, zero_mul, zero_mul]
  rw [key, key] at hL
  exact mul_left_cancel₀ hT0 hL

lemma Icc_eq_Ico {d : ℕ} (hd : 1 ≤ d) : Icc 1 (d - 1) = Ico 1 d := by
  ext u; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega

lemma sum_range_split {d : ℕ} (hd : 1 ≤ d) (g : ℕ → ℂ) :
    ∑ u ∈ range d, g u = g 0 + ∑ u ∈ Icc 1 (d - 1), g u := by
  rw [Icc_eq_Ico hd, Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (by omega)]

/-- **Lemma 2(c).** Under (*), `cc` is orthogonal to every primitive character. -/
theorem lemma2c {d : ℕ} {r₁ r₂ : ℤ} (hd : Odd d) (h : Hyp N d r₁ r₂) (hN : 2 < N)
    (ho₁ : orderOf (r₁ : ZMod N) = d) (ho₂ : orderOf (r₂ : ZMod N) = d)
    (ψ : DirichletCharacter ℂ N) (hprim : ψ.IsPrimitive) :
    ∑ x, cc d (r₁ : ZMod N) (r₂ : ZMod N) x * ψ x = 0 := by
  set ρ₁ : ZMod N := ((r₁ : ℤ) : ZMod N)
  set ρ₂ : ZMod N := ((r₂ : ℤ) : ZMod N)
  have hψ1 : ψ ≠ 1 := by
    intro h1
    have := hprim
    rw [DirichletCharacter.isPrimitive_def, h1, DirichletCharacter.conductor_one] at this
    omega
  have hd1 : 1 ≤ d := hd.pos
  have hsym : ∑ x, cc d ρ₁ ρ₂ x * ψ x = ψ (-1) * ∑ x, cc d ρ₁ ρ₂ x * ψ x := by
    rw [Finset.mul_sum]
    refine Fintype.sum_equiv (Equiv.neg _) _ _ (fun x ↦ ?_)
    simp only [Equiv.neg_apply]
    have hm1 : ψ (-1) ^ 2 = 1 := by rw [sq, ← map_mul, neg_one_mul, neg_neg, map_one]
    rw [cc_neg, show -x = -1 * x by ring, map_mul]
    linear_combination (-(cc d ρ₁ ρ₂ x * ψ x)) * hm1
  rcases ψ.even_or_odd with hev | hodd
  · -- even case
    have hA : ∑ x, ff d ρ₁ ρ₂ (x + 1) * ψ x = 0 := by
      simp only [ff, sub_mul, Finset.sum_sub_distrib, sum_ind_shift]
      have hcs := charsum_eq_of_logprod2 ψ hψ1 hprim hev (Icc 1 (d - 1))
        (fun u ↦ ρ₁ ^ u - 1) (fun u ↦ -ρ₁ ^ u - 1) (fun u ↦ ρ₂ ^ u - 1) (fun u ↦ -ρ₂ ^ u - 1)
        (fun u ↦ by rw [← log_PP hd ho₁ hN u.isUnit, ← log_PP hd ho₂ hN u.isUnit, PP_eq h])
      rw [sum_range_split hd1, sum_range_split hd1, hcs]
      simp
    have hB : ∑ x, ff d ρ₁ ρ₂ (x - 1) * ψ x = 0 := by
      rw [← hA]
      refine Fintype.sum_equiv (Equiv.neg _) _ _ (fun x ↦ ?_)
      simp only [Equiv.neg_apply]
      rw [← ff_neg, show -(x - 1) = -x + 1 by ring, hev.eval_neg]
    simp only [cc, add_mul, Finset.sum_add_distrib, hA, hB, add_zero]
  · -- odd case
    rw [hodd] at hsym
    have : (2 : ℂ) * ∑ x, cc d ρ₁ ρ₂ x * ψ x = 0 := by linear_combination hsym
    simpa using this

end TwoPrimes

-- ===== Kernels =====

/-!
# Lemma 2(b) for MO 503314: kernels

For a prime `q ∣ N` (`N` squarefree, not prime), the orders of `ρ₁, ρ₂` modulo `N/q` agree
(norm computation and unique factorization), and when they are `< d` the two kernels share an
element `t ≠ 1`, `t ≡ 1 (mod N/q)` (all `m`-th roots of unity in `ZMod q` are hit).
-/

open Complex Finset

namespace TwoPrimes

/-! ## Reindexing sums over `range d` -/

lemma sum_range_comp_of_injOn {d : ℕ} (f : ℕ → ℕ) (hf : ∀ u < d, f u < d)
    (hinj : ∀ u < d, ∀ v < d, f u = f v → u = v) (g : ℕ → ℂ) :
    ∑ u ∈ range d, g (f u) = ∑ u ∈ range d, g u := by
  have hinj' : Set.InjOn f ↑(range d) := by
    intro u hu v hv h
    simp only [Finset.coe_range, Set.mem_Iio] at hu hv
    exact hinj u hu v hv h
  have himg : (range d).image f = range d := by
    refine Finset.eq_of_subset_of_card_le ?_ ?_
    · intro x hx
      obtain ⟨u, hu, rfl⟩ := Finset.mem_image.1 hx
      exact Finset.mem_range.2 (hf u (Finset.mem_range.1 hu))
    · rw [Finset.card_image_of_injOn hinj']
  rw [← Finset.sum_image (f := g) hinj', himg]

lemma sum_range_mul_mod {d c : ℕ} (hc : Nat.Coprime c d) (g : ℕ → ℂ) :
    ∑ u ∈ range d, g ((c * u) % d) = ∑ u ∈ range d, g u := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp
  refine sum_range_comp_of_injOn (fun u ↦ (c * u) % d) (fun u _ ↦ Nat.mod_lt _ hd) ?_ g
  intro u hu v hv huv
  have h1 : c * u ≡ c * v [MOD d] := huv
  have h2 := Nat.ModEq.cancel_left_of_coprime (by rw [Nat.gcd_comm]; exact hc) h1
  exact Nat.ModEq.eq_of_lt_of_lt h2 hu hv

lemma sum_range_add_mod {d : ℕ} (j : ℕ) (g : ℕ → ℂ) :
    ∑ u ∈ range d, g ((u + j) % d) = ∑ u ∈ range d, g u := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp
  refine sum_range_comp_of_injOn (fun u ↦ (u + j) % d) (fun u _ ↦ Nat.mod_lt _ hd) ?_ g
  intro u hu v hv huv
  have h1 : u + j ≡ v + j [MOD d] := huv
  exact Nat.ModEq.eq_of_lt_of_lt (Nat.ModEq.add_right_cancel' j h1) hu hv

variable {N : ℕ} [NeZero N]

lemma pow_mod_ord {M : Type*} [Monoid M] {ρ : M} {d : ℕ} (ho : orderOf ρ = d) (n : ℕ) :
    ρ ^ (n % d) = ρ ^ n := by
  rw [← ho, _root_.pow_mod_orderOf]

/-- `ind` is invariant under multiplication by powers of `ρ`. -/
lemma ind_mul_pow {ρ : ZMod N} {d : ℕ} (ho : orderOf ρ = d) (hu : IsUnit ρ) (j : ℕ) (x : ZMod N) :
    ind d ρ (ρ ^ j * x) = ind d ρ x := by
  simp only [ind]
  rw [← sum_range_add_mod (d := d) j]
  refine Finset.sum_congr rfl fun u _ ↦ ?_
  rw [pow_mod_ord ho, pow_add]
  have hj : IsUnit (ρ ^ j) := hu.pow j
  have h1 : (ρ ^ u * ρ ^ j = ρ ^ j * x) ↔ (ρ ^ u = x) := by
    rw [mul_comm (ρ ^ u)]; exact hj.mul_right_inj
  have h2 : (-(ρ ^ u * ρ ^ j) = ρ ^ j * x) ↔ (-ρ ^ u = x) := by
    rw [show -(ρ ^ u * ρ ^ j) = ρ ^ j * -ρ ^ u by ring]; exact hj.mul_right_inj
  simp only [h1, h2]

/-- Counting with a divisibility filter is unchanged under `ρ ↦ ρ^c`, `c` prime to `d`. -/
lemma sum_filter_pow_eq {M : Type*} [Monoid M] {ρ₁ ρ₂ : M} {d c e : ℕ} (hd : 0 < d)
    (ho₁ : orderOf ρ₁ = d) (ho₂ : orderOf ρ₂ = d) (hc : ρ₁ ^ c = ρ₂) (he : e ∣ d) (Φ : M → ℂ) :
    ∑ u ∈ range d, (if e ∣ u then Φ (ρ₂ ^ u) else 0) =
      ∑ u ∈ range d, (if e ∣ u then Φ (ρ₁ ^ u) else 0) := by
  have hcop : Nat.Coprime c d := by
    rcases Nat.eq_zero_or_pos c with rfl | hc0
    · rw [pow_zero] at hc
      rw [← hc, orderOf_one] at ho₂
      rw [← ho₂]; exact Nat.coprime_one_right 0
    have h := orderOf_pow' ρ₁ hc0.ne'
    rw [hc, ho₁, ho₂] at h
    have hpos : 0 < Nat.gcd d c := Nat.gcd_pos_of_pos_left c hd
    have : Nat.gcd d c = 1 := by
      by_contra hne
      have h2 : d / Nat.gcd d c < d := Nat.div_lt_self hd (by omega)
      omega
    rw [Nat.Coprime, Nat.gcd_comm]; exact this
  conv_rhs => rw [← sum_range_mul_mod hcop]
  refine Finset.sum_congr rfl fun u _ ↦ ?_
  have hdiv : e ∣ (c * u) % d ↔ e ∣ u := by
    rw [Nat.dvd_mod_iff he]
    constructor
    · intro h
      exact Nat.Coprime.dvd_of_dvd_mul_left (Nat.Coprime.coprime_dvd_right he hcop).symm h
    · intro h; exact Dvd.dvd.mul_left h c
  rw [pow_mod_ord ho₁, pow_mul, hc]
  simp only [hdiv]

local notation "e" => (ZMod.stdAddChar : AddChar (ZMod N) ℂ)

/-! ## CRT and additive orders -/

lemma eq_of_cast_eq {q : ℕ} (hq : q.Prime) (hqN : q ∣ N) (hsq : ¬ q * q ∣ N) {x y : ZMod N}
    (h1 : (ZMod.cast x : ZMod q) = ZMod.cast y) (h2 : (ZMod.cast x : ZMod (N / q)) = ZMod.cast y) :
    x = y := by
  rw [← sub_eq_zero]
  have hd : N / q ∣ N := Nat.div_dvd_of_dvd hqN
  have a1 : (ZMod.cast (x - y) : ZMod q) = 0 := by rw [ZMod.cast_sub hqN, h1, sub_self]
  have a2 : (ZMod.cast (x - y) : ZMod (N / q)) = 0 := by rw [ZMod.cast_sub hd, h2, sub_self]
  rw [cast_eq_zero_iff_dvd_val] at a1 a2
  have hcop : Nat.Coprime q (N / q) := by
    rw [Nat.Prime.coprime_iff_not_dvd hq]
    intro h; apply hsq
    have := Nat.mul_dvd_mul_left q h
    rwa [Nat.mul_div_cancel' hqN] at this
  have h3 := hcop.mul_dvd_of_dvd_of_dvd a1 a2
  rw [Nat.mul_div_cancel' hqN] at h3
  have := Nat.eq_zero_of_dvd_of_lt h3 (ZMod.val_lt _)
  exact (ZMod.val_eq_zero _).1 this

lemma addOrderOf_eq_iff {a : ZMod N} (ha : a ≠ 0) {q : ℕ} (hq : q.Prime) (hqN : q ∣ N) :
    addOrderOf a = q ↔ (ZMod.cast a : ZMod (N / q)) = 0 := by
  haveI : Fact q.Prime := ⟨hq⟩
  rw [addOrderOf_eq_prime_iff, cast_eq_zero_iff_dvd_val, nsmul_eq_mul]
  have hiff : (q : ZMod N) * a = 0 ↔ N / q ∣ a.val := by
    conv_lhs => rw [← ZMod.natCast_zmod_val a, ← Nat.cast_mul, ZMod.natCast_eq_zero_iff]
    exact nat_dvd_mul_iff_div hq.pos hqN
  rw [hiff]; exact ⟨fun h ↦ h.1, fun h ↦ ⟨h, ha⟩⟩

lemma addOrderOf_dvd_N (a : ZMod N) : addOrderOf a ∣ N :=
  addOrderOf_dvd_of_nsmul_eq_zero (by rw [nsmul_eq_mul, ZMod.natCast_self, zero_mul])

/-- `ρ^u ≠ -1` when `ρ^d = 1`, `d` odd. -/
lemma pow_ne_neg_one' {n : ℕ} {ρ : ZMod n} {d : ℕ} (hd : Odd d) (hρ : ρ ^ d = 1) (hn : 2 < n)
    (u : ℕ) : ρ ^ u ≠ -1 := by
  intro h
  have h1 : (ρ ^ u) ^ d = 1 := by rw [← pow_mul, mul_comm, pow_mul, hρ, one_pow]
  rw [h, hd.neg_one_pow] at h1
  haveI : Fact (2 < n) := ⟨hn⟩
  exact ZMod.neg_one_ne_one h1

/-- Kernel sizes. -/
noncomputable def kap (N q : ℕ) [NeZero N] : ℝ :=
  if h : q ∣ N then (Fintype.card (ZMod.unitsMap h).ker : ℝ) else 0

lemma kap_pos {q : ℕ} (h : q ∣ N) : 0 < kap N q := by
  rw [kap, dif_pos h]; exact_mod_cast Fintype.card_pos

/-- The unit-sum of `log ‖1 - e(k a)‖` for `a ≠ 0`. -/
lemma sum_units_log (hsq : Squarefree N) {a : ZMod N} (ha : a ≠ 0) :
    ∑ k : (ZMod N)ˣ, Real.log ‖1 - e (k * a)‖ =
      ∑ q ∈ N.primeFactors, if addOrderOf a = q then kap N q * Real.log q else 0 := by
  have hdvd := addOrderOf_dvd_N a
  have ho1 : addOrderOf a ≠ 1 := fun h ↦ ha (AddMonoid.addOrderOf_eq_one_iff.1 h)
  have ho0 : 0 < addOrderOf a := addOrderOf_pos a
  rw [sum_log_units a ha rfl hdvd, log_norm_cyclotomic_one (hsq.squarefree_of_dvd hdvd) (by omega)]
  rw [Finset.sum_ite_eq]
  split_ifs with hp hm hm
  · rw [kap, dif_pos hdvd]
  · exact absurd (Nat.mem_primeFactors.2 ⟨hp, hdvd, NeZero.ne N⟩) hm
  · exact absurd (Nat.prime_of_mem_primeFactors hm) hp
  · rw [mul_zero]

/-- The total norm: sum over units of `log PP`. -/
lemma sum_log_PP (hsq : Squarefree N) (hN2 : 2 < N) (hNp : ¬ N.Prime) (hodd : Odd N)
    {ρ : ZMod N} {d : ℕ} (hd : Odd d) (ho : orderOf ρ = d) :
    ∑ k : (ZMod N)ˣ, Real.log (PP d ρ k) = ∑ q ∈ N.primeFactors, kap N q * Real.log q *
      ((Icc 1 (d - 1)).filter fun u ↦ (ZMod.cast ρ : ZMod (N / q)) ^ u = 1).card := by
  simp only [log_PP hd ho hN2 (Units.isUnit _)]
  rw [Finset.sum_comm]
  have hρ1 : ∀ u ∈ Icc 1 (d - 1), ρ ^ u - 1 ≠ 0 := by
    intro u hu
    rw [Finset.mem_Icc] at hu
    rw [sub_ne_zero]
    exact pow_ne_one_of_lt_orderOf (by omega) (by rw [ho]; omega)
  have hρ2 : ∀ u, -ρ ^ u - 1 ≠ 0 := by
    intro u h
    apply pow_ne_neg_one hd ho hN2 u
    rw [← neg_neg (ρ ^ u), sub_eq_zero.1 h]
  have hneg : ∀ u, ∑ q ∈ N.primeFactors,
      (if addOrderOf (-ρ ^ u - 1) = q then kap N q * Real.log q else 0) = 0 := by
    intro u
    refine Finset.sum_eq_zero fun q hq ↦ ?_
    rw [if_neg]
    intro hoq
    have hqp := Nat.prime_of_mem_primeFactors hq
    have hqN := Nat.dvd_of_mem_primeFactors hq
    rw [addOrderOf_eq_iff (hρ2 u) hqp hqN] at hoq
    have hdN : N / q ∣ N := Nat.div_dvd_of_dvd hqN
    rw [ZMod.cast_sub hdN, ZMod.cast_neg hdN, ZMod.cast_one hdN, sub_eq_zero] at hoq
    have hn2 : 2 < N / q := by
      have h1 : N / q ≠ 1 := by
        intro h1
        apply hNp
        have := Nat.div_mul_cancel hqN
        rw [h1, one_mul] at this
        rw [← this]; exact hqp
      have h0 : N / q ≠ 0 := (Nat.div_pos (Nat.le_of_dvd (by omega) hqN) hqp.pos).ne'
      have h2 : N / q ≠ 2 := by
        intro h2
        have : 2 ∣ N := h2 ▸ hdN
        exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 this)
      have h3 : 2 ≤ N / q := (Nat.two_le_iff _).2 ⟨h0, h1⟩
      exact lt_of_le_of_ne h3 (Ne.symm h2)
    have hpow : (ZMod.cast ρ : ZMod (N / q)) ^ d = 1 := by
      rw [← ZMod.cast_pow hdN, ← ho, pow_orderOf_eq_one, ZMod.cast_one hdN]
    rw [ZMod.cast_pow hdN, neg_eq_iff_eq_neg] at hoq
    exact pow_ne_neg_one' hd hpow hn2 u hoq
  calc ∑ u ∈ Icc 1 (d - 1), ∑ k : (ZMod N)ˣ,
        (Real.log ‖1 - e (k * (ρ ^ u - 1))‖ + Real.log ‖1 - e (k * (-ρ ^ u - 1))‖)
      = ∑ u ∈ Icc 1 (d - 1), ∑ q ∈ N.primeFactors,
          (if addOrderOf (ρ ^ u - 1) = q then kap N q * Real.log q else 0) := by
        refine Finset.sum_congr rfl fun u hu ↦ ?_
        rw [Finset.sum_add_distrib, sum_units_log hsq (hρ1 u hu), sum_units_log hsq (hρ2 u),
          hneg u, add_zero]
    _ = ∑ q ∈ N.primeFactors, ∑ u ∈ Icc 1 (d - 1),
          (if addOrderOf (ρ ^ u - 1) = q then kap N q * Real.log q else 0) := Finset.sum_comm
    _ = _ := by
        refine Finset.sum_congr rfl fun q hq ↦ ?_
        have hqp := Nat.prime_of_mem_primeFactors hq
        have hqN := Nat.dvd_of_mem_primeFactors hq
        have hdN : N / q ∣ N := Nat.div_dvd_of_dvd hqN
        rw [Finset.card_filter, Nat.cast_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun u hu ↦ ?_
        have hc : addOrderOf (ρ ^ u - 1) = q ↔ (ZMod.cast ρ : ZMod (N / q)) ^ u = 1 := by
          rw [addOrderOf_eq_iff (hρ1 u hu) hqp hqN, ZMod.cast_sub hdN, ZMod.cast_pow hdN,
            ZMod.cast_one hdN, sub_eq_zero]
        rw [if_congr hc rfl rfl]
        split_ifs <;> simp


/-! ## Unique factorization and equal orders -/

lemma eq_of_sum_mul_log_eq (S : Finset ℕ) (hS : ∀ q ∈ S, q.Prime) (a b : ℕ → ℕ)
    (h : ∑ q ∈ S, (a q : ℝ) * Real.log q = ∑ q ∈ S, (b q : ℝ) * Real.log q) :
    ∀ q ∈ S, a q = b q := by
  have hprod : ∀ c : ℕ → ℕ, ∑ q ∈ S, (c q : ℝ) * Real.log q = Real.log ((∏ q ∈ S, q ^ c q : ℕ) : ℝ) := by
    intro c
    rw [Nat.cast_prod, Real.log_prod]
    · refine Finset.sum_congr rfl fun q _ ↦ ?_
      rw [Nat.cast_pow, Real.log_pow]
    · intro q hq
      exact_mod_cast pow_ne_zero _ (hS q hq).ne_zero
  rw [hprod, hprod] at h
  have hpos : ∀ c : ℕ → ℕ, (0 : ℝ) < ((∏ q ∈ S, q ^ c q : ℕ) : ℝ) := by
    intro c
    exact_mod_cast Finset.prod_pos fun q hq ↦ pow_pos (hS q hq).pos _
  have h2 := Real.log_injOn_pos (Set.mem_Ioi.2 (hpos a)) (Set.mem_Ioi.2 (hpos b)) h
  have h3 : (∏ q ∈ S, q ^ a q : ℕ) = ∏ q ∈ S, q ^ b q := by exact_mod_cast h2
  have hfact : ∀ c : ℕ → ℕ, ∀ q ∈ S, (∏ p ∈ S, p ^ c p).factorization q = c q := by
    intro c q hq
    rw [Nat.factorization_prod (fun p hp ↦ pow_ne_zero _ (hS p hp).ne_zero), Finset.sum_apply']
    rw [Finset.sum_congr rfl (fun p hp ↦ by rw [(hS p hp).factorization_pow])]
    simp [Finsupp.single_apply, hq]
  intro q hq
  rw [← hfact a q hq, ← hfact b q hq, h3]

lemma div_sub_one_eq {d f : ℕ} (hf : f ∣ d) (hf0 : 0 < f) (hd : 0 < d) :
    (d - 1) / f = d / f - 1 := by
  obtain ⟨m, rfl⟩ := hf
  have hm : 0 < m := Nat.pos_of_mul_pos_left hd
  rw [Nat.mul_div_cancel_left _ hf0]
  apply Nat.div_eq_of_lt_le
  · have : f * (m - 1) + f = f * m := by
      rw [← Nat.mul_succ]; congr 1; omega
    rw [mul_comm (m - 1) f]
    omega
  · have : (m - 1 + 1) * f = f * m := by rw [Nat.sub_add_cancel hm, mul_comm]
    omega

lemma card_filter_pow_eq_one {n : ℕ} {σ : ZMod n} {d : ℕ} (hd : 0 < d) (hσ : σ ^ d = 1) :
    ((Icc 1 (d - 1)).filter fun u ↦ σ ^ u = 1).card = d / orderOf σ - 1 := by
  have hdvd : orderOf σ ∣ d := orderOf_dvd_of_pow_eq_one hσ
  have hpos : 0 < orderOf σ := (isOfFinOrder_iff_pow_eq_one.2 ⟨d, hd, hσ⟩).orderOf_pos
  have hIcc : Icc 1 (d - 1) = Ioc 0 (d - 1) := by ext u; simp; omega
  rw [hIcc]
  simp only [← orderOf_dvd_iff_pow_eq_one]
  rw [Nat.Ioc_filter_dvd_card_eq_div, div_sub_one_eq hdvd hpos hd]

/-- **Lemma 2(b)**: equal orders modulo `N/q`. -/
theorem orderOf_cast_eq (hsq : Squarefree N) (hN2 : 2 < N) (hNp : ¬ N.Prime) (hodd : Odd N)
    {d : ℕ} {r₁ r₂ : ℤ} (hd : Odd d) (h : Hyp N d r₁ r₂)
    (ho₁ : orderOf (r₁ : ZMod N) = d) (ho₂ : orderOf (r₂ : ZMod N) = d)
    {q : ℕ} (hq : q ∈ N.primeFactors) :
    orderOf (ZMod.cast (r₁ : ZMod N) : ZMod (N / q)) = orderOf (ZMod.cast (r₂ : ZMod N) : ZMod (N / q)) := by
  have hS := sum_log_PP hsq hN2 hNp hodd hd ho₁
  have hS2 := sum_log_PP hsq hN2 hNp hodd hd ho₂
  have heq : ∑ k : (ZMod N)ˣ, Real.log (PP d (r₁ : ZMod N) k)
      = ∑ k : (ZMod N)ˣ, Real.log (PP d (r₂ : ZMod N) k) := by
    simp only [PP_eq h]
  rw [hS, hS2] at heq
  -- write kap as a natural number
  have hkap : ∀ q' ∈ N.primeFactors, ∃ κ : ℕ, 0 < κ ∧ kap N q' = κ := by
    intro q' hq'
    refine ⟨Fintype.card (ZMod.unitsMap (Nat.dvd_of_mem_primeFactors hq')).ker, Fintype.card_pos, ?_⟩
    rw [kap, dif_pos]
  choose! κ hκ0 hκ using hkap
  have heq' : ∑ q' ∈ N.primeFactors, ((κ q' * ((Icc 1 (d - 1)).filter fun u ↦
        (ZMod.cast (r₁ : ZMod N) : ZMod (N / q')) ^ u = 1).card : ℕ) : ℝ) * Real.log q'
      = ∑ q' ∈ N.primeFactors, ((κ q' * ((Icc 1 (d - 1)).filter fun u ↦
        (ZMod.cast (r₂ : ZMod N) : ZMod (N / q')) ^ u = 1).card : ℕ) : ℝ) * Real.log q' := by
    convert heq using 2 <;> rename_i q' hq' <;> rw [hκ q' hq'] <;> push_cast <;> ring
  have h1 := eq_of_sum_mul_log_eq _ (fun p hp ↦ Nat.prime_of_mem_primeFactors hp) _ _ heq' q hq
  have h2 := Nat.eq_of_mul_eq_mul_left (hκ0 q hq) h1
  have hdN : N / q ∣ N := Nat.div_dvd_of_dvd (Nat.dvd_of_mem_primeFactors hq)
  have hp1 : (ZMod.cast (r₁ : ZMod N) : ZMod (N / q)) ^ d = 1 := by
    rw [← ZMod.cast_pow hdN, ← ho₁, pow_orderOf_eq_one, ZMod.cast_one hdN]
  have hp2 : (ZMod.cast (r₂ : ZMod N) : ZMod (N / q)) ^ d = 1 := by
    rw [← ZMod.cast_pow hdN, ← ho₂, pow_orderOf_eq_one, ZMod.cast_one hdN]
  rw [card_filter_pow_eq_one hd.pos hp1, card_filter_pow_eq_one hd.pos hp2] at h2
  have hd1 := orderOf_dvd_of_pow_eq_one hp1
  have hd2 := orderOf_dvd_of_pow_eq_one hp2
  have hm1 : 0 < d / orderOf (ZMod.cast (r₁ : ZMod N) : ZMod (N / q)) :=
    Nat.div_pos (Nat.le_of_dvd hd.pos hd1) (isOfFinOrder_iff_pow_eq_one.2 ⟨d, hd.pos, hp1⟩).orderOf_pos
  have hm2 : 0 < d / orderOf (ZMod.cast (r₂ : ZMod N) : ZMod (N / q)) :=
    Nat.div_pos (Nat.le_of_dvd hd.pos hd2) (isOfFinOrder_iff_pow_eq_one.2 ⟨d, hd.pos, hp2⟩).orderOf_pos
  have h3 : d / orderOf (ZMod.cast (r₁ : ZMod N) : ZMod (N / q))
      = d / orderOf (ZMod.cast (r₂ : ZMod N) : ZMod (N / q)) := by omega
  have e1 := Nat.div_mul_cancel hd1
  have e2 := Nat.div_mul_cancel hd2
  have h4 : d / orderOf (ZMod.cast (r₂ : ZMod N) : ZMod (N / q)) *
      orderOf (ZMod.cast (r₁ : ZMod N) : ZMod (N / q)) =
      d / orderOf (ZMod.cast (r₂ : ZMod N) : ZMod (N / q)) *
      orderOf (ZMod.cast (r₂ : ZMod N) : ZMod (N / q)) := by
    rw [← h3, e1, h3, e2]
  exact Nat.eq_of_mul_eq_mul_left hm2 h4


/-! ## A common kernel element -/

lemma card_nthRootsFinset_le (m : ℕ) {R : Type*} [CommRing R] [IsDomain R] (a : R) :
    (Polynomial.nthRootsFinset m a).card ≤ m := by
  classical
  unfold Polynomial.nthRootsFinset
  exact (Multiset.toFinset_card_le _).trans (Polynomial.card_nthRoots _ _)

lemma sub_one_eq_nn_mul {q : ℕ} (hq : q ∣ N) {t : ZMod N}
    (ht : (ZMod.cast t : ZMod (N / q)) = 1) : ∃ a : ZMod N, t = 1 + nn N q * a := by
  have hdN : N / q ∣ N := Nat.div_dvd_of_dvd hq
  have h0 : (ZMod.cast (t - 1) : ZMod (N / q)) = 0 := by
    rw [ZMod.cast_sub hdN, ht, ZMod.cast_one hdN, sub_self]
  rw [cast_eq_zero_iff_dvd_val] at h0
  obtain ⟨c, hc⟩ := h0
  refine ⟨(c : ZMod N), ?_⟩
  have : t - 1 = ((t - 1).val : ZMod N) := (ZMod.natCast_zmod_val _).symm
  rw [hc, Nat.cast_mul] at this
  rw [nn, ← this]; ring

theorem common_kernel_elt (hsq : Squarefree N) {d : ℕ} (hd : Odd d) {ρ₁ ρ₂ : ZMod N}
    (ho₁ : orderOf ρ₁ = d) (ho₂ : orderOf ρ₂ = d) (hu₁ : IsUnit ρ₁) {q : ℕ}
    (hq : q ∈ N.primeFactors)
    (he : orderOf (ZMod.cast ρ₁ : ZMod (N / q)) = orderOf (ZMod.cast ρ₂ : ZMod (N / q)))
    (hlt : orderOf (ZMod.cast ρ₁ : ZMod (N / q)) < d) :
    (∃ j, ρ₂ ^ j = ρ₁ ^ orderOf (ZMod.cast ρ₁ : ZMod (N / q))) ∧
      GoodMult q (ρ₁ ^ orderOf (ZMod.cast ρ₁ : ZMod (N / q))) := by
  have hqp := Nat.prime_of_mem_primeFactors hq
  have hqN := Nat.dvd_of_mem_primeFactors hq
  have hqsq : ¬ q * q ∣ N := fun h ↦ hqp.one_lt.ne' (Nat.isUnit_iff.1 (hsq q h))
  haveI : Fact q.Prime := ⟨hqp⟩
  have hdN : N / q ∣ N := Nat.div_dvd_of_dvd hqN
  set E := orderOf (ZMod.cast ρ₁ : ZMod (N / q)) with hE
  have hp1 : (ZMod.cast ρ₁ : ZMod (N / q)) ^ d = 1 := by
    rw [← ZMod.cast_pow hdN, ← ho₁, pow_orderOf_eq_one, ZMod.cast_one hdN]
  have hEd : E ∣ d := orderOf_dvd_of_pow_eq_one hp1
  have hE0 : 0 < E := (isOfFinOrder_iff_pow_eq_one.2 ⟨d, hd.pos, hp1⟩).orderOf_pos
  obtain ⟨m, hm⟩ := hEd
  have hm0 : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · rw [h, mul_zero] at hm; exact absurd hm hd.pos.ne'
    · exact h
  have hcast1 : (ZMod.cast (ρ₁ ^ E) : ZMod (N / q)) = 1 := by
    rw [ZMod.cast_pow hdN, hE, pow_orderOf_eq_one]
  refine ⟨?_, ?_⟩
  · -- the roots argument in `ZMod q`
    have hcast2 : ∀ j, (ZMod.cast (ρ₂ ^ (E * j)) : ZMod (N / q)) = 1 := by
      intro j
      rw [ZMod.cast_pow hdN, pow_mul, he, pow_orderOf_eq_one, one_pow]
    set S := (range m).image (fun j ↦ (ZMod.cast (ρ₂ ^ (E * j)) : ZMod q)) with hS
    have hsub : S ⊆ Polynomial.nthRootsFinset m (1 : ZMod q) := by
      intro y hy
      obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hy
      rw [Polynomial.mem_nthRootsFinset hm0, ← ZMod.cast_pow hqN, ← pow_mul,
        show E * j * m = d * j by rw [hm]; ring, pow_mul, ← ho₂, pow_orderOf_eq_one, one_pow,
        ZMod.cast_one hqN]
    have hinj : Set.InjOn (fun j ↦ (ZMod.cast (ρ₂ ^ (E * j)) : ZMod q)) ↑(range m) := by
      intro j hj j' hj' hjj
      simp only [Finset.coe_range, Set.mem_Iio] at hj hj'
      have h1 := eq_of_cast_eq hqp hqN hqsq hjj (by rw [hcast2, hcast2])
      have hfin : IsOfFinOrder ρ₂ := isOfFinOrder_iff_pow_eq_one.2
        ⟨d, hd.pos, by rw [← ho₂, pow_orderOf_eq_one]⟩
      rw [hfin.pow_inj_mod, ho₂, hm] at h1
      exact Nat.ModEq.eq_of_lt_of_lt (Nat.ModEq.mul_left_cancel' hE0.ne' h1) hj hj'
    have hcard : (Polynomial.nthRootsFinset m (1 : ZMod q)).card ≤ S.card := by
      rw [hS, Finset.card_image_of_injOn hinj, Finset.card_range]
      exact card_nthRootsFinset_le m 1
    have hSeq := Finset.eq_of_subset_of_card_le hsub hcard
    have hmem : (ZMod.cast (ρ₁ ^ E) : ZMod q) ∈ Polynomial.nthRootsFinset m (1 : ZMod q) := by
      rw [Polynomial.mem_nthRootsFinset hm0, ← ZMod.cast_pow hqN, ← pow_mul, ← hm, ← ho₁,
        pow_orderOf_eq_one, ZMod.cast_one hqN]
    rw [← hSeq] at hmem
    obtain ⟨j, -, hj⟩ := Finset.mem_image.1 hmem
    exact ⟨E * j, eq_of_cast_eq hqp hqN hqsq hj (by rw [hcast2, hcast1])⟩
  · refine ⟨hu₁.pow E, ?_, ?_, sub_one_eq_nn_mul hqN hcast1⟩
    · exact pow_ne_one_of_lt_orderOf hE0.ne' (by rw [ho₁]; exact hlt)
    · intro h
      rw [← pow_mul] at h
      have h1 := orderOf_dvd_of_pow_eq_one h
      rw [ho₁] at h1
      have h2 : d ∣ E := Nat.Coprime.dvd_of_dvd_mul_right (Nat.coprime_two_right.2 hd) h1
      exact absurd (Nat.le_of_dvd hE0 h2) (not_le.2 hlt)

end TwoPrimes

-- ===== Lemma4 =====

/-!
# Lemma 4 for MO 503314: pairwise agreement of cyclic subgroups gives agreement

Generalized CRT for pairwise compatible congruences, then: if `ρ₂ ≡ ρ₁^c` modulo every pair of
primes of a squarefree `N` (with `c` depending on the pair), then `ρ₂ = ρ₁^K` in `ZMod N`.
-/

open Finset

namespace TwoPrimes

lemma gcd_lcm_dvd {u v w : ℕ} (hu : u ≠ 0) (hv : v ≠ 0) (hw : w ≠ 0) :
    Nat.gcd (Nat.lcm u v) w ∣ Nat.lcm (Nat.gcd u w) (Nat.gcd v w) := by
  have h1 : Nat.lcm u v ≠ 0 := Nat.lcm_ne_zero hu hv
  have g1 : Nat.gcd u w ≠ 0 := Nat.gcd_ne_zero_left hu
  have g2 : Nat.gcd v w ≠ 0 := Nat.gcd_ne_zero_left hv
  rw [← Nat.factorization_le_iff_dvd (Nat.gcd_ne_zero_left h1) (Nat.lcm_ne_zero g1 g2),
    Nat.factorization_gcd h1 hw, Nat.factorization_lcm hu hv, Nat.factorization_lcm g1 g2,
    Nat.factorization_gcd hu hw, Nat.factorization_gcd hv hw]
  intro p
  simp only [Finsupp.inf_apply, Finsupp.sup_apply]
  omega

lemma gcd_finsetLcm_dvd {ι : Type*} [DecidableEq ι] (S : Finset ι) (D : ι → ℕ)
    (hD : ∀ j ∈ S, D j ≠ 0) {w : ℕ} (hw : w ≠ 0) :
    Nat.gcd (S.lcm D) w ∣ S.lcm (fun j ↦ Nat.gcd (D j) w) := by
  induction S using Finset.induction_on with
  | empty => simp
  | insert b S hb ih =>
    rw [Finset.lcm_insert, Finset.lcm_insert]
    have hS : S.lcm D ≠ 0 := by
      rw [Ne, Finset.lcm_eq_zero_iff]; push_neg
      intro j hj; exact hD j (Finset.mem_insert_of_mem hj)
    have hb0 := hD b (Finset.mem_insert_self b S)
    refine (gcd_lcm_dvd hb0 hS hw).trans ?_
    exact lcm_dvd_lcm dvd_rfl (ih fun j hj ↦ hD j (Finset.mem_insert_of_mem hj))

/-- **Generalized CRT.** Pairwise compatible congruences have a common solution. -/
theorem exists_common_exponent {ι : Type*} [DecidableEq ι] (S : Finset ι) (D k : ι → ℕ)
    (hD : ∀ j ∈ S, D j ≠ 0)
    (h : ∀ a ∈ S, ∀ b ∈ S, ((Nat.gcd (D a) (D b) : ℕ) : ℤ) ∣ (k a : ℤ) - k b) :
    ∃ K : ℕ, ∀ j ∈ S, ((D j : ℕ) : ℤ) ∣ (K : ℤ) - k j := by
  induction S using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | insert a S ha ih =>
    obtain ⟨K', hK'⟩ := ih (fun j hj ↦ hD j (Finset.mem_insert_of_mem hj))
      (fun x hx y hy ↦ h x (Finset.mem_insert_of_mem hx) y (Finset.mem_insert_of_mem hy))
    set L := S.lcm D with hL
    have hDa := hD a (Finset.mem_insert_self a S)
    -- compatibility of K' with k a modulo gcd L (D a)
    have hcomp : ((Nat.gcd L (D a) : ℕ) : ℤ) ∣ (K' : ℤ) - k a := by
      have h1 := gcd_finsetLcm_dvd S D (fun j hj ↦ hD j (Finset.mem_insert_of_mem hj)) hDa
      refine Int.natCast_dvd_natCast.2 h1 |>.trans ?_
      rw [Int.natCast_dvd]
      apply Finset.lcm_dvd
      intro j hj
      rw [← Int.natCast_dvd]
      have h2 := hK' j hj
      have h3 := h j (Finset.mem_insert_of_mem hj) a (Finset.mem_insert_self a S)
      have h4 : ((Nat.gcd (D j) (D a) : ℕ) : ℤ) ∣ (K' : ℤ) - k j :=
        (Int.natCast_dvd_natCast.2 (Nat.gcd_dvd_left _ _)).trans h2
      have := dvd_add h4 h3
      rwa [sub_add_sub_cancel] at this
    have hmod : K' ≡ k a [MOD Nat.gcd L (D a)] := Nat.modEq_iff_dvd.2 (by
      rw [show ((k a : ℕ) : ℤ) - K' = -((K' : ℤ) - k a) by ring]; exact dvd_neg.2 hcomp)
    obtain ⟨K, hK1, hK2⟩ := Nat.chineseRemainder' hmod
    refine ⟨K, fun j hj ↦ ?_⟩
    rcases Finset.mem_insert.1 hj with rfl | hj
    · exact Nat.modEq_iff_dvd.1 hK2.symm
    · have hDL : D j ∣ L := Finset.dvd_lcm hj
      have h1 : ((D j : ℕ) : ℤ) ∣ (K : ℤ) - K' :=
        (Int.natCast_dvd_natCast.2 hDL).trans (Nat.modEq_iff_dvd.1 hK1.symm)
      have := dvd_add h1 (hK' j hj)
      rwa [sub_add_sub_cancel] at this

variable {N : ℕ} [NeZero N]

/-- In `ZMod N`, `N` squarefree, agreement modulo every prime factor gives equality. -/
lemma eq_of_cast_prime_eq (hsq : Squarefree N) {x y : ZMod N}
    (h : ∀ q ∈ N.primeFactors, (ZMod.cast x : ZMod q) = ZMod.cast y) : x = y := by
  rw [← sub_eq_zero]
  have hdvd : ∀ q ∈ N.primeFactors, q ∣ (x - y).val := by
    intro q hq
    rw [← cast_eq_zero_iff_dvd_val, ZMod.cast_sub (Nat.dvd_of_mem_primeFactors hq), h q hq,
      sub_self]
  have hN : N ∣ (x - y).val := by
    conv_lhs => rw [← Nat.prod_primeFactors_of_squarefree hsq]
    exact Finset.prod_primes_dvd _ (fun a ha ↦ (Nat.prime_of_mem_primeFactors ha).prime) hdvd
  exact (ZMod.val_eq_zero _).1 (Nat.eq_zero_of_dvd_of_lt hN (ZMod.val_lt _))

/-- **Lemma 4.** -/
theorem lemma4 (hsq : Squarefree N) {ρ₁ ρ₂ : ZMod N} {d : ℕ} (hd : 0 < d) (ho : orderOf ρ₁ = d)
    (h : ∀ a ∈ N.primeFactors, ∀ b ∈ N.primeFactors, ∃ c : ℕ,
      (ZMod.cast ρ₁ : ZMod a) ^ c = ZMod.cast ρ₂ ∧ (ZMod.cast ρ₁ : ZMod b) ^ c = ZMod.cast ρ₂) :
    ∃ K : ℕ, ρ₁ ^ K = ρ₂ := by
  classical
  have hpow : ∀ q ∈ N.primeFactors, (ZMod.cast ρ₁ : ZMod q) ^ d = 1 := by
    intro q hq
    rw [← ZMod.cast_pow (Nat.dvd_of_mem_primeFactors hq), ← ho, pow_orderOf_eq_one,
      ZMod.cast_one (Nat.dvd_of_mem_primeFactors hq)]
  set D : ℕ → ℕ := fun q ↦ if hq : q ∈ N.primeFactors then
    orderOf (ZMod.cast ρ₁ : ZMod q) else 1 with hDdef
  have hDq : ∀ q ∈ N.primeFactors, D q = orderOf (ZMod.cast ρ₁ : ZMod q) := by
    intro q hq; simp only [hDdef, dif_pos hq]
  have hD0 : ∀ q ∈ N.primeFactors, D q ≠ 0 := by
    intro q hq
    rw [hDq q hq]
    exact (isOfFinOrder_iff_pow_eq_one.2 ⟨d, hd, hpow q hq⟩).orderOf_pos.ne'
  choose! k hk using fun q (hq : q ∈ N.primeFactors) ↦ h q hq q hq
  have hcompat : ∀ a ∈ N.primeFactors, ∀ b ∈ N.primeFactors,
      ((Nat.gcd (D a) (D b) : ℕ) : ℤ) ∣ (k a : ℤ) - k b := by
    intro a ha b hb
    obtain ⟨c, hca, hcb⟩ := h a ha b hb
    have e1 : c ≡ k a [MOD D a] := by
      rw [hDq a ha]
      exact ((isOfFinOrder_iff_pow_eq_one.2 ⟨d, hd, hpow a ha⟩).pow_inj_mod).1
        (by rw [hca, (hk a ha).1])
    have e2 : c ≡ k b [MOD D b] := by
      rw [hDq b hb]
      exact ((isOfFinOrder_iff_pow_eq_one.2 ⟨d, hd, hpow b hb⟩).pow_inj_mod).1
        (by rw [hcb, (hk b hb).1])
    have f1 := Nat.modEq_iff_dvd.1 (e1.of_dvd (Nat.gcd_dvd_left (D a) (D b)))
    have f2 := Nat.modEq_iff_dvd.1 (e2.of_dvd (Nat.gcd_dvd_right (D a) (D b)))
    have := dvd_sub f1 f2
    rwa [sub_sub_sub_cancel_right] at this
  obtain ⟨K, hK⟩ := exists_common_exponent N.primeFactors D k hD0 hcompat
  refine ⟨K, eq_of_cast_prime_eq hsq fun q hq ↦ ?_⟩
  rw [ZMod.cast_pow (Nat.dvd_of_mem_primeFactors hq), ← (hk q hq).1]
  refine ((isOfFinOrder_iff_pow_eq_one.2 ⟨d, hd, hpow q hq⟩).pow_inj_mod).2 ?_
  rw [← hDq q hq]
  exact (Nat.modEq_iff_dvd.2 (hK q hq)).symm

end TwoPrimes

-- ===== Fibre =====

/-!
# Fibre sums for MO 503314 (the identity (‡) and orthogonality from fibres)

For a prime `p ∣ N` (`N` squarefree) and `n = N / p`, fibres of `ZMod N → ZMod n`.
-/

open Complex Finset

namespace TwoPrimes

variable {N : ℕ} [NeZero N]

/-- The fibre of `ZMod N → ZMod (N/p)` over `xb`. -/
noncomputable def fib (p : ℕ) (xb : ZMod (N / p)) : Finset (ZMod N) :=
  univ.filter fun y ↦ (ZMod.cast y : ZMod (N / p)) = xb

noncomputable def uind (y : ZMod N) : ℂ := if IsUnit y then 1 else 0

lemma cast_cast_eq {a b : ℕ} (hab : a ∣ b) (hb : b ∣ N) (y : ZMod N) :
    (ZMod.cast (ZMod.cast y : ZMod b) : ZMod a) = (ZMod.cast y : ZMod a) := by
  have h : (ZMod.castHom hab (ZMod a)).comp (ZMod.castHom hb (ZMod b)) =
      ZMod.castHom (hab.trans hb) (ZMod a) := Subsingleton.elim _ _
  exact RingHom.congr_fun h y

lemma isUnit_of_cast_ne_zero {y : ZMod N} (h : ∀ q ∈ N.primeFactors, (ZMod.cast y : ZMod q) ≠ 0) :
    IsUnit y := by
  rw [← ZMod.natCast_zmod_val y, ZMod.isUnit_iff_coprime, Nat.coprime_iff_gcd_eq_one]
  by_contra hne
  obtain ⟨q, hq, hqd⟩ := Nat.exists_prime_and_dvd hne
  have hqN : q ∣ N := hqd.trans (Nat.gcd_dvd_right _ _)
  apply h q (Nat.mem_primeFactors.2 ⟨hq, hqN, NeZero.ne N⟩)
  rw [cast_eq_zero_iff_dvd_val]
  exact hqd.trans (Nat.gcd_dvd_left _ _)

/-- Units split as units mod `N/p` and nonzero mod `p`. -/
lemma isUnit_iff_split {p : ℕ} (hp : p ∈ N.primeFactors) (y : ZMod N) :
    IsUnit y ↔ IsUnit (ZMod.cast y : ZMod (N / p)) ∧ (ZMod.cast y : ZMod p) ≠ 0 := by
  have hpN := Nat.dvd_of_mem_primeFactors hp
  have hpp := Nat.prime_of_mem_primeFactors hp
  have hdN : N / p ∣ N := Nat.div_dvd_of_dvd hpN
  constructor
  · intro hy
    refine ⟨?_, cast_ne_zero_of_isUnit hp hy⟩
    have := hy.map (ZMod.castHom hdN (ZMod (N / p)))
    simpa using this
  · rintro ⟨h1, h2⟩
    apply isUnit_of_cast_ne_zero
    intro q hq
    by_cases hqp : q = p
    · subst hqp; exact h2
    · have hqn : q ∣ N / p := by
        have hcop : Nat.Coprime q p :=
          (Nat.coprime_primes (Nat.prime_of_mem_primeFactors hq) hpp).2 hqp
        exact hcop.dvd_of_dvd_mul_left (by rw [Nat.mul_div_cancel' hpN]; exact Nat.dvd_of_mem_primeFactors hq)
      have hqn' : q ∈ (N / p).primeFactors := Nat.mem_primeFactors.2
        ⟨Nat.prime_of_mem_primeFactors hq, hqn,
          (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne N)) hpN) hpp.pos).ne'⟩
      haveI : NeZero (N / p) := ⟨(Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne N))
        hpN) hpp.pos).ne'⟩
      have := cast_ne_zero_of_isUnit hqn' h1
      rwa [cast_cast_eq hqn hdN] at this

/-- A single term of the fibre sum. -/
lemma fibre_single {p : ℕ} (hp : p ∈ N.primeFactors) {xb : ZMod (N / p)} (hxb : IsUnit xb)
    (g : ZMod N) :
    ∑ y ∈ fib p xb, uind y * (if g = y + 1 then 1 else 0) =
      if (ZMod.cast g : ZMod (N / p)) = xb + 1 ∧ (ZMod.cast g : ZMod p) ≠ 1 then 1 else 0 := by
  have hpN := Nat.dvd_of_mem_primeFactors hp
  have hdN : N / p ∣ N := Nat.div_dvd_of_dvd hpN
  have h1 : ∀ y, (g = y + 1) ↔ (y = g - 1) := fun y ↦ by
    constructor <;> intro h <;> [rw [h]; rw [h]] <;> ring
  simp only [h1, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq']
  have hmem : g - 1 ∈ fib p xb ↔ (ZMod.cast g : ZMod (N / p)) = xb + 1 := by
    simp only [fib, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [ZMod.cast_sub hdN, ZMod.cast_one hdN, sub_eq_iff_eq_add]
  by_cases hg : (ZMod.cast g : ZMod (N / p)) = xb + 1
  · rw [if_pos (hmem.2 hg)]
    have hc : (ZMod.cast (g - 1) : ZMod (N / p)) = xb := by
      rw [ZMod.cast_sub hdN, ZMod.cast_one hdN, hg, add_sub_cancel_right]
    have hu : IsUnit (g - 1) ↔ (ZMod.cast g : ZMod p) ≠ 1 := by
      rw [isUnit_iff_split hp, hc, ZMod.cast_sub hpN, ZMod.cast_one hpN, Ne, sub_eq_zero]
      exact ⟨fun h ↦ h.2, fun h ↦ ⟨hxb, h⟩⟩
    simp only [uind, hu, hg, true_and]
  · rw [if_neg (fun h ↦ hg (hmem.1 h)), if_neg (fun h ↦ hg h.1)]

/-- Level-`n` count of the kernel part. -/
noncomputable def Lc (p d : ℕ) (ρ : ZMod N) (zb : ZMod (N / p)) : ℂ :=
  ∑ u ∈ range d, if (ZMod.cast ρ : ZMod (N / p)) ^ u = zb ∧ (ZMod.cast ρ : ZMod p) ^ u = 1
    then 1 else 0

/-- The fibre sum of `uind · ind(· + 1)`. -/
lemma fibre_ind {p : ℕ} [NeZero (N / p)] (hp : p ∈ N.primeFactors) (hp2 : 2 < p) {d : ℕ}
    (hd : Odd d)
    {ρ : ZMod N} (hρ : ρ ^ d = 1) {xb : ZMod (N / p)} (hxb : IsUnit xb) :
    ∑ y ∈ fib p xb, uind y * ind d ρ (y + 1) =
      ind d (ZMod.cast ρ : ZMod (N / p)) (xb + 1) - Lc p d ρ (xb + 1) := by
  have hpN := Nat.dvd_of_mem_primeFactors hp
  have hdN : N / p ∣ N := Nat.div_dvd_of_dvd hpN
  have hρp : (ZMod.cast ρ : ZMod p) ^ d = 1 := by
    rw [← ZMod.cast_pow hpN, hρ, ZMod.cast_one hpN]
  simp only [ind, Finset.mul_sum, mul_add]
  rw [Finset.sum_comm, Lc, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun u _ ↦ ?_
  rw [Finset.sum_add_distrib, fibre_single hp hxb, fibre_single hp hxb]
  have hneg : (ZMod.cast (-ρ ^ u) : ZMod p) ≠ 1 := by
    rw [ZMod.cast_neg hpN, ZMod.cast_pow hpN]
    intro h
    exact pow_ne_neg_one' hd hρp hp2 u (by rw [← neg_neg ((ZMod.cast ρ : ZMod p) ^ u), h])
  simp only [ZMod.cast_neg hdN, ZMod.cast_pow hdN, ZMod.cast_pow hpN, ne_eq, hneg,
    not_false_eq_true, and_true]
  rw [ZMod.cast_neg hpN, ZMod.cast_pow hpN] at hneg
  by_cases h1 : (ZMod.cast ρ : ZMod (N / p)) ^ u = xb + 1 <;>
    by_cases h2 : (ZMod.cast ρ : ZMod p) ^ u = 1 <;> simp [h1, h2]


/-! ## Equal counts from the induction hypothesis -/

lemma ind_eq_of_pow {n : ℕ} [NeZero n] {σ₁ σ₂ : ZMod n} {d c : ℕ} (hd : 0 < d)
    (ho₁ : orderOf σ₁ = d) (ho₂ : orderOf σ₂ = d) (hc : σ₁ ^ c = σ₂) (z : ZMod n) :
    ind d σ₂ z = ind d σ₁ z := by
  have := sum_filter_pow_eq hd ho₁ ho₂ hc (one_dvd d)
    (fun g ↦ (if g = z then 1 else 0) + (if -g = z then 1 else 0))
  simpa [ind] using this

lemma Lc_eq_of_pow {p : ℕ} (hp : p ∈ N.primeFactors) {ρ₁ ρ₂ : ZMod N} {d c : ℕ} (hd : 0 < d)
    (ho₁ : orderOf (ZMod.cast ρ₁ : ZMod (N / p)) = d) (ho₂ : orderOf (ZMod.cast ρ₂ : ZMod (N / p)) = d)
    (hc : (ZMod.cast ρ₁ : ZMod (N / p)) ^ c = ZMod.cast ρ₂)
    (hρ₁ : ρ₁ ^ d = 1)
    (hop : orderOf (ZMod.cast ρ₁ : ZMod p) = orderOf (ZMod.cast ρ₂ : ZMod p)) (z : ZMod (N / p)) :
    Lc p d ρ₂ z = Lc p d ρ₁ z := by
  have hpN := Nat.dvd_of_mem_primeFactors hp
  have hρp : (ZMod.cast ρ₁ : ZMod p) ^ d = 1 := by
    rw [← ZMod.cast_pow hpN, hρ₁, ZMod.cast_one hpN]
  have he : orderOf (ZMod.cast ρ₁ : ZMod p) ∣ d := orderOf_dvd_of_pow_eq_one hρp
  have := sum_filter_pow_eq hd ho₁ ho₂ hc he (fun g ↦ if g = z then (1 : ℂ) else 0)
  simp only [Lc]
  have h1 : ∀ (ρ : ZMod N) (u : ℕ), ((ZMod.cast ρ : ZMod p) ^ u = 1) ↔
      orderOf (ZMod.cast ρ : ZMod p) ∣ u := fun ρ u ↦ orderOf_dvd_iff_pow_eq_one.symm
  simp only [h1, ← hop]
  convert this using 2 <;> rename_i u _ <;> by_cases h : orderOf (ZMod.cast ρ₁ : ZMod p) ∣ u <;>
    simp [h, and_comm]

/-! ## Orthogonality from fibres and from periodicity -/

lemma primFun_factor (χ : DirichletCharacter ℂ N) {p : ℕ} (hp : p ∈ N.primeFactors)
    (h : χ.conductor ∣ N / p) (x : ZMod N) :
    primFun χ x = χ.primitiveCharacter
      (ZMod.cast (ZMod.cast x : ZMod (N / p)) : ZMod χ.conductor) := by
  rw [primFun, cast_cast_eq h (Nat.div_dvd_of_dvd (Nat.dvd_of_mem_primeFactors hp))]

/-- Orthogonality to characters factoring through `N/p`, from vanishing fibre sums. -/
theorem orth_of_fibre {p : ℕ} [NeZero (N / p)] (hp : p ∈ N.primeFactors) (φ : ZMod N → ℂ)
    (hφ : ∀ y, ¬ IsUnit y → φ y = 0)
    (hfib : ∀ xb : ZMod (N / p), IsUnit xb → ∑ y ∈ fib p xb, φ y = 0)
    (χ : DirichletCharacter ℂ N) (hχ : χ.conductor ∣ N / p) : ∑ x, φ x * χ x = 0 := by
  classical
  have hpN := Nat.dvd_of_mem_primeFactors hp
  have hdN : N / p ∣ N := Nat.div_dvd_of_dvd hpN
  have h1 : ∀ x, φ x * χ x = φ x * χ.primitiveCharacter
      (ZMod.cast (ZMod.cast x : ZMod (N / p)) : ZMod χ.conductor) := by
    intro x
    by_cases hx : IsUnit x
    · rw [← primFun_factor χ hp hχ, ← IsUnit.unit_spec hx, primFun_unit]
    · rw [hφ x hx, zero_mul, zero_mul]
  simp only [h1]
  rw [← Finset.sum_fiberwise Finset.univ (fun x ↦ (ZMod.cast x : ZMod (N / p)))]
  refine Finset.sum_eq_zero fun xb _ ↦ ?_
  have h2 : ∀ x ∈ univ.filter (fun x ↦ (ZMod.cast x : ZMod (N / p)) = xb),
      φ x * χ.primitiveCharacter (ZMod.cast (ZMod.cast x : ZMod (N / p)) : ZMod χ.conductor)
      = φ x * χ.primitiveCharacter (ZMod.cast xb : ZMod χ.conductor) := by
    intro x hx; rw [(Finset.mem_filter.1 hx).2]
  rw [Finset.sum_congr rfl h2, ← Finset.sum_mul]
  by_cases hxb : IsUnit xb
  · have := hfib xb hxb
    simp only [fib] at this
    rw [this, zero_mul]
  · rw [Finset.sum_eq_zero, zero_mul]
    intro x hx
    rw [Finset.mem_filter] at hx
    apply hφ
    intro hu
    apply hxb
    rw [← hx.2]
    have := hu.map (ZMod.castHom hdN (ZMod (N / p)))
    simpa using this

/-- Orthogonality of `N/p`-periodic functions to characters not factoring through `N/p`. -/
theorem orth_of_periodic (hsq : Squarefree N) {p : ℕ} (hp : p ∈ N.primeFactors)
    (g : ZMod N → ℂ) (hg : Periodic' p g) (χ : DirichletCharacter ℂ N) (hχ : p ∣ χ.conductor) :
    ∑ x, g x * χ x = 0 := by
  have hpN := Nat.dvd_of_mem_primeFactors hp
  have hpp := Nat.prime_of_mem_primeFactors hp
  have hdN : N / p ∣ N := Nat.div_dvd_of_dvd hpN
  have hnot : ¬ χ.FactorsThrough (N / p) := by
    intro hf
    have h1 : χ.conductor ∣ N / p :=
      (DirichletCharacter.mem_conductorSet_iff_conductor_dvd χ hdN).1 hf
    have h2 : p * p ∣ N := by
      have := Nat.mul_dvd_mul_left p (hχ.trans h1)
      rwa [Nat.mul_div_cancel' hpN] at this
    exact hpp.one_lt.ne' (Nat.isUnit_iff.1 (hsq p h2))
  rw [DirichletCharacter.factorsThrough_iff_ker_unitsMap hdN, SetLike.not_le_iff_exists] at hnot
  obtain ⟨u, hu, hχu'⟩ := hnot
  have hχu : χ u ≠ 1 := by
    intro h1; apply hχu'
    rw [MonoidHom.mem_ker]
    exact Units.ext (by rw [MulChar.coe_toUnitHom, h1]; rfl)
  have hcast : (ZMod.cast (u : ZMod N) : ZMod (N / p)) = 1 := by
    have := congrArg Units.val (MonoidHom.mem_ker.1 hu)
    simpa [ZMod.unitsMap_val] using this
  obtain ⟨a, ha⟩ := sub_one_eq_nn_mul hpN hcast
  have hinv : ∀ x, g (u * x) = g x := by
    intro x
    rw [ha, add_mul, one_mul, mul_assoc, hg]
  have hS0 : ∑ x, g (u * x) * χ (u * x) = ∑ x, g x * χ x :=
    Fintype.sum_equiv (Units.mulLeft u) _ _ (fun x ↦ rfl)
  have hS : ∑ x, g x * χ x = χ u * ∑ x, g x * χ x := by
    calc ∑ x, g x * χ x = ∑ x, g (u * x) * χ (u * x) := hS0.symm
      _ = χ u * ∑ x, g x * χ x := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun x _ ↦ ?_
        rw [hinv, map_mul]; ring
  have : (1 - χ u) * ∑ x, g x * χ x = 0 := by rw [sub_mul, one_mul, ← hS, sub_self]
  rcases mul_eq_zero.1 this with h | h
  · exact absurd (sub_eq_zero.1 h).symm hχu
  · exact h

end TwoPrimes

-- ===== Main =====

/-!
# MO 503314: the induction (squarefree moduli) and the reduction to squarefree moduli
-/

open Complex Finset

namespace TwoPrimes

variable {N : ℕ} [NeZero N]

local notation "e" => (ZMod.stdAddChar : AddChar (ZMod N) ℂ)

/-! ## CRT counting in a fibre -/

lemma crt_exists {p : ℕ} (hsq : Squarefree N) (hp : p ∈ N.primeFactors) (a : ZMod p)
    (b : ZMod (N / p)) : ∃ y : ZMod N, (ZMod.cast y : ZMod p) = a ∧ (ZMod.cast y : ZMod (N / p)) = b := by
  have hpN := Nat.dvd_of_mem_primeFactors hp
  have hpp := Nat.prime_of_mem_primeFactors hp
  have hcop : Nat.Coprime p (N / p) := by
    rw [Nat.Prime.coprime_iff_not_dvd hpp]
    intro h
    have : p * p ∣ N := by
      have := Nat.mul_dvd_mul_left p h; rwa [Nat.mul_div_cancel' hpN] at this
    exact hpp.one_lt.ne' (Nat.isUnit_iff.1 (hsq p this))
  have hN : p * (N / p) = N := Nat.mul_div_cancel' hpN
  set E : ZMod N ≃+* ZMod p × ZMod (N / p) :=
    (ZMod.ringEquivCongr hN).symm.trans (ZMod.chineseRemainder hcop) with hE
  have h1 : (RingHom.fst _ _).comp (E : ZMod N →+* ZMod p × ZMod (N / p)) =
      ZMod.castHom hpN (ZMod p) := Subsingleton.elim _ _
  have h2 : (RingHom.snd _ _).comp (E : ZMod N →+* ZMod p × ZMod (N / p)) =
      ZMod.castHom (Nat.div_dvd_of_dvd hpN) (ZMod (N / p)) := Subsingleton.elim _ _
  refine ⟨E.symm (a, b), ?_, ?_⟩
  · have hx : (E (E.symm (a, b))).1 = ZMod.castHom hpN (ZMod p) (E.symm (a, b)) :=
      RingHom.congr_fun h1 _
    rw [RingEquiv.apply_symm_apply] at hx
    exact hx.symm
  · have hx : (E (E.symm (a, b))).2 =
        ZMod.castHom (Nat.div_dvd_of_dvd hpN) (ZMod (N / p)) (E.symm (a, b)) :=
      RingHom.congr_fun h2 _
    rw [RingEquiv.apply_symm_apply] at hx
    exact hx.symm

lemma sum_uind_fib {p : ℕ} (hsq : Squarefree N) (hp : p ∈ N.primeFactors) {xb : ZMod (N / p)}
    (hxb : IsUnit xb) : ∑ y ∈ fib p xb, uind y = ((p - 1 : ℕ) : ℂ) := by
  classical
  have hpN := Nat.dvd_of_mem_primeFactors hp
  have hpp := Nat.prime_of_mem_primeFactors hp
  have hqsq : ¬ p * p ∣ N := fun h ↦ hpp.one_lt.ne' (Nat.isUnit_iff.1 (hsq p h))
  haveI : Fact p.Prime := ⟨hpp⟩
  simp only [uind]
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
  congr 1
  have hset : (fib p xb).filter IsUnit =
      (fib p xb).filter (fun y ↦ (ZMod.cast y : ZMod p) ≠ 0) := by
    refine Finset.filter_congr fun y hy ↦ ?_
    simp only [fib, Finset.mem_filter, Finset.mem_univ, true_and] at hy
    rw [isUnit_iff_split hp, hy]; exact ⟨fun h ↦ h.2, fun h ↦ ⟨hxb, h⟩⟩
  rw [hset]
  have hinj : Set.InjOn (fun y : ZMod N ↦ (ZMod.cast y : ZMod p))
      ↑((fib p xb).filter (fun y ↦ (ZMod.cast y : ZMod p) ≠ 0)) := by
    intro y hy y' hy' h
    have hy1 := Finset.mem_filter.1 (Finset.mem_filter.1 (Finset.mem_coe.1 hy)).1
    have hy2 := Finset.mem_filter.1 (Finset.mem_filter.1 (Finset.mem_coe.1 hy')).1
    exact eq_of_cast_eq hpp hpN hqsq h (by rw [hy1.2, hy2.2])
  rw [← Finset.card_image_of_injOn hinj]
  have himg : ((fib p xb).filter (fun y ↦ (ZMod.cast y : ZMod p) ≠ 0)).image
      (fun y : ZMod N ↦ (ZMod.cast y : ZMod p)) = Finset.univ.erase 0 := by
    ext a
    simp only [Finset.mem_image, Finset.mem_filter, fib, Finset.mem_univ, true_and,
      Finset.mem_erase, and_true]
    constructor
    · rintro ⟨y, ⟨-, hy⟩, rfl⟩; exact hy
    · intro ha
      obtain ⟨y, hy1, hy2⟩ := crt_exists hsq hp a xb
      exact ⟨y, ⟨hy2, by rw [hy1]; exact ha⟩, hy1⟩
  rw [himg, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, ZMod.card]

set_option maxHeartbeats 1000000 in
/-- Fibre sum of `uind · (A(·+1) + A(1-·))`. -/
lemma fibre_sym {p : ℕ} (A : ZMod N → ℂ) (xb : ZMod (N / p)) (hp : p ∣ N) :
    ∑ y ∈ fib p xb, uind y * (A (y + 1) + A (1 - y)) =
      ∑ y ∈ fib p xb, uind y * A (y + 1) + ∑ y ∈ fib p (-xb), uind y * A (y + 1) := by
  have hdN : N / p ∣ N := Nat.div_dvd_of_dvd hp
  simp only [mul_add, Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_nbij' (fun y ↦ -y) (fun y ↦ -y) ?_ ?_ (fun y _ ↦ neg_neg y)
    (fun y _ ↦ neg_neg y) ?_
  · intro y hy
    simp only [fib, Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
    rw [ZMod.cast_neg hdN, hy]
  · intro y hy
    simp only [fib, Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
    rw [ZMod.cast_neg hdN, hy, neg_neg]
  · intro y _
    simp only [uind, IsUnit.neg_iff]
    congr 2; ring


/-! ## Natural-number versions, integrality, conclusion -/

noncomputable def indN (d : ℕ) (ρ x : ZMod N) : ℕ :=
  ∑ u ∈ range d, ((if ρ ^ u = x then 1 else 0) + (if -ρ ^ u = x then 1 else 0))

lemma ind_eq_indN (d : ℕ) (ρ x : ZMod N) : ind d ρ x = (indN d ρ x : ℂ) := by
  simp only [ind, indN]; push_cast; rfl

lemma ind_eq_zero_of_not_unit {ρ : ZMod N} (hρ : IsUnit ρ) (d : ℕ) {x : ZMod N}
    (hx : ¬ IsUnit x) : ind d ρ x = 0 := by
  simp only [ind]
  refine Finset.sum_eq_zero fun u _ ↦ ?_
  rw [if_neg (fun h ↦ hx (by rw [← h]; exact hρ.pow u)),
    if_neg (fun h ↦ hx (by rw [← h]; exact (hρ.pow u).neg)), add_zero]

lemma ff_eq_zero_of_not_unit {ρ₁ ρ₂ : ZMod N} (h₁ : IsUnit ρ₁) (h₂ : IsUnit ρ₂) (d : ℕ)
    {x : ZMod N} (hx : ¬ IsUnit x) : ff d ρ₁ ρ₂ x = 0 := by
  rw [ff, ind_eq_zero_of_not_unit h₁ d hx, ind_eq_zero_of_not_unit h₂ d hx, sub_zero]

/-- From `ff(-ρ₂) = 0` to the conclusion. -/
theorem conclude {ρ₁ ρ₂ : ZMod N} {d : ℕ} (hd : Odd d) (hd1 : 1 < d) (ho₁ : orderOf ρ₁ = d)
    (ho₂ : orderOf ρ₂ = d) (hN : 2 < N) (h : ff d ρ₁ ρ₂ (-ρ₂) = 0) : ∃ c : ℕ, ρ₁ ^ c = ρ₂ := by
  rw [ff, sub_eq_zero, ind_eq_indN, ind_eq_indN] at h
  have h1 : indN d ρ₁ (-ρ₂) = indN d ρ₂ (-ρ₂) := by exact_mod_cast h
  have h2 : 1 ≤ indN d ρ₂ (-ρ₂) := by
    unfold indN
    refine le_trans ?_ (Finset.single_le_sum (f := fun u ↦ (if ρ₂ ^ u = -ρ₂ then 1 else 0) +
      (if -ρ₂ ^ u = -ρ₂ then 1 else 0)) (fun _ _ ↦ Nat.zero_le _)
      (Finset.mem_range.2 hd1))
    simp
  rw [← h1] at h2
  have h3 : indN d ρ₁ (-ρ₂) ≠ 0 := by omega
  obtain ⟨u, hu, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero h3
  by_cases ha : -ρ₁ ^ u = -ρ₂
  · exact ⟨u, neg_inj.1 ha⟩
  · by_cases hb : ρ₁ ^ u = -ρ₂
    · exfalso
      have hρ1d : ρ₁ ^ d = 1 := by rw [← ho₁, pow_orderOf_eq_one]
      have hneg : ρ₂ ^ d = -1 := by
        rw [show ρ₂ = -ρ₁ ^ u by rw [hb, neg_neg], hd.neg_pow, ← pow_mul, mul_comm, pow_mul,
          hρ1d, one_pow]
      have h4 : ρ₂ ^ d = 1 := by rw [← ho₂, pow_orderOf_eq_one]
      haveI : Fact (2 < N) := ⟨hN⟩
      exact ZMod.neg_one_ne_one (hneg.symm.trans h4)
    · simp [ha, hb] at hne


/-! ## Lemma 3 with character input -/

lemma dvd_div_of_ne {a j : ℕ} (ha : a ∈ N.primeFactors) (hj : j ∈ N.primeFactors) (h : a ≠ j) :
    a ∣ N / j := by
  have hcop : Nat.Coprime a j :=
    (Nat.coprime_primes (Nat.prime_of_mem_primeFactors ha) (Nat.prime_of_mem_primeFactors hj)).2 h
  have hjN := Nat.dvd_of_mem_primeFactors hj
  have haN := Nat.dvd_of_mem_primeFactors ha
  exact hcop.dvd_of_dvd_mul_left (by rw [Nat.mul_div_cancel' hjN]; exact haN)

lemma cast_goodMult {p q : ℕ} {t : ZMod N} (ht : GoodMult p t) (hp : p ∈ N.primeFactors)
    (hq : q ∈ N.primeFactors) (hqp : q ≠ p) : (ZMod.cast t : ZMod q) = 1 := by
  obtain ⟨a, ha⟩ := ht.cong
  have hqN := Nat.dvd_of_mem_primeFactors hq
  rw [ha, ZMod.cast_add hqN, ZMod.cast_one hqN, ZMod.cast_mul hqN, nn, ZMod.cast_natCast hqN,
    (ZMod.natCast_eq_zero_iff _ _).2 (dvd_div_of_ne hq hp hqp), zero_mul, add_zero]

lemma cast_add_nn {p q : ℕ} (hp : p ∈ N.primeFactors) (hq : q ∈ N.primeFactors) (hqp : q ≠ p)
    (x y : ZMod N) : (ZMod.cast (x + nn N p * y) : ZMod q) = ZMod.cast x := by
  have hqN := Nat.dvd_of_mem_primeFactors hq
  rw [ZMod.cast_add hqN, ZMod.cast_mul hqN, nn, ZMod.cast_natCast hqN,
    (ZMod.natCast_eq_zero_iff _ _).2 (dvd_div_of_ne hq hp hqp), zero_mul, add_zero]

/-- **Lemma 3, full form.** -/
theorem lemma3full (hsq : Squarefree N) (T R : Finset ℕ) (hTR : T ∪ R = N.primeFactors)
    (hdisj : Disjoint T R) (hne : T.Nonempty) (t : ℕ → ZMod N) (ht : ∀ p ∈ T, GoodMult p (t p))
    (A : ZMod N → ℂ) (hA : ∀ p ∈ T, ∀ x, A (t p * x) = A x) (hAs : ∀ x, ¬ Cop T x → A x = 0)
    (horth : ∀ χ : DirichletCharacter ℂ N, (∀ p ∈ T, p ∣ χ.conductor) →
      ∑ x, (A (x + 1) + A (1 - x)) * χ x = 0) :
    ∀ y, (∀ q ∈ R, (ZMod.cast (y - 1) : ZMod q) ≠ 0) → A y = 0 := by
  classical
  have hT : T ⊆ N.primeFactors := hTR ▸ Finset.subset_union_left
  have hR : R ⊆ N.primeFactors := hTR ▸ Finset.subset_union_right
  have hTRne : ∀ p ∈ T, ∀ q ∈ R, q ≠ p := fun p hp q hq h ↦
    Finset.disjoint_left.1 hdisj hp (h ▸ hq)
  obtain ⟨F, hFp, hFu⟩ := char_decomp T hT (fun x ↦ A (x + 1) + A (1 - x)) horth
  set Ind : ZMod N → ℂ := fun y ↦ if ∀ q ∈ R, (ZMod.cast y : ZMod q) ≠ 0 then 1 else 0 with hInd
  have hIndc : ∀ y y', (∀ q ∈ R, (ZMod.cast y : ZMod q) = ZMod.cast y') → Ind y = Ind y' := by
    intro y y' h
    simp only [hInd]
    congr 1
    exact propext ⟨fun h1 q hq ↦ h q hq ▸ h1 q hq, fun h1 q hq ↦ (h q hq).symm ▸ h1 q hq⟩
  have hIndneg : ∀ y, Ind (-y) = Ind y := by
    intro y
    simp only [hInd]
    congr 1
    refine propext ⟨fun h1 q hq ↦ ?_, fun h1 q hq ↦ ?_⟩
    · have := h1 q hq
      rwa [ZMod.cast_neg (Nat.dvd_of_mem_primeFactors (hR hq)), neg_ne_zero] at this
    · rw [ZMod.cast_neg (Nat.dvd_of_mem_primeFactors (hR hq)), neg_ne_zero]; exact h1 q hq
  set A' : ZMod N → ℂ := fun y ↦ A y * Ind (y - 1) with hA'
  set B' : ZMod N → ℂ := fun y ↦ A' (-y) with hB'
  set F' : ℕ → ZMod N → ℂ := fun p x ↦ F p x * Ind x with hF'
  have hinvA : ∀ p ∈ T, ∀ x, A' (t p * x) = A' x := by
    intro p hp x
    simp only [hA']
    rw [hA p hp x]
    congr 1
    apply hIndc
    intro q hq
    have hqN := Nat.dvd_of_mem_primeFactors (hR hq)
    rw [ZMod.cast_sub hqN, ZMod.cast_sub hqN, ZMod.cast_mul hqN,
      cast_goodMult (ht p hp) (hT hp) (hR hq) (hTRne p hp q hq), one_mul]
  have hL := lemma3 hsq T hT hne t ht A' B' hinvA
    (fun p hp x ↦ by simp only [hB']; rw [← mul_neg, hinvA p hp])
    (fun x hx ↦ by simp only [hA']; rw [hAs x hx, zero_mul])
    (fun x hx ↦ by
      simp only [hB', hA']
      rw [hAs (-x) (fun h ↦ hx (by
        have := cop_neg hT h; rwa [neg_neg] at this)), zero_mul])
    F'
    (fun p hp x ↦ by
      simp only [hF']
      rw [hFp p hp x]
      congr 1
      apply hIndc
      intro q hq
      have := cast_add_nn (hT hp) (hR hq) (hTRne p hp q hq) x 1
      rwa [mul_one] at this)
    (fun x hx ↦ by
      simp only [hA', hB', hF']
      rw [show x + 1 - 1 = x by ring, show -(x - 1) - 1 = -x by ring, hIndneg,
        show -(x - 1) = 1 - x by ring, ← Finset.sum_mul, ← add_mul]
      by_cases hx' : ∀ q ∈ R, (ZMod.cast x : ZMod q) ≠ 0
      · congr 1
        apply hFu
        apply isUnit_of_cast_ne_zero
        intro q hq
        rw [← hTR, Finset.mem_union] at hq
        rcases hq with hq | hq
        · exact hx q hq
        · exact hx' q hq
      · simp only [hInd, if_neg hx', mul_zero])
  intro y hy
  have h1 := congrFun hL.1 y
  simp only [hA', hInd, if_pos hy, mul_one, Pi.zero_apply] at h1
  exact h1


/-! ## Helpers for the case analysis -/

lemma coprime_of_orderOf_pow {M : Type*} [Monoid M] {x : M} {d c : ℕ} (hd : 0 < d)
    (ho₁ : orderOf x = d) (ho₂ : orderOf (x ^ c) = d) : Nat.Coprime c d := by
  rcases Nat.eq_zero_or_pos c with rfl | hc0
  · rw [pow_zero, orderOf_one] at ho₂
    rw [← ho₂]; exact Nat.coprime_one_right 0
  have h := orderOf_pow' x hc0.ne'
  rw [ho₁, ho₂] at h
  have hpos : 0 < Nat.gcd d c := Nat.gcd_pos_of_pos_left c hd
  have : Nat.gcd d c = 1 := by
    by_contra hne
    have h2 : d / Nat.gcd d c < d := Nat.div_lt_self hd (by omega)
    omega
  rw [Nat.Coprime, Nat.gcd_comm]; exact this

lemma orderOf_pow_of_coprime' {M : Type*} [Monoid M] {x : M} {d c : ℕ} (hx : x ^ d = 1)
    (hc : Nat.Coprime c d) : orderOf (x ^ c) = orderOf x := by
  rcases Nat.eq_zero_or_pos c with rfl | hc0
  · rw [Nat.coprime_zero_left] at hc
    subst hc
    rw [pow_one] at hx
    rw [hx, pow_zero]
  rw [orderOf_pow' x hc0.ne']
  have h1 : Nat.gcd (orderOf x) c ∣ Nat.gcd d c :=
    Nat.gcd_dvd_gcd_of_dvd_left c (orderOf_dvd_of_pow_eq_one hx)
  rw [Nat.gcd_comm d c, hc] at h1
  rw [Nat.dvd_one.1 h1, Nat.div_one]

lemma pow_mod_of_pow_eq_one {M : Type*} [Monoid M] {x : M} {d : ℕ} (hx : x ^ d = 1) (n : ℕ) :
    x ^ (n % d) = x ^ n := by
  conv_rhs => rw [← Nat.mod_add_div n d, pow_add, pow_mul, hx, one_pow, mul_one]

lemma prime_gt_two {q : ℕ} (hodd : Odd N) (hq : q ∈ N.primeFactors) : 2 < q := by
  have hqp := Nat.prime_of_mem_primeFactors hq
  have hqN := Nat.dvd_of_mem_primeFactors hq
  have h2 : q ≠ 2 := by
    rintro rfl; exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 hqN)
  have := hqp.two_le
  omega

lemma pf_dvd_of_all {c : ℕ} (hsq : Squarefree N) (hc : c ∣ N)
    (h : ∀ q ∈ N.primeFactors, q ∣ c) : c = N := by
  apply Nat.dvd_antisymm hc
  conv_lhs => rw [← Nat.prod_primeFactors_of_squarefree hsq]
  exact Finset.prod_primes_dvd _ (fun a ha ↦ (Nat.prime_of_mem_primeFactors ha).prime) h

lemma exists_not_dvd_conductor (hsq : Squarefree N) (χ : DirichletCharacter ℂ N)
    (hχ : ¬ χ.IsPrimitive) : ∃ q ∈ N.primeFactors, ¬ q ∣ χ.conductor := by
  by_contra h
  push_neg at h
  exact hχ (pf_dvd_of_all hsq χ.conductor_dvd_level h)

lemma sum_eq_sum_uind (c : ZMod N → ℂ) (χ : DirichletCharacter ℂ N) :
    ∑ x, c x * χ x = ∑ x, uind x * c x * χ x := by
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  by_cases hx : IsUnit x
  · simp [uind, hx]
  · simp [uind, hx, MulChar.map_nonunit _ hx]

/-- The fibre sum of `uind · ff(· + 1)` when the level-`N/p` counts agree. -/
lemma fibre_ff {p : ℕ} [NeZero (N / p)] (hp : p ∈ N.primeFactors) (hp2 : 2 < p) {d : ℕ}
    (hd : Odd d) {ρ₁ ρ₂ : ZMod N} (hρ₁ : ρ₁ ^ d = 1) (hρ₂ : ρ₂ ^ d = 1)
    (hind : ∀ z, ind d (ZMod.cast ρ₂ : ZMod (N / p)) z = ind d (ZMod.cast ρ₁ : ZMod (N / p)) z)
    {xb : ZMod (N / p)} (hxb : IsUnit xb) :
    ∑ y ∈ fib p xb, uind y * ff d ρ₁ ρ₂ (y + 1) = Lc p d ρ₂ (xb + 1) - Lc p d ρ₁ (xb + 1) := by
  simp only [ff, mul_sub, Finset.sum_sub_distrib]
  rw [fibre_ind hp hp2 hd hρ₁ hxb, fibre_ind hp hp2 hd hρ₂ hxb, hind]
  ring

lemma cc_eq (d : ℕ) (ρ₁ ρ₂ x : ZMod N) :
    cc d ρ₁ ρ₂ x = ff d ρ₁ ρ₂ (x + 1) + ff d ρ₁ ρ₂ (1 - x) := by
  rw [cc, ← ff_neg d ρ₁ ρ₂ (x - 1), neg_sub]

/-- Orthogonality of `cc` to characters factoring through `N/p`, when the counts agree. -/
lemma orth_cc_fibre {p : ℕ} [NeZero (N / p)] (hp : p ∈ N.primeFactors) (hp2 : 2 < p) {d : ℕ}
    (hd : Odd d) {ρ₁ ρ₂ : ZMod N} (hρ₁ : ρ₁ ^ d = 1) (hρ₂ : ρ₂ ^ d = 1)
    (hind : ∀ z, ind d (ZMod.cast ρ₂ : ZMod (N / p)) z = ind d (ZMod.cast ρ₁ : ZMod (N / p)) z)
    (hLc : ∀ z, Lc p d ρ₂ z = Lc p d ρ₁ z)
    (χ : DirichletCharacter ℂ N) (hχ : χ.conductor ∣ N / p) :
    ∑ x, cc d ρ₁ ρ₂ x * χ x = 0 := by
  rw [sum_eq_sum_uind]
  have := orth_of_fibre hp (fun y ↦ uind y * cc d ρ₁ ρ₂ y)
    (fun y hy ↦ by simp [uind, hy]) ?_ χ hχ
  · simpa using this
  intro xb hxb
  simp only [cc_eq]
  rw [fibre_sym _ xb (Nat.dvd_of_mem_primeFactors hp), fibre_ff hp hp2 hd hρ₁ hρ₂ hind hxb,
    fibre_ff hp hp2 hd hρ₁ hρ₂ hind hxb.neg, hLc, hLc]
  ring


/-! ## Case: `T ≠ ∅`, every `q ∈ R` has the fibre identity -/

lemma neg_sub_one_cast_ne_zero (hodd : Odd N) {ρ : ZMod N} {d : ℕ} (hd : Odd d) (hρ : ρ ^ d = 1)
    {q : ℕ} (hq : q ∈ N.primeFactors) : (ZMod.cast (-ρ - 1) : ZMod q) ≠ 0 := by
  have hqN := Nat.dvd_of_mem_primeFactors hq
  have hq2 := prime_gt_two hodd hq
  have hρq : (ZMod.cast ρ : ZMod q) ^ d = 1 := by
    rw [← ZMod.cast_pow hqN, hρ, ZMod.cast_one hqN]
  rw [ZMod.cast_sub hqN, ZMod.cast_neg hqN, ZMod.cast_one hqN]
  intro h
  apply pow_ne_neg_one' hd hρq hq2 1
  rw [pow_one]
  linear_combination -h

theorem caseA (hsq : Squarefree N) (hodd : Odd N) {d : ℕ} (hd : Odd d)
    {ρ₁ ρ₂ : ZMod N} (hu₁ : IsUnit ρ₁) (hu₂ : IsUnit ρ₂) (hρ₂ : ρ₂ ^ d = 1)
    (h2c : ∀ χ : DirichletCharacter ℂ N, χ.IsPrimitive → ∑ x, cc d ρ₁ ρ₂ x * χ x = 0)
    (T R : Finset ℕ) (hTR : T ∪ R = N.primeFactors) (hdisj : Disjoint T R) (hne : T.Nonempty)
    (t : ℕ → ZMod N) (ht : ∀ p ∈ T, GoodMult p (t p))
    (hinv₁ : ∀ p ∈ T, ∀ x, ind d ρ₁ (t p * x) = ind d ρ₁ x)
    (hinv₂ : ∀ p ∈ T, ∀ x, ind d ρ₂ (t p * x) = ind d ρ₂ x)
    (horthR : ∀ q ∈ R, ∀ χ : DirichletCharacter ℂ N, χ.conductor ∣ N / q →
      ∑ x, cc d ρ₁ ρ₂ x * χ x = 0) :
    ff d ρ₁ ρ₂ (-ρ₂) = 0 := by
  have hT : T ⊆ N.primeFactors := hTR ▸ Finset.subset_union_left
  refine lemma3full hsq T R hTR hdisj hne t ht (ff d ρ₁ ρ₂) ?_ ?_ ?_ (-ρ₂) ?_
  · intro p hp x; simp only [ff, hinv₁ p hp, hinv₂ p hp]
  · intro x hx
    apply ff_eq_zero_of_not_unit hu₁ hu₂
    intro hu; exact hx (fun q hq ↦ cast_ne_zero_of_isUnit (hT hq) hu)
  · intro χ hχ
    simp only [← cc_eq]
    by_cases hprim : χ.IsPrimitive
    · exact h2c χ hprim
    · obtain ⟨q, hq, hqc⟩ := exists_not_dvd_conductor hsq χ hprim
      have hqR : q ∈ R := by
        rw [← hTR, Finset.mem_union] at hq
        rcases hq with hq | hq
        · exact absurd (hχ q hq) hqc
        · exact hq
      exact horthR q hqR χ (conductor_dvd_div hq hqc)
  · intro q hq
    exact neg_sub_one_cast_ne_zero hodd hd hρ₂ (hTR ▸ Finset.mem_union_right T hq)


/-! ## Case: `R = {p}` (the correction term) -/

noncomputable def LcN (p d : ℕ) (ρ : ZMod N) (zb : ZMod (N / p)) : ℕ :=
  ∑ u ∈ range d, if (ZMod.cast ρ : ZMod (N / p)) ^ u = zb ∧ (ZMod.cast ρ : ZMod p) ^ u = 1
    then 1 else 0

lemma Lc_eq_LcN (p d : ℕ) (ρ : ZMod N) (zb : ZMod (N / p)) : Lc p d ρ zb = (LcN p d ρ zb : ℂ) := by
  simp only [Lc, LcN]; push_cast; rfl

lemma LcN_le_one {p d : ℕ} {ρ : ZMod N} (hσ : orderOf (ZMod.cast ρ : ZMod (N / p)) = d)
    (zb : ZMod (N / p)) : LcN p d ρ zb ≤ 1 := by
  classical
  unfold LcN
  rw [Finset.sum_boole]
  apply Finset.card_le_one.2
  intro a ha b hb
  simp only [Finset.mem_filter, Finset.mem_range] at ha hb
  apply pow_injOn_Iio_orderOf (x := (ZMod.cast ρ : ZMod (N / p)))
  · rw [hσ]; exact ha.1
  · rw [hσ]; exact hb.1
  · simp only; rw [ha.2.1, hb.2.1]

lemma isUnit_cast_of_isUnit {n : ℕ} (hn : n ∣ N) {ρ : ZMod N} (hu : IsUnit ρ) :
    IsUnit (ZMod.cast ρ : ZMod n) := by
  have := hu.map (ZMod.castHom hn (ZMod n))
  simpa using this

lemma Lc_eq_zero_of_not_unit {p d : ℕ} (hpN : p ∣ N) {ρ : ZMod N} (hu : IsUnit ρ)
    {zb : ZMod (N / p)} (hz : ¬ IsUnit zb) : Lc p d ρ zb = 0 := by
  simp only [Lc]
  refine Finset.sum_eq_zero fun u _ ↦ ?_
  rw [if_neg]
  rintro ⟨h, -⟩
  apply hz
  rw [← h]
  exact (isUnit_cast_of_isUnit (Nat.div_dvd_of_dvd hpN) hu).pow u

lemma Lc_mul_pow {p : ℕ} (hp : p ∈ N.primeFactors) {ρ : ZMod N} {d : ℕ} (hd : 0 < d)
    (hσ : orderOf (ZMod.cast ρ : ZMod (N / p)) = d) (hρ : ρ ^ d = 1) {j : ℕ}
    (hj : (ZMod.cast ρ : ZMod p) ^ j = 1) (z : ZMod (N / p)) :
    Lc p d ρ ((ZMod.cast ρ : ZMod (N / p)) ^ j * z) = Lc p d ρ z := by
  have hpN := Nat.dvd_of_mem_primeFactors hp
  simp only [Lc]
  set σ : ZMod (N / p) := ZMod.cast ρ with hσdef
  set τ : ZMod p := ZMod.cast ρ with hτdef
  have hτ : τ ^ d = 1 := by rw [hτdef, ← ZMod.cast_pow hpN, hρ, ZMod.cast_one hpN]
  have hσu : IsUnit σ := (isOfFinOrder_iff_pow_eq_one.2 ⟨d, hd, by rw [← hσ, pow_orderOf_eq_one]⟩).isUnit
  conv_lhs => rw [← sum_range_add_mod (d := d) j]
  refine Finset.sum_congr rfl fun u _ ↦ ?_
  rw [pow_mod_ord hσ, pow_mod_of_pow_eq_one hτ, pow_add, pow_add, hj, mul_one]
  have h1 : (σ ^ u * σ ^ j = σ ^ j * z) ↔ (σ ^ u = z) := by
    rw [mul_comm (σ ^ u)]; exact (hσu.pow j).mul_right_inj
  simp only [h1]


theorem caseB (hsq : Squarefree N) (hodd : Odd N) {d : ℕ} (hd : Odd d)
    {ρ₁ ρ₂ : ZMod N} (hu₁ : IsUnit ρ₁) (hu₂ : IsUnit ρ₂) (hρ₁ : ρ₁ ^ d = 1) (hρ₂ : ρ₂ ^ d = 1)
    (h2c : ∀ χ : DirichletCharacter ℂ N, χ.IsPrimitive → ∑ x, cc d ρ₁ ρ₂ x * χ x = 0)
    (T : Finset ℕ) {p : ℕ} (hTR : T ∪ {p} = N.primeFactors) (hdisj : Disjoint T {p})
    (hne : T.Nonempty) (t : ℕ → ZMod N) (ht : ∀ q ∈ T, GoodMult q (t q))
    (hinv₁ : ∀ q ∈ T, ∀ x, ind d ρ₁ (t q * x) = ind d ρ₁ x)
    (hinv₂ : ∀ q ∈ T, ∀ x, ind d ρ₂ (t q * x) = ind d ρ₂ x)
    (htpow : ∀ q ∈ T, ∃ j₁ j₂ : ℕ, t q = ρ₁ ^ j₁ ∧ t q = ρ₂ ^ j₂)
    [NeZero (N / p)]
    (hσ₁ : orderOf (ZMod.cast ρ₁ : ZMod (N / p)) = d) (hσ₂ : orderOf (ZMod.cast ρ₂ : ZMod (N / p)) = d)
    (hind : ∀ z, ind d (ZMod.cast ρ₂ : ZMod (N / p)) z = ind d (ZMod.cast ρ₁ : ZMod (N / p)) z) :
    ff d ρ₁ ρ₂ (-ρ₂) = 0 := by
  classical
  have hp : p ∈ N.primeFactors := hTR ▸ Finset.mem_union_right T (Finset.mem_singleton_self p)
  have hT : T ⊆ N.primeFactors := hTR ▸ Finset.subset_union_left
  have hpN := Nat.dvd_of_mem_primeFactors hp
  have hdN : N / p ∣ N := Nat.div_dvd_of_dvd hpN
  have hp2 := prime_gt_two hodd hp
  have hqp : ∀ q ∈ T, q ≠ p := fun q hq h ↦
    Finset.disjoint_left.1 hdisj hq (by rw [h]; exact Finset.mem_singleton_self p)
  have hp1 : ((p : ℂ) - 1) ≠ 0 := by
    rw [sub_ne_zero]; exact_mod_cast (by omega : p ≠ 1)
  set Λ : ZMod (N / p) → ℂ := fun z ↦ Lc p d ρ₂ z - Lc p d ρ₁ z with hΛ
  set lam : ZMod N → ℂ := fun y ↦ Λ (ZMod.cast y : ZMod (N / p)) / ((p : ℂ) - 1) with hlam
  set A : ZMod N → ℂ := fun y ↦ ff d ρ₁ ρ₂ y - lam y with hA
  have hlamper : ∀ (k y : ZMod N),
      (ZMod.cast (k + nn N p * y) : ZMod (N / p)) = ZMod.cast k := by
    intro k y
    rw [ZMod.cast_add hdN, ZMod.cast_mul hdN, nn, ZMod.cast_natCast hdN, ZMod.natCast_self,
      zero_mul, add_zero]
  have key := lemma3full hsq T {p} hTR hdisj hne t ht A ?_ ?_ ?_ (-ρ₂) ?_
  · -- integrality
    simp only [hA, hlam, hΛ, sub_eq_zero] at key
    rw [ff, ind_eq_indN, ind_eq_indN, Lc_eq_LcN, Lc_eq_LcN, eq_div_iff hp1] at key
    have hl₁ := LcN_le_one hσ₁ (ZMod.cast (-ρ₂) : ZMod (N / p))
    have hl₂ := LcN_le_one hσ₂ (ZMod.cast (-ρ₂) : ZMod (N / p))
    have hz : ((indN d ρ₁ (-ρ₂) : ℤ) - indN d ρ₂ (-ρ₂)) * ((p : ℤ) - 1)
        = (LcN p d ρ₂ (ZMod.cast (-ρ₂)) : ℤ) - LcN p d ρ₁ (ZMod.cast (-ρ₂)) := by
      exact_mod_cast key
    have hz2 : (indN d ρ₁ (-ρ₂) : ℤ) - indN d ρ₂ (-ρ₂) = 0 := by
      have hp3 : (2 : ℤ) ≤ (p : ℤ) - 1 := by omega
      rcases lt_trichotomy ((indN d ρ₁ (-ρ₂) : ℤ) - indN d ρ₂ (-ρ₂)) 0 with h | h | h
      · nlinarith
      · exact h
      · nlinarith
    rw [ff, ind_eq_indN, ind_eq_indN, sub_eq_zero]
    exact_mod_cast (sub_eq_zero.1 hz2)
  · -- invariance
    intro q hq x
    simp only [hA, hlam, hΛ, ff, hinv₁ q hq, hinv₂ q hq]
    obtain ⟨j₁, j₂, h₁, h₂⟩ := htpow q hq
    have hcp : (ZMod.cast (t q) : ZMod p) = 1 :=
      cast_goodMult (ht q hq) (hT hq) hp (hqp q hq).symm
    have e₁ : (ZMod.cast ρ₁ : ZMod p) ^ j₁ = 1 := by
      rw [← ZMod.cast_pow hpN, ← h₁, hcp]
    have e₂ : (ZMod.cast ρ₂ : ZMod p) ^ j₂ = 1 := by
      rw [← ZMod.cast_pow hpN, ← h₂, hcp]
    have c₁ : (ZMod.cast (t q * x) : ZMod (N / p)) = (ZMod.cast ρ₁ : ZMod (N / p)) ^ j₁ * ZMod.cast x := by
      rw [ZMod.cast_mul hdN, h₁, ZMod.cast_pow hdN]
    have c₂ : (ZMod.cast (t q * x) : ZMod (N / p)) = (ZMod.cast ρ₂ : ZMod (N / p)) ^ j₂ * ZMod.cast x := by
      rw [ZMod.cast_mul hdN, h₂, ZMod.cast_pow hdN]
    have hL₁ : Lc p d ρ₁ (ZMod.cast (t q * x)) = Lc p d ρ₁ (ZMod.cast x) := by
      rw [c₁, Lc_mul_pow hp hd.pos hσ₁ hρ₁ e₁]
    have hL₂ : Lc p d ρ₂ (ZMod.cast (t q * x)) = Lc p d ρ₂ (ZMod.cast x) := by
      rw [c₂, Lc_mul_pow hp hd.pos hσ₂ hρ₂ e₂]
    rw [hL₁, hL₂]
  · -- support
    intro x hx
    have hxu : ¬ IsUnit x := fun hu ↦ hx (fun q hq ↦ cast_ne_zero_of_isUnit (hT hq) hu)
    simp only [hA, hlam, hΛ, ff_eq_zero_of_not_unit hu₁ hu₂ d hxu, zero_sub, neg_eq_zero,
      div_eq_zero_iff, hp1, or_false]
    have hzb : ¬ IsUnit (ZMod.cast x : ZMod (N / p)) := by
      intro hzu
      apply hx
      intro q hq
      have hqn : q ∣ N / p := dvd_div_of_ne (hT hq) hp (hqp q hq)
      have hq' : q ∈ (N / p).primeFactors := Nat.mem_primeFactors.2
        ⟨Nat.prime_of_mem_primeFactors (hT hq), hqn, NeZero.ne _⟩
      have := cast_ne_zero_of_isUnit hq' hzu
      rwa [cast_cast_eq hqn hdN] at this
    rw [Lc_eq_zero_of_not_unit hpN hu₂ hzb, Lc_eq_zero_of_not_unit hpN hu₁ hzb, sub_zero]
  · -- orthogonality
    intro χ hχ
    by_cases hpc : p ∣ χ.conductor
    · have hprim : χ.IsPrimitive := by
        rw [DirichletCharacter.isPrimitive_def]
        apply pf_dvd_of_all hsq χ.conductor_dvd_level
        intro q hq
        rw [← hTR, Finset.mem_union, Finset.mem_singleton] at hq
        rcases hq with hq | rfl
        · exact hχ q hq
        · exact hpc
      have hsplit : ∀ x, (A (x + 1) + A (1 - x)) * χ x =
          cc d ρ₁ ρ₂ x * χ x - (lam (x + 1) + lam (1 - x)) * χ x := by
        intro x; simp only [hA, cc_eq]; ring
      simp only [hsplit, Finset.sum_sub_distrib, h2c χ hprim, zero_sub, neg_eq_zero]
      refine orth_of_periodic hsq hp (fun x ↦ lam (x + 1) + lam (1 - x)) ?_ χ hpc
      intro k y
      simp only [hlam]
      rw [show k + nn N p * y + 1 = (k + 1) + nn N p * y by ring,
        show 1 - (k + nn N p * y) = (1 - k) + nn N p * (-y) by ring, hlamper, hlamper]
    · have hcd := conductor_dvd_div hp hpc
      rw [sum_eq_sum_uind]
      have := orth_of_fibre hp (fun y ↦ uind y * (A (y + 1) + A (1 - y)))
        (fun y hy ↦ by simp [uind, hy]) ?_ χ hcd
      · simpa using this
      intro xb hxb
      have hFS : ∀ zb : ZMod (N / p), IsUnit zb → ∑ y ∈ fib p zb, uind y * A (y + 1) = 0 := by
        intro zb hzb
        simp only [hA, mul_sub, Finset.sum_sub_distrib]
        rw [fibre_ff hp hp2 hd hρ₁ hρ₂ hind hzb]
        have hl : ∀ y ∈ fib p zb, uind y * lam (y + 1) = uind y * (Λ (zb + 1) / ((p : ℂ) - 1)) := by
          intro y hy
          simp only [fib, Finset.mem_filter, Finset.mem_univ, true_and] at hy
          simp only [hlam]
          rw [ZMod.cast_add hdN, ZMod.cast_one hdN, hy]
        rw [Finset.sum_congr rfl hl, ← Finset.sum_mul, sum_uind_fib hsq hp hzb]
        simp only [hΛ]
        rw [Nat.cast_sub (by omega : 1 ≤ p), Nat.cast_one]
        field_simp
        ring
      rw [fibre_sym _ xb hpN, hFS xb hxb, hFS (-xb) hxb.neg, add_zero]
  · intro q hq
    rw [Finset.mem_singleton] at hq
    subst hq
    exact neg_sub_one_cast_ne_zero hodd hd hρ₂ hp


/-! ## Case: two primes, `T = ∅` -/

lemma e_add_e_neg_ne_zero (hodd : Odd N) (k : ZMod N) : e k + e (-k) ≠ 0 := by
  intro h
  have h1 : e k * e k = -1 := by
    have : e k * (e k + e (-k)) = 0 := by rw [h, mul_zero]
    rw [mul_add, ← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul, add_neg_cancel,
      AddChar.map_zero_eq_one] at this
    rw [← AddChar.map_add_eq_mul]; linear_combination this
  have h2 : e (4 * k) = 1 := by
    rw [show 4 * k = (k + k) + (k + k) by ring, AddChar.map_add_eq_mul, AddChar.map_add_eq_mul, h1]
    norm_num
  rw [e_eq_one_iff] at h2
  have h4 : IsUnit (4 : ZMod N) := by
    have := (ZMod.isUnit_iff_coprime 4 N).2 ((Nat.coprime_two_left.2 hodd).pow_left 2)
    simpa using this
  have hk : k = 0 := (h4.mul_right_eq_zero).1 h2
  rw [hk, neg_zero, AddChar.map_zero_eq_one] at h
  norm_num at h

/-- If `ρ` has order `d` modulo `q` and `q ∣ x`, then `ind d ρ (x + 1)` only sees `x = 0`. -/
lemma ind_add_one_of_dvd {ρ : ZMod N} {d : ℕ} (hd : Odd d) {q : ℕ} (hq : q ∈ N.primeFactors)
    (hq2 : 2 < q) (hoq : orderOf (ZMod.cast ρ : ZMod q) = d) {x : ZMod N}
    (hx : (ZMod.cast x : ZMod q) = 0) :
    ind d ρ (x + 1) = ∑ u ∈ range d, if u = 0 ∧ x = 0 then 1 else 0 := by
  have hqN := Nat.dvd_of_mem_primeFactors hq
  have hρq : (ZMod.cast ρ : ZMod q) ^ d = 1 := by rw [← hoq, pow_orderOf_eq_one]
  simp only [ind]
  refine Finset.sum_congr rfl fun u hu ↦ ?_
  rw [Finset.mem_range] at hu
  have hneg : ¬ (-ρ ^ u = x + 1) := by
    intro h
    have := congrArg (fun y : ZMod N ↦ (ZMod.cast y : ZMod q)) h
    simp only [ZMod.cast_neg hqN, ZMod.cast_pow hqN, ZMod.cast_add hqN, hx, ZMod.cast_one hqN,
      zero_add] at this
    exact pow_ne_neg_one' hd hρq hq2 u (by rw [← neg_neg ((ZMod.cast ρ : ZMod q) ^ u), this])
  rw [if_neg hneg, add_zero]
  by_cases hpos : ρ ^ u = x + 1
  · have := congrArg (fun y : ZMod N ↦ (ZMod.cast y : ZMod q)) hpos
    simp only [ZMod.cast_pow hqN, ZMod.cast_add hqN, hx, ZMod.cast_one hqN, zero_add] at this
    have hdu : d ∣ u := hoq ▸ orderOf_dvd_of_pow_eq_one this
    have hu0 : u = 0 := Nat.eq_zero_of_dvd_of_lt hdu hu
    subst hu0
    rw [pow_zero] at hpos
    have hx0 : x = 0 := by linear_combination -hpos
    simp [hx0]
  · rw [if_neg hpos, if_neg]
    rintro ⟨rfl, rfl⟩
    exact hpos (by simp)

theorem caseC (hsq : Squarefree N) (hodd : Odd N) {d : ℕ} (hd : Odd d)
    {ρ₁ ρ₂ : ZMod N} (hu₁ : IsUnit ρ₁) (hu₂ : IsUnit ρ₂)
    (horth : ∀ χ : DirichletCharacter ℂ N, ∑ x, cc d ρ₁ ρ₂ x * χ x = 0)
    (hoq : ∀ q ∈ N.primeFactors, orderOf (ZMod.cast ρ₁ : ZMod q) = d ∧
      orderOf (ZMod.cast ρ₂ : ZMod q) = d) :
    ff d ρ₁ ρ₂ = 0 := by
  obtain ⟨F, -, hFu⟩ := char_decomp ∅ (Finset.empty_subset _) (cc d ρ₁ ρ₂)
    (fun χ _ ↦ horth χ)
  have hffnu : ∀ x, ¬ IsUnit x → ff d ρ₁ ρ₂ (x + 1) = 0 := by
    intro x hx
    have : ∃ q ∈ N.primeFactors, (ZMod.cast x : ZMod q) = 0 := by
      by_contra h; push_neg at h; exact hx (isUnit_of_cast_ne_zero h)
    obtain ⟨q, hq, hxq⟩ := this
    rw [ff, ind_add_one_of_dvd hd hq (prime_gt_two hodd hq) (hoq q hq).1 hxq,
      ind_add_one_of_dvd hd hq (prime_gt_two hodd hq) (hoq q hq).2 hxq, sub_self]
  have hcc : ∀ x, cc d ρ₁ ρ₂ x = 0 := by
    intro x
    by_cases hx : IsUnit x
    · rw [hFu x hx, Finset.sum_empty]
    · rw [cc_eq, hffnu x hx, show (1 : ZMod N) - x = -x + 1 by ring,
        hffnu (-x) (fun h ↦ hx (by simpa using h.neg)), add_zero]
  have hG : GoodPrimes N ∅ := fun p hp ↦ absurd hp (Finset.notMem_empty p)
  refine eq_zero_of_dft_cop hG _ (fun x hx ↦ absurd (fun p hp ↦ absurd hp
    (Finset.notMem_empty p)) hx) fun k _ ↦ ?_
  have h1 : ∑ x, cc d ρ₁ ρ₂ x * e (k * x) = (e (-k) + e k) * fc (ff d ρ₁ ρ₂) k := by
    simp only [cc, add_mul, Finset.sum_add_distrib, fc_shift_add, fc_shift_sub]
  simp only [hcc, zero_mul, Finset.sum_const_zero] at h1
  have h2 := e_add_e_neg_ne_zero hodd k
  rw [add_comm] at h2
  have := (mul_eq_zero.1 h1.symm).resolve_left h2
  simpa [fc] using this

/-! ## The prime case -/

theorem prime_case (hp : N.Prime) {ρ₁ ρ₂ : ZMod N} {d : ℕ} (hd : 0 < d) (ho₁ : orderOf ρ₁ = d)
    (hρ₂ : ρ₂ ^ d = 1) : ∃ c : ℕ, ρ₁ ^ c = ρ₂ := by
  classical
  haveI : Fact N.Prime := ⟨hp⟩
  set S := (range d).image (fun u ↦ ρ₁ ^ u) with hS
  have hsub : S ⊆ Polynomial.nthRootsFinset d (1 : ZMod N) := by
    intro y hy
    obtain ⟨u, -, rfl⟩ := Finset.mem_image.1 hy
    rw [Polynomial.mem_nthRootsFinset hd, ← pow_mul, mul_comm, pow_mul, ← ho₁,
      pow_orderOf_eq_one, one_pow]
  have hinj : Set.InjOn (fun u ↦ ρ₁ ^ u) ↑(range d) := by
    intro u hu v hv h
    simp only [Finset.coe_range] at hu hv
    exact pow_injOn_Iio_orderOf (by rw [ho₁]; exact hu) (by rw [ho₁]; exact hv) h
  have hcard : (Polynomial.nthRootsFinset d (1 : ZMod N)).card ≤ S.card := by
    rw [hS, Finset.card_image_of_injOn hinj, Finset.card_range]
    exact card_nthRootsFinset_le d 1
  have hSeq := Finset.eq_of_subset_of_card_le hsub hcard
  have hmem : ρ₂ ∈ Polynomial.nthRootsFinset d (1 : ZMod N) :=
    (Polynomial.mem_nthRootsFinset hd 1).2 hρ₂
  rw [← hSeq] at hmem
  obtain ⟨u, -, hu⟩ := Finset.mem_image.1 hmem
  exact ⟨u, hu⟩


/-! ## The composite step -/

lemma two_le_card_pf (hsq : Squarefree N) (hN1 : N ≠ 1) (hNp : ¬ N.Prime) :
    2 ≤ N.primeFactors.card := by
  by_contra h
  push_neg at h
  have hprod := Nat.prod_primeFactors_of_squarefree hsq
  rcases Nat.lt_succ_iff.1 h |>.lt_or_eq with h0 | h1
  · rw [Nat.lt_one_iff, Finset.card_eq_zero] at h0
    rw [h0, Finset.prod_empty] at hprod
    exact hN1 hprod.symm
  · obtain ⟨p, hp⟩ := Finset.card_eq_one.1 h1
    rw [hp, Finset.prod_singleton] at hprod
    have : p ∈ N.primeFactors := by rw [hp]; exact Finset.mem_singleton_self p
    exact hNp (hprod ▸ Nat.prime_of_mem_primeFactors this)

lemma cast_pow_down {q k : ℕ} (hqk : q ∣ N / k) (hkN : N / k ∣ N) {ρ₁ ρ₂ : ZMod N} {c : ℕ}
    (hc : (ZMod.cast ρ₁ : ZMod (N / k)) ^ c = ZMod.cast ρ₂) :
    (ZMod.cast ρ₁ : ZMod q) ^ c = ZMod.cast ρ₂ := by
  have := congrArg (fun y : ZMod (N / k) ↦ (ZMod.cast y : ZMod q)) hc
  simp only [ZMod.cast_pow hqk] at this
  rwa [cast_cast_eq hqk hkN, cast_cast_eq hqk hkN] at this

theorem step (hsq : Squarefree N) (hN2 : 2 < N) (hodd : Odd N) (hNp : ¬ N.Prime) {d : ℕ}
    (hd : Odd d) (hd1 : 1 < d) {r₁ r₂ : ℤ} (ho₁ : orderOf (r₁ : ZMod N) = d)
    (ho₂ : orderOf (r₂ : ZMod N) = d) (h : Hyp N d r₁ r₂)
    (IH : ∀ q ∈ N.primeFactors, orderOf (r₁ : ZMod (N / q)) = d → orderOf (r₂ : ZMod (N / q)) = d →
      ∃ c : ℕ, (r₁ : ZMod (N / q)) ^ c = r₂) :
    ∃ c : ℕ, (r₁ : ZMod N) ^ c = r₂ := by
  classical
  set ρ₁ : ZMod N := ((r₁ : ℤ) : ZMod N) with hρ₁def
  set ρ₂ : ZMod N := ((r₂ : ℤ) : ZMod N) with hρ₂def
  have hρ₁ : ρ₁ ^ d = 1 := by rw [← ho₁, pow_orderOf_eq_one]
  have hρ₂ : ρ₂ ^ d = 1 := by rw [← ho₂, pow_orderOf_eq_one]
  have hu₁ : IsUnit ρ₁ := (isOfFinOrder_iff_pow_eq_one.2 ⟨d, hd.pos, hρ₁⟩).isUnit
  have hu₂ : IsUnit ρ₂ := (isOfFinOrder_iff_pow_eq_one.2 ⟨d, hd.pos, hρ₂⟩).isUnit
  have h2c : ∀ χ : DirichletCharacter ℂ N, χ.IsPrimitive → ∑ x, cc d ρ₁ ρ₂ x * χ x = 0 :=
    fun χ hχ ↦ lemma2c hd h hN2 ho₁ ho₂ χ hχ
  have hNeZ : ∀ q ∈ N.primeFactors, NeZero (N / q) := fun q hq ↦
    ⟨(Nat.div_pos (Nat.le_of_dvd (by omega) (Nat.dvd_of_mem_primeFactors hq))
      (Nat.prime_of_mem_primeFactors hq).pos).ne'⟩
  have hcastI : ∀ q ∈ N.primeFactors, ∀ r : ℤ, (r : ZMod (N / q)) = ZMod.cast (r : ZMod N) :=
    fun q hq r ↦ (ZMod.cast_intCast (Nat.div_dvd_of_dvd (Nat.dvd_of_mem_primeFactors hq)) r).symm
  have he : ∀ q ∈ N.primeFactors, orderOf (ZMod.cast ρ₂ : ZMod (N / q)) =
      orderOf (ZMod.cast ρ₁ : ZMod (N / q)) := fun q hq ↦
    (orderOf_cast_eq hsq hN2 hNp hodd hd h ho₁ ho₂ hq).symm
  have hdvd : ∀ q ∈ N.primeFactors, orderOf (ZMod.cast ρ₁ : ZMod (N / q)) ∣ d := by
    intro q hq
    apply orderOf_dvd_of_pow_eq_one
    have hdN := Nat.div_dvd_of_dvd (Nat.dvd_of_mem_primeFactors hq)
    rw [← ZMod.cast_pow hdN, hρ₁, ZMod.cast_one hdN]
  set T := N.primeFactors.filter (fun q ↦ orderOf (ZMod.cast ρ₁ : ZMod (N / q)) < d) with hT
  set R := N.primeFactors.filter (fun q ↦ ¬ orderOf (ZMod.cast ρ₁ : ZMod (N / q)) < d) with hR
  have hTR : T ∪ R = N.primeFactors := Finset.filter_union_filter_not_eq _ _
  have hdisj : Disjoint T R := Finset.disjoint_filter_filter_not _ _ _
  have hRsub : R ⊆ N.primeFactors := Finset.filter_subset _ _
  have hRord : ∀ q ∈ R, orderOf (ZMod.cast ρ₁ : ZMod (N / q)) = d ∧
      orderOf (ZMod.cast ρ₂ : ZMod (N / q)) = d := by
    intro q hq
    rw [hR, Finset.mem_filter] at hq
    have h1 : orderOf (ZMod.cast ρ₁ : ZMod (N / q)) = d :=
      le_antisymm (Nat.le_of_dvd hd.pos (hdvd q hq.1)) (not_lt.1 hq.2)
    exact ⟨h1, (he q hq.1).trans h1⟩
  have hIH : ∀ q ∈ R, ∃ c : ℕ, (ZMod.cast ρ₁ : ZMod (N / q)) ^ c = ZMod.cast ρ₂ := by
    intro q hq
    have hq' := hRsub hq
    obtain ⟨c, hc⟩ := IH q hq' (by rw [hcastI q hq']; exact (hRord q hq).1)
      (by rw [hcastI q hq']; exact (hRord q hq).2)
    exact ⟨c, by rw [← hcastI q hq', ← hcastI q hq']; exact hc⟩
  have hind : ∀ q ∈ R, ∀ z, ind d (ZMod.cast ρ₂ : ZMod (N / q)) z =
      ind d (ZMod.cast ρ₁ : ZMod (N / q)) z := by
    intro q hq z
    haveI := hNeZ q (hRsub hq)
    obtain ⟨c, hc⟩ := hIH q hq
    exact ind_eq_of_pow hd.pos (hRord q hq).1 (hRord q hq).2 hc z
  have hLc : ∀ q ∈ R, (∃ k ∈ R, k ≠ q) → ∀ z, Lc q d ρ₂ z = Lc q d ρ₁ z := by
    intro q hq ⟨k, hk, hkq⟩ z
    have hq' := hRsub hq
    have hk' := hRsub hk
    obtain ⟨c, hc⟩ := hIH k hk
    have hcop : Nat.Coprime c d := by
      apply coprime_of_orderOf_pow hd.pos (hRord k hk).1
      rw [hc]; exact (hRord k hk).2
    have hqk : q ∣ N / k := dvd_div_of_ne hq' hk' hkq.symm
    have hkN := Nat.div_dvd_of_dvd (Nat.dvd_of_mem_primeFactors hk')
    have hcq : (ZMod.cast ρ₁ : ZMod q) ^ c = ZMod.cast ρ₂ := cast_pow_down hqk hkN hc
    have hqN := Nat.dvd_of_mem_primeFactors hq'
    have hρq : (ZMod.cast ρ₁ : ZMod q) ^ d = 1 := by
      rw [← ZMod.cast_pow hqN, hρ₁, ZMod.cast_one hqN]
    have hop : orderOf (ZMod.cast ρ₁ : ZMod q) = orderOf (ZMod.cast ρ₂ : ZMod q) := by
      rw [← hcq, orderOf_pow_of_coprime' hρq hcop]
    obtain ⟨c', hc'⟩ := hIH q hq
    exact Lc_eq_of_pow hq' hd.pos (hRord q hq).1 (hRord q hq).2 hc' hρ₁ hop z
  have horthR : ∀ q ∈ R, (∃ k ∈ R, k ≠ q) → ∀ χ : DirichletCharacter ℂ N,
      χ.conductor ∣ N / q → ∑ x, cc d ρ₁ ρ₂ x * χ x = 0 := by
    intro q hq hk χ hχ
    haveI := hNeZ q (hRsub hq)
    exact orth_cc_fibre (hRsub hq) (prime_gt_two hodd (hRsub hq)) hd hρ₁ hρ₂ (hind q hq)
      (hLc q hq hk) χ hχ
  have hff : ff d ρ₁ ρ₂ (-ρ₂) = 0 := by
    by_cases hTe : T = ∅
    · have hReq : R = N.primeFactors := by rw [← hTR, hTe, Finset.empty_union]
      have hcard := two_le_card_pf hsq (by omega) hNp
      by_cases h3 : 3 ≤ N.primeFactors.card
      · -- Lemma 4
        obtain ⟨K, hK⟩ := lemma4 hsq hd.pos ho₁ (fun a ha b hb ↦ by
          have hc1 := Finset.pred_card_le_card_erase (s := N.primeFactors) (a := a)
          have hc2 := Finset.pred_card_le_card_erase (s := N.primeFactors.erase a) (a := b)
          have hpos : 0 < ((N.primeFactors.erase a).erase b).card := by omega
          obtain ⟨j, hj⟩ := Finset.card_pos.1 hpos
          have hjb : j ≠ b := Finset.ne_of_mem_erase hj
          have hj' := Finset.mem_of_mem_erase hj
          have hja : j ≠ a := Finset.ne_of_mem_erase hj'
          have hjpf := Finset.mem_of_mem_erase hj'
          obtain ⟨c, hc⟩ := hIH j (hReq ▸ hjpf)
          have hjN := Nat.div_dvd_of_dvd (Nat.dvd_of_mem_primeFactors hjpf)
          exact ⟨c, cast_pow_down (dvd_div_of_ne ha hjpf hja.symm) hjN hc,
            cast_pow_down (dvd_div_of_ne hb hjpf hjb.symm) hjN hc⟩)
        rw [ff, ind_eq_of_pow hd.pos ho₁ ho₂ hK, sub_self]
      · -- two primes
        have h2 : N.primeFactors.card = 2 := by omega
        obtain ⟨a, b, hab, hpf⟩ := Finset.card_eq_two.1 h2
        have hother : ∀ q ∈ R, ∃ k ∈ R, k ≠ q := by
          intro q hq
          rw [hReq, hpf] at hq ⊢
          rcases Finset.mem_insert.1 hq with rfl | hq
          · exact ⟨b, by simp, hab.symm⟩
          · rw [Finset.mem_singleton] at hq; subst hq
            exact ⟨a, by simp, hab⟩
        have horth : ∀ χ : DirichletCharacter ℂ N, ∑ x, cc d ρ₁ ρ₂ x * χ x = 0 := by
          intro χ
          by_cases hprim : χ.IsPrimitive
          · exact h2c χ hprim
          · obtain ⟨q, hq, hqc⟩ := exists_not_dvd_conductor hsq χ hprim
            rw [← hReq] at hq
            exact horthR q hq (hother q hq) χ (conductor_dvd_div (hRsub hq) hqc)
        have hNab : N = a * b := by
          rw [← Nat.prod_primeFactors_of_squarefree hsq, hpf, Finset.prod_pair hab]
        have hoq : ∀ q ∈ N.primeFactors, orderOf (ZMod.cast ρ₁ : ZMod q) = d ∧
            orderOf (ZMod.cast ρ₂ : ZMod q) = d := by
          intro q hq
          rw [hpf] at hq
          have ha : a ∈ R := by rw [hReq, hpf]; simp
          have hb : b ∈ R := by rw [hReq, hpf]; simp
          have hapos : 0 < a := Nat.pos_of_ne_zero (by rintro rfl; simp at hNab; omega)
          have hbpos : 0 < b := Nat.pos_of_ne_zero (by rintro rfl; simp at hNab; omega)
          rcases Finset.mem_insert.1 hq with rfl | hq
          · have hNb : N / b = q := by rw [hNab, Nat.mul_div_cancel _ hbpos]
            have := hRord b hb
            rw [hNb] at this
            exact this
          · rw [Finset.mem_singleton] at hq; subst hq
            have hNa : N / a = q := by rw [hNab, Nat.mul_div_cancel_left _ hapos]
            have := hRord a ha
            rw [hNa] at this
            exact this
        rw [caseC hsq hodd hd hu₁ hu₂ horth hoq]
        rfl
    · obtain ⟨q₀, hq₀⟩ := Finset.nonempty_iff_ne_empty.2 hTe
      have hTsub : T ⊆ N.primeFactors := Finset.filter_subset _ _
      have hkern : ∀ q ∈ T, (∃ j, ρ₂ ^ j = ρ₁ ^ orderOf (ZMod.cast ρ₁ : ZMod (N / q))) ∧
          GoodMult q (ρ₁ ^ orderOf (ZMod.cast ρ₁ : ZMod (N / q))) := by
        intro q hq
        have hq' := hTsub hq
        rw [hT, Finset.mem_filter] at hq
        exact common_kernel_elt hsq hd ho₁ ho₂ hu₁ hq' (he q hq').symm hq.2
      set t : ℕ → ZMod N := fun q ↦ ρ₁ ^ orderOf (ZMod.cast ρ₁ : ZMod (N / q)) with htdef
      have ht : ∀ q ∈ T, GoodMult q (t q) := fun q hq ↦ (hkern q hq).2
      have hinv₁ : ∀ q ∈ T, ∀ x, ind d ρ₁ (t q * x) = ind d ρ₁ x :=
        fun q _ x ↦ ind_mul_pow ho₁ hu₁ _ x
      have hinv₂ : ∀ q ∈ T, ∀ x, ind d ρ₂ (t q * x) = ind d ρ₂ x := by
        intro q hq x
        obtain ⟨j, hj⟩ := (hkern q hq).1
        simp only [htdef]
        rw [← hj]; exact ind_mul_pow ho₂ hu₂ j x
      by_cases hR2 : ∀ q ∈ R, ∃ k ∈ R, k ≠ q
      · exact caseA hsq hodd hd hu₁ hu₂ hρ₂ h2c T R hTR hdisj ⟨q₀, hq₀⟩ t ht hinv₁ hinv₂
          (fun q hq ↦ horthR q hq (hR2 q hq))
      · push_neg at hR2
        obtain ⟨p, hp, hpk⟩ := hR2
        have hReq : R = {p} := by
          ext k; rw [Finset.mem_singleton]
          exact ⟨fun hk ↦ by_contra fun h ↦ absurd (hpk k hk) h, fun h ↦ h ▸ hp⟩
        rw [hReq] at hTR hdisj
        haveI := hNeZ p (hRsub hp)
        refine caseB hsq hodd hd hu₁ hu₂ hρ₁ hρ₂ h2c T hTR hdisj ⟨q₀, hq₀⟩ t ht hinv₁ hinv₂
          ?_ (hRord p hp).1 (hRord p hp).2 (hind p hp)
        intro q hq
        obtain ⟨j, hj⟩ := (hkern q hq).1
        exact ⟨_, j, rfl, hj.symm⟩
  exact conclude hd hd1 ho₁ ho₂ hN2 hff


end TwoPrimes

/-! ## The induction on squarefree moduli -/

namespace TwoPrimes

lemma zmod_two_unit {x : ZMod 2} (hx : IsUnit x) : x = 1 := by
  have h0 : x ≠ 0 := hx.ne_zero
  fin_cases x
  · exact absurd rfl h0
  · rfl

lemma odd_of_gcd {N : ℕ} [NeZero N] {d : ℕ} (hd : 0 < d) {r : ℤ} (ho : orderOf (r : ZMod N) = d)
    (hg : Int.gcd (r - 1) N = 1) : Odd N := by
  rw [← Nat.not_even_iff_odd, even_iff_two_dvd]
  rintro ⟨k, hk⟩
  have hu : IsUnit (r : ZMod N) :=
    (isOfFinOrder_iff_pow_eq_one.2 ⟨d, hd, by rw [← ho, pow_orderOf_eq_one]⟩).isUnit
  have c1 : IsCoprime ((N : ℕ) : ℤ) r := (ZMod.coe_int_isUnit_iff_isCoprime r N).1 hu
  have c2 : IsCoprime ((N : ℕ) : ℤ) (r - 1) := (Int.isCoprime_iff_gcd_eq_one.2 hg).symm
  have hN : ((N : ℕ) : ℤ) = ((2 : ℕ) : ℤ) * (k : ℤ) := by rw [hk]; push_cast; ring
  rw [hN] at c1 c2
  have d1 : IsUnit (r : ZMod 2) := (ZMod.coe_int_isUnit_iff_isCoprime r 2).2 c1.of_mul_left_left
  have d2 : IsUnit (((r - 1 : ℤ)) : ZMod 2) :=
    (ZMod.coe_int_isUnit_iff_isCoprime _ 2).2 c2.of_mul_left_left
  have e1 := zmod_two_unit d1
  have e2 := zmod_two_unit d2
  rw [Int.cast_sub, e1, Int.cast_one, sub_self] at e2
  exact zero_ne_one e2

theorem core : ∀ N : ℕ, Squarefree N → 0 < N → ∀ {d : ℕ}, Odd d → ∀ {r₁ r₂ : ℤ},
    orderOf (r₁ : ZMod N) = d → orderOf (r₂ : ZMod N) = d → Int.gcd (r₁ - 1) N = 1 →
    Hyp N d r₁ r₂ → ∃ c : ℕ, (r₁ : ZMod N) ^ c = r₂ := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro hsq hN0 d hd r₁ r₂ ho₁ ho₂ hg h
    haveI : NeZero N := ⟨hN0.ne'⟩
    by_cases hN1 : N = 1
    · subst hN1; exact ⟨0, Subsingleton.elim _ _⟩
    by_cases hd1 : d = 1
    · subst hd1
      refine ⟨0, ?_⟩
      rw [pow_zero, orderOf_eq_one_iff.1 ho₂]
    have hd1' : 1 < d := by have := hd.pos; omega
    have hodd : Odd N := odd_of_gcd hd.pos ho₁ hg
    have hN2 : 2 < N := by
      have : N ≠ 2 := by rintro rfl; exact absurd hodd (by decide)
      omega
    by_cases hNp : N.Prime
    · exact prime_case hNp hd.pos ho₁ (by rw [← ho₂, pow_orderOf_eq_one])
    refine step hsq hN2 hodd hNp hd hd1' ho₁ ho₂ h ?_
    intro q hq hq₁ hq₂
    have hqN := Nat.dvd_of_mem_primeFactors hq
    have hqp := Nat.prime_of_mem_primeFactors hq
    have hlt : N / q < N := Nat.div_lt_self hN0 hqp.one_lt
    have hpos : 0 < N / q := Nat.div_pos (Nat.le_of_dvd hN0 hqN) hqp.pos
    have hdN : N / q ∣ N := Nat.div_dvd_of_dvd hqN
    refine ih (N / q) hlt (hsq.squarefree_of_dvd hdN) hpos hd hq₁ hq₂ ?_ (h.descend hdN hN0)
    have h1 := Int.isCoprime_iff_gcd_eq_one.2 hg
    rw [← Int.isCoprime_iff_gcd_eq_one]
    have hN : ((N : ℕ) : ℤ) = ((N / q : ℕ) : ℤ) * (q : ℤ) := by
      rw [← Nat.cast_mul, Nat.div_mul_cancel hqN]
    rw [hN] at h1
    exact h1.of_mul_right_left

/-! ## Reduction to the radical -/

lemma unipotent_torsion {m m₀ d : ℕ} [NeZero m] (hm₀ : m₀ ∣ m) (hrad : m ∣ m₀ ^ m)
    (hcop : Nat.Coprime m d) {w : ZMod m} (hw : (ZMod.cast w : ZMod m₀) = 1) (hwd : w ^ d = 1) :
    w = 1 := by
  set y := w - 1 with hy
  have hy0 : (ZMod.cast y : ZMod m₀) = 0 := by
    rw [hy, ZMod.cast_sub hm₀, hw, ZMod.cast_one hm₀, sub_self]
  rw [cast_eq_zero_iff_dvd_val] at hy0
  obtain ⟨z, hz⟩ := hy0
  have hyz : y = (m₀ : ZMod m) * (z : ZMod m) := by
    rw [← Nat.cast_mul, ← hz, ZMod.natCast_zmod_val]
  have hnil : IsNilpotent y := by
    refine ⟨m, ?_⟩
    rw [hyz, mul_pow, ← Nat.cast_pow, (ZMod.natCast_eq_zero_iff _ _).2 hrad, zero_mul]
  have hw' : w = 1 + y := by rw [hy]; ring
  -- geometric sums
  have hgeom : (∑ i ∈ range d, w ^ i) * y = 0 := by
    rw [hy, geom_sum_mul, hwd, sub_self]
  have hS : ∃ Q, ∑ i ∈ range d, w ^ i = (d : ZMod m) + y * Q := by
    refine ⟨∑ i ∈ range d, ∑ j ∈ range i, w ^ j, ?_⟩
    rw [Finset.mul_sum]
    have : ∀ i, w ^ i = 1 + y * ∑ j ∈ range i, w ^ j := by
      intro i
      rw [mul_comm, hy, geom_sum_mul]; ring
    rw [Finset.sum_congr rfl (fun i _ ↦ this i), Finset.sum_add_distrib, Finset.sum_const,
      Finset.card_range, nsmul_eq_mul, mul_one]
  obtain ⟨Q, hQ⟩ := hS
  have hdu : IsUnit (d : ZMod m) := (ZMod.isUnit_iff_coprime d m).2 hcop.symm
  have hunit : IsUnit (∑ i ∈ range d, w ^ i) := by
    rw [hQ]
    exact ((Commute.all y Q).isNilpotent_mul_right hnil).isUnit_add_left_of_commute hdu
      (Commute.all _ _)
  have : y = 0 := by
    have := congrArg (fun t ↦ (hunit.unit⁻¹ : (ZMod m)ˣ).1 * t) hgeom
    simpa [← mul_assoc] using this
  rw [hw', this, add_zero]

end TwoPrimes

open TwoPrimes Complex Real in
/-- **MathOverflow 503314.** -/
theorem TwoPrimes.mo503314 (m d : ℕ) (hm : 0 < m) (hd : Odd d) (hmd : Nat.Coprime m d) (r₁ r₂ : ℤ)
    (ho₁ : orderOf (r₁ : ZMod m) = d) (ho₂ : orderOf (r₂ : ZMod m) = d)
    (hg₁ : Int.gcd (r₁ - 1) m = 1) (hg₂ : Int.gcd (r₂ - 1) m = 1)
    (hstar : ∀ k : ℤ,
      (∏ u ∈ Finset.Icc 1 (d - 1),
        (cexp (2 * π * I * k / m) - cexp (2 * π * I * (k * r₁ ^ u) / m)) *
        (cexp (2 * π * I * k / m) - cexp (2 * π * I * (-(k * r₁ ^ u)) / m))) =
      ∏ u ∈ Finset.Icc 1 (d - 1),
        (cexp (2 * π * I * k / m) - cexp (2 * π * I * (k * r₂ ^ u) / m)) *
        (cexp (2 * π * I * k / m) - cexp (2 * π * I * (-(k * r₂ ^ u)) / m))) :
    ∃ c : ℕ, (r₁ : ZMod m) ^ c = (r₂ : ZMod m) := by
  haveI : NeZero m := ⟨hm.ne'⟩
  set m₀ := UniqueFactorizationMonoid.radical m with hm₀
  have hm₀d : m₀ ∣ m := UniqueFactorizationMonoid.radical_dvd_self
  have hm₀sq : Squarefree m₀ := UniqueFactorizationMonoid.squarefree_radical
  have hm₀pos : 0 < m₀ := Nat.radical_pos m
  haveI : NeZero m₀ := ⟨hm₀pos.ne'⟩
  have hrad : m ∣ m₀ ^ m := Nat.dvd_radical_pow_self hm.ne'
  have hρ₁ : (r₁ : ZMod m) ^ d = 1 := by rw [← ho₁, pow_orderOf_eq_one]
  have hρ₂ : (r₂ : ZMod m) ^ d = 1 := by rw [← ho₂, pow_orderOf_eq_one]
  have hcast : ∀ r : ℤ, (r : ZMod m₀) = ZMod.cast (r : ZMod m) :=
    fun r ↦ (ZMod.cast_intCast hm₀d r).symm
  -- orders are preserved
  have hord : ∀ r : ℤ, orderOf (r : ZMod m) = d → orderOf (r : ZMod m₀) = d := by
    intro r ho
    have hρ : (r : ZMod m) ^ d = 1 := by rw [← ho, pow_orderOf_eq_one]
    have h1 : (r : ZMod m₀) ^ d = 1 := by
      rw [hcast, ← ZMod.cast_pow hm₀d, hρ, ZMod.cast_one hm₀d]
    apply le_antisymm (Nat.le_of_dvd hd.pos (orderOf_dvd_of_pow_eq_one h1))
    have h2 : (r : ZMod m) ^ orderOf (r : ZMod m₀) = 1 := by
      apply unipotent_torsion hm₀d hrad hmd
      · rw [ZMod.cast_pow hm₀d, ← hcast, pow_orderOf_eq_one]
      · rw [← pow_mul, mul_comm, pow_mul, hρ, one_pow]
    rw [← ho]
    exact Nat.le_of_dvd (isOfFinOrder_iff_pow_eq_one.2 ⟨d, hd.pos, h1⟩).orderOf_pos
      (orderOf_dvd_of_pow_eq_one h2)
  have hg₀ : Int.gcd (r₁ - 1) m₀ = 1 := by
    have h1 := Int.isCoprime_iff_gcd_eq_one.2 hg₁
    rw [← Int.isCoprime_iff_gcd_eq_one]
    obtain ⟨k, hk⟩ := hm₀d
    have hN : ((m : ℕ) : ℤ) = ((m₀ : ℕ) : ℤ) * (k : ℤ) := by rw [hk, Nat.cast_mul]
    rw [hN] at h1
    exact h1.of_mul_right_left
  obtain ⟨c, hc⟩ := core m₀ hm₀sq hm₀pos hd (hord r₁ ho₁) (hord r₂ ho₂) hg₀
    ((show Hyp m d r₁ r₂ from hstar).descend hm₀d hm)
  refine ⟨c, ?_⟩
  set w := (r₁ : ZMod m) ^ c * (r₂ : ZMod m) ^ (d - 1) with hw
  have hw1 : w = 1 := by
    apply unipotent_torsion hm₀d hrad hmd
    · rw [hw, ZMod.cast_mul hm₀d, ZMod.cast_pow hm₀d, ZMod.cast_pow hm₀d, ← hcast, ← hcast, hc,
        ← pow_succ', Nat.sub_add_cancel hd.pos, ← hord r₂ ho₂, pow_orderOf_eq_one]
    · rw [hw, mul_pow, ← pow_mul, mul_comm c d, pow_mul, hρ₁, one_pow, one_mul, ← pow_mul,
        mul_comm, pow_mul, hρ₂, one_pow]
  calc (r₁ : ZMod m) ^ c = (r₁ : ZMod m) ^ c * (r₂ : ZMod m) ^ d := by rw [hρ₂, mul_one]
    _ = w * (r₂ : ZMod m) := by
        rw [hw, mul_assoc, ← pow_succ, Nat.sub_add_cancel hd.pos]
    _ = (r₂ : ZMod m) := by rw [hw1, one_mul]

