/-
Copyright 2026 Ming-Chih Kao. Licensed under the Apache License, Version 2.0;
see the LICENSE file at the root of this repository.
-/
module

public import E521.Part6

/-! Part of the proof of Erdős 521 (see `E521/Part1.lean` for the port notes): sections P12–P13, F1 of the
merged Left to Solve file `proofs/erdos-521.lean`. -/

@[expose] public section

-- ===== P12 =====
section S_P12

/-! Asymptotics: `μ(H_K) ≥ (4/π)/(40 K)` eventually (original). -/

open Finset MeasureTheory Filter Topology

noncomputable section

namespace E521

/-- `n = 2K - 1 → ∞`. -/
lemma tendsto_nK : Tendsto (fun K : ℕ => ((2 * K - 1 : ℕ) : ℝ)) atTop atTop :=
  tendsto_natCast_atTop_atTop.comp
    (tendsto_atTop_atTop_of_monotone (fun a b h => by omega) (fun b => ⟨b + 1, by omega⟩))

lemma lamK_ge (K : ℕ) : ((2 * K - 1 : ℕ) : ℝ) ^ ((39 : ℝ) / 80) ≤ lamK K := Nat.le_ceil _

lemma lamK_le (K : ℕ) : (lamK K : ℝ) ≤ ((2 * K - 1 : ℕ) : ℝ) ^ ((39 : ℝ) / 80) + 1 :=
  (Nat.ceil_lt_add_one (by positivity)).le

lemma tK_ge (K : ℕ) : ((2 * K - 1 : ℕ) : ℝ) ^ ((19 : ℝ) / 20) ≤ (tK K : ℝ) + 1 :=
  (Nat.lt_floor_add_one _).le

lemma tK_le' (K : ℕ) : (tK K : ℝ) ≤ ((2 * K - 1 : ℕ) : ℝ) ^ ((19 : ℝ) / 20) :=
  Nat.floor_le (by positivity)

/-- the numerical heart: `2 (c+θ)(1+θ)(21/20)/c' ≤ 0.95` with `c = √3/(2π)`, `θ = 1/200`, `c' = 63/100`. -/
lemma key_const : 2 * (√3 / (2 * Real.pi) + 1 / 200) * (1 + 1 / 200) * (21 / 20) / (63 / 100) ≤ 95 / 100 := by
  have hs : √3 ≤ 17321 / 10000 := by
    rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have hpi : (3141 / 1000 : ℝ) < Real.pi := by have := Real.pi_gt_d4; linarith
  have hp0 := Real.pi_pos
  have : √3 / (2 * Real.pi) ≤ (17321 / 10000) / (2 * (3141 / 1000)) := by
    apply div_le_div₀ (by norm_num) hs (by norm_num) (by linarith)
  have hc : (17321 / 10000 : ℝ) / (2 * (3141 / 1000)) ≤ 2758 / 10000 := by norm_num
  nlinarith

end E521

namespace E521

/-- `K · E₁ → 0` (endpoint term). -/
lemma E1_small : Tendsto (fun K : ℕ => (K : ℝ) * (4 * √24 * (lamK K : ℝ) ^ 2 / (K + 1) ^ 2)) atTop (𝓝 0) := by
  -- ≤ 32√24 n^{-1/40}
  have hlim : Tendsto (fun K : ℕ => 32 * √24 * ((2 * K - 1 : ℕ) : ℝ) ^ (-(1 / 40 : ℝ))) atTop (𝓝 0) := by
    have := ((tendsto_rpow_neg_atTop (show (0:ℝ) < 1/40 by norm_num)).comp tendsto_nK).const_mul (32 * √24)
    simpa using this
  refine squeeze_zero' (Eventually.of_forall (fun K => by positivity)) ?_ hlim
  filter_upwards [eventually_ge_atTop 1] with K hK
  set n : ℝ := ((2 * K - 1 : ℕ) : ℝ) with hn
  have hn1 : (1 : ℝ) ≤ n := by rw [hn]; exact_mod_cast (by omega : 1 ≤ 2 * K - 1)
  have hnK : n = 2 * K - 1 := by rw [hn]; push_cast [Nat.cast_sub (by omega : 1 ≤ 2 * K)]; ring
  have hlam := lamK_le K
  have hq : (1 : ℝ) ≤ n ^ ((39 : ℝ) / 80) := Real.one_le_rpow hn1 (by norm_num)
  have hl2 : (lamK K : ℝ) ^ 2 ≤ 4 * n ^ ((39 : ℝ) / 40) := by
    have : (lamK K : ℝ) ≤ 2 * n ^ ((39 : ℝ) / 80) := by linarith
    have h0 : (0 : ℝ) ≤ lamK K := by positivity
    have := pow_le_pow_left₀ h0 this 2
    rw [mul_pow, ← Real.rpow_natCast (n ^ ((39 : ℝ) / 80)) 2, ← Real.rpow_mul (by linarith)] at this
    norm_num at this ⊢; linarith
  have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast hK
  -- K/(K+1)^2 ≤ 1/K ≤ 2/n... use K ≥ (n+1)/2
  have : (K : ℝ) * (4 * √24 * (lamK K : ℝ) ^ 2 / (K + 1) ^ 2) ≤ 4 * √24 * (lamK K : ℝ) ^ 2 / K := by
    rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity)]
    have h0 : (0 : ℝ) ≤ 4 * √24 * (lamK K : ℝ) ^ 2 := by positivity
    nlinarith [mul_nonneg h0 (sq_nonneg (K : ℝ))]
  refine this.trans ?_
  have hKn : (K : ℝ) ≥ n / 2 := by rw [hnK]; linarith
  have e : n ^ (-(1 / 40 : ℝ)) = n ^ ((39 : ℝ) / 40) / n := by
    rw [show (-(1 / 40 : ℝ)) = (39 : ℝ) / 40 - 1 by norm_num, Real.rpow_sub (by linarith), Real.rpow_one]
  rw [e]
  have hn0 : (0 : ℝ) < n := by linarith
  have h24 : (0 : ℝ) ≤ √24 := Real.sqrt_nonneg _
  calc 4 * √24 * (lamK K : ℝ) ^ 2 / K ≤ 4 * √24 * (4 * n ^ ((39 : ℝ) / 40)) / (n / 2) := by
        apply div_le_div₀ (by positivity) (by gcongr) (by positivity) hKn
    _ = 32 * √24 * (n ^ ((39 : ℝ) / 40) / n) := by field_simp; ring

end E521

namespace E521

/-- `K · E₂ → 0` (tail term). -/
lemma E2_small : Tendsto (fun K : ℕ => (K : ℝ) * (2 * ((tK K + 1) *
    (2 * Real.exp (-((2 * (lamK K : ℝ) - 1) ^ 2 / (2 * tK K))))))) atTop (𝓝 0) := by
  have hlim : Tendsto (fun K : ℕ => 8 * (((2 * K - 1 : ℕ) : ℝ) ^ (2 : ℝ) *
      Real.exp (-(1 / 2) * ((2 * K - 1 : ℕ) : ℝ) ^ ((1 : ℝ) / 40)))) atTop (𝓝 0) := by
    have := (((tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (2 * 40) (1 / 2) (by norm_num)).comp
      ((tendsto_rpow_atTop (show (0:ℝ) < 1 / 40 by norm_num)).comp tendsto_nK)).const_mul 8)
    rw [mul_zero] at this
    refine this.congr' (Eventually.of_forall (fun K => ?_))
    simp only [Function.comp]
    rw [← Real.rpow_mul (by positivity)]; norm_num
  refine squeeze_zero' (Eventually.of_forall (fun K => by positivity)) ?_ hlim
  filter_upwards [eventually_ge_atTop 1] with K hK
  set n : ℝ := ((2 * K - 1 : ℕ) : ℝ) with hn
  have hn1 : (1 : ℝ) ≤ n := by rw [hn]; exact_mod_cast (by omega : 1 ≤ 2 * K - 1)
  have hnK : n = 2 * K - 1 := by rw [hn]; push_cast [Nat.cast_sub (by omega : 1 ≤ 2 * K)]; ring
  have hlam := lamK_ge K
  have ht := tK_le' K
  have hq : (1 : ℝ) ≤ n ^ ((39 : ℝ) / 80) := Real.one_le_rpow hn1 (by norm_num)
  have hlam1 : (1 : ℝ) ≤ lamK K := by rw [← hn] at hlam; linarith
  -- exponent
  have hexp : -((2 * (lamK K : ℝ) - 1) ^ 2 / (2 * tK K)) ≤ -(1 / 2) * n ^ ((1 : ℝ) / 40) := by
    have h1t : 1 ≤ tK K := by
      unfold tK; apply Nat.le_floor; push_cast; exact Real.one_le_rpow hn1 (by norm_num)
    have htp : (0 : ℝ) < tK K := by exact_mod_cast h1t
    have h1 : n ^ ((39 : ℝ) / 40) ≤ (2 * (lamK K : ℝ) - 1) ^ 2 := by
      have : n ^ ((39 : ℝ) / 80) ≤ 2 * (lamK K : ℝ) - 1 := by rw [← hn] at hlam; linarith
      have := pow_le_pow_left₀ (by positivity) this 2
      rw [← Real.rpow_natCast (n ^ ((39 : ℝ) / 80)) 2, ← Real.rpow_mul (by linarith)] at this
      norm_num at this; exact this
    have h2 : n ^ ((1 : ℝ) / 40) * n ^ ((19 : ℝ) / 20) = n ^ ((39 : ℝ) / 40) := by
      rw [← Real.rpow_add (by linarith)]; norm_num
    rw [← hn] at ht
    have hx0 := Real.rpow_nonneg (show (0:ℝ) ≤ n by linarith) ((1 : ℝ) / 40)
    have hm := mul_le_mul_of_nonneg_left ht hx0
    have hq2 : (1 / 2) * n ^ ((1 : ℝ) / 40) ≤ (2 * (lamK K : ℝ) - 1) ^ 2 / (2 * tK K) := by
      rw [le_div_iff₀ (by positivity)]
      nlinarith
    linarith
  have hK1 : (K : ℝ) ≤ n := by
    rw [hnK]
    have : (1 : ℝ) ≤ K := by exact_mod_cast hK
    linarith
  have ht1 : (tK K : ℝ) + 1 ≤ 2 * n := by
    have := Real.rpow_le_self_of_one_le hn1 (show (19 : ℝ) / 20 ≤ 1 by norm_num)
    rw [← hn] at ht; linarith
  have hn2 : n ^ (2 : ℝ) = n ^ 2 := Real.rpow_natCast n 2 ▸ by norm_num
  rw [hn2]
  have hE := Real.exp_le_exp.mpr hexp
  have hE0 := Real.exp_pos (-((2 * (lamK K : ℝ) - 1) ^ 2 / (2 * tK K)))
  calc (K : ℝ) * (2 * ((tK K + 1) * (2 * Real.exp (-((2 * (lamK K : ℝ) - 1) ^ 2 / (2 * tK K))))))
      = 4 * (K * (tK K + 1)) * Real.exp (-((2 * (lamK K : ℝ) - 1) ^ 2 / (2 * tK K))) := by ring
    _ ≤ 4 * (n * (2 * n)) * Real.exp (-(1 / 2) * n ^ ((1 : ℝ) / 40)) := by
        (gcongr)
    _ = 8 * (n ^ 2 * Real.exp (-(1 / 2) * n ^ ((1 : ℝ) / 40))) := by ring

end E521

namespace E521

lemma sqrt_bound {x : ℝ} (hx : 2400 ≤ x) : √(1 + 24 / x) ≤ 1 + 1 / 200 := by
  rw [Real.sqrt_le_left (by norm_num)]
  have h : 24 / x ≤ 1 / 100 := by rw [div_le_iff₀ (by linarith)]; linarith
  norm_num
  linarith

lemma ub_step {A x y : ℝ} (hA : 0 ≤ A) (hx : 0 < x) (hy : 0 < y) (h : y ≤ 2 * x) : A / x ≤ (2 * A) / y := by
  rw [div_le_div_iff₀ hx hy]
  have := mul_le_mul_of_nonneg_left h hA
  linarith

lemma tK_half : ∀ᶠ K : ℕ in atTop, (tK K : ℝ) ≤ ((2 * K - 1 : ℕ) : ℝ) / 2 := by
  have h20 := ((tendsto_rpow_atTop (show (0:ℝ) < 1 / 20 by norm_num)).comp tendsto_nK).eventually_ge_atTop 2
  filter_upwards [h20, eventually_ge_atTop 1] with K hK2 hK1
  simp only [Function.comp] at hK2
  have hn1 : (1 : ℝ) ≤ ((2 * K - 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ 2 * K - 1)
  have e : ((2 * K - 1 : ℕ) : ℝ) = ((2 * K - 1 : ℕ) : ℝ) ^ ((19 : ℝ) / 20) * ((2 * K - 1 : ℕ) : ℝ) ^ ((1 : ℝ) / 20) := by
    rw [← Real.rpow_add (by linarith)]; norm_num
  have := tK_le' K
  have hpos : (0 : ℝ) ≤ ((2 * K - 1 : ℕ) : ℝ) ^ ((19 : ℝ) / 20) := by positivity
  have hm := mul_le_mul_of_nonneg_left hK2 hpos
  linarith

end E521

namespace E521

set_option maxHeartbeats 1000000 in
/-- the count term. -/
lemma E3_bound : ∀ᶠ K : ℕ in atTop, (K : ℝ) * ((2 / AK K) * ∑ k ∈ range (pK K),
    ((N2 (LK K k) 0 0 : ℝ) / 4 ^ (LK K k)) * R522.PP (R522.SCev (k + 2))) ≤ (4 / Real.pi) * (96 / 100) := by
  set θ : ℝ := 1 / 200 with hθ
  set a : ℝ := √3 / (2 * Real.pi) + θ with ha
  set b : ℝ := (8 / Real.pi) * (1 + θ) with hb
  have hpi := Real.pi_pos
  have ha0 : 0 ≤ a := by rw [ha, hθ]; positivity
  have hb0 : 0 ≤ b := by rw [hb, hθ]; positivity
  obtain ⟨n1, hn1⟩ := eventually_atTop.mp (R522.pk_bound (θ := θ) (by rw [hθ]; norm_num))
  -- t → ∞ and log n → ∞
  have ht : Tendsto (fun K : ℕ => (tK K : ℝ)) atTop atTop := by
    have h := (tendsto_rpow_atTop (show (0:ℝ) < 19 / 20 by norm_num)).comp tendsto_nK
    refine tendsto_atTop_mono' atTop (Eventually.of_forall (fun K => ?_)) (h.atTop_add (tendsto_const_nhds (x := (-1 : ℝ))))
    simp only [Function.comp]; have := tK_ge K; linarith
  have hlog : Tendsto (fun K : ℕ => Real.log ((2 * K - 1 : ℕ) : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_nK
  have hinvlog := hlog.inv_tendsto_atTop
  set C : ℝ := (2 * a * b + 2 * n1 * b) / (63 / 100) with hC
  have hsmall := (hinvlog.const_mul C).eventually (gt_mem_nhds (show C * 0 < (4 / Real.pi) / 100 by
    rw [mul_zero]; positivity))
  have hhalf := tK_half
  filter_upwards [ht.eventually_ge_atTop (4800 + n1), hlog.eventually_gt_atTop 1, hsmall,
    eventually_ge_atTop (2 * n1 + 2), hhalf] with K htK hlK hsK hK hhK
  set n := 2 * K - 1 with hn
  set t := tK K with htdef
  set p := pK K with hpdef
  have hnr : ((n : ℕ) : ℝ) = 2 * K - 1 := by rw [hn]; push_cast [Nat.cast_sub (by omega : 1 ≤ 2 * K)]; ring
  have htn : t ≤ n := tK_le K (by omega)
  have ht2 : (t : ℝ) ≤ n / 2 := hhK
  have hpn : p = n - t := rfl
  have ht1 : 4800 + n1 ≤ t := by exact_mod_cast htK
  have hp_lt : p < n := by omega
  have hn1p : n1 ≤ p := by
    have : (n : ℝ) / 2 ≤ (p : ℝ) := by
      rw [hpn, Nat.cast_sub htn]; linarith
    have : (n1 : ℝ) ≤ n / 2 := by
      rw [hnr]
      have : ((2 * n1 + 2 : ℕ) : ℝ) ≤ K := by exact_mod_cast hK
      push_cast at this; linarith
    exact_mod_cast (by linarith : (n1 : ℝ) ≤ p)
  -- the u-bound
  have huk : ∀ k < p, (N2 (LK K k) 0 0 : ℝ) / 4 ^ (LK K k) ≤ b / ((n : ℝ) - k) := by
    intro k hk
    have hL2 : n - k ≤ 2 * (LK K k + 1) := by unfold LK; omega
    have hL3 : 2400 ≤ LK K k + 1 := by unfold LK; omega
    have hu := u_upper (LK K k)
    have hnk : (0 : ℝ) < (n : ℝ) - k := by
      have : (k : ℝ) < n := by exact_mod_cast (by omega : k < n)
      linarith
    have hL1 : (2400 : ℝ) ≤ (LK K k : ℝ) + 1 := by exact_mod_cast hL3
    have hsq : √(1 + 24 / ((LK K k : ℝ) + 1)) ≤ 1 + θ := by
      rw [hθ]; exact sqrt_bound hL1
    have hL4 : (n : ℝ) - k ≤ 2 * ((LK K k : ℝ) + 1) := by
      have : ((n - k : ℕ) : ℝ) ≤ ((2 * (LK K k + 1) : ℕ) : ℝ) := by exact_mod_cast hL2
      push_cast [Nat.cast_sub (by omega : k ≤ n)] at this; linarith
    calc (N2 (LK K k) 0 0 : ℝ) / 4 ^ (LK K k) ≤ (4 / Real.pi) / ((LK K k : ℝ) + 1) * √(1 + 24 / ((LK K k : ℝ) + 1)) := hu
      _ ≤ (4 / Real.pi) / ((LK K k : ℝ) + 1) * (1 + θ) := mul_le_mul_of_nonneg_left hsq (by positivity)
      _ ≤ (8 / Real.pi) / ((n : ℝ) - k) * (1 + θ) := by
          apply mul_le_mul_of_nonneg_right _ (by rw [hθ]; norm_num)
          have hst := ub_step (A := 4 / Real.pi) (by positivity) (by positivity) hnk hL4
          rw [show (8 : ℝ) / Real.pi = 2 * (4 / Real.pi) by ring]
          exact hst
      _ = b / ((n : ℝ) - k) := by rw [hb]; ring
  have hcs := E521Q.count_sum (n := n) (p := p) (n0 := n1) ha0 hb0 hp_lt hn1p
    (fun k => R522.PP (R522.SCev (k + 2))) (fun k => (N2 (LK K k) 0 0 : ℝ) / 4 ^ (LK K k))
    (fun k => R522.PP_nonneg _) (fun k => R522.PP_le_one _)
    (fun k hk => by
      have := hn1 (k + 2) (by omega)
      push_cast at this; exact this)
    (fun k => by positivity) huk
  -- logarithms
  have hlogn := hlK
  have hlp : Real.log ((p : ℝ) + 1) ≤ Real.log n + 1 := by
    have hp1 : (p : ℝ) + 1 ≤ n := by exact_mod_cast (by omega : p + 1 ≤ n)
    have := Real.log_le_log (by positivity) hp1
    linarith
  have hlt : (19 / 20) * Real.log n ≤ Real.log ((n : ℝ) - p + 1) := by
    have e : (n : ℝ) - p + 1 = (t : ℝ) + 1 := by rw [hpn, Nat.cast_sub htn]; ring
    rw [e]
    have := tK_ge K
    rw [← hn] at this
    have hn1' : (0 : ℝ) < n := by
      rw [hnr]
      have : (2 : ℝ) ≤ K := by exact_mod_cast (by omega : 2 ≤ K)
      linarith
    calc (19 / 20) * Real.log n = Real.log ((n : ℝ) ^ ((19 : ℝ) / 20)) := by
          rw [Real.log_rpow hn1']
      _ ≤ Real.log ((t : ℝ) + 1) := Real.log_le_log (Real.rpow_pos_of_pos hn1' _) this
  set L := Real.log ((n : ℕ) : ℝ) with hL
  have hA : AK K = (63 / 100) * L := rfl
  have hL0 : 0 < L := by linarith
  have hKn1 : (K : ℝ) ≤ (n : ℝ) - n1 := by
    rw [hnr]; have : ((2 * n1 + 2 : ℕ) : ℝ) ≤ K := by exact_mod_cast hK
    push_cast at this; linarith
  have hKn2 : 2 * (K : ℝ) ≤ (n : ℝ) + 2 := by rw [hnr]; linarith
  have hnn1 : (0 : ℝ) < (n : ℝ) - n1 := by
    have : (1 : ℝ) ≤ K := by exact_mod_cast (by omega : 1 ≤ K)
    linarith
  rw [hA]
  have key := key_const
  have hLne : L ≠ 0 := hL0.ne'
  have hnn1ne : (n : ℝ) - n1 ≠ 0 := hnn1.ne'
  have hn2ne : (n : ℝ) + 2 ≠ 0 := by positivity
  have hpine : Real.pi ≠ 0 := hpi.ne'
  -- assemble
  have hbr : Real.log ((p : ℝ) + 1) + (Real.log n - Real.log ((n : ℝ) - p + 1)) + 1 ≤ (21 / 20) * L + 2 := by
    rw [hL]; linarith
  have hpart1 : (K : ℝ) * (2 / ((63 / 100) * L)) * (n1 * (b / ((n : ℝ) - n1))) ≤ (2 * n1 * b / (63 / 100)) * L⁻¹ := by
    rw [show (K : ℝ) * (2 / ((63 / 100) * L)) * (n1 * (b / ((n : ℝ) - n1))) =
      (2 * n1 * b / (63 / 100)) * L⁻¹ * (K / ((n : ℝ) - n1)) by field_simp]
    have : (K : ℝ) / ((n : ℝ) - n1) ≤ 1 := by rw [div_le_one hnn1]; exact hKn1
    have h0 : 0 ≤ (2 * n1 * b / (63 / 100)) * L⁻¹ :=
      mul_nonneg (div_nonneg (mul_nonneg (by positivity) hb0) (by norm_num)) (inv_nonneg.mpr hL0.le)
    calc (2 * n1 * b / (63 / 100)) * L⁻¹ * (K / ((n : ℝ) - n1)) ≤ (2 * n1 * b / (63 / 100)) * L⁻¹ * 1 :=
          mul_le_mul_of_nonneg_left this h0
      _ = (2 * n1 * b / (63 / 100)) * L⁻¹ := mul_one _
  have hpart2 : (K : ℝ) * (2 / ((63 / 100) * L)) * (a * b * ((Real.log ((p : ℝ) + 1) +
      (Real.log n - Real.log ((n : ℝ) - p + 1)) + 1) / ((n : ℝ) + 2))) ≤
      (a * b / (63 / 100)) * (21 / 20) + (2 * a * b / (63 / 100)) * L⁻¹ := by
    have hn2 : (0 : ℝ) < (n : ℝ) + 2 := by positivity
    have hab : 0 ≤ a * b := mul_nonneg ha0 hb0
    have step : (K : ℝ) * (2 / ((63 / 100) * L)) * (a * b * ((Real.log ((p : ℝ) + 1) +
        (Real.log n - Real.log ((n : ℝ) - p + 1)) + 1) / ((n : ℝ) + 2))) ≤
        (2 * K / ((n : ℝ) + 2)) * ((a * b / (63 / 100)) * (((21 / 20) * L + 2) / L)) := by
      rw [show (K : ℝ) * (2 / ((63 / 100) * L)) * (a * b * ((Real.log ((p : ℝ) + 1) +
        (Real.log n - Real.log ((n : ℝ) - p + 1)) + 1) / ((n : ℝ) + 2))) =
        (2 * K / ((n : ℝ) + 2)) * ((a * b / (63 / 100)) * ((Real.log ((p : ℝ) + 1) +
        (Real.log n - Real.log ((n : ℝ) - p + 1)) + 1) / L)) by field_simp]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply mul_le_mul_of_nonneg_left _ (div_nonneg hab (by norm_num))
      exact div_le_div_of_nonneg_right hbr hL0.le
    refine step.trans ?_
    have h2K : 2 * (K : ℝ) / ((n : ℝ) + 2) ≤ 1 := by rw [div_le_one hn2]; exact hKn2
    have e2 : ((21 / 20) * L + 2) / L = 21 / 20 + 2 * L⁻¹ := by field_simp
    rw [e2]
    have h0 : 0 ≤ (a * b / (63 / 100)) * (21 / 20 + 2 * L⁻¹) :=
      mul_nonneg (div_nonneg hab (by norm_num)) (by have := inv_nonneg.mpr hL0.le; linarith)
    calc (2 * K / ((n : ℝ) + 2)) * ((a * b / (63 / 100)) * (21 / 20 + 2 * L⁻¹))
        ≤ 1 * ((a * b / (63 / 100)) * (21 / 20 + 2 * L⁻¹)) := mul_le_mul_of_nonneg_right h2K h0
      _ = _ := by ring
  have hmain : (K : ℝ) * ((2 / ((63 / 100) * L)) * ∑ k ∈ range p,
      ((N2 (LK K k) 0 0 : ℝ) / 4 ^ (LK K k)) * R522.PP (R522.SCev (k + 2))) ≤
      (a * b / (63 / 100)) * (21 / 20) + C * L⁻¹ := by
    have hcs' := mul_le_mul_of_nonneg_left hcs (show (0 : ℝ) ≤ (K : ℝ) * (2 / ((63 / 100) * L)) from
      mul_nonneg (Nat.cast_nonneg _) (div_nonneg (by norm_num) (mul_nonneg (by norm_num) hL0.le)))
    rw [← mul_assoc]
    refine hcs'.trans ?_
    rw [mul_add]
    have : C * L⁻¹ = (2 * n1 * b / (63 / 100)) * L⁻¹ + (2 * a * b / (63 / 100)) * L⁻¹ := by
      rw [hC]; ring
    linarith
  refine hmain.trans ?_
  have hab_eq : (a * b / (63 / 100)) * (21 / 20) = (4 / Real.pi) * (2 * a * (1 + θ) * (21 / 20) / (63 / 100)) := by
    rw [hb]; field_simp; ring
  rw [hab_eq]
  have hk2 : 2 * a * (1 + θ) * (21 / 20) / (63 / 100) ≤ 95 / 100 := by
    rw [ha, hθ]; exact key
  have h4p : 0 < 4 / Real.pi := by positivity
  have := mul_le_mul_of_nonneg_left hk2 h4p.le
  have hsK' : C * L⁻¹ < (4 / Real.pi) / 100 := hsK
  linarith

/-- **`μ(H_K) ≥ (4/π)/(40 K)` eventually.** -/
theorem Hev_lower : ∀ᶠ K : ℕ in atTop, (4 / Real.pi) / (60 * K) ≤ μS.real (Hev K) := by
  have h1 := E1_small.eventually (gt_mem_nhds (show (0:ℝ) < (4 / Real.pi) / 200 by positivity))
  have h2 := E2_small.eventually (gt_mem_nhds (show (0:ℝ) < (4 / Real.pi) / 200 by positivity))
  have h3 := E3_bound
  have h4 : Tendsto (fun K : ℕ => (K : ℝ) * ((4 / Real.pi) / (K + 4))) atTop (𝓝 (4 / Real.pi)) := by
    have : Tendsto (fun K : ℕ => (4 / Real.pi) * ((K : ℝ) / (K + 4))) atTop (𝓝 ((4 / Real.pi) * 1)) := by
      refine tendsto_const_nhds.mul ?_
      have := tendsto_natCast_div_add_atTop (4 : ℝ)
      exact this
    rw [mul_one] at this
    refine this.congr' (Eventually.of_forall (fun K => ?_)); ring
  have h4' := h4.eventually (lt_mem_nhds (show (4 / Real.pi) * (99 / 100) < 4 / Real.pi by
    have := Real.pi_pos; nlinarith [div_pos (show (0:ℝ) < 4 by norm_num) this]))
  have hlamev : ∀ᶠ K : ℕ in atTop, 1 ≤ lamK K := by
    filter_upwards [eventually_ge_atTop 1] with K hK
    unfold lamK; exact Nat.one_le_iff_ne_zero.mpr (by
      rw [ne_eq, Nat.ceil_eq_zero, not_le]
      have : (1 : ℝ) ≤ ((2 * K - 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ 2 * K - 1)
      positivity)
  have hAev : ∀ᶠ K : ℕ in atTop, 0 < AK K := by
    filter_upwards [eventually_ge_atTop 2] with K hK
    unfold AK; apply mul_pos (by norm_num); apply Real.log_pos
    exact_mod_cast (by omega : 1 < 2 * K - 1)
  filter_upwards [h1, h2, h3, h4', hlamev, hAev, eventually_ge_atTop 2] with K e1 e2 e3 e4 hl hA hK
  have hpn : pK K + 2 ≤ 2 * K := by
    have ht1 : 1 ≤ tK K := by
      unfold tK
      apply Nat.le_floor
      push_cast
      exact Real.one_le_rpow (by exact_mod_cast (by omega : 1 ≤ 2 * K - 1)) (by norm_num)
    unfold pK; omega
  have hdet := Hev_det K (by omega) hl hA hpn
  have hK0 : (0 : ℝ) < K := by exact_mod_cast (by omega : 0 < K)
  rw [div_le_iff₀ (by positivity)]
  have : (4 / Real.pi) / 60 ≤ (K : ℝ) * μS.real (Hev K) := by
    have := mul_le_mul_of_nonneg_left hdet hK0.le
    rw [mul_sub, mul_sub, mul_sub] at this
    have hc4 : 0 < 4 / Real.pi := by positivity
    linarith
  linarith

end E521
end

end S_P12

-- ===== Q1 =====
section S_Q1

/-! A second-moment (Kochen–Stone type) lower bound for unions (original). -/

open MeasureTheory Finset

namespace E521Q

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

/-- `(∑ μ H_m)² ≤ (∑∑ μ(H_m ∩ H_m')) · μ(⋃ H_m)` for finitely many measurable sets. -/
theorem second_moment (s : Finset ℕ) (H : ℕ → Set Ω) (hH : ∀ m, MeasurableSet (H m)) :
    (∑ m ∈ s, μ.real (H m)) ^ 2 ≤
      (∑ m ∈ s, ∑ m' ∈ s, μ.real (H m ∩ H m')) * μ.real (⋃ m ∈ s, H m) := by
  classical
  set U := ⋃ m ∈ s, H m with hU
  have hUm : MeasurableSet U := Finset.measurableSet_biUnion s (fun m _ => hH m)
  set Z : Ω → ℝ := fun ω => ∑ m ∈ s, (H m).indicator (fun _ => (1 : ℝ)) ω with hZ
  have hZi : ∀ m, Integrable ((H m).indicator (fun _ => (1 : ℝ))) μ :=
    fun m => (integrable_const 1).indicator (hH m)
  have hZint : Integrable Z μ := integrable_finsetSum s (fun m _ => hZi m)
  have hZ_eq : ∀ ω, Z ω = Z ω * U.indicator (fun _ => (1 : ℝ)) ω := by
    intro ω
    by_cases hω : ω ∈ U
    · rw [Set.indicator_of_mem hω, mul_one]
    · rw [Set.indicator_of_notMem hω, mul_zero]
      simp only [hZ]
      apply sum_eq_zero; intro m hm
      rw [Set.indicator_of_notMem]
      intro h; apply hω; rw [hU]; exact Set.mem_biUnion hm h
  have hEZ : ∫ ω, Z ω ∂μ = ∑ m ∈ s, μ.real (H m) := by
    simp only [hZ]; rw [integral_finsetSum s (fun m _ => hZi m)]
    apply sum_congr rfl; intro m _; rw [integral_indicator_const _ (hH m)]; simp
  have hZ2 : ∀ ω, Z ω ^ 2 = ∑ m ∈ s, ∑ m' ∈ s, (H m ∩ H m').indicator (fun _ => (1 : ℝ)) ω := by
    intro ω
    simp only [hZ]
    rw [sq, sum_mul_sum]
    apply sum_congr rfl; intro m _; apply sum_congr rfl; intro m' _
    by_cases h1 : ω ∈ H m <;> by_cases h2 : ω ∈ H m' <;> simp [Set.indicator, h1, h2]
  have hEZ2 : ∫ ω, Z ω ^ 2 ∂μ = ∑ m ∈ s, ∑ m' ∈ s, μ.real (H m ∩ H m') := by
    simp_rw [hZ2]
    rw [integral_finsetSum s (fun m _ => integrable_finsetSum s (fun m' _ =>
      (integrable_const 1).indicator ((hH m).inter (hH m'))))]
    apply sum_congr rfl; intro m _
    rw [integral_finsetSum s (fun m' _ => (integrable_const 1).indicator ((hH m).inter (hH m')))]
    apply sum_congr rfl; intro m' _
    rw [integral_indicator_const _ ((hH m).inter (hH m'))]; simp
  -- Cauchy–Schwarz
  have hZb : ∀ ω, |Z ω| ≤ s.card := by
    intro ω
    simp only [hZ]
    rw [abs_of_nonneg (sum_nonneg (fun m _ => Set.indicator_nonneg (fun _ _ => zero_le_one) _))]
    calc ∑ m ∈ s, (H m).indicator (fun _ => (1 : ℝ)) ω ≤ ∑ m ∈ s, (1 : ℝ) :=
          sum_le_sum (fun m _ => Set.indicator_le_self' (fun _ _ => zero_le_one) ω |>.trans (le_refl _))
      _ = s.card := by simp
  have hmemZ : MemLp Z 2 μ := by
    refine MemLp.of_bound hZint.aestronglyMeasurable (s.card : ℝ) (Filter.Eventually.of_forall
      (fun ω => by rw [Real.norm_eq_abs]; exact hZb ω))
  have hmemU : MemLp (U.indicator (fun _ => (1 : ℝ))) 2 μ :=
    (memLp_const (1 : ℝ)).indicator hUm.nullMeasurableSet
  have h2 : ENNReal.ofReal 2 = 2 := by simp
  rw [← h2] at hmemZ hmemU
  have hCS := integral_mul_le_Lp_mul_Lq_of_nonneg (p := 2) (q := 2) (μ := μ)
    (f := Z) (g := U.indicator (fun _ => (1 : ℝ)))
    Real.HolderConjugate.two_two
    (Filter.Eventually.of_forall (fun ω => sum_nonneg (fun m _ =>
      Set.indicator_nonneg (fun _ _ => zero_le_one) ω)))
    (Filter.Eventually.of_forall (fun ω => Set.indicator_nonneg (fun _ _ => zero_le_one) ω))
    hmemZ hmemU
  have hInt : ∫ ω, Z ω * U.indicator (fun _ => (1 : ℝ)) ω ∂μ = ∫ ω, Z ω ∂μ := by
    congr 1; funext ω; exact (hZ_eq ω).symm
  rw [hInt, hEZ] at hCS
  have hU2 : ∫ ω, U.indicator (fun _ => (1 : ℝ)) ω ^ (2 : ℝ) ∂μ = μ.real U := by
    rw [← integral_indicator_one hUm]
    congr 1; funext ω
    by_cases h : ω ∈ U <;> simp [Set.indicator, h]
  have hZ2' : ∫ ω, Z ω ^ (2 : ℝ) ∂μ = ∑ m ∈ s, ∑ m' ∈ s, μ.real (H m ∩ H m') := by
    rw [← hEZ2]; congr 1; funext ω; rw [Real.rpow_two]
  rw [hU2, hZ2'] at hCS
  have h0 : 0 ≤ ∑ m ∈ s, μ.real (H m) := sum_nonneg (fun m _ => measureReal_nonneg)
  have hA : 0 ≤ ∑ m ∈ s, ∑ m' ∈ s, μ.real (H m ∩ H m') :=
    sum_nonneg (fun m _ => sum_nonneg (fun m' _ => measureReal_nonneg))
  have hB : 0 ≤ μ.real U := measureReal_nonneg
  calc (∑ m ∈ s, μ.real (H m)) ^ 2
      ≤ ((∑ m ∈ s, ∑ m' ∈ s, μ.real (H m ∩ H m')) ^ (1 / (2 : ℝ)) * μ.real U ^ (1 / (2 : ℝ))) ^ 2 := by
        exact pow_le_pow_left₀ h0 hCS 2
    _ = (∑ m ∈ s, ∑ m' ∈ s, μ.real (H m ∩ H m')) * μ.real U := by
        rw [mul_pow, ← Real.rpow_natCast, ← Real.rpow_natCast (μ.real U ^ (1 / (2 : ℝ))),
          ← Real.rpow_mul hA, ← Real.rpow_mul hB]
        norm_num

end E521Q

end S_Q1

-- ===== Q3 =====
section S_Q3

/-! From second moments to a positive-probability `limsup` (original). -/

open MeasureTheory Finset Filter Topology

namespace E521Q

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

/-- If on every tail window the second-moment ratio is eventually `≥ δ`, then `μ (limsup H) ≥ δ`. -/
theorem limsup_pos (H : ℕ → Set Ω) (hH : ∀ m, MeasurableSet (H m)) {δ : ℝ} (hδ : 0 < δ)
    (hratio : ∀ N, ∃ M, N ≤ M ∧ δ * (∑ m ∈ Icc N M, ∑ m' ∈ Icc N M, μ.real (H m ∩ H m')) ≤
      (∑ m ∈ Icc N M, μ.real (H m)) ^ 2 ∧ 0 < ∑ m ∈ Icc N M, ∑ m' ∈ Icc N M, μ.real (H m ∩ H m')) :
    δ ≤ μ.real (Filter.limsup H atTop) := by
  -- each tail union has measure ≥ δ
  have htail : ∀ N, δ ≤ μ.real (⋃ m ≥ N, H m) := by
    intro N
    obtain ⟨M, hNM, h1, h2⟩ := hratio N
    have hsm := second_moment μ (Icc N M) H hH
    have hU : μ.real (⋃ m ∈ Icc N M, H m) ≤ μ.real (⋃ m ≥ N, H m) := by
      apply measureReal_mono
      · intro ω hω
        simp only [Set.mem_iUnion, mem_Icc] at hω ⊢
        obtain ⟨m, hm, h⟩ := hω; exact ⟨m, hm.1, h⟩
      · exact measure_ne_top _ _
    have : δ ≤ μ.real (⋃ m ∈ Icc N M, H m) := by
      by_contra hc; push Not at hc
      have := mul_lt_mul_of_pos_left hc h2
      nlinarith
    linarith
  -- limsup = ⋂_N ⋃_{m ≥ N}, decreasing
  rw [Filter.limsup_eq_iInf_iSup_of_nat]
  have hanti : Antitone (fun N => ⋃ m ≥ N, H m) := by
    intro a b hab ω hω
    simp only [Set.mem_iUnion] at hω ⊢
    obtain ⟨m, hm, h⟩ := hω; exact ⟨m, le_trans hab hm, h⟩
  have hmeas : ∀ N, MeasurableSet (⋃ m ≥ N, H m) := fun N =>
    MeasurableSet.iUnion (fun m => MeasurableSet.iUnion (fun _ => hH m))
  have ht := tendsto_measure_iInter_atTop (μ := μ) (fun N => (hmeas N).nullMeasurableSet) hanti
    ⟨0, measure_ne_top _ _⟩
  have e : (⋂ N, ⋃ m ≥ N, H m) = ⨅ N, ⨆ m ≥ N, H m := by
    simp [Set.iInf_eq_iInter, Set.iSup_eq_iUnion]
  rw [← e]
  have ht' : Tendsto (fun N => μ.real (⋃ m ≥ N, H m)) atTop (𝓝 (μ.real (⋂ N, ⋃ m ≥ N, H m))) :=
    (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp ht
  exact ge_of_tendsto' ht' htail

end E521Q

end S_Q3

-- ===== P13 =====
section S_P13

/-! A positive-probability `limsup` of the good events (Kochen–Stone, original). -/

open Finset MeasureTheory Filter Topology

noncomputable section

namespace E521

lemma meas_cnt (K : ℕ) : Measurable (fun ω => (cnt K ω : ℝ)) := by
  classical
  have e : (fun ω => (cnt K ω : ℝ)) = fun ω => ∑ k ∈ range (pK K),
      ((if ω ∈ Iev k then (1 : ℝ) else 0) + (if ω ∈ Ialt k then (1 : ℝ) else 0)) := by
    funext ω; unfold cnt
    rw [sum_add_distrib, Nat.cast_add, card_filter, card_filter]; push_cast; rfl
  rw [e]
  refine Finset.measurable_sum _ (fun k _ => ?_)
  exact (Measurable.ite (meas_Iev k) measurable_const measurable_const).add
    (Measurable.ite (meas_Ialt k) measurable_const measurable_const)

lemma meas_Gev (K : ℕ) : MeasurableSet (Gev K) := by
  simp only [Gev, Set.setOf_forall]
  refine MeasurableSet.iInter fun l => MeasurableSet.iInter fun _ => measurableSet_lt ?_ measurable_const
  exact (Finset.measurable_sum _ (fun i _ => measurable_eR _)).abs

lemma meas_Gev' (K : ℕ) : MeasurableSet (Gev' K) := by
  simp only [Gev', Set.setOf_forall]
  refine MeasurableSet.iInter fun l => MeasurableSet.iInter fun _ => measurableSet_lt ?_ measurable_const
  exact (Finset.measurable_sum _ (fun i _ => (measurable_eR _).const_mul _)).abs

lemma meas_Hev (K : ℕ) : MeasurableSet (Hev K) :=
  (((meas_coneE _ _ _).inter (meas_Gev K)).inter (meas_Gev' K)).inter
    (measurableSet_lt (meas_cnt K) measurable_const)

/-- harmonic upper bound. -/
lemma harm_upper (M : ℕ) : ∑ d ∈ range (M + 1), 1 / ((d : ℝ) + 1) ≤ Real.log (M + 1) + 1 := by
  rw [range_eq_Ico, ← Ico_union_Ico_eq_Ico (show 0 ≤ 1 by omega) (show 1 ≤ M + 1 by omega),
    sum_union (Ico_disjoint_Ico_consecutive _ _ _)]
  have h := E521Q.harm_Ico 1 (M + 1) le_rfl (by omega)
  simp only [Nat.Ico_succ_singleton, sum_singleton, Nat.cast_zero, zero_add, div_one, Nat.cast_one,
    Real.log_one, sub_zero] at h ⊢
  push_cast at h
  linarith

/-- the pair bound in symmetric form. -/
lemma pair_sym (m m' : ℕ) :
    μS.real (Hev m ∩ Hev m') ≤
      (if m ≤ m' then (20 / Real.pi) ^ 2 * (1 / ((m : ℝ) + 1) * (1 / (((m' - m : ℕ) : ℝ) + 1))) else 0) +
      (if m' ≤ m then (20 / Real.pi) ^ 2 * (1 / ((m' : ℝ) + 1) * (1 / (((m - m' : ℕ) : ℝ) + 1))) else 0) := by
  have hp := Real.pi_pos
  have key : ∀ a b : ℕ, a ≤ b → μS.real (Hev a ∩ Hev b) ≤
      (20 / Real.pi) ^ 2 * (1 / ((a : ℝ) + 1) * (1 / (((b - a : ℕ) : ℝ) + 1))) := by
    intro a b hab
    refine (Hev_pair a b hab).trans ?_
    have h1 := u_crude a
    have h2 := u_crude (b - a)
    have h0 : (0 : ℝ) ≤ (N2 (b - a) 0 0 : ℝ) / 4 ^ (b - a) := by positivity
    calc ((N2 a 0 0 : ℝ) / 4 ^ a) * ((N2 (b - a) 0 0 : ℝ) / 4 ^ (b - a))
        ≤ ((20 / Real.pi) / (a + 1)) * ((20 / Real.pi) / (((b - a : ℕ) : ℝ) + 1)) :=
          mul_le_mul h1 h2 h0 (by positivity)
      _ = _ := by ring
  rcases le_total m m' with h | h
  · have := key m m' h
    have hz : 0 ≤ (if m' ≤ m then (20 / Real.pi) ^ 2 * (1 / ((m' : ℝ) + 1) * (1 / (((m - m' : ℕ) : ℝ) + 1))) else 0) := by
      split_ifs <;> positivity
    rw [if_pos h]; linarith
  · have := key m' m h
    rw [Set.inter_comm] at this
    have hz : 0 ≤ (if m ≤ m' then (20 / Real.pi) ^ 2 * (1 / ((m : ℝ) + 1) * (1 / (((m' - m : ℕ) : ℝ) + 1))) else 0) := by
      split_ifs <;> positivity
    rw [if_pos h]; linarith

/-- one-sided row sum. -/
lemma row_sum (N M m : ℕ) :
    ∑ m' ∈ Icc N M, (if m ≤ m' then (1 / (((m' - m : ℕ) : ℝ) + 1)) else 0) ≤ Real.log (M + 1) + 1 := by
  classical
  refine le_trans ?_ (harm_upper M)
  rw [← sum_filter]
  have : ∑ m' ∈ (Icc N M).filter (fun m' => m ≤ m'), 1 / (((m' - m : ℕ) : ℝ) + 1) =
      ∑ d ∈ ((Icc N M).filter (fun m' => m ≤ m')).image (fun m' => m' - m), 1 / ((d : ℝ) + 1) := by
    rw [sum_image]
    intro x hx y hy hxy
    simp only [coe_filter, Set.mem_setOf_eq, mem_Icc] at hx hy
    simp only at hxy; omega
  rw [this]
  apply sum_le_sum_of_subset_of_nonneg
  · intro d hd
    simp only [mem_image, mem_filter, mem_Icc] at hd
    obtain ⟨x, ⟨⟨_, hx⟩, _⟩, rfl⟩ := hd
    rw [mem_range]; omega
  · intro _ _ _; positivity

theorem double_sum_le (N M : ℕ) :
    ∑ m ∈ Icc N M, ∑ m' ∈ Icc N M, μS.real (Hev m ∩ Hev m') ≤
      2 * (20 / Real.pi) ^ 2 * (Real.log (M + 1) + 1) ^ 2 := by
  have hp := Real.pi_pos
  set A : ℝ := (20 / Real.pi) ^ 2
  set g : ℕ → ℕ → ℝ := fun m m' =>
    if m ≤ m' then A * (1 / ((m : ℝ) + 1) * (1 / (((m' - m : ℕ) : ℝ) + 1))) else 0 with hg
  have h1 : ∑ m ∈ Icc N M, ∑ m' ∈ Icc N M, μS.real (Hev m ∩ Hev m') ≤
      ∑ m ∈ Icc N M, ∑ m' ∈ Icc N M, (g m m' + g m' m) :=
    sum_le_sum fun m _ => sum_le_sum fun m' _ => pair_sym m m'
  have hrow : ∀ m, ∑ m' ∈ Icc N M, g m m' ≤ A * (1 / ((m : ℝ) + 1)) * (Real.log (M + 1) + 1) := by
    intro m
    have e : ∑ m' ∈ Icc N M, g m m' =
        A * (1 / ((m : ℝ) + 1)) * ∑ m' ∈ Icc N M, (if m ≤ m' then (1 / (((m' - m : ℕ) : ℝ) + 1)) else 0) := by
      rw [mul_sum]; apply sum_congr rfl; intro m' _
      simp only [hg]; split_ifs <;> ring
    rw [e]
    exact mul_le_mul_of_nonneg_left (row_sum N M m) (by positivity)
  have hG : ∑ m ∈ Icc N M, ∑ m' ∈ Icc N M, g m m' ≤ A * (Real.log (M + 1) + 1) ^ 2 := by
    calc ∑ m ∈ Icc N M, ∑ m' ∈ Icc N M, g m m'
        ≤ ∑ m ∈ Icc N M, A * (1 / ((m : ℝ) + 1)) * (Real.log (M + 1) + 1) := sum_le_sum fun m _ => hrow m
      _ = A * (Real.log (M + 1) + 1) * ∑ m ∈ Icc N M, 1 / ((m : ℝ) + 1) := by
          rw [mul_sum]; apply sum_congr rfl; intro m _; ring
      _ ≤ A * (Real.log (M + 1) + 1) * (Real.log (M + 1) + 1) := by
          apply mul_le_mul_of_nonneg_left _ (by
            have : 0 ≤ Real.log ((M : ℝ) + 1) := Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) M])
            positivity)
          refine le_trans ?_ (harm_upper M)
          apply sum_le_sum_of_subset_of_nonneg
          · intro x hx; rw [mem_Icc] at hx; rw [mem_range]; omega
          · intro _ _ _; positivity
      _ = A * (Real.log (M + 1) + 1) ^ 2 := by ring
  have hsw : ∑ m ∈ Icc N M, ∑ m' ∈ Icc N M, g m' m = ∑ m ∈ Icc N M, ∑ m' ∈ Icc N M, g m m' := sum_comm
  have : ∑ m ∈ Icc N M, ∑ m' ∈ Icc N M, (g m m' + g m' m) =
      ∑ m ∈ Icc N M, ∑ m' ∈ Icc N M, g m m' + ∑ m ∈ Icc N M, ∑ m' ∈ Icc N M, g m' m := by
    rw [← sum_add_distrib]; apply sum_congr rfl; intro m _; rw [sum_add_distrib]
  rw [this, hsw] at h1
  linarith

/-- `∑_{K ∈ [N, M]} 1/(K+1) ≥ log (M+2) - log (N+1)`. -/
lemma harm_lower (N M : ℕ) (h : N ≤ M) :
    Real.log ((M : ℝ) + 2) - Real.log ((N : ℝ) + 1) ≤ ∑ K ∈ Icc N M, 1 / ((K : ℝ) + 1) := by
  induction M, h using Nat.le_induction with
  | base =>
    simp only [Icc_self, sum_singleton]
    rw [← Real.log_div (by positivity) (by positivity)]
    have := Real.log_le_sub_one_of_pos (show (0:ℝ) < ((N : ℝ) + 2) / ((N : ℝ) + 1) by positivity)
    have e : ((N : ℝ) + 2) / ((N : ℝ) + 1) - 1 = 1 / ((N : ℝ) + 1) := by field_simp; ring
    linarith
  | succ M hNM ih =>
    rw [← Finset.insert_Icc_right_eq_Icc_add_one (by omega), sum_insert (by simp)]
    have := Real.log_le_sub_one_of_pos (show (0:ℝ) < ((M + 1 : ℕ) + 2 : ℝ) / ((M : ℝ) + 2) by positivity)
    rw [Real.log_div (by positivity) (by positivity)] at this
    have e : (((M + 1 : ℕ) : ℝ) + 2) / ((M : ℝ) + 2) - 1 = 1 / (((M + 1 : ℕ) : ℝ) + 1) := by
      push_cast; field_simp; ring
    push_cast at this e ⊢
    linarith

/-- **positive-probability limsup.** -/
theorem limsup_Hev_pos : ∃ δ : ℝ, 0 < δ ∧ δ ≤ μS.real (Filter.limsup Hev atTop) := by
  have hp := Real.pi_pos
  set c : ℝ := (4 / Real.pi) / 60 with hc
  set A : ℝ := (20 / Real.pi) ^ 2 with hA
  have hc0 : 0 < c := by positivity
  have hA0 : 0 < A := by positivity
  set δ : ℝ := c ^ 2 / (8 * A) with hδ
  have hδ0 : 0 < δ := by positivity
  refine ⟨δ, hδ0, E521Q.limsup_pos μS Hev meas_Hev hδ0 ?_⟩
  obtain ⟨K0, hK0⟩ := eventually_atTop.mp Hev_lower
  intro N
  set N' := max N (max K0 1) with hN'
  have hlog : Tendsto (fun M : ℕ => Real.log ((M : ℝ) + 2)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop)
  obtain ⟨M, hM1, hM2⟩ := ((hlog.eventually_ge_atTop (2 * Real.log ((N' : ℝ) + 1) + 2)).and
    (eventually_ge_atTop N')).exists
  refine ⟨M, le_trans (le_max_left _ _) hM2, ?_, ?_⟩
  · -- lower bound for the first moment
    have hS : c * (Real.log ((M : ℝ) + 2) - Real.log ((N' : ℝ) + 1)) ≤ ∑ m ∈ Icc N M, μS.real (Hev m) := by
      have hsub : Icc N' M ⊆ Icc N M := Icc_subset_Icc (le_max_left _ _) le_rfl
      refine le_trans ?_ (sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => measureReal_nonneg))
      have hh := harm_lower N' M hM2
      calc c * (Real.log ((M : ℝ) + 2) - Real.log ((N' : ℝ) + 1)) ≤ c * ∑ m ∈ Icc N' M, 1 / ((m : ℝ) + 1) :=
            mul_le_mul_of_nonneg_left hh hc0.le
        _ = ∑ m ∈ Icc N' M, c * (1 / ((m : ℝ) + 1)) := by rw [mul_sum]
        _ ≤ ∑ m ∈ Icc N' M, μS.real (Hev m) := by
            apply sum_le_sum; intro m hm; rw [mem_Icc] at hm
            have hmK : K0 ≤ m := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hm.1
            have hm1 : (1 : ℝ) ≤ m := by
              have : 1 ≤ m := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hm.1
              exact_mod_cast this
            have := hK0 m hmK
            have e : (4 / Real.pi) / (60 * m) = c * (1 / (m : ℝ)) := by rw [hc]; field_simp
            rw [e] at this
            refine le_trans ?_ this
            apply mul_le_mul_of_nonneg_left _ hc0.le
            exact one_div_le_one_div_of_le (by linarith) (by linarith)
    have hD := double_sum_le N M
    have hlN : 0 ≤ Real.log ((N' : ℝ) + 1) := Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) N'])
    have hlM : Real.log ((M : ℝ) + 1) ≤ Real.log ((M : ℝ) + 2) :=
      Real.log_le_log (by positivity) (by linarith)
    have hlM0 : 0 ≤ Real.log ((M : ℝ) + 1) := Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) M])
    -- (log(M+1)+1) ≤ 2 (log(M+2) - log(N'+1))
    have hcmp : Real.log ((M : ℝ) + 1) + 1 ≤ 2 * (Real.log ((M : ℝ) + 2) - Real.log ((N' : ℝ) + 1)) := by
      linarith
    have hX : 0 ≤ Real.log ((M : ℝ) + 1) + 1 := by linarith
    have hsq : (Real.log ((M : ℝ) + 1) + 1) ^ 2 ≤ 4 * (Real.log ((M : ℝ) + 2) - Real.log ((N' : ℝ) + 1)) ^ 2 := by
      nlinarith
    have hS0 : 0 ≤ c * (Real.log ((M : ℝ) + 2) - Real.log ((N' : ℝ) + 1)) := by
      apply mul_nonneg hc0.le; linarith
    have hS2 := pow_le_pow_left₀ hS0 hS 2
    calc δ * ∑ m ∈ Icc N M, ∑ m' ∈ Icc N M, μS.real (Hev m ∩ Hev m')
        ≤ δ * (2 * A * (Real.log ((M : ℝ) + 1) + 1) ^ 2) := mul_le_mul_of_nonneg_left hD hδ0.le
      _ ≤ δ * (2 * A * (4 * (Real.log ((M : ℝ) + 2) - Real.log ((N' : ℝ) + 1)) ^ 2)) := by
          apply mul_le_mul_of_nonneg_left _ hδ0.le
          exact mul_le_mul_of_nonneg_left hsq (by positivity)
      _ = (c * (Real.log ((M : ℝ) + 2) - Real.log ((N' : ℝ) + 1))) ^ 2 := by
          rw [hδ]; field_simp; ring
      _ ≤ _ := hS2
  · -- positivity of the double sum via the diagonal at `M`
    have hMK : K0 ≤ M := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hM2
    have hM1' : 1 ≤ M := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hM2
    have hNM : N ≤ M := le_trans (le_max_left _ _) hM2
    have hpos : 0 < μS.real (Hev M ∩ Hev M) := by
      rw [Set.inter_self]
      refine lt_of_lt_of_le ?_ (hK0 M hMK)
      have : (0 : ℝ) < M := by exact_mod_cast hM1'
      positivity
    have hmem : M ∈ Icc N M := mem_Icc.mpr ⟨hNM, le_rfl⟩
    have h1 : μS.real (Hev M ∩ Hev M) ≤ ∑ m' ∈ Icc N M, μS.real (Hev M ∩ Hev m') :=
      single_le_sum (f := fun m' => μS.real (Hev M ∩ Hev m')) (fun _ _ => measureReal_nonneg) hmem
    have h2 : ∑ m' ∈ Icc N M, μS.real (Hev M ∩ Hev m') ≤ ∑ m ∈ Icc N M, ∑ m' ∈ Icc N M, μS.real (Hev m ∩ Hev m') :=
      single_le_sum (f := fun m => ∑ m' ∈ Icc N M, μS.real (Hev m ∩ Hev m'))
        (fun _ _ => sum_nonneg fun _ _ => measureReal_nonneg) hmem
    linarith

end E521
end

end S_P13

-- ===== F1 =====
section S_F1

/-! **Erdős 521 is false**: almost surely `R_n / log n` does not tend to `2/π` (original). -/

open Finset MeasureTheory Filter Topology

noncomputable section

namespace E521

/-- **The disproof.** -/
theorem erdos521_false_le (Rc : ℕ → (ℕ → Bool) → ℕ) (hRc : ∀ n ω, Rc n ω ≤ (fR n ω).roots.card) :
    ¬ (∀ᵐ ω ∂μS, Tendsto (fun n : ℕ => (Rc n ω : ℝ) / Real.log n) atTop (𝓝 (2 / Real.pi))) := by
  intro hconv
  obtain ⟨δ, hδ, hpos⟩ := limsup_Hev_pos
  have hlin : Tendsto (fun K : ℕ => 2 * K - 1) atTop atTop :=
    tendsto_atTop_atTop_of_monotone (fun a b h => by omega) (fun b => ⟨b + 1, by omega⟩)
  have hc : (635 / 1000 : ℝ) < 2 / Real.pi := by
    rw [lt_div_iff₀ Real.pi_pos]; linarith [Real.pi_lt_d4]
  have hlogT : Tendsto (fun K : ℕ => Real.log ((2 * K - 1 : ℕ) : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp hlin)
  have hlog : ∀ᶠ K : ℕ in atTop, 2 < (5 / 1000) * Real.log ((2 * K - 1 : ℕ) : ℝ) :=
    (hlogT.const_mul_atTop (by norm_num)).eventually_gt_atTop 2
  have hnull : μS (Filter.limsup Hev atTop) = 0 := by
    rw [measure_eq_zero_iff_ae_notMem]
    filter_upwards [hconv] with ω hω
    intro hmem
    rw [mem_limsup_iff_frequently_mem] at hmem
    have hev := hω.eventually (lt_mem_nhds hc)
    have hev2 := hlin.eventually hev
    obtain ⟨K, hKH, ⟨hK2, hK3⟩, hK1⟩ := (hmem.and_eventually ((hev2.and hlog).and (eventually_ge_atTop 2))).exists
    have hroots := roots_on_H K (by omega) ω hKH (tK_le K (by omega))
    have hlogpos : 0 < Real.log ((2 * K - 1 : ℕ) : ℝ) := by
      apply Real.log_pos; exact_mod_cast (by omega : 1 < 2 * K - 1)
    have hK2' : (635 / 1000 : ℝ) < (Rc (2 * K - 1) ω : ℝ) / Real.log ((2 * K - 1 : ℕ) : ℝ) := hK2
    rw [lt_div_iff₀ hlogpos] at hK2'
    have hle : (Rc (2 * K - 1) ω : ℝ) ≤ ((fR (2 * K - 1) ω).roots.card : ℝ) := by
      exact_mod_cast hRc (2 * K - 1) ω
    unfold AK at hroots
    linarith
  have := hpos
  rw [Measure.real, hnull] at this
  simp at this
  linarith

end E521
end

end S_F1


end
