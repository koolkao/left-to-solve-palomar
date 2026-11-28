/-
Copyright 2026 Ming-Chih Kao. Licensed under the Apache License, Version 2.0;
see the LICENSE file at the root of this repository.
-/
module

public import E521.Part5

/-! Part of the proof of Erdős 521 (see `E521/Part1.lean` for the port notes): sections P8–P11 of the
merged Left to Solve file `proofs/erdos-521.lean`. -/

@[expose] public section

-- ===== P8 =====
section S_P8

/-! On the good event, the number of real roots is at most the two sign-change counts plus two
(original). -/

open Finset MeasureTheory Polynomial

namespace E521

noncomputable instance instDecIev (k : ℕ) (ω : ℕ → Bool) : Decidable (ω ∈ Iev k) :=
  inferInstanceAs (Decidable (E521D.Ip _ _))

noncomputable instance instDecIalt (k : ℕ) (ω : ℕ → Bool) : Decidable (ω ∈ Ialt k) :=
  inferInstanceAs (Decidable (E521D.Ip _ _))

/-- forward partial sums from the total and a backward block. -/
lemma fwd_split (e : ℕ → ℝ) (n j : ℕ) (hj : j ≤ n) :
    E521D.S1 e j = ∑ i ∈ range (n + 1), e (n - i) - ∑ i ∈ range (n - j), e (n - i) := by
  unfold E521D.S1
  rw [show n + 1 = (n - j) + (j + 1) by omega, sum_range_add (fun i => e (n - i)) (n - j) (j + 1)]
  have : ∑ y ∈ range (j + 1), e (n - (n - j + y)) = ∑ y ∈ range (j + 1), e y := by
    rw [← sum_range_reflect]
    apply sum_congr rfl; intro y hy; rw [mem_range] at hy; congr 1; omega
  rw [this]; ring

lemma eAlt_pm (e : ℕ → ℝ) (he : ∀ j, e j = 1 ∨ e j = -1) (j : ℕ) : eAlt e j = 1 ∨ eAlt e j = -1 := by
  unfold eAlt
  rcases neg_one_pow_eq_or ℝ j with h | h <;> rcases he j with h' | h' <;> rw [h, h'] <;> norm_num

lemma aS_real (K : ℕ) (ω : ℕ → Bool) (i : ℕ) (hi : i < 2 * K) :
    ((aS (Φ K ω) i : ℤ) : ℝ) = eR ω (2 * K - 1 - i) := by
  rw [aS_Φ K ω i hi]; unfold st eR; split_ifs <;> simp

lemma Tk_real (K : ℕ) (ω : ℕ → Bool) (l : ℕ) (hl : l ≤ 2 * K) :
    ((Tk (Φ K ω) l : ℤ) : ℝ) = ∑ i ∈ range l, eR ω (2 * K - 1 - i) := by
  unfold Tk; push_cast
  apply sum_congr rfl; intro i hi; rw [mem_range] at hi; exact aS_real K ω i (by omega)

lemma Ak_real (K : ℕ) (ω : ℕ → Bool) (l : ℕ) (hl : l ≤ 2 * K) :
    ((Ak (Φ K ω) l : ℤ) : ℝ) = ∑ i ∈ range l, (-1) ^ i * eR ω (2 * K - 1 - i) := by
  unfold Ak; push_cast
  apply sum_congr rfl; intro i hi; rw [mem_range] at hi; rw [aS_real K ω i (by omega)]

/-- backward two-fold sums are sums of backward partial sums. -/
lemma b2_eq_sumT (e : ℕ → ℝ) (n k : ℕ) :
    E521D.b2 e n k = ∑ l ∈ range (k + 2), ∑ i ∈ range l, e (n - i) := by
  unfold E521D.b2
  induction k with
  | zero => simp [sum_range_succ]
  | succ k ih =>
    rw [sum_range_succ (fun l => ∑ i ∈ range l, e (n - i)), ← ih]
    rw [sum_range_succ (fun i => e (n - i) * (((k + 1 : ℕ) : ℝ) - i + 1))]
    rw [sum_range_succ (fun i => e (n - i))]
    have : ∑ i ∈ range (k + 1), e (n - i) * (((k + 1 : ℕ) : ℝ) - i + 1) =
        ∑ i ∈ range (k + 1), e (n - i) * ((k : ℝ) - i + 1) + ∑ i ∈ range (k + 1), e (n - i) := by
      rw [← sum_add_distrib]; apply sum_congr rfl; intro i _; push_cast; ring
    rw [this]; push_cast; ring

end E521

namespace E521

lemma neg_one_pow_sub {n i : ℕ} (hn : Odd n) (hi : i ≤ n) : ((-1 : ℝ) ^ (n - i)) = -((-1) ^ i) := by
  have h : (-1 : ℝ) ^ (n - i) * (-1) ^ i = -1 := by
    rw [← pow_add, Nat.sub_add_cancel hi, hn.neg_one_pow]
  have h2 : ((-1 : ℝ) ^ i) * (-1) ^ i = 1 := by rw [← pow_add, ← two_mul, pow_mul]; simp
  calc (-1 : ℝ) ^ (n - i) = (-1) ^ (n - i) * ((-1) ^ i * (-1) ^ i) := by rw [h2, mul_one]
    _ = ((-1) ^ (n - i) * (-1) ^ i) * (-1) ^ i := by ring
    _ = -((-1) ^ i) := by rw [h]; ring

/-- the negative-root polynomial. -/
lemma comp_neg_eq (e : ℕ → ℝ) (n : ℕ) :
    -((E521D.T e (n + 1)).comp (-X)) = E521D.T (eAlt e) (n + 1) := by
  unfold E521D.T eAlt
  rw [Polynomial.sum_comp, ← sum_neg_distrib]
  apply sum_congr rfl; intro j _
  rw [mul_comp, C_comp, pow_comp, X_comp, neg_pow]
  simp only [map_neg, map_mul, map_pow, map_one]
  ring

/-- **roots on the good event.** -/
theorem roots_good (K t lam : ℕ) (ω : ℕ → Bool) (hK : 1 ≤ K) (ht : t ≤ 2 * K - 1)
    (hcone : ω ∈ coneE K (fun y => (lam : ℤ) ≤ y) (fun y => (lam : ℤ) ≤ y))
    (hG : ∀ l ≤ t, |∑ i ∈ range l, eR ω (2 * K - 1 - i)| < 2 * lam - 1)
    (hG' : ∀ l ≤ t, |∑ i ∈ range l, (-1) ^ i * eR ω (2 * K - 1 - i)| < 2 * lam - 1) :
    (fR (2 * K - 1) ω).roots.card ≤
      ((range (2 * K - 1 - t)).filter (fun k => ω ∈ Iev k)).card +
      ((range (2 * K - 1 - t)).filter (fun k => ω ∈ Ialt k)).card + 2 := by
  classical
  set n := 2 * K - 1 with hn
  have hnodd : Odd n := ⟨K - 1, by omega⟩
  simp only [coneE, Set.mem_preimage, Set.mem_setOf_eq] at hcone
  rw [good2F_iff] at hcone
  obtain ⟨hquad, hUf, hVf⟩ := hcone
  have hq : good2 K 0 0 (Φ K ω) := by
    rw [good2_iff]; intro j hj; exact hquad j hj
  have hT2 := T2_nonneg (Φ K ω) hq
  -- final sums
  obtain ⟨eT, eA⟩ := Tk_even (Φ K ω) K le_rfl
  have hSn : 2 * (lam : ℝ) ≤ ∑ i ∈ range (2 * K), eR ω (2 * K - 1 - i) := by
    rw [← Tk_real K ω (2 * K) le_rfl, eT]; push_cast
    have h1 : (lam : ℤ) ≤ Uc (Φ K ω) K := by simpa using hUf
    have h2 : ((lam : ℤ) : ℝ) ≤ ((Uc (Φ K ω) K : ℤ) : ℝ) := by exact_mod_cast h1
    push_cast at h2
    linarith
  have hAn : 2 * (lam : ℝ) ≤ ∑ i ∈ range (2 * K), (-1) ^ i * eR ω (2 * K - 1 - i) := by
    rw [← Ak_real K ω (2 * K) le_rfl, eA]; push_cast
    have h1 : (lam : ℤ) ≤ Vc (Φ K ω) K := by simpa using hVf
    have h2 : ((lam : ℤ) : ℝ) ≤ ((Vc (Φ K ω) K : ℤ) : ℝ) := by exact_mod_cast h1
    push_cast at h2
    linarith
  have he := eR_pm ω
  have hf0 : (fR n ω).eval 0 ≠ 0 := by
    unfold fR E521D.T
    rw [eval_finsetSum]
    simp only [eval_mul, eval_C, eval_pow, eval_X]
    rw [sum_eq_single 0]
    · simp; rcases he 0 with h | h <;> rw [h] <;> norm_num
    · intro b _ hb; simp [zero_pow hb]
    · intro h; exact absurd (mem_range.mpr (by omega)) h
  rw [E521D.card_roots_split _ hf0]
  have hn1 : n + 1 = 2 * K := by omega
  have hSn' : 2 * (lam : ℝ) ≤ ∑ i ∈ range (2 * K), eR ω (n - i) := hSn
  have hAn' : 2 * (lam : ℝ) ≤ ∑ i ∈ range (2 * K), (-1) ^ i * eR ω (n - i) := hAn
  have heA := eAlt_pm (eR ω) he
  have halt : ∀ i ≤ n, eAlt (eR ω) (n - i) = (-1) ^ i * eR ω (n - i) := by
    intro i hi; unfold eAlt; rw [neg_one_pow_sub hnodd hi]; ring
  -- forward partial sums
  have hS : ∀ j, n - t ≤ j → j ≤ n → 1 ≤ E521D.S1 (eR ω) j := by
    intro j hj1 hj2
    rw [fwd_split _ n j hj2, hn1]
    have hb := hG (n - j) (by omega)
    have := (abs_lt.mp hb).2
    linarith
  have hSA : ∀ j, n - t ≤ j → j ≤ n → 1 ≤ E521D.S1 (eAlt (eR ω)) j := by
    intro j hj1 hj2
    rw [fwd_split _ n j hj2]
    have e1 : ∑ i ∈ range (n + 1), eAlt (eR ω) (n - i) = ∑ i ∈ range (2 * K), (-1) ^ i * eR ω (n - i) := by
      rw [hn1]; apply sum_congr rfl; intro i hi; rw [mem_range] at hi; rw [halt i (by omega)]
    have e2 : ∑ i ∈ range (n - j), eAlt (eR ω) (n - i) = ∑ i ∈ range (n - j), (-1) ^ i * eR ω (n - i) := by
      apply sum_congr rfl; intro i hi; rw [mem_range] at hi; rw [halt i (by omega)]
    rw [e1, e2]
    have hb := hG' (n - j) (by omega)
    have := (abs_lt.mp hb).2
    linarith
  -- backward two-fold sums
  have hB : ∀ k ≤ n, 0 ≤ E521D.b2 (eR ω) n k := by
    intro k hk
    rw [b2_eq_sumT]
    have h := (hT2 (k + 1) (by omega)).1
    have e : ∑ l ∈ range (k + 1 + 1), ((Tk (Φ K ω) l : ℤ) : ℝ) = ∑ l ∈ range (k + 2), ∑ i ∈ range l, eR ω (n - i) := by
      apply sum_congr rfl; intro l hl; rw [mem_range] at hl; rw [Tk_real K ω l (by omega)]
    have h' : (0 : ℝ) ≤ ∑ l ∈ range (k + 1 + 1), ((Tk (Φ K ω) l : ℤ) : ℝ) := by exact_mod_cast h
    rw [e] at h'; exact h'
  have hBA : ∀ k ≤ n, 0 ≤ E521D.b2 (eAlt (eR ω)) n k := by
    intro k hk
    rw [b2_eq_sumT]
    have h := (hT2 (k + 1) (by omega)).2
    have e : ∑ l ∈ range (k + 1 + 1), ((Ak (Φ K ω) l : ℤ) : ℝ) = ∑ l ∈ range (k + 2), ∑ i ∈ range l, eAlt (eR ω) (n - i) := by
      apply sum_congr rfl; intro l hl; rw [mem_range] at hl; rw [Ak_real K ω l (by omega)]
      apply sum_congr rfl; intro i hi; rw [mem_range] at hi; rw [halt i (by omega)]
    have h' : (0 : ℝ) ≤ ∑ l ∈ range (k + 1 + 1), ((Ak (Φ K ω) l : ℤ) : ℝ) := by exact_mod_cast h
    rw [e] at h'; exact h'
  have hpos := E521D.pos_roots_le (eR ω) he n (n - t) (n * n + n + 1) (by omega) le_rfl hS hB
  have hneg := E521D.pos_roots_le (eAlt (eR ω)) heA n (n - t) (n * n + n + 1) (by omega) le_rfl hSA hBA
  have hcomp : ((fR n ω).comp (-X)).roots = (E521D.T (eAlt (eR ω)) (n + 1)).roots := by
    rw [← comp_neg_eq, roots_neg]; rfl
  have c1 : ((range (n - t)).filter (fun k => ω ∈ Iev k)).card =
      ((range (n - t)).filter (fun k => E521D.Ip (E521D.c2 (eR ω) k) (E521D.c2 (eR ω) (k + 1)))).card := by
    congr 1
  have c2' : ((range (n - t)).filter (fun k => ω ∈ Ialt k)).card =
      ((range (n - t)).filter (fun k => E521D.Ip (E521D.c2 (eAlt (eR ω)) k) (E521D.c2 (eAlt (eR ω)) (k + 1)))).card := by
    congr 1
  rw [hcomp, c1, c2']
  have hfR : fR n ω = E521D.T (eR ω) (n + 1) := rfl
  rw [hfR]
  omega

end E521

end S_P8

-- ===== Q4 =====
section S_Q4

/-! Markov for a count of events restricted to an event (original). -/

open MeasureTheory Finset

namespace E521Q

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

theorem markov_count (E : Set Ω) (hE : MeasurableSet E) (s : Finset ℕ) (B : ℕ → Set Ω)
    (hB : ∀ k, MeasurableSet (B k)) [∀ k, DecidablePred (· ∈ B k)] {A : ℝ} (hA : 0 < A) :
    A * μ.real (E ∩ {ω | A ≤ ((s.filter (fun k => ω ∈ B k)).card : ℝ)}) ≤ ∑ k ∈ s, μ.real (E ∩ B k) := by
  classical
  set C := E ∩ {ω | A ≤ ((s.filter (fun k => ω ∈ B k)).card : ℝ)} with hC
  have hcnt : ∀ ω, ((s.filter (fun k => ω ∈ B k)).card : ℝ) = ∑ k ∈ s, (B k).indicator (fun _ => (1 : ℝ)) ω := by
    intro ω
    rw [card_filter]; push_cast
    apply sum_congr rfl; intro k _
    by_cases h : ω ∈ B k <;> simp [h]
  have hCm : MeasurableSet C := by
    apply hE.inter
    have : {ω | A ≤ ((s.filter (fun k => ω ∈ B k)).card : ℝ)} =
        {ω | A ≤ ∑ k ∈ s, (B k).indicator (fun _ => (1 : ℝ)) ω} := by
      ext ω; simp only [Set.mem_setOf_eq, hcnt]
    rw [this]
    exact measurableSet_le measurable_const
      (Finset.measurable_sum _ (fun k _ => (measurable_const.indicator (hB k))))
  have hpt : ∀ ω, A * C.indicator (fun _ => (1 : ℝ)) ω ≤
      ∑ k ∈ s, (E ∩ B k).indicator (fun _ => (1 : ℝ)) ω := by
    intro ω
    by_cases hω : ω ∈ C
    · rw [Set.indicator_of_mem hω, mul_one]
      have h1 : A ≤ ((s.filter (fun k => ω ∈ B k)).card : ℝ) := hω.2
      rw [hcnt] at h1
      refine h1.trans (le_of_eq ?_)
      apply sum_congr rfl; intro k _
      by_cases h : ω ∈ B k
      · rw [Set.indicator_of_mem h, Set.indicator_of_mem (show ω ∈ E ∩ B k from ⟨hω.1, h⟩)]
      · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (fun h' : ω ∈ E ∩ B k => h h'.2)]
    · rw [Set.indicator_of_notMem hω, mul_zero]
      exact sum_nonneg (fun k _ => Set.indicator_nonneg (fun _ _ => zero_le_one) ω)
  have hi : ∀ k, Integrable ((E ∩ B k).indicator (fun _ => (1 : ℝ))) μ :=
    fun k => (integrable_const 1).indicator (hE.inter (hB k))
  have := integral_mono ((integrable_const (1 : ℝ)).indicator hCm |>.const_mul A)
    (integrable_finsetSum s (fun k _ => hi k)) hpt
  rw [integral_const_mul, integral_indicator_const _ hCm, integral_finsetSum s (fun k _ => hi k)] at this
  rw [sum_congr rfl (fun k _ => integral_indicator_const (1 : ℝ) (μ := μ) (hE.inter (hB k)))] at this
  simpa using this

end E521Q

end S_Q4

-- ===== Q2 =====
section S_Q2

/-! Harmonic-type sums (original). -/

open Finset Real

namespace E521Q

lemma inv_succ_le_log (k : ℕ) (hk : 1 ≤ k) : 1 / ((k : ℝ) + 1) ≤ Real.log (k + 1) - Real.log k := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  rw [← Real.log_div (by positivity) hk0.ne']
  have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < k / (k + 1) by positivity)
  rw [Real.log_div hk0.ne' (by positivity)] at h
  rw [Real.log_div (by positivity) hk0.ne']
  have : (k : ℝ) / (k + 1) - 1 = -(1 / ((k : ℝ) + 1)) := by field_simp; ring
  linarith

/-- `∑_{k=a}^{b-1} 1/(k+1) ≤ log b - log a` for `1 ≤ a ≤ b`. -/
lemma harm_Ico (a b : ℕ) (ha : 1 ≤ a) (hab : a ≤ b) :
    ∑ k ∈ Ico a b, 1 / ((k : ℝ) + 1) ≤ Real.log b - Real.log a := by
  induction b, hab using Nat.le_induction with
  | base => simp
  | succ b hab ih =>
    rw [sum_Ico_succ_top hab]
    have := inv_succ_le_log b (by omega)
    push_cast
    linarith

/-- partial fractions: `1/((k+2)(n-k)) = (1/(n+2)) (1/(k+2) + 1/(n-k))`. -/
lemma pf (n k : ℕ) (hk : k < n) :
    1 / (((k : ℝ) + 2) * ((n : ℝ) - k)) = 1 / ((n : ℝ) + 2) * (1 / ((k : ℝ) + 2) + 1 / ((n : ℝ) - k)) := by
  have h1 : (0 : ℝ) < (n : ℝ) - k := by
    have : (k : ℝ) < n := by exact_mod_cast hk
    linarith
  field_simp
  ring

/-- `∑_{k<p} 1/((k+2)(n-k)) ≤ (log (p+1) + log n - log (n-p+1) + 1) / (n+2)` for `p ≤ n`. -/
lemma double_harm (n p : ℕ) (hpl : p < n) (hn : 1 ≤ n) :
    ∑ k ∈ range p, 1 / (((k : ℝ) + 2) * ((n : ℝ) - k)) ≤
      (Real.log (p + 1) + (Real.log n - Real.log (n - p + 1)) + 1) / ((n : ℝ) + 2) := by
  have hp : p ≤ n := hpl.le
  rcases Nat.eq_zero_or_pos p with h0 | hp0
  · subst h0; simp
    have : 0 ≤ Real.log (n : ℝ) - Real.log ((n : ℝ) + 1) + 1 := by
      have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
      have := Real.log_le_sub_one_of_pos (show (0:ℝ) < ((n : ℝ) + 1) / n by positivity)
      rw [Real.log_div (by positivity) hn0.ne'] at this
      have : ((n : ℝ) + 1) / n - 1 ≤ 1 := by
        rw [div_sub_one hn0.ne', div_le_one hn0]
        have : (1 : ℝ) ≤ n := by exact_mod_cast hn
        linarith
      linarith
    first | exact div_nonneg (by linarith) (by positivity) | linarith | positivity
  have e : ∀ k ∈ range p, 1 / (((k : ℝ) + 2) * ((n : ℝ) - k)) =
      1 / ((n : ℝ) + 2) * (1 / ((k + 1 : ℕ) + 1 : ℝ) + 1 / (((n - k - 1 : ℕ) : ℝ) + 1)) := by
    intro k hk; rw [mem_range] at hk
    rw [pf n k (by omega)]
    congr 2
    · push_cast; ring
    · rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; push_cast; ring
  rw [sum_congr rfl e, ← mul_sum, sum_add_distrib]
  -- first harmonic piece: k+1 ranges over [1, p]
  have h1 : ∑ k ∈ range p, 1 / (((k + 1 : ℕ) : ℝ) + 1) ≤ Real.log (p + 1) := by
    have := harm_Ico 1 (p + 1) le_rfl (by omega)
    rw [Nat.cast_one, Real.log_one, sub_zero] at this
    have e2 : ∑ k ∈ Ico 1 (p + 1), 1 / ((k : ℝ) + 1) = ∑ k ∈ range p, 1 / (((k + 1 : ℕ) : ℝ) + 1) := by
      rw [sum_Ico_eq_sum_range]; apply sum_congr (by congr 1) ; intro k _; push_cast; ring_nf
    rw [← e2]; push_cast at this ⊢; exact this
  -- second piece: n-k-1 ranges over [n-p, n-1]
  have h2 : ∑ k ∈ range p, 1 / (((n - k - 1 : ℕ) : ℝ) + 1) ≤ (Real.log n - Real.log (n - p + 1)) + 1 := by
    have hrefl : ∑ k ∈ range p, 1 / (((n - k - 1 : ℕ) : ℝ) + 1) = ∑ j ∈ Ico (n - p) n, 1 / ((j : ℝ) + 1) := by
      rw [sum_Ico_eq_sum_range, show n - (n - p) = p by omega, ← sum_range_reflect]
      apply sum_congr rfl; intro k hk; rw [mem_range] at hk
      congr 3; omega
    rw [hrefl]
    have hpn : p ≠ n := by omega
    have := harm_Ico (n - p) n (by omega) (by omega)
    have hl : Real.log ((n - p : ℕ) : ℝ) ≥ Real.log ((n : ℝ) - p + 1) - 1 := by
      rw [Nat.cast_sub hp]
      have hpos : (0 : ℝ) < (n : ℝ) - p := by
        have : (p : ℝ) < n := by exact_mod_cast (lt_of_le_of_ne hp hpn)
        linarith
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < ((n : ℝ) - p + 1) / ((n : ℝ) - p) by positivity)
      rw [Real.log_div (by positivity) hpos.ne'] at this
      have h1np : (1 : ℝ) ≤ (n : ℝ) - p := by
        have : ((p + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast (by omega : p + 1 ≤ n)
        push_cast at this; linarith
      have : ((n : ℝ) - p + 1) / ((n : ℝ) - p) - 1 ≤ 1 := by
        rw [div_sub_one hpos.ne', div_le_one hpos]
        linarith
      linarith
    linarith
  have hn2 : (0 : ℝ) < (n : ℝ) + 2 := by positivity
  have key : ∑ k ∈ range p, 1 / (((k + 1 : ℕ) : ℝ) + 1) + ∑ k ∈ range p, 1 / (((n - k - 1 : ℕ) : ℝ) + 1) ≤
      Real.log (p + 1) + (Real.log n - Real.log (n - p + 1)) + 1 := by linarith
  calc _ = (∑ k ∈ range p, 1 / (((k + 1 : ℕ) : ℝ) + 1) + ∑ k ∈ range p, 1 / (((n - k - 1 : ℕ) : ℝ) + 1)) /
        ((n : ℝ) + 2) := by ring
    _ ≤ _ := div_le_div_of_nonneg_right key hn2.le

end E521Q

end S_Q2

-- ===== Q5 =====
section S_Q5

/-! The conditional first-moment sum (pure real analysis, original). -/

open Finset Real

namespace E521Q

/-- `∑_{k<p} u_k p_k` with `p_k ≤ a/(k+2)` beyond `n₀` and `u_k ≤ b/(n-k)`. -/
theorem count_sum {n p n0 : ℕ} {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hp : p < n) (hn0 : n0 ≤ p)
    (pk uk : ℕ → ℝ) (hpk0 : ∀ k, 0 ≤ pk k) (hpk1 : ∀ k, pk k ≤ 1)
    (hpk : ∀ k, n0 ≤ k → pk k ≤ a / ((k : ℝ) + 2)) (huk0 : ∀ k, 0 ≤ uk k)
    (huk : ∀ k < p, uk k ≤ b / ((n : ℝ) - k)) :
    ∑ k ∈ range p, uk k * pk k ≤
      n0 * (b / ((n : ℝ) - n0)) + a * b * ((Real.log (p + 1) + (Real.log n - Real.log (n - p + 1)) + 1) / ((n : ℝ) + 2)) := by
  have hn1 : 1 ≤ n := by omega
  have hsplit : ∑ k ∈ range p, uk k * pk k =
      ∑ k ∈ range n0, uk k * pk k + ∑ k ∈ range (p - n0), uk (n0 + k) * pk (n0 + k) := by
    rw [← sum_range_add, Nat.add_sub_cancel' hn0]
  rw [hsplit]
  have h1 : ∑ k ∈ range n0, uk k * pk k ≤ n0 * (b / ((n : ℝ) - n0)) := by
    calc ∑ k ∈ range n0, uk k * pk k ≤ ∑ k ∈ range n0, b / ((n : ℝ) - n0) := by
          apply sum_le_sum; intro k hk; rw [mem_range] at hk
          have hu := huk k (by omega)
          have hnk : (0 : ℝ) < (n : ℝ) - k := by
            have : (k : ℝ) < n := by exact_mod_cast (by omega : k < n)
            linarith
          have hnn0 : (0 : ℝ) < (n : ℝ) - n0 := by
            have : (n0 : ℝ) < n := by exact_mod_cast (by omega : n0 < n)
            linarith
          have : b / ((n : ℝ) - k) ≤ b / ((n : ℝ) - n0) := by
            apply div_le_div_of_nonneg_left hb hnn0
            have : (k : ℝ) ≤ n0 := by exact_mod_cast hk.le
            linarith
          calc uk k * pk k ≤ uk k * 1 := mul_le_mul_of_nonneg_left (hpk1 k) (huk0 k)
            _ ≤ b / ((n : ℝ) - n0) := by rw [mul_one]; exact hu.trans this
      _ = n0 * (b / ((n : ℝ) - n0)) := by simp
  have h2 : ∑ k ∈ range (p - n0), uk (n0 + k) * pk (n0 + k) ≤
      a * b * ∑ k ∈ range p, 1 / (((k : ℝ) + 2) * ((n : ℝ) - k)) := by
    have : ∑ k ∈ range (p - n0), uk (n0 + k) * pk (n0 + k) ≤
        ∑ k ∈ range (p - n0), a * b * (1 / ((((n0 + k : ℕ) : ℝ) + 2) * ((n : ℝ) - (n0 + k : ℕ)))) := by
      apply sum_le_sum; intro k hk; rw [mem_range] at hk
      have hu := huk (n0 + k) (by omega)
      have hpp := hpk (n0 + k) (by omega)
      have hnk : (0 : ℝ) < (n : ℝ) - (n0 + k : ℕ) := by
        have : ((n0 + k : ℕ) : ℝ) < n := by exact_mod_cast (by omega : n0 + k < n)
        linarith
      calc uk (n0 + k) * pk (n0 + k) ≤ (b / ((n : ℝ) - (n0 + k : ℕ))) * (a / (((n0 + k : ℕ) : ℝ) + 2)) :=
            mul_le_mul hu hpp (hpk0 _) (by positivity)
        _ = a * b * (1 / ((((n0 + k : ℕ) : ℝ) + 2) * ((n : ℝ) - (n0 + k : ℕ)))) := by
            field_simp
    refine this.trans ?_
    rw [← mul_sum]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have hsub : ∑ k ∈ range (p - n0), 1 / ((((n0 + k : ℕ) : ℝ) + 2) * ((n : ℝ) - (n0 + k : ℕ))) =
        ∑ k ∈ Ico n0 p, 1 / (((k : ℝ) + 2) * ((n : ℝ) - k)) := by
      rw [sum_Ico_eq_sum_range]
    rw [hsub]
    apply sum_le_sum_of_subset_of_nonneg
    · intro x hx; rw [mem_Ico] at hx; rw [mem_range]; omega
    · intro k hk _
      rw [mem_range] at hk
      have : (k : ℝ) < n := by exact_mod_cast (by omega : k < n)
      have : (0 : ℝ) < (n : ℝ) - k := by linarith
      positivity
  have h3 := double_harm n p hp hn1
  have h2' := h2.trans (mul_le_mul_of_nonneg_left h3 (by positivity))
  linarith

end E521Q

end S_Q5

-- ===== C19 =====
section S_C19

/-! Sharp bounds for the quadrant probability `u_L = N2 L 0 0 / 4^L` via Wallis:
`(4/π)/(L+4) ≤ u_L ≤ (4/π)/(L+1) · √(1 + 40/L)` (original). -/

open Finset Real
open scoped Nat

namespace E521

/-- normalized central binomial `b_h = C(h, ⌈h/2⌉)/2^h`. -/
noncomputable def bb (h : ℕ) : ℝ := (cc h : ℝ) / 2 ^ h

lemma cb_wallis (k : ℕ) :
    (Nat.centralBinom k : ℝ) ^ 2 * (2 * k + 1) = 16 ^ k / Real.Wallis.W k := by
  rw [Real.Wallis.W_eq_factorial_ratio, Nat.centralBinom_eq_two_mul_choose,
    Nat.cast_choose ℝ (show k ≤ 2 * k by omega)]
  have h1 : (2 * k - k) = k := by omega
  rw [h1]
  have hf : (0 : ℝ) < k ! := by exact_mod_cast Nat.factorial_pos k
  have hf2 : (0 : ℝ) < (2 * k)! := by exact_mod_cast Nat.factorial_pos (2 * k)
  rw [show (16 : ℝ) ^ k = 2 ^ (4 * k) by rw [pow_mul]; norm_num]
  field_simp

lemma cb_sq_lower (k : ℕ) : (2 / π) * 16 ^ k ≤ (Nat.centralBinom k : ℝ) ^ 2 * (2 * k + 1) := by
  rw [cb_wallis]
  have hW := Real.Wallis.W_le k
  have hW0 := Real.Wallis.W_pos k
  rw [le_div_iff₀ hW0]
  have : (2 / π) * 16 ^ k * Real.Wallis.W k ≤ (2 / π) * 16 ^ k * (π / 2) := by (gcongr)
  have e : (2 / π) * 16 ^ k * (π / 2) = (16 : ℝ) ^ k := by field_simp
  linarith

lemma cb_sq_upper (k : ℕ) :
    (Nat.centralBinom k : ℝ) ^ 2 * (2 * k + 1) ^ 2 ≤ (2 / π) * 16 ^ k * (2 * k + 2) := by
  have h := cb_wallis k
  have hW := Real.Wallis.le_W k
  have hW0 := Real.Wallis.W_pos k
  have hk : (0 : ℝ) < 2 * k + 1 := by positivity
  have e : (Nat.centralBinom k : ℝ) ^ 2 * (2 * k + 1) ^ 2 = 16 ^ k / Real.Wallis.W k * (2 * k + 1) := by
    rw [← h]; ring
  rw [e, div_mul_eq_mul_div, div_le_iff₀ hW0]
  have : (2 / π) * 16 ^ k * (2 * k + 2) * (((2 : ℝ) * k + 1) / (2 * k + 2) * (π / 2)) ≤
      (2 / π) * 16 ^ k * (2 * k + 2) * Real.Wallis.W k := by (gcongr)
  have e2 : (2 / π) * 16 ^ k * (2 * k + 2) * (((2 : ℝ) * k + 1) / (2 * k + 2) * (π / 2)) =
      16 ^ k * (2 * k + 1) := by field_simp
  linarith

lemma bb_sq_bounds (h : ℕ) :
    (2 / π) / (h + 2) ≤ bb h ^ 2 ∧ bb h ^ 2 ≤ (2 / π) * (h + 2) / (h + 1) ^ 2 := by
  have hpi := Real.pi_pos
  obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' h
  · -- h = 2k
    unfold bb; rw [cc_even, div_pow]
    have h2 : ((2 : ℝ) ^ (2 * k)) ^ 2 = 16 ^ k := by
      rw [← pow_mul, show 2 * k * 2 = 4 * k by ring, pow_mul]; norm_num
    rw [h2]
    have l := cb_sq_lower k
    have u := cb_sq_upper k
    push_cast
    constructor
    · rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [Nat.cast_nonneg (α := ℝ) k]
    · rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [Nat.cast_nonneg (α := ℝ) k]
  · -- h = 2k+1: bb h = c_{k+1}/4^{k+1}
    unfold bb; rw [cc_odd, div_pow]
    have h2 : ((Nat.centralBinom (k + 1) : ℝ) / 2) ^ 2 / ((2 : ℝ) ^ (2 * k + 1)) ^ 2 =
        (Nat.centralBinom (k + 1) : ℝ) ^ 2 / 16 ^ (k + 1) := by
      rw [div_pow, div_div]; congr 1
      rw [← pow_mul, ← pow_add, show 2 + (2 * k + 1) * 2 = 4 * (k + 1) by ring, pow_mul]; norm_num
    rw [h2]
    have l := cb_sq_lower (k + 1)
    have u := cb_sq_upper (k + 1)
    push_cast at l u ⊢
    constructor
    · rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [Nat.cast_nonneg (α := ℝ) k]
    · rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have hk0 := Nat.cast_nonneg (α := ℝ) k
      -- (2k+3)^{-2}(2k+4) ≤ (2k+3)(2k+2)^{-2}: use (h+3)(h+1)^2 ≤ (h+2)^3
      have key : (2 * (k : ℝ) + 4) * (2 * k + 2) ^ 2 ≤ (2 * k + 3) ^ 3 := by nlinarith
      nlinarith [sq_nonneg ((Nat.centralBinom (k + 1) : ℝ)), key,
        mul_le_mul_of_nonneg_left key (by positivity : (0:ℝ) ≤ (2 / π) * 16 ^ (k + 1))]

lemma bb_nonneg (h : ℕ) : 0 ≤ bb h := by unfold bb; positivity

lemma u_eq (L : ℕ) : (N2 L 0 0 : ℝ) / 4 ^ L =
    ∑ h ∈ range (L + 1), (L.choose h : ℝ) / 2 ^ L * (bb h * bb (L - h)) := by
  rw [N2_origin', sum_div]
  apply sum_congr rfl; intro h hh; rw [mem_range] at hh
  unfold bb
  have : (4 : ℝ) ^ L = 2 ^ L * (2 ^ h * 2 ^ (L - h)) := by
    rw [← pow_add, ← pow_add, show h + (L - h) = L by omega, ← two_mul, pow_mul]; norm_num
  rw [this]; field_simp

/-- **lower bound** `u_L ≥ (4/π)/(L+4)`. -/
theorem u_lower (L : ℕ) : (4 / π) / (L + 4) ≤ (N2 L 0 0 : ℝ) / 4 ^ L := by
  rw [u_eq]
  have each : ∀ h ∈ range (L + 1), (L.choose h : ℝ) / 2 ^ L * ((4 / π) / (L + 4)) ≤
      (L.choose h : ℝ) / 2 ^ L * (bb h * bb (L - h)) := by
    intro h hh; rw [mem_range] at hh
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have a := (bb_sq_bounds h).1
    have b := (bb_sq_bounds (L - h)).1
    have hLh : ((L - h : ℕ) : ℝ) = L - h := by rw [Nat.cast_sub (by omega)]
    rw [hLh] at b
    have hx := bb_nonneg h
    have hy := bb_nonneg (L - h)
    have hpi := Real.pi_pos
    have hh0 : (0 : ℝ) ≤ h := by positivity
    have hhL : (h : ℝ) ≤ L := by exact_mod_cast (show h ≤ L by omega)
    -- (bb h bb(L-h))^2 ≥ (2/π)^2/((h+2)(L-h+2)) ≥ (4/π)^2/(L+4)^2
    have amgm : 4 * ((h : ℝ) + 2) * (L - h + 2) ≤ (L + 4) ^ 2 := by
      nlinarith [sq_nonneg (((h : ℝ) + 2) - (L - h + 2))]
    have sq : ((4 / π) / (L + 4)) ^ 2 ≤ (bb h * bb (L - h)) ^ 2 := by
      rw [mul_pow]
      have := mul_le_mul a b (by positivity) (by positivity)
      refine le_trans ?_ this
      rw [div_pow, div_mul_div_comm, div_le_div_iff₀ (by positivity) (by positivity)]
      have : (4 / π) ^ 2 = 4 * (2 / π * (2 / π)) := by ring
      rw [this]
      nlinarith [mul_pos hpi hpi, sq_nonneg (2 / π)]
    exact (pow_le_pow_iff_left₀ (by positivity) (mul_nonneg hx hy) two_ne_zero).mp sq
  have := sum_le_sum each
  rw [← sum_mul] at this
  have hs : ∑ h ∈ range (L + 1), (L.choose h : ℝ) / 2 ^ L = 1 := by
    rw [← sum_div]
    have : ∑ h ∈ range (L + 1), (L.choose h : ℝ) = 2 ^ L := by exact_mod_cast Nat.sum_range_choose L
    rw [this]; exact div_self (by positivity)
  rw [hs, one_mul] at this
  exact this

end E521

end S_C19

-- ===== C20 =====
section S_C20

/-! Upper bound `u_L ≤ (4/π)/(L+1) · √(1 + 24/(L+1))` (original). -/

open Finset Real
open scoped Nat

namespace E521

lemma row_partial (n M r : ℕ) : ∑ h ∈ range M, ((n.choose (h + r) : ℕ) : ℝ) ≤ 2 ^ n := by
  have h1 : ∑ h ∈ range M, ((n.choose (h + r) : ℕ) : ℝ) ≤ ∑ j ∈ range (M + r), ((n.choose j : ℕ) : ℝ) := by
    rw [sum_range_add_sum_Ico _ (show r ≤ M + r by omega) |>.symm]
    have : ∑ h ∈ range M, ((n.choose (h + r) : ℕ) : ℝ) = ∑ j ∈ Ico r (M + r), ((n.choose j : ℕ) : ℝ) := by
      rw [sum_Ico_eq_sum_range]; apply sum_congr (by congr 1; omega); intro h _; rw [add_comm]
    rw [this]
    have : 0 ≤ ∑ j ∈ range r, ((n.choose j : ℕ) : ℝ) := sum_nonneg (fun _ _ => by positivity)
    linarith
  refine h1.trans ?_
  have h2 : ∀ K, ∑ j ∈ range K, ((n.choose j : ℕ) : ℝ) ≤ 2 ^ n := by
    intro K
    rcases le_or_gt K (n + 1) with hK | hK
    · calc ∑ j ∈ range K, ((n.choose j : ℕ) : ℝ) ≤ ∑ j ∈ range (n + 1), ((n.choose j : ℕ) : ℝ) :=
            sum_le_sum_of_subset_of_nonneg (fun x hx => by rw [mem_range] at hx ⊢; omega)
              (fun _ _ _ => by positivity)
        _ = 2 ^ n := by exact_mod_cast Nat.sum_range_choose n
    · rw [show K = (n + 1) + (K - (n + 1)) by omega, sum_range_add]
      have : ∑ j ∈ range (K - (n + 1)), ((n.choose (n + 1 + j) : ℕ) : ℝ) = 0 := by
        apply sum_eq_zero; intro j _; rw [Nat.choose_eq_zero_of_lt (by omega)]; simp
      rw [this, add_zero]
      exact_mod_cast (Nat.sum_range_choose n).le
  exact h2 _

lemma choose_id2 (L h : ℕ) (hh : h ≤ L) :
    (L.choose h : ℝ) * ((L + 1) * (L + 2)) = ((L + 2).choose (h + 1) : ℝ) * ((h + 1) * (L - h + 1)) := by
  have hA := Nat.choose_mul_factorial_mul_factorial hh
  have hB := Nat.choose_mul_factorial_mul_factorial (show h + 1 ≤ L + 2 by omega)
  rw [show L + 2 - (h + 1) = (L - h) + 1 by omega, Nat.factorial_succ h, Nat.factorial_succ (L - h),
    Nat.factorial_succ (L + 1), Nat.factorial_succ L] at hB
  have hA' := congrArg (fun x : ℕ => (x : ℝ)) hA
  have hB' := congrArg (fun x : ℕ => (x : ℝ)) hB
  push_cast [Nat.cast_sub hh] at hA' hB'
  apply mul_right_cancel₀ (show ((h ! : ℕ) : ℝ) * ((L - h)! : ℕ) ≠ 0 by positivity)
  linear_combination ((L : ℝ) + 1) * ((L : ℝ) + 2) * hA' - hB'

lemma choose_id3 (L h : ℕ) (hh : h ≤ L) :
    (L.choose h : ℝ) * ((L + 1) * (L + 2) * (L + 3)) =
      ((L + 3).choose (h + 1) : ℝ) * ((h + 1) * (L - h + 1) * (L - h + 2)) := by
  have hA := Nat.choose_mul_factorial_mul_factorial hh
  have hB := Nat.choose_mul_factorial_mul_factorial (show h + 1 ≤ L + 3 by omega)
  rw [show L + 3 - (h + 1) = (L - h) + 1 + 1 by omega, Nat.factorial_succ h, Nat.factorial_succ (L - h + 1),
    Nat.factorial_succ (L - h), Nat.factorial_succ (L + 2),
    Nat.factorial_succ (L + 1), Nat.factorial_succ L] at hB
  have hA' := congrArg (fun x : ℕ => (x : ℝ)) hA
  have hB' := congrArg (fun x : ℕ => (x : ℝ)) hB
  push_cast [Nat.cast_sub hh] at hA' hB'
  apply mul_right_cancel₀ (show ((h ! : ℕ) : ℝ) * ((L - h)! : ℕ) ≠ 0 by positivity)
  linear_combination ((L : ℝ) + 1) * ((L : ℝ) + 2) * ((L : ℝ) + 3) * hA' - hB'

lemma choose_id4 (L h : ℕ) (hh : h ≤ L) :
    (L.choose h : ℝ) * ((L + 1) * (L + 2) * (L + 3) * (L + 4)) =
      ((L + 4).choose (h + 2) : ℝ) * ((h + 1) * (h + 2) * (L - h + 1) * (L - h + 2)) := by
  have hA := Nat.choose_mul_factorial_mul_factorial hh
  have hB := Nat.choose_mul_factorial_mul_factorial (show h + 2 ≤ L + 4 by omega)
  rw [show L + 4 - (h + 2) = (L - h) + 1 + 1 by omega, Nat.factorial_succ (h + 1), Nat.factorial_succ h, Nat.factorial_succ (L - h + 1),
    Nat.factorial_succ (L - h), Nat.factorial_succ (L + 3),
    Nat.factorial_succ (L + 2),
    Nat.factorial_succ (L + 1), Nat.factorial_succ L] at hB
  have hA' := congrArg (fun x : ℕ => (x : ℝ)) hA
  have hB' := congrArg (fun x : ℕ => (x : ℝ)) hB
  push_cast [Nat.cast_sub hh] at hA' hB'
  apply mul_right_cancel₀ (show ((h ! : ℕ) : ℝ) * ((L - h)! : ℕ) ≠ 0 by positivity)
  linear_combination ((L : ℝ) + 1) * ((L : ℝ) + 2) * ((L : ℝ) + 3) * ((L : ℝ) + 4) * hA' - hB'

lemma choose_id3' (L h : ℕ) (hh : h ≤ L) :
    (L.choose h : ℝ) * ((L + 1) * (L + 2) * (L + 3)) =
      ((L + 3).choose (h + 2) : ℝ) * ((h + 1) * (h + 2) * (L - h + 1)) := by
  have hA := Nat.choose_mul_factorial_mul_factorial hh
  have hB := Nat.choose_mul_factorial_mul_factorial (show h + 2 ≤ L + 3 by omega)
  rw [show L + 3 - (h + 2) = (L - h) + 1 by omega, Nat.factorial_succ (h + 1), Nat.factorial_succ h, Nat.factorial_succ (L - h),
    Nat.factorial_succ (L + 2),
    Nat.factorial_succ (L + 1), Nat.factorial_succ L] at hB
  have hA' := congrArg (fun x : ℕ => (x : ℝ)) hA
  have hB' := congrArg (fun x : ℕ => (x : ℝ)) hB
  push_cast [Nat.cast_sub hh] at hA' hB'
  apply mul_right_cancel₀ (show ((h ! : ℕ) : ℝ) * ((L - h)! : ℕ) ≠ 0 by positivity)
  linear_combination ((L : ℝ) + 1) * ((L : ℝ) + 2) * ((L : ℝ) + 3) * hA' - hB'

lemma term_num {c c2 c3 c3' c4 A B P2 P3 P4 : ℝ} (hA : 1 ≤ A) (hB : 1 ≤ B) (hc : 0 ≤ c)
    (hP2 : 0 < P2) (hP3 : 0 < P3) (hP4 : 0 < P4)
    (I2 : c * P2 = c2 * (A * B)) (I3 : c * P3 = c3 * (A * B * (B + 1)))
    (I3' : c * P3 = c3' * (A * (A + 1) * B)) (I4 : c * P4 = c4 * (A * (A + 1) * B * (B + 1))) :
    c * ((A + 1) * (B + 1) / (A ^ 2 * B ^ 2)) ≤ c2 / P2 + 2 * c3 / P3 + 2 * c3' / P3 + 4 * c4 / P4 := by
  have hA0 : 0 < A := by linarith
  have hB0 : 0 < B := by linarith
  have e : c * ((A + 1) * (B + 1) / (A ^ 2 * B ^ 2)) =
      c / (A * B) + c / (A * B ^ 2) + c / (A ^ 2 * B) + c / (A ^ 2 * B ^ 2) := by
    field_simp; ring
  rw [e]
  have t1 : c / (A * B) = c2 / P2 := by
    rw [div_eq_div_iff (by positivity) hP2.ne']; linarith
  have hAB0 : 0 < A * B := mul_pos hA0 hB0
  have t2 : c / (A * B ^ 2) ≤ 2 * c3 / P3 := by
    have e2 : 2 * c3 / P3 = 2 * c / (A * B * (B + 1)) := by
      rw [div_eq_div_iff hP3.ne' (by positivity)]; linarith [I3]
    rw [e2, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_nonneg hc (mul_nonneg hAB0.le (sub_nonneg.mpr hB))]
  have t3 : c / (A ^ 2 * B) ≤ 2 * c3' / P3 := by
    have e3 : 2 * c3' / P3 = 2 * c / (A * (A + 1) * B) := by
      rw [div_eq_div_iff hP3.ne' (by positivity)]; linarith [I3']
    rw [e3, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_nonneg hc (mul_nonneg hAB0.le (sub_nonneg.mpr hA))]
  have t4 : c / (A ^ 2 * B ^ 2) ≤ 4 * c4 / P4 := by
    have e4 : 4 * c4 / P4 = 4 * c / (A * (A + 1) * B * (B + 1)) := by
      rw [div_eq_div_iff hP4.ne' (by positivity)]; linarith [I4]
    rw [e4, div_le_div_iff₀ (by positivity) (by positivity)]
    have hq : (A + 1) * (B + 1) ≤ 4 * (A * B) := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hA) (sub_nonneg.mpr hB)]
    have := mul_le_mul_of_nonneg_left hq (mul_nonneg hc hAB0.le)
    nlinarith
  linarith

/-- **upper bound** for `u_L`. -/
theorem u_upper (L : ℕ) :
    (N2 L 0 0 : ℝ) / 4 ^ L ≤ (4 / π) / (L + 1) * √(1 + 24 / (L + 1)) := by
  rw [u_eq]
  have hpi := Real.pi_pos
  set w : ℕ → ℝ := fun h => (L.choose h : ℝ) / 2 ^ L with hw
  have hw0 : ∀ h, 0 ≤ w h := fun h => by simp only [hw]; positivity
  have hwsum : ∑ h ∈ range (L + 1), w h = 1 := by
    simp only [hw]; rw [← sum_div]
    have : ∑ h ∈ range (L + 1), (L.choose h : ℝ) = 2 ^ L := by exact_mod_cast Nat.sum_range_choose L
    rw [this]; exact div_self (by positivity)
  -- R h = (h+2)(L-h+2)/((h+1)^2 (L-h+1)^2)
  set Rf : ℕ → ℝ := fun h => ((h : ℝ) + 2) * (L - h + 2) / (((h : ℝ) + 1) ^ 2 * (L - h + 1) ^ 2) with hRf
  have hbb : ∀ h ∈ range (L + 1), bb h * bb (L - h) ≤ (2 / π) * √(Rf h) := by
    intro h hh; rw [mem_range] at hh
    have a := (bb_sq_bounds h).2
    have b := (bb_sq_bounds (L - h)).2
    have hLh : ((L - h : ℕ) : ℝ) = L - h := by rw [Nat.cast_sub (by omega)]
    rw [hLh] at b
    have hh1 : (h : ℝ) ≤ L := by exact_mod_cast (show h ≤ L by omega)
    have sq : (bb h * bb (L - h)) ^ 2 ≤ ((2 / π) * √(Rf h)) ^ 2 := by
      rw [mul_pow, mul_pow, Real.sq_sqrt (by simp only [hRf]; apply div_nonneg <;> nlinarith)]
      have := mul_le_mul a b (by positivity) (by positivity)
      refine this.trans (le_of_eq ?_)
      simp only [hRf]; field_simp
    exact (pow_le_pow_iff_left₀ (mul_nonneg (bb_nonneg _) (bb_nonneg _)) (by positivity)
      two_ne_zero).mp sq
  -- Cauchy–Schwarz: ∑ w √R ≤ √(∑ w R)
  have hCS : ∑ h ∈ range (L + 1), w h * √(Rf h) ≤ √(∑ h ∈ range (L + 1), w h * Rf h) := by
    apply Real.le_sqrt_of_sq_le
    have key := Finset.sum_mul_sq_le_sq_mul_sq (range (L + 1)) (fun h => √(w h)) (fun h => √(w h) * √(Rf h))
    have e1 : ∑ h ∈ range (L + 1), √(w h) * (√(w h) * √(Rf h)) = ∑ h ∈ range (L + 1), w h * √(Rf h) := by
      apply sum_congr rfl; intro h _; rw [← mul_assoc, Real.mul_self_sqrt (hw0 h)]
    have e2 : ∑ h ∈ range (L + 1), √(w h) ^ 2 = 1 := by
      rw [← hwsum]; apply sum_congr rfl; intro h _; rw [Real.sq_sqrt (hw0 h)]
    have e3 : ∑ h ∈ range (L + 1), (√(w h) * √(Rf h)) ^ 2 ≤ ∑ h ∈ range (L + 1), w h * Rf h := by
      apply sum_le_sum; intro h hh; rw [mem_range] at hh
      have hh1 : (h : ℝ) ≤ L := by exact_mod_cast (show h ≤ L by omega)
      have hR0 : 0 ≤ Rf h := by simp only [hRf]; apply div_nonneg <;> nlinarith
      rw [mul_pow, Real.sq_sqrt (hw0 h), Real.sq_sqrt hR0]
    rw [e1, e2, one_mul] at key
    linarith
  -- the moment bound ∑ w R ≤ 4/((L+1)(L+2)) (1 + 24/(L+3))
  have hER : ∑ h ∈ range (L + 1), w h * Rf h ≤ 4 / ((L + 1 : ℝ) ^ 2) * (1 + 24 / (L + 1)) := by
    have per : ∀ h ∈ range (L + 1), w h * Rf h ≤
        (((L + 2).choose (h + 1) : ℝ) / ((L + 1) * (L + 2)) +
         2 * ((L + 3).choose (h + 1) : ℝ) / ((L + 1) * (L + 2) * (L + 3)) +
         2 * ((L + 3).choose (h + 2) : ℝ) / ((L + 1) * (L + 2) * (L + 3)) +
         4 * ((L + 4).choose (h + 2) : ℝ) / ((L + 1) * (L + 2) * (L + 3) * (L + 4))) / 2 ^ L := by
      intro h hh; rw [mem_range] at hh
      have hhL : h ≤ L := by omega
      have hh1 : (h : ℝ) ≤ L := by exact_mod_cast hhL
      have e : w h * Rf h = ((L.choose h : ℝ) * ((((h : ℝ) + 1) + 1) * ((L - h + 1) + 1) /
          (((h : ℝ) + 1) ^ 2 * (L - h + 1) ^ 2))) / 2 ^ L := by
        simp only [hw, hRf]; ring_nf
      rw [e]
      apply div_le_div_of_nonneg_right _ (by positivity)
      have := term_num (c := (L.choose h : ℝ)) (A := (h : ℝ) + 1) (B := (L : ℝ) - h + 1)
        (P2 := ((L : ℝ) + 1) * (L + 2)) (P3 := ((L : ℝ) + 1) * (L + 2) * (L + 3))
        (P4 := ((L : ℝ) + 1) * (L + 2) * (L + 3) * (L + 4))
        (by linarith [Nat.cast_nonneg (α := ℝ) h]) (by linarith) (by positivity)
        (by positivity) (by positivity) (by positivity)
        (choose_id2 L h hhL) (by rw [choose_id3 L h hhL]; ring) (by rw [choose_id3' L h hhL]; ring)
        (by rw [choose_id4 L h hhL]; ring)
      exact this
    refine (sum_le_sum per).trans ?_
    rw [← sum_div, sum_add_distrib, sum_add_distrib, sum_add_distrib, ← sum_div, ← sum_div, ← mul_sum,
      ← sum_div, ← mul_sum, ← sum_div, ← mul_sum]
    have s1 := row_partial (L + 2) (L + 1) 1
    have s2 := row_partial (L + 3) (L + 1) 1
    have s3 := row_partial (L + 3) (L + 1) 2
    have s4 := row_partial (L + 4) (L + 1) 2
    push_cast at s1 s2 s3 s4
    have hL0 : (0 : ℝ) ≤ L := by positivity
    have h2L : (0 : ℝ) < 2 ^ L := by positivity
    rw [div_le_iff₀ h2L]
    have b1 : (∑ h ∈ range (L + 1), ((L + 2).choose (h + 1) : ℝ)) / ((L + 1) * (L + 2)) ≤
        2 ^ (L + 2) / ((L + 1) * (L + 2)) := by (gcongr)
    have b2 : 2 * (∑ h ∈ range (L + 1), ((L + 3).choose (h + 1) : ℝ)) / ((L + 1) * (L + 2) * (L + 3)) ≤
        2 * 2 ^ (L + 3) / ((L + 1) * (L + 2) * (L + 3)) := by (gcongr)
    have b3 : 2 * (∑ h ∈ range (L + 1), ((L + 3).choose (h + 2) : ℝ)) / ((L + 1) * (L + 2) * (L + 3)) ≤
        2 * 2 ^ (L + 3) / ((L + 1) * (L + 2) * (L + 3)) := by (gcongr)
    have b4 : 4 * (∑ h ∈ range (L + 1), ((L + 4).choose (h + 2) : ℝ)) / ((L + 1) * (L + 2) * (L + 3) * (L + 4)) ≤
        4 * 2 ^ (L + 4) / ((L + 1) * (L + 2) * (L + 3) * (L + 4)) := by (gcongr)
    have fin : 2 ^ (L + 2) / ((L + 1 : ℝ) * (L + 2)) + 2 * 2 ^ (L + 3) / ((L + 1) * (L + 2) * (L + 3)) +
        2 * 2 ^ (L + 3) / ((L + 1) * (L + 2) * (L + 3)) + 4 * 2 ^ (L + 4) / ((L + 1) * (L + 2) * (L + 3) * (L + 4))
        ≤ 4 / ((L + 1 : ℝ) ^ 2) * (1 + 24 / (L + 1)) * 2 ^ L := by
      rw [pow_add, pow_add, pow_add]
      have : (2 : ℝ) ^ L * 2 ^ 2 / ((L + 1) * (L + 2)) + 2 * (2 ^ L * 2 ^ 3) / ((L + 1) * (L + 2) * (L + 3)) +
          2 * (2 ^ L * 2 ^ 3) / ((L + 1) * (L + 2) * (L + 3)) + 4 * (2 ^ L * 2 ^ 4) / ((L + 1) * (L + 2) * (L + 3) * (L + 4))
          = 2 ^ L * (4 / ((L + 1) * (L + 2)) + 32 / ((L + 1) * (L + 2) * (L + 3)) +
            64 / ((L + 1) * (L + 2) * (L + 3) * (L + 4))) := by ring
      rw [this, mul_comm]
      apply mul_le_mul_of_nonneg_right _ h2L.le
      rw [div_add_div _ _ (by positivity) (by positivity), div_add_div _ _ (by positivity) (by positivity),
        div_le_iff₀ (by positivity)]
      field_simp
      nlinarith [mul_nonneg hL0 hL0, mul_nonneg (mul_nonneg hL0 hL0) hL0,
        mul_nonneg (mul_nonneg (mul_nonneg hL0 hL0) hL0) hL0]
    linarith
  have hfin : ∑ h ∈ range (L + 1), w h * (bb h * bb (L - h)) ≤
      (2 / π) * √(4 / ((L + 1 : ℝ) ^ 2) * (1 + 24 / (L + 1))) := by
    calc ∑ h ∈ range (L + 1), w h * (bb h * bb (L - h))
        ≤ ∑ h ∈ range (L + 1), w h * ((2 / π) * √(Rf h)) :=
          sum_le_sum (fun h hh => mul_le_mul_of_nonneg_left (hbb h hh) (hw0 h))
      _ = (2 / π) * ∑ h ∈ range (L + 1), w h * √(Rf h) := by
          rw [mul_sum]; apply sum_congr rfl; intro h _; ring
      _ ≤ (2 / π) * √(∑ h ∈ range (L + 1), w h * Rf h) := by (gcongr)
      _ ≤ (2 / π) * √(4 / ((L + 1 : ℝ) ^ 2) * (1 + 24 / (L + 1))) := by (gcongr)
  refine hfin.trans (le_of_eq ?_)
  rw [Real.sqrt_mul (by positivity), show (4 : ℝ) / (L + 1) ^ 2 = (2 / (L + 1)) ^ 2 by rw [div_pow]; norm_num,
    Real.sqrt_sq (by positivity)]
  ring

end E521

end S_C20

-- ===== C21 =====
section S_C21

/-! Endpoint estimates for the quadrant walk (original). -/

open Finset Real

namespace E521

lemma N1F_parity (h : ℕ) : ∀ (u y : ℤ), N1F (· = y) h u ≠ 0 → Even (u + h - y) := by
  induction h with
  | zero =>
    intro u y hne
    rw [N1F_zero] at hne
    split_ifs at hne with hc
    · rw [hc.2]; simp
    · exact absurd rfl hne
  | succ h ih =>
    intro u y hne
    by_cases hu : 0 ≤ u
    · rw [N1F_succ _ h hu] at hne
      rcases Nat.eq_zero_or_pos (N1F (· = y) h (u + 1)) with h1 | h1
      · rw [h1, zero_add] at hne
        have := ih (u - 1) y hne
        have e : u + ((h + 1 : ℕ) : ℤ) - y = (u - 1 + h - y) + 2 := by push_cast; ring
        rw [e]; exact this.add (by decide)
      · have := ih (u + 1) y (by omega)
        have e : u + ((h + 1 : ℕ) : ℤ) - y = u + 1 + h - y := by push_cast; ring
        rw [e]; exact this
    · exact absurd (N1F_neg _ _ (not_le.mp hu)) hne

lemma N1F_true (L : ℕ) : ∀ u : ℤ, N1F (fun _ => True) L u = N1 L u := by
  induction L with
  | zero =>
    intro u; rw [N1F_zero]
    unfold N1
    by_cases hu : 0 ≤ u
    · rw [if_pos ⟨hu, trivial⟩]
      rw [eq_comm, card_eq_one]; refine ⟨default, ?_⟩
      ext p
      have hp : p = default := Subsingleton.elim _ _
      simp only [mem_filter, mem_univ, true_and, mem_singleton]
      constructor
      · intro _; exact hp
      · intro _; first | exact hu | simp [good1, hu] | (simp only [Set.mem_setOf_eq]; simp [good1, hu])
    · rw [if_neg (fun h : 0 ≤ u ∧ _ => hu h.1)]
      have := N1_neg 0 (not_le.mp hu); unfold N1 at this; rw [this]
  | succ L ih =>
    intro u
    by_cases hu : 0 ≤ u
    · rw [N1F_succ _ L hu, N1_succ L hu, ih, ih]
    · rw [N1F_neg _ _ (not_le.mp hu), N1_neg _ (not_le.mp hu)]

lemma N1F_sum (S : Finset ℤ) (L : ℕ) : ∀ u : ℤ,
    N1F (· ∈ S) L u = ∑ y ∈ S, N1F (· = y) L u := by
  induction L with
  | zero =>
    intro u
    rw [N1F_zero]
    simp_rw [N1F_zero]
    by_cases hu : 0 ≤ u
    · by_cases huS : u ∈ S
      · rw [if_pos ⟨hu, huS⟩, sum_eq_single u]
        · rw [if_pos ⟨hu, rfl⟩]
        · intro y _ hy; rw [if_neg (fun h : 0 ≤ u ∧ u = y => hy h.2.symm)]
        · intro h; exact absurd huS h
      · rw [if_neg (fun h => huS h.2)]
        symm; apply sum_eq_zero; intro y hy
        rw [if_neg (fun h : 0 ≤ u ∧ u = y => huS (by rw [h.2]; exact hy))]
    · rw [if_neg (fun h : 0 ≤ u ∧ _ => hu h.1)]
      symm; apply sum_eq_zero; intro y _; rw [if_neg (fun h : 0 ≤ u ∧ u = y => hu h.1)]
  | succ L ih =>
    intro u
    by_cases hu : 0 ≤ u
    · rw [N1F_succ _ L hu, ih, ih]
      simp_rw [N1F_succ _ L hu]
      rw [sum_add_distrib]
    · rw [N1F_neg _ _ (not_le.mp hu)]
      symm; apply sum_eq_zero; intro y _; exact N1F_neg _ _ (not_le.mp hu)

lemma choose_le_cc (h k : ℕ) : h.choose k ≤ cc h := by
  unfold cc
  have h1 := Nat.choose_le_middle k h
  have h2 : h.choose ((h + 1) / 2) = h.choose (h / 2) := by
    rcases Nat.even_or_odd' h with ⟨p, rfl | rfl⟩
    · congr 1; omega
    · rw [show (2 * p + 1 + 1) / 2 = p + 1 by omega, show (2 * p + 1) / 2 = p by omega]
      exact Nat.choose_symm_of_eq_add (by omega)
  rw [h2]; exact h1

/-- endpoint (ballot) bound from the origin: `N1F(·=y) h 0 · (h+2) ≤ 2 (y+1) cc h`. -/
lemma endpoint_bound (h y : ℕ) :
    (N1F (· = (y : ℤ)) h 0 : ℝ) * (h + 2) ≤ 2 * (y + 1) * cc h := by
  by_cases hne : N1F (· = (y : ℤ)) h 0 = 0
  · rw [hne]; simp; positivity
  have hpar := N1F_parity h 0 y hne
  obtain ⟨r, hr⟩ := hpar
  -- k = (h + y)/2
  have hk : ((h : ℤ) + y) = 2 * (y + r) := by omega
  set k : ℤ := y + r with hk_def
  have hy : (0 : ℤ) ≤ ((0 : ℕ) : ℤ) + 2 * k - h := by push_cast; omega
  have hb := ballot h 0 k hy
  have hfin : ((0 : ℕ) : ℤ) + 2 * k - h = (y : ℤ) := by push_cast; omega
  rw [hfin] at hb
  -- k ≥ 0, k ≤ h
  have hk0 : 0 ≤ k := by omega
  have hkn : k.toNat ≤ h ∨ h < k.toNat := le_or_gt _ _
  push_cast at hb
  simp only [add_zero] at hb
  have hchZ1 : chZ h k = (h.choose k.toNat : ℤ) := by unfold chZ; rw [if_neg (by omega)]
  have hchZ2 : chZ h (k + 1) = (h.choose (k.toNat + 1) : ℤ) := by
    unfold chZ; rw [if_neg (by omega)]; congr 2; omega
  rw [hchZ1, hchZ2] at hb
  have hid := Nat.choose_succ_right_eq h k.toNat
  -- (k+1)(C(h,k) - C(h,k+1)) = C(h,k)(2k+1-h) = C(h,k)(y+1)
  have hN : (N1F (· = (y : ℤ)) h 0 : ℝ) = (h.choose k.toNat : ℝ) - h.choose (k.toNat + 1) := by
    exact_mod_cast hb
  have hktn : ((k.toNat : ℕ) : ℝ) = (k : ℝ) := by exact_mod_cast Int.toNat_of_nonneg hk0
  have hkr : 2 * (k : ℝ) = h + y := by exact_mod_cast (show 2 * k = (h : ℤ) + y by omega)
  have hidr : ((h.choose (k.toNat + 1) : ℕ) : ℝ) * (k + 1) = (h.choose k.toNat : ℝ) * (h - k) := by
    have : ((h.choose (k.toNat + 1) * (k.toNat + 1) : ℕ) : ℝ) = ((h.choose k.toNat * (h - k.toNat) : ℕ) : ℝ) := by
      exact_mod_cast hid
    push_cast at this
    by_cases hkh : k.toNat ≤ h
    · rw [Nat.cast_sub hkh, hktn] at this; linarith
    · have hz : h.choose k.toNat = 0 := Nat.choose_eq_zero_of_lt (by omega)
      have hz2 : h.choose (k.toNat + 1) = 0 := Nat.choose_eq_zero_of_lt (by omega)
      rw [hz, hz2]; simp
  have key : (N1F (· = (y : ℤ)) h 0 : ℝ) * (k + 1) = (h.choose k.toNat : ℝ) * (y + 1) := by
    rw [hN, sub_mul, hidr]; nlinarith
  have hC := choose_le_cc h k.toNat
  have hCr : (h.choose k.toNat : ℝ) ≤ cc h := by exact_mod_cast hC
  have hk1 : ((h : ℝ) + 2) ≤ 2 * (k + 1) := by linarith [show (0:ℝ) ≤ y by positivity]
  have hN0 : (0 : ℝ) ≤ N1F (· = (y : ℤ)) h 0 := by positivity
  calc (N1F (· = (y : ℤ)) h 0 : ℝ) * (h + 2) ≤ (N1F (· = (y : ℤ)) h 0 : ℝ) * (2 * (k + 1)) :=
        mul_le_mul_of_nonneg_left hk1 hN0
    _ = 2 * ((h.choose k.toNat : ℝ) * (y + 1)) := by rw [← key]; ring
    _ ≤ 2 * (cc h * (y + 1)) := by (gcongr)
    _ = 2 * (y + 1) * cc h := by ring

end E521

end S_C21

-- ===== C22 =====
section S_C22

/-! The quadrant walk rarely ends near an axis (original). -/

open Finset Real
open scoped Nat

namespace E521

lemma N1F_or (F G : ℤ → Prop) [DecidablePred F] [DecidablePred G] (hdis : ∀ y, ¬ (F y ∧ G y)) (L : ℕ) :
    ∀ u : ℤ, N1F (fun y => F y ∨ G y) L u = N1F F L u + N1F G L u := by
  induction L with
  | zero =>
    intro u
    rw [N1F_zero, N1F_zero, N1F_zero]
    by_cases hu : 0 ≤ u
    · by_cases hF : F u
      · rw [if_pos ⟨hu, Or.inl hF⟩, if_pos ⟨hu, hF⟩, if_neg (fun h : 0 ≤ u ∧ G u => hdis u ⟨hF, h.2⟩)]
      · by_cases hG : G u
        · rw [if_pos ⟨hu, Or.inr hG⟩, if_neg (fun h : 0 ≤ u ∧ F u => hF h.2), if_pos ⟨hu, hG⟩]
        · rw [if_neg (fun h : 0 ≤ u ∧ (F u ∨ G u) => h.2.elim hF hG), if_neg (fun h : 0 ≤ u ∧ F u => hF h.2), if_neg (fun h : 0 ≤ u ∧ G u => hG h.2)]
    · rw [if_neg (fun h : 0 ≤ u ∧ _ => hu h.1), if_neg (fun h : 0 ≤ u ∧ _ => hu h.1), if_neg (fun h : 0 ≤ u ∧ _ => hu h.1)]
  | succ L ih =>
    intro u
    by_cases hu : 0 ≤ u
    · rw [N1F_succ _ L hu, N1F_succ _ L hu, N1F_succ _ L hu, ih, ih]; ring
    · rw [N1F_neg _ _ (not_le.mp hu), N1F_neg _ _ (not_le.mp hu), N1F_neg _ _ (not_le.mp hu)]

lemma choose_id3b (L h : ℕ) (hh : h ≤ L) :
    (L.choose h : ℝ) * ((L + 1) * (L + 2) * (L + 3)) =
      ((L + 3).choose (h + 3) : ℝ) * ((h + 1) * (h + 2) * (h + 3)) := by
  rw [Nat.cast_choose ℝ hh, Nat.cast_choose ℝ (show h + 3 ≤ L + 3 by omega)]
  have e : L + 3 - (h + 3) = L - h := by omega
  rw [e, show L + 3 = (L + 2) + 1 by ring, Nat.factorial_succ (L + 2), show L + 2 = (L + 1) + 1 by ring,
    Nat.factorial_succ (L + 1), Nat.factorial_succ L, show h + 3 = (h + 2) + 1 by ring,
    Nat.factorial_succ (h + 2), show h + 2 = (h + 1) + 1 by ring, Nat.factorial_succ (h + 1),
    Nat.factorial_succ h]
  have h1 : (0 : ℝ) < h ! := by exact_mod_cast Nat.factorial_pos h
  have h2 : (0 : ℝ) < (L - h)! := by exact_mod_cast Nat.factorial_pos (L - h)
  push_cast
  field_simp
  ring

/-- `P(quadrant ∧ U_end ≤ x) ≤ 2√24 (x+1)²/(L+1)²`. -/
theorem end_small (L x : ℕ) :
    (N2F (· ∈ Icc (0 : ℤ) x) (fun _ => True) L 0 0 : ℝ) / 4 ^ L ≤ 2 * √24 * ((x : ℝ) + 1) ^ 2 / (L + 1) ^ 2 := by
  rw [N2F_eq]
  push_cast
  -- bound each term
  have hterm : ∀ h ∈ range (L + 1), (L.choose h : ℝ) * ((N1F (· ∈ Icc (0 : ℤ) x) h 0 : ℝ) *
      (N1F (fun _ => True) (L - h) 0 : ℝ)) ≤
      (L.choose h : ℝ) * (2 * ((x : ℝ) + 1) ^ 2 * cc h / (h + 2) * cc (L - h)) := by
    intro h _
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have e1 : (N1F (fun _ => True) (L - h) 0 : ℝ) = cc (L - h) := by
      rw [N1F_true]
      have := N1_eq_Wn (L - h) 0
      simp only [Nat.cast_zero] at this
      rw [this, Wn_zero_start]; rfl
    rw [e1]
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    rw [N1F_sum]
    push_cast
    rw [le_div_iff₀ (by positivity), sum_mul]
    have : ∀ y ∈ Icc (0 : ℤ) x, (N1F (· = y) h 0 : ℝ) * (h + 2) ≤ 2 * ((x : ℝ) + 1) * cc h := by
      intro y hy
      rw [mem_Icc] at hy
      have hy0 : y = ((y.toNat : ℕ) : ℤ) := by omega
      rw [hy0]
      refine (endpoint_bound h y.toNat).trans ?_
      (gcongr)
      have : (y.toNat : ℝ) ≤ x := by exact_mod_cast (show y.toNat ≤ x by omega)
      linarith
    calc ∑ y ∈ Icc (0 : ℤ) x, (N1F (· = y) h 0 : ℝ) * (h + 2)
        ≤ ∑ y ∈ Icc (0 : ℤ) x, 2 * ((x : ℝ) + 1) * cc h := sum_le_sum this
      _ = ((x : ℝ) + 1) * (2 * ((x : ℝ) + 1) * cc h) := by
          rw [sum_const, Int.card_Icc, nsmul_eq_mul, show ((x : ℤ) + 1 - 0).toNat = x + 1 by omega]
          push_cast; ring
      _ = 2 * ((x : ℝ) + 1) ^ 2 * cc h := by ring
  refine (div_le_div_of_nonneg_right (sum_le_sum hterm) (by positivity)).trans ?_
  -- normalize: ∑ w_h · 2(x+1)² bb_h bb_{L-h}/(h+2), with bb_h ≤ 1/√(h+1)
  set w : ℕ → ℝ := fun h => (L.choose h : ℝ) / 2 ^ L with hw
  have hw0 : ∀ h, 0 ≤ w h := fun h => by simp only [hw]; positivity
  have e1 : (∑ h ∈ range (L + 1), (L.choose h : ℝ) * (2 * ((x : ℝ) + 1) ^ 2 * cc h / (h + 2) * cc (L - h))) / 4 ^ L
      = 2 * ((x : ℝ) + 1) ^ 2 * ∑ h ∈ range (L + 1), w h * (bb h * bb (L - h) / (h + 2)) := by
    rw [sum_div, mul_sum]
    apply sum_congr rfl; intro h hh; rw [mem_range] at hh
    simp only [hw, bb]
    have : (4 : ℝ) ^ L = 2 ^ L * (2 ^ h * 2 ^ (L - h)) := by
      rw [← pow_add, ← pow_add, show h + (L - h) = L by omega, ← two_mul, pow_mul]; norm_num
    rw [this]; field_simp
  rw [e1]
  have hbb : ∀ h, bb h ≤ 1 / √((h : ℝ) + 1) := by
    intro h
    have := cc_upper h
    unfold bb
    rw [div_le_div_iff₀ (by positivity) (by positivity), one_mul]
    have h2 : ((cc h : ℝ) * √((h : ℝ) + 1)) ^ 2 ≤ ((2 : ℝ) ^ h) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (by positivity), ← pow_mul, mul_comm h 2, pow_mul]; norm_num; linarith
    exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).mp h2
  -- g h = 1/((h+2) √(h+1) √(L-h+1))
  have hg : ∀ h ∈ range (L + 1), w h * (bb h * bb (L - h) / (h + 2)) ≤
      √(w h) * (1 / (((h : ℝ) + 2) * √((h : ℝ) + 1))) * (√(w h) * (1 / √(((L - h : ℕ) : ℝ) + 1))) := by
    intro h _
    have e2 : √(w h) * (1 / (((h : ℝ) + 2) * √((h : ℝ) + 1))) * (√(w h) * (1 / √(((L - h : ℕ) : ℝ) + 1))) =
        w h * ((1 / √((h : ℝ) + 1)) * (1 / √(((L - h : ℕ) : ℝ) + 1)) / (h + 2)) := by
      rw [show √(w h) * (1 / (((h : ℝ) + 2) * √((h : ℝ) + 1))) * (√(w h) * (1 / √(((L - h : ℕ) : ℝ) + 1))) =
        (√(w h) * √(w h)) * ((1 / √((h : ℝ) + 1)) * (1 / √(((L - h : ℕ) : ℝ) + 1)) / (h + 2)) by
          field_simp]
      rw [Real.mul_self_sqrt (hw0 h)]
    rw [e2]
    apply mul_le_mul_of_nonneg_left _ (hw0 h)
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact mul_le_mul (hbb h) (hbb (L - h)) (bb_nonneg _) (by positivity)
  have hCS := Finset.sum_mul_sq_le_sq_mul_sq (range (L + 1))
    (fun h => √(w h) * (1 / (((h : ℝ) + 2) * √((h : ℝ) + 1))))
    (fun h => √(w h) * (1 / √(((L - h : ℕ) : ℝ) + 1)))
  have hA : ∑ h ∈ range (L + 1), (√(w h) * (1 / (((h : ℝ) + 2) * √((h : ℝ) + 1)))) ^ 2 ≤
      12 / ((L : ℝ) + 1) ^ 3 := by
    have per : ∀ h ∈ range (L + 1), (√(w h) * (1 / (((h : ℝ) + 2) * √((h : ℝ) + 1)))) ^ 2 ≤
        (3 / 2) * (((L + 3).choose (h + 3) : ℝ) / ((L + 1) * (L + 2) * (L + 3))) / 2 ^ L := by
      intro h hh; rw [mem_range] at hh
      rw [mul_pow, Real.sq_sqrt (hw0 h), div_pow, one_pow, mul_pow, Real.sq_sqrt (by positivity)]
      have hid := choose_id3b L h (by omega)
      simp only [hw]
      have hq : ((L + 3).choose (h + 3) : ℝ) / ((L + 1) * (L + 2) * (L + 3)) =
          (L.choose h : ℝ) / ((h + 1) * (h + 2) * (h + 3)) := by
        rw [div_eq_div_iff (by positivity) (by positivity)]; linarith [hid]
      rw [hq]
      have lhs : (L.choose h : ℝ) / 2 ^ L * (1 / (((h : ℝ) + 2) ^ 2 * ((h : ℝ) + 1))) =
          (L.choose h : ℝ) * 1 / (2 ^ L * (((h : ℝ) + 2) ^ 2 * ((h : ℝ) + 1))) := by
        rw [div_mul_div_comm]
      have rhs : (3 / 2 : ℝ) * ((L.choose h : ℝ) / (((h : ℝ) + 1) * ((h : ℝ) + 2) * ((h : ℝ) + 3))) / 2 ^ L =
          3 * (L.choose h : ℝ) / (2 * (((h : ℝ) + 1) * ((h : ℝ) + 2) * ((h : ℝ) + 3)) * 2 ^ L) := by
        rw [div_mul_div_comm, div_div]
      rw [lhs, rhs, div_le_div_iff₀ (by positivity) (by positivity)]
      have hpos : 0 ≤ (L.choose h : ℝ) * 2 ^ L * (((h : ℝ) + 1) * ((h : ℝ) + 2)) * h := by positivity
      nlinarith [hpos]
    refine (sum_le_sum per).trans ?_
    rw [← sum_div, ← mul_sum, ← sum_div]
    have hs := row_partial (L + 3) (L + 1) 3
    push_cast at hs
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have : (3 / 2 : ℝ) * ((∑ h ∈ range (L + 1), ((L + 3).choose (h + 3) : ℝ)) / ((L + 1) * (L + 2) * (L + 3))) *
        ((L : ℝ) + 1) ^ 3 ≤ (3 / 2) * (2 ^ (L + 3) / ((L + 1) * (L + 2) * (L + 3))) * ((L : ℝ) + 1) ^ 3 := by
      (gcongr)
    refine this.trans ?_
    have hL0 : (0 : ℝ) ≤ L := by positivity
    have hP : (0 : ℝ) < ((L : ℝ) + 1) * (L + 2) * (L + 3) := by positivity
    have e : (3 / 2 : ℝ) * (2 ^ (L + 3) / (((L : ℝ) + 1) * (L + 2) * (L + 3))) * ((L : ℝ) + 1) ^ 3 =
        12 * 2 ^ L * (((L : ℝ) + 1) ^ 3 / (((L : ℝ) + 1) * (L + 2) * (L + 3))) := by
      rw [pow_add]; ring
    rw [e]
    have hfrac : ((L : ℝ) + 1) ^ 3 / (((L : ℝ) + 1) * (L + 2) * (L + 3)) ≤ 1 := by
      rw [div_le_one hP]; nlinarith [hL0]
    have h2 : (0 : ℝ) < 12 * 2 ^ L := by positivity
    calc _ ≤ 12 * 2 ^ L * 1 := mul_le_mul_of_nonneg_left hfrac h2.le
      _ = 12 * 2 ^ L := mul_one _
  have hB : ∑ h ∈ range (L + 1), (√(w h) * (1 / √(((L - h : ℕ) : ℝ) + 1))) ^ 2 ≤ 2 / ((L : ℝ) + 1) := by
    have e3 : ∑ h ∈ range (L + 1), (√(w h) * (1 / √(((L - h : ℕ) : ℝ) + 1))) ^ 2 =
        (∑ h ∈ range (L + 1), (L.choose h : ℝ) / (h + 1)) / 2 ^ L := by
      rw [← sum_range_reflect (fun h => (L.choose h : ℝ) / (h + 1)), sum_div]
      apply sum_congr rfl; intro h hh; rw [mem_range] at hh
      rw [mul_pow, Real.sq_sqrt (hw0 h), div_pow, one_pow, Real.sq_sqrt (by positivity)]
      simp only [hw]
      rw [show L + 1 - 1 - h = L - h by omega, Nat.choose_symm (by omega)]
      field_simp
    rw [e3]
    have := sum_choose_div L
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    rw [le_div_iff₀ (by positivity)] at this
    rw [pow_succ] at this
    nlinarith [pow_pos (show (0:ℝ) < 2 by norm_num) L]
  have hsum : ∑ h ∈ range (L + 1), w h * (bb h * bb (L - h) / (h + 2)) ≤ √24 / ((L : ℝ) + 1) ^ 2 := by
    refine (sum_le_sum hg).trans ?_
    have hnn : 0 ≤ ∑ h ∈ range (L + 1), √(w h) * (1 / (((h : ℝ) + 2) * √((h : ℝ) + 1))) *
        (√(w h) * (1 / √(((L - h : ℕ) : ℝ) + 1))) := sum_nonneg (fun h _ => by positivity)
    have hsq : (∑ h ∈ range (L + 1), √(w h) * (1 / (((h : ℝ) + 2) * √((h : ℝ) + 1))) *
        (√(w h) * (1 / √(((L - h : ℕ) : ℝ) + 1)))) ^ 2 ≤ (√24 / ((L : ℝ) + 1) ^ 2) ^ 2 := by
      refine hCS.trans ?_
      calc _ ≤ 12 / ((L : ℝ) + 1) ^ 3 * (2 / ((L : ℝ) + 1)) :=
            mul_le_mul hA hB (sum_nonneg (fun _ _ => by positivity)) (by positivity)
        _ = (√24 / ((L : ℝ) + 1) ^ 2) ^ 2 := by
            rw [div_pow, Real.sq_sqrt (by norm_num)]; field_simp; ring
    exact (pow_le_pow_iff_left₀ hnn (by positivity) two_ne_zero).mp hsq
  have := mul_le_mul_of_nonneg_left hsum (show (0 : ℝ) ≤ 2 * ((x : ℝ) + 1) ^ 2 by positivity)
  refine this.trans (le_of_eq ?_)
  ring

end E521

end S_C22

-- ===== C23 =====
section S_C23

/-! The cone with large final coordinates keeps almost all of the quadrant mass (original). -/

open Finset Real

namespace E521

lemma N1F_congr (F G : ℤ → Prop) [DecidablePred F] [DecidablePred G] (hFG : ∀ y, 0 ≤ y → (F y ↔ G y))
    (L : ℕ) : ∀ u : ℤ, N1F F L u = N1F G L u := by
  induction L with
  | zero =>
    intro u; rw [N1F_zero, N1F_zero]
    by_cases hu : 0 ≤ u
    · by_cases hF : F u
      · rw [if_pos ⟨hu, hF⟩, if_pos ⟨hu, (hFG u hu).mp hF⟩]
      · rw [if_neg (fun h : 0 ≤ u ∧ F u => hF h.2), if_neg (fun h : 0 ≤ u ∧ G u => hF ((hFG u hu).mpr h.2))]
    · rw [if_neg (fun h : 0 ≤ u ∧ _ => hu h.1), if_neg (fun h : 0 ≤ u ∧ _ => hu h.1)]
  | succ L ih =>
    intro u
    by_cases hu : 0 ≤ u
    · rw [N1F_succ _ L hu, N1F_succ _ L hu, ih, ih]
    · rw [N1F_neg _ _ (not_le.mp hu), N1F_neg _ _ (not_le.mp hu)]

lemma N1_split (lam : ℕ) (hlam : 1 ≤ lam) (L : ℕ) (u : ℤ) :
    N1 L u = N1F (fun y => (lam : ℤ) ≤ y) L u + N1F (· ∈ Icc (0 : ℤ) ((lam - 1 : ℕ) : ℤ)) L u := by
  rw [← N1F_true, ← N1F_or _ _ (fun y h => by
    rcases h with ⟨h1, h2⟩; rw [mem_Icc] at h2; omega)]
  apply N1F_congr
  intro y hy
  simp only [true_iff, mem_Icc]
  omega

/-- the final-coordinate restriction costs at most `4√24 λ²/(K+1)²`. -/
theorem cone_plus_lower (K lam : ℕ) (hlam : 1 ≤ lam) :
    (N2 K 0 0 : ℝ) / 4 ^ K - 4 * √24 * (lam : ℝ) ^ 2 / (K + 1) ^ 2 ≤
      (N2F (fun y => (lam : ℤ) ≤ y) (fun y => (lam : ℤ) ≤ y) K 0 0 : ℝ) / 4 ^ K := by
  have hN2 : (N2 K 0 0 : ℝ) ≤ N2F (fun y => (lam : ℤ) ≤ y) (fun y => (lam : ℤ) ≤ y) K 0 0 + N2F (· ∈ Icc (0 : ℤ) ((lam - 1 : ℕ) : ℤ)) (fun _ => True) K 0 0
      + N2F (fun _ => True) (· ∈ Icc (0 : ℤ) ((lam - 1 : ℕ) : ℤ)) K 0 0 := by
    rw [N2_eq, N2F_eq, N2F_eq, N2F_eq]
    push_cast
    rw [← sum_add_distrib, ← sum_add_distrib]
    apply sum_le_sum; intro h _
    rw [N1_split lam hlam h 0, N1_split lam hlam (K - h) 0, N1F_true, N1F_true, N1_split lam hlam h 0,
      N1_split lam hlam (K - h) 0]
    push_cast
    have hc := Nat.cast_nonneg (α := ℝ) (K.choose h)
    have a1 := Nat.cast_nonneg (α := ℝ) (N1F (fun y => (lam : ℤ) ≤ y) h 0)
    have a2 := Nat.cast_nonneg (α := ℝ) (N1F (· ∈ Icc (0 : ℤ) ((lam - 1 : ℕ) : ℤ)) h 0)
    have a3 := Nat.cast_nonneg (α := ℝ) (N1F (fun y => (lam : ℤ) ≤ y) (K - h) 0)
    have a4 := Nat.cast_nonneg (α := ℝ) (N1F (· ∈ Icc (0 : ℤ) ((lam - 1 : ℕ) : ℤ)) (K - h) 0)
    have := mul_nonneg hc (mul_nonneg a2 a4)
    nlinarith
  have hx : ((lam - 1 : ℕ) : ℝ) + 1 = lam := by rw [Nat.cast_sub hlam]; push_cast; ring
  have e1 := end_small K (lam - 1)
  rw [hx] at e1
  have e2 : (N2F (fun _ => True) (· ∈ Icc (0 : ℤ) ((lam - 1 : ℕ) : ℤ)) K 0 0 : ℝ) = N2F (· ∈ Icc (0 : ℤ) ((lam - 1 : ℕ) : ℤ)) (fun _ => True) K 0 0 := by
    rw [N2F_eq, N2F_eq]
    push_cast
    rw [← sum_range_reflect]
    apply sum_congr rfl; intro h hh; rw [mem_range] at hh
    rw [show K + 1 - 1 - h = K - h by omega, show K - (K - h) = h by omega, Nat.choose_symm (by omega)]
    ring
  rw [e2] at hN2
  have h4 : (0 : ℝ) < 4 ^ K := by positivity
  have key : (N2 K 0 0 : ℝ) / 4 ^ K ≤ (N2F (fun y => (lam : ℤ) ≤ y) (fun y => (lam : ℤ) ≤ y) K 0 0 : ℝ) / 4 ^ K + (N2F (· ∈ Icc (0 : ℤ) ((lam - 1 : ℕ) : ℤ)) (fun _ => True) K 0 0 : ℝ) / 4 ^ K
      + (N2F (· ∈ Icc (0 : ℤ) ((lam - 1 : ℕ) : ℤ)) (fun _ => True) K 0 0 : ℝ) / 4 ^ K := by
    rw [← add_div, ← add_div]
    exact div_le_div_of_nonneg_right hN2 h4.le
  have e1' : (N2F (· ∈ Icc (0 : ℤ) ((lam - 1 : ℕ) : ℤ)) (fun _ => True) K 0 0 : ℝ) / 4 ^ K ≤ 2 * √24 * (lam : ℝ) ^ 2 / (K + 1) ^ 2 := e1
  have : 2 * √24 * (lam : ℝ) ^ 2 / (K + 1) ^ 2 + 2 * √24 * (lam : ℝ) ^ 2 / (K + 1) ^ 2 =
      4 * √24 * (lam : ℝ) ^ 2 / (K + 1) ^ 2 := by ring
  linarith

end E521

end S_C23

-- ===== P9 =====
section S_P9

/-! The good event `H_K` and its probability (original). Parameters for `n = 2K - 1`:
`t = ⌊n^{19/20}⌋`, `λ = ⌈n^{39/80}⌉`, count threshold `A = c' log n` with `c' = 63/100`. -/

open Finset MeasureTheory Filter Topology

noncomputable section

namespace E521

def tK (K : ℕ) : ℕ := ⌊((2 * K - 1 : ℕ) : ℝ) ^ ((19 : ℝ) / 20)⌋₊
def lamK (K : ℕ) : ℕ := ⌈((2 * K - 1 : ℕ) : ℝ) ^ ((39 : ℝ) / 80)⌉₊
def pK (K : ℕ) : ℕ := (2 * K - 1) - tK K
def AK (K : ℕ) : ℝ := (63 / 100) * Real.log ((2 * K - 1 : ℕ) : ℝ)

/-- the tail events. -/
def Gev (K : ℕ) : Set (ℕ → Bool) :=
  {ω | ∀ l ≤ tK K, |∑ i ∈ range l, eR ω (2 * K - 1 - i)| < 2 * (lamK K : ℝ) - 1}
def Gev' (K : ℕ) : Set (ℕ → Bool) :=
  {ω | ∀ l ≤ tK K, |∑ i ∈ range l, (-1) ^ i * eR ω (2 * K - 1 - i)| < 2 * (lamK K : ℝ) - 1}

/-- the sign-change count before `p`. -/
def cnt (K : ℕ) (ω : ℕ → Bool) : ℕ :=
  ((range (pK K)).filter (fun k => ω ∈ Iev k)).card + ((range (pK K)).filter (fun k => ω ∈ Ialt k)).card

def Cplus (K : ℕ) : Set (ℕ → Bool) := coneE K (fun y => (lamK K : ℤ) ≤ y) (fun y => (lamK K : ℤ) ≤ y)

/-- **the good event**. -/
def Hev (K : ℕ) : Set (ℕ → Bool) := Cplus K ∩ Gev K ∩ Gev' K ∩ {ω | (cnt K ω : ℝ) < AK K}

/-- on the good event the root count is small. -/
theorem roots_on_H (K : ℕ) (hK : 1 ≤ K) (ω : ℕ → Bool) (hω : ω ∈ Hev K) (ht : tK K ≤ 2 * K - 1) :
    ((fR (2 * K - 1) ω).roots.card : ℝ) < AK K + 2 := by
  obtain ⟨⟨⟨hC, hG⟩, hG'⟩, hc⟩ := hω
  have := roots_good K (tK K) (lamK K) ω hK ht hC hG hG'
  have hc' : (cnt K ω : ℝ) < AK K := hc
  unfold cnt at hc'
  have : ((fR (2 * K - 1) ω).roots.card : ℝ) ≤
      ((((range (2 * K - 1 - tK K)).filter (fun k => ω ∈ Iev k)).card +
      ((range (2 * K - 1 - tK K)).filter (fun k => ω ∈ Ialt k)).card + 2 : ℕ) : ℝ) := by
    exact_mod_cast this
  push_cast at this hc'
  unfold pK at hc'
  linarith

end E521
end

end S_P9

-- ===== P10 =====
section S_P10

/-! A deterministic lower bound for `μ(H_K)` (original). -/

open Finset MeasureTheory Filter Topology

noncomputable section

namespace E521

lemma measurable_eR (j : ℕ) : Measurable (fun ω : ℕ → Bool => eR ω j) := by
  unfold eR
  exact Measurable.ite (measurableSet_eq_fun (measurable_pi_apply j) measurable_const)
    measurable_const measurable_const

lemma meas_blockset (l : ℕ) (w : ℕ → ℝ) (x : ℝ) :
    MeasurableSet {ω : ℕ → Bool | x ≤ |∑ j ∈ range l, w j * eR ω j|} := by
  apply measurableSet_le measurable_const
  exact (Finset.measurable_sum _ (fun j _ => (measurable_eR j).const_mul (w j))).abs

/-- generic tail bound for backward blocks. -/
lemma back_tail (n t : ℕ) (ht : t ≤ n + 1) (w : ℕ → ℝ) (hw : ∀ j, w j ^ 2 = 1) {x : ℝ} (hx : 0 < x) :
    μS.real {ω | ∃ l ≤ t, x ≤ |∑ i ∈ range l, w i * eR ω (n - i)|} ≤ (t + 1) * (2 * Real.exp (-(x ^ 2 / (2 * t)))) := by
  have hsub : {ω | ∃ l ≤ t, x ≤ |∑ i ∈ range l, w i * eR ω (n - i)|} ⊆
      ⋃ l ∈ range (t + 1), {ω | x ≤ |∑ i ∈ range l, w i * eR ω (n - i)|} := by
    intro ω ⟨l, hl, h⟩; simp only [Set.mem_iUnion, mem_range]; exact ⟨l, by omega, h⟩
  refine (measureReal_mono hsub (measure_ne_top _ _)).trans ?_
  refine (measureReal_biUnion_finset_le _ _).trans ?_
  have each : ∀ l ∈ range (t + 1), μS.real {ω | x ≤ |∑ i ∈ range l, w i * eR ω (n - i)|} ≤
      2 * Real.exp (-(x ^ 2 / (2 * t))) := by
    intro l hl; rw [mem_range] at hl
    rcases Nat.eq_zero_or_pos l with h0 | hpos
    · subst h0
      have : {ω : ℕ → Bool | x ≤ |∑ i ∈ range 0, w i * eR ω (n - i)|} = ∅ := by
        ext ω; simp; linarith
      rw [this]; simp; positivity
    · have hset : {ω | x ≤ |∑ i ∈ range l, w i * eR ω (n - i)|} =
          (fun ω i => ω (i + (n + 1 - l))) ⁻¹' {ω | x ≤ |∑ j ∈ range l, w (l - 1 - j) * eR ω j|} := by
        ext ω; simp only [Set.mem_setOf_eq, Set.mem_preimage]
        rw [back_shift n l (by omega) w ω]
      rw [hset, Measure.real, μS_shift_preimage _ (meas_blockset l _ x), ← Measure.real]
      refine (block_hoeffding_w l (fun j => w (l - 1 - j)) (fun j => hw _) hx).trans ?_
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply Real.exp_le_exp.mpr
      have hl' : (l : ℝ) ≤ t := by exact_mod_cast (by omega : l ≤ t)
      have hl0 : (0 : ℝ) < l := by exact_mod_cast hpos
      have : x ^ 2 / (2 * t) ≤ x ^ 2 / (2 * l) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith)
      linarith
  refine (sum_le_sum each).trans (le_of_eq ?_)
  rw [sum_const, card_range, nsmul_eq_mul]; push_cast; ring

lemma Gev_compl_le (K : ℕ) (hK : 1 ≤ K) (hlam : 1 ≤ lamK K) (ht : tK K ≤ 2 * K - 1) :
    μS.real (Gev K)ᶜ ≤ (tK K + 1) * (2 * Real.exp (-((2 * (lamK K : ℝ) - 1) ^ 2 / (2 * tK K)))) := by
  have hx : (0 : ℝ) < 2 * (lamK K : ℝ) - 1 := by
    have : (1 : ℝ) ≤ lamK K := by exact_mod_cast hlam
    linarith
  have hsub : (Gev K)ᶜ ⊆ {ω | ∃ l ≤ tK K, 2 * (lamK K : ℝ) - 1 ≤
      |∑ i ∈ range l, (fun _ => (1 : ℝ)) i * eR ω (2 * K - 1 - i)|} := by
    intro ω hω
    simp only [Gev, Set.mem_compl_iff, Set.mem_setOf_eq, not_forall, not_lt] at hω
    obtain ⟨l, hl, h⟩ := hω
    exact ⟨l, hl, by simpa using h⟩
  refine (measureReal_mono hsub (measure_ne_top _ _)).trans ?_
  exact back_tail (2 * K - 1) (tK K) (by omega) (fun _ => 1) (fun _ => by norm_num) hx

lemma Gev'_compl_le (K : ℕ) (hK : 1 ≤ K) (hlam : 1 ≤ lamK K) (ht : tK K ≤ 2 * K - 1) :
    μS.real (Gev' K)ᶜ ≤ (tK K + 1) * (2 * Real.exp (-((2 * (lamK K : ℝ) - 1) ^ 2 / (2 * tK K)))) := by
  have hx : (0 : ℝ) < 2 * (lamK K : ℝ) - 1 := by
    have : (1 : ℝ) ≤ lamK K := by exact_mod_cast hlam
    linarith
  have hsub : (Gev' K)ᶜ ⊆ {ω | ∃ l ≤ tK K, 2 * (lamK K : ℝ) - 1 ≤
      |∑ i ∈ range l, (fun i => (-1 : ℝ) ^ i) i * eR ω (2 * K - 1 - i)|} := by
    intro ω hω
    simp only [Gev', Set.mem_compl_iff, Set.mem_setOf_eq, not_forall, not_lt] at hω
    obtain ⟨l, hl, h⟩ := hω
    exact ⟨l, hl, h⟩
  refine (measureReal_mono hsub (measure_ne_top _ _)).trans ?_
  exact back_tail (2 * K - 1) (tK K) (by omega) (fun i => (-1) ^ i)
    (fun j => by rw [← pow_mul, mul_comm, pow_mul]; norm_num) hx

end E521
end

end S_P10

-- ===== P11 =====
section S_P11

/-! `μ(H_K) ≥ (1/40)(4/π)/K` for large `K`, the pair bound, and a positive-probability `limsup`
(original). -/

open Finset MeasureTheory Filter Topology

noncomputable section

namespace E521

lemma tK_le (K : ℕ) (hK : 1 ≤ K) : tK K ≤ 2 * K - 1 := by
  unfold tK
  have hn : (1 : ℝ) ≤ ((2 * K - 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ 2 * K - 1)
  have := Real.rpow_le_self_of_one_le hn (show (19 : ℝ) / 20 ≤ 1 by norm_num)
  have h := Nat.floor_le (show (0 : ℝ) ≤ ((2 * K - 1 : ℕ) : ℝ) ^ ((19 : ℝ) / 20) by positivity)
  exact_mod_cast (h.trans this)

/-- the combined event family for Markov. -/
def Bfam (K : ℕ) (k : ℕ) : Set (ℕ → Bool) := if k < pK K then Iev k else Ialt (k - pK K)

instance instDecBfam (K k : ℕ) (ω : ℕ → Bool) : Decidable (ω ∈ Bfam K k) := by
  unfold Bfam; split_ifs <;> infer_instance

lemma cnt_eq (K : ℕ) (ω : ℕ → Bool) :
    cnt K ω = ((range (2 * pK K)).filter (fun k => ω ∈ Bfam K k)).card := by
  classical
  unfold cnt
  rw [card_filter, card_filter, card_filter, show 2 * pK K = pK K + pK K by ring, sum_range_add]
  congr 1
  · apply sum_congr rfl; intro k hk; rw [mem_range] at hk
    have e : (ω ∈ Bfam K k) ↔ ω ∈ Iev k := by unfold Bfam; rw [if_pos hk]
    by_cases h : ω ∈ Iev k
    · rw [if_pos h, if_pos (e.mpr h)]
    · rw [if_neg h, if_neg (fun h' => h (e.mp h'))]
  · apply sum_congr rfl; intro k _
    have e : (ω ∈ Bfam K (pK K + k)) ↔ ω ∈ Ialt k := by
      unfold Bfam; rw [if_neg (by omega), Nat.add_sub_cancel_left]
    by_cases h : ω ∈ Ialt k
    · rw [if_pos h, if_pos (e.mpr h)]
    · rw [if_neg h, if_neg (fun h' => h (e.mp h'))]

end E521

namespace E521

lemma coneE_le_u (K : ℕ) (F G : ℤ → Prop) :
    μS.real (coneE K F G) ≤ (N2 K 0 0 : ℝ) / 4 ^ K := by
  rw [← topE_real K K le_rfl]
  exact measureReal_mono (cone_sub_top K K le_rfl F G) (measure_ne_top _ _)

lemma Hev_sub (K : ℕ) : Hev K ⊆ Cplus K := fun ω h => h.1.1.1

lemma Hev_pair (K K' : ℕ) (h : K ≤ K') :
    μS.real (Hev K ∩ Hev K') ≤ ((N2 K 0 0 : ℝ) / 4 ^ K) * ((N2 (K' - K) 0 0 : ℝ) / 4 ^ (K' - K)) := by
  have h1 : Hev K ∩ Hev K' ⊆ Cplus K ∩ Cplus K' :=
    Set.inter_subset_inter (Hev_sub K) (Hev_sub K')
  refine (measureReal_mono h1 (measure_ne_top _ _)).trans ?_
  refine (cone_pair K K' h _ _ _ _).trans ?_
  apply mul_le_mul_of_nonneg_right (coneE_le_u K _ _) (by positivity)

lemma u_crude (L : ℕ) : (N2 L 0 0 : ℝ) / 4 ^ L ≤ (20 / Real.pi) / (L + 1) := by
  refine (u_upper L).trans ?_
  have h : √(1 + 24 / ((L : ℝ) + 1)) ≤ 5 := by
    rw [Real.sqrt_le_left (by norm_num)]
    have : 24 / ((L : ℝ) + 1) ≤ 24 := by
      rw [div_le_iff₀ (by positivity)]; nlinarith [Nat.cast_nonneg (α := ℝ) L]
    linarith
  have hp := Real.pi_pos
  calc (4 / Real.pi) / ((L : ℝ) + 1) * √(1 + 24 / ((L : ℝ) + 1)) ≤ (4 / Real.pi) / ((L : ℝ) + 1) * 5 :=
        mul_le_mul_of_nonneg_left h (by positivity)
    _ = (20 / Real.pi) / (L + 1) := by ring

end E521

namespace E521

lemma meas_Iev (k : ℕ) : MeasurableSet (Iev k) := by
  rw [Iev_cyl]; exact measurableSet_rs _ _

lemma meas_Ialt (k : ℕ) : MeasurableSet (Ialt k) := by
  rw [Ialt_cyl]; exact measurableSet_rs _ _

lemma meas_coneE (K : ℕ) (F G : ℤ → Prop) : MeasurableSet (coneE K F G) := measurableSet_Φ K _

lemma meas_Bfam (K k : ℕ) : MeasurableSet (Bfam K k) := by
  unfold Bfam; split_ifs; exacts [meas_Iev _, meas_Ialt _]

/-- Markov for the combined count. -/
lemma cone_cnt (K : ℕ) (hA : 0 < AK K) :
    AK K * μS.real (Cplus K ∩ {ω | AK K ≤ (cnt K ω : ℝ)}) ≤
      ∑ k ∈ range (pK K), (μS.real (Cplus K ∩ Iev k) + μS.real (Cplus K ∩ Ialt k)) := by
  classical
  have hset : Cplus K ∩ {ω | AK K ≤ (cnt K ω : ℝ)} =
      Cplus K ∩ {ω | AK K ≤ (((range (2 * pK K)).filter (fun k => ω ∈ Bfam K k)).card : ℝ)} := by
    ext ω; simp only [Set.mem_inter_iff, Set.mem_setOf_eq, cnt_eq]
  rw [hset]
  have hm := E521Q.markov_count μS (Cplus K) (meas_coneE _ _ _) (range (2 * pK K)) (Bfam K)
    (meas_Bfam K) hA
  refine hm.trans (le_of_eq ?_)
  rw [show 2 * pK K = pK K + pK K by ring, sum_range_add, sum_add_distrib]
  congr 1
  · apply sum_congr rfl; intro k hk; rw [mem_range] at hk; simp [Bfam, hk]
  · apply sum_congr rfl; intro k _; simp [Bfam]

end E521

namespace E521

def LK (K k : ℕ) : ℕ := (2 * K - k - 2) / 2

/-- **deterministic lower bound for `μ(H_K)`.** -/
theorem Hev_det (K : ℕ) (hK : 1 ≤ K) (hlam : 1 ≤ lamK K) (hA : 0 < AK K) (hpn : pK K + 2 ≤ 2 * K) :
    (4 / Real.pi) / (K + 4) - 4 * √24 * (lamK K : ℝ) ^ 2 / (K + 1) ^ 2
      - 2 * ((tK K + 1) * (2 * Real.exp (-((2 * (lamK K : ℝ) - 1) ^ 2 / (2 * tK K)))))
      - (2 / AK K) * ∑ k ∈ range (pK K), ((N2 (LK K k) 0 0 : ℝ) / 4 ^ (LK K k)) * R522.PP (R522.SCev (k + 2))
      ≤ μS.real (Hev K) := by
  classical
  have ht := tK_le K hK
  -- covering
  have hcov : Cplus K ⊆ Hev K ∪ (Gev K)ᶜ ∪ (Gev' K)ᶜ ∪ (Cplus K ∩ {ω | AK K ≤ (cnt K ω : ℝ)}) := by
    intro ω hω
    by_cases h1 : ω ∈ Gev K
    · by_cases h2 : ω ∈ Gev' K
      · by_cases h3 : (cnt K ω : ℝ) < AK K
        · left; left; left; exact ⟨⟨⟨hω, h1⟩, h2⟩, h3⟩
        · right; exact ⟨hω, not_lt.mp h3⟩
      · left; right; exact h2
    · left; left; right; exact h1
  have hmeas := measureReal_mono (μ := μS) hcov (measure_ne_top _ _)
  have hu1 := measureReal_union_le (μ := μS) (Hev K ∪ (Gev K)ᶜ ∪ (Gev' K)ᶜ) (Cplus K ∩ {ω | AK K ≤ (cnt K ω : ℝ)})
  have hu2 := measureReal_union_le (μ := μS) (Hev K ∪ (Gev K)ᶜ) (Gev' K)ᶜ
  have hu3 := measureReal_union_le (μ := μS) (Hev K) (Gev K)ᶜ
  -- the cone
  have hC : (4 / Real.pi) / (K + 4) - 4 * √24 * (lamK K : ℝ) ^ 2 / (K + 1) ^ 2 ≤ μS.real (Cplus K) := by
    unfold Cplus
    rw [coneE_real]
    have := cone_plus_lower K (lamK K) hlam
    have := u_lower K
    linarith
  have hG := Gev_compl_le K hK hlam ht
  have hG' := Gev'_compl_le K hK hlam ht
  -- the count
  have hcnt := cone_cnt K hA
  have hsum : ∑ k ∈ range (pK K), (μS.real (Cplus K ∩ Iev k) + μS.real (Cplus K ∩ Ialt k)) ≤
      2 * ∑ k ∈ range (pK K), ((N2 (LK K k) 0 0 : ℝ) / 4 ^ (LK K k)) * R522.PP (R522.SCev (k + 2)) := by
    rw [mul_sum]
    apply sum_le_sum; intro k hk; rw [mem_range] at hk
    have hL : LK K k ≤ K := by unfold LK; omega
    have hk2 : k + 2 ≤ 2 * K - 2 * LK K k := by unfold LK; omega
    have a := cone_Iev K (LK K k) k hL hk2 (fun y => (lamK K : ℤ) ≤ y) (fun y => (lamK K : ℤ) ≤ y)
    have b := cone_Ialt K (LK K k) k hL hk2 (fun y => (lamK K : ℤ) ≤ y) (fun y => (lamK K : ℤ) ≤ y)
    unfold Cplus; linarith
  have hcnt' : μS.real (Cplus K ∩ {ω | AK K ≤ (cnt K ω : ℝ)}) ≤
      (2 / AK K) * ∑ k ∈ range (pK K), ((N2 (LK K k) 0 0 : ℝ) / 4 ^ (LK K k)) * R522.PP (R522.SCev (k + 2)) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hA]
    linarith
  linarith

end E521
end

end S_P11


end
