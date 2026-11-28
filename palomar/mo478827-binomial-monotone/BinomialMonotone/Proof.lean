/-
Copyright 2026 Ming-Chih Kao. Licensed under the Apache License, Version 2.0;
see the LICENSE file at the root of this repository.
-/
module

public import Mathlib

/-! Port: copied from `MO478827.lean` of github.com/koolkao/mo478827-binomial-monotone (commit
3d17061d300988d21b3b1f23cf4bf91b6129dc62, v1.0.0, Lean v4.36.0, same Mathlib) and put into the module system:
the `module` header, `public import`, a public section, and the namespaces `MO478827` and `MO478827Check`
renamed `BinomialMonotone` and `BinomialMonotoneCheck` so that `Solution.lean` can state the compared
theorems under the names `MO478827.*`. The mathematics and the proofs are unchanged. -/

@[expose] public section

-- ===== Part 1: Lemma C =====

/-!
# MO 478827, Lemma C (the parameter-free inequality behind Case 2)

For integers `k ≥ 2`, `c < k`, `w ≥ 1` with `2w ≤ c`, put `N1 = c+1`, `N2 = k-c`,
`A = w(k-w)/(N1 N2)`, `P_{i+1} = ∏_{j=1}^{i} (N1-j)(N2-j)/((N1+j)(N2+j))`, `s = ⌊c/w⌋` and
`m0 = min (max 1 ⌊s/2⌋) (min N1 N2)`. Then `1 ≤ 2 √A ∑_{i<m0} √P_{i+1}`.
-/

open Finset Real

noncomputable section

namespace BinomialMonotone

/-- The factor with index `j+1`. -/
def fac (N1 N2 : ℝ) (j : ℕ) : ℝ :=
  ((N1 - (j + 1)) * (N2 - (j + 1))) / ((N1 + (j + 1)) * (N2 + (j + 1)))

/-- `Q i = P_{i+1}`. -/
def Q (N1 N2 : ℝ) (i : ℕ) : ℝ := ∏ j ∈ range i, fac N1 N2 j

/-- The lower product. -/
def Bp (N1 N2 : ℝ) (i : ℕ) : ℝ := ∏ j ∈ range i, ((1 - (j + 1) / N1) * (1 - (j + 1) / N2))

lemma sq_le_ratio (N x : ℝ) (hN : 0 < N) (hx : 0 ≤ x) (hxN : x ≤ N) :
    (1 - x / N) ^ 2 ≤ (N - x) / (N + x) := by
  have e : 1 - x / N = (N - x) / N := by field_simp
  rw [e, div_pow, div_le_div_iff₀ (by positivity) (by linarith)]
  have h1 : 0 ≤ N - x := by linarith
  nlinarith [mul_nonneg h1 (mul_nonneg hx hx)]

lemma fac_ge (N1 N2 : ℝ) (j : ℕ) (h1 : 0 < N1) (h2 : 0 < N2)
    (hj1 : ((j : ℝ) + 1) ≤ N1) (hj2 : ((j : ℝ) + 1) ≤ N2) :
    ((1 - (j + 1) / N1) * (1 - (j + 1) / N2)) ^ 2 ≤ fac N1 N2 j := by
  have hx : (0 : ℝ) ≤ (j : ℝ) + 1 := by positivity
  unfold fac
  rw [mul_pow, mul_div_mul_comm]
  have a1 := sq_le_ratio N1 ((j : ℝ) + 1) h1 hx hj1
  have a2 := sq_le_ratio N2 ((j : ℝ) + 1) h2 hx hj2
  exact mul_le_mul a1 a2 (sq_nonneg _) (div_nonneg (by linarith) (by linarith))

lemma factor_mem (N : ℝ) (j : ℕ) (hN : 0 < N) (hj : ((j : ℝ) + 1) ≤ N) :
    0 ≤ 1 - (j + 1) / N ∧ 1 - (j + 1) / N ≤ 1 := by
  constructor
  · rw [sub_nonneg, div_le_one hN]; exact hj
  · have : 0 ≤ ((j : ℝ) + 1) / N := by positivity
    linarith

lemma Bp_nonneg (N1 N2 : ℝ) (i : ℕ) (h1 : 0 < N1) (h2 : 0 < N2)
    (hi1 : (i : ℝ) ≤ N1) (hi2 : (i : ℝ) ≤ N2) : 0 ≤ Bp N1 N2 i := by
  unfold Bp
  apply prod_nonneg
  intro j hj
  have hj' : ((j : ℝ) + 1) ≤ i := by
    have := mem_range.mp hj; exact_mod_cast this
  exact mul_nonneg (factor_mem N1 j h1 (by linarith)).1 (factor_mem N2 j h2 (by linarith)).1

lemma Bp_sq_le_Q (N1 N2 : ℝ) (i : ℕ) (h1 : 0 < N1) (h2 : 0 < N2)
    (hi1 : (i : ℝ) ≤ N1) (hi2 : (i : ℝ) ≤ N2) : (Bp N1 N2 i) ^ 2 ≤ Q N1 N2 i := by
  unfold Bp Q
  rw [← prod_pow]
  apply prod_le_prod₀
  · intro j _; exact sq_nonneg _
  · intro j hj
    have hj' : ((j : ℝ) + 1) ≤ i := by
      have := mem_range.mp hj; exact_mod_cast this
    exact fac_ge N1 N2 j h1 h2 (by linarith) (by linarith)

/-- Weierstrass product inequality. -/
lemma weierstrass (x : ℕ → ℝ) (i : ℕ) (hx : ∀ j < i, 0 ≤ x j ∧ x j ≤ 1) :
    1 - ∑ j ∈ range i, (1 - x j) ≤ ∏ j ∈ range i, x j := by
  induction i with
  | zero => simp
  | succ i ih =>
    have ih' := ih (fun j hj => hx j (by omega))
    have hxi := hx i (by omega)
    rw [sum_range_succ, prod_range_succ]
    have hS : 0 ≤ ∑ j ∈ range i, (1 - x j) := by
      apply sum_nonneg; intro j hj
      have := (hx j (by have := mem_range.mp hj; omega)).2; linarith
    have key : (1 - ∑ j ∈ range i, (1 - x j)) * x i ≤ (∏ j ∈ range i, x j) * x i :=
      mul_le_mul_of_nonneg_right ih' hxi.1
    nlinarith [mul_nonneg (sub_nonneg.mpr hxi.2) hS]

lemma Bp_ge (N1 N2 : ℝ) (i : ℕ) (h1 : 0 < N1) (h2 : 0 < N2)
    (hi1 : (i : ℝ) ≤ N1) (hi2 : (i : ℝ) ≤ N2) :
    1 - (1 / N1 + 1 / N2) * ((i : ℝ) * (i + 1) / 2) ≤ Bp N1 N2 i := by
  unfold Bp
  have hw := weierstrass (fun j => (1 - (j + 1) / N1) * (1 - (j + 1) / N2)) i (by
    intro j hj
    have hj' : ((j : ℝ) + 1) ≤ i := by exact_mod_cast hj
    obtain ⟨a0, a1⟩ := factor_mem N1 j h1 (by linarith)
    obtain ⟨b0, b1⟩ := factor_mem N2 j h2 (by linarith)
    exact ⟨mul_nonneg a0 b0, by nlinarith⟩)
  refine le_trans ?_ hw
  have hsum : ∑ j ∈ range i, (1 - (1 - (j + 1) / N1) * (1 - (j + 1) / N2))
      ≤ ∑ j ∈ range i, (1 / N1 + 1 / N2) * ((j : ℝ) + 1) := by
    apply sum_le_sum; intro j _
    have : 0 ≤ ((j : ℝ) + 1) / N1 * (((j : ℝ) + 1) / N2) := by positivity
    have e : (1 / N1 + 1 / N2) * ((j : ℝ) + 1) = (j + 1) / N1 + (j + 1) / N2 := by ring
    rw [e]; nlinarith
  have hgauss : ∀ n : ℕ, ∑ j ∈ range n, ((j : ℝ) + 1) = (n : ℝ) * (n + 1) / 2 := by
    intro n; induction n with
    | zero => simp
    | succ n ih => rw [sum_range_succ, ih]; push_cast; ring
  rw [← mul_sum, hgauss] at hsum
  linarith

lemma sum_sqrt_Q_ge (N1 N2 : ℝ) (M : ℕ) (h1 : 0 < N1) (h2 : 0 < N2)
    (hM1 : (M : ℝ) ≤ N1) (hM2 : (M : ℝ) ≤ N2) :
    (M : ℝ) - (1 / N1 + 1 / N2) * (((M : ℝ) ^ 3 - M) / 6) ≤ ∑ i ∈ range M, √(Q N1 N2 i) := by
  have step : ∀ i ∈ range M, 1 - (1 / N1 + 1 / N2) * ((i : ℝ) * (i + 1) / 2) ≤ √(Q N1 N2 i) := by
    intro i hi
    have hi' : (i : ℝ) ≤ M := by have := mem_range.mp hi; exact_mod_cast this.le
    have hB := Bp_ge N1 N2 i h1 h2 (by linarith) (by linarith)
    have hB0 := Bp_nonneg N1 N2 i h1 h2 (by linarith) (by linarith)
    have hsq := Bp_sq_le_Q N1 N2 i h1 h2 (by linarith) (by linarith)
    have : Bp N1 N2 i ≤ √(Q N1 N2 i) := by
      rw [Real.le_sqrt hB0 (le_trans (sq_nonneg _) hsq)]; exact hsq
    linarith
  refine le_trans (le_of_eq ?_) (sum_le_sum step)
  have hs : ∀ n : ℕ, ∑ i ∈ range n, (1 - (1 / N1 + 1 / N2) * ((i : ℝ) * (i + 1) / 2))
      = (n : ℝ) - (1 / N1 + 1 / N2) * (((n : ℝ) ^ 3 - n) / 6) := by
    intro n; induction n with
    | zero => simp
    | succ n ih => rw [sum_range_succ, ih]; push_cast; ring
  rw [hs]

/-- `ψ(τ) = 2τ - (2/3)τ³ ≥ 1` on `0.3136 ≤ τ² ≤ 1.9044`, i.e. `τ ∈ [0.56, 1.38]`. -/
lemma psi_ge (τ : ℝ) (h0 : 0 ≤ τ) (hl : 0.3136 ≤ τ ^ 2) (hu : τ ^ 2 ≤ 1.9044) :
    1 ≤ 2 * τ - 2 / 3 * τ ^ 3 := by
  have ha : 0.56 ≤ τ := by nlinarith
  have hb : τ ≤ 1.38 := by nlinarith
  nlinarith [mul_nonneg (sub_nonneg.mpr ha) (sub_nonneg.mpr hb),
    mul_nonneg (mul_nonneg (sub_nonneg.mpr ha) (sub_nonneg.mpr hb)) h0]

set_option maxHeartbeats 1000000 in
/-- **Lemma C.** -/
theorem lemmaC (k c w : ℕ) (hck : c < k) (hw : 1 ≤ w) (h2w : 2 * w ≤ c) :
    1 ≤ 2 * √((w : ℝ) * ((k : ℝ) - w) / (((c : ℝ) + 1) * ((k : ℝ) - c))) *
      ∑ i ∈ range (min (max 1 (c / w / 2)) (min (c + 1) (k - c))),
        √(Q ((c : ℝ) + 1) ((k : ℝ) - c) i) := by
  set N1 : ℝ := (c : ℝ) + 1 with hN1
  set N2 : ℝ := (k : ℝ) - c with hN2
  set A : ℝ := (w : ℝ) * ((k : ℝ) - w) / (N1 * N2) with hA
  set H : ℝ := 1 / N1 + 1 / N2 with hH
  set s : ℕ := c / w with hs
  set h : ℕ := s / 2 with hh
  set m0 : ℕ := min (max 1 h) (min (c + 1) (k - c)) with hm0
  have hckR : (c : ℝ) + 1 ≤ k := by exact_mod_cast hck
  have hwR : (1 : ℝ) ≤ w := by exact_mod_cast hw
  have h2wR : 2 * (w : ℝ) ≤ c := by exact_mod_cast h2w
  have hN1pos : 0 < N1 := by positivity
  have hN2ge : 1 ≤ N2 := by rw [hN2]; linarith
  have hN2pos : 0 < N2 := by linarith
  have hkcN : ((k - c : ℕ) : ℝ) = N2 := by rw [hN2]; push_cast [hck.le]; ring
  -- facts about s
  have hsw : s * w ≤ c := Nat.div_mul_le_self c w
  have hsw2 : c < (s + 1) * w := by
    have := Nat.lt_div_mul_add (a := c) (b := w) (by omega)
    rw [hs]; nlinarith [this]
  have hsR : (c : ℝ) + 1 ≤ ((s : ℝ) + 1) * w := by
    have : c + 1 ≤ (s + 1) * w := hsw2
    exact_mod_cast this
  have hs2 : 2 ≤ s := by
    rw [hs]; exact (Nat.le_div_iff_mul_le (by omega)).mpr (by linarith)
  -- bounds on A
  have hkw : (k : ℝ) - w ≥ N2 := by rw [hN2]; linarith
  have hA1 : (w : ℝ) / N1 ≤ A := by
    rw [hA, div_le_div_iff₀ hN1pos (by positivity)]
    have : (w : ℝ) * (N1 * N2) = (w * N2) * N1 := by ring
    rw [this]; apply mul_le_mul_of_nonneg_right _ hN1pos.le
    exact mul_le_mul_of_nonneg_left hkw (by positivity)
  have hAs : 1 / ((s : ℝ) + 1) ≤ A := by
    refine le_trans ?_ hA1
    rw [div_le_div_iff₀ (by positivity) hN1pos]; linarith
  have hAH : H / 2 ≤ A := by
    -- k - w ≥ N2 + (N1 - 1)/2
    have hkw2 : (k : ℝ) - w ≥ N2 + (N1 - 1) / 2 := by rw [hN1, hN2]; linarith
    have hstep : (w : ℝ) * (N2 + (N1 - 1) / 2) / (N1 * N2) ≤ A := by
      rw [hA]; apply div_le_div_of_nonneg_right _ (by positivity)
      exact mul_le_mul_of_nonneg_left hkw2 (by positivity)
    refine le_trans ?_ hstep
    rw [hH]
    have e : (w : ℝ) * (N2 + (N1 - 1) / 2) / (N1 * N2)
        = w * (1 / N1 + 1 / (2 * N2) - 1 / (2 * N1 * N2)) := by field_simp; ring
    rw [e]
    have hdiff : (1 / N1 + 1 / N2) / 2 ≤ 1 / N1 + 1 / (2 * N2) - 1 / (2 * N1 * N2) := by
      have : 1 / N1 + 1 / (2 * N2) - 1 / (2 * N1 * N2) - (1 / N1 + 1 / N2) / 2
          = (1 / (2 * N1)) * (1 - 1 / N2) := by field_simp; ring
      have h3 : 0 ≤ (1 / (2 * N1)) * (1 - 1 / N2) := by
        apply mul_nonneg (by positivity)
        rw [sub_nonneg, div_le_one hN2pos]; exact hN2ge
      linarith
    have hpos : 0 ≤ 1 / N1 + 1 / (2 * N2) - 1 / (2 * N1 * N2) := by
      have : 0 ≤ (1 / N1 + 1 / N2) / 2 := by positivity
      linarith
    calc (1 / N1 + 1 / N2) / 2 ≤ 1 / N1 + 1 / (2 * N2) - 1 / (2 * N1 * N2) := hdiff
      _ = 1 * (1 / N1 + 1 / (2 * N2) - 1 / (2 * N1 * N2)) := by ring
      _ ≤ w * (1 / N1 + 1 / (2 * N2) - 1 / (2 * N1 * N2)) :=
          mul_le_mul_of_nonneg_right hwR hpos
  have hHpos : 0 < H := by positivity
  have hHle : H ≤ 2 := by
    rw [hH]
    have a : 1 / N1 ≤ 1 := by rw [div_le_one hN1pos]; rw [hN1]; linarith [(Nat.cast_nonneg c : (0:ℝ) ≤ c)]
    have b : 1 / N2 ≤ 1 := by rw [div_le_one hN2pos]; exact hN2ge
    linarith
  have hHgt : 1 / N2 < H := by rw [hH]; have : 0 < 1 / N1 := by positivity
                               linarith
  have hA0 : 0 ≤ A := le_trans (by positivity) hAH
  -- monotonicity of the partial sums in the range
  have mono : ∀ M : ℕ, M ≤ m0 → ∑ i ∈ range M, √(Q N1 N2 i) ≤ ∑ i ∈ range m0, √(Q N1 N2 i) := by
    intro M hM
    exact sum_le_sum_of_subset_of_nonneg (range_subset_range.mpr hM) (fun _ _ _ => sqrt_nonneg _)
  -- generic: M ≤ N2 from H M^2 ≤ 2 (M ≥ 1)
  have le_N2 : ∀ M : ℕ, H * (M : ℝ) ^ 2 ≤ 2 → (M : ℝ) ≤ N2 := by
    intro M hM
    by_contra hcon
    push_neg at hcon
    -- M ≥ N2 + 1 as integers
    have hint : N2 + 1 ≤ (M : ℝ) := by
      have : (k - c : ℕ) < M := by
        have : ((k - c : ℕ) : ℝ) < M := by rw [hkcN]; exact hcon
        exact_mod_cast this
      have : (k - c : ℕ) + 1 ≤ M := this
      have : (((k - c : ℕ) + 1 : ℕ) : ℝ) ≤ M := by exact_mod_cast this
      push_cast at this; rw [hkcN] at this; linarith
    have : H * (M : ℝ) ^ 2 > 2 := by
      have hM2 : (N2 + 1) ^ 2 ≤ (M : ℝ) ^ 2 := by
        exact pow_le_pow_left₀ (by linarith) hint 2
      have : (1 / N2) * (N2 + 1) ^ 2 > 2 := by
        rw [gt_iff_lt, ← sub_pos]
        have e : (1 / N2) * (N2 + 1) ^ 2 - 2 = (N2 ^ 2 + 1) / N2 := by field_simp; ring
        rw [e]; positivity
      calc H * (M : ℝ) ^ 2 ≥ (1 / N2) * (M : ℝ) ^ 2 :=
            mul_le_mul_of_nonneg_right hHgt.le (sq_nonneg _)
        _ ≥ (1 / N2) * (N2 + 1) ^ 2 := mul_le_mul_of_nonneg_left hM2 (by positivity)
        _ > 2 := this
    linarith
  have hm0ge1 : 1 ≤ m0 := by rw [hm0]; omega
  have hhc : (h : ℝ) + 1 ≤ N1 := by
    have : h ≤ c := by rw [hh]; have : s ≤ c := by rw [hs]; exact Nat.div_le_self c w
                       omega
    rw [hN1]; exact_mod_cast (by omega : h + 1 ≤ c + 1)
  -- the main estimate for a chosen M
  have finish : ∀ M : ℕ, 1 ≤ M → M ≤ m0 → (M : ℝ) ≤ N1 → (M : ℝ) ≤ N2 →
      1 ≤ 2 * √A * ((M : ℝ) - H * (((M : ℝ) ^ 3 - M) / 6)) → 1 ≤ 2 * √A * ∑ i ∈ range m0, √(Q N1 N2 i) := by
    intro M _ hMm hM1 hM2 hb
    have hsum := sum_sqrt_Q_ge N1 N2 M hN1pos hN2pos hM1 hM2
    have := mono M hMm
    have hsq : 0 ≤ 2 * √A := by positivity
    calc (1 : ℝ) ≤ 2 * √A * ((M : ℝ) - H * (((M : ℝ) ^ 3 - M) / 6)) := hb
      _ ≤ 2 * √A * ∑ i ∈ range M, √(Q N1 N2 i) := mul_le_mul_of_nonneg_left hsum hsq
      _ ≤ 2 * √A * ∑ i ∈ range m0, √(Q N1 N2 i) := mul_le_mul_of_nonneg_left this hsq
  by_cases hd1 : H * (h : ℝ) ^ 2 ≤ 2
  · -- case (d1)
    by_cases hh1 : h ≤ 1
    · -- M = 1, s ≤ 3
      apply finish 1 le_rfl hm0ge1 (by rw [hN1]; push_cast; linarith [(Nat.cast_nonneg c : (0:ℝ) ≤ c)])
        (by push_cast; exact hN2ge)
      have hs3 : s ≤ 3 := by omega
      have hs3R : (s : ℝ) + 1 ≤ 4 := by exact_mod_cast (by omega : s + 1 ≤ 4)
      have hA4 : 1 / 4 ≤ A := le_trans (one_div_le_one_div_of_le (by positivity) hs3R) hAs
      have hsqA : 1 / 2 ≤ √A := by
        rw [Real.le_sqrt (by norm_num) hA0]; nlinarith
      push_cast; nlinarith
    · -- M = h ≥ 2
      push_neg at hh1
      have hm : h ≤ m0 := by
        have hN2h : (h : ℝ) ≤ N2 := le_N2 h hd1
        have : h ≤ k - c := by
          have : (h : ℝ) ≤ ((k - c : ℕ) : ℝ) := by rw [hkcN]; exact hN2h
          exact_mod_cast this
        rw [hm0]; have : h ≤ c := by rw [hh]; have : s ≤ c := by rw [hs]; exact Nat.div_le_self c w
                                     omega
        omega
      apply finish h (by omega) hm (by linarith) (le_N2 h hd1)
      have hhR : (2 : ℝ) ≤ h := by exact_mod_cast hh1
      have hs2h : (s : ℝ) + 1 ≤ 2 * h + 2 := by
        have : s ≤ 2 * h + 1 := by omega
        exact_mod_cast (by omega : s + 1 ≤ 2 * h + 2)
      -- A ≥ 1/(2h+2)
      have hA' : 1 / (2 * (h : ℝ) + 2) ≤ A :=
        le_trans (one_div_le_one_div_of_le (by positivity) hs2h) hAs
      -- bracket ≥ 2h/3
      have hbr : 2 * (h : ℝ) / 3 ≤ (h : ℝ) - H * (((h : ℝ) ^ 3 - h) / 6) := by
        have : H * ((h : ℝ) ^ 3) ≤ 2 * h := by
          have := mul_le_mul_of_nonneg_right hd1 (by positivity : (0:ℝ) ≤ h)
          nlinarith
        nlinarith [mul_nonneg hHpos.le (by positivity : (0:ℝ) ≤ h)]
      -- √A ≥ 3/(4h)
      have hsqA : 3 / (4 * (h : ℝ)) ≤ √A := by
        rw [Real.le_sqrt (by positivity) hA0]
        refine le_trans ?_ hA'
        rw [div_pow, div_le_div_iff₀ (by positivity) (by positivity)]
        have h32 : 32 * (h : ℝ) ≤ 16 * (h : ℝ) ^ 2 := by nlinarith
        have e : ((4 : ℝ) * h) ^ 2 = 16 * (h : ℝ) ^ 2 := by ring
        rw [e]; linarith
      have h3 : 0 ≤ 3 / (4 * (h : ℝ)) := by positivity
      have hh0 : (h : ℝ) ≠ 0 := by positivity
      calc (1 : ℝ) = 2 * (3 / (4 * (h : ℝ))) * (2 * h / 3) := by field_simp <;> ring
        _ ≤ 2 * √A * ((h : ℝ) - H * (((h : ℝ) ^ 3 - h) / 6)) := by
          apply mul_le_mul (by linarith) hbr (by positivity) (by positivity)
  · -- case (d2)
    push_neg at hd1
    have hex : ∃ M : ℕ, 2 < H * ((M : ℝ) + 1) ^ 2 := by
      refine ⟨h - 1, ?_⟩
      have h1 : 1 ≤ h := by
        by_contra hc; push_neg at hc
        have : h = 0 := by omega
        rw [this] at hd1; simp at hd1; linarith
      have : ((h - 1 : ℕ) : ℝ) + 1 = h := by
        rw [Nat.cast_sub h1]; push_cast; ring
      rw [this]; exact hd1
    classical
    set Ms := Nat.find hex with hMs
    have hMs1 : 2 < H * ((Ms : ℝ) + 1) ^ 2 := Nat.find_spec hex
    have hMs0 : 1 ≤ Ms := by
      by_contra hc; push_neg at hc
      have : Ms = 0 := by omega
      rw [this] at hMs1; simp at hMs1; linarith
    have hMs2 : H * (Ms : ℝ) ^ 2 ≤ 2 := by
      have := Nat.find_min hex (show Ms - 1 < Ms by omega)
      push_neg at this
      have e : ((Ms - 1 : ℕ) : ℝ) + 1 = Ms := by rw [Nat.cast_sub hMs0]; push_cast; ring
      rwa [e] at this
    have hMsh : Ms + 1 ≤ h := by
      have h1 : 1 ≤ h := by
        by_contra hc; push_neg at hc
        have : h = 0 := by omega
        rw [this] at hd1; simp at hd1; linarith
      have := Nat.find_min' hex (show 2 < H * (((h - 1 : ℕ) : ℝ) + 1) ^ 2 by
        have : ((h - 1 : ℕ) : ℝ) + 1 = h := by rw [Nat.cast_sub h1]; push_cast; ring
        rw [this]; exact hd1)
      omega
    have hhc' : h ≤ c := by
      rw [hh]; have : s ≤ c := by rw [hs]; exact Nat.div_le_self c w
      omega
    -- generic bound via τ
    have tau_bound : ∀ M : ℕ, 0.6272 ≤ H * (M : ℝ) ^ 2 → H * (M : ℝ) ^ 2 ≤ 3.8088 →
        1 ≤ 2 * √A * ((M : ℝ) - H * (((M : ℝ) ^ 3 - M) / 6)) := by
      intro M hl hu
      set r := √(H / 2) with hr
      have hr0 : 0 ≤ r := sqrt_nonneg _
      have hr2 : r ^ 2 = H / 2 := by rw [hr, sq_sqrt (by positivity)]
      have hrA : r ≤ √A := sqrt_le_sqrt hAH
      have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg M
      set τ := (M : ℝ) * r with hτ
      have hτ2 : τ ^ 2 = H * (M : ℝ) ^ 2 / 2 := by rw [hτ, mul_pow, hr2]; ring
      have hτ0 : 0 ≤ τ := mul_nonneg hM0 hr0
      have hpsi := psi_ge τ hτ0 (by rw [hτ2]; linarith) (by rw [hτ2]; linarith)
      have hbr0 : 0 ≤ (M : ℝ) - H * ((M : ℝ) ^ 3) / 6 := by
        have : H * ((M : ℝ) ^ 3) = (H * (M : ℝ) ^ 2) * M := by ring
        rw [this]; nlinarith
      have hbr : (M : ℝ) - H * ((M : ℝ) ^ 3) / 6 ≤ (M : ℝ) - H * (((M : ℝ) ^ 3 - M) / 6) := by
        nlinarith [mul_nonneg hHpos.le hM0]
      have e : 2 * r * ((M : ℝ) - H * ((M : ℝ) ^ 3) / 6) = 2 * τ - 2 / 3 * τ ^ 3 := by
        have : H = 2 * r ^ 2 := by rw [hr2]; ring
        rw [hτ, this]; ring
      calc (1 : ℝ) ≤ 2 * τ - 2 / 3 * τ ^ 3 := hpsi
        _ = 2 * r * ((M : ℝ) - H * ((M : ℝ) ^ 3) / 6) := e.symm
        _ ≤ 2 * √A * ((M : ℝ) - H * (((M : ℝ) ^ 3 - M) / 6)) := by
          apply mul_le_mul (by linarith) hbr hbr0 (by positivity)
    by_cases hc1 : 0.6272 ≤ H * (Ms : ℝ) ^ 2
    · -- M = Ms
      have hMsN2 := le_N2 Ms hMs2
      have hm : Ms ≤ m0 := by
        have : Ms ≤ k - c := by
          have : (Ms : ℝ) ≤ ((k - c : ℕ) : ℝ) := by rw [hkcN]; exact hMsN2
          exact_mod_cast this
        rw [hm0]; omega
      apply finish Ms hMs0 hm (by
        have : (Ms : ℝ) + 1 ≤ h := by exact_mod_cast hMsh
        linarith) hMsN2
      exact tau_bound Ms hc1 (by linarith)
    · -- M = Ms + 1
      push_neg at hc1
      have hN2' : (Ms : ℝ) + 1 ≤ N2 := by
        by_contra hcon; push_neg at hcon
        -- Ms ≥ N2, so H Ms^2 > N2 ≥ 1 > 0.6272
        have hMsge : N2 ≤ (Ms : ℝ) := by
          have : (k - c : ℕ) ≤ Ms := by
            have : ((k - c : ℕ) : ℝ) < (Ms : ℝ) + 1 := by rw [hkcN]; exact hcon
            have : (k - c : ℕ) < Ms + 1 := by exact_mod_cast this
            omega
          have : ((k - c : ℕ) : ℝ) ≤ Ms := by exact_mod_cast this
          rwa [hkcN] at this
        have : H * (Ms : ℝ) ^ 2 ≥ (1 / N2) * N2 ^ 2 := by
          calc H * (Ms : ℝ) ^ 2 ≥ (1 / N2) * (Ms : ℝ) ^ 2 :=
                mul_le_mul_of_nonneg_right hHgt.le (sq_nonneg _)
            _ ≥ (1 / N2) * N2 ^ 2 :=
                mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hN2pos.le hMsge 2) (by positivity)
        have e : (1 / N2) * N2 ^ 2 = N2 := by field_simp
        rw [e] at this; linarith
      have hm : Ms + 1 ≤ m0 := by
        have : Ms + 1 ≤ k - c := by
          have : ((Ms + 1 : ℕ) : ℝ) ≤ ((k - c : ℕ) : ℝ) := by rw [hkcN]; push_cast; exact hN2'
          exact_mod_cast this
        rw [hm0]; omega
      apply finish (Ms + 1) (by omega) hm (by
        have : ((Ms + 1 : ℕ) : ℝ) ≤ h := by exact_mod_cast hMsh
        linarith) (by push_cast; exact hN2')
      apply tau_bound (Ms + 1) (by push_cast; linarith)
      push_cast
      have hMsR : (1 : ℝ) ≤ Ms := by exact_mod_cast hMs0
      have : ((Ms : ℝ) + 1) ^ 2 ≤ 4 * (Ms : ℝ) ^ 2 := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_left this hHpos.le]

end BinomialMonotone

-- ===== Part 2: binomial ratio identities (Row) =====

/-!
# MO 478827: binomial ratio identities and the per-row AM-GM domination
-/

open Finset Real

noncomputable section

namespace BinomialMonotone

/-- binomial pmf value `C(m,j) p^j (1-p)^(m-j)` -/
def bp (m j : ℕ) (p : ℝ) : ℝ := (m.choose j : ℝ) * p ^ j * (1 - p) ^ (m - j)

lemma bp_nonneg (m j : ℕ) (p : ℝ) (h0 : 0 ≤ p) (h1 : p ≤ 1) : 0 ≤ bp m j p := by
  unfold bp; have : 0 ≤ 1 - p := by linarith
  exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg h0 _)) (pow_nonneg this _)

/-- (L1) `k b_n(j) q = (k-j) b_k(j)` with `k = n+1`, `j ≤ n`. -/
lemma L1 (n j : ℕ) (p : ℝ) (hj : j ≤ n) :
    ((n : ℝ) + 1) * bp n j p * (1 - p) = ((n : ℝ) + 1 - j) * bp (n + 1) j p := by
  unfold bp
  have hc : ((n.choose j : ℕ) : ℝ) * ((n + 1 : ℕ) : ℝ) = (((n + 1).choose j : ℕ) : ℝ) * ((n + 1 - j : ℕ) : ℝ) := by
    exact_mod_cast Nat.choose_mul_succ_eq n j
  have he : n + 1 - j = (n - j) + 1 := by omega
  rw [he, pow_succ]
  have hcast : ((n - j + 1 : ℕ) : ℝ) = (n : ℝ) + 1 - j := by push_cast [hj]; ring
  rw [he, hcast] at hc
  push_cast at hc
  linear_combination (p ^ j * (1 - p) ^ (n - j) * (1 - p)) * hc

/-- (L2) `k b_n(j) p = (j+1) b_k(j+1)` with `k = n+1`. -/
lemma L2 (n j : ℕ) (p : ℝ) :
    ((n : ℝ) + 1) * bp n j p * p = ((j : ℝ) + 1) * bp (n + 1) (j + 1) p := by
  unfold bp
  have hc : ((n + 1 : ℕ) : ℝ) * ((n.choose j : ℕ) : ℝ) = (((n + 1).choose (j + 1) : ℕ) : ℝ) * ((j + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.add_one_mul_choose_eq n j
  have he : n + 1 - (j + 1) = n - j := by omega
  rw [he, pow_succ]
  push_cast at hc
  linear_combination (p ^ j * (1 - p) ^ (n - j) * p) * hc

/-- (L3) `b_k(j+1)(j+1) q = b_k(j)(k-j) p` for `j < k`. -/
lemma L3 (k j : ℕ) (p : ℝ) (hj : j < k) :
    bp k (j + 1) p * ((j : ℝ) + 1) * (1 - p) = bp k j p * ((k : ℝ) - j) * p := by
  unfold bp
  have hc : ((k.choose (j + 1) : ℕ) : ℝ) * ((j + 1 : ℕ) : ℝ) = ((k.choose j : ℕ) : ℝ) * ((k - j : ℕ) : ℝ) := by
    exact_mod_cast Nat.choose_succ_right_eq k j
  have he : k - j = (k - (j + 1)) + 1 := by omega
  have hcast : ((k - j : ℕ) : ℝ) = (k : ℝ) - j := by push_cast [hj.le]; ring
  rw [hcast] at hc
  push_cast at hc
  rw [he, pow_succ, pow_succ]
  linear_combination (p ^ j * (1 - p) ^ (k - (j + 1)) * p * (1 - p)) * hc

/-- Ratio identity, the pair product: `T(i) = b_k(c-i) b_k(c+1+i) = T(0) Q_i`. -/
lemma pair_prod (n c : ℕ) (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (hc : c ≤ n) :
    ∀ i : ℕ, i ≤ c → c + 1 + i ≤ n + 1 →
      bp (n + 1) (c - i) p * bp (n + 1) (c + 1 + i) p =
        bp (n + 1) c p * bp (n + 1) (c + 1) p * Q ((c : ℝ) + 1) (((n + 1 : ℕ) : ℝ) - c) i := by
  intro i
  induction i with
  | zero => intro _ _; simp [Q]
  | succ i ih =>
    intro hi1 hi2
    have ih' := ih (by omega) (by omega)
    have hq : 0 < 1 - p := by linarith
    have hcn' : (c : ℝ) ≤ n := by exact_mod_cast hc
    have hci : (i : ℝ) + 1 ≤ c := by exact_mod_cast hi1
    have hi0 : (0 : ℝ) ≤ i := Nat.cast_nonneg i
    have hl := L3 (n + 1) (c - (i + 1)) p (by omega)
    have e1 : c - (i + 1) + 1 = c - i := by omega
    rw [e1] at hl
    have hcast1 : ((c - (i + 1) : ℕ) : ℝ) = (c : ℝ) - i - 1 := by
      rw [Nat.cast_sub hi1]; push_cast; ring
    rw [hcast1] at hl
    have hr := L3 (n + 1) (c + 1 + i) p (by omega)
    have e2 : c + 1 + i + 1 = c + 1 + (i + 1) := by omega
    rw [e2] at hr
    push_cast at hl hr
    set α : ℝ := ((c : ℝ) - i) * (1 - p) / (((n : ℝ) + 1 - ((c : ℝ) - i - 1)) * p) with hα
    set β : ℝ := ((n : ℝ) + 1 - ((c : ℝ) + 1 + i)) * p / (((c : ℝ) + 1 + i + 1) * (1 - p)) with hβ
    have hd1 : (0 : ℝ) < (n : ℝ) + 1 - ((c : ℝ) - i - 1) := by linarith
    have hd2 : (0 : ℝ) < (c : ℝ) + 1 + i + 1 := by positivity
    have hnew_l : bp (n + 1) (c - (i + 1)) p = bp (n + 1) (c - i) p * α := by
      rw [hα, mul_div_assoc', eq_div_iff (mul_pos hd1 hp0).ne']
      linear_combination (-1 : ℝ) * hl
    have hnew_r : bp (n + 1) (c + 1 + (i + 1)) p = bp (n + 1) (c + 1 + i) p * β := by
      rw [hβ, mul_div_assoc', eq_div_iff (mul_pos hd2 hq).ne']
      linear_combination hr
    have hαβ : α * β = fac ((c : ℝ) + 1) (((n + 1 : ℕ) : ℝ) - c) i := by
      rw [hα, hβ]; unfold fac; push_cast
      have h1 : p ≠ 0 := hp0.ne'
      have h2 : (1 - p) ≠ 0 := hq.ne'
      have h3 : ((n : ℝ) + 1 - ((c : ℝ) - i - 1)) ≠ 0 := hd1.ne'
      have h4 : ((c : ℝ) + 1 + i + 1) ≠ 0 := hd2.ne'
      have h5 : ((c : ℝ) + 1 + (i + 1)) ≠ 0 := by positivity
      have h6 : ((n : ℝ) + 1 - c + (i + 1)) ≠ 0 := by
        have : (0 : ℝ) < (n : ℝ) + 1 - c + (i + 1) := by linarith
        exact this.ne'
      field_simp
      ring
    unfold Q at ih' ⊢
    rw [prod_range_succ, hnew_l, hnew_r]
    calc bp (n + 1) (c - i) p * α * (bp (n + 1) (c + 1 + i) p * β)
        = (bp (n + 1) (c - i) p * bp (n + 1) (c + 1 + i) p) * (α * β) := by ring
      _ = _ := by rw [ih', hαβ]; ring

/-- The full ratio identity:
`b_k(c-i) b_n(w-1) b_k(c+1+i) b_n(w) = (b_k(w) b_n(c))^2 A Q_i`. -/
lemma ratio_identity (n c w i : ℕ) (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (hc : c ≤ n)
    (hw1 : 1 ≤ w) (hwn : w ≤ n) (hi1 : i ≤ c) (hi2 : c + 1 + i ≤ n + 1) :
    (bp (n + 1) (c - i) p * bp n (w - 1) p) * (bp (n + 1) (c + 1 + i) p * bp n w p) =
      (bp (n + 1) w p * bp n c p) ^ 2 *
        ((w : ℝ) * (((n + 1 : ℕ) : ℝ) - w) / (((c : ℝ) + 1) * (((n + 1 : ℕ) : ℝ) - c))) *
        Q ((c : ℝ) + 1) (((n + 1 : ℕ) : ℝ) - c) i := by
  have hpp := pair_prod n c p hp0 hp1 hc i hi1 hi2
  have hq : 0 < 1 - p := by linarith
  -- b_n(w-1): k b_n(w-1) p = w b_k(w)
  have hw' := L2 n (w - 1) p
  have e : w - 1 + 1 = w := by omega
  rw [e] at hw'
  have hcw : ((w - 1 : ℕ) : ℝ) + 1 = w := by push_cast [hw1]; ring
  rw [hcw] at hw'
  have hw2 := L1 n w p hwn
  have hc1 := L1 n c p hc
  have hc2 := L2 n c p
  have hk : (((n + 1 : ℕ) : ℝ)) = (n : ℝ) + 1 := by push_cast; ring
  rw [hk]
  have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hcn : (c : ℝ) ≤ n := by exact_mod_cast hc
  have hkc : (0 : ℝ) < (n : ℝ) + 1 - c := by linarith
  -- express everything through b_n(c), b_k(w)
  have e1 : bp n (w - 1) p = (w : ℝ) * bp (n + 1) w p / (((n : ℝ) + 1) * p) := by
    rw [eq_div_iff (mul_pos hn hp0).ne']; linear_combination hw'
  have e2 : bp n w p = ((n : ℝ) + 1 - w) * bp (n + 1) w p / (((n : ℝ) + 1) * (1 - p)) := by
    rw [eq_div_iff (mul_pos hn hq).ne']; linear_combination hw2
  have e3 : bp (n + 1) c p = ((n : ℝ) + 1) * bp n c p * (1 - p) / ((n : ℝ) + 1 - c) := by
    rw [eq_div_iff hkc.ne']; linear_combination (-1 : ℝ) * hc1
  have e4 : bp (n + 1) (c + 1) p = ((n : ℝ) + 1) * bp n c p * p / ((c : ℝ) + 1) := by
    rw [eq_div_iff (by positivity)]; linear_combination (-1 : ℝ) * hc2
  have : bp (n + 1) (c - i) p * bp n (w - 1) p * (bp (n + 1) (c + 1 + i) p * bp n w p)
      = (bp (n + 1) (c - i) p * bp (n + 1) (c + 1 + i) p) * (bp n (w - 1) p * bp n w p) := by ring
  rw [this, hpp, e1, e2, e3, e4]
  rw [hk]
  have n1 : p ≠ 0 := hp0.ne'
  have n2 : (1 - p) ≠ 0 := hq.ne'
  have n3 : ((n : ℝ) + 1) ≠ 0 := hn.ne'
  have n4 : ((n : ℝ) + 1 - c) ≠ 0 := hkc.ne'
  have n5 : ((c : ℝ) + 1) ≠ 0 := by positivity
  field_simp <;> ring

lemma amgm (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) : 2 * √(x * y) ≤ x + y := by
  rw [sqrt_mul hx]
  nlinarith [sq_nonneg (√x - √y), sq_sqrt hx, sq_sqrt hy, sqrt_nonneg x, sqrt_nonneg y]

end BinomialMonotone

-- ===== Part 3: the staircase (Stair) =====

/-!
# MO 478827: the staircase (row starts `y0`, column tops `u`) and the per-row domination
`K = n + 1` is the number of trials; `cond y w` means `(y,w) ∈ R`, i.e. `g K + l y - (1+g) w > 0`.
-/

open Finset Real

noncomputable section

namespace BinomialMonotone

structure Hyp (g l : ℝ) : Prop where
  g0 : 0 < g
  g1 : g < 1
  l0 : 0 < l
  l2 : 2 * l ≤ 1 + g

variable {g l : ℝ}

abbrev cond (n : ℕ) (g l : ℝ) (y w : ℕ) : Prop := (1 + g) * (w : ℝ) < g * ((n : ℝ) + 1) + l * y

lemma ex_y0 (n : ℕ) (h : Hyp g l) (w : ℕ) : ∃ y : ℕ, cond n g l y w := by
  obtain ⟨y, hy⟩ := exists_nat_gt ((1 + g) * (w : ℝ) / l)
  refine ⟨y, ?_⟩
  unfold cond
  have hl := h.l0
  rw [div_lt_iff₀ hl] at hy
  have : 0 < g * ((n : ℝ) + 1) := by have := h.g0; positivity
  nlinarith

lemma ex_u (n : ℕ) (h : Hyp g l) (y : ℕ) : ∃ w : ℕ, ¬ cond n g l y (w + 1) := by
  obtain ⟨w, hw⟩ := exists_nat_gt ((g * ((n : ℝ) + 1) + l * y) / (1 + g))
  refine ⟨w, ?_⟩
  unfold cond
  have h1 : 0 < 1 + g := by have := h.g0; linarith
  rw [div_lt_iff₀ h1] at hw
  push_cast
  rw [not_lt]
  nlinarith

/-- first column of row `w` inside `R` -/
def y0 (n : ℕ) (h : Hyp g l) (w : ℕ) : ℕ := Nat.find (ex_y0 n h w)

/-- top of column `y` inside `R` -/
def u (n : ℕ) (h : Hyp g l) (y : ℕ) : ℕ := Nat.find (ex_u n h y)

variable (n : ℕ) (h : Hyp g l)
include h

lemma cond_mono_y {y y' w : ℕ} (hyy : y ≤ y') (hc : cond n g l y w) : cond n g l y' w := by
  unfold cond at *
  have : (y : ℝ) ≤ y' := by exact_mod_cast hyy
  have := h.l0
  nlinarith

lemma cond_anti_w {y w w' : ℕ} (hww : w' ≤ w) (hc : cond n g l y w) : cond n g l y w' := by
  unfold cond at *
  have : (w' : ℝ) ≤ w := by exact_mod_cast hww
  have := h.g0
  nlinarith

lemma cond_iff_y0 (y w : ℕ) : cond n g l y w ↔ y0 n h w ≤ y := by
  constructor
  · intro hc; exact Nat.find_min' (ex_y0 n h w) hc
  · intro hy; exact cond_mono_y n h hy (Nat.find_spec (ex_y0 n h w))

lemma cond_zero (y : ℕ) : cond n g l y 0 := by
  unfold cond
  have := h.g0; have := h.l0
  push_cast
  have : (0 : ℝ) ≤ y := Nat.cast_nonneg y
  nlinarith

lemma cond_iff_u (y w : ℕ) : cond n g l y w ↔ w ≤ u n h y := by
  constructor
  · intro hc
    by_contra hlt
    push_neg at hlt
    have hs : ¬ cond n g l y (u n h y + 1) := Nat.find_spec (ex_u n h y)
    exact hs (cond_anti_w n h (show u n h y + 1 ≤ w by omega) hc)
  · intro hw
    rcases Nat.eq_zero_or_pos w with h0 | hpos
    · rw [h0]; exact cond_zero n h y
    · have : w - 1 < u n h y := by omega
      have hm := Nat.find_min (ex_u n h y) (show w - 1 < Nat.find (ex_u n h y) from this)
      push_neg at hm
      have e : w - 1 + 1 = w := by omega
      rwa [e] at hm

lemma u_eq_of {y v : ℕ} (h1 : cond n g l y v) (h2 : ¬ cond n g l y (v + 1)) : u n h y = v := by
  rw [cond_iff_u n h] at h1 h2
  omega

lemma u_le (y : ℕ) (hy : y ≤ n + 1) : u n h y ≤ n := by
  unfold u
  apply Nat.find_min'
  unfold cond
  push_cast
  rw [not_lt]
  have : (y : ℝ) ≤ n + 1 := by exact_mod_cast hy
  have := h.l0; have := h.g0
  have hl1 : l ≤ 1 := by have := h.l2; have := h.g1; linarith
  nlinarith

lemma y0_zero : y0 n h 0 = 0 := by
  have := (cond_iff_y0 n h 0 0).mp (cond_zero n h 0)
  omega

lemma y0_mono {w w' : ℕ} (hww : w ≤ w') : y0 n h w ≤ y0 n h w' := by
  have hs : cond n g l (y0 n h w') w' := (cond_iff_y0 n h _ _).mpr le_rfl
  exact (cond_iff_y0 n h _ _).mp (cond_anti_w n h hww hs)

/-- `ρ = ⌊(1+g)/l⌋` -/
def rho (g l : ℝ) : ℕ := ⌊(1 + g) / l⌋₊

lemma rho_ge_two : 2 ≤ rho g l := by
  unfold rho
  apply Nat.le_floor
  rw [le_div_iff₀ h.l0]; push_cast; linarith [h.l2]

lemma gap (w : ℕ) (hw : 1 ≤ y0 n h w) : y0 n h w + rho g l ≤ y0 n h (w + 1) := by
  have hb : cond n g l (y0 n h (w + 1)) (w + 1) := (cond_iff_y0 n h _ _).mpr le_rfl
  have ha : ¬ cond n g l ((y0 n h w) - 1) w := by
    rw [cond_iff_y0 n h]; omega
  have hab : (y0 n h w) ≤ (y0 n h (w + 1)) := y0_mono n h (Nat.le_succ w)
  have hw' := hw
  unfold cond at hb ha
  push_neg at ha
  push_cast at hb
  have hcast : (((y0 n h w) - 1 : ℕ) : ℝ) = ((y0 n h w) : ℝ) - 1 := by push_cast [hw]; ring
  rw [hcast] at ha
  have hl := h.l0
  have key : (1 + g) / l < ((y0 n h (w + 1)) : ℝ) - (y0 n h w) + 1 := by
    rw [div_lt_iff₀ hl]; nlinarith
  have hr : (rho g l : ℝ) ≤ (1 + g) / l := by
    unfold rho; exact Nat.floor_le (by have := h.g0; positivity)
  have : (rho g l : ℝ) < ((y0 n h (w + 1)) : ℝ) - (y0 n h w) + 1 := lt_of_le_of_lt hr key
  have : rho g l < (y0 n h (w + 1)) - (y0 n h w) + 1 := by
    have e : (((y0 n h (w + 1)) - (y0 n h w) + 1 : ℕ) : ℝ) = ((y0 n h (w + 1)) : ℝ) - (y0 n h w) + 1 := by push_cast [hab]; ring
    have : (rho g l : ℝ) < (((y0 n h (w + 1)) - (y0 n h w) + 1 : ℕ) : ℝ) := by rw [e]; exact this
    exact_mod_cast this
  omega

lemma gap' (w w' : ℕ) (hw : 1 ≤ y0 n h w) (hww : w < w') : y0 n h w + rho g l ≤ y0 n h w' :=
  le_trans (gap n h w hw) (y0_mono n h hww)

/-- `s = ⌊c/w⌋ ≤ ρ` for an active row. -/
lemma s_le_rho (w : ℕ) (hw : 1 ≤ w) (ha : 1 ≤ y0 n h w) : (y0 n h w - 1) / w ≤ rho g l := by
  have hnc : ¬ cond n g l (y0 n h w - 1) w := by rw [cond_iff_y0 n h]; omega
  unfold cond at hnc; push_neg at hnc
  have hcst : (((y0 n h w - 1 : ℕ)) : ℝ) = (y0 n h w : ℝ) - 1 := by push_cast [ha]; ring
  rw [hcst] at hnc
  unfold rho
  apply Nat.le_floor
  rw [le_div_iff₀ h.l0]
  have hdw : ((((y0 n h w - 1) / w : ℕ) : ℝ)) * w ≤ (y0 n h w - 1) := by exact_mod_cast Nat.div_mul_le_self (y0 n h w - 1) w
  have hwR : (1 : ℝ) ≤ w := by exact_mod_cast hw
  have : 0 < g * ((n : ℝ) + 1) := by have := h.g0; positivity
  have hlc : l * ((y0 n h w - 1) : ℝ) ≤ (1 + g) * w := by nlinarith
  have hl := h.l0
  have h3 : (((y0 n h w - 1) / w : ℕ) : ℝ) * w * l ≤ (1 + g) * w := by nlinarith
  have h4 : (((y0 n h w - 1) / w : ℕ) : ℝ) * l * w ≤ (1 + g) * w := by linarith
  exact le_of_mul_le_mul_right h4 (by linarith)

/-- Case 1 inequality: if `2w ≥ c+1` then `4 w (K-w) ≥ (c+1)(K-c)` (here `c+1 = y0 w`). -/
lemma case1 (w : ℕ) (ha : 1 ≤ y0 n h w) (hk : y0 n h w ≤ n + 1) (hw2 : y0 n h w ≤ 2 * w) :
    ((y0 n h w : ℝ)) * (((n : ℝ) + 1) - ((y0 n h w : ℝ) - 1)) ≤ 4 * (w : ℝ) * (((n : ℝ) + 1) - w) := by
  have hc : cond n g l (y0 n h w) w := (cond_iff_y0 n h _ _).mpr le_rfl
  unfold cond at hc
  have h2N : 2 * w ≤ n + (y0 n h w) := by
    by_contra hcon; push_neg at hcon
    have hR : (n : ℝ) + 1 + (y0 n h w) ≤ 2 * (w : ℝ) := by exact_mod_cast (show n + 1 + (y0 n h w) ≤ 2 * w by omega)
    have hg := h.g1; have hl2 := h.l2; have hg0 := h.g0
    have hc0 : (0 : ℝ) ≤ (y0 n h w) := Nat.cast_nonneg _
    nlinarith
  have h2 : 2 * (w : ℝ) ≤ (n : ℝ) + (y0 n h w) := by exact_mod_cast h2N
  have hw2' : ((y0 n h w) : ℝ) ≤ 2 * w := by exact_mod_cast hw2
  have hkR : ((y0 n h w) : ℝ) ≤ n + 1 := by exact_mod_cast hk
  have hc1 : (1 : ℝ) ≤ (y0 n h w) := by exact_mod_cast ha
  have e1 : 0 ≤ ((n : ℝ) + 1) - (((y0 n h w) : ℝ) - 1) := by linarith
  have e2 : ((n : ℝ) + 1) - (((y0 n h w) : ℝ) - 1) ≤ 2 * (((n : ℝ) + 1) - w) := by linarith
  have e3 : (0 : ℝ) ≤ (y0 n h w) := by linarith
  calc ((y0 n h w) : ℝ) * (((n : ℝ) + 1) - (((y0 n h w) : ℝ) - 1)) ≤ (2 * w) * (2 * (((n : ℝ) + 1) - w)) :=
        mul_le_mul hw2' e2 e1 (by linarith)
    _ = 4 * (w : ℝ) * (((n : ℝ) + 1) - w) := by ring

end BinomialMonotone

-- ===== Part 4: derivative and domination (Main) =====

/-!
# MO 478827: `f_k(p) = P((1+g) X + l Y > k)` is strictly decreasing

`X ~ Bin(k, 1-p)`, `Y ~ Bin(k, p)` independent, `0 < g < 1`, `0 < l ≤ (1+g)/2`
(in particular `0 < l ≤ g < 1`, the hypothesis of the question).
-/

open Finset Polynomial Real

noncomputable section

namespace BinomialMonotone

open Classical

variable {g l : ℝ}

abbrev Bern (m j : ℕ) : ℝ[X] := bernsteinPolynomial ℝ m j

lemma eval_Bern (m j : ℕ) (p : ℝ) : (Bern m j).eval p = bp m j p := by
  simp [Bern, bernsteinPolynomial, bp]

/-- `a n 0 = 0`, `a n (j+1) = Bern n j` -/
def aP (n : ℕ) : ℕ → ℝ[X]
  | 0 => 0
  | j + 1 => Bern n j

lemma dBern (n j : ℕ) : derivative (Bern (n + 1) j) = ((n : ℝ[X]) + 1) * (aP n j - aP n (j + 1)) := by
  cases j with
  | zero =>
    simp only [Bern, aP]
    rw [bernsteinPolynomial.derivative_zero]
    simp <;> ring
  | succ j =>
    simp only [Bern, aP]
    rw [bernsteinPolynomial.derivative_succ]
    simp

/-- the polynomial `f` in the variables `(y, w)`, `W = k - X` -/
def F (n : ℕ) (g l : ℝ) : ℝ[X] :=
  ∑ y ∈ range (n + 2), ∑ w ∈ range (n + 2),
    if cond n g l y w then Bern (n + 1) y * Bern (n + 1) w else 0

/-- evaluated `a` -/
def ea (n : ℕ) (p : ℝ) (j : ℕ) : ℝ := (aP n j).eval p

lemma ea_zero (n : ℕ) (p : ℝ) : ea n p 0 = 0 := by simp [ea, aP]

lemma ea_succ (n j : ℕ) (p : ℝ) : ea n p (j + 1) = bp n j p := by simp [ea, aP, eval_Bern]

lemma ea_top (n : ℕ) (p : ℝ) : ea n p (n + 2) = 0 := by
  rw [ea_succ]; unfold bp; simp [Nat.choose_eq_zero_of_lt (Nat.lt_succ_self n)]

lemma tele_up (a : ℕ → ℝ) (t K : ℕ) :
    ∑ y ∈ range K, (if t ≤ y then a y - a (y + 1) else 0) = if t ≤ K then a t - a K else 0 := by
  induction K with
  | zero =>
    simp only [range_zero, sum_empty]
    split_ifs with h
    · have : t = 0 := by omega
      subst this; ring
    · rfl
  | succ K ih =>
    rw [sum_range_succ, ih]
    by_cases h1 : t ≤ K
    · have h2 : t ≤ K + 1 := by omega
      simp only [h1, h2, if_true]; ring
    · by_cases h3 : t = K + 1
      · subst h3; simp
      · have h4 : ¬ t ≤ K + 1 := by omega
        simp [h1, h4]

lemma tele_down (a : ℕ → ℝ) (t K : ℕ) (ht : t < K) :
    ∑ w ∈ range K, (if w ≤ t then a w - a (w + 1) else 0) = a 0 - a (t + 1) := by
  induction K with
  | zero => omega
  | succ K ih =>
    rw [sum_range_succ]
    by_cases h : t < K
    · rw [ih h]
      have : ¬ K ≤ t := by omega
      simp [this]
    · have ht' : t = K := by omega
      subst ht'
      simp only [le_refl, if_true]
      have : ∀ w ∈ range t, (if w ≤ t then a w - a (w + 1) else 0) = a w - a (w + 1) := by
        intro w hw; have : w ≤ t := by have := mem_range.mp hw; omega
        simp [this]
      rw [sum_congr rfl this, sum_range_sub']
      ring

variable (n : ℕ) (h : Hyp g l)
include h

/-- active rows: `1 ≤ y0 w ≤ n+1` -/
def act (w : ℕ) : Prop := 1 ≤ y0 n h w ∧ y0 n h w ≤ n + 1

def rowInd (p : ℝ) (y w : ℕ) : ℝ := if y0 n h w ≤ y then ea n p y - ea n p (y + 1) else 0

def colInd (p : ℝ) (y w : ℕ) : ℝ := if w ≤ u n h y then ea n p w - ea n p (w + 1) else 0

/-- the window of row `w` -/
def win (w : ℕ) : Finset ℕ :=
  Ico (y0 n h w - min (rho g l / 2) (min (y0 n h w) (n + 2 - y0 n h w)))
      (y0 n h w + min (rho g l / 2) (min (y0 n h w) (n + 2 - y0 n h w)))

/-- The derivative formula `f'(p) = K (Σ_w b_K(w) r(w) - Σ_y b_K(y) b_n(u y))`. -/
lemma deriv_formula (p : ℝ) :
    (derivative (F n g l)).eval p = ((n : ℝ) + 1) *
      (∑ w ∈ range (n + 2), bp (n + 1) w p * (if act n h w then bp n (y0 n h w - 1) p else 0) -
        ∑ y ∈ range (n + 2), bp (n + 1) y p * bp n (u n h y) p) := by
  have hd : derivative (F n g l) = ∑ y ∈ range (n + 2), ∑ w ∈ range (n + 2),
      if cond n g l y w then (derivative (Bern (n + 1) y) * Bern (n + 1) w +
        Bern (n + 1) y * derivative (Bern (n + 1) w)) else 0 := by
    unfold F
    simp only [derivative_sum]
    apply sum_congr rfl; intro y _; apply sum_congr rfl; intro w _
    split_ifs <;> simp [derivative_mul]
  have hterm : ∀ y w : ℕ, eval p (if cond n g l y w then (derivative (Bern (n + 1) y) * Bern (n + 1) w +
        Bern (n + 1) y * derivative (Bern (n + 1) w)) else 0) =
      ((n : ℝ) + 1) * (bp (n + 1) w p * rowInd n h p y w) +
      ((n : ℝ) + 1) * (bp (n + 1) y p * colInd n h p y w) := by
    intro y w
    unfold rowInd colInd
    by_cases hc : cond n g l y w
    · have h1 : y0 n h w ≤ y := (cond_iff_y0 n h y w).mp hc
      have h2 : w ≤ u n h y := (cond_iff_u n h y w).mp hc
      rw [if_pos hc, if_pos h1, if_pos h2]
      simp only [eval_add, eval_mul, dBern, eval_sub, eval_natCast, eval_one, eval_Bern, ea]
      ring
    · have h1 : ¬ y0 n h w ≤ y := fun hh => hc ((cond_iff_y0 n h y w).mpr hh)
      have h2 : ¬ w ≤ u n h y := fun hh => hc ((cond_iff_u n h y w).mpr hh)
      rw [if_neg hc, if_neg h1, if_neg h2]
      simp
  have hrow : ∀ w ∈ range (n + 2), ∑ y ∈ range (n + 2), rowInd n h p y w =
      (if act n h w then bp n (y0 n h w - 1) p else 0) := by
    intro w _
    unfold rowInd
    rw [tele_up (ea n p) (y0 n h w) (n + 2), ea_top]
    unfold act
    by_cases h0 : y0 n h w = 0
    · rw [h0]; simp [ea_zero]
    · by_cases h1 : y0 n h w ≤ n + 1
      · have h1' : 1 ≤ y0 n h w := by omega
        have h2 : y0 n h w ≤ n + 2 := by omega
        have e : y0 n h w = (y0 n h w - 1) + 1 := by omega
        rw [if_pos h2, if_pos ⟨h1', h1⟩, sub_zero, e, ea_succ]
        simp
      · by_cases h3 : y0 n h w = n + 2
        · have h4 : ¬ (1 ≤ y0 n h w ∧ y0 n h w ≤ n + 1) := by omega
          rw [if_neg h4, h3, if_pos le_rfl, ea_top]; ring
        · have h4 : ¬ y0 n h w ≤ n + 2 := by omega
          have h5 : ¬ (1 ≤ y0 n h w ∧ y0 n h w ≤ n + 1) := by omega
          rw [if_neg h4, if_neg h5]
  have hcol : ∀ y ∈ range (n + 2), ∑ w ∈ range (n + 2), colInd n h p y w = - bp n (u n h y) p := by
    intro y hy
    unfold colInd
    have hy' : y ≤ n + 1 := by have := mem_range.mp hy; omega
    rw [tele_down (ea n p) (u n h y) (n + 2) (by have := u_le n h y hy'; omega), ea_zero, ea_succ]
    ring
  calc (derivative (F n g l)).eval p
      = ∑ y ∈ range (n + 2), ∑ w ∈ range (n + 2),
          (((n : ℝ) + 1) * (bp (n + 1) w p * rowInd n h p y w) +
           ((n : ℝ) + 1) * (bp (n + 1) y p * colInd n h p y w)) := by
        rw [hd]; simp only [eval_finsetSum]
        exact sum_congr rfl (fun y _ => sum_congr rfl (fun w _ => hterm y w))
    _ = ((n : ℝ) + 1) * (∑ w ∈ range (n + 2), bp (n + 1) w p * ∑ y ∈ range (n + 2), rowInd n h p y w) +
        ((n : ℝ) + 1) * (∑ y ∈ range (n + 2), bp (n + 1) y p * ∑ w ∈ range (n + 2), colInd n h p y w) := by
        simp only [sum_add_distrib, mul_sum]
        congr 1
        rw [sum_comm]
    _ = _ := by
        have r1 : ∑ w ∈ range (n + 2), bp (n + 1) w p * ∑ y ∈ range (n + 2), rowInd n h p y w =
            ∑ w ∈ range (n + 2), bp (n + 1) w p * (if act n h w then bp n (y0 n h w - 1) p else 0) :=
          sum_congr rfl (fun w hw => by rw [hrow w hw])
        have r2 : ∑ y ∈ range (n + 2), bp (n + 1) y p * ∑ w ∈ range (n + 2), colInd n h p y w =
            ∑ y ∈ range (n + 2), bp (n + 1) y p * (- bp n (u n h y) p) :=
          sum_congr rfl (fun y hy => by rw [hcol y hy])
        rw [r1, r2]
        simp only [mul_neg, sum_neg_distrib]
        ring

/-- the per-row domination -/
lemma row_dom (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (w : ℕ) (hw : act n h w) :
    bp (n + 1) w p * bp n (y0 n h w - 1) p ≤
      ∑ y ∈ win n h w, bp (n + 1) y p * bp n (u n h y) p := by
  obtain ⟨ha1, ha2⟩ := hw
  unfold win
  obtain ⟨c, hcdef⟩ : ∃ c, c = y0 n h w - 1 := ⟨_, rfl⟩
  have hc1 : y0 n h w = c + 1 := by omega
  rw [← hcdef]
  have hcn : c ≤ n := by omega
  obtain ⟨m, hm⟩ : ∃ m, m = min (rho g l / 2) (min (y0 n h w) (n + 2 - y0 n h w)) := ⟨_, rfl⟩
  rw [← hm]
  have hr2 := rho_ge_two h
  have hm1 : 1 ≤ m := by rw [hm]; omega
  have hmc : m ≤ c + 1 := by rw [hm]; omega
  have hmk : c + 1 + m ≤ n + 2 := by rw [hm]; omega
  have hmr : m ≤ rho g l / 2 := by rw [hm]; omega
  have hw1 : 1 ≤ w := by
    by_contra hcon; push_neg at hcon
    have : w = 0 := by omega
    rw [this, y0_zero] at ha1; omega
  have hwn : w ≤ n := by
    have hcw : cond n g l (y0 n h w) w := (cond_iff_y0 n h _ _).mpr le_rfl
    have := (cond_iff_u n h _ _).mp hcw
    have := u_le n h (y0 n h w) ha2
    omega
  have uL : ∀ i, i < m → u n h (c - i) = w - 1 := by
    intro i hi
    apply u_eq_of n h
    · rw [cond_iff_y0 n h]
      by_cases hz : y0 n h (w - 1) = 0
      · omega
      · have hg := gap' n h (w - 1) w (by omega) (by omega)
        omega
    · have e : w - 1 + 1 = w := by omega
      rw [e, cond_iff_y0 n h]; omega
  have uR : ∀ i, i < m → u n h (c + 1 + i) = w := by
    intro i hi
    apply u_eq_of n h
    · rw [cond_iff_y0 n h]; omega
    · rw [cond_iff_y0 n h]
      have hg := gap n h w (by omega)
      omega
  have hsplit : ∑ y ∈ Ico (y0 n h w - m) (y0 n h w + m), bp (n + 1) y p * bp n (u n h y) p =
      ∑ i ∈ range m, (bp (n + 1) (c - i) p * bp n (w - 1) p + bp (n + 1) (c + 1 + i) p * bp n w p) := by
    rw [← sum_Ico_consecutive _ (show y0 n h w - m ≤ y0 n h w by omega) (show y0 n h w ≤ y0 n h w + m by omega)]
    rw [sum_Ico_eq_sum_range, sum_Ico_eq_sum_range, sum_add_distrib]
    have e1 : y0 n h w - (y0 n h w - m) = m := by omega
    have e2 : y0 n h w + m - y0 n h w = m := by omega
    rw [e1, e2]
    congr 1
    · rw [← sum_range_reflect (fun i => bp (n + 1) (c - i) p * bp n (w - 1) p) m]
      apply sum_congr rfl; intro j hj
      have hj' := mem_range.mp hj
      have e : y0 n h w - m + j = c - (m - 1 - j) := by omega
      rw [e, uL (m - 1 - j) (by omega)]
    · apply sum_congr rfl; intro i hi
      have hi' := mem_range.mp hi
      have e : y0 n h w + i = c + 1 + i := by omega
      rw [e, uR i hi']
  rw [hsplit]
  obtain ⟨neg, hneg⟩ : ∃ neg, neg = bp (n + 1) w p * bp n c p := ⟨_, rfl⟩
  obtain ⟨A, hA⟩ : ∃ A, A = (w : ℝ) * (((n + 1 : ℕ) : ℝ) - w) / (((c : ℝ) + 1) * (((n + 1 : ℕ) : ℝ) - c)) :=
    ⟨_, rfl⟩
  rw [← hneg]
  have hneg0 : 0 ≤ neg := by
    rw [hneg]; exact mul_nonneg (bp_nonneg _ _ _ hp0.le hp1.le) (bp_nonneg _ _ _ hp0.le hp1.le)
  have hcnR : (c : ℝ) ≤ n := by exact_mod_cast hcn
  have hkc : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) - c := by push_cast; linarith
  have hA0 : 0 ≤ A := by
    rw [hA]; apply div_nonneg
    · apply mul_nonneg (Nat.cast_nonneg _); push_cast
      have : (w : ℝ) ≤ n := by exact_mod_cast hwn
      linarith
    · exact (mul_pos (by positivity) hkc).le
  have pairs : ∀ i ∈ range m, 2 * neg * √A * √(Q ((c : ℝ) + 1) (((n + 1 : ℕ) : ℝ) - c) i) ≤
      bp (n + 1) (c - i) p * bp n (w - 1) p + bp (n + 1) (c + 1 + i) p * bp n w p := by
    intro i hi
    have hi' := mem_range.mp hi
    have hid := ratio_identity n c w i p hp0 hp1 hcn hw1 hwn (by omega) (by omega)
    rw [← hneg, ← hA] at hid
    have hx := mul_nonneg (bp_nonneg (n + 1) (c - i) p hp0.le hp1.le) (bp_nonneg n (w - 1) p hp0.le hp1.le)
    have hy := mul_nonneg (bp_nonneg (n + 1) (c + 1 + i) p hp0.le hp1.le) (bp_nonneg n w p hp0.le hp1.le)
    have hamgm := amgm _ _ hx hy
    rw [hid] at hamgm
    have hQ0 : 0 ≤ Q ((c : ℝ) + 1) (((n + 1 : ℕ) : ℝ) - c) i := by
      have hb := Bp_sq_le_Q ((c : ℝ) + 1) (((n + 1 : ℕ) : ℝ) - c) i (by positivity) hkc
        (by have : (i : ℝ) + 1 ≤ c + 1 := by exact_mod_cast (show i + 1 ≤ c + 1 by omega)
            linarith)
        (by push_cast
            have : (i : ℝ) + 1 + c ≤ n + 1 := by exact_mod_cast (show i + 1 + c ≤ n + 1 by omega)
            linarith)
      exact le_trans (sq_nonneg _) hb
    have hs : √(neg ^ 2 * A * Q ((c : ℝ) + 1) (((n + 1 : ℕ) : ℝ) - c) i) =
        neg * √A * √(Q ((c : ℝ) + 1) (((n + 1 : ℕ) : ℝ) - c) i) := by
      rw [sqrt_mul (mul_nonneg (sq_nonneg _) hA0), sqrt_mul (sq_nonneg _), sqrt_sq hneg0]
    rw [hs] at hamgm
    linarith
  have hsum := sum_le_sum pairs
  rw [← mul_sum] at hsum
  have key : 1 ≤ 2 * √A * ∑ i ∈ range m, √(Q ((c : ℝ) + 1) (((n + 1 : ℕ) : ℝ) - c) i) := by
    by_cases hcase : y0 n h w ≤ 2 * w
    · have h1 := case1 n h w ha1 ha2 hcase
      rw [hc1] at h1
      have hA4 : 1 / 4 ≤ A := by
        rw [hA, le_div_iff₀ (mul_pos (by positivity) hkc)]
        push_cast at h1 ⊢
        nlinarith
      have hsA : 1 / 2 ≤ √A := by rw [Real.le_sqrt (by norm_num) hA0]; nlinarith
      have hS : 1 ≤ ∑ i ∈ range m, √(Q ((c : ℝ) + 1) (((n + 1 : ℕ) : ℝ) - c) i) := by
        have := single_le_sum (f := fun i => √(Q ((c : ℝ) + 1) (((n + 1 : ℕ) : ℝ) - c) i))
            (fun i _ => sqrt_nonneg _) (mem_range.mpr hm1)
        simpa [Q] using this
      nlinarith [mul_le_mul hsA hS (by norm_num) (sqrt_nonneg A)]
    · push_neg at hcase
      have h2w : 2 * w ≤ c := by omega
      have hC := lemmaC (n + 1) c w (by omega) hw1 h2w
      rw [← hA] at hC
      have hs := s_le_rho n h w hw1 ha1
      rw [← hcdef] at hs
      obtain ⟨sv, hsv⟩ : ∃ sv, sv = c / w := ⟨_, rfl⟩
      rw [← hsv] at hs hC
      have hm0 : min (max 1 (sv / 2)) (min (c + 1) (n + 1 - c)) ≤ m := by
        have : sv / 2 ≤ rho g l / 2 := Nat.div_le_div_right hs
        rw [hm]; omega
      have hmono : ∑ i ∈ range (min (max 1 (sv / 2)) (min (c + 1) (n + 1 - c))),
            √(Q ((c : ℝ) + 1) (((n + 1 : ℕ) : ℝ) - c) i) ≤
          ∑ i ∈ range m, √(Q ((c : ℝ) + 1) (((n + 1 : ℕ) : ℝ) - c) i) :=
        sum_le_sum_of_subset_of_nonneg (range_subset_range.mpr hm0) (fun _ _ _ => sqrt_nonneg _)
      have hsA : 0 ≤ 2 * √A := by positivity
      calc (1 : ℝ) ≤ _ := hC
        _ ≤ 2 * √A * ∑ i ∈ range m, √(Q ((c : ℝ) + 1) (((n + 1 : ℕ) : ℝ) - c) i) :=
            mul_le_mul_of_nonneg_left hmono hsA
  calc neg = neg * 1 := by ring
    _ ≤ neg * (2 * √A * ∑ i ∈ range m, √(Q ((c : ℝ) + 1) (((n + 1 : ℕ) : ℝ) - c) i)) :=
        mul_le_mul_of_nonneg_left key hneg0
    _ = 2 * neg * √A * ∑ i ∈ range m, √(Q ((c : ℝ) + 1) (((n + 1 : ℕ) : ℝ) - c) i) := by ring
    _ ≤ _ := hsum

/-- the derivative is `≤ 0` on `(0,1)` -/
lemma deriv_nonpos (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) : (derivative (F n g l)).eval p ≤ 0 := by
  rw [deriv_formula n h p]
  apply mul_nonpos_of_nonneg_of_nonpos (by positivity)
  rw [sub_nonpos]
  obtain ⟨S, hS⟩ : ∃ S, S = (range (n + 2)).filter (act n h) := ⟨_, rfl⟩
  have hpos : ∀ y, 0 ≤ bp (n + 1) y p * bp n (u n h y) p := fun y =>
    mul_nonneg (bp_nonneg _ _ _ hp0.le hp1.le) (bp_nonneg _ _ _ hp0.le hp1.le)
  have step1 : ∑ w ∈ range (n + 2), bp (n + 1) w p * (if act n h w then bp n (y0 n h w - 1) p else 0) =
      ∑ w ∈ S, bp (n + 1) w p * bp n (y0 n h w - 1) p := by
    rw [hS, sum_filter]; apply sum_congr rfl; intro w _; split_ifs <;> simp
  rw [step1]
  have step2 : ∑ w ∈ S, bp (n + 1) w p * bp n (y0 n h w - 1) p ≤
      ∑ w ∈ S, ∑ y ∈ win n h w, bp (n + 1) y p * bp n (u n h y) p := by
    apply sum_le_sum; intro w hw
    rw [hS, mem_filter] at hw
    exact row_dom n h p hp0 hp1 w hw.2
  have hdisj : Set.PairwiseDisjoint (↑S) (win n h) := by
    intro w hw w' hw' hne
    have hw2 : act n h w := by rw [hS] at hw; exact (mem_filter.mp (mem_coe.mp hw)).2
    have hw2' : act n h w' := by rw [hS] at hw'; exact (mem_filter.mp (mem_coe.mp hw')).2
    unfold act at hw2 hw2'
    show Disjoint (win n h w) (win n h w')
    rw [disjoint_left]
    intro y hy hy'
    unfold win at hy hy'
    rw [mem_Ico] at hy hy'
    have hr2 := rho_ge_two h
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · have := gap' n h w w' hw2.1 hlt
      omega
    · have := gap' n h w' w hw2'.1 hlt
      omega
  have step3 : ∑ w ∈ S, ∑ y ∈ win n h w, bp (n + 1) y p * bp n (u n h y) p ≤
      ∑ y ∈ range (n + 2), bp (n + 1) y p * bp n (u n h y) p := by
    rw [← sum_biUnion hdisj]
    apply sum_le_sum_of_subset_of_nonneg
    · intro y hy
      rw [mem_biUnion] at hy
      obtain ⟨w, hw, hyw⟩ := hy
      have hw2 : act n h w := by rw [hS] at hw; exact (mem_filter.mp hw).2
      unfold act at hw2
      unfold win at hyw
      rw [mem_Ico] at hyw
      rw [mem_range]; omega
    · intro y _ _; exact hpos y
  linarith

lemma F_eval_zero : (F n g l).eval 0 = 1 := by
  unfold F
  simp only [eval_finsetSum]
  have h1 : ∀ y ∈ range (n + 2), ∑ w ∈ range (n + 2),
      eval 0 (if cond n g l y w then Bern (n + 1) y * Bern (n + 1) w else 0) = if y = 0 then 1 else 0 := by
    intro y _
    rw [sum_eq_single 0]
    · by_cases hy : y = 0
      · subst hy; rw [if_pos (cond_zero n h 0)]; simp [Bern, bernsteinPolynomial.eval_at_0]
      · split_ifs <;> simp [Bern, bernsteinPolynomial.eval_at_0, hy]
    · intro w _ hw; split_ifs <;> simp [Bern, bernsteinPolynomial.eval_at_0, hw]
    · intro h0; simp at h0
  rw [sum_congr rfl h1]; simp

lemma F_eval_one : (F n g l).eval 1 = 0 := by
  unfold F
  simp only [eval_finsetSum]
  apply sum_eq_zero; intro y hy; apply sum_eq_zero; intro w hw
  by_cases hyk : y = n + 1
  · by_cases hwk : w = n + 1
    · have hnc : ¬ cond n g l y w := by
        unfold cond; rw [hyk, hwk]; push_cast; rw [not_lt]
        have := h.l2; have := h.g1; have := h.l0
        have hl1 : l ≤ 1 := by linarith
        nlinarith [mul_nonneg (sub_nonneg.mpr hl1) (by positivity : (0 : ℝ) ≤ (n : ℝ) + 1)]
      rw [if_neg hnc]; simp
    · split_ifs <;> simp [Bern, bernsteinPolynomial.eval_at_1, hwk]
  · split_ifs <;> simp [Bern, bernsteinPolynomial.eval_at_1, hyk]

/-- Main theorem in the `(Y, W)` form. -/
theorem F_strictAnti : StrictAntiOn (fun p => (F n g l).eval p) (Set.Icc 0 1) := by
  have hanti : AntitoneOn (fun p => (F n g l).eval p) (Set.Icc 0 1) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc 0 1) (F n g l).continuous.continuousOn
      (F n g l).differentiable.differentiableOn
    intro x hx
    rw [interior_Icc] at hx
    rw [Polynomial.deriv]
    exact deriv_nonpos n h x hx.1 hx.2
  intro a ha b hb hab
  apply lt_of_le_of_ne (hanti ha hb hab.le)
  intro heq
  -- constant on [a,b], hence everywhere
  have hconst : F n g l = Polynomial.C ((F n g l).eval a) := by
    apply Polynomial.eq_of_infinite_eval_eq
    apply Set.Infinite.mono _ (Set.Icc_infinite hab)
    intro x hx
    simp only [Set.mem_setOf_eq, eval_C]
    have hx' : x ∈ Set.Icc (0 : ℝ) 1 := ⟨le_trans ha.1 hx.1, le_trans hx.2 hb.2⟩
    have h1 : (F n g l).eval x ≤ (F n g l).eval a := hanti ha hx' hx.1
    have h2 : (F n g l).eval b ≤ (F n g l).eval x := hanti hx' hb hx.2
    have heq' : (F n g l).eval b = (F n g l).eval a := heq
    linarith
  have e0 := F_eval_zero n h
  have e1 := F_eval_one n h
  rw [hconst] at e0 e1
  simp at e0 e1
  linarith

end BinomialMonotone

-- ===== Part 5: the theorem in the explicit binomial form (Final) =====

/-!
# MathOverflow 478827 — literal statement

For `g, l ∈ (0,1)` with `g ≥ l`, `X ~ Bin(k, 1-p)`, `Y ~ Bin(k, p)` independent,
`f_k(p) = P((1+g) X + l Y > k)` is strictly decreasing in `p ∈ [0,1]`.
We prove it under the weaker hypothesis `0 < g < 1`, `0 < l`, `2 l ≤ 1 + g`.
-/

open Finset Real

noncomputable section

namespace BinomialMonotone

/-- `f_k(p) = P((1+g) X + l Y > k)` written out with the two binomial pmfs. -/
def fk (k : ℕ) (g l : ℝ) (p : ℝ) : ℝ :=
  ∑ x ∈ range (k + 1), ∑ y ∈ range (k + 1),
    if (k : ℝ) < (1 + g) * x + l * y then
      ((k.choose x : ℝ) * (1 - p) ^ x * p ^ (k - x)) * ((k.choose y : ℝ) * p ^ y * (1 - p) ^ (k - y))
    else 0

lemma fk_eq (n : ℕ) (g l : ℝ) (p : ℝ) : fk (n + 1) g l p = (F n g l).eval p := by
  classical
  unfold fk F
  simp only [Polynomial.eval_finsetSum]
  rw [show n + 1 + 1 = n + 2 from rfl]
  conv_lhs => rw [← sum_range_reflect]
  rw [sum_comm]
  apply sum_congr rfl; intro y hy
  apply sum_congr rfl; intro w hw
  have hw' : w ≤ n + 1 := by have := mem_range.mp hw; omega
  have e1 : n + 2 - 1 - w = n + 1 - w := by omega
  rw [e1]
  have hcast : (((n + 1 - w : ℕ)) : ℝ) = (n : ℝ) + 1 - w := by push_cast [hw']; ring
  have hiff : ((n + 1 : ℕ) : ℝ) < (1 + g) * (((n + 1 - w : ℕ)) : ℝ) + l * y ↔ cond n g l y w := by
    rw [hcast]; unfold cond; push_cast; constructor <;> intro h <;> linarith
  have hch : (n + 1).choose (n + 1 - w) = (n + 1).choose w := Nat.choose_symm hw'
  have hpw : n + 1 - (n + 1 - w) = w := by omega
  by_cases hc : cond n g l y w
  · rw [if_pos (hiff.mpr hc), if_pos hc, Polynomial.eval_mul, eval_Bern, eval_Bern]
    unfold bp
    rw [hch, hpw]; ring
  · rw [if_neg (fun h => hc (hiff.mp h)), if_neg hc, Polynomial.eval_zero]

/-- **Theorem (general form).** -/
theorem fk_strictAnti (k : ℕ) (hk : 1 ≤ k) (g l : ℝ) (hg0 : 0 < g) (hg1 : g < 1) (hl0 : 0 < l)
    (hl2 : 2 * l ≤ 1 + g) : StrictAntiOn (fk k g l) (Set.Icc 0 1) := by
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
  have h : Hyp g l := ⟨hg0, hg1, hl0, hl2⟩
  have : fk (n + 1) g l = fun p => (F n g l).eval p := funext (fk_eq n g l)
  rw [this]
  exact F_strictAnti n h

/-- **MathOverflow 478827**, exactly as asked: `g, l ∈ (0,1)`, `g ≥ l`. -/
theorem mo478827 (k : ℕ) (hk : 1 ≤ k) (g l : ℝ) (hl0 : 0 < l) (hlg : l ≤ g) (hg1 : g < 1) :
    StrictAntiOn (fun p : ℝ => ∑ x ∈ range (k + 1), ∑ y ∈ range (k + 1),
      if (k : ℝ) < (1 + g) * x + l * y then
        ((k.choose x : ℝ) * (1 - p) ^ x * p ^ (k - x)) * ((k.choose y : ℝ) * p ^ y * (1 - p) ^ (k - y))
      else 0) (Set.Icc 0 1) :=
  fk_strictAnti k hk g l (lt_of_lt_of_le hl0 hlg) hg1 hl0 (by linarith)

end BinomialMonotone
