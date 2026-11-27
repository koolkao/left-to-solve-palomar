/-
Copyright 2026 Ming-Chih Kao. Licensed under the Apache License, Version 2.0;
see the LICENSE file at the root of this repository.
-/
module

public import FriedanQ.Pair

/-! Port: copied from `quantum-lean/FriedanQ/Schur.lean` of github.com/koolkao/friedan-entropy-inequality (commit 0f4ba65dc126f59e7158fbcbc01548baa78cf21d, Lean v4.36.0, Mathlib fc4f59e, physlib edc607c) and put into the module system (`module` header, `public import`, public section). The proofs are unchanged unless a comment marked `Port` says otherwise. -/

@[expose] public section

/-!
# Schur step: `g(x) = K² log K - K ∑ eˣⁱ xᵢ` (`= (∑ eˣ)² H(softmax x)`) preserves weak majorization

Vectors are `ℕ → ℝ`, used on `range n`. For `x, y` antitone on `range n` with
`∑_{i<k} x i ≤ ∑_{i<k} y i` for all `k ≤ n`, `G n x ≤ G n y` (`G_le`). Proof: along the segment
`z(t) = x + t (y - x)` (antitone for `t ∈ [0,1]`), `d/dt G = ∑ (yᵢ - xᵢ) Wᵢ` with
`Wᵢ = K² Zᵢ (H(Z) - log Zᵢ)` nonnegative and antitone in `i` (`pair_vec`), so Abel summation
(`abel_nonneg`) makes the derivative nonnegative.
-/

open Real Finset

namespace FriedanQ

/-! ## Abel summation and subset sums -/

lemma abel_nonneg (n : ℕ) : ∀ (w d : ℕ → ℝ), (∀ i j, i ≤ j → j < n → w j ≤ w i) →
    (∀ i < n, 0 ≤ w i) → (∀ k ≤ n, 0 ≤ ∑ i ∈ range k, d i) →
    0 ≤ ∑ i ∈ range n, w i * d i := by
  induction n with
  | zero => intros; simp
  | succ n ih =>
    intro w d hw hw0 hd
    have hid : ∑ i ∈ range (n + 1), w i * d i =
        ∑ i ∈ range n, (w i - w n) * d i + w n * ∑ i ∈ range (n + 1), d i := by
      simp only [sub_mul, sum_sub_distrib, sum_range_succ, mul_add, mul_sum]
      ring
    rw [hid]
    have h1 : 0 ≤ ∑ i ∈ range n, (w i - w n) * d i := by
      apply ih (fun i => w i - w n) d
      · intro i j hij hj; have := hw i j hij (by omega); linarith
      · intro i hi; have := hw i n hi.le (by omega); linarith
      · intro k hk; exact hd k (by omega)
    have h2 : 0 ≤ w n * ∑ i ∈ range (n + 1), d i :=
      mul_nonneg (hw0 n (by omega)) (hd (n + 1) le_rfl)
    linarith

/-- For `f` antitone on `range n`, the sum over any `k`-subset of `range n` is at most the sum of
the first `k` values. -/
lemma sum_subset_le_prefix {n : ℕ} (f : ℕ → ℝ) (hf : ∀ i j, i ≤ j → j < n → f j ≤ f i)
    (T : Finset ℕ) (hT : T ⊆ range n) : ∑ i ∈ T, f i ≤ ∑ i ∈ range T.card, f i := by
  set R := range T.card
  have e1 := sum_sdiff (f := f) (inter_subset_left : T ∩ R ⊆ T)
  have e2 := sum_sdiff (f := f) (inter_subset_right : T ∩ R ⊆ R)
  rw [sdiff_inter_self_left] at e1
  rw [sdiff_inter_self_right] at e2
  have hc : (T \ R).card = (R \ T).card := card_sdiff_comm (by simp [R])
  suffices h : ∑ i ∈ T \ R, f i ≤ ∑ i ∈ R \ T, f i by linarith
  rcases (T \ R).eq_empty_or_nonempty with he | ⟨t0, ht0⟩
  · rw [he, card_empty] at hc
    rw [he, card_eq_zero.1 hc.symm]
  · have ht0' := mem_sdiff.1 ht0
    have hkn : T.card < n := by
      have : T.card ≤ t0 := by simpa [R] using ht0'.2
      have := mem_range.1 (hT ht0'.1); omega
    calc ∑ i ∈ T \ R, f i ≤ (T \ R).card • f T.card := by
          apply sum_le_card_nsmul
          intro t ht
          have ht' := mem_sdiff.1 ht
          exact hf _ _ (by simpa [R] using ht'.2) (mem_range.1 (hT ht'.1))
      _ = (R \ T).card • f T.card := by rw [hc]
      _ ≤ ∑ i ∈ R \ T, f i := by
          apply card_nsmul_le_sum
          intro s hs
          have hs' := mem_sdiff.1 hs
          exact hf _ _ (by simpa [R] using (mem_range.1 hs'.1).le) hkn

/-! ## The function `G` and its derivative along a segment -/

noncomputable def Kx (n : ℕ) (x : ℕ → ℝ) : ℝ := ∑ i ∈ range n, exp (x i)
noncomputable def Ex (n : ℕ) (x : ℕ → ℝ) : ℝ := ∑ i ∈ range n, exp (x i) * x i
/-- `G n x = K² log K - K E = K² H(softmax x)` (`G_eq`). -/
noncomputable def G (n : ℕ) (x : ℕ → ℝ) : ℝ := Kx n x ^ 2 * log (Kx n x) - Kx n x * Ex n x

lemma Kx_pos {n : ℕ} (hn : 0 < n) (x : ℕ → ℝ) : 0 < Kx n x :=
  sum_pos (fun i _ => exp_pos _) (nonempty_range_iff.2 hn.ne')

lemma G_eq {n : ℕ} (hn : 0 < n) (x : ℕ → ℝ) :
    G n x = Kx n x ^ 2 * ∑ i ∈ range n, negMulLog (exp (x i) / Kx n x) := by
  have hK := Kx_pos hn x
  have e : ∀ i, Kx n x ^ 2 * negMulLog (exp (x i) / Kx n x) =
      Kx n x * log (Kx n x) * exp (x i) - Kx n x * (exp (x i) * x i) := by
    intro i
    unfold negMulLog
    rw [log_div (exp_pos _).ne' hK.ne', log_exp]
    field_simp
    ring
  rw [mul_sum, sum_congr rfl (fun i _ => e i), sum_sub_distrib, ← mul_sum, ← mul_sum]
  unfold G Ex
  rw [show ∑ i ∈ range n, exp (x i) = Kx n x from rfl]
  ring

/-- the weight `Wᵢ = ∂G/∂xᵢ` -/
noncomputable def W (n : ℕ) (z : ℕ → ℝ) (i : ℕ) : ℝ :=
  exp (z i) * (2 * Kx n z * log (Kx n z) - Ex n z - Kx n z * z i)

lemma hasDerivAt_G_seg {n : ℕ} (hn : 0 < n) (x y : ℕ → ℝ) (t : ℝ) :
    HasDerivAt (fun s => G n (fun i => x i + s * (y i - x i)))
      (∑ i ∈ range n, (y i - x i) * W n (fun i => x i + t * (y i - x i)) i) t := by
  set z := fun i => x i + t * (y i - x i) with hz
  have hzi : ∀ i, HasDerivAt (fun s => x i + s * (y i - x i)) (y i - x i) t := by
    intro i
    simpa using ((hasDerivAt_id t).mul_const (y i - x i)).const_add (x i)
  have hK : HasDerivAt (fun s => Kx n (fun i => x i + s * (y i - x i)))
      (∑ i ∈ range n, exp (z i) * (y i - x i)) t := by
    unfold Kx
    exact HasDerivAt.fun_sum (fun i _ => (hzi i).exp)
  have hE : HasDerivAt (fun s => Ex n (fun i => x i + s * (y i - x i)))
      (∑ i ∈ range n, (exp (z i) * (y i - x i) * z i + exp (z i) * (y i - x i))) t := by
    unfold Ex
    exact HasDerivAt.fun_sum (fun i _ => ((hzi i).exp.mul (hzi i)))
  have hKpos : 0 < Kx n z := Kx_pos hn z
  have hlog := hK.log hKpos.ne'
  have hG := ((hK.pow 2).mul hlog).sub (hK.mul hE)
  unfold G
  convert hG using 1
  simp only [← hz]
  set K := Kx n z
  set E := Ex n z
  set K' := ∑ i ∈ range n, exp (z i) * (y i - x i)
  have h1 : ∑ i ∈ range n, (y i - x i) * W n z i =
      (2 * K * log K - E) * K' - K * ∑ i ∈ range n, exp (z i) * (y i - x i) * z i := by
    unfold W
    rw [mul_sum, mul_sum, ← sum_sub_distrib]
    refine sum_congr rfl (fun i _ => ?_)
    simp only [K, E]
    ring
  rw [h1, sum_add_distrib]
  simp only [Pi.pow_apply]
  rw [show (Kx n fun i => x i + t * (y i - x i)) = K from rfl]
  field_simp
  ring

/-- `Wᵢ` is nonnegative and antitone along antitone `z`. -/
lemma W_props {n : ℕ} (hn : 0 < n) (z : ℕ → ℝ) (hz : ∀ i j, i ≤ j → j < n → z j ≤ z i) :
    (∀ i < n, 0 ≤ W n z i) ∧ (∀ i j, i ≤ j → j < n → W n z j ≤ W n z i) := by
  set K := Kx n z
  have hK : 0 < K := Kx_pos hn z
  set Z : ℕ → ℝ := fun i => exp (z i) / K
  have hZ : ∀ k < n, 0 < Z k := fun k _ => div_pos (exp_pos _) hK
  have hZs : ∑ k ∈ range n, Z k = 1 := by
    simp only [Z, ← sum_div]; exact div_self hK.ne'
  set H := ∑ k ∈ range n, negMulLog (Z k)
  have hH : H = -(Ex n z) / K + log K := by
    simp only [H, Z, negMulLog]
    have e : ∀ k, -(exp (z k) / K) * log (exp (z k) / K) =
        -(exp (z k) * z k) / K + log K * (exp (z k) / K) := by
      intro k; rw [log_div (exp_pos _).ne' hK.ne', log_exp]; ring
    rw [sum_congr rfl (fun k _ => e k), sum_add_distrib, ← sum_div, ← mul_sum,
      ← sum_div, show ∑ k ∈ range n, exp (z k) = K from rfl, div_self hK.ne', mul_one]
    unfold Ex; simp only [sum_neg_distrib]
  have hWZ : ∀ i, W n z i = K ^ 2 * (Z i * (H - log (Z i))) := by
    intro i
    unfold W
    rw [hH]
    simp only [Z]
    rw [log_div (exp_pos _).ne' hK.ne', log_exp]
    field_simp
    ring
  have hZle : ∀ k < n, Z k ≤ 1 := by
    intro k hk
    have := single_le_sum (fun l hl => (hZ l (mem_range.1 hl)).le) (mem_range.2 hk)
    linarith
  constructor
  · intro i hi
    rw [hWZ]
    have hH0 : 0 ≤ H := sum_nonneg fun k hk =>
      negMulLog_nonneg (hZ k (mem_range.1 hk)).le (hZle k (mem_range.1 hk))
    have hl : log (Z i) ≤ 0 := log_nonpos (hZ i hi).le (hZle i hi)
    exact mul_nonneg (by positivity) (mul_nonneg (hZ i hi).le (by linarith))
  · intro i j hij hj
    rcases eq_or_ne i j with h | h
    · subst h; rfl
    rw [hWZ, hWZ]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply pair_vec hZ hZs (by omega) hj h
    simp only [Z]
    exact div_le_div_of_nonneg_right (exp_le_exp.2 (hz i j hij hj)) hK.le

/-- **Schur step.** -/
theorem G_le (n : ℕ) (x y : ℕ → ℝ) (hx : ∀ i j, i ≤ j → j < n → x j ≤ x i)
    (hy : ∀ i j, i ≤ j → j < n → y j ≤ y i)
    (hmaj : ∀ k ≤ n, ∑ i ∈ range k, x i ≤ ∑ i ∈ range k, y i) : G n x ≤ G n y := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; simp [G, Kx, Ex]
  set φ := fun s : ℝ => G n (fun i => x i + s * (y i - x i))
  have hd := hasDerivAt_G_seg hn x y
  have hmono : MonotoneOn φ (Set.Icc 0 1) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 1)
      (fun s _ => (hd s).continuousAt.continuousWithinAt)
      (fun s _ => (hd s).hasDerivWithinAt)
    intro s hs
    rw [interior_Icc] at hs
    have hzs : ∀ i j, i ≤ j → j < n →
        x j + s * (y j - x j) ≤ x i + s * (y i - x i) := by
      intro i j hij hj
      have h1 := hx i j hij hj; have h2 := hy i j hij hj
      nlinarith [hs.1, hs.2]
    obtain ⟨h0, hanti⟩ := W_props hn _ hzs
    rw [sum_congr rfl (fun i _ => mul_comm _ _)]
    apply abel_nonneg n _ _ hanti h0
    intro k hk
    have := hmaj k hk
    rw [sum_sub_distrib]; linarith
  have h01 := hmono (show (0 : ℝ) ∈ Set.Icc 0 1 by simp) (show (1 : ℝ) ∈ Set.Icc 0 1 by simp)
    zero_le_one
  simp only [φ, zero_mul, add_zero, one_mul, add_sub_cancel] at h01
  exact h01

end FriedanQ

end
