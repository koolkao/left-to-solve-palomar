/-
Copyright 2026 Ming-Chih Kao. Licensed under the Apache License, Version 2.0;
see the LICENSE file at the root of this repository.
-/
module

public import FriedanQ.Classical

/-! Port: copied from `quantum-lean/FriedanQ/Pair.lean` of github.com/koolkao/friedan-entropy-inequality (commit 0f4ba65dc126f59e7158fbcbc01548baa78cf21d, Lean v4.36.0, Mathlib fc4f59e, physlib edc607c) and put into the module system (`module` header, `public import`, public section). The proofs are unchanged unless a comment marked `Port` says otherwise. -/

@[expose] public section

/-!
# The pair lemma (Schur–Ostrowski condition for `g(x) = (∑ eˣ)² H(softmax x)`)

For a probability vector `Z > 0` and `Z_j ≤ Z_i`:
`Z_j (H(Z) - log Z_j) ≤ Z_i (H(Z) - log Z_i)`.
Its core is the two-variable inequality `pair_core`, which reduces to `Friedan.dd_nonneg`
(Lemma 5 of the classical proof) by the scaling `u = w y`, `v = w (1 - y)`.
-/

open Real Finset

namespace FriedanQ

lemma negMulLog_le_one_sub {y : ℝ} (hy : 0 ≤ y) : negMulLog y ≤ 1 - y := by
  rcases hy.eq_or_lt with h | h
  · subst h; simp
  have := Real.one_sub_inv_le_log_of_pos h
  unfold negMulLog
  have e : y * (1 - y⁻¹) = y - 1 := by field_simp
  nlinarith

/-- Core two-variable inequality: `(1 - u + v) η(v) ≤ (1 + u - v) η(u)` for `0 < v ≤ u`,
`u + v ≤ 1`. -/
lemma pair_core {u v : ℝ} (hv : 0 < v) (hvu : v ≤ u) (huv : u + v ≤ 1) :
    (1 - u + v) * negMulLog v ≤ (1 + u - v) * negMulLog u := by
  set w := u + v with hwdef
  have hu : 0 < u := lt_of_lt_of_le hv hvu
  have hw : 0 < w := by positivity
  set y := u / w with hydef
  have huy : u = w * y := by rw [hydef]; field_simp
  have hvy : v = w * (1 - y) := by rw [hydef]; field_simp; linarith
  have hy0 : 0 < y := div_pos hu hw
  have hy1 : 0 < 1 - y := by
    have : 0 < w * (1 - y) := by rw [← hvy]; exact hv
    exact pos_of_mul_pos_right this hw.le
  have hyh : 1 / 2 ≤ y := by
    rw [hydef, le_div_iff₀ hw]; linarith
  have hdd' : 0 ≤ Friedan.dd y := Friedan.dd_nonneg hyh (by linarith)
  have hlu : log u = log w + log y := by rw [huy, Real.log_mul hw.ne' hy0.ne']
  have hlv : log v = log w + log (1 - y) := by rw [hvy, Real.log_mul hw.ne' hy1.ne']
  set L := -log w with hL
  have hL1 : 1 - w ≤ L := by have := Real.log_le_sub_one_of_pos hw; rw [hL]; linarith
  have hL0 : 0 ≤ L := by rw [hL]; have := Real.log_nonpos hw.le (by linarith); linarith
  set H2 := negMulLog y + negMulLog (1 - y) with hH2
  have hH2le : H2 ≤ 1 := by
    have := negMulLog_le_one_sub hy0.le; have := negMulLog_le_one_sub hy1.le; rw [hH2]; linarith
  have hH2nn : 0 ≤ H2 := by
    have := negMulLog_nonneg hy0.le (by linarith); have := negMulLog_nonneg hy1.le (by linarith)
    rw [hH2]; linarith
  have key : (1 + u - v) * negMulLog u - (1 - u + v) * negMulLog v =
      w * (2 * Friedan.dd y + (2 * y - 1) * ((w - 1) * H2 + (1 + w) * L)) := by
    unfold negMulLog
    rw [hlu, hlv, hH2, hL, Friedan.dd, huy, hvy]
    unfold negMulLog
    ring
  have hb : 0 ≤ (w - 1) * H2 + (1 + w) * L := by nlinarith
  have hy2 : 0 ≤ 2 * y - 1 := by linarith
  have : 0 ≤ w * (2 * Friedan.dd y + (2 * y - 1) * ((w - 1) * H2 + (1 + w) * L)) := by
    have := mul_nonneg hy2 hb
    positivity
  linarith

/-- Two-point form: if `η(u) + η(v) ≤ h`, then `v (h - log v) ≤ u (h - log u)`. -/
lemma pair_h {u v h : ℝ} (hv : 0 < v) (hvu : v ≤ u) (huv : u + v ≤ 1)
    (hh : negMulLog u + negMulLog v ≤ h) :
    v * (h - log v) ≤ u * (h - log u) := by
  have hc := pair_core hv hvu huv
  have h1 : (u - v) * (negMulLog u + negMulLog v) ≤ (u - v) * h :=
    mul_le_mul_of_nonneg_left hh (by linarith)
  unfold negMulLog at hc h1
  nlinarith

/-- Vector form (over `range n`): for a probability vector `Z > 0` on `range n`, `i ≠ j` in
`range n` with `Z j ≤ Z i`, `Z j (H - log Z j) ≤ Z i (H - log Z i)`, `H = ∑ η(Z k)`. -/
lemma pair_vec {n : ℕ} {Z : ℕ → ℝ} (hZ : ∀ k < n, 0 < Z k) (hs : ∑ k ∈ range n, Z k = 1)
    {i j : ℕ} (hi : i < n) (hj : j < n) (hij : i ≠ j) (hle : Z j ≤ Z i) :
    Z j * ((∑ k ∈ range n, negMulLog (Z k)) - log (Z j)) ≤
      Z i * ((∑ k ∈ range n, negMulLog (Z k)) - log (Z i)) := by
  have hmi : i ∈ range n := mem_range.2 hi
  have hmj : j ∈ ((range n).erase i) := mem_erase.2 ⟨hij.symm, mem_range.2 hj⟩
  have hsplit : ∀ f : ℕ → ℝ, ∑ k ∈ range n, f k =
      f i + (f j + ∑ k ∈ ((range n).erase i).erase j, f k) := by
    intro f
    rw [← add_sum_erase _ _ hmi, ← add_sum_erase _ _ hmj]
  have hrest_nn : 0 ≤ ∑ k ∈ ((range n).erase i).erase j, Z k :=
    sum_nonneg fun k hk => (hZ k (mem_range.1 (mem_of_mem_erase (mem_of_mem_erase hk)))).le
  have huv : Z i + Z j ≤ 1 := by
    have := hsplit Z; linarith
  have hZle : ∀ k < n, Z k ≤ 1 := by
    intro k hk
    have := single_le_sum (fun l hl => (hZ l (mem_range.1 hl)).le) (mem_range.2 hk)
    linarith
  have hh : negMulLog (Z i) + negMulLog (Z j) ≤ ∑ k ∈ range n, negMulLog (Z k) := by
    rw [hsplit (fun k => negMulLog (Z k))]
    have : 0 ≤ ∑ k ∈ ((range n).erase i).erase j, negMulLog (Z k) :=
      sum_nonneg fun k hk => by
        have hk' := mem_range.1 (mem_of_mem_erase (mem_of_mem_erase hk))
        exact negMulLog_nonneg (hZ k hk').le (hZle k hk')
    linarith
  exact pair_h (hZ j hj) hle huv hh

end FriedanQ

end
