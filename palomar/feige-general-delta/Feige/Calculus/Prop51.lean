module

public import Feige.Calculus.NoInteriorMin

/- Port (Palomar entry): `module` header, `public import`s and a public section added for the module system; otherwise unchanged from github.com/koolkao/feige-lean at commit 7da24abf1619706bf4f705bb24aa4d00bc63b49f. -/

@[expose] public section

/-!
# M-Calc-B: Prop. 5.1 of the manuscript (Ling's Claim 3.4)

For `b > 0`, weights `αⱼ ≥ b` (`j ∈ t`), and `d + K > αⱼ`, `d + K > b`, the function
`G L = ∑ⱼ log (1 - αⱼ/(d+L)) + ((L - K)/b) log (1 - b/(d+L))`
has no interior minimum on `[K, K + b]`.

Written with `R = d + L`, `uⱼ = 1/(R-αⱼ) - 1/R`, `v = 1/(R-b) - 1/R`, `ℓ = log (R-b) - log R`:
`G' = ∑ uⱼ + ℓ/b + ((L-K)/b) v` and `G'' = -∑ uⱼ kⱼ + 2v/b - ((L-K)/b) v k_b` with
`kⱼ = 1/(R-αⱼ) + 1/R ≥ k_b`.  At a stationary point `G'' ≤ (k_b ℓ + 2v)/b`, which is negative
because `log (1-x) < -2x/(2-x)` for `x = b/R ∈ (0,1)`.
-/

open Set Real Finset

namespace Samuels

/-- `log (1 - x) < -2x/(2-x)` for `0 < x < 1`. -/
lemma log_one_sub_lt {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) : log (1 - x) < -(2 * x / (2 - x)) := by
  -- `ψ t = log (1-t) + 2t/(2-t)` has `ψ 0 = 0` and `ψ' t = -t²/((1-t)(2-t)²) < 0`.
  let ψ : ℝ → ℝ := fun t => log (1 - t) + 2 * t / (2 - t)
  have hd : ∀ t ∈ Ioo 0 x, HasDerivAt ψ (-(t ^ 2 / ((1 - t) * (2 - t) ^ 2))) t := by
    intro t ht
    have h1 : 1 - t ≠ 0 := by linarith [ht.2]
    have h2 : 2 - t ≠ 0 := by linarith [ht.2]
    have hA : HasDerivAt (fun t => log (1 - t)) (-1 / (1 - t)) t := by
      have := ((hasDerivAt_id' t).const_sub 1).log h1
      simpa using this
    have hB : HasDerivAt (fun t => 2 * t / (2 - t)) (4 / (2 - t) ^ 2) t := by
      have := ((hasDerivAt_id' t).const_mul 2).div ((hasDerivAt_id' t).const_sub 2) h2
      exact this.congr_deriv (by ring)
    refine (hA.add hB).congr_deriv ?_
    field_simp
    ring
  have hlt := lt_of_hasDerivAt_neg hx0
    (fun t ht => (show ContinuousAt ψ t by
      have h1 : 1 - t ≠ 0 := by linarith [ht.2]
      have h2 : 2 - t ≠ 0 := by linarith [ht.2]
      exact ((continuousAt_const.sub continuousAt_id).log h1).add
        ((continuousAt_const.mul continuousAt_id).div (continuousAt_const.sub continuousAt_id) h2)
      ).continuousWithinAt) hd
    (fun t ht => by
      have h1 : 0 < 1 - t := by linarith [ht.2]
      have h2 : 0 < (2 - t) ^ 2 := pow_pos (by linarith [ht.2]) 2
      have : 0 < t ^ 2 / ((1 - t) * (2 - t) ^ 2) := by have := ht.1; positivity
      linarith)
  simp only [ψ, sub_zero, log_one, mul_zero, zero_div, add_zero] at hlt
  linarith

variable {κ : Type*}

/-- The function `G` of Prop. 5.1, with logarithms of differences. -/
noncomputable def G51 (t : Finset κ) (α : κ → ℝ) (b d K L : ℝ) : ℝ :=
  ∑ j ∈ t, (log (d + L - α j) - log (d + L)) + (L - K) / b * (log (d + L - b) - log (d + L))

noncomputable def G51' (t : Finset κ) (α : κ → ℝ) (b d K L : ℝ) : ℝ :=
  ∑ j ∈ t, (1 / (d + L - α j) - 1 / (d + L)) + 1 / b * (log (d + L - b) - log (d + L)) +
    (L - K) / b * (1 / (d + L - b) - 1 / (d + L))

noncomputable def G51'' (t : Finset κ) (α : κ → ℝ) (b d K L : ℝ) : ℝ :=
  ∑ j ∈ t, (-(1 / (d + L - α j) ^ 2) + 1 / (d + L) ^ 2) +
    2 / b * (1 / (d + L - b) - 1 / (d + L)) +
    (L - K) / b * (-(1 / (d + L - b) ^ 2) + 1 / (d + L) ^ 2)

lemma hasDerivAt_log_sub {c L : ℝ} (h : 0 < L - c) :
    HasDerivAt (fun y => log (y - c)) (1 / (L - c)) L := by
  have := ((hasDerivAt_id' L).sub_const c).log h.ne'
  simpa using this

lemma hasDerivAt_inv_sub {c L : ℝ} (h : 0 < L - c) :
    HasDerivAt (fun y => 1 / (y - c)) (-(1 / (L - c) ^ 2)) L := by
  have := ((hasDerivAt_id' L).sub_const c).inv h.ne'
  have e : (fun y => 1 / (y - c)) = (fun x => x - c)⁻¹ := by funext y; simp
  rw [e]
  exact this.congr_deriv (by field_simp)

lemma hasDerivAt_G51 (t : Finset κ) (α : κ → ℝ) {b d K L : ℝ} (hb : 0 < b)
    (hα : ∀ j ∈ t, α j < d + L) (hbL : b < d + L) :
    HasDerivAt (G51 t α b d K) (G51' t α b d K L) L := by
  have hR : 0 < d + L := by linarith
  have e : ∀ c : ℝ, (fun y => log (d + y - c)) = fun y => log (y - (c - d)) := fun c => by
    funext y; ring_nf
  have hlc : ∀ c, c < d + L → HasDerivAt (fun y => log (d + y - c)) (1 / (d + L - c)) L := by
    intro c hc
    rw [e c]
    have := hasDerivAt_log_sub (c := c - d) (L := L) (by linarith)
    convert this using 2; ring
  have h0 : HasDerivAt (fun y => log (d + y)) (1 / (d + L)) L := by
    have := hlc 0 hR
    simpa using this
  have hsum : HasDerivAt (fun y => ∑ j ∈ t, (log (d + y - α j) - log (d + y)))
      (∑ j ∈ t, (1 / (d + L - α j) - 1 / (d + L))) L :=
    HasDerivAt.fun_sum (fun j hj => (hlc (α j) (hα j hj)).sub h0)
  have hlin : HasDerivAt (fun y => (y - K) / b) (1 / b) L := by
    have := ((hasDerivAt_id' L).sub_const K).div_const b
    simpa using this
  have := hsum.add (hlin.mul ((hlc b hbL).sub h0))
  exact this.congr_deriv (by simp only [Pi.sub_apply]; unfold G51'; ring)

lemma hasDerivAt_G51' (t : Finset κ) (α : κ → ℝ) {b d K L : ℝ} (hb : 0 < b)
    (hα : ∀ j ∈ t, α j < d + L) (hbL : b < d + L) :
    HasDerivAt (G51' t α b d K) (G51'' t α b d K L) L := by
  have hR : 0 < d + L := by linarith
  have hic : ∀ c, c < d + L → HasDerivAt (fun y => 1 / (d + y - c)) (-(1 / (d + L - c) ^ 2)) L := by
    intro c hc
    have e : (fun y => 1 / (d + y - c)) = fun y => 1 / (y - (c - d)) := by funext y; ring_nf
    rw [e]
    have := hasDerivAt_inv_sub (c := c - d) (L := L) (by linarith)
    convert this using 2; ring
  have hlc : ∀ c, c < d + L → HasDerivAt (fun y => log (d + y - c)) (1 / (d + L - c)) L := by
    intro c hc
    have e : (fun y => log (d + y - c)) = fun y => log (y - (c - d)) := by funext y; ring_nf
    rw [e]
    have := hasDerivAt_log_sub (c := c - d) (L := L) (by linarith)
    convert this using 2; ring
  have h0 : HasDerivAt (fun y => 1 / (d + y)) (-(1 / (d + L) ^ 2)) L := by
    have := hic 0 hR; simpa using this
  have hl0 : HasDerivAt (fun y => log (d + y)) (1 / (d + L)) L := by
    have := hlc 0 hR; simpa using this
  have hsum : HasDerivAt (fun y => ∑ j ∈ t, (1 / (d + y - α j) - 1 / (d + y)))
      (∑ j ∈ t, (-(1 / (d + L - α j) ^ 2) + 1 / (d + L) ^ 2)) L := by
    have := HasDerivAt.fun_sum (u := t) (fun j hj => (hic (α j) (hα j hj)).sub h0)
    convert this using 2 with j
    ring
  have hlin : HasDerivAt (fun y => (y - K) / b) (1 / b) L := by
    have := ((hasDerivAt_id' L).sub_const K).div_const b
    simpa using this
  have h2 := ((hlc b hbL).sub hl0).const_mul (1 / b)
  have h3 := hlin.mul ((hic b hbL).sub h0)
  have := (hsum.add h2).add h3
  exact this.congr_deriv (by simp only [Pi.sub_apply]; unfold G51''; ring)

/-- **Prop. 5.1** (Claim 3.4): every stationary point of `G` is a strict local maximum, so the
minimum over `[K, K + b]` is at an endpoint. -/
theorem prop51 (t : Finset κ) (α : κ → ℝ) {b d K : ℝ} (hb : 0 < b)
    (hαb : ∀ j ∈ t, b ≤ α j) (hα : ∀ j ∈ t, α j < d + K) (hbK : b < d + K) :
    ∀ L ∈ Icc K (K + b), min (G51 t α b d K K) (G51 t α b d K (K + b)) ≤ G51 t α b d K L := by
  -- Port: `g`, `a`, `b` given explicitly (unification no longer finds `g` under the module system).
  apply min_endpoints_le_of_stationary (g := G51 t α b d K) (a := K) (b := K + b)
    (g' := G51' t α b d K) (g'' := G51'' t α b d K)
  · intro L hL
    exact (hasDerivAt_G51 t α hb (fun j hj => by linarith [hα j hj, hL.1])
      (by linarith [hL.1])).continuousAt.continuousWithinAt
  · intro L hL
    exact hasDerivAt_G51 t α hb (fun j hj => by linarith [hα j hj, hL.1]) (by linarith [hL.1])
  · intro L hL
    exact hasDerivAt_G51' t α hb (fun j hj => by linarith [hα j hj, hL.1]) (by linarith [hL.1])
  · intro L hL hst
    set R := d + L with hRdef
    have hRb : 0 < R - b := by linarith [hL.1]
    have hR : 0 < R := by linarith
    have hRα : ∀ j ∈ t, 0 < R - α j := fun j hj => by linarith [hα j hj, hL.1]
    have hLK : 0 ≤ L - K := by linarith [hL.1]
    set u : κ → ℝ := fun j => 1 / (R - α j) - 1 / R
    set v := 1 / (R - b) - 1 / R
    set kb := 1 / (R - b) + 1 / R
    set ℓ := log (R - b) - log R
    have hu : ∀ j ∈ t, 0 ≤ u j := fun j hj => by
      simp only [u]
      rw [sub_nonneg]
      exact one_div_le_one_div_of_le (hRα j hj) (by linarith [hαb j hj, hb])
    have hk : ∀ j ∈ t, kb ≤ 1 / (R - α j) + 1 / R := fun j hj => by
      simp only [kb]
      have := one_div_le_one_div_of_le (hRα j hj) (show R - α j ≤ R - b by linarith [hαb j hj])
      linarith
    have hv : 0 < v := by
      simp only [v]
      rw [sub_pos]
      exact one_div_lt_one_div_of_lt hRb (by linarith)
    -- rewrite `G''` through `u`, `v`, `k`
    have hG'' : G51'' t α b d K L = -∑ j ∈ t, u j * (1 / (R - α j) + 1 / R) +
        2 / b * v - (L - K) / b * v * kb := by
      unfold G51''
      rw [← hRdef]
      have : ∀ j ∈ t, (-(1 / (R - α j) ^ 2) + 1 / R ^ 2) = -(u j * (1 / (R - α j) + 1 / R)) :=
        fun j hj => by
          have h1 := (hRα j hj).ne'
          simp only [u]; field_simp; ring
      rw [Finset.sum_congr rfl this, Finset.sum_neg_distrib]
      simp only [v, kb, ← one_div_pow]
      ring
    have hG' : G51' t α b d K L = ∑ j ∈ t, u j + 1 / b * ℓ + (L - K) / b * v := by
      unfold G51'; rfl
    rw [hG'] at hst
    have hbound : kb * ∑ j ∈ t, u j ≤ ∑ j ∈ t, u j * (1 / (R - α j) + 1 / R) := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro j hj
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_left (hk j hj) (hu j hj)
    -- at the stationary point, `∑ u = -ℓ/b - ((L-K)/b) v`
    have hsumu : ∑ j ∈ t, u j = -(1 / b * ℓ) - (L - K) / b * v := by linarith
    have hneg : kb * ℓ + 2 * v < 0 := by
      have hx0 : 0 < b / R := div_pos hb hR
      have hx1 : b / R < 1 := (div_lt_one hR).mpr (by linarith)
      have hlog := log_one_sub_lt hx0 hx1
      have hℓ : ℓ = log (1 - b / R) := by
        simp only [ℓ]
        rw [← log_div hRb.ne' hR.ne']
        congr 1; field_simp
      have hkb : kb = (2 * R - b) / (R * (R - b)) := by simp only [kb]; field_simp; ring
      have hvv : v = b / (R * (R - b)) := by simp only [v]; field_simp; ring
      rw [hℓ, hkb, hvv]
      have hden : 0 < R * (R - b) := mul_pos hR hRb
      have h2R : 0 < 2 * R - b := by linarith
      have hfrac : 2 * (b / R) / (2 - b / R) = 2 * b / (2 * R - b) := by field_simp
      rw [hfrac] at hlog
      have : (2 * R - b) * log (1 - b / R) < -(2 * b) := by
        have := mul_lt_mul_of_pos_left hlog h2R
        rw [mul_neg, mul_div_cancel₀ _ h2R.ne'] at this
        exact this
      rw [div_mul_eq_mul_div, mul_div_assoc', ← add_div]
      apply div_neg_of_neg_of_pos _ hden
      linarith
    rw [hG'']
    have : -∑ j ∈ t, u j * (1 / (R - α j) + 1 / R) + 2 / b * v - (L - K) / b * v * kb ≤
        (kb * ℓ + 2 * v) / b := by
      have h1 : -∑ j ∈ t, u j * (1 / (R - α j) + 1 / R) ≤ -(kb * ∑ j ∈ t, u j) := by linarith
      rw [hsumu] at h1
      have : (kb * ℓ + 2 * v) / b = -(kb * (-(1 / b * ℓ) - (L - K) / b * v)) + 2 / b * v -
          (L - K) / b * v * kb := by field_simp; ring
      rw [this]; linarith
    have : (kb * ℓ + 2 * v) / b < 0 := div_neg_of_neg_of_pos hneg hb
    linarith

end Samuels

end
