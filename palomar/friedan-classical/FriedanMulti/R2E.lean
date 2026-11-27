/-
Copyright 2026 Ming-Chih Kao. Licensed under the Apache License, Version 2.0;
see the LICENSE file at the root of this repository.
-/
module

public import Mathlib

/-! Port: copied from `FriedanMulti/R2E.lean` of github.com/koolkao/friedan-entropy-inequality (commit 0f4ba65dc126f59e7158fbcbc01548baa78cf21d, Lean v4.33.1, Mathlib 0df444a) and put into the module system (`module` header, `public import`, public section). No other change was needed for Lean v4.36.0 / Mathlib fc4f59e. -/

@[expose] public section

/-!
# The critical-order inequality `E ≥ 0` (order `c = 2 log 2`)

In the variable `s = -log r > 0` (so `r = e^{-s}`, `x = r^c = e^{-cs}`),
`Gs s = log(1+r) - log(1+x)/c - (r - x)/((1+x)(1-r)) = E(r)/(1-r)` and
`Gs' = -K · S` with `K > 0` and
`S s = (c-1) sinh(3s/2) + (c+3) sinh(s/2) - 3 sinh((c-1/2)s) - sinh((3/2-c)s)`.
`S'''' ≥ 0` on `[0,∞)` termwise, and `S(0) = S'(0) = S''(0) = 0`, so `S` changes sign at most once,
from `-` to `+` (`S_N`). With `Gs → 0` at `0+` (this is where `c = 2 log 2` enters) and at `∞`,
`Gs ≥ 0` (`Gs_nonneg`). (Route suggested by Fable 5.2; it replaces the Descartes-rule argument of
MULTI.md §5.2, which is not formalized.)
-/

open Real Filter Topology

namespace FriedanR2

noncomputable def cc : ℝ := 2 * Real.log 2

lemma cc_gt : (13862 / 10000 : ℝ) < cc := by
  unfold cc; have := Real.log_two_gt_d9; norm_num at this ⊢; linarith

lemma cc_lt : cc < (13863 / 10000 : ℝ) := by
  unfold cc; have := Real.log_two_lt_d9; norm_num at this ⊢; linarith

/-! ### The sinh sum and its derivatives -/

noncomputable def Sk (k : ℕ) (s : ℝ) : ℝ :=
  (cc - 1) * (3 / 2) ^ k * (if Even k then Real.sinh (3 / 2 * s) else Real.cosh (3 / 2 * s))
  + (cc + 3) * (1 / 2) ^ k * (if Even k then Real.sinh (1 / 2 * s) else Real.cosh (1 / 2 * s))
  - 3 * (cc - 1 / 2) ^ k * (if Even k then Real.sinh ((cc - 1 / 2) * s) else Real.cosh ((cc - 1 / 2) * s))
  - (3 / 2 - cc) ^ k * (if Even k then Real.sinh ((3 / 2 - cc) * s) else Real.cosh ((3 / 2 - cc) * s))

lemma hd_shch (a : ℝ) (k : ℕ) (s : ℝ) :
    HasDerivAt (fun s => if Even k then Real.sinh (a * s) else Real.cosh (a * s))
      (a * if Even (k + 1) then Real.sinh (a * s) else Real.cosh (a * s)) s := by
  have hs : HasDerivAt (fun s => Real.sinh (a * s)) (a * Real.cosh (a * s)) s :=
    ((Real.hasDerivAt_sinh (a * s)).comp s ((hasDerivAt_id' s).const_mul a)).congr_deriv (by ring)
  have hc : HasDerivAt (fun s => Real.cosh (a * s)) (a * Real.sinh (a * s)) s :=
    ((Real.hasDerivAt_cosh (a * s)).comp s ((hasDerivAt_id' s).const_mul a)).congr_deriv (by ring)
  rcases Nat.even_or_odd k with hk | hk
  · have hk1 : ¬ Even (k + 1) := by rw [Nat.even_add_one]; exact not_not.2 hk
    simp only [hk, hk1, if_true, if_false]
    exact hs
  · have hk0 : ¬ Even k := Nat.not_even_iff_odd.2 hk
    have hk1 : Even (k + 1) := hk.add_one
    simp only [hk0, hk1, if_true, if_false]
    exact hc

lemma hd_Sk (k : ℕ) (s : ℝ) : HasDerivAt (Sk k) (Sk (k + 1) s) s := by
  unfold Sk
  refine ((((hd_shch (3 / 2) k s).const_mul ((cc - 1) * (3 / 2) ^ k)).add
    ((hd_shch (1 / 2) k s).const_mul ((cc + 3) * (1 / 2) ^ k))).sub
    ((hd_shch (cc - 1 / 2) k s).const_mul (3 * (cc - 1 / 2) ^ k))).sub
    ((hd_shch (3 / 2 - cc) k s).const_mul ((3 / 2 - cc) ^ k)) |>.congr_deriv ?_
  simp only [pow_succ]
  ring

lemma Sk_zero_even {k : ℕ} (hk : Even k) : Sk k 0 = 0 := by
  simp [Sk, hk]

lemma S1_zero : Sk 1 0 = 0 := by
  simp only [Sk, Nat.not_even_one, if_false, mul_zero, Real.cosh_zero, pow_one]
  ring

lemma S4_nonneg {s : ℝ} (hs : 0 ≤ s) : 0 ≤ Sk 4 s := by
  have h4 : Even 4 := by decide
  simp only [Sk, h4, if_true]
  have c1 := cc_gt
  have c2 := cc_lt
  have a1 : Real.sinh ((cc - 1 / 2) * s) ≤ Real.sinh (3 / 2 * s) :=
    Real.sinh_le_sinh.2 (by nlinarith)
  have a2 : Real.sinh ((3 / 2 - cc) * s) ≤ Real.sinh (1 / 2 * s) :=
    Real.sinh_le_sinh.2 (by nlinarith)
  have b1 : 0 ≤ Real.sinh (3 / 2 * s) := Real.sinh_nonneg_iff.2 (by linarith)
  have b2 : 0 ≤ Real.sinh ((3 / 2 - cc) * s) := Real.sinh_nonneg_iff.2 (by nlinarith)
  have b3 : 0 ≤ Real.sinh ((cc - 1 / 2) * s) := Real.sinh_nonneg_iff.2 (by nlinarith)
  -- coefficients: (c-1)(3/2)^4 ≥ 3 (c-1/2)^4 and (c+3)/16 ≥ (3/2-c)^4
  have p1 : (cc - 1 / 2) ^ 4 ≤ (8863 / 10000 : ℝ) ^ 4 :=
    pow_le_pow_left₀ (by linarith) (by linarith) 4
  have p2 : (3 / 2 - cc) ^ 4 ≤ (115 / 1000 : ℝ) ^ 4 :=
    pow_le_pow_left₀ (by linarith) (by linarith) 4
  have q1 : 3 * (cc - 1 / 2) ^ 4 ≤ (cc - 1) * (3 / 2) ^ 4 := by nlinarith
  have q2 : (3 / 2 - cc) ^ 4 ≤ (cc + 3) * (1 / 2) ^ 4 := by nlinarith
  have r1 := mul_le_mul q1 a1 b3 (by nlinarith)
  have r2 := mul_le_mul q2 a2 b2 (by nlinarith)
  nlinarith

/-! ### "Once nonnegative, stays nonnegative" -/

def NP (φ : ℝ → ℝ) : Prop := ∀ x y, 0 < x → x ≤ y → 0 ≤ φ x → 0 ≤ φ y

lemma NP_of_deriv {φ φ' : ℝ → ℝ} (hd : ∀ x, HasDerivAt φ (φ' x) x) (h0 : φ 0 = 0) (hN : NP φ') :
    NP φ := by
  intro x y hx hxy hφx
  by_contra hy
  push Not at hy
  have hxy' : x < y := lt_of_le_of_ne hxy (by rintro rfl; linarith)
  obtain ⟨ξ, hξ, hξd⟩ := exists_hasDerivAt_eq_slope φ φ' hxy'
    (fun t _ => (hd t).continuousAt.continuousWithinAt) (fun t _ => hd t)
  have hneg : φ' ξ < 0 := by
    rw [hξd]; exact div_neg_of_neg_of_pos (by linarith) (by linarith)
  have hall : ∀ t, 0 < t → t ≤ ξ → φ' t < 0 := by
    intro t ht htξ
    by_contra h
    push Not at h
    have := hN t ξ ht htξ h
    linarith
  have hanti : StrictAntiOn φ (Set.Icc 0 ξ) := by
    refine strictAntiOn_of_hasDerivWithinAt_neg (convex_Icc 0 ξ) (f' := φ')
      (fun t _ => (hd t).continuousAt.continuousWithinAt) (fun t _ => (hd t).hasDerivWithinAt) ?_
    intro t ht
    rw [interior_Icc] at ht
    exact hall t ht.1 ht.2.le
  have := hanti ⟨le_rfl, by linarith [hξ.1]⟩ ⟨hx.le, by linarith [hξ.1]⟩ hx
  linarith

lemma S_N : NP (Sk 0) := by
  have h3 : NP (Sk 3) := by
    have hm : MonotoneOn (Sk 3) (Set.Ici 0) := by
      refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0) (f' := Sk 4)
        (fun t _ => (hd_Sk 3 t).continuousAt.continuousWithinAt)
        (fun t _ => (hd_Sk 3 t).hasDerivWithinAt) ?_
      intro t ht
      rw [interior_Ici] at ht
      exact S4_nonneg (le_of_lt ht)
    intro x y hx hxy h
    exact h.trans (hm (Set.mem_Ici.2 hx.le) (Set.mem_Ici.2 (hx.le.trans hxy)) hxy)
  have h2 : NP (Sk 2) := NP_of_deriv (hd_Sk 2) (Sk_zero_even (by decide)) h3
  have h1 : NP (Sk 1) := NP_of_deriv (hd_Sk 1) S1_zero h2
  exact NP_of_deriv (hd_Sk 0) (Sk_zero_even (by decide)) h1

end FriedanR2

end
