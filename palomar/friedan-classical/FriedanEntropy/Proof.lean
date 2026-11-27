/-
Copyright 2026 Ming-Chih Kao. Licensed under the Apache License, Version 2.0;
see the LICENSE file at the root of this repository.
-/
module

public import FriedanEntropy.Statement
public import Mathlib

/-! Port: copied from `FriedanEntropy/Proof.lean` of github.com/koolkao/friedan-entropy-inequality (commit 0f4ba65dc126f59e7158fbcbc01548baa78cf21d, Lean v4.33.1, Mathlib 0df444a) and put into the module system (`module` header, `public import`, public section). The proof body is unchanged; it builds on Lean v4.36.0 / Mathlib fc4f59e as is (the source repository's `quantum-lean/FriedanQ/Classical.lean` is the same body). -/

@[expose] public section

/-!
# Friedan's generalized entropy inequality (MathOverflow 138395): proof

Proof of `OMA.S_mo_138395.main` (Left to Solve statement mo-138395): for probability vectors
`X, Y` on `Fin n`, `0 ≤ α ≤ 1` and `K = ∑ X^α Y^(1-α) > 0`,
`K² H(X^α Y^(1-α) / K) ≤ α H(X) + (1-α) H(Y)`.

Copyright (c) 2026 Ming-Chih Kao (https://github.com/koolkao), Apache 2.0. Original proof; no
external library beyond Mathlib.

Outline (all for `0 < α < 1`; `α ∈ {0, 1}` is immediate since `0^0 = 1`):
* `Phi = α H(X) + (1-α) H(Y) - K ∑ η(z) - K² log K` equals the deficit (`ent_div`).
* Part 0 (`phi_nonneg`): perturb to strictly positive vectors and pass to the limit.
* Induction on the support size (`good_nonneg`), moving along the family `X·(1+su), Y·(1+su)`
  with `u` in the kernel of the constraint matrix (`kernel_exists`, `descent`):
  - Part I (`partI`, support ≥ 4): with `∑ z u = 0` too, `K` is constant and `Phi` is concave
    in `s` (`partI_concave`, concavity of `η`);
  - Part II (`partII`, support 3): `Phi` is concave in `s` because its second derivative is
    `-Q ≤ 0` (`psi2_nonpos`, `Q3`), using that the varentropy on three points is at most 1
    (`two_pt`, `cosh_ge`);
  - Part III (`two_point`, support 2): one-variable calculus in logit coordinates
    (`n2_logit`, `path_ineq`, `Δ_nonneg`, `Om_mono`, `dd_nonneg`).
-/


open Real

namespace Friedan

/-! ## Part III: the two-point case, in logit coordinates -/

noncomputable def lp (t : ℝ) : ℝ := Real.log (Real.exp (t / 2) + Real.exp (-t / 2))
noncomputable def sg (t : ℝ) : ℝ := Real.exp (t / 2) / (Real.exp (t / 2) + Real.exp (-t / 2))
noncomputable def hh (t : ℝ) : ℝ := lp t - t * (sg t - 1 / 2)

lemma den_pos (t : ℝ) : 0 < Real.exp (t / 2) + Real.exp (-t / 2) := by positivity

lemma lp_neg (t : ℝ) : lp (-t) = lp t := by
  unfold lp; rw [neg_neg, add_comm]

lemma sg_pos (t : ℝ) : 0 < sg t := div_pos (Real.exp_pos _) (den_pos t)

lemma one_sub_sg (t : ℝ) :
    1 - sg t = Real.exp (-t / 2) / (Real.exp (t / 2) + Real.exp (-t / 2)) := by
  unfold sg
  rw [eq_div_iff (den_pos t).ne', sub_mul, div_mul_cancel₀ _ (den_pos t).ne']
  ring

lemma sg_lt_one (t : ℝ) : sg t < 1 := by
  have : 0 < 1 - sg t := by rw [one_sub_sg]; exact div_pos (Real.exp_pos _) (den_pos t)
  linarith

lemma sg_neg (t : ℝ) : sg (-t) = 1 - sg t := by
  rw [one_sub_sg]; unfold sg; rw [neg_neg, add_comm (Real.exp (-t / 2))]

lemma log_sg (t : ℝ) : Real.log (sg t) = t / 2 - lp t := by
  unfold sg lp; rw [Real.log_div (Real.exp_pos _).ne' (den_pos t).ne', Real.log_exp]

lemma log_one_sub_sg (t : ℝ) : Real.log (1 - sg t) = -t / 2 - lp t := by
  rw [one_sub_sg]; unfold lp; rw [Real.log_div (Real.exp_pos _).ne' (den_pos t).ne', Real.log_exp]

lemma sg_exp (t : ℝ) : sg t = Real.exp (t / 2 - lp t) := by
  rw [← log_sg, Real.exp_log (sg_pos t)]

lemma one_sub_sg_exp (t : ℝ) : 1 - sg t = Real.exp (-t / 2 - lp t) := by
  rw [← log_one_sub_sg, Real.exp_log (by linarith [sg_lt_one t])]

lemma hasDerivAt_ehalf (t : ℝ) :
    HasDerivAt (fun t => Real.exp (t / 2)) (Real.exp (t / 2) * (1 / 2)) t :=
  ((hasDerivAt_id' t).div_const 2).exp

lemma hasDerivAt_den (t : ℝ) :
    HasDerivAt (fun t => Real.exp (t / 2) + Real.exp (-t / 2))
      (Real.exp (t / 2) / 2 - Real.exp (-t / 2) / 2) t := by
  have h2 : HasDerivAt (fun t => Real.exp (-t / 2)) (Real.exp (-t / 2) * (-1 / 2)) t :=
    ((hasDerivAt_id' t).neg.div_const 2).exp
  exact ((hasDerivAt_ehalf t).add h2).congr_deriv (by ring)

lemma hasDerivAt_lp (t : ℝ) : HasDerivAt lp (sg t - 1 / 2) t := by
  have h := (hasDerivAt_den t).log (den_pos t).ne'
  refine h.congr_deriv ?_
  have hd := (den_pos t).ne'
  unfold sg
  field_simp
  ring

lemma hasDerivAt_sg (t : ℝ) : HasDerivAt sg (sg t * (1 - sg t)) t := by
  have h := (hasDerivAt_ehalf t).div (hasDerivAt_den t) (den_pos t).ne'
  refine h.congr_deriv ?_
  have hd := (den_pos t).ne'
  rw [one_sub_sg]
  unfold sg
  field_simp
  ring

lemma hasDerivAt_hh (t : ℝ) : HasDerivAt hh (-t * (sg t * (1 - sg t))) t :=
  ((hasDerivAt_lp t).sub ((hasDerivAt_id' t).mul ((hasDerivAt_sg t).sub_const (1 / 2)))).congr_deriv
    (by ring)

lemma sg_zero : sg 0 = 1 / 2 := by
  unfold sg; norm_num

lemma sg_mono : Monotone sg := by
  have := monotoneOn_of_hasDerivWithinAt_nonneg (D := Set.univ) convex_univ (f := sg)
    (f' := fun t => sg t * (1 - sg t))
    (fun t _ => (hasDerivAt_sg t).continuousAt.continuousWithinAt)
    (fun t _ => (hasDerivAt_sg t).hasDerivWithinAt)
    (fun t _ => mul_nonneg (sg_pos t).le (sub_nonneg.2 (sg_lt_one t).le))
  exact monotoneOn_univ.1 this

lemma sg_ge_half {t : ℝ} (ht : 0 ≤ t) : 1 / 2 ≤ sg t := sg_zero ▸ sg_mono ht

lemma hh_neg (t : ℝ) : hh (-t) = hh t := by
  unfold hh; rw [lp_neg, sg_neg]; ring

lemma lp_abs (t : ℝ) : lp |t| = lp t := by
  rcases abs_choice t with h | h <;> rw [h]
  exact lp_neg t

lemma hh_abs (t : ℝ) : hh |t| = hh t := by
  rcases abs_choice t with h | h <;> rw [h]
  exact hh_neg t

lemma hh_anti : AntitoneOn hh (Set.Ici 0) := by
  refine antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici 0) (f' := fun t => -t * (sg t * (1 - sg t)))
    (fun t _ => (hasDerivAt_hh t).continuousAt.continuousWithinAt)
    (fun t _ => (hasDerivAt_hh t).hasDerivWithinAt) ?_
  intro t ht
  rw [interior_Ici] at ht
  have : 0 ≤ sg t * (1 - sg t) := mul_nonneg (sg_pos t).le (sub_nonneg.2 (sg_lt_one t).le)
  have ht' : 0 < t := ht
  nlinarith

lemma hh_ent (t : ℝ) : hh t = Real.negMulLog (sg t) + Real.negMulLog (1 - sg t) := by
  simp only [Real.negMulLog]
  rw [log_sg, log_one_sub_sg]
  unfold hh
  ring

/-! Lemma 5 in probability form. -/

noncomputable def dd (p : ℝ) : ℝ := p * Real.negMulLog p - (1 - p) * Real.negMulLog (1 - p)

noncomputable def dd1 (p : ℝ) : ℝ := -2 * (p * Real.log p) - 2 * ((1 - p) * Real.log (1 - p)) - 1

lemma hasDerivAt_dd {p : ℝ} (hp : p ≠ 0) (hq : 1 - p ≠ 0) : HasDerivAt dd (dd1 p) p := by
  have h1 := (hasDerivAt_id' p).mul (Real.hasDerivAt_negMulLog hp)
  have h2 : HasDerivAt (fun x : ℝ => 1 - x) (-1) p := by
    simpa using (hasDerivAt_id' p).const_sub 1
  have h3 := h2.mul ((Real.hasDerivAt_negMulLog hq).comp p h2)
  refine (h1.sub h3).congr_deriv ?_
  unfold dd1
  simp only [Function.comp_apply, Real.negMulLog]
  ring

lemma hasDerivAt_dd1 {p : ℝ} (hp : p ≠ 0) (hq : 1 - p ≠ 0) :
    HasDerivAt dd1 (2 * (Real.log (1 - p) - Real.log p)) p := by
  have h2 : HasDerivAt (fun x : ℝ => 1 - x) (-1) p := by
    simpa using (hasDerivAt_id' p).const_sub 1
  have g1 := Real.hasDerivAt_mul_log hp
  have g2 := (Real.hasDerivAt_mul_log hq).comp p h2
  exact (((g1.const_mul (-2)).sub (g2.const_mul 2)).sub_const 1).congr_deriv (by ring)

lemma dd_concave : ConcaveOn ℝ (Set.Icc (1 / 2) 1) dd := by
  have hc : Continuous dd := by unfold dd; fun_prop
  refine concaveOn_of_hasDerivWithinAt2_nonpos (convex_Icc _ _) hc.continuousOn
    (f' := dd1) (f'' := fun p => 2 * (Real.log (1 - p) - Real.log p)) ?_ ?_ ?_
  · intro x hx
    rw [interior_Icc] at hx
    exact (hasDerivAt_dd (by linarith [hx.1]) (by linarith [hx.2])).hasDerivWithinAt
  · intro x hx
    rw [interior_Icc] at hx
    exact (hasDerivAt_dd1 (by linarith [hx.1]) (by linarith [hx.2])).hasDerivWithinAt
  · intro x hx
    rw [interior_Icc] at hx
    have : Real.log (1 - x) ≤ Real.log x := Real.log_le_log (by linarith [hx.2]) (by linarith [hx.1])
    linarith

lemma dd_nonneg {p : ℝ} (h1 : 1 / 2 ≤ p) (h2 : p ≤ 1) : 0 ≤ dd p := by
  have := dd_concave.2 (show (1 / 2 : ℝ) ∈ Set.Icc (1 / 2) 1 from ⟨le_rfl, by norm_num⟩)
    (show (1 : ℝ) ∈ Set.Icc (1 / 2) 1 from ⟨by norm_num, le_rfl⟩)
    (show (0 : ℝ) ≤ 2 * (1 - p) by linarith) (show (0 : ℝ) ≤ 2 * p - 1 by linarith)
    (show 2 * (1 - p) + (2 * p - 1) = 1 by ring)
  simp only [smul_eq_mul] at this
  rw [show 2 * (1 - p) * (1 / 2 : ℝ) + (2 * p - 1) * 1 = p by ring] at this
  have e1 : dd (1 / 2) = 0 := by unfold dd; norm_num
  have e2 : dd 1 = 0 := by unfold dd; simp
  rw [e1, e2] at this
  linarith

noncomputable def Δ0 (t : ℝ) : ℝ := 2 * (sg t - 1 / 2) * hh t - t * (sg t * (1 - sg t))

lemma Δ0_eq (t : ℝ) : Δ0 t = dd (sg t) := by
  unfold dd
  simp only [Real.negMulLog]
  rw [log_sg, log_one_sub_sg]
  unfold Δ0 hh
  ring

lemma Δ0_nonneg {t : ℝ} (ht : 0 ≤ t) : 0 ≤ Δ0 t := by
  rw [Δ0_eq]; exact dd_nonneg (sg_ge_half ht) (sg_lt_one t).le

noncomputable def Om (t : ℝ) : ℝ := Real.exp (2 * lp t) * hh t

lemma hasDerivAt_Om (t : ℝ) : HasDerivAt Om (Real.exp (2 * lp t) * Δ0 t) t := by
  have e1 : HasDerivAt (fun t => Real.exp (2 * lp t)) (Real.exp (2 * lp t) * (2 * (sg t - 1 / 2))) t :=
    ((hasDerivAt_lp t).const_mul 2).exp
  exact (e1.mul (hasDerivAt_hh t)).congr_deriv (by unfold Δ0; ring)

lemma Om_mono : MonotoneOn Om (Set.Ici 0) := by
  refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0) (f' := fun t => Real.exp (2 * lp t) * Δ0 t)
    (fun t _ => (hasDerivAt_Om t).continuousAt.continuousWithinAt)
    (fun t _ => (hasDerivAt_Om t).hasDerivWithinAt) ?_
  intro t ht
  rw [interior_Ici] at ht
  exact mul_nonneg (Real.exp_pos _).le (Δ0_nonneg (le_of_lt ht))

lemma Om_abs (t : ℝ) : Om |t| = Om t := by
  unfold Om; rw [lp_abs, hh_abs]

/-! Lemma 6. -/

noncomputable def Δ (A b : ℝ) : ℝ :=
  -A * (sg A * (1 - sg A)) + b * (sg b * (1 - sg b)) + 2 * hh A * (sg A - sg b)

lemma hasDerivAt_Δ (A b : ℝ) :
    HasDerivAt (fun b => Δ A b) (sg b * (1 - sg b) * (1 - b * (2 * sg b - 1) - 2 * hh A)) b := by
  have h := ((hasDerivAt_const b (-A * (sg A * (1 - sg A)))).add
    ((hasDerivAt_id' b).mul ((hasDerivAt_sg b).mul ((hasDerivAt_sg b).const_sub 1)))).add
    (((hasDerivAt_sg b).const_sub (sg A)).const_mul (2 * hh A))
  exact h.congr_deriv (by simp only [Pi.mul_apply]; ring)

lemma Δ_nonneg {A B : ℝ} (hB : 0 ≤ B) (hAB : B ≤ A) : 0 ≤ Δ A B := by
  have hcont : ∀ s : Set ℝ, ContinuousOn (fun b => Δ A b) s :=
    fun s b _ => (hasDerivAt_Δ A b).continuousAt.continuousWithinAt
  have phi_anti : ∀ b b' : ℝ, 0 ≤ b → b ≤ b' →
      b * (2 * sg b - 1) ≤ b' * (2 * sg b' - 1) := by
    intro b b' hb hbb'
    have h1 := sg_mono hbb'
    have h2 := sg_ge_half hb
    exact mul_le_mul hbb' (by linarith) (by linarith) (by linarith)
  have q_nonneg : ∀ b, 0 ≤ sg b * (1 - sg b) :=
    fun b => mul_nonneg (sg_pos b).le (sub_nonneg.2 (sg_lt_one b).le)
  by_cases hφ : 0 ≤ 1 - B * (2 * sg B - 1) - 2 * hh A
  · have hm : MonotoneOn (fun b => Δ A b) (Set.Icc 0 B) := by
      refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 B) (hcont _)
        (fun b _ => (hasDerivAt_Δ A b).hasDerivWithinAt) ?_
      intro b hb
      rw [interior_Icc] at hb
      have := phi_anti b B hb.1.le hb.2.le
      exact mul_nonneg (q_nonneg b) (by linarith)
    have h0 := hm ⟨le_rfl, hB⟩ ⟨hB, le_rfl⟩ hB
    have e : Δ A 0 = Δ0 A := by unfold Δ Δ0; rw [sg_zero]; ring
    simp only at h0
    rw [e] at h0
    linarith [Δ0_nonneg (hB.trans hAB)]
  · have ha : AntitoneOn (fun b => Δ A b) (Set.Icc B A) := by
      refine antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc B A) (hcont _)
        (fun b _ => (hasDerivAt_Δ A b).hasDerivWithinAt) ?_
      intro b hb
      rw [interior_Icc] at hb
      have := phi_anti B b hB hb.1.le
      exact mul_nonpos_of_nonneg_of_nonpos (q_nonneg b) (by linarith)
    have h0 := ha ⟨le_rfl, hAB⟩ ⟨hAB, le_rfl⟩ hAB
    have e : Δ A A = 0 := by unfold Δ; ring
    simp only at h0
    rw [e] at h0
    exact h0

/-! Step 2: the monotone path. -/

lemma path_ineq {a A B w δ : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (hB : 0 ≤ B) (hAB : B ≤ A)
    (hw : w = a * A + (1 - a) * B) (hδ : δ = A - B) :
    Real.exp (2 * (lp w - a * lp A - (1 - a) * lp B)) * hh w ≤ a * hh A + (1 - a) * hh B := by
  have hδ0 : 0 ≤ δ := by rw [hδ]; linarith
  -- the path
  let Au : ℝ → ℝ := fun u => w + (1 - a) * u * δ
  let Bu : ℝ → ℝ := fun u => w - a * u * δ
  let L : ℝ → ℝ := fun u => a * hh (Au u) + (1 - a) * hh (Bu u)
  let Ex : ℝ → ℝ := fun u => -2 * (lp w - a * lp (Au u) - (1 - a) * lp (Bu u))
  let Q : ℝ → ℝ := fun u => L u * Real.exp (Ex u)
  let Q' : ℝ → ℝ := fun u => Real.exp (Ex u) * (a * (1 - a) * δ) *
    (-(Au u) * (sg (Au u) * (1 - sg (Au u))) + Bu u * (sg (Bu u) * (1 - sg (Bu u)))
      + 2 * L u * (sg (Au u) - sg (Bu u)))
  have dA : ∀ u, HasDerivAt Au ((1 - a) * δ) u := fun u =>
    ((((hasDerivAt_id' u).const_mul (1 - a)).mul_const δ).const_add w).congr_deriv (by ring)
  have dB : ∀ u, HasDerivAt Bu (-(a * δ)) u := fun u =>
    ((((hasDerivAt_id' u).const_mul a).mul_const δ).const_sub w).congr_deriv (by ring)
  have dQ : ∀ u, HasDerivAt Q (Q' u) u := by
    intro u
    have hA := (hasDerivAt_hh (Au u)).comp u (dA u)
    have hB' := (hasDerivAt_hh (Bu u)).comp u (dB u)
    have lA := (hasDerivAt_lp (Au u)).comp u (dA u)
    have lB := (hasDerivAt_lp (Bu u)).comp u (dB u)
    have hL := (hA.const_mul a).add (hB'.const_mul (1 - a))
    have hE := ((((hasDerivAt_const u (lp w)).sub (lA.const_mul a)).sub
      (lB.const_mul (1 - a))).const_mul (-2)).exp
    exact (hL.mul hE).congr_deriv (by
      simp only [Q', L, Ex, Function.comp_apply, Pi.add_apply, Pi.sub_apply]; ring)
  have hmono : MonotoneOn Q (Set.Icc 0 1) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 1)
      (fun u _ => (dQ u).continuousAt.continuousWithinAt)
      (fun u _ => (dQ u).hasDerivWithinAt) ?_
    intro u hu
    rw [interior_Icc] at hu
    have hwB : w - B = a * δ := by rw [hw, hδ]; ring
    have hBu : B ≤ Bu u := by
      have := mul_nonneg (mul_nonneg ha0.le hδ0) (sub_nonneg.2 hu.2.le)
      simp only [Bu]; nlinarith
    have hAuBu : Bu u ≤ Au u := by
      have := mul_nonneg hu.1.le hδ0
      simp only [Au, Bu]; nlinarith
    have hBu0 : 0 ≤ Bu u := hB.trans hBu
    have hΔ := Δ_nonneg hBu0 hAuBu
    have hhAB : hh (Au u) ≤ hh (Bu u) := hh_anti hBu0 (hBu0.trans hAuBu) hAuBu
    have hsg : sg (Bu u) ≤ sg (Au u) := sg_mono hAuBu
    have key : -(Au u) * (sg (Au u) * (1 - sg (Au u))) + Bu u * (sg (Bu u) * (1 - sg (Bu u)))
        + 2 * L u * (sg (Au u) - sg (Bu u)) =
        Δ (Au u) (Bu u) + 2 * ((1 - a) * (hh (Bu u) - hh (Au u))) * (sg (Au u) - sg (Bu u)) := by
      simp only [L, Δ]; ring
    have h2 : 0 ≤ 2 * ((1 - a) * (hh (Bu u) - hh (Au u))) * (sg (Au u) - sg (Bu u)) := by
      apply mul_nonneg
      · apply mul_nonneg (by norm_num)
        exact mul_nonneg (by linarith) (by linarith)
      · linarith
    show 0 ≤ Q' u
    simp only [Q']
    rw [key]
    apply mul_nonneg
    · apply mul_nonneg (Real.exp_pos _).le
      exact mul_nonneg (mul_nonneg ha0.le (by linarith)) hδ0
    · linarith
  have h01 := hmono ⟨le_rfl, zero_le_one⟩ ⟨zero_le_one, le_rfl⟩ zero_le_one
  have e0 : Q 0 = hh w := by
    simp only [Q, L, Ex, Au, Bu]
    rw [show w + (1 - a) * 0 * δ = w by ring, show w - a * 0 * δ = w by ring,
      show -2 * (lp w - a * lp w - (1 - a) * lp w) = 0 by ring, Real.exp_zero]
    ring
  have e1 : Q 1 = (a * hh A + (1 - a) * hh B) *
      Real.exp (-2 * (lp w - a * lp A - (1 - a) * lp B)) := by
    simp only [Q, L, Ex, Au, Bu]
    rw [show w + (1 - a) * 1 * δ = A by rw [hw, hδ]; ring,
      show w - a * 1 * δ = B by rw [hw, hδ]; ring]
  rw [e0, e1] at h01
  set X := lp w - a * lp A - (1 - a) * lp B
  have hpos := (Real.exp_pos (2 * X)).le
  calc Real.exp (2 * X) * hh w
      ≤ Real.exp (2 * X) * ((a * hh A + (1 - a) * hh B) * Real.exp (-2 * X)) :=
        mul_le_mul_of_nonneg_left h01 hpos
    _ = (a * hh A + (1 - a) * hh B) * Real.exp (2 * X + -2 * X) := by
        rw [Real.exp_add]; ring
    _ = a * hh A + (1 - a) * hh B := by
        rw [show 2 * X + -2 * X = 0 by ring, Real.exp_zero, mul_one]

theorem n2_logit {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (A B : ℝ) :
    Real.exp (2 * (lp (a * A + (1 - a) * B) - a * lp A - (1 - a) * lp B)) * hh (a * A + (1 - a) * B)
      ≤ a * hh A + (1 - a) * hh B := by
  have hM : a * lp A + (1 - a) * lp B = a * lp |A| + (1 - a) * lp |B| := by rw [lp_abs, lp_abs]
  have split : ∀ v M : ℝ, Real.exp (2 * (lp v - M)) * hh v = Real.exp (-2 * M) * Om v := by
    intro v M; unfold Om
    rw [← mul_assoc, ← Real.exp_add, show 2 * (lp v - M) = -2 * M + 2 * lp v by ring]
  have e : ∀ v, lp v - a * lp A - (1 - a) * lp B = lp v - (a * lp A + (1 - a) * lp B) :=
    fun v => by ring
  rw [e, split]
  have hle : |a * A + (1 - a) * B| ≤ a * |A| + (1 - a) * |B| := by
    have h1 := mul_le_mul_of_nonneg_left (le_abs_self A) ha0.le
    have h2 := mul_le_mul_of_nonneg_left (le_abs_self B) (by linarith : (0 : ℝ) ≤ 1 - a)
    have h3 := mul_le_mul_of_nonneg_left (neg_abs_le A) ha0.le
    have h4 := mul_le_mul_of_nonneg_left (neg_abs_le B) (by linarith : (0 : ℝ) ≤ 1 - a)
    rw [abs_le]; constructor <;> nlinarith
  have hOm : Om (a * A + (1 - a) * B) ≤ Om (a * |A| + (1 - a) * |B|) := by
    rw [← Om_abs (a * A + (1 - a) * B)]
    exact Om_mono (Set.mem_Ici.2 (abs_nonneg _)) (Set.mem_Ici.2 ((abs_nonneg _).trans hle)) hle
  have hnn : Real.exp (2 * (lp (a * |A| + (1 - a) * |B|) - (a * lp |A| + (1 - a) * lp |B|))) *
      hh (a * |A| + (1 - a) * |B|) ≤ a * hh |A| + (1 - a) * hh |B| := by
    rcases le_total |B| |A| with h | h
    · have := path_ineq (δ := |A| - |B|) ha0 ha1 (abs_nonneg B) h rfl rfl
      rw [show lp (a * |A| + (1 - a) * |B|) - (a * lp |A| + (1 - a) * lp |B|) =
        lp (a * |A| + (1 - a) * |B|) - a * lp |A| - (1 - a) * lp |B| by ring]
      exact this
    · have := path_ineq (a := 1 - a) (A := |B|) (B := |A|) (w := a * |A| + (1 - a) * |B|)
        (δ := |B| - |A|) (by linarith) (by linarith) (abs_nonneg A) h (by ring) rfl
      rw [show lp (a * |A| + (1 - a) * |B|) - (a * lp |A| + (1 - a) * lp |B|) =
        lp (a * |A| + (1 - a) * |B|) - (1 - a) * lp |B| - (1 - (1 - a)) * lp |A| by ring]
      linarith
  rw [hh_abs, hh_abs, ← hM, split] at hnn
  calc Real.exp (-2 * (a * lp A + (1 - a) * lp B)) * Om (a * A + (1 - a) * B)
      ≤ Real.exp (-2 * (a * lp A + (1 - a) * lp B)) * Om (a * |A| + (1 - a) * |B|) :=
        mul_le_mul_of_nonneg_left hOm (Real.exp_pos _).le
    _ ≤ _ := hnn

/-! Probability form of the two-point case. -/

lemma sg_logit {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) : sg (Real.log x - Real.log (1 - x)) = x := by
  have h1 : 0 < 1 - x := by linarith
  rw [sg_exp]
  have : Real.log (sg (Real.log x - Real.log (1 - x))) = Real.log x := by
    have hl := log_sg (Real.log x - Real.log (1 - x))
    have hl2 := log_one_sub_sg (Real.log x - Real.log (1 - x))
    -- log sg - log (1 - sg) = t, and sg + (1 - sg) = 1
    have hs := sg_pos (Real.log x - Real.log (1 - x))
    have hs1 := sg_lt_one (Real.log x - Real.log (1 - x))
    set s := sg (Real.log x - Real.log (1 - x))
    have hdiff : Real.log s - Real.log (1 - s) = Real.log x - Real.log (1 - x) := by
      rw [hl, hl2]; ring
    -- the map s ↦ log s - log (1 - s) is injective on (0,1)
    have inj : ∀ u v : ℝ, 0 < u → u < 1 → 0 < v → v < 1 →
        Real.log u - Real.log (1 - u) ≤ Real.log v - Real.log (1 - v) → u ≤ v := by
      intro u v hu0 hu1 hv0 hv1 h
      by_contra hc
      rw [not_le] at hc
      have := Real.log_lt_log hv0 hc
      have := Real.log_lt_log (by linarith : 0 < 1 - u) (by linarith : 1 - u < 1 - v)
      linarith
    have := le_antisymm (inj s x hs hs1 hx0 hx1 hdiff.le) (inj x s hx0 hx1 hs hs1 hdiff.ge)
    rw [this]
  rw [← sg_exp, ← Real.exp_log (sg_pos _), this, Real.exp_log hx0]

lemma ent_scale (K p : ℝ) :
    K * (Real.negMulLog (K * p) + Real.negMulLog (K * (1 - p))) + K ^ 2 * Real.log K
      = K ^ 2 * (Real.negMulLog p + Real.negMulLog (1 - p)) := by
  rw [Real.negMulLog_mul, Real.negMulLog_mul]
  simp only [Real.negMulLog]
  ring

theorem two_point {a x y : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (hx0 : 0 < x) (hx1 : x < 1)
    (hy0 : 0 < y) (hy1 : y < 1) :
    (x ^ a * y ^ (1 - a) + (1 - x) ^ a * (1 - y) ^ (1 - a)) *
        (Real.negMulLog (x ^ a * y ^ (1 - a)) + Real.negMulLog ((1 - x) ^ a * (1 - y) ^ (1 - a))) +
      (x ^ a * y ^ (1 - a) + (1 - x) ^ a * (1 - y) ^ (1 - a)) ^ 2 *
        Real.log (x ^ a * y ^ (1 - a) + (1 - x) ^ a * (1 - y) ^ (1 - a))
      ≤ a * (Real.negMulLog x + Real.negMulLog (1 - x)) +
        (1 - a) * (Real.negMulLog y + Real.negMulLog (1 - y)) := by
  have hx1' : 0 < 1 - x := by linarith
  have hy1' : 0 < 1 - y := by linarith
  set A := Real.log x - Real.log (1 - x)
  set B := Real.log y - Real.log (1 - y)
  have hxA : sg A = x := sg_logit hx0 hx1
  have hyB : sg B = y := sg_logit hy0 hy1
  have lx : Real.log x = A / 2 - lp A := by rw [← log_sg, hxA]
  have lx' : Real.log (1 - x) = -A / 2 - lp A := by rw [← log_one_sub_sg, hxA]
  have ly : Real.log y = B / 2 - lp B := by rw [← log_sg, hyB]
  have ly' : Real.log (1 - y) = -B / 2 - lp B := by rw [← log_one_sub_sg, hyB]
  set w := a * A + (1 - a) * B
  set M := a * lp A + (1 - a) * lp B
  obtain ⟨K, hKdef⟩ : ∃ K, K = Real.exp (lp w - M) := ⟨_, rfl⟩
  have hz1 : x ^ a * y ^ (1 - a) = K * sg w := by
    rw [hKdef, Real.rpow_def_of_pos hx0, Real.rpow_def_of_pos hy0, ← Real.exp_add, sg_exp, ← Real.exp_add,
      lx, ly]
    congr 1; simp only [w, M]; ring
  have hz2 : (1 - x) ^ a * (1 - y) ^ (1 - a) = K * (1 - sg w) := by
    rw [hKdef, Real.rpow_def_of_pos hx1', Real.rpow_def_of_pos hy1', ← Real.exp_add, one_sub_sg_exp,
      ← Real.exp_add, lx', ly']
    congr 1; simp only [w, M]; ring
  have hK : x ^ a * y ^ (1 - a) + (1 - x) ^ a * (1 - y) ^ (1 - a) = K := by
    rw [hz1, hz2]; ring
  rw [hK, hz1, hz2, ent_scale, ← hh_ent, ← hxA, ← hyB, ← hh_ent, ← hh_ent]
  have hK2 : K ^ 2 = Real.exp (2 * (lp w - a * lp A - (1 - a) * lp B)) := by
    rw [hKdef, sq, ← Real.exp_add]; congr 1; simp only [M]; ring
  rw [hK2]
  exact n2_logit ha0 ha1 A B


/-! ## General framework -/

section General

open Finset

variable {n : ℕ}

noncomputable def zz (a : ℝ) (X Y : Fin n → ℝ) (i : Fin n) : ℝ := X i ^ a * Y i ^ (1 - a)

noncomputable def KK (a : ℝ) (X Y : Fin n → ℝ) : ℝ := ∑ i, zz a X Y i

/-- `Phi = a H(X) + (1-a) H(Y) - K^2 H(Z)` written without division. -/
noncomputable def Phi (a : ℝ) (X Y : Fin n → ℝ) : ℝ :=
  a * ∑ i, Real.negMulLog (X i) + (1 - a) * ∑ i, Real.negMulLog (Y i)
    - KK a X Y * ∑ i, Real.negMulLog (zz a X Y i) - KK a X Y ^ 2 * Real.log (KK a X Y)

structure Good (X Y : Fin n → ℝ) : Prop where
  x0 : ∀ i, 0 ≤ X i
  y0 : ∀ i, 0 ≤ Y i
  xs : ∑ i, X i = 1
  ys : ∑ i, Y i = 1
  iff : ∀ i, X i = 0 ↔ Y i = 0

noncomputable def supp (X : Fin n → ℝ) : Finset (Fin n) := univ.filter (fun i => X i ≠ 0)

lemma mem_supp {X : Fin n → ℝ} {i : Fin n} : i ∈ supp X ↔ X i ≠ 0 := by simp [supp]

lemma zz_zero {a : ℝ} (ha0 : 0 < a) {X Y : Fin n → ℝ} {i : Fin n} (h : X i = 0) :
    zz a X Y i = 0 := by
  unfold zz; rw [h, Real.zero_rpow ha0.ne', zero_mul]

lemma zz_le {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {X Y : Fin n → ℝ} (G : Good X Y) (i : Fin n) :
    zz a X Y i ≤ a * X i + (1 - a) * Y i :=
  Real.geom_mean_le_arith_mean2_weighted ha0.le (by linarith) (G.x0 i) (G.y0 i) (by ring)

lemma zz_nonneg {a : ℝ} {X Y : Fin n → ℝ} (G : Good X Y) (i : Fin n) : 0 ≤ zz a X Y i :=
  mul_nonneg (Real.rpow_nonneg (G.x0 i) _) (Real.rpow_nonneg (G.y0 i) _)

lemma zz_pos {a : ℝ} {X Y : Fin n → ℝ} (G : Good X Y) {i : Fin n} (h : X i ≠ 0) :
    0 < zz a X Y i := by
  have hx : 0 < X i := lt_of_le_of_ne (G.x0 i) (Ne.symm h)
  have hy : 0 < Y i := lt_of_le_of_ne (G.y0 i) (fun e => h ((G.iff i).2 e.symm))
  exact mul_pos (Real.rpow_pos_of_pos hx _) (Real.rpow_pos_of_pos hy _)

lemma KK_le_one {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {X Y : Fin n → ℝ} (G : Good X Y) :
    KK a X Y ≤ 1 := by
  unfold KK
  calc ∑ i, zz a X Y i ≤ ∑ i, (a * X i + (1 - a) * Y i) := sum_le_sum (fun i _ => zz_le ha0 ha1 G i)
    _ = 1 := by rw [sum_add_distrib, ← mul_sum, ← mul_sum, G.xs, G.ys]; ring

lemma exists_ne_zero {X Y : Fin n → ℝ} (G : Good X Y) : ∃ i, X i ≠ 0 := by
  by_contra h
  push Not at h
  have := G.xs
  simp [h] at this

lemma KK_pos {a : ℝ} {X Y : Fin n → ℝ} (G : Good X Y) : 0 < KK a X Y := by
  obtain ⟨i, hi⟩ := exists_ne_zero G
  unfold KK
  exact lt_of_lt_of_le (zz_pos G hi)
    (single_le_sum (f := fun i => zz a X Y i) (fun j _ => zz_nonneg G j) (mem_univ i))

lemma zz_mul {a : ℝ} {X Y : Fin n → ℝ} {i : Fin n} {v : ℝ} (hX : 0 ≤ X i) (hY : 0 ≤ Y i)
    (hv : 0 ≤ v) : (X i * v) ^ a * (Y i * v) ^ (1 - a) = zz a X Y i * v := by
  have h1 : v ^ a * v ^ (1 - a) = v := by
    rw [← Real.rpow_add' hv (by ring_nf; exact one_ne_zero), show a + (1 - a) = 1 by ring,
      Real.rpow_one]
  unfold zz
  rw [Real.mul_rpow hX hv, Real.mul_rpow hY hv]
  calc X i ^ a * v ^ a * (Y i ^ (1 - a) * v ^ (1 - a))
      = X i ^ a * Y i ^ (1 - a) * (v ^ a * v ^ (1 - a)) := by ring
    _ = _ := by rw [h1]

lemma Phi_scale {a : ℝ} {X Y : Fin n → ℝ} (G : Good X Y) (v : Fin n → ℝ) (hv : ∀ i, 0 ≤ v i) :
    Phi a (fun i => X i * v i) (fun i => Y i * v i) =
      a * ∑ i, Real.negMulLog (X i * v i) + (1 - a) * ∑ i, Real.negMulLog (Y i * v i)
        - (∑ i, zz a X Y i * v i) * ∑ i, Real.negMulLog (zz a X Y i * v i)
        - (∑ i, zz a X Y i * v i) ^ 2 * Real.log (∑ i, zz a X Y i * v i) := by
  have h : ∀ i, zz a (fun i => X i * v i) (fun i => Y i * v i) i = zz a X Y i * v i :=
    fun i => zz_mul (G.x0 i) (G.y0 i) (hv i)
  unfold Phi KK
  simp only [h]

lemma scaled_good {X Y : Fin n → ℝ} (G : Good X Y) (u : Fin n → ℝ) (s : ℝ)
    (hv : ∀ i, 0 ≤ 1 + s * u i) (hXu : ∑ i, X i * u i = 0) (hYu : ∑ i, Y i * u i = 0) :
    Good (fun i => X i * (1 + s * u i)) (fun i => Y i * (1 + s * u i)) where
  x0 i := mul_nonneg (G.x0 i) (hv i)
  y0 i := mul_nonneg (G.y0 i) (hv i)
  xs := by
    have : ∀ i, X i * (1 + s * u i) = X i + s * (X i * u i) := fun i => by ring
    simp only [this, sum_add_distrib, ← mul_sum, hXu, G.xs]; ring
  ys := by
    have : ∀ i, Y i * (1 + s * u i) = Y i + s * (Y i * u i) := fun i => by ring
    simp only [this, sum_add_distrib, ← mul_sum, hYu, G.ys]; ring
  iff i := by
    simp only [mul_eq_zero]
    rw [G.iff i]

lemma supp_scaled_lt {X : Fin n → ℝ} (v : Fin n → ℝ) {i0 : Fin n} (hi0 : X i0 ≠ 0) (hv : v i0 = 0) :
    (supp (fun i => X i * v i)).card < (supp X).card := by
  apply card_lt_card
  rw [ssubset_iff_of_subset]
  · refine ⟨i0, mem_supp.2 hi0, ?_⟩
    rw [mem_supp, hv, mul_zero]; exact fun h => h rfl
  · intro i hi
    rw [mem_supp] at hi ⊢
    exact fun h => hi (by rw [h, zero_mul])

lemma endpoint (T : Finset (Fin n)) (u : Fin n → ℝ) (h : ∃ i ∈ T, u i < 0) :
    ∃ s > 0, (∀ i ∈ T, 0 ≤ 1 + s * u i) ∧ ∃ i ∈ T, 1 + s * u i = 0 := by
  obtain ⟨i, hiT, hi⟩ := h
  obtain ⟨i0, hi0, hmin⟩ := exists_min_image (T.filter (fun i => u i < 0)) (fun i => -1 / u i)
    ⟨i, mem_filter.2 ⟨hiT, hi⟩⟩
  rw [mem_filter] at hi0
  refine ⟨-1 / u i0, div_pos_of_neg_of_neg (by norm_num) hi0.2, ?_, i0, hi0.1, ?_⟩
  · intro j hj
    by_cases hu : u j < 0
    · have := hmin j (mem_filter.2 ⟨hj, hu⟩)
      have h2 : -1 / u j * u j = -1 := div_mul_cancel₀ (-1) hu.ne
      nlinarith [mul_le_mul_of_nonpos_right this hu.le]
    · push Not at hu
      have : 0 ≤ -1 / u i0 := (div_pos_of_neg_of_neg (by norm_num) hi0.2).le
      nlinarith [mul_nonneg this hu]
  · field_simp [hi0.2.ne]; ring

lemma neg_exists {X Y : Fin n → ℝ} (G : Good X Y) (u : Fin n → ℝ)
    (hune : ∃ i, X i ≠ 0 ∧ u i ≠ 0) (hXu : ∑ i, X i * u i = 0) : ∃ i ∈ supp X, u i < 0 := by
  by_contra h
  push Not at h
  have hnn : ∀ i ∈ univ, 0 ≤ X i * u i := by
    intro i _
    by_cases hx : X i = 0
    · rw [hx, zero_mul]
    · exact mul_nonneg (G.x0 i) (h i (mem_supp.2 hx))
  have := (sum_eq_zero_iff_of_nonneg hnn).1 hXu
  obtain ⟨i, hx, hu⟩ := hune
  exact mul_ne_zero hx hu (this i (mem_univ i))

lemma descent {X Y : Fin n → ℝ} (G : Good X Y) (u : Fin n → ℝ) (hu0 : ∀ i, X i = 0 → u i = 0)
    (hune : ∃ i, X i ≠ 0 ∧ u i ≠ 0) (hXu : ∑ i, X i * u i = 0) :
    ∃ s1 s2 : ℝ, 0 < s1 ∧ 0 < s2 ∧ (∀ i, 0 ≤ 1 + s1 * u i) ∧ (∀ i, 0 ≤ 1 + (-s2) * u i) ∧
      (supp (fun i => X i * (1 + s1 * u i))).card < (supp X).card ∧
      (supp (fun i => X i * (1 + (-s2) * u i))).card < (supp X).card := by
  obtain ⟨s1, hs1, hv1, i1, hi1, he1⟩ := endpoint (supp X) u (neg_exists G u hune hXu)
  have hune' : ∃ i, X i ≠ 0 ∧ (-u) i ≠ 0 := by
    obtain ⟨i, h1, h2⟩ := hune; exact ⟨i, h1, by simpa using h2⟩
  have hXu' : ∑ i, X i * (-u) i = 0 := by simp [hXu]
  obtain ⟨s2, hs2, hv2, i2, hi2, he2⟩ := endpoint (supp X) (-u) (neg_exists G (-u) hune' hXu')
  refine ⟨s1, s2, hs1, hs2, ?_, ?_, ?_, ?_⟩
  · intro i
    by_cases hx : X i = 0
    · rw [hu0 i hx]; norm_num
    · exact hv1 i (mem_supp.2 hx)
  · intro i
    by_cases hx : X i = 0
    · rw [hu0 i hx]; norm_num
    · have := hv2 i (mem_supp.2 hx); simp only [Pi.neg_apply] at this; linarith
  · exact supp_scaled_lt (fun i => 1 + s1 * u i) (mem_supp.1 hi1) he1
  · refine supp_scaled_lt (fun i => 1 + (-s2) * u i) (mem_supp.1 hi2) ?_
    simp only [Pi.neg_apply] at he2; linarith

lemma kernel_exists (t : Finset (Fin n)) (k : ℕ) (ht : t.card = k) (F : Fin k → Fin n → ℝ)
    (r0 : Fin k) (hr0 : F r0 = 0) :
    ∃ u : Fin n → ℝ, (∀ i, i ∉ t → u i = 0) ∧ (∃ i ∈ t, u i ≠ 0) ∧
      ∀ r, ∑ i, F r i * u i = 0 := by
  classical
  let e := t.orderEmbOfFin ht
  let M : Matrix (Fin k) (Fin k) ℝ := fun r l => F r (e l)
  have hdet : M.det = 0 := Matrix.det_eq_zero_of_row_eq_zero r0 (fun l => by simp [M, hr0])
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet
  let u : Fin n → ℝ := fun i => ∑ l, if e l = i then v l else 0
  have hu_e : ∀ l, u (e l) = v l := by
    intro l; simp only [u]
    rw [sum_eq_single l]
    · simp
    · intro b _ hb; rw [if_neg]; exact fun h => hb (e.injective h)
    · intro h; exact absurd (mem_univ l) h
  refine ⟨u, ?_, ?_, ?_⟩
  · intro i hi; simp only [u]
    apply sum_eq_zero; intro l _
    rw [if_neg]; intro h; exact hi (h ▸ t.orderEmbOfFin_mem ht l)
  · obtain ⟨l, hl⟩ := Function.ne_iff.1 hv0
    exact ⟨e l, t.orderEmbOfFin_mem ht l, by rw [hu_e]; exact hl⟩
  · intro r
    have h1 := congrFun hv r
    simp only [Matrix.mulVec, dotProduct, Pi.zero_apply] at h1
    rw [← h1]; simp only [u, mul_sum]
    rw [sum_comm]
    apply sum_congr rfl; intro l _
    rw [sum_eq_single (e l)]
    · simp [M]
    · intro b _ hb; rw [if_neg (Ne.symm hb), mul_zero]
    · intro h; exact absurd (mem_univ _) h

lemma Phi_self {a : ℝ} {X : Fin n → ℝ} (hx : ∀ i, 0 ≤ X i) (hs : ∑ i, X i = 1) : Phi a X X = 0 := by
  have hz : ∀ i, zz a X X i = X i := by
    intro i; unfold zz
    rw [← Real.rpow_add' (hx i) (by ring_nf; exact one_ne_zero), show a + (1 - a) = 1 by ring,
      Real.rpow_one]
  unfold Phi KK; simp only [hz, hs]; simp; ring

/-! ## Part I: four or more atoms -/

lemma Phi_expand {a : ℝ} {X Y : Fin n → ℝ} (G : Good X Y) (v : Fin n → ℝ) (hv : ∀ i, 0 ≤ v i)
    (hK : ∑ i, zz a X Y i * v i = KK a X Y) :
    Phi a (fun i => X i * v i) (fun i => Y i * v i) =
      ∑ i, ((a * X i + (1 - a) * Y i - KK a X Y * zz a X Y i) * Real.negMulLog (v i) +
        v i * (a * Real.negMulLog (X i) + (1 - a) * Real.negMulLog (Y i)
          - KK a X Y * Real.negMulLog (zz a X Y i)))
        - KK a X Y ^ 2 * Real.log (KK a X Y) := by
  rw [Phi_scale G v hv, hK]
  congr 1
  rw [mul_sum, mul_sum, mul_sum, ← sum_add_distrib, ← sum_sub_distrib]
  apply sum_congr rfl; intro i _
  rw [Real.negMulLog_mul, Real.negMulLog_mul, Real.negMulLog_mul]
  ring

lemma partI_concave {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {X Y : Fin n → ℝ} (G : Good X Y)
    (v1 v2 : Fin n → ℝ) (hv1 : ∀ i, 0 ≤ v1 i) (hv2 : ∀ i, 0 ≤ v2 i)
    (hK1 : ∑ i, zz a X Y i * v1 i = KK a X Y) (hK2 : ∑ i, zz a X Y i * v2 i = KK a X Y)
    (l : ℝ) (hl0 : 0 ≤ l) (hl1 : l ≤ 1) (hv : ∀ i, l * v1 i + (1 - l) * v2 i = 1) :
    l * Phi a (fun i => X i * v1 i) (fun i => Y i * v1 i) +
      (1 - l) * Phi a (fun i => X i * v2 i) (fun i => Y i * v2 i) ≤ Phi a X Y := by
  have h1 : ∀ _ : Fin n, (0 : ℝ) ≤ 1 := fun _ => zero_le_one
  have hK0 : ∑ i, zz a X Y i * 1 = KK a X Y := by simp [KK]
  have e0 := Phi_expand (a := a) G (fun _ => 1) h1 hK0
  simp only [mul_one, one_mul, Real.negMulLog_one, mul_zero, zero_add] at e0
  rw [Phi_expand G v1 hv1 hK1, Phi_expand G v2 hv2 hK2, e0]
  set C := KK a X Y ^ 2 * Real.log (KK a X Y)
  rw [show ∀ (A B : ℝ), l * (A - C) + (1 - l) * (B - C) = l * A + (1 - l) * B - C from
    fun A B => by ring]
  rw [mul_sum, mul_sum, ← sum_add_distrib]
  gcongr with i _
  have hK1' := KK_le_one ha0 ha1 G
  have hc : 0 ≤ a * X i + (1 - a) * Y i - KK a X Y * zz a X Y i := by
    have := zz_le ha0 ha1 G i
    have := zz_nonneg (a := a) G i
    nlinarith [KK_pos (a := a) G]
  have hconc := concaveOn_negMulLog.2 (Set.mem_Ici.2 (hv1 i)) (Set.mem_Ici.2 (hv2 i)) hl0
    (by linarith : 0 ≤ 1 - l) (by ring)
  simp only [smul_eq_mul, hv i, Real.negMulLog_one] at hconc
  set c := a * X i + (1 - a) * Y i - KK a X Y * zz a X Y i
  set E := a * Real.negMulLog (X i) + (1 - a) * Real.negMulLog (Y i)
    - KK a X Y * Real.negMulLog (zz a X Y i)
  have key : l * (c * Real.negMulLog (v1 i) + v1 i * E) + (1 - l) * (c * Real.negMulLog (v2 i) + v2 i * E)
      = c * (l * Real.negMulLog (v1 i) + (1 - l) * Real.negMulLog (v2 i)) +
        (l * v1 i + (1 - l) * v2 i) * E := by ring
  rw [key, hv i]
  nlinarith [mul_le_mul_of_nonneg_left hconc hc]


/-! ## Part II: three atoms -/

lemma cosh_ge (x : ℝ) : 1 + x ^ 2 / 2 ≤ Real.cosh x := by
  have h := Real.cosh_two_mul (x / 2)
  rw [show 2 * (x / 2) = x by ring] at h
  have h2 := Real.cosh_sq (x / 2)
  have h3 : (x / 2) ^ 2 ≤ Real.sinh (x / 2) ^ 2 := by
    rcases le_total 0 (x / 2) with hy | hy
    · have := Real.self_le_sinh_iff.2 hy; nlinarith
    · have := Real.self_le_sinh_iff.2 (neg_nonneg.2 hy)
      rw [Real.sinh_neg] at this; nlinarith
  nlinarith

lemma two_pt {p q : ℝ} (hp : 0 < p) (hq : 0 < q) :
    2 * p * q * (Real.log p - Real.log q) ^ 2 ≤ (p + q) ^ 2 := by
  obtain ⟨L, hL⟩ : ∃ L, L = Real.log p - Real.log q := ⟨_, rfl⟩
  rw [← hL]
  have hpq : p = q * Real.exp L := by
    rw [hL, Real.exp_sub, Real.exp_log hp, Real.exp_log hq]; field_simp
  have hc := cosh_ge (L / 2)
  rw [Real.cosh_eq] at hc
  obtain ⟨E, hE⟩ : ∃ E, E = Real.exp (L / 2) := ⟨_, rfl⟩
  obtain ⟨F, hF⟩ : ∃ F, F = Real.exp (-(L / 2)) := ⟨_, rfl⟩
  rw [← hE, ← hF] at hc
  have hEF : E * F = 1 := by rw [hE, hF, ← Real.exp_add]; simp
  have hE2 : Real.exp L = E ^ 2 := by rw [hE, sq, ← Real.exp_add]; ring_nf
  have hsum : 2 + L ^ 2 / 4 ≤ E + F := by nlinarith
  have key : 2 * E ^ 2 * L ^ 2 ≤ (E ^ 2 + 1) ^ 2 := by
    have e1 : E ^ 2 + 1 = E * (E + F) := by rw [mul_add, hEF]; ring
    rw [e1]
    have h0 : 0 ≤ 2 + L ^ 2 / 4 := by positivity
    have h4 := mul_le_mul hsum hsum h0 (by linarith)
    have h5 : 2 * L ^ 2 ≤ (E + F) ^ 2 := by nlinarith [sq_nonneg (2 - L ^ 2 / 4)]
    have h6 := mul_le_mul_of_nonneg_left h5 (sq_nonneg E)
    nlinarith
  rw [hpq, hE2]
  nlinarith [mul_le_mul_of_nonneg_left key (sq_nonneg q)]

set_option maxHeartbeats 1000000 in
lemma Q3core {w1 w2 w3 z1 z2 z3 t1 t2 t3 l1 l2 l3 : ℝ} (hz1 : 0 < z1) (hz2 : 0 < z2) (hz3 : 0 < z3)
    (hle1 : z1 ≤ w1) (hle2 : z2 ≤ w2) (hle3 : z3 ≤ w3) (hw : w1 + w2 + w3 = 1)
    (hwt : w1 * t1 + w2 * t2 + w3 * t3 = 0) (hl1 : l1 ≤ 0) (hl2 : l2 ≤ 0) (hl3 : l3 ≤ 0)
    (hV : (z1 + z2 + z3) * (z1 * l1 ^ 2 + z2 * l2 ^ 2 + z3 * l3 ^ 2)
      - (z1 * l1 + z2 * l2 + z3 * l3) ^ 2 ≤ (z1 + z2 + z3) ^ 2) :
    0 ≤ (w1 - (z1 + z2 + z3) * z1) * t1 ^ 2 + (w2 - (z1 + z2 + z3) * z2) * t2 ^ 2
      + (w3 - (z1 + z2 + z3) * z3) * t3 ^ 2
      - 2 * (z1 * t1 + z2 * t2 + z3 * t3) * (z1 * t1 * l1 + z2 * t2 * l2 + z3 * t3 * l3)
      + (z1 * t1 + z2 * t2 + z3 * t3) ^ 2 := by
  obtain ⟨K, hK⟩ : ∃ K, K = z1 + z2 + z3 := ⟨_, rfl⟩
  obtain ⟨k, hk⟩ : ∃ k, k = z1 * t1 + z2 * t2 + z3 * t3 := ⟨_, rfl⟩
  obtain ⟨G2, hG2⟩ : ∃ x, x = (w1 - z1) * t1 ^ 2 + (w2 - z2) * t2 ^ 2 + (w3 - z3) * t3 ^ 2 :=
    ⟨_, rfl⟩
  obtain ⟨S2, hS2⟩ : ∃ x, x = z1 * t1 ^ 2 + z2 * t2 ^ 2 + z3 * t3 ^ 2 := ⟨_, rfl⟩
  obtain ⟨S1, hS1⟩ : ∃ x, x = z1 * t1 * l1 + z2 * t2 * l2 + z3 * t3 * l3 := ⟨_, rfl⟩
  obtain ⟨P, hP⟩ : ∃ x, x = z1 * l1 + z2 * l2 + z3 * l3 := ⟨_, rfl⟩
  obtain ⟨R, hR⟩ : ∃ x, x = z1 * l1 ^ 2 + z2 * l2 ^ 2 + z3 * l3 ^ 2 := ⟨_, rfl⟩
  have hKpos : 0 < K := by rw [hK]; linarith
  have hK1 : K ≤ 1 := by rw [hK]; linarith
  have g1 := sub_nonneg.2 hle1
  have g2 := sub_nonneg.2 hle2
  have g3 := sub_nonneg.2 hle3
  have hQ : (w1 - (z1 + z2 + z3) * z1) * t1 ^ 2 + (w2 - (z1 + z2 + z3) * z2) * t2 ^ 2
      + (w3 - (z1 + z2 + z3) * z3) * t3 ^ 2
      - 2 * (z1 * t1 + z2 * t2 + z3 * t3) * (z1 * t1 * l1 + z2 * t2 * l2 + z3 * t3 * l3)
      + (z1 * t1 + z2 * t2 + z3 * t3) ^ 2 = G2 + (1 - K) * S2 - 2 * k * S1 + k ^ 2 := by
    rw [hG2, hS2, hS1, hK, hk]; ring
  rw [hQ]
  have hCS : 0 ≤ (1 - K) * G2 - k ^ 2 := by
    have e : (1 - K) * G2 - k ^ 2 = (w1 - z1) * (w2 - z2) * (t1 - t2) ^ 2 +
        (w1 - z1) * (w3 - z3) * (t1 - t3) ^ 2 + (w2 - z2) * (w3 - z3) * (t2 - t3) ^ 2 := by
      rw [hG2, hK, hk]
      linear_combination (-((w1 - z1) * t1 ^ 2 + (w2 - z2) * t2 ^ 2 + (w3 - z3) * t3 ^ 2)) * hw +
        (-2 * (z1 * t1 + z2 * t2 + z3 * t3) + (w1 * t1 + w2 * t2 + w3 * t3)) * hwt
    rw [e]
    have := mul_nonneg (mul_nonneg g1 g2) (sq_nonneg (t1 - t2))
    have := mul_nonneg (mul_nonneg g1 g3) (sq_nonneg (t1 - t3))
    have := mul_nonneg (mul_nonneg g2 g3) (sq_nonneg (t2 - t3))
    linarith
  have hSOS : 0 ≤ (1 - K) ^ 2 * (K * S2 - k ^ 2) - 2 * (1 - K) * k * (K * S1 - k * P)
      + k ^ 2 * (K * R - P ^ 2) := by
    have e : K * ((1 - K) ^ 2 * (K * S2 - k ^ 2) - 2 * (1 - K) * k * (K * S1 - k * P)
        + k ^ 2 * (K * R - P ^ 2)) =
        z1 * ((1 - K) * (K * t1 - k) - k * (K * l1 - P)) ^ 2 +
        z2 * ((1 - K) * (K * t2 - k) - k * (K * l2 - P)) ^ 2 +
        z3 * ((1 - K) * (K * t3 - k) - k * (K * l3 - P)) ^ 2 := by
      rw [hS2, hS1, hR, hP, hK, hk]; ring
    have h0 : 0 ≤ K * ((1 - K) ^ 2 * (K * S2 - k ^ 2) - 2 * (1 - K) * k * (K * S1 - k * P)
        + k ^ 2 * (K * R - P ^ 2)) := by
      rw [e]
      have := mul_nonneg hz1.le (sq_nonneg ((1 - K) * (K * t1 - k) - k * (K * l1 - P)))
      have := mul_nonneg hz2.le (sq_nonneg ((1 - K) * (K * t2 - k) - k * (K * l2 - P)))
      have := mul_nonneg hz3.le (sq_nonneg ((1 - K) * (K * t3 - k) - k * (K * l3 - P)))
      linarith
    exact (mul_nonneg_iff_of_pos_left hKpos).1 h0
  have hT : 0 ≤ 1 - 2 * (1 - K) * P - (K * R - P ^ 2) := by
    have hP0 : P ≤ 0 := by
      rw [hP]
      linarith [mul_nonpos_of_nonneg_of_nonpos hz1.le hl1, mul_nonpos_of_nonneg_of_nonpos hz2.le hl2,
        mul_nonpos_of_nonneg_of_nonpos hz3.le hl3]
    have hV' : K * R - P ^ 2 ≤ K ^ 2 := by rw [hK, hR, hP]; exact hV
    have := mul_nonneg (sub_nonneg.2 hK1) (neg_nonneg.2 hP0)
    have := mul_le_mul hK1 hK1 hKpos.le zero_le_one
    nlinarith only [this, hV', mul_nonneg (sub_nonneg.2 hK1) (neg_nonneg.2 hP0)]
  have hmain : K * ((1 - K) * (G2 + (1 - K) * S2 - 2 * k * S1 + k ^ 2)) =
      K * ((1 - K) * G2 - k ^ 2) + ((1 - K) ^ 2 * (K * S2 - k ^ 2) - 2 * (1 - K) * k * (K * S1 - k * P)
        + k ^ 2 * (K * R - P ^ 2)) + k ^ 2 * (1 - 2 * (1 - K) * P - (K * R - P ^ 2)) := by ring
  have h0 : 0 ≤ K * ((1 - K) * (G2 + (1 - K) * S2 - 2 * k * S1 + k ^ 2)) := by
    rw [hmain]
    have := mul_nonneg hKpos.le hCS
    have := mul_nonneg (sq_nonneg k) hT
    linarith
  have h1 := (mul_nonneg_iff_of_pos_left hKpos).1 h0
  rcases lt_or_eq_of_le hK1 with hlt | heq
  · exact (mul_nonneg_iff_of_pos_left (by linarith)).1 h1
  · have hk0 : k = 0 := by
      have h := hCS
      rw [heq, sub_self, zero_mul, zero_sub, neg_nonneg] at h
      exact (pow_eq_zero_iff two_ne_zero).1 (le_antisymm h (sq_nonneg k))
    have hG : 0 ≤ G2 := by
      rw [hG2]
      have := mul_nonneg g1 (sq_nonneg t1)
      have := mul_nonneg g2 (sq_nonneg t2)
      have := mul_nonneg g3 (sq_nonneg t3)
      linarith
    rw [hk0, heq]
    have e : G2 + (1 - 1) * S2 - 2 * 0 * S1 + (0 : ℝ) ^ 2 = G2 := by ring
    rw [e]; exact hG

lemma Q3 {w1 w2 w3 z1 z2 z3 t1 t2 t3 : ℝ} (hz1 : 0 < z1) (hz2 : 0 < z2) (hz3 : 0 < z3)
    (hle1 : z1 ≤ w1) (hle2 : z2 ≤ w2) (hle3 : z3 ≤ w3) (hw : w1 + w2 + w3 = 1)
    (hwt : w1 * t1 + w2 * t2 + w3 * t3 = 0) :
    0 ≤ (w1 - (z1 + z2 + z3) * z1) * t1 ^ 2 + (w2 - (z1 + z2 + z3) * z2) * t2 ^ 2
      + (w3 - (z1 + z2 + z3) * z3) * t3 ^ 2
      - 2 * (z1 * t1 + z2 * t2 + z3 * t3) *
        (z1 * t1 * Real.log z1 + z2 * t2 * Real.log z2 + z3 * t3 * Real.log z3)
      + 2 * (z1 * t1 + z2 * t2 + z3 * t3) ^ 2 * Real.log (z1 + z2 + z3)
      + (z1 * t1 + z2 * t2 + z3 * t3) ^ 2 := by
  have hK : 0 < z1 + z2 + z3 := by linarith
  have hl : ∀ z : ℝ, 0 < z → z ≤ z1 + z2 + z3 → Real.log z - Real.log (z1 + z2 + z3) ≤ 0 :=
    fun z hz hzK => by linarith [Real.log_le_log hz hzK]
  have hV : (z1 + z2 + z3) * (z1 * (Real.log z1 - Real.log (z1 + z2 + z3)) ^ 2 +
      z2 * (Real.log z2 - Real.log (z1 + z2 + z3)) ^ 2 + z3 * (Real.log z3 - Real.log (z1 + z2 + z3)) ^ 2)
      - (z1 * (Real.log z1 - Real.log (z1 + z2 + z3)) + z2 * (Real.log z2 - Real.log (z1 + z2 + z3))
        + z3 * (Real.log z3 - Real.log (z1 + z2 + z3))) ^ 2 ≤ (z1 + z2 + z3) ^ 2 := by
    have e : (z1 + z2 + z3) * (z1 * (Real.log z1 - Real.log (z1 + z2 + z3)) ^ 2 +
      z2 * (Real.log z2 - Real.log (z1 + z2 + z3)) ^ 2 + z3 * (Real.log z3 - Real.log (z1 + z2 + z3)) ^ 2)
      - (z1 * (Real.log z1 - Real.log (z1 + z2 + z3)) + z2 * (Real.log z2 - Real.log (z1 + z2 + z3))
        + z3 * (Real.log z3 - Real.log (z1 + z2 + z3))) ^ 2 =
        z1 * z2 * (Real.log z1 - Real.log z2) ^ 2 + z1 * z3 * (Real.log z1 - Real.log z3) ^ 2 +
        z2 * z3 * (Real.log z2 - Real.log z3) ^ 2 := by ring
    rw [e]
    have := two_pt hz1 hz2
    have := two_pt hz1 hz3
    have := two_pt hz2 hz3
    nlinarith only [this, two_pt hz1 hz2, two_pt hz1 hz3, mul_pos hz1 hz2, mul_pos hz1 hz3,
      mul_pos hz2 hz3]
  have := Q3core (t1 := t1) (t2 := t2) (t3 := t3) hz1 hz2 hz3 hle1 hle2 hle3 hw hwt
    (hl z1 hz1 (by linarith)) (hl z2 hz2 (by linarith)) (hl z3 hz3 (by linarith)) hV
  refine le_of_le_of_eq this ?_
  ring

/-! Derivatives along the multiplicative family. -/

lemma hd_eta (c u s : ℝ) (h : c = 0 ∨ c * (1 + s * u) ≠ 0) :
    HasDerivAt (fun s => Real.negMulLog (c * (1 + s * u)))
      (c * u * (-Real.log (c * (1 + s * u)) - 1)) s := by
  rcases h with h | h
  · subst h; simp only [zero_mul, Real.negMulLog_zero]; exact hasDerivAt_const s 0
  · have hin : HasDerivAt (fun s => c * (1 + s * u)) (c * u) s :=
      ((((hasDerivAt_id' s).mul_const u).const_add 1).const_mul c).congr_deriv (by ring)
    refine ((Real.hasDerivAt_negMulLog h).comp s hin).congr_deriv ?_
    ring

lemma hd_eta2 (c u s : ℝ) (h : c = 0 ∨ c * (1 + s * u) ≠ 0) :
    HasDerivAt (fun s => c * u * (-Real.log (c * (1 + s * u)) - 1))
      (-(c * u ^ 2 / (1 + s * u))) s := by
  rcases h with h | h
  · subst h; simp only [zero_mul, zero_div, neg_zero]; exact hasDerivAt_const s 0
  · have hin : HasDerivAt (fun s => c * (1 + s * u)) (c * u) s :=
      ((((hasDerivAt_id' s).mul_const u).const_add 1).const_mul c).congr_deriv (by ring)
    have hc : c ≠ 0 := left_ne_zero_of_mul h
    have hv : 1 + s * u ≠ 0 := right_ne_zero_of_mul h
    refine (((hin.log h).neg.sub_const 1).const_mul (c * u)).congr_deriv ?_
    field_simp

noncomputable def E1 (u P : Fin n → ℝ) (s : ℝ) : ℝ := ∑ i, Real.negMulLog (P i * (1 + s * u i))
noncomputable def D1 (u P : Fin n → ℝ) (s : ℝ) : ℝ :=
  ∑ i, P i * u i * (-Real.log (P i * (1 + s * u i)) - 1)
noncomputable def D2 (u P : Fin n → ℝ) (s : ℝ) : ℝ := ∑ i, -(P i * u i ^ 2 / (1 + s * u i))
noncomputable def Kf (u P : Fin n → ℝ) (s : ℝ) : ℝ := ∑ i, P i * (1 + s * u i)

lemma hasDerivAt_E1 (u P : Fin n → ℝ) (s : ℝ) (h : ∀ i, P i = 0 ∨ P i * (1 + s * u i) ≠ 0) :
    HasDerivAt (E1 u P) (D1 u P s) s := by
  unfold E1 D1
  exact HasDerivAt.fun_sum (fun i _ => hd_eta (P i) (u i) s (h i))

lemma hasDerivAt_D1 (u P : Fin n → ℝ) (s : ℝ) (h : ∀ i, P i = 0 ∨ P i * (1 + s * u i) ≠ 0) :
    HasDerivAt (D1 u P) (D2 u P s) s := by
  unfold D1 D2
  exact HasDerivAt.fun_sum (fun i _ => hd_eta2 (P i) (u i) s (h i))

lemma hasDerivAt_Kf (u P : Fin n → ℝ) (s : ℝ) : HasDerivAt (Kf u P) (∑ i, P i * u i) s := by
  unfold Kf
  exact HasDerivAt.fun_sum (fun i _ =>
    ((((hasDerivAt_id' s).mul_const (u i)).const_add 1).const_mul (P i)).congr_deriv (by ring))

lemma continuous_E1 (u P : Fin n → ℝ) : Continuous (E1 u P) := by
  unfold E1
  exact continuous_finsetSum _ (fun i _ => Real.continuous_negMulLog.comp (by fun_prop))

lemma continuous_Kf (u P : Fin n → ℝ) : Continuous (Kf u P) := by
  unfold Kf
  exact continuous_finsetSum _ (fun i _ => by fun_prop)

noncomputable def psi (a : ℝ) (X Y u : Fin n → ℝ) (s : ℝ) : ℝ :=
  a * E1 u X s + (1 - a) * E1 u Y s - Kf u (zz a X Y) s * E1 u (zz a X Y) s
    - Kf u (zz a X Y) s ^ 2 * Real.log (Kf u (zz a X Y) s)

noncomputable def psi1 (a : ℝ) (X Y u : Fin n → ℝ) (s : ℝ) : ℝ :=
  a * D1 u X s + (1 - a) * D1 u Y s -
    ((∑ i, zz a X Y i * u i) * E1 u (zz a X Y) s + Kf u (zz a X Y) s * D1 u (zz a X Y) s)
    - (2 * Kf u (zz a X Y) s * (∑ i, zz a X Y i * u i) * Real.log (Kf u (zz a X Y) s)
      + Kf u (zz a X Y) s * (∑ i, zz a X Y i * u i))

noncomputable def psi2 (a : ℝ) (X Y u : Fin n → ℝ) (s : ℝ) : ℝ :=
  a * D2 u X s + (1 - a) * D2 u Y s -
    ((∑ i, zz a X Y i * u i) * D1 u (zz a X Y) s +
      ((∑ i, zz a X Y i * u i) * D1 u (zz a X Y) s + Kf u (zz a X Y) s * D2 u (zz a X Y) s))
    - (2 * (∑ i, zz a X Y i * u i) ^ 2 * Real.log (Kf u (zz a X Y) s)
      + 3 * (∑ i, zz a X Y i * u i) ^ 2)

lemma hasDerivAt_psi (a : ℝ) (X Y u : Fin n → ℝ) (s : ℝ)
    (hX : ∀ i, X i = 0 ∨ X i * (1 + s * u i) ≠ 0) (hY : ∀ i, Y i = 0 ∨ Y i * (1 + s * u i) ≠ 0)
    (hz : ∀ i, zz a X Y i = 0 ∨ zz a X Y i * (1 + s * u i) ≠ 0) (hK : Kf u (zz a X Y) s ≠ 0) :
    HasDerivAt (psi a X Y u) (psi1 a X Y u s) s := by
  have hKf := hasDerivAt_Kf u (zz a X Y) s
  have h := (((hasDerivAt_E1 u X s hX).const_mul a).add ((hasDerivAt_E1 u Y s hY).const_mul (1 - a))).sub
    (hKf.mul (hasDerivAt_E1 u (zz a X Y) s hz)) |>.sub ((hKf.pow 2).mul (hKf.log hK))
  refine h.congr_deriv ?_
  unfold psi1
  simp only [Pi.pow_apply]
  field_simp
  ring

lemma hasDerivAt_psi1 (a : ℝ) (X Y u : Fin n → ℝ) (s : ℝ)
    (hX : ∀ i, X i = 0 ∨ X i * (1 + s * u i) ≠ 0) (hY : ∀ i, Y i = 0 ∨ Y i * (1 + s * u i) ≠ 0)
    (hz : ∀ i, zz a X Y i = 0 ∨ zz a X Y i * (1 + s * u i) ≠ 0) (hK : Kf u (zz a X Y) s ≠ 0) :
    HasDerivAt (psi1 a X Y u) (psi2 a X Y u s) s := by
  have hKf := hasDerivAt_Kf u (zz a X Y) s
  set k := ∑ i, zz a X Y i * u i
  have h := (((hasDerivAt_D1 u X s hX).const_mul a).add ((hasDerivAt_D1 u Y s hY).const_mul (1 - a))).sub
    (((hasDerivAt_E1 u (zz a X Y) s hz).const_mul k).add (hKf.mul (hasDerivAt_D1 u (zz a X Y) s hz)))
    |>.sub ((((hKf.const_mul 2).mul_const k).mul (hKf.log hK)).add (hKf.mul_const k))
  refine h.congr_deriv ?_
  unfold psi2
  field_simp
  ring


lemma sum3 {f : Fin n → ℝ} {i j k : Fin n} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (h : ∀ l, l ≠ i → l ≠ j → l ≠ k → f l = 0) : ∑ l, f l = f i + f j + f k := by
  rw [← Finset.sum_subset (Finset.subset_univ {i, j, k}) (fun l _ hl => by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hl
    exact h l hl.1 hl.2.1 hl.2.2)]
  rw [Finset.sum_insert (by simp [hij, hik]), Finset.sum_insert (by simp [hjk]),
    Finset.sum_singleton]
  ring

lemma psi2_ident (a X1 X2 X3 Y1 Y2 Y3 z1 z2 z3 u1 u2 u3 v1 v2 v3 : ℝ) (h1 : v1 ≠ 0) (h2 : v2 ≠ 0)
    (h3 : v3 ≠ 0) :
    a * (-(X1 * u1 ^ 2 / v1) + -(X2 * u2 ^ 2 / v2) + -(X3 * u3 ^ 2 / v3)) +
      (1 - a) * (-(Y1 * u1 ^ 2 / v1) + -(Y2 * u2 ^ 2 / v2) + -(Y3 * u3 ^ 2 / v3)) -
      ((z1 * u1 + z2 * u2 + z3 * u3) *
          (z1 * u1 * (-Real.log (z1 * v1) - 1) + z2 * u2 * (-Real.log (z2 * v2) - 1) +
            z3 * u3 * (-Real.log (z3 * v3) - 1)) +
        ((z1 * u1 + z2 * u2 + z3 * u3) *
            (z1 * u1 * (-Real.log (z1 * v1) - 1) + z2 * u2 * (-Real.log (z2 * v2) - 1) +
              z3 * u3 * (-Real.log (z3 * v3) - 1)) +
          (z1 * v1 + z2 * v2 + z3 * v3) *
            (-(z1 * u1 ^ 2 / v1) + -(z2 * u2 ^ 2 / v2) + -(z3 * u3 ^ 2 / v3)))) -
      (2 * (z1 * u1 + z2 * u2 + z3 * u3) ^ 2 * Real.log (z1 * v1 + z2 * v2 + z3 * v3) +
        3 * (z1 * u1 + z2 * u2 + z3 * u3) ^ 2)
    = -(((a * X1 + (1 - a) * Y1) * v1 - (z1 * v1 + z2 * v2 + z3 * v3) * (z1 * v1)) * (u1 / v1) ^ 2 +
        ((a * X2 + (1 - a) * Y2) * v2 - (z1 * v1 + z2 * v2 + z3 * v3) * (z2 * v2)) * (u2 / v2) ^ 2 +
        ((a * X3 + (1 - a) * Y3) * v3 - (z1 * v1 + z2 * v2 + z3 * v3) * (z3 * v3)) * (u3 / v3) ^ 2 -
        2 * (z1 * v1 * (u1 / v1) + z2 * v2 * (u2 / v2) + z3 * v3 * (u3 / v3)) *
          (z1 * v1 * (u1 / v1) * Real.log (z1 * v1) + z2 * v2 * (u2 / v2) * Real.log (z2 * v2) +
            z3 * v3 * (u3 / v3) * Real.log (z3 * v3)) +
        2 * (z1 * v1 * (u1 / v1) + z2 * v2 * (u2 / v2) + z3 * v3 * (u3 / v3)) ^ 2 *
          Real.log (z1 * v1 + z2 * v2 + z3 * v3) +
        (z1 * v1 * (u1 / v1) + z2 * v2 * (u2 / v2) + z3 * v3 * (u3 / v3)) ^ 2) := by
  have c1 : z1 * v1 * (u1 / v1) = z1 * u1 := by field_simp
  have c2 : z2 * v2 * (u2 / v2) = z2 * u2 := by field_simp
  have c3 : z3 * v3 * (u3 / v3) = z3 * u3 := by field_simp
  rw [c1, c2, c3]
  have d : ∀ c v u : ℝ, v ≠ 0 → c * v * (u / v) ^ 2 = c * u ^ 2 / v := fun c v u hv => by
    field_simp
  have e1 : ((a * X1 + (1 - a) * Y1) * v1 - (z1 * v1 + z2 * v2 + z3 * v3) * (z1 * v1)) * (u1 / v1) ^ 2
      = (a * X1 + (1 - a) * Y1) * u1 ^ 2 / v1 - (z1 * v1 + z2 * v2 + z3 * v3) * (z1 * u1 ^ 2 / v1) := by
    rw [sub_mul, d _ _ _ h1, mul_assoc, d _ _ _ h1]
  have e2 : ((a * X2 + (1 - a) * Y2) * v2 - (z1 * v1 + z2 * v2 + z3 * v3) * (z2 * v2)) * (u2 / v2) ^ 2
      = (a * X2 + (1 - a) * Y2) * u2 ^ 2 / v2 - (z1 * v1 + z2 * v2 + z3 * v3) * (z2 * u2 ^ 2 / v2) := by
    rw [sub_mul, d _ _ _ h2, mul_assoc, d _ _ _ h2]
  have e3 : ((a * X3 + (1 - a) * Y3) * v3 - (z1 * v1 + z2 * v2 + z3 * v3) * (z3 * v3)) * (u3 / v3) ^ 2
      = (a * X3 + (1 - a) * Y3) * u3 ^ 2 / v3 - (z1 * v1 + z2 * v2 + z3 * v3) * (z3 * u3 ^ 2 / v3) := by
    rw [sub_mul, d _ _ _ h3, mul_assoc, d _ _ _ h3]
  rw [e1, e2, e3]
  ring

lemma psi2_nonpos {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {X Y : Fin n → ℝ} (G : Good X Y)
    {i j k : Fin n} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hS : ∀ l, l ≠ i → l ≠ j → l ≠ k → X l = 0)
    (hXi : X i ≠ 0) (hXj : X j ≠ 0) (hXk : X k ≠ 0)
    (u : Fin n → ℝ) (hXu : ∑ l, X l * u l = 0) (hYu : ∑ l, Y l * u l = 0) (s : ℝ)
    (hvi : 0 < 1 + s * u i) (hvj : 0 < 1 + s * u j) (hvk : 0 < 1 + s * u k) :
    psi2 a X Y u s ≤ 0 := by
  have S3 : ∀ f : Fin n → ℝ, (∀ l, X l = 0 → f l = 0) → ∑ l, f l = f i + f j + f k :=
    fun f hf => sum3 hij hik hjk (fun l h1 h2 h3 => hf l (hS l h1 h2 h3))
  have hY0 : ∀ l, X l = 0 → Y l = 0 := fun l h => (G.iff l).1 h
  have hz0 : ∀ l, X l = 0 → zz a X Y l = 0 := fun l h => zz_zero ha0 h
  have hXv : ∑ l, X l * (1 + s * u l) = 1 := by
    have : ∀ l, X l * (1 + s * u l) = X l + s * (X l * u l) := fun l => by ring
    simp only [this, Finset.sum_add_distrib, ← Finset.mul_sum, hXu, G.xs]; ring
  have hYv : ∑ l, Y l * (1 + s * u l) = 1 := by
    have : ∀ l, Y l * (1 + s * u l) = Y l + s * (Y l * u l) := fun l => by ring
    simp only [this, Finset.sum_add_distrib, ← Finset.mul_sum, hYu, G.ys]; ring
  rw [S3 _ (fun l h => by simp [h])] at hXv
  rw [S3 _ (fun l h => by simp [hY0 l h])] at hYv
  rw [S3 _ (fun l h => by simp [h])] at hXu
  rw [S3 _ (fun l h => by simp [hY0 l h])] at hYu
  have hD2X : D2 u X s = -(X i * u i ^ 2 / (1 + s * u i)) + -(X j * u j ^ 2 / (1 + s * u j))
      + -(X k * u k ^ 2 / (1 + s * u k)) := by
    unfold D2; exact S3 _ (fun l h => by simp [h])
  have hD2Y : D2 u Y s = -(Y i * u i ^ 2 / (1 + s * u i)) + -(Y j * u j ^ 2 / (1 + s * u j))
      + -(Y k * u k ^ 2 / (1 + s * u k)) := by
    unfold D2; exact S3 _ (fun l h => by simp [hY0 l h])
  have hD2z : D2 u (zz a X Y) s = -(zz a X Y i * u i ^ 2 / (1 + s * u i))
      + -(zz a X Y j * u j ^ 2 / (1 + s * u j)) + -(zz a X Y k * u k ^ 2 / (1 + s * u k)) := by
    unfold D2; exact S3 _ (fun l h => by simp [hz0 l h])
  have hD1z : D1 u (zz a X Y) s =
      zz a X Y i * u i * (-Real.log (zz a X Y i * (1 + s * u i)) - 1)
      + zz a X Y j * u j * (-Real.log (zz a X Y j * (1 + s * u j)) - 1)
      + zz a X Y k * u k * (-Real.log (zz a X Y k * (1 + s * u k)) - 1) := by
    unfold D1; exact S3 _ (fun l h => by simp [hz0 l h])
  have hKf : Kf u (zz a X Y) s = zz a X Y i * (1 + s * u i) + zz a X Y j * (1 + s * u j)
      + zz a X Y k * (1 + s * u k) := by
    unfold Kf; exact S3 _ (fun l h => by simp [hz0 l h])
  have hk : ∑ l, zz a X Y l * u l = zz a X Y i * u i + zz a X Y j * u j + zz a X Y k * u k :=
    S3 _ (fun l h => by simp [hz0 l h])
  have hc : ∀ c v w : ℝ, v ≠ 0 → c * v * (w / v) = c * w := fun c v w hv => by field_simp
  have hQ := Q3 (w1 := (a * X i + (1 - a) * Y i) * (1 + s * u i))
    (w2 := (a * X j + (1 - a) * Y j) * (1 + s * u j))
    (w3 := (a * X k + (1 - a) * Y k) * (1 + s * u k))
    (z1 := zz a X Y i * (1 + s * u i)) (z2 := zz a X Y j * (1 + s * u j))
    (z3 := zz a X Y k * (1 + s * u k))
    (t1 := u i / (1 + s * u i)) (t2 := u j / (1 + s * u j)) (t3 := u k / (1 + s * u k))
    (mul_pos (zz_pos G hXi) hvi) (mul_pos (zz_pos G hXj) hvj) (mul_pos (zz_pos G hXk) hvk)
    (mul_le_mul_of_nonneg_right (zz_le ha0 ha1 G i) hvi.le)
    (mul_le_mul_of_nonneg_right (zz_le ha0 ha1 G j) hvj.le)
    (mul_le_mul_of_nonneg_right (zz_le ha0 ha1 G k) hvk.le)
    (by linear_combination a * hXv + (1 - a) * hYv)
    (by rw [hc _ _ _ hvi.ne', hc _ _ _ hvj.ne', hc _ _ _ hvk.ne']
        linear_combination a * hXu + (1 - a) * hYu)
  unfold psi2
  rw [hD2X, hD2Y, hD2z, hD1z, hKf, hk]
  refine le_trans (le_of_eq ?_) (neg_nonpos.2 hQ)
  exact psi2_ident a (X i) (X j) (X k) (Y i) (Y j) (Y k) (zz a X Y i) (zz a X Y j) (zz a X Y k)
    (u i) (u j) (u k) _ _ _ hvi.ne' hvj.ne' hvk.ne'

lemma interp_nonneg {s1 s2 s u : ℝ} (h1 : 0 ≤ 1 + s1 * u) (h2 : 0 ≤ 1 + (-s2) * u)
    (hs : s ∈ Set.Icc (-s2) s1) : 0 ≤ 1 + s * u := by
  rcases le_total 0 u with hu | hu
  · nlinarith [mul_le_mul_of_nonneg_right hs.1 hu]
  · nlinarith [mul_le_mul_of_nonpos_right hs.2 hu]

lemma interp_pos {s1 s2 s u : ℝ} (h1 : 0 ≤ 1 + s1 * u) (h2 : 0 ≤ 1 + (-s2) * u)
    (hs : s ∈ Set.Ioo (-s2) s1) : 0 < 1 + s * u := by
  rcases lt_trichotomy u 0 with hu | hu | hu
  · have := mul_lt_mul_of_neg_right hs.2 hu; linarith
  · rw [hu]; norm_num
  · have := mul_lt_mul_of_pos_right hs.1 hu; linarith

lemma KK_scale {a : ℝ} {X Y : Fin n → ℝ} (G : Good X Y) (v : Fin n → ℝ) (hv : ∀ i, 0 ≤ v i) :
    KK a (fun l => X l * v l) (fun l => Y l * v l) = ∑ l, zz a X Y l * v l := by
  unfold KK
  exact Finset.sum_congr rfl (fun l _ => zz_mul (G.x0 l) (G.y0 l) (hv l))

lemma partII {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {X Y : Fin n → ℝ} (G : Good X Y)
    (hcard : (supp X).card = 3)
    (IH : ∀ X' Y' : Fin n → ℝ, Good X' Y' → (supp X').card < 3 → 0 ≤ Phi a X' Y') :
    0 ≤ Phi a X Y := by
  obtain ⟨i, j, k, hij, hik, hjk, hSeq⟩ := Finset.card_eq_three.1 hcard
  have hmem : ∀ l, X l ≠ 0 ↔ (l = i ∨ l = j ∨ l = k) := by
    intro l; rw [← mem_supp, hSeq]; simp
  have hS : ∀ l, l ≠ i → l ≠ j → l ≠ k → X l = 0 := by
    intro l h1 h2 h3; by_contra h
    rcases (hmem l).1 h with h' | h' | h' <;> contradiction
  have hXi : X i ≠ 0 := (hmem i).2 (Or.inl rfl)
  have hXj : X j ≠ 0 := (hmem j).2 (Or.inr (Or.inl rfl))
  have hXk : X k ≠ 0 := (hmem k).2 (Or.inr (Or.inr rfl))
  obtain ⟨u, hu_off, ⟨i0, hi0, hu0⟩, hcons⟩ :=
    kernel_exists (supp X) 3 hcard ![X, Y, 0] 2 (by simp)
  have hXu : ∑ l, X l * u l = 0 := by simpa using hcons 0
  have hYu : ∑ l, Y l * u l = 0 := by simpa using hcons 1
  have hu0' : ∀ l, X l = 0 → u l = 0 :=
    fun l h => hu_off l (by rw [mem_supp]; exact fun h' => h' h)
  obtain ⟨s1, s2, hs1, hs2, hv1, hv2, hc1, hc2⟩ := descent G u hu0' ⟨i0, mem_supp.1 hi0, hu0⟩ hXu
  have hvD : ∀ s ∈ Set.Icc (-s2) s1, ∀ l, 0 ≤ 1 + s * u l :=
    fun s hs l => interp_nonneg (hv1 l) (hv2 l) hs
  have hGD : ∀ s ∈ Set.Icc (-s2) s1,
      Good (fun l => X l * (1 + s * u l)) (fun l => Y l * (1 + s * u l)) :=
    fun s hs => scaled_good G u s (hvD s hs) hXu hYu
  have hpsi : ∀ s ∈ Set.Icc (-s2) s1, psi a X Y u s =
      Phi a (fun l => X l * (1 + s * u l)) (fun l => Y l * (1 + s * u l)) :=
    fun s hs => (Phi_scale G (fun l => 1 + s * u l) (hvD s hs)).symm
  have hKD : ∀ s ∈ Set.Icc (-s2) s1, 0 < Kf u (zz a X Y) s := by
    intro s hs
    have := KK_pos (a := a) (hGD s hs)
    rw [KK_scale G (fun l => 1 + s * u l) (hvD s hs)] at this
    exact this
  have hcont : ContinuousOn (psi a X Y u) (Set.Icc (-s2) s1) := by
    intro s hs
    apply ContinuousAt.continuousWithinAt
    have hK := (hKD s hs).ne'
    have c1 := continuous_E1 u X
    have c2 := continuous_E1 u Y
    have c3 := continuous_E1 u (zz a X Y)
    have cK := continuous_Kf u (zz a X Y)
    unfold psi
    exact (((continuous_const.mul c1).add (continuous_const.mul c2)).sub (cK.mul c3)).continuousAt.sub
      ((cK.pow 2).continuousAt.mul (cK.continuousAt.log hK))
  have hconc : ConcaveOn ℝ (Set.Icc (-s2) s1) (psi a X Y u) := by
    refine concaveOn_of_hasDerivWithinAt2_nonpos (convex_Icc _ _) hcont
      (f' := psi1 a X Y u) (f'' := psi2 a X Y u) ?_ ?_ ?_
    all_goals
      intro s hs
      rw [interior_Icc] at hs
      have hvpos : ∀ l, 0 < 1 + s * u l := fun l => interp_pos (hv1 l) (hv2 l) hs
      have hsD : s ∈ Set.Icc (-s2) s1 := Set.Ioo_subset_Icc_self hs
      have cond : ∀ P : Fin n → ℝ, ∀ l, P l = 0 ∨ P l * (1 + s * u l) ≠ 0 := by
        intro P l
        by_cases h : P l = 0
        · exact Or.inl h
        · exact Or.inr (mul_ne_zero h (hvpos l).ne')
    · exact (hasDerivAt_psi a X Y u s (cond X) (cond Y) (cond _) (hKD s hsD).ne').hasDerivWithinAt
    · exact (hasDerivAt_psi1 a X Y u s (cond X) (cond Y) (cond _) (hKD s hsD).ne').hasDerivWithinAt
    · exact psi2_nonpos ha0 ha1 G hij hik hjk hS hXi hXj hXk u hXu hYu s (hvpos i) (hvpos j)
        (hvpos k)
  have hs1D : s1 ∈ Set.Icc (-s2) s1 := ⟨by linarith, le_rfl⟩
  have hs2D : -s2 ∈ Set.Icc (-s2) s1 := ⟨le_rfl, by linarith⟩
  have h0D : (0 : ℝ) ∈ Set.Icc (-s2) s1 := ⟨by linarith, hs1.le⟩
  have e1 := IH _ _ (hGD s1 hs1D) (hcard ▸ hc1)
  have e2 := IH _ _ (hGD (-s2) hs2D) (hcard ▸ hc2)
  rw [← hpsi s1 hs1D] at e1
  rw [← hpsi (-s2) hs2D] at e2
  have h0 : psi a X Y u 0 = Phi a X Y := by
    rw [hpsi 0 h0D]; simp only [zero_mul, add_zero, mul_one]
  have hsum : 0 < s1 + s2 := by linarith
  have := hconc.2 hs1D hs2D (div_nonneg hs2.le hsum.le) (div_nonneg hs1.le hsum.le)
    (by field_simp; ring)
  simp only [smul_eq_mul] at this
  rw [show s2 / (s1 + s2) * s1 + s1 / (s1 + s2) * -s2 = 0 by field_simp; ring, h0] at this
  have p1 := mul_nonneg (div_nonneg hs2.le hsum.le) e1
  have p2 := mul_nonneg (div_nonneg hs1.le hsum.le) e2
  linarith

lemma partI {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {X Y : Fin n → ℝ} (G : Good X Y)
    (hcard : 4 ≤ (supp X).card)
    (IH : ∀ X' Y' : Fin n → ℝ, Good X' Y' → (supp X').card < (supp X).card → 0 ≤ Phi a X' Y') :
    0 ≤ Phi a X Y := by
  obtain ⟨t, hts, htc⟩ := Finset.exists_subset_card_eq hcard
  obtain ⟨u, hu_off, ⟨i0, hi0, hu0⟩, hcons⟩ :=
    kernel_exists t 4 htc ![X, Y, zz a X Y, 0] 3 (by simp)
  have hXu : ∑ l, X l * u l = 0 := by simpa using hcons 0
  have hYu : ∑ l, Y l * u l = 0 := by simpa using hcons 1
  have hzu : ∑ l, zz a X Y l * u l = 0 := by simpa using hcons 2
  have hu0' : ∀ l, X l = 0 → u l = 0 :=
    fun l h => hu_off l (fun hl => (mem_supp.1 (hts hl)) h)
  obtain ⟨s1, s2, hs1, hs2, hv1, hv2, hc1, hc2⟩ :=
    descent G u hu0' ⟨i0, mem_supp.1 (hts hi0), hu0⟩ hXu
  have hK : ∀ s : ℝ, ∑ l, zz a X Y l * (1 + s * u l) = KK a X Y := by
    intro s
    have : ∀ l, zz a X Y l * (1 + s * u l) = zz a X Y l + s * (zz a X Y l * u l) :=
      fun l => by ring
    simp only [this, Finset.sum_add_distrib, ← Finset.mul_sum, hzu]
    unfold KK; ring
  have hsum : 0 < s1 + s2 := by linarith
  have hconc := partI_concave ha0 ha1 G (fun l => 1 + s1 * u l) (fun l => 1 + (-s2) * u l)
    hv1 hv2 (hK s1) (hK (-s2)) (s2 / (s1 + s2)) (div_nonneg hs2.le hsum.le)
    (by rw [div_le_one hsum]; linarith) (fun l => by field_simp; ring)
  have e1 := IH _ _ (scaled_good G u s1 hv1 hXu hYu) hc1
  have e2 := IH _ _ (scaled_good G u (-s2) hv2 hXu hYu) hc2
  have p1 := mul_nonneg (div_nonneg hs2.le hsum.le) e1
  have p2 := mul_nonneg (show 0 ≤ 1 - s2 / (s1 + s2) by rw [sub_nonneg, div_le_one hsum]; linarith) e2
  linarith

lemma case2 {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {X Y : Fin n → ℝ} (G : Good X Y)
    (hcard : (supp X).card = 2) : 0 ≤ Phi a X Y := by
  obtain ⟨i, j, hij, hSeq⟩ := Finset.card_eq_two.1 hcard
  have hmem : ∀ l, X l ≠ 0 ↔ (l = i ∨ l = j) := by
    intro l; rw [← mem_supp, hSeq]; simp
  have hS : ∀ l, l ≠ i ∧ l ≠ j → X l = 0 := by
    intro l hl; by_contra h
    rcases (hmem l).1 h with h' | h'
    · exact hl.1 h'
    · exact hl.2 h'
  have S2 : ∀ f : Fin n → ℝ, (∀ l, X l = 0 → f l = 0) → ∑ l, f l = f i + f j :=
    fun f hf => Fintype.sum_eq_add i j hij (fun l hl => hf l (hS l hl))
  have hY0 : ∀ l, X l = 0 → Y l = 0 := fun l h => (G.iff l).1 h
  have hXi : X i ≠ 0 := (hmem i).2 (Or.inl rfl)
  have hXj : X j ≠ 0 := (hmem j).2 (Or.inr rfl)
  have hYi : Y i ≠ 0 := fun h => hXi ((G.iff i).2 h)
  have hYj : Y j ≠ 0 := fun h => hXj ((G.iff j).2 h)
  have pXi : 0 < X i := lt_of_le_of_ne (G.x0 i) (Ne.symm hXi)
  have pXj : 0 < X j := lt_of_le_of_ne (G.x0 j) (Ne.symm hXj)
  have pYi : 0 < Y i := lt_of_le_of_ne (G.y0 i) (Ne.symm hYi)
  have pYj : 0 < Y j := lt_of_le_of_ne (G.y0 j) (Ne.symm hYj)
  have hXs : X i + X j = 1 := by rw [← S2 X (fun l h => h)]; exact G.xs
  have hYs : Y i + Y j = 1 := by rw [← S2 Y hY0]; exact G.ys
  have h1 : ∑ l, Real.negMulLog (X l) = Real.negMulLog (X i) + Real.negMulLog (X j) :=
    S2 _ (fun l h => by simp [h])
  have h2 : ∑ l, Real.negMulLog (Y l) = Real.negMulLog (Y i) + Real.negMulLog (Y j) :=
    S2 _ (fun l h => by simp [hY0 l h])
  have h3 : ∑ l, zz a X Y l = zz a X Y i + zz a X Y j := S2 _ (fun l h => zz_zero ha0 h)
  have h4 : ∑ l, Real.negMulLog (zz a X Y l) =
      Real.negMulLog (zz a X Y i) + Real.negMulLog (zz a X Y j) :=
    S2 _ (fun l h => by simp [zz_zero ha0 h])
  unfold Phi KK
  rw [h1, h2, h3, h4]
  unfold zz
  rw [show X j = 1 - X i by linarith, show Y j = 1 - Y i by linarith]
  have := two_point ha0 ha1 pXi (by linarith) pYi (by linarith)
  linarith

lemma case1 {a : ℝ} {X Y : Fin n → ℝ} (G : Good X Y) (hcard : (supp X).card = 1) :
    0 ≤ Phi a X Y := by
  obtain ⟨i, hSeq⟩ := Finset.card_eq_one.1 hcard
  have hS : ∀ l, l ≠ i → X l = 0 := by
    intro l hl; by_contra h
    have : l ∈ supp X := mem_supp.2 h
    rw [hSeq, Finset.mem_singleton] at this; exact hl this
  have hY : ∀ l, l ≠ i → Y l = 0 := fun l hl => (G.iff l).1 (hS l hl)
  have hXi : X i = 1 := by
    rw [← G.xs, Finset.sum_eq_single i (fun l _ hl => hS l hl) (by simp)]
  have hYi : Y i = 1 := by
    rw [← G.ys, Finset.sum_eq_single i (fun l _ hl => hY l hl) (by simp)]
  have hXY : Y = X := by
    funext l
    by_cases hl : l = i
    · rw [hl, hXi, hYi]
    · rw [hS l hl, hY l hl]
  rw [hXY, Phi_self G.x0 G.xs]

theorem good_nonneg {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) :
    ∀ (m : ℕ) (X Y : Fin n → ℝ), Good X Y → (supp X).card = m → 0 ≤ Phi a X Y := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m IH =>
    intro X Y G hm
    have IH' : ∀ X' Y' : Fin n → ℝ, Good X' Y' → (supp X').card < m → 0 ≤ Phi a X' Y' :=
      fun X' Y' G' h => IH _ h X' Y' G' rfl
    rcases (show m = 0 ∨ m = 1 ∨ m = 2 ∨ m = 3 ∨ 4 ≤ m by omega) with h | h | h | h | h
    · exfalso
      obtain ⟨i, hi⟩ := exists_ne_zero G
      have : i ∈ supp X := mem_supp.2 hi
      rw [Finset.card_eq_zero.1 (hm.trans h)] at this
      simp at this
    · exact case1 G (hm.trans h)
    · exact case2 ha0 ha1 G (hm.trans h)
    · exact partII ha0 ha1 G (hm.trans h) (fun X' Y' G' h' => IH' X' Y' G' (by omega))
    · exact partI ha0 ha1 G (by omega) (fun X' Y' G' h' => IH' X' Y' G' (by omega))

/-! ## Part 0: reduction to positive entries by continuity -/

theorem phi_nonneg {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (X Y : Fin n → ℝ) (hX0 : ∀ i, 0 ≤ X i)
    (hXs : ∑ i, X i = 1) (hY0 : ∀ i, 0 ≤ Y i) (hYs : ∑ i, Y i = 1) (hK : 0 < KK a X Y) :
    0 ≤ Phi a X Y := by
  have hn : (0 : ℝ) < n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h; simp at hXs
    · exact_mod_cast h
  let Xe : ℝ → Fin n → ℝ := fun e i => (1 - e) * X i + e / n
  let Ye : ℝ → Fin n → ℝ := fun e i => (1 - e) * Y i + e / n
  have Ge : ∀ e ∈ Set.Ioo (0 : ℝ) 1, Good (Xe e) (Ye e) := by
    intro e he
    have hp : ∀ (Z : Fin n → ℝ), (∀ i, 0 ≤ Z i) → ∀ i, 0 < (1 - e) * Z i + e / n :=
      fun Z hZ i => by
        have := mul_nonneg (by linarith [he.2] : (0 : ℝ) ≤ 1 - e) (hZ i)
        have := div_pos he.1 hn
        linarith
    have hs : ∀ (Z : Fin n → ℝ), ∑ i, Z i = 1 → ∑ i, ((1 - e) * Z i + e / n) = 1 := by
      intro Z hZ
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, hZ, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul]
      field_simp; ring
    exact {
      x0 := fun i => (hp X hX0 i).le
      y0 := fun i => (hp Y hY0 i).le
      xs := hs X hXs
      ys := hs Y hYs
      iff := fun i => ⟨fun h => absurd h (hp X hX0 i).ne', fun h => absurd h (hp Y hY0 i).ne'⟩ }
  have hpos : ∀ e ∈ Set.Ioo (0 : ℝ) 1, 0 ≤ Phi a (Xe e) (Ye e) :=
    fun e he => good_nonneg ha0 ha1 _ _ _ (Ge e he) rfl
  have h0X : Xe 0 = X := by funext i; simp [Xe]
  have h0Y : Ye 0 = Y := by funext i; simp [Ye]
  have crp : ∀ q : ℝ, 0 ≤ q → Continuous (fun x : ℝ => x ^ q) :=
    fun q hq => continuous_iff_continuousAt.2 (fun x => Real.continuousAt_rpow_const x q (Or.inr hq))
  have cX : ∀ i, Continuous (fun e => Xe e i) := fun i => by simp only [Xe]; fun_prop
  have cY : ∀ i, Continuous (fun e => Ye e i) := fun i => by simp only [Ye]; fun_prop
  have cz : ∀ i, Continuous (fun e => zz a (Xe e) (Ye e) i) :=
    fun i => ((crp a ha0.le).comp (cX i)).mul ((crp (1 - a) (by linarith)).comp (cY i))
  have cK : Continuous (fun e => KK a (Xe e) (Ye e)) :=
    continuous_finsetSum _ (fun i _ => cz i)
  have cE : ∀ (f : ℝ → Fin n → ℝ), (∀ i, Continuous fun e => f e i) →
      Continuous (fun e => ∑ i, Real.negMulLog (f e i)) :=
    fun f hf => continuous_finsetSum _ (fun i _ => Real.continuous_negMulLog.comp (hf i))
  have hK0 : KK a (Xe 0) (Ye 0) ≠ 0 := by rw [h0X, h0Y]; exact hK.ne'
  have hcont : ContinuousAt (fun e => Phi a (Xe e) (Ye e)) 0 := by
    unfold Phi
    exact ((((continuous_const.mul (cE Xe cX)).add (continuous_const.mul (cE Ye cY))).sub
      (cK.mul (cE (fun e => zz a (Xe e) (Ye e)) cz))).continuousAt).sub
      ((cK.pow 2).continuousAt.mul (cK.continuousAt.log hK0))
  have hlim := hcont.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
  have := ge_of_tendsto hlim (Filter.mem_of_superset (Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num))
    (fun e he => hpos e he))
  simp only [h0X, h0Y] at this
  exact this

lemma ent_div (z : Fin n → ℝ) (K : ℝ) (hK : 0 < K) (hz : ∑ i, z i = K) :
    K ^ 2 * ∑ i, Real.negMulLog (z i / K) = K * ∑ i, Real.negMulLog (z i) + K ^ 2 * Real.log K := by
  have e : ∀ i, Real.negMulLog (z i / K) = K⁻¹ * Real.negMulLog (z i) + z i * (K⁻¹ * Real.log K) := by
    intro i
    rw [div_eq_mul_inv, Real.negMulLog_mul]
    simp only [Real.negMulLog, Real.log_inv]
    ring
  simp only [e, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul, hz]
  field_simp

end General

end Friedan

theorem Friedan.main_proof :
    ∀ (n : ℕ) (X Y : Fin n → ℝ), (∀ i, 0 ≤ X i) → ∑ i, X i = 1 → (∀ i, 0 ≤ Y i) → ∑ i, Y i = 1 →
      ∀ α : ℝ, 0 ≤ α → α ≤ 1 →
        0 < ∑ i, X i ^ α * Y i ^ (1 - α) →
        (∑ i, X i ^ α * Y i ^ (1 - α)) ^ 2 *
            OMA.S_mo_138395.entropy
              (fun i => X i ^ α * Y i ^ (1 - α) / (∑ j, X j ^ α * Y j ^ (1 - α))) ≤
          α * OMA.S_mo_138395.entropy X + (1 - α) * OMA.S_mo_138395.entropy Y := by
  intro n X Y hX0 hXs hY0 hYs α h0 h1 hK
  unfold OMA.S_mo_138395.entropy
  rcases eq_or_lt_of_le h0 with h0' | h0'
  · subst h0'
    simp only [Real.rpow_zero, one_mul, sub_zero, Real.rpow_one]
    rw [hYs]
    simp
  rcases eq_or_lt_of_le h1 with h1' | h1'
  · subst h1'
    simp only [sub_self, Real.rpow_zero, mul_one, Real.rpow_one]
    rw [hXs]
    simp
  have hP := Friedan.phi_nonneg h0' h1' X Y hX0 hXs hY0 hYs hK
  unfold Friedan.Phi Friedan.KK Friedan.zz at hP
  rw [Friedan.ent_div _ _ hK rfl]
  linarith

/-- Friedan's inequality, exactly the statement `main` of Left to Solve `mo-138395`. -/
theorem OMA.S_mo_138395.main : OMA.S_mo_138395.MainStatement := Friedan.main_proof

end
