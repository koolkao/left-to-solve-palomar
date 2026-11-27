/-
Copyright 2026 Ming-Chih Kao. Licensed under the Apache License, Version 2.0;
see the LICENSE file at the root of this repository.
-/
module

public import FriedanMulti.R2Descent
public import FriedanMulti.R2Delta

/-! Port: copied from `FriedanMulti/R2Main.lean` of github.com/koolkao/friedan-entropy-inequality (commit 0f4ba65dc126f59e7158fbcbc01548baa78cf21d, Lean v4.33.1, Mathlib 0df444a) and put into the module system (`module` header, `public import`, public section). No other change was needed for Lean v4.36.0 / Mathlib fc4f59e. -/

@[expose] public section

/-!
# Theorem R2: Friedan's inequality for the Rényi entropy on two points

For `0 < g < 1` or `1 < g ≤ 2 log 2`, all `m`, probability vectors `X j` on `Fin 2` and weights `a`:
`K² H_g(Z) ≤ ∑ aⱼ H_g(Xⱼ)`, `H_g(P) = log(∑ Pᵢ^g)/(1-g)`.
-/

open Real Finset Filter Topology Friedan

namespace FriedanMulti

/-- Rényi entropy of order `g` (natural logarithm). -/
noncomputable def renyi (g : ℝ) {n : ℕ} (P : Fin n → ℝ) : ℝ := Real.log (∑ i, P i ^ g) / (1 - g)

/-- Theorem R2 (binary Rényi version of Friedan's inequality, all `m`), as a proposition. -/
def TheoremR2 : Prop :=
  ∀ (m : ℕ) (X : Fin m → Fin 2 → ℝ), (∀ j i, 0 ≤ X j i) → (∀ j, ∑ i, X j i = 1) →
    ∀ a : Fin m → ℝ, (∀ j, 0 ≤ a j) → ∑ j, a j = 1 →
    ∀ g : ℝ, 0 < g → g ≠ 1 → g ≤ 2 * Real.log 2 →
      0 < ∑ i, ∏ j, X j i ^ a j →
      (∑ i, ∏ j, X j i ^ a j) ^ 2 *
          renyi g (fun i => (∏ j, X j i ^ a j) / ∑ k, ∏ j, X j k ^ a j) ≤
        ∑ j, a j * renyi g (X j)

end FriedanMulti

namespace FriedanR2

open FriedanMulti

variable {m : ℕ}

lemma exp_lp (u : ℝ) : Real.exp (lp u) = Real.exp (u / 2) + Real.exp (-u / 2) := by
  unfold Friedan.lp; exact Real.exp_log (den_pos u)

lemma renyi_sg (g t : ℝ) :
    Real.log (sg t ^ g + (1 - sg t) ^ g) / (1 - g) = hg g t := by
  rw [Real.rpow_def_of_pos (sg_pos t), Real.rpow_def_of_pos (by linarith [sg_lt_one t]), log_sg,
    log_one_sub_sg]
  have e : Real.exp ((t / 2 - lp t) * g) + Real.exp ((-t / 2 - lp t) * g) =
      Real.exp (-(g * lp t)) * Real.exp (lp (g * t)) := by
    rw [exp_lp, mul_add, ← Real.exp_add, ← Real.exp_add]
    congr 1 <;> congr 1 <;> ring
  rw [e, Real.log_mul (Real.exp_pos _).ne' (Real.exp_pos _).ne', Real.log_exp, Real.log_exp]
  unfold hg
  ring

/-- The key inequality in logits, for arbitrary real logits and weights `a ≥ 0` summing to `1`. -/
theorem omega_le {g : ℝ} (hg0 : 0 < g) (hg1' : g ≠ 1) (hgc : g ≤ cc) (a A : Fin m → ℝ)
    (ha0 : ∀ j, 0 ≤ a j) (has : ∑ j, a j = 1) :
    Omg g (∑ j, a j * A j) ≤ QQs (hg g) univ a A := by
  set s := univ.filter (fun j => a j ≠ 0) with hs
  have hsum : ∀ f : Fin m → ℝ, ∑ j ∈ s, a j * f j = ∑ j, a j * f j := by
    intro f
    rw [hs, Finset.sum_filter_of_ne]
    intro j _ h
    exact left_ne_zero_of_mul h
  have hsa : ∑ j ∈ s, a j = 1 := by
    have := hsum (fun _ => 1); simp only [mul_one] at this; rw [this, has]
  have hapos : ∀ j ∈ s, 0 < a j := by
    intro j hj
    rw [hs, Finset.mem_filter] at hj
    exact lt_of_le_of_ne (ha0 j) (Ne.symm hj.2)
  set B : Fin m → ℝ := fun j => |A j|
  have hB0 : ∀ j ∈ s, 0 ≤ B j := fun j _ => abs_nonneg _
  have hdesc := descent (hg g) (hg1 g) (hd_hg g) (hg_anti hg0 hg1')
    (fun A B hB hAB => Dg_nonneg hg0 hg1' hgc hB hAB) s.card s rfl a B hapos hsa hB0
  have hw : |∑ j, a j * A j| ≤ ∑ j ∈ s, a j * B j := by
    rw [hsum]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [abs_mul, abs_of_nonneg (ha0 j)]
  have hmono := Omg_mono (g := g) (fun A hA => Dg_nonneg hg0 hg1' hgc le_rfl hA)
  have h1 : Omg g (∑ j, a j * A j) ≤ Omg g (∑ j ∈ s, a j * B j) := by
    rw [← Omg_abs]
    exact hmono (Set.mem_Ici.2 (abs_nonneg (∑ j, a j * A j)))
      (Set.mem_Ici.2 ((abs_nonneg _).trans hw)) hw
  have h2 : QQs (hg g) s a B = QQs (hg g) univ a A := by
    unfold QQs
    rw [hsum (fun j => hg g (B j)), hsum (fun j => lp (B j))]
    simp only [B, hg_abs, lp_abs]
  calc Omg g (∑ j, a j * A j) ≤ Omg g (∑ j ∈ s, a j * B j) := h1
    _ ≤ QQs (hg g) s a B := hdesc
    _ = QQs (hg g) univ a A := h2

/-- Positive case. -/
theorem pos_case_R2 (X : Fin m → Fin 2 → ℝ) (hX : ∀ j i, 0 < X j i) (hXs : ∀ j, ∑ i, X j i = 1)
    (a : Fin m → ℝ) (ha0 : ∀ j, 0 ≤ a j) (has : ∑ j, a j = 1) {g : ℝ} (hg0 : 0 < g) (hg1' : g ≠ 1)
    (hgc : g ≤ cc) :
    (∑ i, ∏ j, X j i ^ a j) ^ 2 *
        renyi g (fun i => (∏ j, X j i ^ a j) / ∑ k, ∏ j, X j k ^ a j) ≤
      ∑ j, a j * renyi g (X j) := by
  have hX1 : ∀ j, X j 1 = 1 - X j 0 := by
    intro j; have := hXs j; rw [Fin.sum_univ_two] at this; linarith
  have hX0lt : ∀ j, X j 0 < 1 := by intro j; have := hX j 1; rw [hX1] at this; linarith
  let A : Fin m → ℝ := fun j => Real.log (X j 0) - Real.log (1 - X j 0)
  have hsg : ∀ j, sg (A j) = X j 0 := fun j => sg_logit (hX j 0) (hX0lt j)
  have lx : ∀ j, Real.log (X j 0) = A j / 2 - lp (A j) := fun j => by rw [← log_sg, hsg]
  have lx' : ∀ j, Real.log (X j 1) = -A j / 2 - lp (A j) := fun j => by
    rw [hX1, ← log_one_sub_sg, hsg]
  set w := ∑ j, a j * A j with hw
  set M := ∑ j, a j * lp (A j) with hM
  have hz0 : ∏ j, X j 0 ^ a j = Real.exp (w / 2 - M) := by
    have e : w / 2 - M = ∑ j, (A j / 2 - lp (A j)) * a j := by
      rw [hw, hM, Finset.sum_div, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun j _ => by ring)
    rw [e, Real.exp_sum]
    refine Finset.prod_congr rfl (fun j _ => ?_)
    rw [Real.rpow_def_of_pos (hX j 0), lx]
  have hz1 : ∏ j, X j 1 ^ a j = Real.exp (-w / 2 - M) := by
    have e : -w / 2 - M = ∑ j, (-A j / 2 - lp (A j)) * a j := by
      rw [hw, hM, neg_div, Finset.sum_div, ← Finset.sum_neg_distrib, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun j _ => by ring)
    rw [e, Real.exp_sum]
    refine Finset.prod_congr rfl (fun j _ => ?_)
    rw [Real.rpow_def_of_pos (hX j 1), lx']
  have hK : ∑ i, ∏ j, X j i ^ a j = Real.exp (lp w - M) := by
    rw [Fin.sum_univ_two, hz0, hz1, Real.exp_sub, Real.exp_sub, Real.exp_sub, exp_lp, add_div]
  have hZ0 : Real.exp (w / 2 - M) / Real.exp (lp w - M) = sg w := by
    rw [← Real.exp_sub, sg_exp]; congr 1; ring
  have hZ1 : Real.exp (-w / 2 - M) / Real.exp (lp w - M) = 1 - sg w := by
    rw [← Real.exp_sub, one_sub_sg_exp]; congr 1; ring
  have hL : (∑ i, ∏ j, X j i ^ a j) ^ 2 *
      renyi g (fun i => (∏ j, X j i ^ a j) / ∑ k, ∏ j, X j k ^ a j) =
      Real.exp (2 * (lp w - M)) * hg g w := by
    rw [hK]
    unfold renyi
    rw [Fin.sum_univ_two]
    simp only
    rw [hz0, hz1, hZ0, hZ1, renyi_sg, sq, ← Real.exp_add]
    ring_nf
  have hR : ∀ j, renyi g (X j) = hg g (A j) := by
    intro j
    unfold renyi
    rw [Fin.sum_univ_two, ← renyi_sg, hsg, hX1]
  rw [hL]
  simp only [hR]
  have key := omega_le hg0 hg1' hgc a A ha0 has
  unfold Omg QQs at key
  rw [← hw, ← hM] at key
  have e : Real.exp (2 * (lp w - M)) = Real.exp (2 * lp w) * Real.exp (-(2 * M)) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [e]
  have hpos := Real.exp_pos (-(2 * M))
  have e2 : (∑ j, a j * hg g (A j)) = (∑ j, a j * hg g (A j)) * Real.exp (2 * M) *
      Real.exp (-(2 * M)) := by
    rw [mul_assoc, ← Real.exp_add]; simp
  rw [e2]
  have := mul_le_mul_of_nonneg_right key hpos.le
  linarith

lemma pow_sum_pos {n : ℕ} {g : ℝ} (P : Fin n → ℝ) (hP0 : ∀ i, 0 ≤ P i)
    (hPs : ∑ i, P i = 1) : 0 < ∑ i, P i ^ g := by
  obtain ⟨i, hi⟩ : ∃ i, P i ≠ 0 := by
    by_contra h; push Not at h; simp [h] at hPs
  exact Finset.sum_pos' (fun j _ => Real.rpow_nonneg (hP0 j) g)
    ⟨i, Finset.mem_univ i, Real.rpow_pos_of_pos (lt_of_le_of_ne (hP0 i) (Ne.symm hi)) g⟩

/-- **Theorem R2.** -/
theorem theoremR2 : TheoremR2 := by
  intro m X hX0 hXs a ha0 has g hg0 hg1' hgc hK
  have hgc' : g ≤ cc := hgc
  let Xe : ℝ → Fin m → Fin 2 → ℝ := fun e j i => (1 - e) * X j i + e / 2
  have hpos : ∀ e ∈ Set.Ioo (0 : ℝ) 1, ∀ j i, 0 < Xe e j i := by
    intro e he j i
    have := mul_nonneg (by linarith [he.2] : (0 : ℝ) ≤ 1 - e) (hX0 j i)
    simp only [Xe]
    linarith [he.1]
  have hsum : ∀ e : ℝ, ∀ j, ∑ i, Xe e j i = 1 := by
    intro e j
    simp only [Xe]
    rw [Fin.sum_univ_two]
    have := hXs j
    rw [Fin.sum_univ_two] at this
    linear_combination (1 - e) * this
  let L : ℝ → ℝ := fun e => (∑ i, ∏ j, Xe e j i ^ a j) ^ 2 *
    renyi g (fun i => (∏ j, Xe e j i ^ a j) / ∑ k, ∏ j, Xe e j k ^ a j)
  let R : ℝ → ℝ := fun e => ∑ j, a j * renyi g (Xe e j)
  have hLR : ∀ e ∈ Set.Ioo (0 : ℝ) 1, L e ≤ R e :=
    fun e he => pos_case_R2 (Xe e) (hpos e he) (hsum e) a ha0 has hg0 hg1' hgc'
  have h0 : Xe 0 = X := by funext j i; simp [Xe]
  have crp : ∀ q : ℝ, 0 ≤ q → Continuous (fun x : ℝ => x ^ q) :=
    fun q hq => continuous_iff_continuousAt.2 (fun x => Real.continuousAt_rpow_const x q (Or.inr hq))
  have cX : ∀ j i, Continuous (fun e => Xe e j i) := fun j i => by simp only [Xe]; fun_prop
  have cz : ∀ i, Continuous (fun e => ∏ j, Xe e j i ^ a j) :=
    fun i => continuous_finsetProd _ (fun j _ => (crp (a j) (ha0 j)).comp (cX j i))
  have cK : Continuous (fun e => ∑ i, ∏ j, Xe e j i ^ a j) :=
    continuous_finsetSum _ (fun i _ => cz i)
  have hK0 : (∑ i, ∏ j, Xe 0 j i ^ a j) ≠ 0 := by rw [h0]; exact hK.ne'
  -- the normalized vector at `e = 0` is a probability vector
  have hZ0 : 0 < ∑ i, ((∏ j, Xe 0 j i ^ a j) / ∑ k, ∏ j, Xe 0 j k ^ a j) ^ g := by
    rw [h0]
    refine pow_sum_pos _ (fun i => div_nonneg
      (Finset.prod_nonneg (fun j _ => Real.rpow_nonneg (hX0 j i) _)) hK.le) ?_
    rw [← Finset.sum_div, div_self hK.ne']
  have cE : ContinuousAt
      (fun e => renyi g (fun i => (∏ j, Xe e j i ^ a j) / ∑ k, ∏ j, Xe e j k ^ a j)) 0 := by
    unfold renyi
    have : ContinuousAt (fun e => ∑ i, ((∏ j, Xe e j i ^ a j) / ∑ k, ∏ j, Xe e j k ^ a j) ^ g) 0 :=
      tendsto_finsetSum _ (fun i _ =>
        ((crp g hg0.le).continuousAt).comp ((cz i).continuousAt.div cK.continuousAt hK0))
    exact (this.log hZ0.ne').div_const _
  have cL : ContinuousAt L 0 := (cK.pow 2).continuousAt.mul cE
  have cR : ContinuousAt R 0 := by
    simp only [R, renyi]
    refine tendsto_finsetSum _ (fun j _ => ?_)
    have hpj : 0 < ∑ i, Xe 0 j i ^ g := by rw [h0]; exact pow_sum_pos _ (hX0 j) (hXs j)
    have : ContinuousAt (fun e => ∑ i, Xe e j i ^ g) 0 :=
      (continuous_finsetSum _ (fun i _ => (crp g hg0.le).comp (cX j i))).continuousAt
    exact continuousAt_const.mul ((this.log hpj.ne').div_const _)
  have hcont : ContinuousAt (fun e => R e - L e) 0 := cR.sub cL
  have hlim := hcont.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
  have := ge_of_tendsto hlim (Filter.mem_of_superset
    (Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)) (fun e he => sub_nonneg.2 (hLR e he)))
  have h' : L 0 ≤ R 0 := sub_nonneg.1 this
  simp only [L, R, h0] at h'
  exact h'

end FriedanR2

end
