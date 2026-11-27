/-
Copyright 2026 Ming-Chih Kao. Licensed under the Apache License, Version 2.0;
see the LICENSE file at the root of this repository.
-/
module

public import FriedanMulti.Calc
public import FriedanQ.Classical

/-! Port: copied from `quantum-lean/FriedanMulti/Induction.lean` of github.com/koolkao/friedan-entropy-inequality (commit 0f4ba65dc126f59e7158fbcbc01548baa78cf21d, Lean v4.36.0, Mathlib fc4f59e, physlib edc607c) and put into the module system (`module` header, `public import`, public section). The proofs are unchanged unless a comment marked `Port` says otherwise. -/

@[expose] public section

/-!
# Induction on the support of the weights

For log-probability vectors `x j` (`Sx (x j) = 1`) and weights `a` in the face `Face s` of the
simplex, `phi x a = gg (∑ aⱼ xⱼ) - ∑ aⱼ gg xⱼ ≤ 0`. Support 1: trivial; support 2: the two-distribution
theorem (`Friedan.main_proof`); support ≥ 3: a maximum of `phi + ε ∑ aⱼ²` on the compact face is on
the boundary (induction), because at an interior point the index lemma gives a direction along
which `phi + ε ∑ aⱼ²` is strictly convex.
-/

open Real Finset Filter Topology

namespace FriedanMulti

variable {n m : ℕ}

noncomputable def comb (x : Fin m → Fin n → ℝ) (a : Fin m → ℝ) : Fin n → ℝ :=
  fun i => ∑ j, a j * x j i

noncomputable def phi (x : Fin m → Fin n → ℝ) (a : Fin m → ℝ) : ℝ :=
  gg (comb x a) - ∑ j, a j * gg (x j)

def Face (s : Finset (Fin m)) : Set (Fin m → ℝ) :=
  {a | (∀ j, 0 ≤ a j) ∧ ∑ j, a j = 1 ∧ ∀ j, j ∉ s → a j = 0}

/-! ### Entropy in log coordinates and the two-distribution theorem -/

lemma ent_exp [NeZero n] (w : Fin n → ℝ) :
    Sx w ^ 2 * ∑ i, negMulLog (exp (w i) / Sx w) = gg w := by
  have hS := Sx_pos w
  have e : ∀ i, negMulLog (exp (w i) / Sx w) =
      Real.log (Sx w) * exp (w i) / Sx w - w i * exp (w i) / Sx w := by
    intro i
    rw [Real.negMulLog, Real.log_div (exp_pos _).ne' hS.ne', Real.log_exp]
    ring
  rw [Finset.sum_congr rfl (fun i _ => e i), Finset.sum_sub_distrib, ← Finset.sum_div,
    ← Finset.sum_div, ← Finset.mul_sum]
  unfold gg
  rw [show (∑ i, exp (w i)) = Sx w from rfl, show (∑ i, w i * exp (w i)) = Tx w from rfl]
  field_simp

lemma ent_one (w : Fin n → ℝ) (h : Sx w = 1) : ∑ i, negMulLog (exp (w i)) = gg w := by
  unfold gg Tx
  rw [h, Real.log_one, show (1 : ℝ) ^ 2 * 0 - 1 * ∑ i, w i * exp (w i) =
    ∑ i, -(w i * exp (w i)) by rw [Finset.sum_neg_distrib]; ring]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Real.negMulLog, Real.log_exp]
  ring

lemma two [NeZero n] (x1 x2 : Fin n → ℝ) (h1 : Sx x1 = 1) (h2 : Sx x2 = 1) (t : ℝ) (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) :
    gg (fun i => t * x1 i + (1 - t) * x2 i) ≤ t * gg x1 + (1 - t) * gg x2 := by
  have hz : ∀ i, exp (x1 i) ^ t * exp (x2 i) ^ (1 - t) = exp (t * x1 i + (1 - t) * x2 i) := by
    intro i
    rw [← Real.exp_mul, ← Real.exp_mul, ← Real.exp_add]
    congr 1
    ring
  have H := Friedan.main_proof n (fun i => exp (x1 i)) (fun i => exp (x2 i))
    (fun i => (exp_pos _).le) h1 (fun i => (exp_pos _).le) h2 t ht0 ht1
  simp only [hz] at H
  have H' := H (Sx_pos (fun i => t * x1 i + (1 - t) * x2 i))
  simp only [OMA.S_mo_138395.entropy] at H'
  have E := ent_exp (fun i => t * x1 i + (1 - t) * x2 i)
  simp only [Sx] at E
  rw [E, ent_one x1 h1, ent_one x2 h2] at H'
  exact H'

/-! ### Faces of the simplex -/

lemma face_sub_Icc (s : Finset (Fin m)) : Face s ⊆ Set.Icc (0 : Fin m → ℝ) 1 := by
  intro a ha
  refine ⟨fun j => ha.1 j, fun j => ?_⟩
  have := Finset.single_le_sum (f := a) (fun k _ => ha.1 k) (Finset.mem_univ j)
  rw [ha.2.1] at this
  exact this

lemma face_closed (s : Finset (Fin m)) : IsClosed (Face s) := by
  show IsClosed ({a : Fin m → ℝ | ∀ j, 0 ≤ a j} ∩
    ({a | ∑ j, a j = 1} ∩ {a | ∀ j, j ∉ s → a j = 0}))
  refine IsClosed.inter ?_ (IsClosed.inter ?_ ?_)
  · rw [Set.ofPred_forall]
    exact isClosed_iInter (fun j => isClosed_le continuous_const (continuous_apply j))
  · exact isClosed_eq (continuous_finsetSum _ (fun j _ => continuous_apply j)) continuous_const
  · rw [Set.ofPred_forall]
    refine isClosed_iInter (fun j => ?_)
    by_cases hj : j ∈ s
    · simp [hj]
    · simpa [hj] using isClosed_eq (continuous_apply j) (continuous_const : Continuous fun _ : Fin m → ℝ => (0 : ℝ))

lemma face_compact (s : Finset (Fin m)) : IsCompact (Face s) :=
  isCompact_Icc.of_isClosed_subset (face_closed s) (face_sub_Icc s)

lemma face_sq (s : Finset (Fin m)) {a : Fin m → ℝ} (ha : a ∈ Face s) : ∑ j, a j ^ 2 ≤ 1 := by
  calc ∑ j, a j ^ 2 ≤ ∑ j, a j := Finset.sum_le_sum (fun j _ => by
        have h1 := (face_sub_Icc s ha).2 j
        have h0 := ha.1 j
        simp only [Pi.one_apply] at h1
        nlinarith)
    _ = 1 := ha.2.1

lemma cont_phi [NeZero n] (x : Fin m → Fin n → ℝ) : Continuous (phi x) := by
  have cS : Continuous (fun a => Sx (comb x a)) := by
    unfold Sx comb
    exact continuous_finsetSum _ (fun i _ => by fun_prop)
  have cT : Continuous (fun a => Tx (comb x a)) := by
    unfold Tx comb
    exact continuous_finsetSum _ (fun i _ => by fun_prop)
  have cL : Continuous (fun a => Real.log (Sx (comb x a))) := cS.log (fun a => (Sx_pos _).ne')
  have cG : Continuous (fun a => gg (comb x a)) := by unfold gg; fun_prop
  unfold phi
  exact cG.sub (continuous_finsetSum _ (fun j _ => by fun_prop))

/-! ### Base cases -/

lemma face_one (x : Fin m → Fin n → ℝ) (s : Finset (Fin m)) (hs : s.card = 1) (a : Fin m → ℝ)
    (ha : a ∈ Face s) : phi x a = 0 := by
  obtain ⟨j, rfl⟩ := Finset.card_eq_one.1 hs
  have hoff : ∀ k, k ≠ j → a k = 0 := fun k hk => ha.2.2 k (by simpa using hk)
  have haj : a j = 1 := by
    have := ha.2.1
    rwa [Fintype.sum_eq_single j hoff] at this
  have hc : comb x a = x j := by
    funext i
    unfold comb
    rw [Fintype.sum_eq_single j (fun k hk => by simp [hoff k hk]), haj, one_mul]
  unfold phi
  rw [hc, Fintype.sum_eq_single j (fun k hk => by simp [hoff k hk]), haj, one_mul, sub_self]

lemma face_two [NeZero n] (x : Fin m → Fin n → ℝ) (hx : ∀ j, Sx (x j) = 1) (s : Finset (Fin m))
    (hs : s.card = 2) (a : Fin m → ℝ) (ha : a ∈ Face s) : phi x a ≤ 0 := by
  obtain ⟨j, k, hjk, rfl⟩ := Finset.card_eq_two.1 hs
  have hoff : ∀ l, l ≠ j ∧ l ≠ k → a l = 0 := fun l hl => ha.2.2 l (by simp [hl.1, hl.2])
  have hsum : a j + a k = 1 := by
    have := ha.2.1
    rwa [Fintype.sum_eq_add j k hjk hoff] at this
  have hc : comb x a = fun i => a j * x j i + (1 - a j) * x k i := by
    funext i
    unfold comb
    rw [Fintype.sum_eq_add j k hjk (fun l hl => by simp [hoff l hl]),
      show 1 - a j = a k by linarith]
  have ha1 : a j ≤ 1 := by linarith [ha.1 k]
  have := two (x j) (x k) (hx j) (hx k) (a j) (ha.1 j) ha1
  unfold phi
  rw [hc, Fintype.sum_eq_add j k hjk (fun l hl => by simp [hoff l hl]),
    show a k = 1 - a j by linarith]
  linarith

/-! ### The interior step -/

/-- A direction `b` in the face `s`, summing to `0`, with `∑ bⱼ vⱼ = σ (v₁ - v₃) + τ (v₂ - v₃)`. -/
lemma dir_exists (s : Finset (Fin m)) {j1 j2 j3 : Fin m} (hj1 : j1 ∈ s) (hj2 : j2 ∈ s)
    (hj3 : j3 ∈ s) (h12 : j1 ≠ j2) (h13 : j1 ≠ j3) (h23 : j2 ≠ j3) (σ τ : ℝ)
    (hne : σ ≠ 0 ∨ τ ≠ 0) :
    ∃ b : Fin m → ℝ, ∑ j, b j = 0 ∧ (∀ j, j ∉ s → b j = 0) ∧ 0 < ∑ j, b j ^ 2 ∧
      ∀ v : Fin m → ℝ, ∑ j, b j * v j = σ * (v j1 - v j3) + τ * (v j2 - v j3) := by
  refine ⟨fun j => (if j = j1 then σ else 0) + (if j = j2 then τ else 0) -
    (if j = j3 then σ + τ else 0), ?_, ?_, ?_, ?_⟩
  · simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_ite_eq',
      Finset.mem_univ, if_true]
    ring
  · intro j hj
    have e1 : j ≠ j1 := fun h => hj (h ▸ hj1)
    have e2 : j ≠ j2 := fun h => hj (h ▸ hj2)
    have e3 : j ≠ j3 := fun h => hj (h ▸ hj3)
    simp [e1, e2, e3]
  · have hsub := Finset.sum_le_sum_of_subset_of_nonneg
      (f := fun j => ((if j = j1 then σ else 0) + (if j = j2 then τ else 0) -
        (if j = j3 then σ + τ else 0)) ^ 2)
      (Finset.subset_univ {j1, j2}) (fun k _ _ => sq_nonneg _)
    rw [Finset.sum_pair h12] at hsub
    simp only [if_true, if_neg h12, if_neg h13, if_neg h12.symm, if_neg h23, add_zero, zero_add,
      sub_zero] at hsub
    have h1 : 0 < σ ^ 2 ∨ 0 < τ ^ 2 := hne.imp (fun h => by positivity) (fun h => by positivity)
    rcases h1 with h1 | h1 <;> nlinarith [sq_nonneg σ, sq_nonneg τ]
  · intro v
    simp only [add_mul, sub_mul, ite_mul, zero_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
    ring

/-- No interior local maximum along a direction where `QQ ≥ 0`, once `ε B r²` is added. -/
lemma no_local_max [NeZero n] {xs y : Fin n → ℝ} (hQ : 0 ≤ QQ xs y) (f : ℝ → ℝ)
    (c0 A1 C1 B eps : ℝ) (hB : 0 < B) (heps : 0 < eps)
    (hf : ∀ r, f r = gg (ln xs y r) + c0 - r * A1 + eps * (2 * r * C1 + r ^ 2 * B))
    (hloc : ∀ᶠ r in 𝓝 (0 : ℝ), f r ≤ f 0) : False := by
  have hEB : 0 < eps * B := mul_pos heps hB
  have hQev : ∀ᶠ r in 𝓝 (0 : ℝ), -(eps * B) < QQ (ln xs y r) y := by
    have hc := (cont_QQ xs y).continuousAt (x := 0)
    have : -(eps * B) < QQ (ln xs y 0) y := by rw [ln_zero]; linarith
    exact hc.eventually (lt_mem_nhds this)
  obtain ⟨δ, hδ, hδP⟩ := Metric.eventually_nhds_iff.1 (hloc.and hQev)
  set D := Set.Ioo (-δ) δ with hD
  have hDi : interior D = D := isOpen_Ioo.interior_eq
  let k : ℝ → ℝ := fun r => gg (ln xs y r) + eps * B / 2 * (r * r)
  have hk1 : ∀ r, HasDerivAt k (g1 (ln xs y r) y + eps * B * r) r := fun r =>
    ((hd_gg xs y r).add (((hasDerivAt_id' r).mul (hasDerivAt_id' r)).const_mul (eps * B / 2))).congr_deriv
      (by ring)
  have hk2 : ∀ r, HasDerivAt (fun r => g1 (ln xs y r) y + eps * B * r) (QQ (ln xs y r) y + eps * B) r :=
    fun r => ((hd_g1 xs y r).add ((hasDerivAt_id' r).const_mul (eps * B))).congr_deriv (by ring)
  have hconv : ConvexOn ℝ D k := by
    refine convexOn_of_hasDerivWithinAt2_nonneg (convex_Ioo _ _)
      (fun r _ => (hk1 r).continuousAt.continuousWithinAt)
      (fun r _ => (hk1 r).hasDerivWithinAt) (fun r _ => (hk2 r).hasDerivWithinAt) ?_
    intro r hr
    rw [hDi] at hr
    have hdist : dist r 0 < δ := by
      rw [Real.dist_eq, sub_zero, abs_lt]; exact ⟨hr.1, hr.2⟩
    have := (hδP hdist).2
    linarith
  set r0 := δ / 2 with hr0def
  have hr0 : 0 < r0 := by positivity
  have m1 : r0 ∈ D := ⟨by linarith, by linarith⟩
  have m2 : -r0 ∈ D := ⟨by linarith, by linarith⟩
  have hcv := hconv.2 m2 m1 (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num)
  simp only [smul_eq_mul] at hcv
  rw [show 1 / 2 * -r0 + 1 / 2 * r0 = 0 by ring] at hcv
  have d1 : dist r0 0 < δ := by rw [Real.dist_eq, sub_zero, abs_of_pos hr0]; linarith
  have d2 : dist (-r0) 0 < δ := by rw [Real.dist_eq, sub_zero, abs_neg, abs_of_pos hr0]; linarith
  have f1 := (hδP d1).1
  have f2 := (hδP d2).1
  rw [hf, hf] at f1 f2
  simp only [k] at hcv
  have hsq : 0 < eps * B * r0 ^ 2 := by positivity
  nlinarith

lemma face_step [NeZero n] (x : Fin m → Fin n → ℝ) (s : Finset (Fin m)) (hs : 3 ≤ s.card)
    (IH : ∀ s' : Finset (Fin m), s'.card < s.card → ∀ a ∈ Face s', phi x a ≤ 0) :
    ∀ a ∈ Face s, phi x a ≤ 0 := by
  by_contra hcon
  push Not at hcon
  obtain ⟨a0, ha0, hpos⟩ := hcon
  set eps := phi x a0 / 2 with heps
  have heps0 : 0 < eps := by rw [heps]; linarith
  let psi : (Fin m → ℝ) → ℝ := fun a => phi x a + eps * ∑ j, a j ^ 2
  have hsq : Continuous (fun a : Fin m → ℝ => ∑ j, a j ^ 2) :=
    continuous_finsetSum _ (fun j _ => (continuous_apply j).pow 2)
  have hcont : Continuous psi := (cont_phi x).add (continuous_const.mul hsq)
  obtain ⟨a', ha', hmax⟩ := (face_compact s).exists_isMaxOn ⟨a0, ha0⟩ hcont.continuousOn
  have hmax' : ∀ a ∈ Face s, psi a ≤ psi a' := isMaxOn_iff.1 hmax
  by_cases hbd : ∃ j ∈ s, a' j = 0
  · obtain ⟨j, hj, hj0⟩ := hbd
    have ha'' : a' ∈ Face (s.erase j) := ⟨ha'.1, ha'.2.1, fun l hl => by
      by_cases hlj : l = j
      · rw [hlj]; exact hj0
      · exact ha'.2.2 l (fun h => hl (Finset.mem_erase.2 ⟨hlj, h⟩))⟩
    have h1 := IH (s.erase j) (by rw [Finset.card_erase_of_mem hj]; omega) a' ha''
    have h2 := hmax' a0 ha0
    have h3 := face_sq s ha'
    have h4 : 0 ≤ ∑ j, a0 j ^ 2 := Finset.sum_nonneg (fun j _ => sq_nonneg _)
    simp only [psi] at h2
    have h5 := mul_nonneg heps0.le h4
    have h6 := mul_le_mul_of_nonneg_left h3 heps0.le
    nlinarith
  · push Not at hbd
    have hpos' : ∀ j ∈ s, 0 < a' j := fun j hj => lt_of_le_of_ne (ha'.1 j) (hbd j hj).symm
    obtain ⟨j1, hj1, j2, hj2, j3, hj3, h12, h13, h23⟩ :=
      Finset.two_lt_card.1 (by omega : 2 < s.card)
    set xs := comb x a' with hxs
    obtain ⟨σ, τ, hne, hQ⟩ := index xs (fun i => x j1 i - x j3 i) (fun i => x j2 i - x j3 i)
    set y : Fin n → ℝ := fun i => σ * (x j1 i - x j3 i) + τ * (x j2 i - x j3 i) with hy
    obtain ⟨b, hb_sum, hb_off, hB, hb_comb⟩ := dir_exists s hj1 hj2 hj3 h12 h13 h23 σ τ hne
    have hline : ∀ r, comb x (fun j => a' j + r * b j) = ln xs y r := by
      intro r
      funext i
      unfold comb ln
      have := hb_comb (fun j => x j i)
      rw [hxs]
      unfold comb
      simp only [add_mul, Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum, this, hy]
    have hsum1 : ∀ r, ∑ j, (a' j + r * b j) * gg (x j) =
        ∑ j, a' j * gg (x j) + r * ∑ j, b j * gg (x j) := by
      intro r
      simp only [add_mul, Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum]
    have hsum2 : ∀ r, ∑ j, (a' j + r * b j) ^ 2 =
        ∑ j, a' j ^ 2 + (2 * r * ∑ j, a' j * b j + r ^ 2 * ∑ j, b j ^ 2) := by
      intro r
      have e : ∀ j, (a' j + r * b j) ^ 2 = a' j ^ 2 + (2 * r * (a' j * b j) + r ^ 2 * b j ^ 2) := by
        intro j; ring
      simp only [e, Finset.sum_add_distrib, ← Finset.mul_sum]
    let f : ℝ → ℝ := fun r => psi (fun j => a' j + r * b j)
    have hf : ∀ r, f r = gg (ln xs y r) + (eps * ∑ j, a' j ^ 2 - ∑ j, a' j * gg (x j))
        - r * ∑ j, b j * gg (x j) + eps * (2 * r * ∑ j, a' j * b j + r ^ 2 * ∑ j, b j ^ 2) := by
      intro r
      simp only [f, psi, phi]
      rw [hline r, hsum1 r, hsum2 r]
      ring
    have hf0 : f 0 = psi a' := by
      simp only [f, zero_mul, add_zero]
    have hev : ∀ᶠ r in 𝓝 (0 : ℝ), (fun j => a' j + r * b j) ∈ Face s := by
      have h1 : ∀ j, ∀ᶠ r in 𝓝 (0 : ℝ), 0 ≤ a' j + r * b j := by
        intro j
        by_cases hj : j ∈ s
        · have hc : ContinuousAt (fun r : ℝ => a' j + r * b j) 0 := by fun_prop
          have h0 : (0 : ℝ) < a' j + 0 * b j := by simpa using hpos' j hj
          exact (hc.eventually (lt_mem_nhds h0)).mono (fun r hr => hr.le)
        · exact Filter.Eventually.of_forall (fun r => by simp [ha'.2.2 j hj, hb_off j hj])
      filter_upwards [Filter.eventually_all.2 h1] with r hr
      refine ⟨hr, ?_, fun j hj => by simp [ha'.2.2 j hj, hb_off j hj]⟩
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, hb_sum, ha'.2.1]
      ring
    have hloc : ∀ᶠ r in 𝓝 (0 : ℝ), f r ≤ f 0 := by
      filter_upwards [hev] with r hr
      rw [hf0]
      exact hmax' _ hr
    exact no_local_max hQ f _ _ _ _ eps hB heps0 hf hloc

theorem face_claim [NeZero n] (x : Fin m → Fin n → ℝ) (hx : ∀ j, Sx (x j) = 1) :
    ∀ (k : ℕ) (s : Finset (Fin m)), s.card = k → ∀ a ∈ Face s, phi x a ≤ 0 := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k IH =>
    intro s hs a ha
    rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ 3 ≤ k by omega) with h | h | h | h
    · exfalso
      rw [h, Finset.card_eq_zero] at hs
      have h0 : ∀ j, a j = 0 := fun j => ha.2.2 j (by simp [hs])
      have := ha.2.1
      simp [h0] at this
    · exact (face_one x s (hs.trans h) a ha).le
    · exact face_two x hx s (hs.trans h) a ha
    · exact face_step x s (by omega) (fun s' hs' => IH s'.card (by omega) s' rfl) a ha

/-- Theorem M in log coordinates. -/
theorem log_thm [NeZero n] (x : Fin m → Fin n → ℝ) (hx : ∀ j, Sx (x j) = 1) (a : Fin m → ℝ)
    (ha0 : ∀ j, 0 ≤ a j) (has : ∑ j, a j = 1) :
    gg (comb x a) ≤ ∑ j, a j * gg (x j) := by
  have := face_claim x hx _ Finset.univ rfl a ⟨ha0, has, fun j hj => absurd (Finset.mem_univ j) hj⟩
  unfold phi at this
  linarith

end FriedanMulti

end
