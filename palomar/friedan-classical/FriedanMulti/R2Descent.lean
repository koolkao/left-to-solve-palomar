/-
Copyright 2026 Ming-Chih Kao. Licensed under the Apache License, Version 2.0;
see the LICENSE file at the root of this repository.
-/
module

public import FriedanEntropy.Proof

/-! Port: copied from `FriedanMulti/R2Descent.lean` of github.com/koolkao/friedan-entropy-inequality (commit 0f4ba65dc126f59e7158fbcbc01548baa78cf21d, Lean v4.33.1, Mathlib 0df444a) and put into the module system (`module` header, `public import`, public section). No other change was needed for Lean v4.36.0 / Mathlib fc4f59e. -/

@[expose] public section

/-!
# The descent for binary entropies (all `m`)

Abstract setting: `h` differentiable with derivative `h1`, antitone on `[0, ∞)`, and
`Δ(A, B) = h1 A - h1 B + 2 h(A) (sg A - sg B) ≥ 0` for `0 ≤ B ≤ A`. Then for weights `a > 0` on a
finset `s` summing to `1` and logits `A ≥ 0`,
`e^{2 l(w)} h(w) ≤ (∑ a h(A)) e^{2 ∑ a l(A)}`, `w = ∑ a A` (`descent`). The two largest values are
merged to their weighted mean along a straight path; the moving top value stays the global maximum.
-/

open Real Finset Friedan

namespace FriedanR2

variable {ι : Type*} [DecidableEq ι]

noncomputable def QQs (h : ℝ → ℝ) (s : Finset ι) (a A : ι → ℝ) : ℝ :=
  (∑ j ∈ s, a j * h (A j)) * Real.exp (2 * ∑ j ∈ s, a j * lp (A j))

section
variable (h h1 : ℝ → ℝ) (hd : ∀ t, HasDerivAt h (h1 t) t) (hanti : AntitoneOn h (Set.Ici 0))
  (hD : ∀ A B, 0 ≤ B → B ≤ A → 0 ≤ h1 A - h1 B + 2 * h A * (sg A - sg B))
include hd hanti hD

/-- One merge step: replacing the top two values by their weighted mean does not increase `QQs`. -/
lemma merge_step (s : Finset ι) (a A : ι → ℝ) (ha : ∀ j ∈ s, 0 < a j) (has : ∑ j ∈ s, a j = 1)
    (hA : ∀ j ∈ s, 0 ≤ A j) {p q : ι} (hp : p ∈ s) (hq : q ∈ s) (hpq : p ≠ q)
    (hqp : A q ≤ A p) (htop : ∀ j ∈ s, j ≠ p → A j ≤ A q) :
    QQs h s a (fun j => A j + (if j = p then (a p * A p + a q * A q) / (a p + a q) - A p
      else if j = q then (a p * A p + a q * A q) / (a p + a q) - A q else 0)) ≤ QQs h s a A := by
  set cm := (a p * A p + a q * A q) / (a p + a q) with hcm
  set dir : ι → ℝ := fun j => if j = p then cm - A p else if j = q then cm - A q else 0 with hdir
  have hap := ha p hp
  have haq := ha q hq
  have hsum0 : a p + a q ≠ 0 := by linarith
  set κ := a p * a q * (A p - A q) / (a p + a q) with hκ
  have hκ0 : 0 ≤ κ := div_nonneg (mul_nonneg (mul_nonneg hap.le haq.le) (by linarith)) (by linarith)
  have hdp : a p * (cm - A p) = -κ := by rw [hcm, hκ]; field_simp; ring
  have hdq : a q * (cm - A q) = κ := by rw [hcm, hκ]; field_simp; ring
  have hcmq : A q ≤ cm := by
    rw [hcm, le_div_iff₀ (by linarith)]; nlinarith
  have hcmp : cm ≤ A p := by
    rw [hcm, div_le_iff₀ (by linarith)]; nlinarith
  -- sums of `a j F j dir j` collapse to the two moving indices
  have hcoll : ∀ F : ι → ℝ, ∑ j ∈ s, a j * F j * dir j = -κ * (F p - F q) := by
    intro F
    rw [Finset.sum_eq_add_of_mem p q hp hq hpq (fun j _ hj => by
      simp [hdir, hj.1, hj.2])]
    simp only [hdir, if_pos rfl, if_neg hpq.symm, if_true]
    rw [show a p * F p * (cm - A p) = F p * (a p * (cm - A p)) by ring,
      show a q * F q * (cm - A q) = F q * (a q * (cm - A q)) by ring, hdp, hdq]
    ring
  let At : ℝ → ι → ℝ := fun t j => A j + t * dir j
  let L : ℝ → ℝ := fun t => ∑ j ∈ s, a j * h (At t j)
  let M : ℝ → ℝ := fun t => ∑ j ∈ s, a j * lp (At t j)
  have hL : ∀ t, HasDerivAt L (∑ j ∈ s, a j * h1 (At t j) * dir j) t := by
    intro t
    refine HasDerivAt.fun_sum (fun j _ => ?_)
    have := ((hd (At t j)).comp t (((hasDerivAt_id' t).mul_const (dir j)).const_add (A j)))
    exact (this.const_mul (a j)).congr_deriv (by ring)
  have hM : ∀ t, HasDerivAt M (∑ j ∈ s, a j * (sg (At t j) - 1 / 2) * dir j) t := by
    intro t
    refine HasDerivAt.fun_sum (fun j _ => ?_)
    have := ((hasDerivAt_lp (At t j)).comp t (((hasDerivAt_id' t).mul_const (dir j)).const_add (A j)))
    exact (this.const_mul (a j)).congr_deriv (by ring)
  let φ : ℝ → ℝ := fun t => L t * Real.exp (2 * M t)
  have hφ : ∀ t, HasDerivAt φ (-κ * Real.exp (2 * M t) * (h1 (At t p) - h1 (At t q) +
      2 * L t * (sg (At t p) - sg (At t q)))) t := by
    intro t
    refine ((hL t).mul ((hM t).const_mul 2).exp).congr_deriv ?_
    rw [hcoll (fun j => h1 (At t j)), hcoll (fun j => sg (At t j) - 1 / 2)]
    ring
  have hAtp : ∀ t, At t p = A p + t * (cm - A p) := fun t => by simp [At, hdir]
  have hAtq : ∀ t, At t q = A q + t * (cm - A q) := fun t => by simp [At, hdir, hpq.symm]
  have hAto : ∀ t, ∀ j, j ≠ p → j ≠ q → At t j = A j := fun t j h1' h2' => by
    simp [At, hdir, h1', h2']
  have hanti' : AntitoneOn φ (Set.Icc 0 1) := by
    refine antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc 0 1) (f' := fun t =>
        -κ * Real.exp (2 * M t) * (h1 (At t p) - h1 (At t q) + 2 * L t * (sg (At t p) - sg (At t q))))
      (fun t _ => (hφ t).continuousAt.continuousWithinAt) (fun t _ => (hφ t).hasDerivWithinAt) ?_
    intro t ht
    rw [interior_Icc] at ht
    have hq0 : 0 ≤ At t q := by rw [hAtq]; nlinarith [hA q hq, ht.1]
    have hqp' : At t q ≤ At t p := by rw [hAtq, hAtp]; nlinarith [ht.2, ht.1]
    have hqq : A q ≤ At t q := by rw [hAtq]; nlinarith [ht.1]
    have hp0 : 0 ≤ At t p := le_trans hq0 hqp'
    -- every current value is at most the top one
    have hle : ∀ j ∈ s, h (At t p) ≤ h (At t j) := by
      intro j hj
      by_cases hjp : j = p
      · rw [hjp]
      by_cases hjq : j = q
      · rw [hjq]; exact hanti hq0 hp0 hqp'
      rw [hAto t j hjp hjq]
      exact hanti (hA j hj) hp0 (le_trans (htop j hj hjp) (le_trans hqq hqp'))
    have hLge : h (At t p) ≤ L t := by
      have : ∑ j ∈ s, a j * h (At t p) ≤ L t :=
        Finset.sum_le_sum (fun j hj => mul_le_mul_of_nonneg_left (hle j hj) (ha j hj).le)
      rwa [← Finset.sum_mul, has, one_mul] at this
    have hsg : sg (At t q) ≤ sg (At t p) := sg_mono hqp'
    have hDel := hD (At t p) (At t q) hq0 hqp'
    have hbr : 0 ≤ h1 (At t p) - h1 (At t q) + 2 * L t * (sg (At t p) - sg (At t q)) := by
      nlinarith
    have he := Real.exp_pos (2 * M t)
    have := mul_nonneg (mul_nonneg hκ0 he.le) hbr
    linarith
  have h01 := hanti' ⟨le_rfl, zero_le_one⟩ ⟨zero_le_one, le_rfl⟩ zero_le_one
  have e0 : φ 0 = QQs h s a A := by
    simp only [φ, L, M, At, zero_mul, add_zero]; rfl
  have e1 : φ 1 = QQs h s a (fun j => A j + dir j) := by
    simp only [φ, L, M, At, one_mul]; rfl
  rw [← e0]
  rw [← e1] at *
  exact h01

end

/-- Merging two indices with equal values. -/
lemma merge_sum (s : Finset ι) (a B : ι → ℝ) (G : ℝ → ℝ) {p q : ι} (hp : p ∈ s) (hq : q ∈ s)
    (hpq : p ≠ q) (hB : B p = B q) :
    ∑ j ∈ s, a j * G (B j) =
      ∑ j ∈ s.erase q, Function.update a p (a p + a q) j * G (B j) := by
  have hp' : p ∈ s.erase q := Finset.mem_erase.2 ⟨hpq, hp⟩
  have e : ∀ j, Function.update a p (a p + a q) j * G (B j) =
      a j * G (B j) + (if j = p then a q * G (B p) else 0) := by
    intro j
    by_cases hj : j = p
    · subst hj; simp; ring
    · simp [hj]
  rw [Finset.sum_congr rfl (fun j _ => e j), Finset.sum_add_distrib, Finset.sum_ite_eq',
    if_pos hp', ← Finset.add_sum_erase s _ hq, hB]
  ring

section
variable (h h1 : ℝ → ℝ) (hd : ∀ t, HasDerivAt h (h1 t) t) (hanti : AntitoneOn h (Set.Ici 0))
  (hD : ∀ A B, 0 ≤ B → B ≤ A → 0 ≤ h1 A - h1 B + 2 * h A * (sg A - sg B))
include hd hanti hD

theorem descent : ∀ (k : ℕ) (s : Finset ι), s.card = k → ∀ a A : ι → ℝ, (∀ j ∈ s, 0 < a j) →
    ∑ j ∈ s, a j = 1 → (∀ j ∈ s, 0 ≤ A j) →
    Real.exp (2 * lp (∑ j ∈ s, a j * A j)) * h (∑ j ∈ s, a j * A j) ≤ QQs h s a A := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k IH =>
    intro s hs a A ha has hA
    rcases (show k = 0 ∨ k = 1 ∨ 2 ≤ k by omega) with hk | hk | hk
    · rw [hk, Finset.card_eq_zero] at hs; subst hs; simp at has
    · obtain ⟨p, rfl⟩ := Finset.card_eq_one.1 (hs.trans hk)
      simp only [Finset.sum_singleton] at has ⊢
      unfold QQs
      simp only [Finset.sum_singleton, has, one_mul]
      exact le_of_eq (mul_comm _ _)
    · have hne : s.Nonempty := Finset.card_pos.1 (by omega)
      obtain ⟨p, hp, hpmax⟩ := Finset.exists_max_image s A hne
      have hne' : (s.erase p).Nonempty := Finset.card_pos.1 (by
        rw [Finset.card_erase_of_mem hp]; omega)
      obtain ⟨q, hq', hqmax⟩ := Finset.exists_max_image (s.erase p) A hne'
      have hqp : q ≠ p := (Finset.mem_erase.1 hq').1
      have hq : q ∈ s := (Finset.mem_erase.1 hq').2
      have htop : ∀ j ∈ s, j ≠ p → A j ≤ A q :=
        fun j hj hjp => hqmax j (Finset.mem_erase.2 ⟨hjp, hj⟩)
      have hstep := merge_step h h1 hd hanti hD s a A ha has hA hp hq hqp.symm (hpmax q hq) htop
      set cm := (a p * A p + a q * A q) / (a p + a q) with hcm
      set B : ι → ℝ := fun j => A j + (if j = p then cm - A p else if j = q then cm - A q else 0)
        with hBdef
      have hBp : B p = cm := by simp [hBdef]
      have hBq : B q = cm := by simp [hBdef, hqp]
      have hBo : ∀ j, j ≠ p → j ≠ q → B j = A j := fun j h1' h2' => by simp [hBdef, h1', h2']
      have hap := ha p hp
      have haq := ha q hq
      have hcm0 : 0 ≤ cm := div_nonneg (add_nonneg (mul_nonneg hap.le (hA p hp))
        (mul_nonneg haq.le (hA q hq))) (by linarith)
      -- the weighted mean is preserved
      have hw : ∑ j ∈ s, a j * B j = ∑ j ∈ s, a j * A j := by
        rw [← Finset.add_sum_erase s (fun j => a j * B j) hp,
          ← Finset.add_sum_erase s (fun j => a j * A j) hp,
          ← Finset.add_sum_erase (s.erase p) (fun j => a j * B j) hq',
          ← Finset.add_sum_erase (s.erase p) (fun j => a j * A j) hq']
        have hrest : ∑ j ∈ (s.erase p).erase q, a j * B j = ∑ j ∈ (s.erase p).erase q, a j * A j :=
          Finset.sum_congr rfl (fun j hj => by
            have h1' := Finset.ne_of_mem_erase hj
            have h2' := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hj)
            rw [hBo j h2' h1'])
        rw [hrest, hBp, hBq, hcm]
        field_simp
        ring
      -- merge q into p
      set a' := Function.update a p (a p + a q) with ha'
      have hpe : p ∈ s.erase q := Finset.mem_erase.2 ⟨hqp.symm, hp⟩
      have hB_eq : B p = B q := by rw [hBp, hBq]
      have m1 := merge_sum s a B h hp hq hqp.symm hB_eq
      have m2 := merge_sum s a B lp hp hq hqp.symm hB_eq
      have m3 := merge_sum s a B id hp hq hqp.symm hB_eq
      have m4 := merge_sum s a (fun _ => (1 : ℝ)) id hp hq hqp.symm rfl
      simp only [id, mul_one] at m3 m4
      have hQB : QQs h s a B = QQs h (s.erase q) a' B := by
        unfold QQs; rw [m1, m2]
      have ha'pos : ∀ j ∈ s.erase q, 0 < a' j := by
        intro j hj
        by_cases hjp : j = p
        · rw [hjp, ha', Function.update_self]; linarith
        · rw [ha', Function.update_of_ne hjp]; exact ha j (Finset.mem_of_mem_erase hj)
      have ha's : ∑ j ∈ s.erase q, a' j = 1 := by rw [← m4, has]
      have hB0 : ∀ j ∈ s.erase q, 0 ≤ B j := by
        intro j hj
        by_cases hjp : j = p
        · rw [hjp, hBp]; exact hcm0
        · have hjq : j ≠ q := (Finset.mem_erase.1 hj).1
          rw [hBo j hjp hjq]; exact hA j (Finset.mem_of_mem_erase hj)
      have hcard : (s.erase q).card < k := by rw [Finset.card_erase_of_mem hq]; omega
      have hIH := IH _ hcard (s.erase q) rfl a' B ha'pos ha's hB0
      rw [← m3, hw] at hIH
      rw [← hQB] at hIH
      exact hIH.trans hstep

end

end FriedanR2

end
