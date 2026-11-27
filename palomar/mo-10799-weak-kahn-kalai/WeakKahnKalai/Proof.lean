/-
Copyright 2026 Ming-Chih Kao. Licensed under the Apache License, Version 2.0;
see the LICENSE file at the root of this repository.
`μ_sum_eq_one` and `μFamily_univ` are copied from formal-conjectures
`FormalConjectures/Mathoverflow/10799.lean` (Copyright 2026 The Formal Conjectures Authors,
Apache-2.0). The definitions `mu`, `M`, `I` and the lemmas `sd1` … `I_insert` in namespace
`OMA10799W` come from Left to Solve PR #341 by Genbox, not from Ming-Chih Kao; their
licence is unresolved (see NOTICE).
-/
module

public import WeakKahnKalai.Defs

/-! Ported from the archived Left to Solve file `Mathoverflow10799.mathoverflow_10799.variants.weak_kahn_kalai.lean` (Lean v4.33.1) to Lean
v4.36.0 and the module system; the mathematics and the proof are unchanged unless a comment
says otherwise. -/

@[expose] public section

namespace Mathoverflow10799

open Finset Real

-- Copied from formal-conjectures `FormalConjectures/Mathoverflow/10799.lean` (Apache-2.0).
/--
The $p$-biased measure is a probability distribution: it sums to $1$ over all subsets.
This is the binomial identity $(p + (1-p))^n = 1$.
-/
theorem μ_sum_eq_one (n : ℕ) (p : ℝ) :
    ∑ S : Finset (Fin n), μ p S = 1 := by
  unfold μ
  have h := Fintype.sum_pow_mul_eq_add_pow (Fin n) p (1 - p)
  rw [Fintype.card_fin] at h
  rw [h]
  simp

/-- The measure of the full power set is $1$. -/
theorem μFamily_univ (n : ℕ) (p : ℝ) :
    μFamily p (Finset.univ : Finset (Finset (Fin n))) = 1 := by
  unfold μFamily
  exact μ_sum_eq_one n p

end Mathoverflow10799

-- Problem: Optimal monotone families for the discrete isoperimetric inequality — weak kahn kalai
-- Upstream: formal-conjectures FormalConjectures/Mathoverflow/10799.lean:218 (declaration Mathoverflow10799.mathoverflow_10799.variants.weak_kahn_kalai)
-- Credit: @koolkao (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
--
-- Proof (Kahn–Kalai 2006): Russo–Margulis gives d/dp μ_p(F) = I^p(F) in this normalization; then the
-- Cauchy mean value theorem for G(p) = -log(-log μ_p(F)) against log p on [n^{-ε} t, t].
-- The definitions mu, M, I and the lemmas sd1, sd2, sd3, mu_nonneg, mu_ins0, mu_ins1, M_insert, I_insert
-- are reused from the merged proof of Mathoverflow10799.discrete_isoperimetric_inequality
-- (open-math-agents PR #341).

namespace OMA10799W
open Finset Real

variable {α : Type*} [DecidableEq α]

noncomputable def mu (p : ℝ) (U S : Finset α) : ℝ := p ^ S.card * (1 - p) ^ (U.card - S.card)

open Classical in
noncomputable def M (p : ℝ) (U : Finset α) (P : Finset α → Prop) : ℝ :=
  ∑ S ∈ U.powerset, if P S then mu p U S else 0

open Classical in
noncomputable def I (p : ℝ) (U : Finset α) (P : Finset α → Prop) : ℝ :=
  ∑ S ∈ U.powerset, mu p U S * ∑ i ∈ U, (if Xor (P S) (P (symmDiff S {i})) then (1:ℝ) else 0)

lemma sd1 {a : α} {S : Finset α} (h : a ∉ S) : symmDiff S {a} = insert a S := by
  ext x; simp only [mem_symmDiff, mem_singleton, mem_insert]; by_cases hx : x = a <;> simp_all

lemma sd2 {a : α} {S : Finset α} (h : a ∉ S) : symmDiff (insert a S) {a} = S := by
  ext x; simp only [mem_symmDiff, mem_singleton, mem_insert]; by_cases hx : x = a <;> simp_all

lemma sd3 {a i : α} {S : Finset α} (h : i ≠ a) :
    symmDiff (insert a S) {i} = insert a (symmDiff S {i}) := by
  ext x; simp only [mem_symmDiff, mem_singleton, mem_insert]
  by_cases hx : x = a <;> by_cases hi : x = i <;> simp_all

omit [DecidableEq α] in
lemma mu_nonneg {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (U S : Finset α) : 0 ≤ mu p U S := by
  unfold mu; have : 0 ≤ 1 - p := by linarith
  positivity

lemma mu_ins0 {p : ℝ} {a : α} {U S : Finset α} (ha : a ∉ U) (hS : S ⊆ U) :
    mu p (insert a U) S = (1 - p) * mu p U S := by
  unfold mu
  have := card_le_card hS
  rw [card_insert_of_notMem ha, show U.card + 1 - S.card = (U.card - S.card) + 1 by omega, pow_succ]
  ring

lemma mu_ins1 {p : ℝ} {a : α} {U S : Finset α} (ha : a ∉ U) (hS : S ⊆ U) :
    mu p (insert a U) (insert a S) = p * mu p U S := by
  unfold mu
  have haS : a ∉ S := fun h => ha (hS h)
  rw [card_insert_of_notMem ha, card_insert_of_notMem haS, pow_succ,
    show U.card + 1 - (S.card + 1) = U.card - S.card by omega]
  ring

lemma M_insert {p : ℝ} {a : α} {U : Finset α} (ha : a ∉ U) (P : Finset α → Prop) :
    M p (insert a U) P = (1 - p) * M p U P + p * M p U (fun S => P (insert a S)) := by
  classical
  unfold M
  rw [sum_powerset_insert ha, mul_sum, mul_sum]
  congr 1 <;> refine sum_congr rfl fun S hS => ?_ <;> rw [mem_powerset] at hS
  · rw [mu_ins0 ha hS]; split_ifs <;> ring
  · rw [mu_ins1 ha hS]; split_ifs <;> ring

lemma I_insert {p : ℝ} {a : α} {U : Finset α} (ha : a ∉ U) (P : Finset α → Prop)
    (hP : ∀ S T, P S → S ⊆ T → P T) :
    I p (insert a U) P = (1 - p) * I p U P + p * I p U (fun S => P (insert a S))
      + (M p U (fun S => P (insert a S)) - M p U P) := by
  classical
  unfold I M
  rw [sum_powerset_insert ha, ← sum_add_distrib, mul_sum, mul_sum, ← sum_sub_distrib,
    ← sum_add_distrib, ← sum_add_distrib]
  refine sum_congr rfl fun S hS => ?_
  rw [mem_powerset] at hS
  have haS : a ∉ S := fun h => ha (hS h)
  have h3 : ∑ i ∈ U, (if Xor (P (insert a S)) (P (symmDiff (insert a S) {i})) then (1:ℝ) else 0)
      = ∑ i ∈ U, (if Xor (P (insert a S)) (P (insert a (symmDiff S {i}))) then (1:ℝ) else 0) :=
    sum_congr rfl fun i hi => by rw [sd3 (show i ≠ a by rintro rfl; exact ha hi)]
  rw [mu_ins0 ha hS, mu_ins1 ha hS, sum_insert ha, sum_insert ha, sd1 haS, sd2 haS, h3]
  by_cases h1 : P S <;> by_cases h2 : P (insert a S)
  · simp [Xor, h1, h2]; ring
  · exact absurd (hP _ _ h1 (subset_insert _ _)) h2
  · simp [Xor, h1, h2]; ring
  · simp [Xor, h1, h2]; ring

/-- Russo–Margulis, by induction on the ground set. -/
theorem hasDerivAt_M (p : ℝ) (U : Finset α) :
    ∀ (P : Finset α → Prop), (∀ S T, P S → S ⊆ T → P T) →
      HasDerivAt (fun q => M q U P) (I p U P) p := by
  induction U using Finset.induction_on with
  | empty =>
    intro P _
    classical
    have hf : (fun q => M q (∅ : Finset α) P) = fun _ => M 0 (∅ : Finset α) P := by
      funext q; simp [M, mu]
    have hI : I p (∅ : Finset α) P = 0 := by simp [I]
    rw [hf, hI]
    exact hasDerivAt_const p _
  | @insert a U ha ih =>
    intro P hP
    have hP1 : ∀ S T, P (insert a S) → S ⊆ T → P (insert a T) :=
      fun S T h hST => hP _ _ h (insert_subset_insert a hST)
    have i0 := ih P hP
    have i1 := ih _ hP1
    have hf : (fun q => M q (insert a U) P) =
        fun q => (1 - q) * M q U P + q * M q U (fun S => P (insert a S)) := by
      funext q; exact M_insert ha P
    rw [hf, I_insert ha P hP]
    have h := (((hasDerivAt_id p).const_sub 1).mul i0).add ((hasDerivAt_id p).mul i1)
    refine h.congr_deriv ?_
    simp only [id]
    ring

end OMA10799W

namespace OMA10799W
open Finset Real Mathoverflow10799

theorem M_eq {n : ℕ} (p : ℝ) (F : Finset (Finset (Fin n))) :
    M p univ (fun S => S ∈ F) = μFamily p F := by
  classical
  unfold M μFamily
  simp only [powerset_univ]
  have e : ∀ S : Finset (Fin n), mu p univ S = μ p S := fun S => by
    simp [mu, μ]
  trans ∑ x : Finset (Fin n), if x ∈ F then μ p x else 0
  · exact sum_congr rfl fun x _ => by split_ifs <;> simp [e]
  · rw [Finset.sum_ite_mem, univ_inter]

theorem I_eq {n : ℕ} (p : ℝ) (F : Finset (Finset (Fin n))) :
    I p univ (fun S => S ∈ F) = edgeBoundary n p F := by
  classical
  unfold I edgeBoundary boundaryCount
  rw [powerset_univ]
  refine sum_congr rfl fun S _ => ?_
  simp only [mu, μ, card_univ, Fintype.card_fin]
  congr 1
  rw [Finset.natCast_card_filter]
  exact Finset.sum_congr rfl fun x _ => by split_ifs <;> rfl

theorem russo {n : ℕ} (p : ℝ) (F : Finset (Finset (Fin n))) (hF : IsMonotoneIncreasing F) :
    HasDerivAt (fun q => μFamily q F) (edgeBoundary n p F) p := by
  have hP : ∀ S T : Finset (Fin n), S ∈ F → S ⊆ T → T ∈ F := fun S T hS hST => hF hST hS
  have h := hasDerivAt_M p (Finset.univ) (fun S => S ∈ F) hP
  rw [I_eq] at h
  have e : (fun q => M q univ (fun S => S ∈ F)) = fun q => μFamily q F :=
    funext fun q => M_eq q F
  rwa [e] at h

theorem μ_pos {n : ℕ} {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (S : Finset (Fin n)) : 0 < μ p S := by
  unfold μ; have : 0 < 1 - p := by linarith
  positivity

theorem μFamily_pos {n : ℕ} {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) {F : Finset (Finset (Fin n))}
    (hne : F.Nonempty) : 0 < μFamily p F :=
  Finset.sum_pos (fun S _ => μ_pos hp0 hp1 S) hne

theorem μFamily_lt_one {n : ℕ} {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) {F : Finset (Finset (Fin n))}
    {T : Finset (Fin n)} (hT : T ∉ F) : μFamily p F < 1 := by
  rw [← μFamily_univ n p]
  exact Finset.sum_lt_sum_of_subset (subset_univ F) (mem_univ T) hT (μ_pos hp0 hp1 T)
    (fun j _ _ => (μ_pos hp0 hp1 j).le)

theorem μ_ge {n : ℕ} {s t : ℝ} (hs : 0 < s) (hst : s ≤ t) (ht1 : t < 1) (S : Finset (Fin n)) :
    (s / t) ^ n * μ t S ≤ μ s S := by
  have ht : 0 < t := lt_of_lt_of_le hs hst
  have hk : #S ≤ n := S.card_le_univ.trans_eq (Fintype.card_fin n)
  unfold μ
  have e : (s / t) ^ n * (t ^ #S * (1 - t) ^ (n - #S)) =
      s ^ #S * ((s / t) * (1 - t)) ^ (n - #S) := by
    rw [← pow_mul_pow_sub (s / t) hk, mul_pow, div_pow, div_pow]
    field_simp
  rw [e]
  have h1 : 0 ≤ (s / t) * (1 - t) := by
    have : 0 ≤ 1 - t := by linarith
    positivity
  have h2 : (s / t) * (1 - t) ≤ 1 - s := by
    rw [div_mul_eq_mul_div, div_le_iff₀ ht]
    nlinarith
  gcongr

theorem μFamily_ge {n : ℕ} {s t : ℝ} (hs : 0 < s) (hst : s ≤ t) (ht1 : t < 1)
    (F : Finset (Finset (Fin n))) : (s / t) ^ n * μFamily t F ≤ μFamily s F := by
  unfold μFamily
  rw [mul_sum]
  exact sum_le_sum fun S _ => μ_ge hs hst ht1 S

end OMA10799W

open Finset Real Mathoverflow10799 in
theorem OMA.solution :
    ∀ ε > (0 : ℝ), ∃ C > (0 : ℝ), ∀ (n : ℕ) (_ : 2 ≤ n)
    (F : Finset (Finset (Fin n))) (_ : Mathoverflow10799.IsMonotoneIncreasing F)
    (t : ℝ) (_ : 0 < t) (_ : t < 1) (_ : Mathoverflow10799.μFamily t F = 1 / 2),
    ∃ p, (n : ℝ) ^ (-ε) * t ≤ p ∧ p ≤ t ∧ Mathoverflow10799.IsOptimalWith C p F := by
  intro ε hε
  refine ⟨4 + 4 / ε, by positivity, ?_⟩
  intro n hn F hF t ht0 ht1 hmt
  have hn2 : (2:ℝ) ≤ n := by exact_mod_cast hn
  have hn1 : (1:ℝ) < n := by linarith
  have hlog2 : 1 / 2 < log 2 := by have := Real.log_two_gt_d9; linarith
  have hlogn : log 2 ≤ log n := log_le_log (by norm_num) hn2
  have hlogn1 : log (n:ℝ) ≤ n - 1 := Real.log_le_sub_one_of_pos (by linarith)
  have hr0 : 0 < (n:ℝ) ^ (-ε) := rpow_pos_of_pos (by linarith) _
  have hr1 : (n:ℝ) ^ (-ε) < 1 := rpow_lt_one_of_one_lt_of_neg hn1 (by linarith)
  have hlogr : log ((n:ℝ) ^ (-ε)) = -ε * log n := Real.log_rpow (by linarith) _
  set r := (n:ℝ) ^ (-ε) with hr
  set s := r * t with hs
  have hs0 : 0 < s := mul_pos hr0 ht0
  have hst : s < t := mul_lt_of_lt_one_left ht0 hr1
  have hlogs : log s = -ε * log n + log t := by rw [hs, log_mul hr0.ne' ht0.ne', hlogr]
  have hne : F.Nonempty := by
    rcases F.eq_empty_or_nonempty with h | h
    · rw [h] at hmt; simp [μFamily] at hmt
    · exact h
  obtain ⟨T, hT⟩ : ∃ T, T ∉ F := by
    by_contra h
    have : F = univ := eq_univ_of_forall (fun T => by by_contra hT; exact h ⟨T, hT⟩)
    rw [this, μFamily_univ] at hmt; norm_num at hmt
  have hm0 : ∀ q, 0 < q → q < 1 → 0 < μFamily q F := fun q h0 h1 =>
    OMA10799W.μFamily_pos h0 h1 hne
  have hm1 : ∀ q, 0 < q → q < 1 → μFamily q F < 1 := fun q h0 h1 =>
    OMA10799W.μFamily_lt_one h0 h1 hT
  have hL0 : ∀ q, 0 < q → q < 1 → 0 < -log (μFamily q F) := fun q h0 h1 =>
    neg_pos.mpr (log_neg (hm0 q h0 h1) (hm1 q h0 h1))
  set G : ℝ → ℝ := fun q => -log (-log (μFamily q F)) with hG
  set f' : ℝ → ℝ := fun q =>
    -((-(edgeBoundary n q F / μFamily q F)) / (-log (μFamily q F))) with hf'
  have hGd : ∀ q, 0 < q → q < 1 → HasDerivAt G (f' q) q := fun q h0 h1 =>
    (((OMA10799W.russo q F hF).log (hm0 q h0 h1).ne').neg.log (hL0 q h0 h1).ne').neg
  have hIcc : ∀ x ∈ Set.Icc s t, 0 < x ∧ x < 1 := fun x hx =>
    ⟨lt_of_lt_of_le hs0 hx.1, lt_of_le_of_lt hx.2 ht1⟩
  have hGc : ContinuousOn G (Set.Icc s t) := fun x hx =>
    (hGd x (hIcc x hx).1 (hIcc x hx).2).continuousAt.continuousWithinAt
  have hlc : ContinuousOn log (Set.Icc s t) := Real.continuousOn_log.mono fun x hx =>
    (hIcc x hx).1.ne'
  obtain ⟨c, hc, hceq⟩ := exists_ratio_hasDerivAt_eq_ratio_slope G f' hst hGc
    (fun x hx => hGd x (lt_trans hs0 hx.1) (lt_trans hx.2 ht1)) log (fun x => x⁻¹) hlc
    (fun x hx => Real.hasDerivAt_log (lt_trans hs0 hx.1).ne')
  have hc0 : 0 < c := lt_trans hs0 hc.1
  have hc1 : c < 1 := lt_trans hc.2 ht1
  refine ⟨c, hc.1.le, hc.2.le, ?_⟩
  -- the bound on G t - G s
  have hGt : G t = -log (log 2) := by
    simp only [hG, hmt, one_div, log_inv, neg_neg]
  have hms : r ^ n * (1 / 2) ≤ μFamily s F := by
    have h := OMA10799W.μFamily_ge hs0 hst.le ht1 F
    rwa [hmt, show s / t = r by rw [hs]; field_simp] at h
  have hLs : -log (μFamily s F) ≤ ε * n ^ 2 + log 2 := by
    have h1 : log (r ^ n * (1 / 2)) ≤ log (μFamily s F) :=
      log_le_log (by positivity) hms
    rw [log_mul (by positivity) (by norm_num), log_pow, hlogr, one_div, log_inv] at h1
    have h2 : (n:ℝ) * (ε * log n) ≤ n * (ε * n) := by
      gcongr; linarith
    nlinarith
  have hLs0 := hL0 s hs0 (lt_trans hst ht1)
  have hGs : G t - G s ≤ (4 + 4 / ε) * (log t - log s) := by
    have e1 : G t - G s = log (-log (μFamily s F)) - log (log 2) := by
      rw [hGt]; simp only [hG]; ring
    have h3 : ε * n ^ 2 + log 2 ≤ log 2 * ((1 + 2 * ε) * n ^ 2) := by
      have hsq : (1:ℝ) ≤ (n:ℝ) ^ 2 := by nlinarith
      nlinarith [mul_nonneg (mul_nonneg hε.le (sq_nonneg (n:ℝ))) (by linarith : (0:ℝ) ≤ 2 * log 2 - 1),
        mul_nonneg (by linarith : (0:ℝ) ≤ log 2) (by linarith : (0:ℝ) ≤ (n:ℝ) ^ 2 - 1)]
    have h4 : log (-log (μFamily s F)) ≤ log (log 2) + (log (1 + 2 * ε) + 2 * log n) := by
      have := log_le_log hLs0 (hLs.trans h3)
      rwa [log_mul (by positivity) (by positivity), log_mul (by positivity) (by positivity),
        log_pow] at this
    have h5 : log (1 + 2 * ε) ≤ 2 * ε := by
      have := Real.log_le_sub_one_of_pos (show 0 < 1 + 2 * ε by positivity); linarith
    have e2 : (4 + 4 / ε) * (log t - log s) = (4 * ε + 4) * log n := by
      rw [hlogs]; field_simp; ring
    rw [e1, e2]
    nlinarith
  -- conclude
  have hD : 0 < log t - log s := by rw [hlogs]; nlinarith
  have hmc := hm0 c hc0 hc1
  have hLc := hL0 c hc0 hc1
  have hf'c : f' c = edgeBoundary n c F / μFamily c F / -log (μFamily c F) := by
    simp only [hf']; ring
  have key : edgeBoundary n c F / μFamily c F / -log (μFamily c F) ≤ (4 + 4 / ε) * c⁻¹ := by
    rw [← hf'c]
    have : (log t - log s) * f' c ≤ (log t - log s) * ((4 + 4 / ε) * c⁻¹) := by
      rw [hceq]
      have hci : 0 < c⁻¹ := inv_pos.mpr hc0
      nlinarith
    exact le_of_mul_le_mul_left this hD
  rw [div_div, div_le_iff₀ (by positivity)] at key
  show edgeBoundary n c F ≤ (4 + 4 / ε) * log (1 / c) * (μFamily c F * logb c (μFamily c F) / c)
  have hlc0 : log c ≠ 0 := (log_neg hc0 hc1).ne
  have e3 : (4 + 4 / ε) * log (1 / c) * (μFamily c F * logb c (μFamily c F) / c) =
      (4 + 4 / ε) * c⁻¹ * (μFamily c F * -log (μFamily c F)) := by
    unfold logb; rw [one_div, log_inv]; field_simp
  rw [e3]; exact key
