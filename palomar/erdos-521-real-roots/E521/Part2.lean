/-
Copyright 2026 Ming-Chih Kao. Licensed under the Apache License, Version 2.0;
see the LICENSE file at the root of this repository.
-/
module

public import E521.Part1

/-! Part of the proof of Erdős 521 (see `E521/Part1.lean` for the port notes): sections C4 (RR0–RR5) of the
merged Left to Solve file `proofs/erdos-521.lean`. -/

@[expose] public section

-- ===== C4 =====
section S_C4

-- ===== RR0 =====

/-!
# Erdős 522 (real roots), part 0: Erdős's Littlewood–Offord bound

For signs `ε : ι → ℤˣ` and weights `a` with `|a i| ≥ 1` on a set `I` of size `M`, the number of sign
vectors with `∑ ε i a i` in a half-open interval of length `2` is at most `2^|ι| / √M`.
(Erdős 1945, via Sperner's theorem.)
-/

open Finset Real

noncomputable section S_RR0

namespace R522

/-- Signed sum. -/
def ssum {ι : Type*} [Fintype ι] (ε : ι → ℤˣ) (a : ι → ℝ) : ℝ := ∑ i, ((ε i : ℤ) : ℝ) * a i

lemma cb_sq (p : ℕ) : (Nat.centralBinom p : ℝ) ^ 2 * (2 * p + 1) ≤ 16 ^ p := by
  induction p with
  | zero => simp
  | succ p ih =>
    have h := Nat.succ_mul_centralBinom_succ p
    have hc : (Nat.centralBinom (p + 1) : ℝ) = 2 * (2 * p + 1) * Nat.centralBinom p / (p + 1) := by
      rw [eq_div_iff (by positivity)]
      have : ((p + 1 : ℕ) : ℝ) * Nat.centralBinom (p + 1) = 2 * (2 * p + 1) * Nat.centralBinom p := by
        exact_mod_cast h
      push_cast at this; linarith
    rw [hc, div_pow, div_mul_eq_mul_div]
    have hp : (0 : ℝ) < ((p : ℝ) + 1) ^ 2 := by positivity
    rw [div_le_iff₀ hp]
    have key : (2 * (p : ℝ) + 1) * (2 * ((p : ℝ) + 1) + 1) ≤ 4 * ((p : ℝ) + 1) ^ 2 := by nlinarith
    have e1 : (2 * (2 * (p : ℝ) + 1) * (Nat.centralBinom p : ℝ)) ^ 2 * (2 * ((p : ℝ) + 1) + 1)
        = 4 * (((Nat.centralBinom p : ℝ)) ^ 2 * (2 * p + 1)) * ((2 * p + 1) * (2 * ((p : ℝ) + 1) + 1)) := by
      ring
    push_cast
    rw [e1]
    have := mul_le_mul ih key (by positivity) (by positivity)
    calc 4 * (((Nat.centralBinom p : ℝ)) ^ 2 * (2 * p + 1)) * ((2 * p + 1) * (2 * ((p : ℝ) + 1) + 1))
        = 4 * ((((Nat.centralBinom p : ℝ)) ^ 2 * (2 * p + 1)) * ((2 * p + 1) * (2 * ((p : ℝ) + 1) + 1))) := by ring
      _ ≤ 4 * (16 ^ p * (4 * ((p : ℝ) + 1) ^ 2)) := by linarith
      _ = 16 ^ (p + 1) * ((p : ℝ) + 1) ^ 2 := by rw [pow_succ]; ring

lemma choose_half_sq (M : ℕ) : ((M.choose (M / 2) : ℕ) : ℝ) ^ 2 * M ≤ 4 ^ M := by
  obtain ⟨p, rfl | rfl⟩ := Nat.even_or_odd' M
  · have h2 : 2 * p / 2 = p := by omega
    rw [h2, ← Nat.centralBinom_eq_two_mul_choose]
    have := cb_sq p
    have h16 : (4 : ℝ) ^ (2 * p) = 16 ^ p := by rw [pow_mul]; norm_num
    rw [h16]; push_cast
    have : (0 : ℝ) ≤ (Nat.centralBinom p : ℝ) ^ 2 := by positivity
    nlinarith
  · have h2 : (2 * p + 1) / 2 = p := by omega
    rw [h2]
    have hsum : Nat.centralBinom (p + 1) = 2 * (2 * p + 1).choose p := by
      rw [Nat.centralBinom_eq_two_mul_choose, show 2 * (p + 1) = (2 * p + 1) + 1 by ring,
        Nat.choose_succ_succ, Nat.choose_symm_of_eq_add (show 2 * p + 1 = (p + 1) + p by omega)]
      ring
    have := cb_sq (p + 1)
    have hc : ((2 * p + 1).choose p : ℝ) = Nat.centralBinom (p + 1) / 2 := by
      rw [hsum]; push_cast; ring
    rw [hc]
    have h16 : (4 : ℝ) ^ (2 * p + 1) = 16 ^ (p + 1) / 4 := by
      rw [pow_succ, pow_mul, pow_succ]; ring
    rw [h16]; push_cast at this ⊢
    have : (0 : ℝ) ≤ (Nat.centralBinom (p + 1) : ℝ) ^ 2 := by positivity
    nlinarith

/-- The antichain step: with the outside signs fixed, the inside sign patterns giving a sum in
`[t, t + 2)` form an antichain. -/
lemma lo_fiber {κ : Type*} [Fintype κ] [DecidableEq κ] (a : κ → ℝ) (ha : ∀ i, 1 ≤ |a i|)
    (c t : ℝ) :
    ((univ.filter fun ε : κ → ℤˣ => t ≤ c + ssum ε a ∧ c + ssum ε a < t + 2).card)
      ≤ (Fintype.card κ).choose (Fintype.card κ / 2) := by
  classical
  -- sign of each weight
  set s : κ → ℤˣ := fun i => if 0 ≤ a i then 1 else -1 with hs
  have hsa : ∀ i, ((s i : ℤ) : ℝ) * a i = |a i| := by
    intro i; simp only [hs]; split_ifs with h
    · simp [abs_of_nonneg h]
    · simp [abs_of_neg (not_le.mp h)]
  set T : (κ → ℤˣ) → Finset κ := fun ε => univ.filter fun i => ε i = s i with hT
  have hval : ∀ (ε : κ → ℤˣ) i, ε i = s i ∨ ε i = -s i := by
    intro ε i
    rcases Int.units_eq_one_or (ε i) with h | h <;> rcases Int.units_eq_one_or (s i) with h' | h' <;>
      simp [h, h']
  have hTinj : Function.Injective T := by
    intro ε ε' h
    funext i
    have hi := congrArg (fun F => i ∈ F) h
    simp only [hT, mem_filter, mem_univ, true_and, eq_iff_iff] at hi
    rcases hval ε i with h1 | h1 <;> rcases hval ε' i with h2 | h2
    · rw [h1, h2]
    · exfalso; have := hi.mp h1; rw [this] at h2
      exact absurd h2 (by rcases Int.units_eq_one_or (s i) with h | h <;> simp [h])
    · exfalso; have := hi.mpr h2; rw [this] at h1
      exact absurd h1 (by rcases Int.units_eq_one_or (s i) with h | h <;> simp [h])
    · rw [h1, h2]
  -- sum formula: ssum ε a = 2 ∑_{T ε} |a| - ∑ |a|
  have hsum : ∀ ε : κ → ℤˣ, ssum ε a = 2 * ∑ i ∈ T ε, |a i| - ∑ i, |a i| := by
    intro ε
    unfold ssum
    have : ∀ i, ((ε i : ℤ) : ℝ) * a i = 2 * (if ε i = s i then |a i| else 0) - |a i| := by
      intro i
      rcases hval ε i with h | h
      · rw [if_pos h, h, hsa]; ring
      · rw [if_neg (by rw [h]; rcases Int.units_eq_one_or (s i) with h' | h' <;> simp [h']), h]
        push_cast; rw [neg_mul, hsa]; ring
    simp_rw [this]
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_ite, Finset.sum_const_zero, add_zero]
  set F := univ.filter fun ε : κ → ℤˣ => t ≤ c + ssum ε a ∧ c + ssum ε a < t + 2 with hF
  have hanti : IsAntichain (· ⊆ ·) (SetLike.coe (F.image T)) := by
    intro A hA B hB hAB hsub
    simp only [coe_image, Set.mem_image, mem_coe] at hA hB
    obtain ⟨ε, hε, rfl⟩ := hA
    obtain ⟨ε', hε', rfl⟩ := hB
    have hne : T ε ⊂ T ε' := Finset.ssubset_iff_subset_ne.mpr ⟨hsub, hAB⟩
    obtain ⟨j, hj', hj⟩ := Finset.exists_of_ssubset hne
    have hdiff : ∑ i ∈ T ε', |a i| - ∑ i ∈ T ε, |a i| ≥ 1 := by
      rw [← Finset.sum_sdiff hsub]
      have : |a j| ≤ ∑ i ∈ T ε' \ T ε, |a i| :=
        Finset.single_le_sum (f := fun i => |a i|) (fun i _ => abs_nonneg _)
          (Finset.mem_sdiff.mpr ⟨hj', hj⟩)
      linarith [ha j]
    simp only [hF, mem_filter, mem_univ, true_and] at hε hε'
    rw [hsum] at hε hε'
    linarith [hε.1, hε'.2]
  have := hanti.sperner
  rwa [Finset.card_image_of_injective _ hTinj] at this

/-- **Erdős's Littlewood–Offord bound.** -/
theorem lo_interval {ι : Type*} [Fintype ι] [DecidableEq ι] (a : ι → ℝ) (I : Finset ι)
    (hI : ∀ i ∈ I, 1 ≤ |a i|) (hIne : I.Nonempty) (t : ℝ) :
    ((univ.filter fun ε : ι → ℤˣ => t ≤ ssum ε a ∧ ssum ε a < t + 2).card : ℝ)
      ≤ 2 ^ Fintype.card ι / √(I.card) := by
  classical
  set p : ι → Prop := fun i => i ∈ I
  let e := Equiv.piEquivPiSubtypeProd p (fun _ => ℤˣ)
  let κ := {i // p i}
  let ν := {i // ¬ p i}
  have hsplit : ∀ ε : ι → ℤˣ, ssum ε a = (∑ j : ν, (((e ε).2 j : ℤ) : ℝ) * a j)
      + ssum (e ε).1 (fun i : κ => a i) := by
    intro ε
    unfold ssum
    rw [add_comm]
    convert (Fintype.sum_subtype_add_sum_subtype p (fun i => ((ε i : ℤ) : ℝ) * a i)).symm <;> rfl
  -- count via the equivalence
  have hcount : ((univ.filter fun ε : ι → ℤˣ => t ≤ ssum ε a ∧ ssum ε a < t + 2).card : ℝ)
      = ∑ o : ν → ℤˣ, ((univ.filter fun ε : κ → ℤˣ =>
          t ≤ (∑ j : ν, ((o j : ℤ) : ℝ) * a j) + ssum ε (fun i : κ => a i) ∧
          (∑ j : ν, ((o j : ℤ) : ℝ) * a j) + ssum ε (fun i : κ => a i) < t + 2).card : ℝ) := by
    rw [Finset.card_filter]
    push_cast
    rw [← e.symm.sum_comp, Fintype.sum_prod_type, Finset.sum_comm]
    refine Finset.sum_congr rfl (fun o _ => ?_)
    rw [Finset.card_filter]; push_cast
    refine Finset.sum_congr rfl (fun ε _ => ?_)
    simp only [hsplit, Equiv.apply_symm_apply]
  have hfib : ∀ o : ν → ℤˣ, ((univ.filter fun ε : κ → ℤˣ =>
          t ≤ (∑ j : ν, ((o j : ℤ) : ℝ) * a j) + ssum ε (fun i : κ => a i) ∧
          (∑ j : ν, ((o j : ℤ) : ℝ) * a j) + ssum ε (fun i : κ => a i) < t + 2).card : ℝ)
        ≤ (Fintype.card κ).choose (Fintype.card κ / 2) := by
    intro o
    exact_mod_cast lo_fiber (fun i : κ => a i) (fun i => hI i i.2) _ t
  have hκ : Fintype.card κ = I.card := by
    simp only [κ, p]; exact Fintype.card_coe I
  have hν : Fintype.card (ν → ℤˣ) * 2 ^ I.card = 2 ^ Fintype.card ι := by
    rw [Fintype.card_fun, Fintype.card_units_int, ← hκ, ← pow_add]
    congr 1
    rw [add_comm, Fintype.card_subtype_compl]
    have := Fintype.card_subtype_le p
    show Fintype.card {x // p x} + _ = _
    omega
  rw [hcount]
  have hM : (0 : ℝ) < I.card := by exact_mod_cast hIne.card_pos
  calc _ ≤ ∑ _o : ν → ℤˣ, (((Fintype.card κ).choose (Fintype.card κ / 2) : ℕ) : ℝ) :=
        Finset.sum_le_sum (fun o _ => hfib o)
    _ = Fintype.card (ν → ℤˣ) * ((I.card.choose (I.card / 2) : ℕ) : ℝ) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hκ]
    _ ≤ 2 ^ Fintype.card ι / √(I.card) := by
        rw [le_div_iff₀ (Real.sqrt_pos.mpr hM)]
        have h1 := choose_half_sq I.card
        have hsq : ((I.card.choose (I.card / 2) : ℕ) : ℝ) * √(I.card) ≤ 2 ^ I.card := by
          have h0 : 0 ≤ ((I.card.choose (I.card / 2) : ℕ) : ℝ) * √(I.card) := by positivity
          have : (((I.card.choose (I.card / 2) : ℕ) : ℝ) * √(I.card)) ^ 2 ≤ (2 ^ I.card) ^ 2 := by
            rw [mul_pow, Real.sq_sqrt hM.le, ← pow_mul, mul_comm I.card 2, pow_mul]; norm_num
            linarith
          exact (pow_le_pow_iff_left₀ h0 (by positivity) (by norm_num)).mp this
        have hν' : (Fintype.card (ν → ℤˣ) : ℝ) * 2 ^ I.card = 2 ^ Fintype.card ι := by
          exact_mod_cast hν
        calc (Fintype.card (ν → ℤˣ) : ℝ) * ((I.card.choose (I.card / 2) : ℕ) : ℝ) * √(I.card)
            = (Fintype.card (ν → ℤˣ) : ℝ) * (((I.card.choose (I.card / 2) : ℕ) : ℝ) * √(I.card)) := by ring
          _ ≤ (Fintype.card (ν → ℤˣ) : ℝ) * 2 ^ I.card := by gcongr
          _ = _ := hν'

end R522

end S_RR0
-- ===== RR2 =====

/-!
# Erdős 522 (real roots), part 2: averages over sign vectors

`EE f` is the average of `f` over `ε : ι → ℤˣ`, and `PP S` the proportion of sign vectors in `S`.
Markov and Chebyshev, second moments of signed sums, a weighted Cauchy–Schwarz bound, and
independence of functions of disjoint coordinate sets.
-/

open Finset Real

noncomputable section S_RR2

namespace R522

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Average over sign vectors. -/
def EE (f : (ι → ℤˣ) → ℝ) : ℝ := (∑ ε, f ε) / 2 ^ Fintype.card ι

open scoped Classical in
/-- Proportion of sign vectors satisfying `S`. -/
def PP (S : (ι → ℤˣ) → Prop) : ℝ := EE fun ε => if S ε then 1 else 0

lemma PP_eq (S : (ι → ℤˣ) → Prop) [DecidablePred S] :
    PP S = EE fun ε => if S ε then (1 : ℝ) else 0 := by
  unfold PP; congr 1; ext ε; split_ifs <;> simp_all

lemma card_signs : (Fintype.card (ι → ℤˣ) : ℝ) = 2 ^ Fintype.card ι := by
  rw [Fintype.card_fun, Fintype.card_units_int]; push_cast; rfl

lemma EE_const (c : ℝ) : EE (ι := ι) (fun _ => c) = c := by
  unfold EE
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, card_signs]
  field_simp

lemma EE_add (f g : (ι → ℤˣ) → ℝ) : EE (fun ε => f ε + g ε) = EE f + EE g := by
  unfold EE; rw [Finset.sum_add_distrib, add_div]

lemma EE_sub (f g : (ι → ℤˣ) → ℝ) : EE (fun ε => f ε - g ε) = EE f - EE g := by
  unfold EE; rw [Finset.sum_sub_distrib, sub_div]

lemma EE_smul (c : ℝ) (f : (ι → ℤˣ) → ℝ) : EE (fun ε => c * f ε) = c * EE f := by
  unfold EE; rw [← Finset.mul_sum, mul_div_assoc]

lemma EE_sum {κ : Type*} (s : Finset κ) (f : κ → (ι → ℤˣ) → ℝ) :
    EE (fun ε => ∑ k ∈ s, f k ε) = ∑ k ∈ s, EE (f k) := by
  unfold EE; rw [Finset.sum_comm, Finset.sum_div]

lemma EE_mono {f g : (ι → ℤˣ) → ℝ} (h : ∀ ε, f ε ≤ g ε) : EE f ≤ EE g := by
  unfold EE; gcongr with ε; exact h ε

lemma EE_nonneg {f : (ι → ℤˣ) → ℝ} (h : ∀ ε, 0 ≤ f ε) : 0 ≤ EE f := by
  have := EE_mono (f := fun _ => (0 : ℝ)) h
  rwa [EE_const] at this

lemma PP_nonneg (S : (ι → ℤˣ) → Prop) : 0 ≤ PP S := by
  classical
  unfold PP; exact EE_nonneg (fun ε => by split_ifs <;> norm_num)

lemma PP_le_one (S : (ι → ℤˣ) → Prop) : PP S ≤ 1 := by
  classical
  unfold PP
  have := EE_mono (f := fun ε => if S ε then (1 : ℝ) else 0) (g := fun _ => 1)
    (fun ε => by split_ifs <;> norm_num)
  rwa [EE_const] at this

lemma PP_mono {S T : (ι → ℤˣ) → Prop} (h : ∀ ε, S ε → T ε) : PP S ≤ PP T := by
  classical
  unfold PP
  exact EE_mono (fun ε => by
    by_cases hs : S ε
    · rw [if_pos hs, if_pos (h ε hs)]
    · rw [if_neg hs]; split_ifs <;> norm_num)

lemma PP_or_le (S T : (ι → ℤˣ) → Prop) : PP (fun ε => S ε ∨ T ε) ≤ PP S + PP T := by
  classical
  unfold PP
  rw [← EE_add]
  exact EE_mono (fun ε => by split_ifs <;> simp_all)

lemma PP_exists_le {κ : Type*} (s : Finset κ) (S : κ → (ι → ℤˣ) → Prop) :
    PP (fun ε => ∃ k ∈ s, S k ε) ≤ ∑ k ∈ s, PP (S k) := by
  classical
  unfold PP
  rw [← EE_sum]
  refine EE_mono (fun ε => ?_)
  split_ifs with h
  · obtain ⟨k, hk, hS⟩ := h
    calc (1 : ℝ) = if S k ε then 1 else 0 := by rw [if_pos hS]
      _ ≤ ∑ j ∈ s, if S j ε then (1 : ℝ) else 0 :=
          Finset.single_le_sum (f := fun j => if S j ε then (1 : ℝ) else 0)
            (fun j _ => by split_ifs <;> norm_num) hk
  · exact Finset.sum_nonneg (fun j _ => by split_ifs <;> norm_num)

lemma PP_compl (S : (ι → ℤˣ) → Prop) : PP (fun ε => ¬ S ε) = 1 - PP S := by
  classical
  unfold PP
  have key : ∀ g : (ι → ℤˣ) → ℝ, (∀ ε, g ε = 1 - (if S ε then 1 else 0)) →
      EE g = 1 - EE (fun ε => if S ε then (1 : ℝ) else 0) := by
    intro g hg
    rw [show g = fun ε => 1 - (if S ε then (1 : ℝ) else 0) from funext hg, EE_sub, EE_const]
  exact key _ (fun ε => by by_cases h : S ε <;> simp [h])

/-- Markov. -/
lemma markov {f : (ι → ℤˣ) → ℝ} (hf : ∀ ε, 0 ≤ f ε) {t : ℝ} (ht : 0 < t) :
    PP (fun ε => t ≤ f ε) ≤ EE f / t := by
  classical
  rw [le_div_iff₀ ht]
  unfold PP
  rw [mul_comm, ← EE_smul]
  exact EE_mono (fun ε => by split_ifs with h <;> nlinarith [hf ε])

/-- Markov with indicators bounded above by a function. -/
lemma PP_le_EE {S : (ι → ℤˣ) → Prop} {f : (ι → ℤˣ) → ℝ} (hf : ∀ ε, 0 ≤ f ε)
    (h : ∀ ε, S ε → 1 ≤ f ε) : PP S ≤ EE f := by
  classical
  unfold PP
  exact EE_mono (fun ε => by split_ifs with hs; exacts [h ε hs, hf ε])

/-- Chebyshev. -/
lemma chebyshev (f : (ι → ℤˣ) → ℝ) {t : ℝ} (ht : 0 < t) :
    PP (fun ε => t ≤ |f ε|) ≤ EE (fun ε => f ε ^ 2) / t ^ 2 := by
  have h := markov (f := fun ε => f ε ^ 2) (fun ε => sq_nonneg _) (pow_pos ht 2)
  refine (PP_mono (fun ε hε => ?_)).trans h
  have : t ^ 2 ≤ |f ε| ^ 2 := pow_le_pow_left₀ ht.le hε 2
  rwa [sq_abs] at this

/-! ### Flips and first moments -/

/-- Flip coordinate `i`. -/
def flipAt (i : ι) (ε : ι → ℤˣ) : ι → ℤˣ := Function.update ε i (-ε i)

lemma flipAt_invol (i : ι) : Function.Involutive (flipAt i) := by
  intro ε; funext j; unfold flipAt
  by_cases h : j = i
  · subst h; simp
  · simp [Function.update_of_ne h]

lemma sum_flip {M : Type*} [AddCommMonoid M] (i : ι) (f : (ι → ℤˣ) → M) :
    ∑ ε, f (flipAt i ε) = ∑ ε, f ε :=
  Equiv.sum_comp (flipAt_invol i).toPerm f

lemma EE_coord (i : ι) : EE (ι := ι) (fun ε => ((ε i : ℤ) : ℝ)) = 0 := by
  unfold EE
  have h := sum_flip i (fun ε => ((ε i : ℤ) : ℝ))
  simp only [flipAt, Function.update_self, Units.val_neg, Int.cast_neg, Finset.sum_neg_distrib] at h
  have : ∑ ε : ι → ℤˣ, ((ε i : ℤ) : ℝ) = 0 := by linarith
  rw [this, zero_div]

lemma EE_coord_mul (i j : ι) (hij : i ≠ j) :
    EE (ι := ι) (fun ε => ((ε i : ℤ) : ℝ) * ((ε j : ℤ) : ℝ)) = 0 := by
  unfold EE
  have h := sum_flip i (fun ε => ((ε i : ℤ) : ℝ) * ((ε j : ℤ) : ℝ))
  simp only [flipAt, Function.update_self, Function.update_of_ne hij.symm, Units.val_neg,
    Int.cast_neg, neg_mul, Finset.sum_neg_distrib] at h
  have : ∑ ε : ι → ℤˣ, ((ε i : ℤ) : ℝ) * ((ε j : ℤ) : ℝ) = 0 := by linarith
  rw [this, zero_div]

lemma unit_sq (u : ℤˣ) : ((u : ℤ) : ℝ) * ((u : ℤ) : ℝ) = 1 := by
  rcases Int.units_eq_one_or u with h | h <;> simp [h]

/-- Second mixed moment of signed sums. -/
lemma EE_ssum_mul (c d : ι → ℝ) :
    EE (fun ε => ssum ε c * ssum ε d) = ∑ i, c i * d i := by
  unfold ssum
  have : ∀ ε : ι → ℤˣ, (∑ i, ((ε i : ℤ) : ℝ) * c i) * (∑ j, ((ε j : ℤ) : ℝ) * d j)
      = ∑ i, ∑ j, (c i * d j) * (((ε i : ℤ) : ℝ) * ((ε j : ℤ) : ℝ)) := by
    intro ε; rw [Finset.sum_mul_sum]; refine Finset.sum_congr rfl (fun i _ =>
      Finset.sum_congr rfl (fun j _ => by ring))
  simp_rw [this]
  rw [EE_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [EE_sum, Finset.sum_eq_single i]
  · rw [EE_smul]
    simp_rw [unit_sq]; rw [EE_const, mul_one]
  · intro j _ hj; rw [EE_smul, EE_coord_mul i j (Ne.symm hj), mul_zero]
  · simp

lemma EE_ssum_sq (c : ι → ℝ) : EE (fun ε => ssum ε c ^ 2) = ∑ i, c i ^ 2 := by
  have := EE_ssum_mul c c
  simp_rw [sq]; exact this

/-- Chebyshev for signed sums. -/
lemma cheb_ssum (c : ι → ℝ) {t : ℝ} (ht : 0 < t) :
    PP (fun ε => t ≤ |ssum ε c|) ≤ (∑ i, c i ^ 2) / t ^ 2 := by
  have := chebyshev (fun ε => ssum ε c) ht
  rwa [EE_ssum_sq] at this

/-- Weighted Cauchy–Schwarz: if `E X_j² ≤ μ_j²` then `E (∑ w_j |X_j|)² ≤ (∑ w_j μ_j)²`. -/
lemma EE_wsum_sq {κ : Type*} (s : Finset κ) (w μ : κ → ℝ) (X : κ → (ι → ℤˣ) → ℝ)
    (hw : ∀ k ∈ s, 0 ≤ w k) (hμ : ∀ k ∈ s, 0 < μ k) (hX : ∀ k ∈ s, EE (fun ε => X k ε ^ 2) ≤ μ k ^ 2) :
    EE (fun ε => (∑ k ∈ s, w k * |X k ε|) ^ 2) ≤ (∑ k ∈ s, w k * μ k) ^ 2 := by
  set W := ∑ k ∈ s, w k * μ k with hW
  have hW0 : 0 ≤ W := Finset.sum_nonneg (fun k hk => mul_nonneg (hw k hk) (hμ k hk).le)
  have hpt : ∀ ε, (∑ k ∈ s, w k * |X k ε|) ^ 2 ≤ W * ∑ k ∈ s, w k * (X k ε ^ 2 / μ k) := by
    intro ε
    have := Finset.sum_mul_sq_le_sq_mul_sq s (fun k => √(w k * μ k)) (fun k => √(w k / μ k) * |X k ε|)
    have e1 : ∀ k ∈ s, √(w k * μ k) * (√(w k / μ k) * |X k ε|) = w k * |X k ε| := by
      intro k hk
      rw [← mul_assoc, ← Real.sqrt_mul (mul_nonneg (hw k hk) (hμ k hk).le)]
      have : w k * μ k * (w k / μ k) = w k ^ 2 := by field_simp [(hμ k hk).ne']
      rw [this, Real.sqrt_sq (hw k hk)]
    have e2 : ∀ k ∈ s, √(w k * μ k) ^ 2 = w k * μ k := fun k hk =>
      Real.sq_sqrt (mul_nonneg (hw k hk) (hμ k hk).le)
    have e3 : ∀ k ∈ s, (√(w k / μ k) * |X k ε|) ^ 2 = w k * (X k ε ^ 2 / μ k) := by
      intro k hk
      rw [mul_pow, Real.sq_sqrt (div_nonneg (hw k hk) (hμ k hk).le), sq_abs]; ring
    rw [Finset.sum_congr rfl e1, Finset.sum_congr rfl e2, Finset.sum_congr rfl e3] at this
    exact this
  calc EE (fun ε => (∑ k ∈ s, w k * |X k ε|) ^ 2)
      ≤ EE (fun ε => W * ∑ k ∈ s, w k * (X k ε ^ 2 / μ k)) := EE_mono hpt
    _ = W * ∑ k ∈ s, w k * (EE (fun ε => X k ε ^ 2) / μ k) := by
        rw [EE_smul, EE_sum]; congr 1
        refine Finset.sum_congr rfl (fun k _ => ?_)
        rw [show (fun ε => w k * (X k ε ^ 2 / μ k)) = (fun ε => (w k / μ k) * X k ε ^ 2) by
          ext ε; ring, EE_smul]; ring
    _ ≤ W * ∑ k ∈ s, w k * (μ k ^ 2 / μ k) := by
        gcongr with k hk
        · exact hw k hk
        · exact (hμ k hk).le
        · exact hX k hk
    _ = W ^ 2 := by
        rw [sq, hW]; congr 1
        refine Finset.sum_congr rfl (fun k hk => ?_)
        field_simp [(hμ k hk).ne']

/-! ### Independence of disjoint coordinate sets -/

/-- `f` only depends on the coordinates in `A`. -/
def DepOn (A : Finset ι) (f : (ι → ℤˣ) → ℝ) : Prop :=
  ∀ ε ε' : ι → ℤˣ, (∀ i ∈ A, ε i = ε' i) → f ε = f ε'

lemma EE_mul_indep (A : Finset ι) (f g : (ι → ℤˣ) → ℝ) (hf : DepOn A f)
    (hg : DepOn Aᶜ g) : EE (fun ε => f ε * g ε) = EE f * EE g := by
  classical
  set p : ι → Prop := fun i => i ∈ A
  let e := Equiv.piEquivPiSubtypeProd p (fun _ => ℤˣ)
  -- glue two partial sign vectors
  let glue : ({i // p i} → ℤˣ) → ({i // ¬ p i} → ℤˣ) → (ι → ℤˣ) := fun α β => e.symm (α, β)
  have hglue1 : ∀ α β, ∀ i (hi : p i), glue α β i = α ⟨i, hi⟩ := by
    intro α β i hi; simp [glue, e, Equiv.piEquivPiSubtypeProd, hi]
  have hglue2 : ∀ α β, ∀ i (hi : ¬ p i), glue α β i = β ⟨i, hi⟩ := by
    intro α β i hi; simp [glue, e, Equiv.piEquivPiSubtypeProd, hi]
  -- choose a reference point
  let β0 : {i // ¬ p i} → ℤˣ := fun _ => 1
  let α0 : {i // p i} → ℤˣ := fun _ => 1
  have hf' : ∀ α β, f (glue α β) = f (glue α β0) := by
    intro α β; apply hf; intro i hi
    rw [hglue1 α β i hi, hglue1 α β0 i hi]
  have hg' : ∀ α β, g (glue α β) = g (glue α0 β) := by
    intro α β; apply hg; intro i hi
    have hi' : ¬ p i := by simpa [p] using hi
    rw [hglue2 α β i hi', hglue2 α0 β i hi']
  have hsum : ∀ F : (ι → ℤˣ) → ℝ, ∑ ε, F ε = ∑ α, ∑ β, F (glue α β) := by
    intro F
    rw [← e.symm.sum_comp, Fintype.sum_prod_type]
  have hcard : (2 : ℝ) ^ Fintype.card ι
      = (2 : ℝ) ^ Fintype.card {i // p i} * (2 : ℝ) ^ Fintype.card {i // ¬ p i} := by
    rw [← pow_add, Fintype.card_subtype_compl]
    congr 1; have := Fintype.card_subtype_le p; omega
  have hA : ∑ ε, f ε = (∑ α, f (glue α β0)) * 2 ^ Fintype.card {i // ¬ p i} := by
    rw [hsum]; simp_rw [hf']
    rw [Finset.sum_mul]; congr 1; ext α
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_comm]
    congr 1
    rw [Fintype.card_fun, Fintype.card_units_int]; push_cast; rfl
  have hB : ∑ ε, g ε = (∑ β, g (glue α0 β)) * 2 ^ Fintype.card {i // p i} := by
    rw [hsum, Finset.sum_comm]; simp_rw [hg']
    rw [Finset.sum_mul]; congr 1; ext β
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_comm]
    congr 1
    rw [Fintype.card_fun, Fintype.card_units_int]; push_cast; rfl
  have hAB : ∑ ε, f ε * g ε = (∑ α, f (glue α β0)) * (∑ β, g (glue α0 β)) := by
    rw [hsum]
    simp_rw [hf', hg']
    rw [Finset.sum_mul_sum]
  unfold EE
  rw [hAB, hA, hB, hcard]
  field_simp

end R522

end S_RR2

-- ===== RR3 =====

/-!
# Erdős 522 (real roots), part 3: a two-point CLT by Fourier inversion

For Schwartz test functions `ψ₁, ψ₂` and unit weight vectors `a, b` with correlation `ρ`,
the sign-vector average of `ψ₁(∑ ε a) ψ₂(∑ ε b)` and the Gaussian average of `ψ₁(Z₁) ψ₂(ρ Z₁ + σ Z₂)`
(`σ² = 1 - ρ²`) are both `∫∫ 𝓕ψ₁ 𝓕ψ₂ · K`, with `K` a cosine product resp. a Gaussian; their
difference is at most `16 (2π)⁴ (M₄ψ₁ M₀ψ₂ ∑ a⁴ + M₀ψ₁ M₄ψ₂ ∑ b⁴)`.
-/

open Finset Real MeasureTheory FourierTransform ProbabilityTheory

noncomputable section S_RR3

namespace R522

lemma schwartz_inv (ψ : SchwartzMap ℝ ℂ) (x : ℝ) :
    ψ x = ∫ ξ : ℝ, Complex.exp (↑(2 * π * ξ * x) * Complex.I) * 𝓕 (ψ : ℝ → ℂ) ξ := by
  have h := ψ.continuous.fourierInv_fourier_eq ψ.integrable (by
    rw [← SchwartzMap.fourier_coe]; exact (𝓕 ψ).integrable)
  have := congrFun h x
  rw [← this, Real.fourierInv_eq']
  simp only [smul_eq_mul, RCLike.inner_apply, conj_trivial]
  congr 1; ext ξ; congr 3; push_cast; ring

lemma fourier_integrable (ψ : SchwartzMap ℝ ℂ) : Integrable (𝓕 (ψ : ℝ → ℂ)) := by
  rw [← SchwartzMap.fourier_coe]; exact (𝓕 ψ).integrable

lemma fourier_continuous (ψ : SchwartzMap ℝ ℂ) : Continuous (𝓕 (ψ : ℝ → ℂ)) := by
  rw [← SchwartzMap.fourier_coe]; exact (𝓕 ψ).continuous

lemma integrable_exp_mul_fourier (ψ : SchwartzMap ℝ ℂ) (x : ℝ) :
    Integrable (fun ξ : ℝ => Complex.exp (↑(2 * π * ξ * x) * Complex.I) * 𝓕 (ψ : ℝ → ℂ) ξ) := by
  refine (fourier_integrable ψ).bdd_mul (c := 1) (by fun_prop) ?_
  refine Filter.Eventually.of_forall (fun ξ => ?_)
  rw [Complex.norm_exp_ofReal_mul_I]

/-- Fourier moments. -/
def Mom (k : ℕ) (ψ : SchwartzMap ℝ ℂ) : ℝ := ∫ u : ℝ, |u| ^ k * ‖𝓕 (ψ : ℝ → ℂ) u‖

lemma integrable_mom (k : ℕ) (ψ : SchwartzMap ℝ ℂ) :
    Integrable (fun u : ℝ => |u| ^ k * ‖𝓕 (ψ : ℝ → ℂ) u‖) := by
  have := (𝓕 ψ).integrable_pow_mul volume k
  rw [SchwartzMap.fourier_coe] at this
  simpa [Real.norm_eq_abs] using this

lemma mom_nonneg (k : ℕ) (ψ : SchwartzMap ℝ ℂ) : 0 ≤ Mom k ψ :=
  integral_nonneg (fun u => by positivity)

lemma mom_zero (ψ : SchwartzMap ℝ ℂ) : Mom 0 ψ = ∫ u : ℝ, ‖𝓕 (ψ : ℝ → ℂ) u‖ := by
  simp [Mom]

/-! ### The sign-vector side -/

lemma sum_units_exp (ξ c : ℝ) :
    ∑ u : ℤˣ, Complex.exp (↑(2 * π * ξ * (((u : ℤ) : ℝ) * c)) * Complex.I)
      = 2 * (Real.cos (2 * π * ξ * c) : ℂ) := by
  rw [show (Finset.univ : Finset ℤˣ) = {1, -1} from by decide]
  rw [Finset.sum_pair (by decide)]
  simp only [Units.val_one, Int.cast_one, one_mul, Units.val_neg, Int.cast_neg, neg_mul]
  rw [Complex.ofReal_cos, Complex.cos]
  push_cast
  ring_nf

lemma sum_signs_exp {ι : Type*} [Fintype ι] [DecidableEq ι] (c : ι → ℝ) (ξ : ℝ) :
    ∑ b : ι → ℤˣ, Complex.exp (↑(2 * π * ξ * ∑ i, ((b i : ℤ) : ℝ) * c i) * Complex.I)
      = ∏ i, 2 * (Real.cos (2 * π * ξ * c i) : ℂ) := by
  have : ∀ b : ι → ℤˣ, Complex.exp (↑(2 * π * ξ * ∑ i, ((b i : ℤ) : ℝ) * c i) * Complex.I)
      = ∏ i, Complex.exp (↑(2 * π * ξ * (((b i : ℤ) : ℝ) * c i)) * Complex.I) := by
    intro b
    rw [← Complex.exp_sum]
    congr 1
    rw [← Finset.sum_mul]
    congr 1
    push_cast
    rw [Finset.mul_sum]
  simp_rw [this]
  rw [← Fintype.prod_sum (fun i (u : ℤˣ) =>
    Complex.exp (↑(2 * π * ξ * (((u : ℤ) : ℝ) * c i)) * Complex.I))]
  simp_rw [sum_units_exp]

/-- **Two-point identity on the sign side.** -/
theorem avg_two {ι : Type*} [Fintype ι] [DecidableEq ι] (ψ₁ ψ₂ : SchwartzMap ℝ ℂ)
    (c d : ι → ℝ) :
    (∑ b : ι → ℤˣ, ψ₁ (ssum b c) * ψ₂ (ssum b d)) / 2 ^ Fintype.card ι
      = ∫ u : ℝ, ∫ v : ℝ, 𝓕 (ψ₁ : ℝ → ℂ) u * 𝓕 (ψ₂ : ℝ → ℂ) v *
          ∏ i, (Real.cos (2 * π * (u * c i + v * d i)) : ℂ) := by
  set F₁ := 𝓕 (ψ₁ : ℝ → ℂ)
  set F₂ := 𝓕 (ψ₂ : ℝ → ℂ)
  have hprod : ∀ x y : ℝ, ψ₁ x * ψ₂ y = ∫ u : ℝ, ∫ v : ℝ,
      Complex.exp (↑(2 * π * u * x) * Complex.I) * Complex.exp (↑(2 * π * v * y) * Complex.I) *
        (F₁ u * F₂ v) := by
    intro x y
    rw [schwartz_inv ψ₁ x, schwartz_inv ψ₂ y, ← integral_mul_const]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun u => ?_))
    simp only
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun v => ?_))
    simp only; ring
  have hinner : ∀ (x y u : ℝ), Integrable (fun v : ℝ =>
      Complex.exp (↑(2 * π * u * x) * Complex.I) * Complex.exp (↑(2 * π * v * y) * Complex.I) *
        (F₁ u * F₂ v)) := by
    intro x y u
    have := (integrable_exp_mul_fourier ψ₂ y).const_mul
      (Complex.exp (↑(2 * π * u * x) * Complex.I) * F₁ u)
    refine this.congr (Filter.Eventually.of_forall (fun v => ?_))
    simp only; ring
  have hinner_eval : ∀ (x y u : ℝ), ∫ v : ℝ,
      Complex.exp (↑(2 * π * u * x) * Complex.I) * Complex.exp (↑(2 * π * v * y) * Complex.I) *
        (F₁ u * F₂ v) = Complex.exp (↑(2 * π * u * x) * Complex.I) * F₁ u * ψ₂ y := by
    intro x y u
    rw [schwartz_inv ψ₂ y, ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun v => ?_))
    simp only; ring
  have houter : ∀ x y : ℝ, Integrable (fun u : ℝ => ∫ v : ℝ,
      Complex.exp (↑(2 * π * u * x) * Complex.I) * Complex.exp (↑(2 * π * v * y) * Complex.I) *
        (F₁ u * F₂ v)) := by
    intro x y
    simp_rw [hinner_eval x y]
    exact (integrable_exp_mul_fourier ψ₁ x).mul_const _
  simp_rw [hprod]
  rw [← integral_finsetSum _ (fun b _ => houter _ _)]
  rw [div_eq_mul_inv, mul_comm, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun u => ?_))
  simp only
  rw [← integral_finsetSum _ (fun b _ => hinner _ _ u)]
  rw [← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun v => ?_))
  simp only
  have hc : ∀ b : ι → ℤˣ, Complex.exp (↑(2 * π * u * ssum b c) * Complex.I) *
      Complex.exp (↑(2 * π * v * ssum b d) * Complex.I)
      = Complex.exp (↑(2 * π * ∑ i, ((b i : ℤ) : ℝ) * (u * c i + v * d i)) * Complex.I) := by
    intro b
    unfold ssum
    rw [← Complex.exp_add]; congr 1
    push_cast
    simp only [Finset.mul_sum, mul_add, Finset.sum_add_distrib]
    rw [← add_mul]; congr 1
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun i _ => by ring)
  simp_rw [← mul_assoc, hc]
  have hs := sum_signs_exp (fun i => u * c i + v * d i) 1
  simp only [mul_one] at hs
  rw [← Finset.sum_mul, ← Finset.sum_mul, hs, Finset.prod_mul_distrib]
  simp only [Finset.prod_const, Finset.card_univ]
  field_simp

/-! ### The Gaussian side -/

/-- Fubini for a probability measure. -/
theorem fub_two {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X Y : Ω → ℝ) (hX : Measurable X) (hY : Measurable Y) (ψ₁ ψ₂ : SchwartzMap ℝ ℂ) :
    ∫ ω, ψ₁ (X ω) * ψ₂ (Y ω) ∂μ = ∫ u : ℝ, ∫ v : ℝ, 𝓕 (ψ₁ : ℝ → ℂ) u * 𝓕 (ψ₂ : ℝ → ℂ) v *
      ∫ ω, Complex.exp (↑(2 * π * (u * X ω + v * Y ω)) * Complex.I) ∂μ := by
  set F₁ := 𝓕 (ψ₁ : ℝ → ℂ)
  set F₂ := 𝓕 (ψ₂ : ℝ → ℂ)
  have hF₁ := fourier_integrable ψ₁
  have hF₂ := fourier_integrable ψ₂
  have cF₁ := fourier_continuous ψ₁
  have cF₂ := fourier_continuous ψ₂
  obtain ⟨C₂, hC₂⟩ : ∃ C, ∀ y, ‖ψ₂ y‖ ≤ C := ⟨SchwartzMap.seminorm ℝ 0 0 ψ₂, fun y => by
    have := ψ₂.le_seminorm ℝ 0 0 y; simpa [norm_iteratedFDeriv_zero] using this⟩
  -- step 1: expand `ψ₁` and swap
  have step1 : ∀ ω, ψ₁ (X ω) * ψ₂ (Y ω)
      = ∫ u : ℝ, Complex.exp (↑(2 * π * u * X ω) * Complex.I) * F₁ u * ψ₂ (Y ω) := by
    intro ω; rw [schwartz_inv ψ₁, ← integral_mul_const]
  have int1 : Integrable (Function.uncurry fun (ω : Ω) (u : ℝ) =>
      Complex.exp (↑(2 * π * u * X ω) * Complex.I) * F₁ u * ψ₂ (Y ω)) (μ.prod volume) := by
    refine Integrable.mono' ((integrable_const C₂).mul_prod hF₁.norm) ?_ ?_
    · have m1 : Measurable (fun p : Ω × ℝ => (X p.1, p.2, Y p.1)) :=
        (hX.comp measurable_fst).prodMk (measurable_snd.prodMk (hY.comp measurable_fst))
      have c1 : Continuous (fun q : ℝ × ℝ × ℝ =>
          Complex.exp (↑(2 * π * q.2.1 * q.1) * Complex.I) * F₁ q.2.1 * ψ₂ q.2.2) :=
        ((by fun_prop : Continuous fun (q : ℝ × ℝ × ℝ) =>
          Complex.exp (↑(2 * π * q.2.1 * q.1) * Complex.I)).mul (cF₁.comp (by fun_prop))).mul
          (ψ₂.continuous.comp (by fun_prop))
      exact (c1.measurable.comp m1).aestronglyMeasurable
    · refine Filter.Eventually.of_forall (fun p => ?_)
      simp only [Function.uncurry, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
      rw [mul_comm]; exact mul_le_mul_of_nonneg_right (hC₂ _) (norm_nonneg _)
  have hL : ∫ ω, ψ₁ (X ω) * ψ₂ (Y ω) ∂μ
      = ∫ u : ℝ, F₁ u * ∫ ω, Complex.exp (↑(2 * π * u * X ω) * Complex.I) * ψ₂ (Y ω) ∂μ := by
    simp_rw [step1]
    rw [integral_integral_swap int1]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun u => ?_))
    simp only
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun ω => ?_))
    simp only; ring
  rw [hL]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun u => ?_))
  simp only
  -- step 2: expand `ψ₂` and swap
  have step2 : ∀ ω, Complex.exp (↑(2 * π * u * X ω) * Complex.I) * ψ₂ (Y ω)
      = ∫ v : ℝ, Complex.exp (↑(2 * π * u * X ω) * Complex.I) *
          Complex.exp (↑(2 * π * v * Y ω) * Complex.I) * F₂ v := by
    intro ω; rw [schwartz_inv ψ₂, ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun v => ?_)); simp only; ring
  have int2 : Integrable (Function.uncurry fun (ω : Ω) (v : ℝ) =>
      Complex.exp (↑(2 * π * u * X ω) * Complex.I) *
          Complex.exp (↑(2 * π * v * Y ω) * Complex.I) * F₂ v) (μ.prod volume) := by
    refine Integrable.mono' ((integrable_const (1 : ℝ)).mul_prod hF₂.norm) ?_ ?_
    · have m1 : Measurable (fun p : Ω × ℝ => (X p.1, p.2, Y p.1)) :=
        (hX.comp measurable_fst).prodMk (measurable_snd.prodMk (hY.comp measurable_fst))
      have c1 : Continuous (fun q : ℝ × ℝ × ℝ =>
          Complex.exp (↑(2 * π * u * q.1) * Complex.I) *
            Complex.exp (↑(2 * π * q.2.1 * q.2.2) * Complex.I) * F₂ q.2.1) :=
        (by fun_prop : Continuous fun (q : ℝ × ℝ × ℝ) =>
          Complex.exp (↑(2 * π * u * q.1) * Complex.I) *
            Complex.exp (↑(2 * π * q.2.1 * q.2.2) * Complex.I)).mul (cF₂.comp (by fun_prop))
      exact (c1.measurable.comp m1).aestronglyMeasurable
    · refine Filter.Eventually.of_forall (fun p => ?_)
      simp only [Function.uncurry, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
      exact le_refl _
  simp_rw [step2]
  rw [integral_integral_swap int2, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun v => ?_))
  simp only
  rw [← integral_const_mul, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun ω => ?_))
  simp only
  rw [show (↑(2 * π * (u * X ω + v * Y ω)) * Complex.I : ℂ)
      = ↑(2 * π * u * X ω) * Complex.I + ↑(2 * π * v * Y ω) * Complex.I by push_cast; ring,
    Complex.exp_add]
  ring

/-- The standard Gaussian. -/
abbrev γ : Measure ℝ := gaussianReal 0 1

lemma gauss_char (t : ℝ) : ∫ x, Complex.exp (↑(t * x) * Complex.I) ∂γ = Complex.exp (-(t ^ 2 / 2 : ℝ)) := by
  have h := charFun_gaussianReal (μ := 0) (v := 1) t
  rw [charFun_apply_real] at h
  rw [show (fun x : ℝ => Complex.exp (↑(t * x) * Complex.I)) = fun x : ℝ => Complex.exp (↑t * ↑x * Complex.I) by
    ext x; push_cast; ring_nf]
  rw [h]; congr 1; push_cast; ring

/-- **Two-point identity on the Gaussian side.** -/
theorem gauss_two (ψ₁ ψ₂ : SchwartzMap ℝ ℂ) (ρ σ : ℝ) :
    ∫ z, ψ₁ z.1 * ψ₂ (ρ * z.1 + σ * z.2) ∂(γ.prod γ)
      = ∫ u : ℝ, ∫ v : ℝ, 𝓕 (ψ₁ : ℝ → ℂ) u * 𝓕 (ψ₂ : ℝ → ℂ) v *
          Complex.exp (-(2 * π ^ 2 * ((u + ρ * v) ^ 2 + σ ^ 2 * v ^ 2) : ℝ)) := by
  rw [fub_two (γ.prod γ) (fun z => z.1) (fun z => ρ * z.1 + σ * z.2) measurable_fst
    (by fun_prop) ψ₁ ψ₂]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun u => ?_))
  refine integral_congr_ae (Filter.Eventually.of_forall (fun v => ?_))
  simp only
  congr 1
  have : ∀ z : ℝ × ℝ, Complex.exp (↑(2 * π * (u * z.1 + v * (ρ * z.1 + σ * z.2))) * Complex.I)
      = Complex.exp (↑((2 * π * (u + ρ * v)) * z.1) * Complex.I) *
          Complex.exp (↑((2 * π * σ * v) * z.2) * Complex.I) := by
    intro z; rw [← Complex.exp_add]; congr 1; push_cast; ring
  simp_rw [this]
  rw [integral_prod_mul (fun x => Complex.exp (↑((2 * π * (u + ρ * v)) * x) * Complex.I))
    (fun y => Complex.exp (↑((2 * π * σ * v) * y) * Complex.I)), gauss_char, gauss_char,
    ← Complex.exp_add]
  congr 1; push_cast; ring

/-! ### The error -/

lemma cos_exp_err (θ : ℝ) : |Real.cos θ - Real.exp (-(θ ^ 2 / 2))| ≤ 2 * θ ^ 4 := by
  by_cases hθ : |θ| ≤ 1
  · have h1 := Real.cos_bound hθ
    have hy : |-(θ ^ 2 / 2)| ≤ 1 := by
      rw [abs_neg, abs_of_nonneg (by positivity)]
      have : θ ^ 2 ≤ 1 := by rw [← sq_abs]; nlinarith [abs_nonneg θ]
      linarith
    have h2 := Real.abs_exp_sub_one_sub_id_le hy
    have h4 : |θ| ^ 4 = θ ^ 4 := by rw [← abs_pow]; exact abs_of_nonneg (by positivity)
    rw [h4] at h1
    have : (-(θ ^ 2 / 2)) ^ 2 = θ ^ 4 / 4 := by ring
    rw [this] at h2
    calc |Real.cos θ - Real.exp (-(θ ^ 2 / 2))|
        = |(Real.cos θ - (1 - θ ^ 2 / 2)) - (Real.exp (-(θ ^ 2 / 2)) - 1 - -(θ ^ 2 / 2))| := by
          congr 1; ring
      _ ≤ |Real.cos θ - (1 - θ ^ 2 / 2)| + |Real.exp (-(θ ^ 2 / 2)) - 1 - -(θ ^ 2 / 2)| :=
          abs_sub _ _
      _ ≤ θ ^ 4 * (5 / 96) + θ ^ 4 / 4 := add_le_add h1 h2
      _ ≤ 2 * θ ^ 4 := by nlinarith [pow_nonneg (sq_nonneg θ) 2]
  · push Not at hθ
    have h1 : 1 ≤ θ ^ 4 := by
      have : 1 ≤ |θ| ^ 4 := one_le_pow₀ hθ.le
      rwa [← abs_pow, abs_of_nonneg (by positivity)] at this
    have hc := Real.abs_cos_le_one θ
    have he : |Real.exp (-(θ ^ 2 / 2))| ≤ 1 := by
      rw [abs_of_pos (Real.exp_pos _)]; exact Real.exp_le_one_iff.2 (by nlinarith [sq_nonneg θ])
    calc _ ≤ |Real.cos θ| + |Real.exp (-(θ ^ 2 / 2))| := abs_sub _ _
      _ ≤ 2 := by linarith
      _ ≤ 2 * θ ^ 4 := by linarith

lemma prod_sub_prod_le {ι : Type*} (s : Finset ι) (x y : ι → ℝ) (hx : ∀ i ∈ s, |x i| ≤ 1)
    (hy : ∀ i ∈ s, |y i| ≤ 1) : |∏ i ∈ s, x i - ∏ i ∈ s, y i| ≤ ∑ i ∈ s, |x i - y i| := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha, Finset.sum_insert ha]
    have ih' := ih (fun i hi => hx i (Finset.mem_insert_of_mem hi))
      (fun i hi => hy i (Finset.mem_insert_of_mem hi))
    have hxa := hx a (Finset.mem_insert_self a s)
    have hPy : |∏ i ∈ s, y i| ≤ 1 := by
      rw [Finset.abs_prod]
      exact Finset.prod_le_one₀ (fun i _ => abs_nonneg _)
        (fun i hi => hy i (Finset.mem_insert_of_mem hi))
    calc |x a * ∏ i ∈ s, x i - y a * ∏ i ∈ s, y i|
        = |x a * (∏ i ∈ s, x i - ∏ i ∈ s, y i) + (x a - y a) * ∏ i ∈ s, y i| := by congr 1; ring
      _ ≤ |x a| * |∏ i ∈ s, x i - ∏ i ∈ s, y i| + |x a - y a| * |∏ i ∈ s, y i| := by
          refine (abs_add_le _ _).trans ?_; rw [abs_mul, abs_mul]
      _ ≤ 1 * ∑ i ∈ s, |x i - y i| + |x a - y a| * 1 := by
          gcongr
      _ = |x a - y a| + ∑ i ∈ s, |x i - y i| := by ring

lemma sum_fourth_le (s t : ℝ) (a b : ℝ) : (s * a + t * b) ^ 4 ≤ 8 * (s ^ 4 * a ^ 4 + t ^ 4 * b ^ 4) := by
  nlinarith [sq_nonneg (s * a - t * b), sq_nonneg (s * a + t * b), sq_nonneg ((s*a)^2 - (t*b)^2),
    sq_nonneg (s*a), sq_nonneg (t*b), mul_self_nonneg (s * a * (t * b))]

lemma norm_iter_le {k : ℕ} (f : ℝ → ℝ → ℂ) (a b : Fin k → ℝ → ℝ) (ha : ∀ i, Integrable (a i))
    (hb : ∀ i, Integrable (b i)) (h : ∀ u v, ‖f u v‖ ≤ ∑ i, a i u * b i v) :
    ‖∫ u, ∫ v, f u v‖ ≤ ∑ i, (∫ u, a i u) * (∫ v, b i v) := by
  have hin : ∀ u, ‖∫ v, f u v‖ ≤ ∑ i, a i u * ∫ v, b i v := by
    intro u
    refine (norm_integral_le_of_norm_le (g := fun v => ∑ i, a i u * b i v)
      (integrable_finsetSum _ (fun i _ => (hb i).const_mul _))
      (Filter.Eventually.of_forall (h u))).trans (le_of_eq ?_)
    rw [integral_finsetSum _ (fun i _ => (hb i).const_mul _)]
    exact Finset.sum_congr rfl (fun i _ => integral_const_mul _ _)
  refine (norm_integral_le_of_norm_le (g := fun u => ∑ i, a i u * ∫ v, b i v)
    (integrable_finsetSum _ (fun i _ => (ha i).mul_const _))
    (Filter.Eventually.of_forall hin)).trans (le_of_eq ?_)
  rw [integral_finsetSum _ (fun i _ => (ha i).mul_const _)]
  exact Finset.sum_congr rfl (fun i _ => integral_mul_const _ _)

/-- Integrability of a bounded kernel against `𝓕ψ₁ ⊗ 𝓕ψ₂`. -/
lemma int_kernel (ψ₁ ψ₂ : SchwartzMap ℝ ℂ) (K : ℝ → ℝ → ℂ) (hK : Continuous (Function.uncurry K))
    (hK1 : ∀ u v, ‖K u v‖ ≤ 1) :
    Integrable (Function.uncurry fun u v => 𝓕 (ψ₁ : ℝ → ℂ) u * 𝓕 (ψ₂ : ℝ → ℂ) v * K u v)
      (volume.prod volume) := by
  refine Integrable.mono' ((fourier_integrable ψ₁).norm.mul_prod (fourier_integrable ψ₂).norm) ?_ ?_
  · exact (((fourier_continuous ψ₁).comp continuous_fst).mul
      ((fourier_continuous ψ₂).comp continuous_snd) |>.mul hK).aestronglyMeasurable
  · refine Filter.Eventually.of_forall (fun p => ?_)
    simp only [Function.uncurry, norm_mul]
    have := hK1 p.1 p.2
    calc ‖𝓕 (ψ₁ : ℝ → ℂ) p.1‖ * ‖𝓕 (ψ₂ : ℝ → ℂ) p.2‖ * ‖K p.1 p.2‖
        ≤ ‖𝓕 (ψ₁ : ℝ → ℂ) p.1‖ * ‖𝓕 (ψ₂ : ℝ → ℂ) p.2‖ * 1 := by gcongr
      _ = _ := by ring

lemma int_kernel_u (ψ₁ ψ₂ : SchwartzMap ℝ ℂ) (K : ℝ → ℝ → ℂ) (hK : ∀ u, Continuous (K u))
    (hK1 : ∀ u v, ‖K u v‖ ≤ 1) (u : ℝ) :
    Integrable (fun v => 𝓕 (ψ₁ : ℝ → ℂ) u * 𝓕 (ψ₂ : ℝ → ℂ) v * K u v) := by
  refine Integrable.mono' ((fourier_integrable ψ₂).norm.const_mul ‖𝓕 (ψ₁ : ℝ → ℂ) u‖) ?_ ?_
  · exact ((continuous_const.mul (fourier_continuous ψ₂)).mul (hK u)).aestronglyMeasurable
  · refine Filter.Eventually.of_forall (fun v => ?_)
    simp only [norm_mul]
    have := hK1 u v
    calc ‖𝓕 (ψ₁ : ℝ → ℂ) u‖ * ‖𝓕 (ψ₂ : ℝ → ℂ) v‖ * ‖K u v‖
        ≤ ‖𝓕 (ψ₁ : ℝ → ℂ) u‖ * ‖𝓕 (ψ₂ : ℝ → ℂ) v‖ * 1 := by gcongr
      _ = _ := by ring

/-- The Gaussian kernel. -/
def gk (ρ : ℝ) (u v : ℝ) : ℝ := Real.exp (-(2 * π ^ 2 * (u ^ 2 + 2 * ρ * u * v + v ^ 2)))

/-- The kernel difference. -/
lemma kernel_diff {ι : Type*} [Fintype ι] (a b : ι → ℝ) (ρ : ℝ) (ha : ∑ i, a i ^ 2 = 1)
    (hb : ∑ i, b i ^ 2 = 1) (hab : ∑ i, a i * b i = ρ) (u v : ℝ) :
    |∏ i, Real.cos (2 * π * (u * a i + v * b i)) - gk ρ u v|
      ≤ 16 * (2 * π) ^ 4 * ((∑ i, a i ^ 4) * u ^ 4 + (∑ i, b i ^ 4) * v ^ 4) := by
  have hg : gk ρ u v = ∏ i, Real.exp (-((2 * π * (u * a i + v * b i)) ^ 2 / 2)) := by
    rw [← Real.exp_sum]; unfold gk; congr 1
    rw [Finset.sum_neg_distrib]
    have : ∑ i, (2 * π * (u * a i + v * b i)) ^ 2 / 2
        = 2 * π ^ 2 * (u ^ 2 * ∑ i, a i ^ 2 + 2 * u * v * ∑ i, a i * b i + v ^ 2 * ∑ i, b i ^ 2) := by
      rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
        ← Finset.sum_add_distrib, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun i _ => by ring)
    rw [this, ha, hb, hab]; ring
  rw [hg]
  refine (prod_sub_prod_le _ _ _ (fun i _ => Real.abs_cos_le_one _) (fun i _ => by
    rw [abs_of_pos (Real.exp_pos _)]; exact Real.exp_le_one_iff.2 (by
      have := sq_nonneg (2 * π * (u * a i + v * b i)); linarith))).trans ?_
  have hpi : (0 : ℝ) ≤ (2 * π) ^ 4 := by positivity
  calc ∑ i, |Real.cos (2 * π * (u * a i + v * b i)) - Real.exp (-((2 * π * (u * a i + v * b i)) ^ 2 / 2))|
      ≤ ∑ i, 2 * (2 * π * (u * a i + v * b i)) ^ 4 :=
        Finset.sum_le_sum (fun i _ => cos_exp_err _)
    _ ≤ ∑ i, 2 * (2 * π) ^ 4 * (8 * (u ^ 4 * a i ^ 4 + v ^ 4 * b i ^ 4)) := by
        refine Finset.sum_le_sum (fun i _ => ?_)
        rw [show (2 * π * (u * a i + v * b i)) ^ 4 = (2 * π) ^ 4 * (u * a i + v * b i) ^ 4 by ring,
          ← mul_assoc]
        exact mul_le_mul_of_nonneg_left (sum_fourth_le u v (a i) (b i)) (by positivity)
    _ = 16 * (2 * π) ^ 4 * ((∑ i, a i ^ 4) * u ^ 4 + (∑ i, b i ^ 4) * v ^ 4) := by
        rw [Finset.sum_mul, Finset.sum_mul, ← Finset.sum_add_distrib, Finset.mul_sum]
        refine Finset.sum_congr rfl (fun i _ => by ring)

lemma abs_rho_le {ι : Type*} [Fintype ι] (a b : ι → ℝ) (ρ : ℝ) (ha : ∑ i, a i ^ 2 = 1)
    (hb : ∑ i, b i ^ 2 = 1) (hab : ∑ i, a i * b i = ρ) : ρ ^ 2 ≤ 1 := by
  rw [← hab]
  have h2 := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ a b
  rw [ha, hb, one_mul] at h2; exact h2

lemma gk_le_one (ρ : ℝ) (hρ : ρ ^ 2 ≤ 1) (u v : ℝ) : |gk ρ u v| ≤ 1 := by
  unfold gk
  rw [abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff, neg_nonpos]
  have : 0 ≤ u ^ 2 + 2 * ρ * u * v + v ^ 2 := by
    nlinarith [sq_nonneg (u + ρ * v), sq_nonneg v]
  positivity

/-- **Two-point CLT.** -/
theorem clt_two {ι : Type*} [Fintype ι] [DecidableEq ι] (ψ₁ ψ₂ : SchwartzMap ℝ ℂ)
    (a b : ι → ℝ) (ρ : ℝ) (ha : ∑ i, a i ^ 2 = 1) (hb : ∑ i, b i ^ 2 = 1)
    (hab : ∑ i, a i * b i = ρ) :
    ‖(∑ ε : ι → ℤˣ, ψ₁ (ssum ε a) * ψ₂ (ssum ε b)) / 2 ^ Fintype.card ι
      - ∫ u : ℝ, ∫ v : ℝ, 𝓕 (ψ₁ : ℝ → ℂ) u * 𝓕 (ψ₂ : ℝ → ℂ) v * (gk ρ u v : ℂ)‖
      ≤ 16 * (2 * π) ^ 4 * (Mom 4 ψ₁ * Mom 0 ψ₂ * ∑ i, a i ^ 4 + Mom 0 ψ₁ * Mom 4 ψ₂ * ∑ i, b i ^ 4) := by
  rw [avg_two]
  have hρ := abs_rho_le a b ρ ha hb hab
  obtain ⟨Kc, hKc⟩ : ∃ K : ℝ → ℝ → ℂ, K = fun u v => ∏ i, (Real.cos (2 * π * (u * a i + v * b i)) : ℂ) :=
    ⟨_, rfl⟩
  obtain ⟨Kg, hKg⟩ : ∃ K : ℝ → ℝ → ℂ, K = fun u v => (gk ρ u v : ℂ) := ⟨_, rfl⟩
  have eC : ∀ u v, (∏ i, (Real.cos (2 * π * (u * a i + v * b i)) : ℂ)) = Kc u v := by
    intro u v; rw [hKc]
  have eG : ∀ u v, ((gk ρ u v : ℝ) : ℂ) = Kg u v := by intro u v; rw [hKg]
  simp_rw [eC, eG]
  have hKc1 : ∀ u v, ‖Kc u v‖ ≤ 1 := by
    intro u v; rw [hKc]; simp only [norm_prod]
    exact Finset.prod_le_one₀ (fun i _ => norm_nonneg _) (fun i _ => by
      rw [Complex.norm_real, Real.norm_eq_abs]; exact Real.abs_cos_le_one _)
  have hKg1 : ∀ u v, ‖Kg u v‖ ≤ 1 := by
    intro u v; rw [hKg]; simp only [Complex.norm_real, Real.norm_eq_abs]
    exact gk_le_one ρ hρ u v
  have cKc : Continuous (Function.uncurry Kc) := by
    rw [hKc]; exact continuous_finsetProd _ (fun i _ => by fun_prop)
  have cKg : Continuous (Function.uncurry Kg) := by
    rw [hKg]; simp only [gk]; fun_prop
  have hdiff : ∀ u v, ‖Kc u v - Kg u v‖
      ≤ 16 * (2 * π) ^ 4 * ((∑ i, a i ^ 4) * u ^ 4 + (∑ i, b i ^ 4) * v ^ 4) := by
    intro u v
    rw [hKc, hKg]; simp only
    rw [← Complex.ofReal_prod, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    exact kernel_diff a b ρ ha hb hab u v
  set F₁ := 𝓕 (ψ₁ : ℝ → ℂ)
  set F₂ := 𝓕 (ψ₂ : ℝ → ℂ)
  have iC := int_kernel ψ₁ ψ₂ Kc cKc hKc1
  have iG := int_kernel ψ₁ ψ₂ Kg cKg hKg1
  have iCu := int_kernel_u ψ₁ ψ₂ Kc (fun u => cKc.comp (Continuous.prodMk_right u)) hKc1
  have iGu := int_kernel_u ψ₁ ψ₂ Kg (fun u => cKg.comp (Continuous.prodMk_right u)) hKg1
  have iC' : Integrable (fun u => ∫ v, F₁ u * F₂ v * Kc u v) := iC.integral_prod_left
  have iG' : Integrable (fun u => ∫ v, F₁ u * F₂ v * Kg u v) := iG.integral_prod_left
  rw [← integral_sub iC' iG']
  have : ∀ u, (∫ v, F₁ u * F₂ v * Kc u v) - ∫ v, F₁ u * F₂ v * Kg u v
      = ∫ v, F₁ u * F₂ v * (Kc u v - Kg u v) := by
    intro u; rw [← integral_sub (iCu u) (iGu u)]; congr 1; ext v; ring
  simp_rw [this]
  set A4 := ∑ i, a i ^ 4
  set B4 := ∑ i, b i ^ 4
  set C0 := 16 * (2 * π) ^ 4
  have hA : 0 ≤ A4 := Finset.sum_nonneg (fun i _ => by positivity)
  have hB : 0 ≤ B4 := Finset.sum_nonneg (fun i _ => by positivity)
  have hC0 : 0 ≤ C0 := by positivity
  let fa : Fin 2 → ℝ → ℝ := ![fun u => C0 * A4 * (|u| ^ 4 * ‖F₁ u‖), fun u => C0 * B4 * (|u| ^ 0 * ‖F₁ u‖)]
  let fb : Fin 2 → ℝ → ℝ := ![fun v => |v| ^ 0 * ‖F₂ v‖, fun v => |v| ^ 4 * ‖F₂ v‖]
  have ia : ∀ i, Integrable (fa i) := by
    intro i; fin_cases i
    · exact (integrable_mom 4 ψ₁).const_mul _
    · exact (integrable_mom 0 ψ₁).const_mul _
  have ib : ∀ i, Integrable (fb i) := by
    intro i; fin_cases i
    · exact integrable_mom 0 ψ₂
    · exact integrable_mom 4 ψ₂
  have key := norm_iter_le (k := 2) (fun u v => F₁ u * F₂ v * (Kc u v - Kg u v)) fa fb ia ib (by
    intro u v
    simp only [fa, fb, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, pow_zero, one_mul]
    rw [norm_mul, norm_mul]
    have hu4 : |u| ^ 4 = u ^ 4 := by rw [← abs_pow]; exact abs_of_nonneg (by positivity)
    have hv4 : |v| ^ 4 = v ^ 4 := by rw [← abs_pow]; exact abs_of_nonneg (by positivity)
    rw [hu4, hv4]
    calc ‖F₁ u‖ * ‖F₂ v‖ * ‖Kc u v - Kg u v‖
        ≤ ‖F₁ u‖ * ‖F₂ v‖ * (C0 * (A4 * u ^ 4 + B4 * v ^ 4)) := by
          gcongr; exact hdiff u v
      _ = _ := by ring)
  refine key.trans (le_of_eq ?_)
  simp only [fa, fb, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [integral_const_mul, integral_const_mul]
  unfold Mom
  ring

end R522

end S_RR3

-- ===== RR4 =====

/-!
# Erdős 522 (real roots), part 4: Gaussian facts

* `wedge`: `(γ ⊗ γ) {z₁ > 0, ρ z₁ + σ z₂ < 0} = arccos ρ / (2π)` (polar coordinates).
* `wedge'`: the opposite wedge has the same measure.
* `law_Y`: `ρ z₁ + σ z₂` is standard Gaussian when `ρ² + σ² = 1`.
* `gauss_strip`, `gauss_tail`: `γ [a, a + w] ≤ w / √(2π)`, `γ {R ≤ |x|} ≤ 1 / R²`.
-/

open Finset Real MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

noncomputable section S_RR4

namespace R522

/-- The standard Gaussian density (as `ℝ≥0∞`). -/
abbrev φ : ℝ → ℝ≥0∞ := gaussianPDF 0 1

lemma γ_eq : γ = volume.withDensity φ := gaussianReal_of_var_ne_zero 0 one_ne_zero

lemma γγ_eq : γ.prod γ = (volume : Measure (ℝ × ℝ)).withDensity (fun z => φ z.1 * φ z.2) := by
  rw [γ_eq, prod_withDensity (measurable_gaussianPDF 0 1) (measurable_gaussianPDF 0 1),
    Measure.volume_eq_prod]

lemma φ_apply (x : ℝ) : φ x = ENNReal.ofReal ((√(2 * π))⁻¹ * Real.exp (-x ^ 2 / 2)) := by
  simp [φ, gaussianPDF, gaussianPDFReal]

lemma φφ_polar (r θ : ℝ) : φ (r * Real.cos θ) * φ (r * Real.sin θ)
    = ENNReal.ofReal ((2 * π)⁻¹ * Real.exp (-r ^ 2 / 2)) := by
  rw [φ_apply, φ_apply, ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  have h1 : (√(2 * π))⁻¹ * (√(2 * π))⁻¹ = (2 * π)⁻¹ := by
    rw [← mul_inv, Real.mul_self_sqrt (by positivity)]
  have h2 : Real.exp (-(r * Real.cos θ) ^ 2 / 2) * Real.exp (-(r * Real.sin θ) ^ 2 / 2)
      = Real.exp (-r ^ 2 / 2) := by
    rw [← Real.exp_add]; congr 1
    have := Real.sin_sq_add_cos_sq θ
    have : (r * Real.cos θ) ^ 2 + (r * Real.sin θ) ^ 2 = r ^ 2 := by
      rw [mul_pow, mul_pow, ← mul_add]; nlinarith
    linarith
  calc (√(2 * π))⁻¹ * Real.exp (-(r * Real.cos θ) ^ 2 / 2) * ((√(2 * π))⁻¹ * Real.exp (-(r * Real.sin θ) ^ 2 / 2))
      = ((√(2 * π))⁻¹ * (√(2 * π))⁻¹) * (Real.exp (-(r * Real.cos θ) ^ 2 / 2) *
          Real.exp (-(r * Real.sin θ) ^ 2 / 2)) := by ring
    _ = _ := by rw [h1, h2]

/-- Angular description of the wedge. -/
lemma wedge_angle {ρ : ℝ} (hρ1 : -1 < ρ) (hρ2 : ρ < 1) {r θ : ℝ} (hr : 0 < r)
    (hθ : θ ∈ Set.Ioo (-π) π) :
    (0 < r * Real.cos θ ∧ ρ * (r * Real.cos θ) + √(1 - ρ ^ 2) * (r * Real.sin θ) < 0)
      ↔ θ ∈ Set.Ioo (-(π / 2)) (Real.arccos ρ - π / 2) := by
  set α := Real.arccos ρ with hα
  have hα0 : 0 < α := Real.arccos_pos.2 hρ2
  have hαπ : α < π := Real.arccos_lt_pi.2 hρ1
  have hcos : Real.cos α = ρ := Real.cos_arccos hρ1.le hρ2.le
  have hsin : Real.sin α = √(1 - ρ ^ 2) := Real.sin_arccos ρ
  have hexp : ρ * (r * Real.cos θ) + √(1 - ρ ^ 2) * (r * Real.sin θ) = r * Real.cos (θ - α) := by
    rw [Real.cos_sub, hcos, hsin]; ring
  rw [hexp]
  have hpos : 0 < r * Real.cos θ ↔ θ ∈ Set.Ioo (-(π / 2)) (π / 2) := by
    rw [mul_pos_iff_of_pos_left hr]
    constructor
    · intro h
      by_contra hn
      simp only [Set.mem_Ioo, not_and_or, not_lt] at hn
      rcases hn with h1 | h1
      · have : Real.cos θ ≤ 0 := by
          rw [← Real.cos_neg]
          exact Real.cos_nonpos_of_pi_div_two_le_of_le (by linarith) (by linarith [hθ.1])
        linarith
      · have : Real.cos θ ≤ 0 :=
          Real.cos_nonpos_of_pi_div_two_le_of_le h1 (by linarith [hθ.2])
        linarith
    · intro h; exact Real.cos_pos_of_mem_Ioo h
  rw [hpos, mul_neg_iff]
  simp only [Set.mem_Ioo]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    rcases h3 with ⟨_, h3⟩ | ⟨h3, _⟩
    · refine ⟨h1, ?_⟩
      by_contra hn; push Not at hn
      have : 0 ≤ Real.cos (θ - α) := Real.cos_nonneg_of_mem_Icc ⟨by linarith, by linarith⟩
      linarith
    · linarith
  · rintro ⟨h1, h2⟩
    refine ⟨⟨h1, by linarith⟩, Or.inl ⟨hr, ?_⟩⟩
    rw [← Real.cos_neg]
    exact Real.cos_neg_of_pi_div_two_lt_of_lt (by linarith) (by linarith)

/-- **The Gaussian wedge.** -/
theorem wedge {ρ : ℝ} (hρ1 : -1 < ρ) (hρ2 : ρ < 1) :
    (γ.prod γ) {z : ℝ × ℝ | 0 < z.1 ∧ ρ * z.1 + √(1 - ρ ^ 2) * z.2 < 0}
      = ENNReal.ofReal (Real.arccos ρ / (2 * π)) := by
  set W := {z : ℝ × ℝ | 0 < z.1 ∧ ρ * z.1 + √(1 - ρ ^ 2) * z.2 < 0} with hW
  have hWm : MeasurableSet W := by
    simp only [W, Set.setOf_and]
    apply MeasurableSet.inter
    · exact measurableSet_lt measurable_const measurable_fst
    · exact measurableSet_lt (f := fun z : ℝ × ℝ => ρ * z.1 + √(1 - ρ ^ 2) * z.2)
        (g := fun _ => (0 : ℝ)) (by fun_prop) measurable_const
  rw [γγ_eq, withDensity_apply _ hWm, ← lintegral_indicator hWm,
    ← lintegral_comp_polarCoord_symm]
  set α := Real.arccos ρ
  have hα0 : 0 < α := Real.arccos_pos.2 hρ2
  have hαπ : α < π := Real.arccos_lt_pi.2 hρ1
  -- the integrand on the target
  have hpt : ∀ p ∈ polarCoord.target, ENNReal.ofReal p.1 •
      W.indicator (fun z => φ z.1 * φ z.2) (polarCoord.symm p)
      = ENNReal.ofReal (p.1 * ((2 * π)⁻¹ * Real.exp (-p.1 ^ 2 / 2))) *
          (Set.Ioo (-(π / 2)) (α - π / 2)).indicator 1 p.2 := by
    rintro ⟨r, θ⟩ ⟨hr, hθ⟩
    simp only [Set.mem_Ioi] at hr
    simp only [smul_eq_mul, polarCoord, OpenPartialHomeomorph.coe_mk_symm, PartialEquiv.coe_symm_mk]
    by_cases hin : θ ∈ Set.Ioo (-(π / 2)) (α - π / 2)
    · have hmem : (r * Real.cos θ, r * Real.sin θ) ∈ W := (wedge_angle hρ1 hρ2 hr hθ).2 hin
      rw [Set.indicator_of_mem hmem, Set.indicator_of_mem hin, Pi.one_apply, mul_one, φφ_polar,
        ← ENNReal.ofReal_mul hr.le]
    · have hmem : (r * Real.cos θ, r * Real.sin θ) ∉ W := fun h => hin ((wedge_angle hρ1 hρ2 hr hθ).1 h)
      rw [Set.indicator_of_notMem hmem, Set.indicator_of_notMem hin, mul_zero, mul_zero]
  rw [setLIntegral_congr_fun polarCoord.open_target.measurableSet hpt]
  have htarget : polarCoord.target = Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-π) π := rfl
  rw [htarget, Measure.volume_eq_prod, ← Measure.prod_restrict]
  rw [lintegral_prod_mul (f := fun r => ENNReal.ofReal (r * ((2 * π)⁻¹ * Real.exp (-r ^ 2 / 2))))
    (g := (Set.Ioo (-(π / 2)) (α - π / 2)).indicator 1)
    ((ENNReal.measurable_ofReal.comp (by fun_prop)).aemeasurable)
    ((measurable_one.indicator measurableSet_Ioo).aemeasurable)]
  -- radial part
  have hrad : ∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal (r * ((2 * π)⁻¹ * Real.exp (-r ^ 2 / 2)))
      = ENNReal.ofReal ((2 * π)⁻¹) := by
    have hint : IntegrableOn (fun r : ℝ => r * ((2 * π)⁻¹ * Real.exp (-r ^ 2 / 2))) (Set.Ioi 0) := by
      have := (integrable_mul_exp_neg_mul_sq (b := 1 / 2) (by norm_num)).integrableOn (s := Set.Ioi 0)
      refine IntegrableOn.congr_fun (this.const_mul (2 * π)⁻¹) (fun r _ => ?_) measurableSet_Ioi
      ring_nf
    rw [← ofReal_integral_eq_lintegral_ofReal hint (ae_restrict_of_forall_mem measurableSet_Ioi
      (fun r hr => by simp only [Pi.zero_apply]; have : (0 : ℝ) < r := hr; positivity))]
    · congr 1
      have hc := integral_mul_cexp_neg_mul_sq (b := (1 / 2 : ℂ)) (by norm_num)
      have : ∫ r in Set.Ioi (0 : ℝ), r * Real.exp (-r ^ 2 / 2) = 1 := by
        have h2 : (∫ r in Set.Ioi (0 : ℝ), ((r * Real.exp (-r ^ 2 / 2) : ℝ) : ℂ)) = 1 := by
          rw [show (2 * (1 / 2 : ℂ))⁻¹ = 1 by norm_num] at hc
          rw [← hc]
          refine setIntegral_congr_fun measurableSet_Ioi (fun r _ => ?_)
          push_cast; congr 2; ring
        rw [integral_complex_ofReal] at h2
        exact_mod_cast h2
      rw [show (fun r : ℝ => r * ((2 * π)⁻¹ * Real.exp (-r ^ 2 / 2)))
          = fun r => (2 * π)⁻¹ * (r * Real.exp (-r ^ 2 / 2)) by ext r; ring,
        integral_const_mul, this, mul_one]
  have hang : ∫⁻ θ in Set.Ioo (-π) π, (Set.Ioo (-(π / 2)) (α - π / 2)).indicator 1 θ
      = ENNReal.ofReal α := by
    rw [lintegral_indicator_one measurableSet_Ioo, Measure.restrict_apply measurableSet_Ioo,
      Set.inter_eq_left.mpr (Set.Ioo_subset_Ioo (by linarith [Real.pi_pos]) (by linarith)),
      Real.volume_Ioo]
    congr 1; ring
  rw [hrad, hang, ← ENNReal.ofReal_mul (by positivity)]
  congr 1; ring

lemma map_neg_γ : γ.map (fun x => -x) = γ := by
  rw [gaussianReal_map_neg, neg_zero]

/-- The opposite wedge. -/
theorem wedge' {ρ : ℝ} (hρ1 : -1 < ρ) (hρ2 : ρ < 1) :
    (γ.prod γ) {z : ℝ × ℝ | z.1 < 0 ∧ 0 < ρ * z.1 + √(1 - ρ ^ 2) * z.2}
      = ENNReal.ofReal (Real.arccos ρ / (2 * π)) := by
  have hW : MeasurableSet {z : ℝ × ℝ | 0 < z.1 ∧ ρ * z.1 + √(1 - ρ ^ 2) * z.2 < 0} := by
    simp only [Set.setOf_and]
    apply MeasurableSet.inter
    · exact measurableSet_lt measurable_const measurable_fst
    · exact measurableSet_lt (f := fun z : ℝ × ℝ => ρ * z.1 + √(1 - ρ ^ 2) * z.2)
        (g := fun _ => (0 : ℝ)) (by fun_prop) measurable_const
  have hm : Measurable (Prod.map (fun x : ℝ => -x) (fun x : ℝ => -x)) := by fun_prop
  have hmap : (γ.prod γ).map (Prod.map (fun x : ℝ => -x) (fun x : ℝ => -x)) = γ.prod γ := by
    rw [← Measure.map_prod_map γ γ (by fun_prop) (by fun_prop), map_neg_γ]
  rw [← wedge hρ1 hρ2, ← hmap, Measure.map_apply hm hW]
  congr 1
  ext z
  simp only [Set.mem_ofPred_eq, Set.mem_preimage, Prod.map_fst, Prod.map_snd]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨by linarith, by linarith⟩
  · rintro ⟨h1, h2⟩; exact ⟨by linarith, by linarith⟩

/-- The law of `ρ z₁ + σ z₂`. -/
theorem law_Y (ρ σ : ℝ) (h : ρ ^ 2 + σ ^ 2 = 1) :
    (γ.prod γ).map (fun z : ℝ × ℝ => ρ * z.1 + σ * z.2) = γ := by
  have e : (fun z : ℝ × ℝ => ρ * z.1 + σ * z.2)
      = (fun p : ℝ × ℝ => p.1 + p.2) ∘ Prod.map (fun x : ℝ => ρ * x) (fun x : ℝ => σ * x) := by
    ext z; rfl
  rw [e, ← Measure.map_map (by fun_prop) (by fun_prop),
    ← Measure.map_prod_map γ γ (by fun_prop) (by fun_prop), gaussianReal_map_const_mul,
    gaussianReal_map_const_mul]
  change Measure.conv _ _ = _
  rw [gaussianReal_conv_gaussianReal]
  congr 1
  · simp
  · ext; simp [h]

lemma φ_le (x : ℝ) : φ x ≤ ENNReal.ofReal ((√(2 * π))⁻¹) := by
  rw [φ_apply]
  apply ENNReal.ofReal_le_ofReal
  have : Real.exp (-x ^ 2 / 2) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith [sq_nonneg x])
  have h0 : 0 ≤ (√(2 * π))⁻¹ := by positivity
  nlinarith

/-- Gaussian strips. -/
theorem gauss_strip (a b : ℝ) (hab : a ≤ b) : γ.real (Set.Icc a b) ≤ (b - a) / √(2 * π) := by
  have h1 : γ (Set.Icc a b) ≤ ENNReal.ofReal ((√(2 * π))⁻¹) * ENNReal.ofReal (b - a) := by
    rw [γ_eq, withDensity_apply _ measurableSet_Icc]
    calc ∫⁻ x in Set.Icc a b, φ x ≤ ∫⁻ _x in Set.Icc a b, ENNReal.ofReal ((√(2 * π))⁻¹) :=
          lintegral_mono (fun x => φ_le x)
      _ = _ := by rw [setLIntegral_const, Real.volume_Icc]
  rw [← ENNReal.ofReal_mul (by positivity)] at h1
  have := ENNReal.toReal_mono ENNReal.ofReal_ne_top h1
  have hba : 0 ≤ (√(2 * π))⁻¹ * (b - a) := mul_nonneg (by positivity) (by linarith)
  rw [ENNReal.toReal_ofReal hba] at this
  rw [measureReal_def]
  calc _ ≤ (√(2 * π))⁻¹ * (b - a) := this
    _ = _ := by ring

/-- Gaussian tails. -/
theorem gauss_tail {R : ℝ} (hR : 0 < R) : γ.real {x | R ≤ |x|} ≤ 1 / R ^ 2 := by
  have h := meas_ge_le_variance_div_sq (μ := γ) (X := id) (memLp_id_gaussianReal 2) hR
  have e1 : ∫ x, id x ∂γ = 0 := integral_id_gaussianReal
  have e2 : Var[id; γ] = 1 := by rw [variance_id_gaussianReal]; simp
  rw [e1, e2] at h
  simp only [id, sub_zero] at h
  rw [measureReal_def]
  have := ENNReal.toReal_mono ENNReal.ofReal_ne_top h
  rwa [ENNReal.toReal_ofReal (by positivity)] at this

lemma wedge_real {ρ : ℝ} (hρ1 : -1 < ρ) (hρ2 : ρ < 1) :
    (γ.prod γ).real {z : ℝ × ℝ | 0 < z.1 ∧ ρ * z.1 + √(1 - ρ ^ 2) * z.2 < 0}
      = Real.arccos ρ / (2 * π) := by
  rw [measureReal_def, wedge hρ1 hρ2, ENNReal.toReal_ofReal]
  have := Real.arccos_nonneg ρ; positivity

lemma wedge'_real {ρ : ℝ} (hρ1 : -1 < ρ) (hρ2 : ρ < 1) :
    (γ.prod γ).real {z : ℝ × ℝ | z.1 < 0 ∧ 0 < ρ * z.1 + √(1 - ρ ^ 2) * z.2}
      = Real.arccos ρ / (2 * π) := by
  rw [measureReal_def, wedge' hρ1 hρ2, ENNReal.toReal_ofReal]
  have := Real.arccos_nonneg ρ; positivity

/-- Strips for the second coordinate. -/
theorem strip_Y (ρ σ : ℝ) (h : ρ ^ 2 + σ ^ 2 = 1) (a b : ℝ) (hab : a ≤ b) :
    (γ.prod γ).real {z : ℝ × ℝ | ρ * z.1 + σ * z.2 ∈ Set.Icc a b} ≤ (b - a) / √(2 * π) := by
  have hm : Measurable (fun z : ℝ × ℝ => ρ * z.1 + σ * z.2) := by fun_prop
  have := map_measureReal_apply hm (μ := γ.prod γ) measurableSet_Icc (s := Set.Icc a b)
  rw [law_Y ρ σ h] at this
  rw [show {z : ℝ × ℝ | ρ * z.1 + σ * z.2 ∈ Set.Icc a b}
      = (fun z : ℝ × ℝ => ρ * z.1 + σ * z.2) ⁻¹' Set.Icc a b from rfl, ← this]
  exact gauss_strip a b hab

theorem strip_X (a b : ℝ) (hab : a ≤ b) :
    (γ.prod γ).real {z : ℝ × ℝ | z.1 ∈ Set.Icc a b} ≤ (b - a) / √(2 * π) := by
  have := strip_Y 1 0 (by norm_num) a b hab
  simpa using this

theorem tail_Y (ρ σ : ℝ) (h : ρ ^ 2 + σ ^ 2 = 1) {R : ℝ} (hR : 0 < R) :
    (γ.prod γ).real {z : ℝ × ℝ | R ≤ |ρ * z.1 + σ * z.2|} ≤ 1 / R ^ 2 := by
  have hm : Measurable (fun z : ℝ × ℝ => ρ * z.1 + σ * z.2) := by fun_prop
  have hs : MeasurableSet {x : ℝ | R ≤ |x|} := measurableSet_le measurable_const (by fun_prop)
  have := map_measureReal_apply hm (μ := γ.prod γ) hs
  rw [law_Y ρ σ h] at this
  rw [show {z : ℝ × ℝ | R ≤ |ρ * z.1 + σ * z.2|}
      = (fun z : ℝ × ℝ => ρ * z.1 + σ * z.2) ⁻¹' {x | R ≤ |x|} from rfl, ← this]
  exact gauss_tail hR

theorem tail_X {R : ℝ} (hR : 0 < R) : (γ.prod γ).real {z : ℝ × ℝ | R ≤ |z.1|} ≤ 1 / R ^ 2 := by
  have := tail_Y 1 0 (by norm_num) hR
  simpa using this

end R522

end S_RR4

-- ===== RR5 =====

/-!
# Erdős 522 (real roots), part 5: quadrant probabilities for signed sums

`quad_up`: `P(∑ εa > 0, ∑ εb < 0) ≤ arccos ρ/(2π) + 2w/√(2π) + 2/R² + C·(∑a⁴ + ∑b⁴)`.
`quad_low`: `P(∑ εa > τ, ∑ εb < -τ) ≥ arccos ρ/(2π) - 2(τ+2w)/√(2π) - 2/R² - C·(∑a⁴ + ∑b⁴)`.
The constants only depend on `(τ, R, w)`.
-/

open Finset Real MeasureTheory FourierTransform ProbabilityTheory

noncomputable section S_RR5

namespace R522

/-- A bump: `1` on `[p, q]`, `0` outside `(p - w, q + w)`. -/
def bb (p q w : ℝ) (hpq : p < q) (hw : 0 < w) : ContDiffBump ((p + q) / 2) :=
  ⟨(q - p) / 2, (q - p) / 2 + w, by linarith, by linarith⟩

lemma bb_one {p q w : ℝ} (hpq : p < q) (hw : 0 < w) {x : ℝ} (hx : x ∈ Set.Icc p q) :
    bb p q w hpq hw x = 1 := by
  apply ContDiffBump.one_of_mem_closedBall
  rw [Real.closedBall_eq_Icc]
  simp only [bb, Set.mem_Icc] at hx ⊢
  constructor <;> linarith [hx.1, hx.2]

lemma bb_zero {p q w : ℝ} (hpq : p < q) (hw : 0 < w) {x : ℝ} (hx : x ∉ Set.Ioo (p - w) (q + w)) :
    bb p q w hpq hw x = 0 := by
  apply ContDiffBump.zero_of_le_dist
  simp only [bb, Set.mem_Ioo, not_and_or, not_lt] at hx ⊢
  rw [Real.dist_eq]
  rcases hx with h | h
  · rw [abs_of_nonpos (by linarith)]; linarith
  · rw [abs_of_nonneg (by linarith)]; linarith

lemma bb_nonneg (p q w : ℝ) (hpq : p < q) (hw : 0 < w) (x : ℝ) : 0 ≤ bb p q w hpq hw x :=
  ContDiffBump.nonneg _

lemma bb_le_one (p q w : ℝ) (hpq : p < q) (hw : 0 < w) (x : ℝ) : bb p q w hpq hw x ≤ 1 :=
  ContDiffBump.le_one _

/-- The bump as a Schwartz function. -/
def Sb (p q w : ℝ) (hpq : p < q) (hw : 0 < w) : SchwartzMap ℝ ℂ :=
  (((bb p q w hpq hw).hasCompactSupport).comp_left Complex.ofReal_zero).toSchwartzMap
    (Complex.ofRealCLM.contDiff.comp (bb p q w hpq hw).contDiff)

lemma Sb_apply (p q w : ℝ) (hpq : p < q) (hw : 0 < w) (x : ℝ) :
    Sb p q w hpq hw x = ((bb p q w hpq hw x : ℝ) : ℂ) := rfl

/-- The CLT for bumps, in real form. -/
theorem clt_bb {ι : Type*} [Fintype ι] [DecidableEq ι] {p₁ q₁ w₁ p₂ q₂ w₂ : ℝ}
    (h₁ : p₁ < q₁) (k₁ : 0 < w₁) (h₂ : p₂ < q₂) (k₂ : 0 < w₂)
    (a b : ι → ℝ) (ρ : ℝ) (ha : ∑ i, a i ^ 2 = 1) (hb : ∑ i, b i ^ 2 = 1)
    (hab : ∑ i, a i * b i = ρ) :
    |EE (fun ε => bb p₁ q₁ w₁ h₁ k₁ (ssum ε a) * bb p₂ q₂ w₂ h₂ k₂ (ssum ε b))
      - ∫ z, bb p₁ q₁ w₁ h₁ k₁ z.1 * bb p₂ q₂ w₂ h₂ k₂ (ρ * z.1 + √(1 - ρ ^ 2) * z.2) ∂(γ.prod γ)|
      ≤ 16 * (2 * π) ^ 4 * (Mom 4 (Sb p₁ q₁ w₁ h₁ k₁) * Mom 0 (Sb p₂ q₂ w₂ h₂ k₂) * ∑ i, a i ^ 4
          + Mom 0 (Sb p₁ q₁ w₁ h₁ k₁) * Mom 4 (Sb p₂ q₂ w₂ h₂ k₂) * ∑ i, b i ^ 4) := by
  have hρ := abs_rho_le a b ρ ha hb hab
  have h := clt_two (Sb p₁ q₁ w₁ h₁ k₁) (Sb p₂ q₂ w₂ h₂ k₂) a b ρ ha hb hab
  have hσ : √(1 - ρ ^ 2) ^ 2 = 1 - ρ ^ 2 := Real.sq_sqrt (by linarith)
  have hG := gauss_two (Sb p₁ q₁ w₁ h₁ k₁) (Sb p₂ q₂ w₂ h₂ k₂) ρ (√(1 - ρ ^ 2))
  have hk : ∀ u v : ℝ, Complex.exp (-(2 * π ^ 2 * ((u + ρ * v) ^ 2 + √(1 - ρ ^ 2) ^ 2 * v ^ 2) : ℝ))
      = (gk ρ u v : ℂ) := by
    intro u v; unfold gk; rw [hσ, Complex.ofReal_exp]; congr 1; push_cast; ring
  simp_rw [hk] at hG
  rw [← hG] at h
  simp only [Sb_apply] at h
  have e1 : (∑ ε : ι → ℤˣ, ((bb p₁ q₁ w₁ h₁ k₁ (ssum ε a) : ℝ) : ℂ) *
      ((bb p₂ q₂ w₂ h₂ k₂ (ssum ε b) : ℝ) : ℂ)) / 2 ^ Fintype.card ι
      = ((EE (fun ε => bb p₁ q₁ w₁ h₁ k₁ (ssum ε a) * bb p₂ q₂ w₂ h₂ k₂ (ssum ε b)) : ℝ) : ℂ) := by
    unfold EE; push_cast; rfl
  have e2 : ∫ z, ((bb p₁ q₁ w₁ h₁ k₁ z.1 : ℝ) : ℂ) *
      ((bb p₂ q₂ w₂ h₂ k₂ (ρ * z.1 + √(1 - ρ ^ 2) * z.2) : ℝ) : ℂ) ∂(γ.prod γ)
      = ((∫ z, bb p₁ q₁ w₁ h₁ k₁ z.1 * bb p₂ q₂ w₂ h₂ k₂ (ρ * z.1 + √(1 - ρ ^ 2) * z.2)
          ∂(γ.prod γ) : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]; push_cast; rfl
  rw [e1, e2, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] at h
  exact h

/-- Integrals of `[0, 1]`-valued functions vs. measures of sets. -/
lemma integral_le_of_supp {f : ℝ × ℝ → ℝ} (hf : Continuous f) (h0 : ∀ z, 0 ≤ f z)
    (h1 : ∀ z, f z ≤ 1) {A : Set (ℝ × ℝ)} (hA : MeasurableSet A) (hfA : ∀ z, z ∉ A → f z = 0) :
    ∫ z, f z ∂(γ.prod γ) ≤ (γ.prod γ).real A := by
  rw [← integral_indicator_one hA]
  refine integral_mono (Integrable.mono' (integrable_const (1 : ℝ)) hf.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun z => by rw [Real.norm_eq_abs, abs_of_nonneg (h0 z)]; exact h1 z)))
    ((integrable_const (1 : ℝ)).indicator hA) (fun z => ?_)
  by_cases hz : z ∈ A
  · rw [Set.indicator_of_mem hz]; exact h1 z
  · rw [Set.indicator_of_notMem hz, hfA z hz]

lemma integral_ge_of_one {f : ℝ × ℝ → ℝ} (hf : Continuous f) (h0 : ∀ z, 0 ≤ f z)
    (h1 : ∀ z, f z ≤ 1) {B : Set (ℝ × ℝ)} (hB : MeasurableSet B) (hfB : ∀ z, z ∈ B → f z = 1) :
    (γ.prod γ).real B ≤ ∫ z, f z ∂(γ.prod γ) := by
  rw [← integral_indicator_one hB]
  refine integral_mono ((integrable_const (1 : ℝ)).indicator hB)
    (Integrable.mono' (integrable_const (1 : ℝ)) hf.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun z => by rw [Real.norm_eq_abs, abs_of_nonneg (h0 z)]; exact h1 z)))
    (fun z => ?_)
  by_cases hz : z ∈ B
  · rw [Set.indicator_of_mem hz, hfB z hz]; rfl
  · rw [Set.indicator_of_notMem hz]; exact h0 z

/-- The constant of the quadrant bounds. -/
def Cq (p₁ q₁ w₁ p₂ q₂ w₂ : ℝ) (h₁ : p₁ < q₁) (k₁ : 0 < w₁) (h₂ : p₂ < q₂) (k₂ : 0 < w₂) : ℝ :=
  16 * (2 * π) ^ 4 * (Mom 4 (Sb p₁ q₁ w₁ h₁ k₁) * Mom 0 (Sb p₂ q₂ w₂ h₂ k₂)
    + Mom 0 (Sb p₁ q₁ w₁ h₁ k₁) * Mom 4 (Sb p₂ q₂ w₂ h₂ k₂))

lemma clt_bb' {ι : Type*} [Fintype ι] [DecidableEq ι] {p₁ q₁ w₁ p₂ q₂ w₂ : ℝ}
    (h₁ : p₁ < q₁) (k₁ : 0 < w₁) (h₂ : p₂ < q₂) (k₂ : 0 < w₂)
    (a b : ι → ℝ) (ρ : ℝ) (ha : ∑ i, a i ^ 2 = 1) (hb : ∑ i, b i ^ 2 = 1)
    (hab : ∑ i, a i * b i = ρ) :
    |EE (fun ε => bb p₁ q₁ w₁ h₁ k₁ (ssum ε a) * bb p₂ q₂ w₂ h₂ k₂ (ssum ε b))
      - ∫ z, bb p₁ q₁ w₁ h₁ k₁ z.1 * bb p₂ q₂ w₂ h₂ k₂ (ρ * z.1 + √(1 - ρ ^ 2) * z.2) ∂(γ.prod γ)|
      ≤ Cq p₁ q₁ w₁ p₂ q₂ w₂ h₁ k₁ h₂ k₂ * (∑ i, a i ^ 4 + ∑ i, b i ^ 4) := by
  refine (clt_bb h₁ k₁ h₂ k₂ a b ρ ha hb hab).trans ?_
  unfold Cq
  have m1 := mom_nonneg 4 (Sb p₁ q₁ w₁ h₁ k₁)
  have m2 := mom_nonneg 0 (Sb p₂ q₂ w₂ h₂ k₂)
  have m3 := mom_nonneg 0 (Sb p₁ q₁ w₁ h₁ k₁)
  have m4 := mom_nonneg 4 (Sb p₂ q₂ w₂ h₂ k₂)
  have hA : 0 ≤ ∑ i, a i ^ 4 := Finset.sum_nonneg (fun i _ => by positivity)
  have hB : 0 ≤ ∑ i, b i ^ 4 := Finset.sum_nonneg (fun i _ => by positivity)
  have hc : (0 : ℝ) ≤ 16 * (2 * π) ^ 4 := by positivity
  have key : Mom 4 (Sb p₁ q₁ w₁ h₁ k₁) * Mom 0 (Sb p₂ q₂ w₂ h₂ k₂) * ∑ i, a i ^ 4
      + Mom 0 (Sb p₁ q₁ w₁ h₁ k₁) * Mom 4 (Sb p₂ q₂ w₂ h₂ k₂) * ∑ i, b i ^ 4
      ≤ (Mom 4 (Sb p₁ q₁ w₁ h₁ k₁) * Mom 0 (Sb p₂ q₂ w₂ h₂ k₂)
        + Mom 0 (Sb p₁ q₁ w₁ h₁ k₁) * Mom 4 (Sb p₂ q₂ w₂ h₂ k₂)) * (∑ i, a i ^ 4 + ∑ i, b i ^ 4) := by
    nlinarith [mul_nonneg (mul_nonneg m1 m2) hB, mul_nonneg (mul_nonneg m3 m4) hA]
  calc _ ≤ 16 * (2 * π) ^ 4 * ((Mom 4 (Sb p₁ q₁ w₁ h₁ k₁) * Mom 0 (Sb p₂ q₂ w₂ h₂ k₂)
        + Mom 0 (Sb p₁ q₁ w₁ h₁ k₁) * Mom 4 (Sb p₂ q₂ w₂ h₂ k₂)) * (∑ i, a i ^ 4 + ∑ i, b i ^ 4)) :=
        mul_le_mul_of_nonneg_left key hc
    _ = _ := by ring

/-- **Upper quadrant bound.** -/
theorem quad_up {ι : Type*} [Fintype ι] [DecidableEq ι] (a b : ι → ℝ) (ρ : ℝ)
    (ha : ∑ i, a i ^ 2 = 1) (hb : ∑ i, b i ^ 2 = 1) (hab : ∑ i, a i * b i = ρ)
    (hρ1 : -1 < ρ) (hρ2 : ρ < 1) {R w : ℝ} (hR : 0 < R) (hw : 0 < w) :
    PP (fun ε => 0 < ssum ε a ∧ ssum ε b < 0)
      ≤ Real.arccos ρ / (2 * π) + 2 * w / √(2 * π) + 2 / R ^ 2
        + Cq 0 R w (-R) 0 w hR hw (by linarith) hw * (∑ i, a i ^ 4 + ∑ i, b i ^ 4) := by
  classical
  have hR' : -R < 0 := by linarith
  have hclt := clt_bb' hR hw hR' hw a b ρ ha hb hab
  set f₁ := bb 0 R w hR hw
  set f₂ := bb (-R) 0 w hR' hw
  set σ := √(1 - ρ ^ 2) with hσdef
  have hσ : ρ ^ 2 + σ ^ 2 = 1 := by rw [hσdef, Real.sq_sqrt (by nlinarith)]; ring
  -- pointwise
  have hpt : ∀ ε : ι → ℤˣ, (if 0 < ssum ε a ∧ ssum ε b < 0 then (1 : ℝ) else 0)
      ≤ f₁ (ssum ε a) * f₂ (ssum ε b) + (if R ≤ |ssum ε a| then 1 else 0)
        + (if R ≤ |ssum ε b| then 1 else 0) := by
    intro ε
    have n1 := bb_nonneg 0 R w hR hw (ssum ε a)
    have n2 := bb_nonneg (-R) 0 w (by linarith) hw (ssum ε b)
    split_ifs with h hA hB hB <;> try nlinarith
    push Not at hA hB
    rw [abs_lt] at hA hB
    rw [bb_one hR hw ⟨h.1.le, by linarith⟩, bb_one (by linarith) hw ⟨by linarith, h.2.le⟩]
    norm_num
  have hP : PP (fun ε => 0 < ssum ε a ∧ ssum ε b < 0)
      ≤ EE (fun ε => f₁ (ssum ε a) * f₂ (ssum ε b)) + PP (fun ε => R ≤ |ssum ε a|)
        + PP (fun ε => R ≤ |ssum ε b|) := by
    rw [PP_eq, PP_eq, PP_eq, ← EE_add, ← EE_add]
    exact EE_mono hpt
  have t1 := cheb_ssum a hR
  have t2 := cheb_ssum b hR
  rw [ha] at t1; rw [hb] at t2
  -- the Gaussian integral
  have hint : ∫ z, f₁ z.1 * f₂ (ρ * z.1 + σ * z.2) ∂(γ.prod γ)
      ≤ Real.arccos ρ / (2 * π) + 2 * w / √(2 * π) := by
    set A := {z : ℝ × ℝ | z.1 ∈ Set.Ioo (0 - w) (R + w) ∧ ρ * z.1 + σ * z.2 ∈ Set.Ioo (-R - w) (0 + w)}
    have hA : MeasurableSet A := by
      simp only [A, Set.setOf_and]
      apply MeasurableSet.inter
      · exact measurableSet_Ioo.preimage measurable_fst
      · exact measurableSet_Ioo.preimage (by fun_prop)
    have h1 := integral_le_of_supp (f := fun z : ℝ × ℝ => f₁ z.1 * f₂ (ρ * z.1 + σ * z.2))
      ((f₁.continuous.comp continuous_fst).mul (f₂.continuous.comp (by fun_prop))) (fun z => mul_nonneg (bb_nonneg _ _ _ _ _ _) (bb_nonneg _ _ _ _ _ _))
      (fun z => mul_le_one₀ (bb_le_one _ _ _ _ _ _) (bb_nonneg _ _ _ _ _ _) (bb_le_one _ _ _ _ _ _))
      hA (fun z hz => by
        simp only [A, Set.mem_ofPred_eq, not_and_or] at hz
        rcases hz with hz | hz
        · rw [bb_zero hR hw hz, zero_mul]
        · rw [bb_zero (by linarith) hw hz, mul_zero])
    refine h1.trans ?_
    have hsub : A ⊆ {z : ℝ × ℝ | 0 < z.1 ∧ ρ * z.1 + σ * z.2 < 0} ∪
        {z : ℝ × ℝ | z.1 ∈ Set.Icc (-w) 0} ∪ {z : ℝ × ℝ | ρ * z.1 + σ * z.2 ∈ Set.Icc 0 w} := by
      intro z hz
      simp only [A, Set.mem_ofPred_eq, Set.mem_Ioo] at hz
      simp only [Set.mem_union, Set.mem_ofPred_eq, Set.mem_Icc]
      by_cases h1 : 0 < z.1
      · by_cases h2 : ρ * z.1 + σ * z.2 < 0
        · exact Or.inl (Or.inl ⟨h1, h2⟩)
        · exact Or.inr ⟨by linarith, by linarith⟩
      · exact Or.inl (Or.inr ⟨by linarith, by linarith⟩)
    calc (γ.prod γ).real A
        ≤ (γ.prod γ).real ({z : ℝ × ℝ | 0 < z.1 ∧ ρ * z.1 + σ * z.2 < 0} ∪
            {z : ℝ × ℝ | z.1 ∈ Set.Icc (-w) 0} ∪ {z : ℝ × ℝ | ρ * z.1 + σ * z.2 ∈ Set.Icc 0 w}) :=
          measureReal_mono hsub
      _ ≤ (γ.prod γ).real {z : ℝ × ℝ | 0 < z.1 ∧ ρ * z.1 + σ * z.2 < 0}
          + (γ.prod γ).real {z : ℝ × ℝ | z.1 ∈ Set.Icc (-w) 0}
          + (γ.prod γ).real {z : ℝ × ℝ | ρ * z.1 + σ * z.2 ∈ Set.Icc 0 w} := by
          refine (measureReal_union_le _ _).trans ?_
          gcongr
          exact measureReal_union_le _ _
      _ ≤ Real.arccos ρ / (2 * π) + (0 - -w) / √(2 * π) + (w - 0) / √(2 * π) := by
          gcongr
          · rw [hσdef, wedge_real hρ1 hρ2]
          · exact strip_X (-w) 0 (by linarith)
          · exact strip_Y ρ σ hσ 0 w hw.le
      _ = _ := by ring
  have hc := (abs_le.mp hclt).2
  have final : PP (fun ε => 0 < ssum ε a ∧ ssum ε b < 0)
      ≤ Real.arccos ρ / (2 * π) + 2 * w / √(2 * π) + 2 / R ^ 2
        + Cq 0 R w (-R) 0 w hR hw hR' hw * (∑ i, a i ^ 4 + ∑ i, b i ^ 4) := by
    have e : (2 : ℝ) / R ^ 2 = 1 / R ^ 2 + 1 / R ^ 2 := by ring
    linarith
  exact final

/-- **Lower quadrant bound (with margin `τ`).** -/
theorem quad_low {ι : Type*} [Fintype ι] [DecidableEq ι] (a b : ι → ℝ) (ρ : ℝ)
    (ha : ∑ i, a i ^ 2 = 1) (hb : ∑ i, b i ^ 2 = 1) (hab : ∑ i, a i * b i = ρ)
    (hρ1 : -1 < ρ) (hρ2 : ρ < 1) {τ R w : ℝ} (hτ : 0 ≤ τ) (hw : 0 < w) (hR : τ + 2 * w < R) :
    Real.arccos ρ / (2 * π) - 2 * (τ + 2 * w) / √(2 * π) - 2 / R ^ 2
        - Cq (τ + 2 * w) R w (-R) (-τ - 2 * w) w hR hw (by linarith) hw
          * (∑ i, a i ^ 4 + ∑ i, b i ^ 4)
      ≤ PP (fun ε => τ < ssum ε a ∧ ssum ε b < -τ) := by
  classical
  have hR0 : 0 < R := by linarith
  have hR' : -R < -τ - 2 * w := by linarith
  have hclt := clt_bb' hR hw hR' hw a b ρ ha hb hab
  set f₁ := bb (τ + 2 * w) R w hR hw
  set f₂ := bb (-R) (-τ - 2 * w) w hR' hw
  set σ := √(1 - ρ ^ 2) with hσdef
  have hσ : ρ ^ 2 + σ ^ 2 = 1 := by rw [hσdef, Real.sq_sqrt (by nlinarith)]; ring
  have hpt : ∀ ε : ι → ℤˣ, f₁ (ssum ε a) * f₂ (ssum ε b)
      ≤ if τ < ssum ε a ∧ ssum ε b < -τ then (1 : ℝ) else 0 := by
    intro ε
    split_ifs with h
    · exact mul_le_one₀ (bb_le_one _ _ _ _ _ _) (bb_nonneg _ _ _ _ _ _) (bb_le_one _ _ _ _ _ _)
    · rw [not_and_or, not_lt, not_lt] at h
      rcases h with h | h
      · rw [bb_zero (p := τ + 2 * w) (q := R) (x := ssum ε a) hR hw
          (by simp only [Set.mem_Ioo, not_and_or, not_lt]; left; linarith), zero_mul]
      · rw [bb_zero (p := -R) (q := -τ - 2 * w) (x := ssum ε b) (by linarith) hw
          (by simp only [Set.mem_Ioo, not_and_or, not_lt]; right; linarith), mul_zero]
  have hP : EE (fun ε => f₁ (ssum ε a) * f₂ (ssum ε b))
      ≤ PP (fun ε => τ < ssum ε a ∧ ssum ε b < -τ) := by rw [PP_eq]; exact EE_mono hpt
  have hint : Real.arccos ρ / (2 * π) - 2 * (τ + 2 * w) / √(2 * π) - 2 / R ^ 2
      ≤ ∫ z, f₁ z.1 * f₂ (ρ * z.1 + σ * z.2) ∂(γ.prod γ) := by
    set B := {z : ℝ × ℝ | z.1 ∈ Set.Icc (τ + 2 * w) R ∧ ρ * z.1 + σ * z.2 ∈ Set.Icc (-R) (-τ - 2 * w)}
    have hB : MeasurableSet B := by
      simp only [B, Set.setOf_and]
      apply MeasurableSet.inter
      · exact measurableSet_Icc.preimage measurable_fst
      · exact measurableSet_Icc.preimage (by fun_prop)
    have h1 := integral_ge_of_one (f := fun z : ℝ × ℝ => f₁ z.1 * f₂ (ρ * z.1 + σ * z.2))
      ((f₁.continuous.comp continuous_fst).mul (f₂.continuous.comp (by fun_prop))) (fun z => mul_nonneg (bb_nonneg _ _ _ _ _ _) (bb_nonneg _ _ _ _ _ _))
      (fun z => mul_le_one₀ (bb_le_one _ _ _ _ _ _) (bb_nonneg _ _ _ _ _ _) (bb_le_one _ _ _ _ _ _))
      hB (fun z hz => by
        simp only [B, Set.mem_ofPred_eq] at hz
        simp only [f₁, f₂]
        rw [bb_one hR hw hz.1, bb_one (by linarith) hw hz.2, mul_one])
    refine le_trans ?_ h1
    have hsub : {z : ℝ × ℝ | 0 < z.1 ∧ ρ * z.1 + σ * z.2 < 0} ⊆ B ∪
        {z : ℝ × ℝ | z.1 ∈ Set.Icc 0 (τ + 2 * w)} ∪
        {z : ℝ × ℝ | ρ * z.1 + σ * z.2 ∈ Set.Icc (-τ - 2 * w) 0} ∪ {z : ℝ × ℝ | R ≤ |z.1|} ∪
        {z : ℝ × ℝ | R ≤ |ρ * z.1 + σ * z.2|} := by
      intro z ⟨h1, h2⟩
      simp only [B, Set.mem_union, Set.mem_ofPred_eq, Set.mem_Icc]
      by_cases c1 : z.1 ≤ τ + 2 * w
      · left; left; left; right; exact ⟨h1.le, c1⟩
      by_cases c2 : -τ - 2 * w ≤ ρ * z.1 + σ * z.2
      · left; left; right; exact ⟨c2, h2.le⟩
      by_cases c3 : R ≤ |z.1|
      · left; right; exact c3
      by_cases c4 : R ≤ |ρ * z.1 + σ * z.2|
      · right; exact c4
      left; left; left; left
      push Not at c1 c2 c3 c4
      rw [abs_lt] at c3 c4
      exact ⟨⟨c1.le, c3.2.le⟩, ⟨c4.1.le, c2.le⟩⟩
    have hW := wedge_real hρ1 hρ2
    rw [← hσdef] at hW
    have s1 := strip_X 0 (τ + 2 * w) (by linarith)
    have s2 := strip_Y ρ σ hσ (-τ - 2 * w) 0 (by linarith)
    have t1 := tail_X hR0
    have t2 := tail_Y ρ σ hσ hR0
    have hmono := measureReal_mono (μ := γ.prod γ) hsub
    have u1 := measureReal_union_le (μ := γ.prod γ) (B ∪ {z : ℝ × ℝ | z.1 ∈ Set.Icc 0 (τ + 2 * w)} ∪
        {z : ℝ × ℝ | ρ * z.1 + σ * z.2 ∈ Set.Icc (-τ - 2 * w) 0} ∪ {z : ℝ × ℝ | R ≤ |z.1|})
        {z : ℝ × ℝ | R ≤ |ρ * z.1 + σ * z.2|}
    have u2 := measureReal_union_le (μ := γ.prod γ) (B ∪ {z : ℝ × ℝ | z.1 ∈ Set.Icc 0 (τ + 2 * w)} ∪
        {z : ℝ × ℝ | ρ * z.1 + σ * z.2 ∈ Set.Icc (-τ - 2 * w) 0}) {z : ℝ × ℝ | R ≤ |z.1|}
    have u3 := measureReal_union_le (μ := γ.prod γ) (B ∪ {z : ℝ × ℝ | z.1 ∈ Set.Icc 0 (τ + 2 * w)})
        {z : ℝ × ℝ | ρ * z.1 + σ * z.2 ∈ Set.Icc (-τ - 2 * w) 0}
    have u4 := measureReal_union_le (μ := γ.prod γ) B {z : ℝ × ℝ | z.1 ∈ Set.Icc 0 (τ + 2 * w)}
    have e1 : (τ + 2 * w - 0) / √(2 * π) + (0 - (-τ - 2 * w)) / √(2 * π)
        = 2 * (τ + 2 * w) / √(2 * π) := by ring
    have e2 : 1 / R ^ 2 + 1 / R ^ 2 = 2 / R ^ 2 := by ring
    linarith
  have hc := (abs_le.mp hclt).1
  have final : Real.arccos ρ / (2 * π) - 2 * (τ + 2 * w) / √(2 * π) - 2 / R ^ 2
        - Cq (τ + 2 * w) R w (-R) (-τ - 2 * w) w hR hw hR' hw * (∑ i, a i ^ 4 + ∑ i, b i ^ 4)
      ≤ PP (fun ε => τ < ssum ε a ∧ ssum ε b < -τ) := by linarith
  exact final

end R522

end S_RR5

end S_C4


end
