/-
Copyright 2026 Ming-Chih Kao. Licensed under the Apache License, Version 2.0;
see the LICENSE file at the root of this repository.
-/
module

public import E521.Part4

/-! Part of the proof of Erdős 521 (see `E521/Part1.lean` for the port notes): sections P3–D6, F0 of the
merged Left to Solve file `proofs/erdos-521.lean`. -/

@[expose] public section

-- ===== P3 =====
section S_P3

/-! Forward cylinder events and the bridge to sign-vector averages (original). -/

open Finset MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace E521

lemma rs_preimage_singleton (s : Finset ℕ) (r : s → Bool) :
    rs s ⁻¹' {r} = Set.pi (↑s) (fun i => {if h : i ∈ s then r ⟨i, h⟩ else false}) := by
  ext ω
  simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_pi, mem_coe]
  constructor
  · intro h i hi; subst h; simp [rs, hi]
  · intro h; funext i; have := h i i.2; simp only [dif_pos i.2] at this; exact this

lemma μS_rs_singleton (s : Finset ℕ) (r : s → Bool) : μS (rs s ⁻¹' {r}) = (2⁻¹ : ℝ≥0∞) ^ s.card := by
  rw [rs_preimage_singleton, μS]
  have h := Measure.infinitePi_pi (μ := fun _ : ℕ => ν) (s := s)
    (t := fun i => ({if h : i ∈ s then r ⟨i, h⟩ else false} : Set Bool)) (fun i _ => measurableSet_singleton _)
  refine h.trans ?_
  simp only [ν_singleton, prod_const]

lemma μS_rs_real (s : Finset ℕ) (Q : Finset (s → Bool)) :
    μS.real (rs s ⁻¹' (Q : Set (s → Bool))) = Q.card / 2 ^ s.card := by
  have : rs s ⁻¹' (Q : Set (s → Bool)) = ⋃ r ∈ Q, rs s ⁻¹' {r} := by ext ω; simp
  rw [Measure.real, this, measure_biUnion_finset]
  · simp only [μS_rs_singleton, sum_const, nsmul_eq_mul]
    rw [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_inv]
    simp [div_eq_mul_inv]
  · intro p _ q _ hpq
    simp only [Function.onFun]
    rw [Set.disjoint_iff]
    intro ω ⟨h1, h2⟩
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at h1 h2
    exact hpq (h1.symm.trans h2)
  · intro r _; exact measurable_rs s (measurableSet_singleton r)

/-- real signs of `ω`. -/
def eR (ω : ℕ → Bool) (j : ℕ) : ℝ := if ω j then 1 else -1

lemma eR_pm (ω : ℕ → Bool) (j : ℕ) : eR ω j = 1 ∨ eR ω j = -1 := by
  unfold eR; split_ifs <;> simp

/-- the weak sign-change event of the forward two-fold sums at `k`. -/
def Iev (k : ℕ) : Set (ℕ → Bool) :=
  {ω | E521D.Ip (E521D.c2 (eR ω) k) (E521D.c2 (eR ω) (k + 1))}

end E521

namespace E521

/-- Bool patterns on `range n` vs sign vectors on `Fin n`. -/
def toSigns (n : ℕ) (r : range n → Bool) : Fin n → ℤˣ :=
  fun j => if r ⟨j, mem_range.mpr j.2⟩ then 1 else -1

def ofSigns (n : ℕ) (ε : Fin n → ℤˣ) : range n → Bool :=
  fun i => decide (ε ⟨i, mem_range.mp i.2⟩ = 1)

lemma units_eq (u : ℤˣ) : u = 1 ∨ u = -1 := Int.units_eq_one_or u

def signEquiv (n : ℕ) : (range n → Bool) ≃ (Fin n → ℤˣ) where
  toFun := toSigns n
  invFun := ofSigns n
  left_inv r := by
    funext i
    simp only [ofSigns, toSigns]
    by_cases h : r ⟨(i : ℕ), mem_range.mpr (mem_range.mp i.2)⟩ <;> simp_all
  right_inv ε := by
    funext j
    simp only [ofSigns, toSigns]
    rcases units_eq (ε j) with h | h <;> simp [h]

lemma toSigns_val (n : ℕ) (r : range n → Bool) (j : Fin n) :
    (((toSigns n r j : ℤˣ) : ℤ) : ℝ) = if r ⟨j, mem_range.mpr j.2⟩ then 1 else -1 := by
  unfold toSigns; split_ifs <;> simp

/-- the forward signs of a pattern. -/
def extR (n : ℕ) (r : range n → Bool) (j : ℕ) : ℝ :=
  if h : j < n then (if r ⟨j, mem_range.mpr h⟩ then 1 else -1) else 0

lemma extR_rs (n : ℕ) (ω : ℕ → Bool) {j : ℕ} (hj : j < n) : extR n (rs (range n) ω) j = eR ω j := by
  (unfold extR rs eR; rw [dif_pos hj]) <;> (split_ifs <;> simp_all)

lemma c2_ext (k : ℕ) (ω : ℕ → Bool) (i : ℕ) (hi : i ≤ k + 1) :
    E521D.c2 (eR ω) i = E521D.c2 (extR (k + 2) (rs (range (k + 2)) ω)) i := by
  unfold E521D.c2
  apply sum_congr rfl; intro j hj; rw [mem_range] at hj
  rw [extR_rs _ _ (by omega)]

lemma Iev_cyl (k : ℕ) :
    Iev k = rs (range (k + 2)) ⁻¹' {r | E521D.Ip (E521D.c2 (extR (k + 2) r) k)
      (E521D.c2 (extR (k + 2) r) (k + 1))} := by
  ext ω
  simp only [Iev, Set.mem_setOf_eq, Set.mem_preimage]
  rw [c2_ext k ω k (by omega), c2_ext k ω (k + 1) le_rfl]

lemma card_bridge (n : ℕ) (P : (range n → Bool) → Prop) [DecidablePred P] :
    (univ.filter P).card = (univ.filter (fun ε : Fin n → ℤˣ => P (ofSigns n ε))).card := by
  apply card_bij (fun r _ => toSigns n r)
  · intro r hr; simp only [mem_filter, mem_univ, true_and] at hr ⊢
    have : ofSigns n (toSigns n r) = r := (signEquiv n).left_inv r
    rw [this]; exact hr
  · intro r1 _ r2 _ h; exact (signEquiv n).injective h
  · intro ε hε; refine ⟨ofSigns n ε, ?_, (signEquiv n).right_inv ε⟩
    simp only [mem_filter, mem_univ, true_and] at hε ⊢; exact hε

/-- **range bridge**: a cylinder event on the first `n` coordinates has the sign-vector probability. -/
theorem μS_range_bridge (n : ℕ) (P : (range n → Bool) → Prop) [DecidablePred P] :
    μS.real (rs (range n) ⁻¹' {r | P r}) = R522.PP (fun ε : Fin n → ℤˣ => P (ofSigns n ε)) := by
  classical
  have h := μS_rs_real (range n) (univ.filter P)
  have e : ((univ.filter P : Finset (range n → Bool)) : Set (range n → Bool)) = {r | P r} := by
    ext r; simp
  rw [e] at h
  rw [h, R522.PP_eq]
  unfold R522.EE
  rw [card_range, Fintype.card_fin, card_bridge n P]
  congr 1
  rw [card_filter]; push_cast
  apply sum_congr rfl; intro ε _; split_ifs <;> simp

lemma extR_ofSigns (n : ℕ) (ε : Fin n → ℤˣ) (j : ℕ) (hj : j < n) :
    extR n (ofSigns n ε) j = ((ε ⟨j, hj⟩ : ℤ) : ℝ) := by
  unfold extR ofSigns
  rw [dif_pos hj]
  rcases units_eq (ε ⟨j, hj⟩) with h | h <;> simp [h]

end E521

end S_P3

-- ===== P4 =====
section S_P4

/-! The probability of a weak sign change at `k` is the sign-vector quantity `p_k` (original). -/

open Finset MeasureTheory

namespace E521

lemma c2_signs (k : ℕ) (ε : Fin (k + 2) → ℤˣ) :
    E521D.c2 (extR (k + 2) (ofSigns (k + 2) ε)) k = R522.ssum ε (R522.wt (k + 2)) ∧
    E521D.c2 (extR (k + 2) (ofSigns (k + 2) ε)) (k + 1) =
      R522.ssum ε (R522.wt (k + 2)) + R522.ssum ε (fun _ => (1 : ℝ)) := by
  set e := extR (k + 2) (ofSigns (k + 2) ε)
  have he : ∀ j (hj : j < k + 2), e j = ((ε ⟨j, hj⟩ : ℤ) : ℝ) := fun j hj => extR_ofSigns _ ε j hj
  have hw : R522.ssum ε (R522.wt (k + 2)) = ∑ j ∈ range (k + 2), e j * ((k : ℝ) + 1 - j) := by
    unfold R522.ssum R522.wt
    rw [Fin.sum_univ_eq_sum_range (fun j => e j * ((k : ℝ) + 1 - j)) (k + 2) |>.symm]
    apply Fintype.sum_congr; intro j; rw [he j j.2]; push_cast; ring
  have h1 : R522.ssum ε (fun _ => (1 : ℝ)) = ∑ j ∈ range (k + 2), e j := by
    unfold R522.ssum
    rw [Fin.sum_univ_eq_sum_range (fun j => e j) (k + 2) |>.symm]
    apply Fintype.sum_congr; intro j; rw [he j j.2]; ring
  constructor
  · rw [hw]; unfold E521D.c2
    rw [show k + 2 = (k + 1) + 1 by ring, sum_range_succ (fun j => e j * ((k : ℝ) + 1 - j)) (k + 1)]
    have : ((k : ℝ) + 1 - ((k + 1 : ℕ) : ℝ)) = 0 := by push_cast; ring
    rw [this, mul_zero, add_zero]
    apply sum_congr rfl; intro j _; ring
  · rw [hw, h1, ← sum_add_distrib]; unfold E521D.c2
    apply sum_congr rfl; intro j _; push_cast; ring

/-- **`μ(I_k) = p_k`.** -/
theorem Iev_real (k : ℕ) : μS.real (Iev k) = R522.PP (R522.SCev (k + 2)) := by
  classical
  rw [Iev_cyl, μS_range_bridge]
  congr 1; funext ε
  obtain ⟨h1, h2⟩ := c2_signs k ε
  apply propext
  simp only [E521D.Ip, R522.SCev]
  rw [h1, h2]

end E521

end S_P4

-- ===== P5 =====
section S_P5

/-! Hoeffding for blocks of coordinates under `μS`; the tail event (original). -/

open Finset MeasureTheory

namespace E521

/-- `μ (|∑_{j<l} ε_j| ≥ x) ≤ 2 exp (-x²/(2l))`. -/
lemma block_hoeffding (l : ℕ) (hl : 1 ≤ l) {x : ℝ} (hx : 0 < x) :
    μS.real {ω | x ≤ |∑ j ∈ range l, eR ω j|} ≤ 2 * Real.exp (-(x ^ 2 / (2 * l))) := by
  classical
  have hcyl : {ω | x ≤ |∑ j ∈ range l, eR ω j|} =
      rs (range l) ⁻¹' {r | x ≤ |∑ j ∈ range l, extR l r j|} := by
    ext ω; simp only [Set.mem_setOf_eq, Set.mem_preimage]
    congr! 2
    apply sum_congr rfl; intro j hj; rw [mem_range] at hj; rw [extR_rs _ _ hj]
  rw [hcyl, μS_range_bridge]
  have e : ∀ ε : Fin l → ℤˣ, ∑ j ∈ range l, extR l (ofSigns l ε) j = R522.ssum ε (fun _ => (1 : ℝ)) := by
    intro ε
    unfold R522.ssum
    rw [Fin.sum_univ_eq_sum_range (fun j => extR l (ofSigns l ε) j) l |>.symm]
    apply Fintype.sum_congr; intro j; rw [extR_ofSigns _ ε j j.2]; ring
  simp_rw [e]
  have h := R522.hoeffding (ι := Fin l) (fun _ => (1 : ℝ)) hx
  simp only [one_pow, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one] at h
  exact h

end E521

namespace E521

/-- Hoeffding for a block with unit-modulus weights. -/
lemma block_hoeffding_w (l : ℕ) (w : ℕ → ℝ) (hw : ∀ j, w j ^ 2 = 1) {x : ℝ} (hx : 0 < x) :
    μS.real {ω | x ≤ |∑ j ∈ range l, w j * eR ω j|} ≤ 2 * Real.exp (-(x ^ 2 / (2 * l))) := by
  classical
  have hcyl : {ω | x ≤ |∑ j ∈ range l, w j * eR ω j|} =
      rs (range l) ⁻¹' {r | x ≤ |∑ j ∈ range l, w j * extR l r j|} := by
    ext ω; simp only [Set.mem_setOf_eq, Set.mem_preimage]
    congr! 2
    apply sum_congr rfl; intro j hj; rw [mem_range] at hj; rw [extR_rs _ _ hj]
  rw [hcyl, μS_range_bridge]
  have e : ∀ ε : Fin l → ℤˣ, ∑ j ∈ range l, w j * extR l (ofSigns l ε) j = R522.ssum ε (fun j => w j) := by
    intro ε
    unfold R522.ssum
    rw [Fin.sum_univ_eq_sum_range (fun j => w j * extR l (ofSigns l ε) j) l |>.symm]
    apply Fintype.sum_congr; intro j; rw [extR_ofSigns _ ε j j.2]; ring
  simp_rw [e]
  have h := R522.hoeffding (ι := Fin l) (fun j => w j) hx
  have hs : ∑ i : Fin l, w i ^ 2 = l := by simp [hw]
  rw [hs] at h
  exact h

/-- the backward block sum, shifted to the front. -/
lemma back_shift (n l : ℕ) (hl : l ≤ n + 1) (w : ℕ → ℝ) (ω : ℕ → Bool) :
    ∑ i ∈ range l, w i * eR ω (n - i) =
      ∑ j ∈ range l, w (l - 1 - j) * eR (fun i => ω (i + (n + 1 - l))) j := by
  rw [← sum_range_reflect]
  apply sum_congr rfl; intro j hj; rw [mem_range] at hj
  have e1 : n - (l - 1 - j) = j + (n + 1 - l) := by omega
  have e2 : l - 1 - (l - 1 - j) = j := by omega
  simp only [eR, e1, e2]

end E521

end S_P5

-- ===== P6 =====
section S_P6

/-! Pair bound for cones and the independence of a forward event from the top block (original). -/

open Finset MeasureTheory

namespace E521

lemma coneE_cyl (K : ℕ) (F G : ℤ → Prop) :
    ∃ Q : Set (range (2 * K) → Bool), coneE K F G = rs (range (2 * K)) ⁻¹' Q := by
  refine ⟨{r | good2F F G K 0 0 (fun j : Fin K =>
    (r ⟨2 * K - 1 - 2 * j, by have := j.isLt; simp [mem_range]; omega⟩,
     r ⟨2 * K - 2 - 2 * j, by have := j.isLt; simp [mem_range]; omega⟩))}, ?_⟩
  ext ω; exact Iff.rfl

lemma disjoint_range_Ico (a b c : ℕ) (h : a ≤ b) : Disjoint (range a) (Ico b c) := by
  rw [Finset.disjoint_left]; intro x hx hx'; rw [mem_range] at hx; rw [mem_Ico] at hx'; omega

/-- `μ(cone_K ∩ cone_K') ≤ μ(cone_K) u_{K'-K}`. -/
theorem cone_pair (K K' : ℕ) (hKK : K ≤ K') (F G F' G' : ℤ → Prop) :
    μS.real (coneE K F G ∩ coneE K' F' G') ≤ μS.real (coneE K F G) * ((N2 (K' - K) 0 0 : ℝ) / 4 ^ (K' - K)) := by
  have hsub : coneE K F G ∩ coneE K' F' G' ⊆ coneE K F G ∩ topE K' (K' - K) :=
    Set.inter_subset_inter_right _ (cone_sub_top K' (K' - K) (by omega) F' G')
  obtain ⟨Q1, hQ1⟩ := coneE_cyl K F G
  obtain ⟨Q2, hQ2⟩ := topE_cyl K' (K' - K) (by omega)
  have hdis : Disjoint (range (2 * K)) (Ico (2 * K' - 2 * (K' - K)) (2 * K')) :=
    disjoint_range_Ico _ _ _ (by omega)
  have hind := indep_blocks hdis Q1 Q2
  rw [← hQ1, ← hQ2] at hind
  calc μS.real (coneE K F G ∩ coneE K' F' G') ≤ μS.real (coneE K F G ∩ topE K' (K' - K)) :=
        measureReal_mono hsub (measure_ne_top _ _)
    _ = μS.real (coneE K F G) * μS.real (topE K' (K' - K)) := by
        rw [Measure.real, hind, ENNReal.toReal_mul]; rfl
    _ = _ := by rw [topE_real K' (K' - K) (by omega)]

/-- `μ(cone_K ∩ I_k) ≤ u_L p_k` when the forward block `[0, k+2)` lies below the top block. -/
theorem cone_Iev (K L k : ℕ) (hL : L ≤ K) (hk : k + 2 ≤ 2 * K - 2 * L) (F G : ℤ → Prop) :
    μS.real (coneE K F G ∩ Iev k) ≤ ((N2 L 0 0 : ℝ) / 4 ^ L) * R522.PP (R522.SCev (k + 2)) := by
  have hsub : coneE K F G ∩ Iev k ⊆ topE K L ∩ Iev k :=
    Set.inter_subset_inter_left _ (cone_sub_top K L hL F G)
  obtain ⟨Q2, hQ2⟩ := topE_cyl K L hL
  have hcyl := Iev_cyl k
  have hdis : Disjoint (range (k + 2)) (Ico (2 * K - 2 * L) (2 * K)) :=
    disjoint_range_Ico _ _ _ hk
  have hind := indep_blocks hdis {r | E521D.Ip (E521D.c2 (extR (k + 2) r) k) (E521D.c2 (extR (k + 2) r) (k + 1))} Q2
  rw [← hcyl, ← hQ2] at hind
  calc μS.real (coneE K F G ∩ Iev k) ≤ μS.real (topE K L ∩ Iev k) :=
        measureReal_mono hsub (measure_ne_top _ _)
    _ = μS.real (Iev k ∩ topE K L) := by rw [Set.inter_comm]
    _ = μS.real (Iev k) * μS.real (topE K L) := by
        rw [Measure.real, hind, ENNReal.toReal_mul]; rfl
    _ = _ := by rw [topE_real K L hL, Iev_real]; ring

end E521

end S_P6

-- ===== P7 =====
section S_P7

/-! The alternating (negative-root) sign-change event has the same probability (original). -/

open Finset MeasureTheory

namespace E521

/-- coefficients of `-f(-x)`: `ẽ_j = -(-1)^j e_j`. -/
def eAlt (e : ℕ → ℝ) (j : ℕ) : ℝ := -((-1) ^ j * e j)

def Ialt (k : ℕ) : Set (ℕ → Bool) :=
  {ω | E521D.Ip (E521D.c2 (eAlt (eR ω)) k) (E521D.c2 (eAlt (eR ω)) (k + 1))}

lemma Ialt_cyl (k : ℕ) :
    Ialt k = rs (range (k + 2)) ⁻¹' {r | E521D.Ip (E521D.c2 (eAlt (extR (k + 2) r)) k)
      (E521D.c2 (eAlt (extR (k + 2) r)) (k + 1))} := by
  ext ω
  simp only [Ialt, Set.mem_setOf_eq, Set.mem_preimage]
  have h : ∀ i ≤ k + 1, E521D.c2 (eAlt (eR ω)) i = E521D.c2 (eAlt (extR (k + 2) (rs (range (k + 2)) ω))) i := by
    intro i hi
    unfold E521D.c2 eAlt
    apply sum_congr rfl; intro j hj; rw [mem_range] at hj
    rw [extR_rs _ _ (by omega)]
  rw [h k (by omega), h (k + 1) le_rfl]

/-- the involution `ε ↦ (j ↦ -(-1)^j ε_j)` on sign vectors. -/
def altU {n : ℕ} (ε : Fin n → ℤˣ) : Fin n → ℤˣ := fun j => -((-1) ^ (j : ℕ) * ε j)

lemma altU_invol {n : ℕ} (ε : Fin n → ℤˣ) : altU (altU ε) = ε := by
  funext j; simp only [altU]
  rw [neg_mul_eq_mul_neg, neg_neg, ← mul_assoc, ← pow_add, ← two_mul, pow_mul]; simp

lemma extR_ofSigns_altU (n : ℕ) (ε : Fin n → ℤˣ) (j : ℕ) (hj : j < n) :
    eAlt (extR n (ofSigns n ε)) j = extR n (ofSigns n (altU ε)) j := by
  rw [extR_ofSigns _ _ _ hj, eAlt, extR_ofSigns _ _ _ hj]
  simp only [altU]; push_cast; ring

theorem Ialt_real (k : ℕ) : μS.real (Ialt k) = R522.PP (R522.SCev (k + 2)) := by
  classical
  rw [Ialt_cyl, μS_range_bridge]
  have e : ∀ ε : Fin (k + 2) → ℤˣ, ∀ i ≤ k + 1,
      E521D.c2 (eAlt (extR (k + 2) (ofSigns (k + 2) ε))) i = E521D.c2 (extR (k + 2) (ofSigns (k + 2) (altU ε))) i := by
    intro ε i hi
    unfold E521D.c2
    apply sum_congr rfl; intro j hj; rw [mem_range] at hj
    rw [extR_ofSigns_altU _ _ _ (by omega)]
  have h1 : R522.PP (fun ε : Fin (k + 2) → ℤˣ => E521D.Ip (E521D.c2 (eAlt (extR (k + 2) (ofSigns (k + 2) ε))) k)
      (E521D.c2 (eAlt (extR (k + 2) (ofSigns (k + 2) ε))) (k + 1))) =
      R522.PP (fun ε : Fin (k + 2) → ℤˣ => R522.SCev (k + 2) (altU ε)) := by
    congr 1; funext ε
    obtain ⟨h1, h2⟩ := c2_signs k (altU ε)
    rw [e ε k (by omega), e ε (k + 1) le_rfl, h1, h2]
    rfl
  rw [h1]
  -- PP is invariant under the involution
  rw [R522.PP_eq, R522.PP_eq]
  unfold R522.EE
  congr 1
  exact Fintype.sum_equiv ⟨altU, altU, altU_invol, altU_invol⟩ _ _ (fun ε => rfl)

end E521

namespace E521

theorem cone_Ialt (K L k : ℕ) (hL : L ≤ K) (hk : k + 2 ≤ 2 * K - 2 * L) (F G : ℤ → Prop) :
    μS.real (coneE K F G ∩ Ialt k) ≤ ((N2 L 0 0 : ℝ) / 4 ^ L) * R522.PP (R522.SCev (k + 2)) := by
  have hsub : coneE K F G ∩ Ialt k ⊆ topE K L ∩ Ialt k :=
    Set.inter_subset_inter_left _ (cone_sub_top K L hL F G)
  obtain ⟨Q2, hQ2⟩ := topE_cyl K L hL
  have hcyl := Ialt_cyl k
  have hdis : Disjoint (range (k + 2)) (Ico (2 * K - 2 * L) (2 * K)) :=
    disjoint_range_Ico _ _ _ hk
  have hind := indep_blocks hdis {r | E521D.Ip (E521D.c2 (eAlt (extR (k + 2) r)) k)
    (E521D.c2 (eAlt (extR (k + 2) r)) (k + 1))} Q2
  rw [← hcyl, ← hQ2] at hind
  calc μS.real (coneE K F G ∩ Ialt k) ≤ μS.real (topE K L ∩ Ialt k) :=
        measureReal_mono hsub (measure_ne_top _ _)
    _ = μS.real (Ialt k ∩ topE K L) := by rw [Set.inter_comm]
    _ = μS.real (Ialt k) * μS.real (topE K L) := by
        rw [Measure.real, hind, ENNReal.toReal_mul]; rfl
    _ = _ := by rw [topE_real K L hL, Ialt_real]; ring

end E521

end S_P7

-- ===== D4 =====
section S_D4

/-! The closed quadrant forces nonnegative backward two-fold sums (original). -/

open Finset

namespace E521

/-- the backward sequence `a_i` read from the pairs: `a_{2j} = st (p j).1`, `a_{2j+1} = st (p j).2`. -/
lemma Tk_two_step {L : ℕ} (q : Fin L → Bool × Bool) (j : ℕ) (hj : j < L) :
    Tk q (2 * j + 1) = 2 * Uc q j + (dU (q ⟨j, hj⟩) + dV (q ⟨j, hj⟩)) ∧
    Ak q (2 * j + 1) = 2 * Vc q j + (dU (q ⟨j, hj⟩) + dV (q ⟨j, hj⟩)) := by
  obtain ⟨e1, e2⟩ := Tk_even q j hj.le
  obtain ⟨o1, o2⟩ := Tk_odd q j hj
  have hs : st (q ⟨j, hj⟩).1 = dU (q ⟨j, hj⟩) + dV (q ⟨j, hj⟩) := by
    rcases q ⟨j, hj⟩ with ⟨a, b⟩; cases a <;> cases b <;> simp [dU, dV, st]
  rw [o1, o2, e1, e2, hs]; exact ⟨rfl, rfl⟩

lemma Uc_succ {L : ℕ} (q : Fin L → Bool × Bool) (j : ℕ) (hj : j < L) :
    Uc q (j + 1) = Uc q j + dU (q ⟨j, hj⟩) := by
  unfold Uc; rw [sum_range_succ, dif_pos hj]

lemma Vc_succ {L : ℕ} (q : Fin L → Bool × Bool) (j : ℕ) (hj : j < L) :
    Vc q (j + 1) = Vc q j + dV (q ⟨j, hj⟩) := by
  unfold Vc; rw [sum_range_succ, dif_pos hj]

/-- `∑_{l ≤ k} T_l ≥ 0` on the closed quadrant (backward two-fold sums are nonnegative). -/
theorem T2_nonneg {L : ℕ} (q : Fin L → Bool × Bool) (hq : good2 L 0 0 q) :
    ∀ k ≤ 2 * L, 0 ≤ ∑ l ∈ range (k + 1), Tk q l ∧ 0 ≤ ∑ l ∈ range (k + 1), Ak q l := by
  rw [good2_iff] at hq
  -- even prefixes: ∑_{l ≤ 2J} T_l = ∑_{j<J} (U_j + 3 U_{j+1}) + V_J  (and symmetric for A)
  have heven : ∀ J ≤ L, ∑ l ∈ range (2 * J + 1), Tk q l =
      ∑ j ∈ range J, (Uc q j + 3 * Uc q (j + 1)) + Vc q J ∧
      ∑ l ∈ range (2 * J + 1), Ak q l = ∑ j ∈ range J, (Vc q j + 3 * Vc q (j + 1)) + Uc q J := by
    intro J hJ
    induction J with
    | zero => simp [Tk, Ak, Uc, Vc]
    | succ J ih =>
      obtain ⟨i1, i2⟩ := ih (by omega)
      have hJL : J < L := by omega
      rw [show 2 * (J + 1) + 1 = (2 * J + 1) + 1 + 1 by ring, sum_range_succ, sum_range_succ,
        sum_range_succ (fun l => Ak q l), sum_range_succ (fun l => Ak q l), i1, i2]
      obtain ⟨o1, o2⟩ := Tk_two_step q J hJL
      obtain ⟨e1, e2⟩ := Tk_even q (J + 1) (by omega)
      rw [show 2 * J + 1 + 1 = 2 * (J + 1) by ring, e1, e2, o1, o2, sum_range_succ, sum_range_succ,
        Uc_succ q J hJL, Vc_succ q J hJL]
      constructor <;> ring
  intro k hk
  have hU : ∀ j ≤ L, 0 ≤ Uc q j := fun j hj => by have := (hq j hj).1; simpa using this
  have hV : ∀ j ≤ L, 0 ≤ Vc q j := fun j hj => by have := (hq j hj).2; simpa using this
  have hsumU : ∀ J ≤ L, 0 ≤ ∑ j ∈ range J, (Uc q j + 3 * Uc q (j + 1)) := fun J hJ =>
    sum_nonneg (fun j hj => by rw [mem_range] at hj; linarith [hU j (by omega), hU (j + 1) (by omega)])
  have hsumV : ∀ J ≤ L, 0 ≤ ∑ j ∈ range J, (Vc q j + 3 * Vc q (j + 1)) := fun J hJ =>
    sum_nonneg (fun j hj => by rw [mem_range] at hj; linarith [hV j (by omega), hV (j + 1) (by omega)])
  obtain ⟨J, rfl | rfl⟩ := Nat.even_or_odd' k
  · obtain ⟨h1, h2⟩ := heven J (by omega)
    rw [h1, h2]
    exact ⟨by linarith [hsumU J (by omega), hV J (by omega)], by linarith [hsumV J (by omega), hU J (by omega)]⟩
  · -- k = 2J+1 < 2L
    have hJL : J < L := by omega
    obtain ⟨h1, h2⟩ := heven J (by omega)
    obtain ⟨o1, o2⟩ := Tk_two_step q J hJL
    rw [show 2 * J + 1 + 1 = (2 * J + 1) + 1 by ring, sum_range_succ, sum_range_succ (fun l => Ak q l),
      h1, h2, o1, o2]
    have hu1 := hU (J + 1) (by omega)
    have hv1 := hV (J + 1) (by omega)
    rw [Uc_succ q J hJL] at hu1
    rw [Vc_succ q J hJL] at hv1
    constructor
    · nlinarith [hsumU J (by omega), hV J (by omega), hU J (by omega)]
    · nlinarith [hsumV J (by omega), hU J (by omega), hV J (by omega)]

end E521

end S_D4

-- ===== D5 =====
section S_D5

/-! Real roots: from `ℂ` to `ℝ`, and negative roots via `x ↦ -x` (original). -/

open Polynomial

namespace E521D

open scoped Classical in
lemma realRoots_card (p : ℝ[X]) :
    ((p.map Complex.ofRealHom).roots.filter (fun z => ∃ r : ℝ, (r : ℂ) = z)).card = p.roots.card := by
  classical
  have h := filter_roots_map_range_eq_map_roots (f := Complex.ofRealHom) Complex.ofReal_injective p
  have e : (p.map Complex.ofRealHom).roots.filter (fun z => ∃ r : ℝ, (r : ℂ) = z) =
      (p.map Complex.ofRealHom).roots.filter (· ∈ Complex.ofRealHom.range) := by
    apply Multiset.filter_congr; intro z _; simp [RingHom.mem_range]
  rw [e, h, Multiset.card_map]

lemma neg_comp_aux (p : ℝ[X]) (a : ℝ) (k : ℕ) :
    (X - C a) ^ k ∣ p.comp (-X) ↔ (X - C (-a)) ^ k ∣ p := by
  have key : ∀ q : ℝ[X], (q.comp (-X)).comp (-X) = q := by
    intro q; rw [comp_assoc]; simp
  have hlin : (X - C (-a)).comp (-X) = -(X - C a) := by simp; ring
  constructor
  · intro h
    obtain ⟨r, hr⟩ := h
    refine ⟨(-1) ^ k * r.comp (-X), ?_⟩
    have := congrArg (fun q => q.comp (-X)) hr
    simp only [key] at this
    rw [this, mul_comp, pow_comp]
    have e2 : (X - C a).comp (-X) = -(X - C (-a)) := by simp; ring
    rw [e2, neg_pow]; ring
  · intro h
    obtain ⟨r, hr⟩ := h
    refine ⟨(-1) ^ k * r.comp (-X), ?_⟩
    rw [hr, mul_comp, pow_comp, hlin, neg_pow]; ring

lemma rootMultiplicity_comp_neg (p : ℝ[X]) (a : ℝ) :
    rootMultiplicity a (p.comp (-X)) = rootMultiplicity (-a) p := by
  by_cases hp : p = 0
  · simp [hp]
  have hp' : p.comp (-X) ≠ 0 := by
    intro h
    have := congrArg (fun q => q.comp (-X)) h
    simp only [zero_comp] at this
    rw [comp_assoc] at this; simp at this; exact hp this
  apply le_antisymm
  · rw [le_rootMultiplicity_iff hp, ← neg_comp_aux]
    exact pow_rootMultiplicity_dvd _ _
  · rw [le_rootMultiplicity_iff hp', neg_comp_aux]
    exact pow_rootMultiplicity_dvd _ _

lemma roots_comp_neg (p : ℝ[X]) : (p.comp (-X)).roots = p.roots.map (fun x => -x) := by
  classical
  ext a
  rw [count_roots, rootMultiplicity_comp_neg, ← count_roots]
  have h := Multiset.count_map_eq_count' (fun x : ℝ => -x) p.roots neg_injective (-a)
  simp only [neg_neg] at h
  exact h.symm

lemma countP_neg_roots (p : ℝ[X]) :
    p.roots.countP (· < 0) = (p.comp (-X)).roots.countP (0 < ·) := by
  rw [roots_comp_neg, Multiset.countP_map, Multiset.countP_eq_card_filter]
  simp only [neg_pos]

/-- the number of real roots splits into positive and negative ones when `p(0) ≠ 0`. -/
lemma card_roots_split (p : ℝ[X]) (h0 : p.eval 0 ≠ 0) :
    p.roots.card = p.roots.countP (0 < ·) + (p.comp (-X)).roots.countP (0 < ·) := by
  rw [← countP_neg_roots]
  have h1 := Multiset.card_eq_countP_add_countP (fun x : ℝ => 0 < x) p.roots
  have h2 : p.roots.countP (fun x => ¬ 0 < x) = p.roots.countP (· < 0) := by
    apply Multiset.countP_congr rfl
    intro x hx
    have hx0 : x ≠ 0 := by
      intro h; rw [h] at hx
      exact h0 (isRoot_of_mem_roots hx)
    simp only [not_lt]
    apply propext
    constructor
    · intro h; exact lt_of_le_of_ne h hx0
    · intro h; exact h.le
  rw [h1, h2]

end E521D

end S_D5

-- ===== D6 =====
section S_D6

/-! The positive-root bound (original). -/

open Polynomial Finset

namespace E521D

lemma T_ne_zero (e : ℕ → ℝ) (he : ∀ j, e j = 1 ∨ e j = -1) (n : ℕ) : T e (n + 1) ≠ 0 := by
  intro h
  have := congrArg (fun p => p.coeff 0) h
  simp only [T_coeff, coeff_zero] at this
  rw [if_pos (by omega)] at this
  rcases he 0 with h0 | h0 <;> rw [h0] at this <;> norm_num at this

lemma DN_ne_zero (N : ℕ) : DN N ≠ 0 := by
  intro h
  have := congrArg (fun p => p.coeff 0) h
  simp only [DN, finsetSum_coeff, coeff_X_pow, coeff_zero] at this
  rw [sum_eq_single 0] at this
  · simp at this
  · intro b _ hb; rw [if_neg (Ne.symm hb)]
  · intro h0; exact absurd (mem_range.mpr (by omega)) h0

lemma DN_pos_roots (N : ℕ) : (DN N * DN N).roots.countP (0 < ·) = 0 := by
  rw [Multiset.countP_eq_zero]
  intro x hx hx0
  have hr := isRoot_of_mem_roots hx
  rw [IsRoot, eval_mul, mul_self_eq_zero] at hr
  unfold DN at hr
  rw [eval_finsetSum] at hr
  have : 0 < ∑ i ∈ range (N + 1), eval x (X ^ i : ℝ[X]) := by
    apply sum_pos (fun i _ => by rw [eval_pow, eval_X]; exact pow_pos hx0 i) ⟨0, by simp⟩
  linarith

/-- **Positive roots** of `f = ∑_{j≤n} e_j X^j`: at most `#{k < p : Ip(c_k, c_{k+1})} + 1`, when
the forward partial sums are `≥ 1` on `[p, n]`, the backward two-fold sums are `≥ 0`, and `N ≥ n²+n+1`. -/
theorem pos_roots_le (e : ℕ → ℝ) (he : ∀ j, e j = 1 ∨ e j = -1) (n p N : ℕ) (hp : p ≤ n)
    (hN : n * n + n + 1 ≤ N) (hS : ∀ j, p ≤ j → j ≤ n → 1 ≤ S1 e j)
    (hB : ∀ k ≤ n, 0 ≤ b2 e n k) :
    (T e (n + 1)).roots.countP (0 < ·) ≤
      ((range p).filter (fun k => Ip (c2 e k) (c2 e (k + 1)))).card + 1 := by
  classical
  set Q := T e (n + 1) * (DN N * DN N) with hQ
  have hf0 := T_ne_zero e he n
  have hD0 : DN N * DN N ≠ 0 := mul_ne_zero (DN_ne_zero N) (DN_ne_zero N)
  have hQ0 : Q ≠ 0 := mul_ne_zero hf0 hD0
  have hnN : n ≤ N := by nlinarith
  -- roots of f are roots of Q
  have hroots : (T e (n + 1)).roots.countP (0 < ·) ≤ Q.roots.countP (0 < ·) := by
    rw [hQ, roots_mul hQ0, Multiset.countP_add]; omega
  refine hroots.trans ((roots_countP_pos_le_signVariations Q).trans ?_)
  set c := Q.coeff with hc
  set D := Q.natDegree with hD
  have hQT : Q = T c (D + 1) := by
    rw [hc]; unfold T; exact as_sum_range_C_mul_X_pow Q
  -- coefficient facts
  have hlow : ∀ k ≤ n, c k = c2 e k := fun k hk => Qc_low e hk hnN
  have hS1n : 1 ≤ S1 e n := hS n hp le_rfl
  have hdiff : ∀ k, c2 e (k + 1) - c2 e k = S1 e (k + 1) := by
    intro k; unfold c2 S1
    rw [sum_range_succ (fun j => e j * (((k + 1 : ℕ) : ℝ) - j + 1)), sum_range_succ (fun j => e j)]
    have : ∑ j ∈ range (k + 1), e j * (((k + 1 : ℕ) : ℝ) - j + 1) - ∑ j ∈ range (k + 1), e j * ((k : ℝ) - j + 1)
        = ∑ j ∈ range (k + 1), e j := by
      rw [← sum_sub_distrib]; apply sum_congr rfl; intro j _; push_cast; ring
    push_cast at this ⊢
    linarith
  have hinc : ∀ k, p ≤ k → k < N → c k < c (k + 1) := by
    intro k hk1 hk2
    by_cases hkn : k + 1 ≤ n
    · rw [hlow k (by omega), hlow (k + 1) hkn]
      have := hdiff k; have := hS (k + 1) (by omega) hkn; linarith
    · have hk : n ≤ k := by omega
      have h1 := Qc_mid_lin e (N := N) hk hk2.le
      have h2 := Qc_mid_lin e (n := n) (N := N) (k := k + 1) (by omega) hk2
      rw [← hQ] at h1 h2
      show Q.coeff k < Q.coeff (k + 1)
      rw [h1, h2]
      have : ∑ j ∈ range (n + 1), e j * (((k + 1 : ℕ) : ℝ) - j + 1) - ∑ j ∈ range (n + 1), e j * ((k : ℝ) - j + 1)
          = S1 e n := by
        unfold S1; rw [← sum_sub_distrib]; apply sum_congr rfl; intro j _; push_cast; ring
      linarith
  have hmidpos : ∀ k, N ≤ k → k ≤ N + n → 0 < c k := by
    intro k h1 h2
    have := Qc_mid_pos e he hN hS1n h1 h2
    rw [← hQ] at this; exact this
  have hDle : D ≤ 2 * N + n := by
    rw [hD, hQ]
    refine (natDegree_mul_le).trans ?_
    have h1 : (T e (n + 1)).natDegree ≤ n := by
      have := T_degree_lt e (n + 1)
      exact Nat.lt_succ_iff.mp ((natDegree_lt_iff_degree_lt hf0).mpr this)
    have h2 : (DN N * DN N).natDegree ≤ 2 * N := by
      refine (natDegree_mul_le).trans ?_
      have : (DN N).natDegree ≤ N := by
        unfold DN
        refine (natDegree_sum_le _ _).trans ?_
        rw [Finset.fold_max_le]
        refine ⟨by omega, fun i hi => ?_⟩
        rw [mem_range] at hi; simp only [Function.comp, natDegree_X_pow]; omega
      omega
    omega
  have hNle : N ≤ D := by
    rw [hD]; apply le_natDegree_of_ne_zero
    have := hmidpos N le_rfl (by omega)
    rw [hc] at this; exact this.ne'
  have htop : ∀ k, N < k → k ≤ D → 0 ≤ c k := by
    intro k h1 h2
    by_cases hk : k ≤ N + n
    · exact (hmidpos k h1.le hk).le
    · have h := Qc_top e (N := N) (k := k) (by omega) (by omega) hnN
      rw [← hQ] at h
      show 0 ≤ Q.coeff k
      rw [h]
      set k' := 2 * N + n - k with hk'
      by_cases hkn : k' ≤ n
      · have : ∑ i ∈ range (n + 1), (if i ≤ k' then e (n - i) * ((k' : ℝ) - i + 1) else 0) = b2 e n k' := by
          unfold b2
          rw [show n + 1 = (k' + 1) + (n - k') by omega, sum_range_add]
          have : ∑ x ∈ range (n - k'), (if k' + 1 + x ≤ k' then e (n - (k' + 1 + x)) *
              ((k' : ℝ) - ((k' + 1 + x : ℕ) : ℝ) + 1) else 0) = 0 := by
            apply sum_eq_zero; intro x _; rw [if_neg (by omega)]
          rw [this, add_zero]
          apply sum_congr rfl; intro i hi; rw [mem_range] at hi; rw [if_pos (by omega)]
        rw [this]; exact hB k' hkn
      · have : ∑ i ∈ range (n + 1), (if i ≤ k' then e (n - i) * ((k' : ℝ) - i + 1) else 0) =
            b2 e n n + ((k' : ℝ) - n) * S1 e n := by
          unfold b2 S1
          rw [← sum_range_reflect (fun j => e j) (n + 1), mul_sum, ← sum_add_distrib]
          apply sum_congr rfl; intro i hi; rw [mem_range] at hi
          rw [if_pos (by omega), show n + 1 - 1 - i = n - i by omega]; ring
        rw [this]
        have := hB n le_rfl
        have : (0 : ℝ) ≤ (k' : ℝ) - n := by
          have : (n : ℝ) ≤ k' := by exact_mod_cast (by omega : n ≤ k')
          linarith
        nlinarith
  -- assemble the sign-variation count
  rw [hQT]
  have s1 := sv_range c 0 p (Nat.zero_le p)
  simp only [zero_add] at s1
  rw [sv_one] at s1
  have s2 := sv_range c p N (by omega)
  have s3 := Ip_incr c p N hinc
  have hlead : 0 < (T c (N + 1)).leadingCoeff := by
    rw [T_lead_of c (hmidpos N le_rfl (by omega)).ne']; exact hmidpos N le_rfl (by omega)
  have s4 := (sv_nonneg c N hlead D hNle (fun k h1 h2 => htop k h1 h2)).1
  have hcount : ((Ico 0 p).filter (fun k => Ip (c k) (c (k + 1)))).card =
      ((range p).filter (fun k => Ip (c2 e k) (c2 e (k + 1)))).card := by
    rw [range_eq_Ico]
    congr 1
    apply filter_congr; intro k hk; rw [mem_Ico] at hk
    rw [hlow k (by omega), hlow (k + 1) (by omega)]
  rw [hcount] at s1
  omega

end E521D

end S_D6

-- ===== F0 =====
section S_F0

/-! The site statement's objects in our notation (original). -/

open Polynomial Finset MeasureTheory Filter Topology
open scoped ENNReal

namespace E521

/-- verbatim copies of the statement's definitions (namespace `OMA.S_erdos_521`). -/
noncomputable def signMeasure' : Measure (ℕ → Bool) :=
  Measure.infinitePi (fun _ : ℕ => (2 : ℝ≥0∞)⁻¹ • (Measure.dirac true + Measure.dirac false))

def eps' (k : ℕ) (ω : ℕ → Bool) : ℤ := if ω k then 1 else -1

noncomputable def randPoly' (n : ℕ) (ω : ℕ → Bool) : Polynomial ℂ :=
  ∑ k ∈ Finset.range (n + 1), Polynomial.C ((eps' k ω : ℂ)) * Polynomial.X ^ k

open scoped Classical in
noncomputable def realRootCount' (n : ℕ) (ω : ℕ → Bool) : ℕ :=
  ((randPoly' n ω).roots.filter (fun z => ∃ r : ℝ, (r : ℂ) = z)).card

lemma signMeasure'_eq : signMeasure' = μS := rfl

/-- the real polynomial. -/
noncomputable def fR (n : ℕ) (ω : ℕ → Bool) : ℝ[X] := E521D.T (eR ω) (n + 1)

lemma randPoly'_eq (n : ℕ) (ω : ℕ → Bool) : randPoly' n ω = (fR n ω).map Complex.ofRealHom := by
  unfold randPoly' fR E521D.T
  rw [Polynomial.map_sum]
  apply sum_congr rfl; intro k _
  rw [Polynomial.map_mul, Polynomial.map_pow, map_X, map_C]
  congr 2
  unfold eps' eR; split_ifs <;> simp

lemma realRootCount'_eq (n : ℕ) (ω : ℕ → Bool) : realRootCount' n ω = (fR n ω).roots.card := by
  classical
  unfold realRootCount'
  rw [randPoly'_eq]
  convert E521D.realRoots_card (fR n ω)

end E521

end S_F0


end
