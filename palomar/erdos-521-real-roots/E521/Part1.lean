/-
Copyright 2026 Ming-Chih Kao. Licensed under the Apache License, Version 2.0;
see the LICENSE file at the root of this repository.
-/
module

public import Mathlib

/-! Port of the merged Left to Solve file `proofs/erdos-521.lean`
(GuillaumeBAUD-coder/open-math-agents PR #12504, merged 28 Nov 2026; Lean v4.33.1, Mathlib 0df444a), sections
C1–P2 (Part1); the rest is in `E521/Part2.lean` … `E521/Part7.lean`, split at the file's section markers.

Changes for Lean v4.36.0 / Mathlib fc4f59e and the module system: the `module` header, public imports and a
public section in each part; the import of the Left to Solve statement and the final sections F2 (the bridge to
`OMA.S_erdos_521.main`) are dropped, and `erdos521_false` (Part7) is generalized to `erdos521_false_le` (any root
count bounded by the count with multiplicity); `E521/Main.lean` connects it to the formal-conjectures statement.
Proof repairs: `Finset.prod_le_one`/`prod_le_prod` → `prod_le_one₀`/`prod_le_prod₀` (nonnegative factors);
`*_finset_sum` → `*_finsetSum`; `simp only [Set.setOf_and]` (and the local definition) before
`apply MeasurableSet.inter` where `{z | p z ∧ q z}` no longer unifies with an intersection; a type ascription
in one `indicator_of_notMem`; `MemLp.indicator` now takes a `NullMeasurableSet`. The mathematics and the proofs
are otherwise unchanged. -/

@[expose] public section

-- ===== C1 =====
section S_C1

/-! Ballot counts in one and two dimensions (original). -/

open Finset

namespace E521

/-- Reflection-principle window: number of `±1` paths of length `h` started at height `u`
that stay `≥ 0`. -/
def Wn (h u : ℕ) : ℕ :=
  ∑ k ∈ range (h + 1), if h ≤ 2 * k + u ∧ 2 * k ≤ h + u + 1 then h.choose k else 0

lemma Wn_zero (u : ℕ) : Wn 0 u = 1 := by
  simp [Wn]

lemma Wn_succ (h u : ℕ) :
    Wn (h + 1) u = Wn h (u + 1) + (if u = 0 then 0 else Wn h (u - 1)) := by
  -- write both sides as sums over `range (h + 1)` against `h.choose j`
  have hL : Wn (h + 1) u = ∑ j ∈ range (h + 1),
      ((if h + 1 ≤ 2 * j + u ∧ 2 * j ≤ h + u + 2 then h.choose j else 0) +
       (if h ≤ 2 * j + u + 1 ∧ 2 * j ≤ h + u then h.choose j else 0)) := by
    unfold Wn
    rw [sum_range_succ', Finset.sum_add_distrib]
    have e1 : ∀ k ∈ range (h + 1),
        (if h + 1 ≤ 2 * (k + 1) + u ∧ 2 * (k + 1) ≤ h + 1 + u + 1 then (h + 1).choose (k + 1) else 0)
        = (if h + 1 ≤ 2 * (k + 1) + u ∧ 2 * (k + 1) ≤ h + u + 2 then h.choose (k + 1) else 0)
          + (if h ≤ 2 * k + u + 1 ∧ 2 * k ≤ h + u then h.choose k else 0) := by
      intro k _
      rw [Nat.choose_succ_succ']
      by_cases c1 : h + 1 ≤ 2 * (k + 1) + u ∧ 2 * (k + 1) ≤ h + 1 + u + 1
      · rw [if_pos c1, if_pos (by omega), if_pos (by omega)]; ring
      · rw [if_neg c1, if_neg (by omega), if_neg (by omega)]
    rw [sum_congr rfl e1, Finset.sum_add_distrib]
    -- the `choose (k+1)` part: reindex to `j = k + 1`, add the `j = 0` term
    have e2 : (∑ k ∈ range (h + 1),
        (if h + 1 ≤ 2 * (k + 1) + u ∧ 2 * (k + 1) ≤ h + u + 2 then h.choose (k + 1) else 0)) +
        (if h + 1 ≤ 2 * 0 + u ∧ 2 * 0 ≤ h + 1 + u + 1 then (h + 1).choose 0 else 0) =
        ∑ j ∈ range (h + 1),
          (if h + 1 ≤ 2 * j + u ∧ 2 * j ≤ h + u + 2 then h.choose j else 0) := by
      have := sum_range_succ' (fun j =>
        (if h + 1 ≤ 2 * j + u ∧ 2 * j ≤ h + u + 2 then h.choose j else 0)) (h + 1)
      rw [sum_range_succ] at this
      have hz : (if h + 1 ≤ 2 * (h + 1) + u ∧ 2 * (h + 1) ≤ h + u + 2 then h.choose (h + 1) else 0)
          = 0 := by
        split_ifs <;> simp
      rw [hz, add_zero] at this
      rw [this]
      congr 1
      simp only [Nat.choose_zero_right]
      by_cases c : h + 1 ≤ u
      · rw [if_pos (by omega), if_pos (by omega)]
      · rw [if_neg (by omega), if_neg (by omega)]
    rw [← Finset.sum_add_distrib] at *
    rw [← e2, Finset.sum_add_distrib]
    ring
  rw [hL]
  have hR : Wn h (u + 1) + (if u = 0 then 0 else Wn h (u - 1)) = ∑ j ∈ range (h + 1),
      ((if h ≤ 2 * j + (u + 1) ∧ 2 * j ≤ h + (u + 1) + 1 then h.choose j else 0) +
       (if u = 0 then 0 else if h ≤ 2 * j + (u - 1) ∧ 2 * j ≤ h + (u - 1) + 1 then h.choose j else 0))
      := by
    rw [Finset.sum_add_distrib]
    unfold Wn
    congr 1
    by_cases hu : u = 0
    · simp [hu]
    · simp [hu]
  rw [hR]
  apply sum_congr rfl
  intro j _
  by_cases hu : u = 0
  · subst hu
    simp only [if_true]
    split_ifs <;> omega
  · rw [if_neg hu]
    split_ifs <;> omega

lemma Wn_zero_start (h : ℕ) : Wn h 0 = h.choose ((h + 1) / 2) := by
  unfold Wn
  rw [sum_eq_single ((h + 1) / 2)]
  · rw [if_pos (by omega)]
  · intro k _ hk
    rw [if_neg (by omega)]
  · intro hk
    exfalso; apply hk; rw [mem_range]; omega

/-! ### one-dimensional paths -/

/-- `±1` step of a coin. -/
def st (b : Bool) : ℤ := if b then 1 else -1

/-- a path of `L` steps started at `u` stays `≥ 0` (including the start). -/
def good1 : (L : ℕ) → ℤ → (Fin L → Bool) → Prop
  | 0, u, _ => 0 ≤ u
  | L + 1, u, p => 0 ≤ u ∧ good1 L (u + st (p 0)) (Fin.tail p)

instance good1_dec : ∀ (L : ℕ) (u : ℤ) (p : Fin L → Bool), Decidable (good1 L u p)
  | 0, u, _ => by unfold good1; infer_instance
  | L + 1, u, p => by
    unfold good1
    haveI := good1_dec L (u + st (p 0)) (Fin.tail p)
    infer_instance

def N1 (L : ℕ) (u : ℤ) : ℕ := (univ.filter (fun p : Fin L → Bool => good1 L u p)).card

lemma N1_neg (L : ℕ) {u : ℤ} (hu : u < 0) : N1 L u = 0 := by
  unfold N1
  rw [card_eq_zero, filter_eq_empty_iff]
  intro p _
  cases L with
  | zero => simp only [good1]; omega
  | succ L => simp only [good1]; omega

/-- sum over sequences by the first coordinate. -/
lemma sum_cons {α : Type*} [Fintype α] {L : ℕ} (f : (Fin (L + 1) → α) → ℕ) :
    ∑ p, f p = ∑ a : α, ∑ q : Fin L → α, f (Fin.cons a q) := by
  rw [← Fintype.sum_prod_type']
  exact (Fintype.sum_equiv (Fin.consEquiv (fun _ => α)) _ _ (fun _ => rfl)).symm

lemma card_filter_eq_sum {β : Type*} [Fintype β] (P : β → Prop) [DecidablePred P] :
    (univ.filter P).card = ∑ x, if P x then 1 else 0 := by
  rw [card_filter]

lemma N1_succ (L : ℕ) {u : ℤ} (hu : 0 ≤ u) : N1 (L + 1) u = N1 L (u + 1) + N1 L (u - 1) := by
  unfold N1
  rw [card_filter_eq_sum, card_filter_eq_sum, card_filter_eq_sum, sum_cons]
  simp only [Fintype.univ_bool, mem_insert, mem_singleton, Bool.true_eq_false, not_false_eq_true,
    sum_insert, sum_singleton]
  congr 1
  · apply Fintype.sum_congr; intro q
    simp only [good1, Fin.cons_zero, Fin.tail_cons, st, if_true]
    by_cases h : good1 L (u + 1) q
    · rw [if_pos ⟨hu, h⟩, if_pos h]
    · rw [if_neg (fun h' => h h'.2), if_neg h]
  · apply Fintype.sum_congr; intro q
    simp only [good1, Fin.cons_zero, Fin.tail_cons, st]
    have e : u + (if false = true then (1 : ℤ) else -1) = u - 1 := by simp; ring
    rw [e]
    by_cases h : good1 L (u - 1) q
    · rw [if_pos ⟨hu, h⟩, if_pos h]
    · rw [if_neg (fun h' => h h'.2), if_neg h]

lemma N1_eq_Wn (L : ℕ) : ∀ u : ℕ, N1 L u = Wn L u := by
  induction L with
  | zero =>
    intro u
    unfold N1
    rw [Wn_zero, card_eq_one]
    refine ⟨default, ?_⟩
    ext p
    have hp : p = default := Subsingleton.elim _ _
    simp only [mem_filter, mem_univ, true_and, mem_singleton, good1]
    refine ⟨fun _ => hp, fun _ => ?_⟩
    exact Finset.mem_filter.mpr ⟨mem_univ _, show (0:ℤ) ≤ (u:ℤ) by positivity⟩
  | succ L ih =>
    intro u
    rw [N1_succ L (by positivity), Wn_succ]
    have h1 : ((u : ℤ) + 1) = ((u + 1 : ℕ) : ℤ) := by push_cast; ring
    rw [h1, ih]
    congr 1
    by_cases hu : u = 0
    · subst hu; rw [if_pos rfl]; exact N1_neg L (by norm_num)
    · rw [if_neg hu]
      have h2 : ((u : ℤ) - 1) = ((u - 1 : ℕ) : ℤ) := by omega
      rw [h2, ih]

/-! ### two-dimensional axis walk -/

/-- a pair of coins `(a, b)`: if `a = b` the walk moves horizontally by `st a`,
otherwise vertically by `st a`. -/
def dU (s : Bool × Bool) : ℤ := if s.1 = s.2 then st s.1 else 0
def dV (s : Bool × Bool) : ℤ := if s.1 = s.2 then 0 else st s.1

def good2 : (L : ℕ) → ℤ → ℤ → (Fin L → Bool × Bool) → Prop
  | 0, u, v, _ => 0 ≤ u ∧ 0 ≤ v
  | L + 1, u, v, p => 0 ≤ u ∧ 0 ≤ v ∧ good2 L (u + dU (p 0)) (v + dV (p 0)) (Fin.tail p)

instance good2_dec : ∀ (L : ℕ) (u v : ℤ) (p : Fin L → Bool × Bool), Decidable (good2 L u v p)
  | 0, u, v, _ => by unfold good2; infer_instance
  | L + 1, u, v, p => by
    unfold good2
    haveI := good2_dec L (u + dU (p 0)) (v + dV (p 0)) (Fin.tail p)
    infer_instance

def N2 (L : ℕ) (u v : ℤ) : ℕ := (univ.filter (fun p : Fin L → Bool × Bool => good2 L u v p)).card

lemma N2_succ (L : ℕ) {u v : ℤ} (hu : 0 ≤ u) (hv : 0 ≤ v) :
    N2 (L + 1) u v = N2 L (u + 1) v + N2 L (u - 1) v + N2 L u (v + 1) + N2 L u (v - 1) := by
  unfold N2
  simp only [card_filter_eq_sum]
  rw [sum_cons]
  rw [Fintype.sum_prod_type]
  simp only [Fintype.univ_bool, mem_insert, mem_singleton, Bool.true_eq_false, not_false_eq_true,
    sum_insert, sum_singleton]
  have key : ∀ (a b : Bool) (q : Fin L → Bool × Bool),
      (if good2 (L + 1) u v (Fin.cons (a, b) q) then 1 else 0) =
      (if good2 L (u + dU (a, b)) (v + dV (a, b)) q then 1 else 0) := by
    intro a b q
    simp only [good2, Fin.cons_zero, Fin.tail_cons]
    by_cases h : good2 L (u + dU (a, b)) (v + dV (a, b)) q
    · rw [if_pos ⟨hu, hv, h⟩, if_pos h]
    · rw [if_neg (fun h' => h h'.2.2), if_neg h]
  simp only [key, dU, dV, st]
  simp only [if_true, Bool.true_eq_false, if_false, Bool.false_eq_true, add_zero]
  have e : u + -1 = u - 1 := by ring
  have e' : v + -1 = v - 1 := by ring
  rw [e, e']
  ring

lemma N2_neg {L : ℕ} {u v : ℤ} (h : u < 0 ∨ v < 0) : N2 L u v = 0 := by
  unfold N2
  rw [card_eq_zero, filter_eq_empty_iff]
  intro p _
  cases L with
  | zero => simp only [good2]; omega
  | succ L => simp only [good2]; omega

/-- product formula: the axis walk is a binomial interleaving of two independent 1D walks. -/
theorem N2_eq (L : ℕ) : ∀ u v : ℤ,
    N2 L u v = ∑ h ∈ range (L + 1), L.choose h * (N1 h u * N1 (L - h) v) := by
  induction L with
  | zero =>
    intro u v
    simp only [zero_add, range_one, sum_singleton, Nat.choose_self, Nat.sub_self, one_mul]
    unfold N2 N1
    by_cases hu : 0 ≤ u
    · by_cases hv : 0 ≤ v
      · have e1 : (univ.filter (fun p : Fin 0 → Bool × Bool => good2 0 u v p)) = univ := by
          ext p; simp [good2, hu, hv]
        have e2 : (univ.filter (fun p : Fin 0 → Bool => good1 0 u p)) = univ := by
          ext p; simp [good1, hu]
        have e3 : (univ.filter (fun p : Fin 0 → Bool => good1 0 v p)) = univ := by
          ext p; simp [good1, hv]
        rw [e1, e2, e3]; simp
      · have := N2_neg (L := 0) (u := u) (v := v) (Or.inr (by omega))
        unfold N2 at this; rw [this]
        have := N1_neg 0 (u := v) (by omega)
        unfold N1 at this; rw [this]; simp
    · have := N2_neg (L := 0) (u := u) (v := v) (Or.inl (by omega))
      unfold N2 at this; rw [this]
      have := N1_neg 0 (u := u) (by omega)
      unfold N1 at this; rw [this]; simp
  | succ L ih =>
    intro u v
    by_cases huv : 0 ≤ u ∧ 0 ≤ v
    · rw [N2_succ L huv.1 huv.2, ih, ih, ih, ih]
      -- 1D recursions
      have r1 : ∀ h, N1 h (u + 1) + N1 h (u - 1) = N1 (h + 1) u := fun h =>
        (N1_succ h huv.1).symm
      have r2 : ∀ h, N1 h (v + 1) + N1 h (v - 1) = N1 (h + 1) v := fun h =>
        (N1_succ h huv.2).symm
      have A : (∑ h ∈ range (L + 1), L.choose h * (N1 h (u + 1) * N1 (L - h) v)) +
          (∑ h ∈ range (L + 1), L.choose h * (N1 h (u - 1) * N1 (L - h) v)) =
          ∑ h ∈ range (L + 1), L.choose h * (N1 (h + 1) u * N1 (L - h) v) := by
        rw [← sum_add_distrib]; apply sum_congr rfl; intro h _; rw [← r1]; ring
      have B : (∑ h ∈ range (L + 1), L.choose h * (N1 h u * N1 (L - h) (v + 1))) +
          (∑ h ∈ range (L + 1), L.choose h * (N1 h u * N1 (L - h) (v - 1))) =
          ∑ h ∈ range (L + 1), L.choose h * (N1 h u * N1 (L - h + 1) v) := by
        rw [← sum_add_distrib]; apply sum_congr rfl; intro h _; rw [← r2]; ring
      rw [A, add_assoc, B]
      -- Pascal on the right
      rw [sum_range_succ' _ (L + 1)]
      simp only [Nat.choose_succ_succ', add_mul, sum_add_distrib]
      rw [sum_range_succ (fun h => L.choose (h + 1) * (N1 (h + 1) u * N1 (L + 1 - (h + 1)) v)) L]
      simp only [Nat.choose_succ_self, zero_mul, add_zero, Nat.choose_zero_right, one_mul,
        Nat.sub_zero]
      have C1 : ∑ h ∈ range (L + 1), L.choose h * (N1 (h + 1) u * N1 (L + 1 - (h + 1)) v) =
          ∑ h ∈ range (L + 1), L.choose h * (N1 (h + 1) u * N1 (L - h) v) := by
        apply sum_congr rfl; intro h _; congr 3; omega
      have C2 : ∑ h ∈ range L, L.choose (h + 1) * (N1 (h + 1) u * N1 (L + 1 - (h + 1)) v) +
          N1 0 u * N1 (L + 1) v =
          ∑ h ∈ range (L + 1), L.choose h * (N1 h u * N1 (L - h + 1) v) := by
        rw [sum_range_succ' (fun h => L.choose h * (N1 h u * N1 (L - h + 1) v))]
        simp only [Nat.choose_zero_right, one_mul, Nat.sub_zero]
        congr 1
        apply sum_congr rfl; intro h hh; rw [mem_range] at hh; congr 3; omega
      rw [C1, ← C2]; ring
    · rw [N2_neg (by omega)]
      symm
      apply sum_eq_zero
      intro h _
      rcases not_and_or.mp huv with hu | hv
      · rw [N1_neg h (by omega)]; ring
      · rw [N1_neg (L + 1 - h) (by omega)]; ring

/-- total number of axis walks of length `L` from the origin staying in the closed quadrant. -/
theorem N2_origin (L : ℕ) : N2 L 0 0 =
    ∑ h ∈ range (L + 1), L.choose h * (h.choose ((h + 1) / 2) * (L - h).choose ((L - h + 1) / 2)) := by
  rw [N2_eq]
  apply sum_congr rfl
  intro h _
  have e1 := N1_eq_Wn h 0
  have e2 := N1_eq_Wn (L - h) 0
  simp only [Nat.cast_zero] at e1 e2
  rw [e1, e2, Wn_zero_start, Wn_zero_start]

end E521

end S_C1

-- ===== C2 =====
section S_C2

/-! Two-sided bounds for the quadrant count `N2 L 0 0` (original). -/

open Finset

namespace E521

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

/-- lower bound `16^p ≤ 4 p c_p^2` for `p ≥ 1`. -/
lemma cb_sq_low (p : ℕ) (hp : 1 ≤ p) : (16 : ℝ) ^ p ≤ 4 * p * (Nat.centralBinom p : ℝ) ^ 2 := by
  induction p, hp using Nat.le_induction with
  | base => rw [show Nat.centralBinom 1 = 2 by rfl]; norm_num
  | succ p hp ih =>
    have h := Nat.succ_mul_centralBinom_succ p
    have hc : (Nat.centralBinom (p + 1) : ℝ) = 2 * (2 * p + 1) * Nat.centralBinom p / (p + 1) := by
      rw [eq_div_iff (by positivity)]
      have : ((p + 1 : ℕ) : ℝ) * Nat.centralBinom (p + 1) = 2 * (2 * p + 1) * Nat.centralBinom p := by
        exact_mod_cast h
      push_cast at this; linarith
    rw [hc]
    have hp1 : (0 : ℝ) < (p : ℝ) + 1 := by positivity
    have e : 4 * ((p + 1 : ℕ) : ℝ) * (2 * (2 * p + 1) * Nat.centralBinom p / (p + 1)) ^ 2
        = 16 * (2 * (p : ℝ) + 1) ^ 2 / (p + 1) * (Nat.centralBinom p : ℝ) ^ 2 := by
      push_cast; field_simp; ring
    rw [e, pow_succ]
    have key : 4 * (p : ℝ) ≤ (2 * (p : ℝ) + 1) ^ 2 / (p + 1) * (p : ℝ)⁻¹ * (p:ℝ) * (p + 1) / (p + 1) := by
      have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
      rw [mul_assoc ((2 * (p : ℝ) + 1) ^ 2 / (p + 1)), inv_mul_cancel₀ hp0.ne', mul_one,
        mul_div_assoc, div_self hp1.ne', mul_one, le_div_iff₀ hp1]
      nlinarith
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
    have hc0 : (0 : ℝ) ≤ (Nat.centralBinom p : ℝ) ^ 2 := by positivity
    have : (2 * (p : ℝ) + 1) ^ 2 / (p + 1) ≥ 4 * p := by
      rw [ge_iff_le, le_div_iff₀ hp1]; nlinarith
    calc (16 : ℝ) ^ p * 16 ≤ (4 * p * (Nat.centralBinom p : ℝ) ^ 2) * 16 := by linarith
      _ ≤ 16 * (2 * (p : ℝ) + 1) ^ 2 / (p + 1) * (Nat.centralBinom p : ℝ) ^ 2 := by
        rw [mul_div_assoc]; nlinarith

/-- `C(h, ⌈h/2⌉)` -/
def cc (h : ℕ) : ℕ := h.choose ((h + 1) / 2)

lemma cc_odd (p : ℕ) : (cc (2 * p + 1) : ℝ) = Nat.centralBinom (p + 1) / 2 := by
  unfold cc
  have h2 : (2 * p + 1 + 1) / 2 = p + 1 := by omega
  rw [h2]
  have hsum : Nat.centralBinom (p + 1) = 2 * (2 * p + 1).choose (p + 1) := by
    rw [Nat.centralBinom_eq_two_mul_choose, show 2 * (p + 1) = (2 * p + 1) + 1 by ring,
      Nat.choose_succ_succ, Nat.choose_symm_of_eq_add (show 2 * p + 1 = (p + 1) + p by omega)]
    ring
  rw [hsum]; push_cast; ring

lemma cc_even (p : ℕ) : (cc (2 * p) : ℝ) = Nat.centralBinom p := by
  unfold cc
  have h2 : (2 * p + 1) / 2 = p := by omega
  rw [h2, Nat.centralBinom_eq_two_mul_choose]

lemma cc_upper (h : ℕ) : (cc h : ℝ) ^ 2 * (h + 1) ≤ 4 ^ h := by
  obtain ⟨p, rfl | rfl⟩ := Nat.even_or_odd' h
  · rw [cc_even]
    have := cb_sq p
    have h16 : (4 : ℝ) ^ (2 * p) = 16 ^ p := by rw [pow_mul]; norm_num
    rw [h16]; push_cast; linarith
  · rw [cc_odd]
    have := cb_sq (p + 1)
    have h16 : (4 : ℝ) ^ (2 * p + 1) = 16 ^ (p + 1) / 4 := by
      rw [pow_succ, pow_mul, pow_succ]; ring
    rw [h16]; push_cast at this ⊢
    have : (0 : ℝ) ≤ (Nat.centralBinom (p + 1) : ℝ) ^ 2 := by positivity
    nlinarith

lemma cc_lower (h : ℕ) : (4 : ℝ) ^ h ≤ 2 * (h + 1) * (cc h : ℝ) ^ 2 := by
  obtain ⟨p, rfl | rfl⟩ := Nat.even_or_odd' h
  · rw [cc_even]
    rcases Nat.eq_zero_or_pos p with hp | hp
    · subst hp; simp
    · have := cb_sq_low p hp
      have h16 : (4 : ℝ) ^ (2 * p) = 16 ^ p := by rw [pow_mul]; norm_num
      rw [h16]; push_cast
      have : (0 : ℝ) ≤ (Nat.centralBinom p : ℝ) ^ 2 := by positivity
      nlinarith
  · rw [cc_odd]
    have := cb_sq_low (p + 1) (by omega)
    have h16 : (4 : ℝ) ^ (2 * p + 1) = 16 ^ (p + 1) / 4 := by
      rw [pow_succ, pow_mul, pow_succ]; ring
    rw [h16]; push_cast at this ⊢
    nlinarith

lemma N2_origin' (L : ℕ) : (N2 L 0 0 : ℝ) =
    ∑ h ∈ range (L + 1), (L.choose h : ℝ) * ((cc h : ℝ) * (cc (L - h) : ℝ)) := by
  rw [N2_origin]; push_cast; rfl

theorem N2_lower (L : ℕ) : (4 : ℝ) ^ L / (L + 2) ≤ N2 L 0 0 := by
  rw [N2_origin']
  have hL : (0 : ℝ) < L + 2 := by positivity
  have each : ∀ h ∈ range (L + 1), (L.choose h : ℝ) * (2 ^ L / (L + 2)) ≤
      (L.choose h : ℝ) * ((cc h : ℝ) * (cc (L - h) : ℝ)) := by
    intro h hh
    rw [mem_range] at hh
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have a := cc_lower h
    have b := cc_lower (L - h)
    have hLh : ((L - h : ℕ) : ℝ) = L - h := by rw [Nat.cast_sub (by omega)]
    rw [hLh] at b
    set x := (cc h : ℝ)
    set y := (cc (L - h) : ℝ)
    have hx : 0 ≤ x := by positivity
    have hy : 0 ≤ y := by positivity
    -- (x y)^2 ≥ 4^L / (4 (h+1)(L-h+1)) ≥ 4^L/(L+2)^2
    have h4 : (4 : ℝ) ^ L = 4 ^ h * 4 ^ (L - h) := by rw [← pow_add]; congr 1; omega
    have hh0 : (0 : ℝ) ≤ h := by positivity
    have hh1 : (h : ℝ) ≤ L := by exact_mod_cast (by omega : h ≤ L)
    have prod : (4 : ℝ) ^ L ≤ (L + 2) ^ 2 * (x * y) ^ 2 := by
      have amgm : 4 * ((h : ℝ) + 1) * (L - h + 1) ≤ (L + 2) ^ 2 := by
        nlinarith [sq_nonneg (((h : ℝ) + 1) - (L - h + 1))]
      have := mul_le_mul a b (by positivity) (by positivity)
      rw [h4]
      calc (4 : ℝ) ^ h * 4 ^ (L - h) ≤ 2 * (h + 1) * x ^ 2 * (2 * ((L : ℝ) - h + 1) * y ^ 2) := this
        _ = (4 * ((h : ℝ) + 1) * (L - h + 1)) * (x * y) ^ 2 := by ring
        _ ≤ (L + 2) ^ 2 * (x * y) ^ 2 := by
          apply mul_le_mul_of_nonneg_right amgm (by positivity)
    have h2 : ((2 : ℝ) ^ L) ^ 2 = 4 ^ L := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
    rw [div_le_iff₀ hL]
    have hxy : 0 ≤ x * y * (L + 2) := by positivity
    have : ((2 : ℝ) ^ L) ^ 2 ≤ (x * y * (L + 2)) ^ 2 := by rw [h2]; nlinarith
    have := (pow_le_pow_iff_left₀ (by positivity) hxy two_ne_zero).mp this
    linarith
  have := sum_le_sum each
  rw [← sum_mul] at this
  have hs : ∑ h ∈ range (L + 1), (L.choose h : ℝ) = 2 ^ L := by
    exact_mod_cast Nat.sum_range_choose L
  rw [hs] at this
  calc (4 : ℝ) ^ L / (L + 2) = 2 ^ L * (2 ^ L / (L + 2)) := by
        rw [show (4 : ℝ) ^ L = 2 ^ L * 2 ^ L by rw [← mul_pow]; norm_num]; ring
    _ ≤ _ := this

/-- `∑ C(L,h)/(h+1) ≤ 2^(L+1)/(L+1)`. -/
lemma sum_choose_div (L : ℕ) :
    ∑ h ∈ range (L + 1), (L.choose h : ℝ) / (h + 1) ≤ 2 ^ (L + 1) / (L + 1) := by
  have e : ∀ h ∈ range (L + 1), (L.choose h : ℝ) / (h + 1) = ((L + 1).choose (h + 1) : ℝ) / (L + 1) := by
    intro h _
    have := Nat.add_one_mul_choose_eq L h
    rw [div_eq_div_iff (by positivity) (by positivity)]
    have : ((L + 1 : ℕ) : ℝ) * (L.choose h : ℝ) = ((L + 1).choose (h + 1) : ℝ) * ((h + 1 : ℕ) : ℝ) := by
      exact_mod_cast this
    push_cast at this; linarith
  rw [sum_congr rfl e, ← sum_div]
  apply div_le_div_of_nonneg_right _ (by positivity)
  have : ∑ h ∈ range (L + 1), ((L + 1).choose (h + 1) : ℝ) ≤ ∑ h ∈ range (L + 2), ((L + 1).choose h : ℝ) := by
    rw [sum_range_succ' (fun h => ((L + 1).choose h : ℝ))]
    simp
  calc _ ≤ _ := this
    _ = 2 ^ (L + 1) := by exact_mod_cast Nat.sum_range_choose (L + 1)

theorem N2_upper (L : ℕ) : (N2 L 0 0 : ℝ) ≤ 2 * 4 ^ L / (L + 1) := by
  rw [N2_origin']
  have each : ∀ h ∈ range (L + 1), (L.choose h : ℝ) * ((cc h : ℝ) * (cc (L - h) : ℝ)) ≤
      2 ^ L * ((L.choose h : ℝ) / (h + 1) + ((L.choose (L - h)) : ℝ) / ((L - h : ℕ) + 1)) / 2 := by
    intro h hh
    rw [mem_range] at hh
    have a := cc_upper h
    have b := cc_upper (L - h)
    set x := (cc h : ℝ)
    set y := (cc (L - h) : ℝ)
    set A := (h : ℝ) + 1
    set B := ((L - h : ℕ) : ℝ) + 1
    have hA : 0 < A := by positivity
    have hB : 0 < B := by positivity
    have hsym : (L.choose (L - h) : ℝ) = L.choose h := by rw [Nat.choose_symm (by omega)]
    rw [hsym]
    have h4 : (4 : ℝ) ^ L = 4 ^ h * 4 ^ (L - h) := by rw [← pow_add]; congr 1; omega
    have h2 : ((2 : ℝ) ^ L) ^ 2 = 4 ^ L := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
    -- (x y)^2 A B ≤ 4^L, hence x y ≤ 2^L / sqrt(A B) ≤ 2^L (1/A + 1/B)/2
    have hxy2 : (x * y) ^ 2 * (A * B) ≤ ((2 : ℝ) ^ L) ^ 2 := by
      rw [h2, h4]
      have := mul_le_mul a b (by positivity) (by positivity)
      calc (x * y) ^ 2 * (A * B) = x ^ 2 * A * (y ^ 2 * B) := by ring
        _ ≤ _ := this
    have hx : 0 ≤ x := by positivity
    have hy : 0 ≤ y := by positivity
    have hc : (0 : ℝ) ≤ L.choose h := by positivity
    have key : x * y ≤ 2 ^ L * (1 / A + 1 / B) / 2 := by
      -- 2 xy ≤ 2^L (A+B)/(AB) since 2 sqrt(AB) ≤ A + B
      have hAB : 0 < A * B := by positivity
      have s1 : (x * y * (A * B)) ^ 2 ≤ ((2 : ℝ) ^ L) ^ 2 * (A * B) := by nlinarith
      have s2 : (2 * x * y * (A * B)) ^ 2 ≤ ((2 : ℝ) ^ L * (A + B)) ^ 2 := by
        have : 4 * (A * B) ≤ (A + B) ^ 2 := by nlinarith [sq_nonneg (A - B)]
        nlinarith
      have s3 : 2 * x * y * (A * B) ≤ (2 : ℝ) ^ L * (A + B) := by
        exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).mp s2
      rw [show (2 : ℝ) ^ L * (1 / A + 1 / B) / 2 = (2 : ℝ) ^ L * (A + B) / (2 * (A * B)) by
        field_simp; ring]
      rw [le_div_iff₀ (by positivity)]; linarith
    calc (L.choose h : ℝ) * (x * y) ≤ (L.choose h : ℝ) * (2 ^ L * (1 / A + 1 / B) / 2) :=
          mul_le_mul_of_nonneg_left key hc
      _ = _ := by ring
  have := sum_le_sum each
  rw [← sum_div, ← mul_sum, sum_add_distrib] at this
  have s1 := sum_choose_div L
  have s2 : ∑ h ∈ range (L + 1), ((L.choose (L - h)) : ℝ) / ((L - h : ℕ) + 1) =
      ∑ h ∈ range (L + 1), (L.choose h : ℝ) / (h + 1) := by
    exact sum_range_reflect (fun h => (L.choose h : ℝ) / (h + 1)) (L + 1)
  rw [s2] at this
  calc _ ≤ _ := this
    _ ≤ 2 ^ L * (2 ^ (L + 1) / (L + 1) + 2 ^ (L + 1) / (L + 1)) / 2 := by
        gcongr
    _ = 2 * 4 ^ L / (L + 1) := by
        rw [show (4 : ℝ) ^ L = 2 ^ L * 2 ^ L by rw [← mul_pow]; norm_num, pow_succ]; ring

end E521

end S_C2

-- ===== C3 =====
section S_C3

/-! Cylinder probabilities for the sign measure, read through backward pairs (original). -/

open Finset MeasureTheory
open scoped ENNReal

namespace E521

noncomputable def ν : Measure Bool := (2 : ℝ≥0∞)⁻¹ • (Measure.dirac true + Measure.dirac false)

instance : IsProbabilityMeasure ν := by
  constructor
  simp [ν]
  rw [ENNReal.inv_two_add_inv_two]

lemma ν_singleton (b : Bool) : ν {b} = 2⁻¹ := by
  cases b <;> simp [ν]

noncomputable def μS : Measure (ℕ → Bool) := Measure.infinitePi (fun _ : ℕ => ν)

instance : IsProbabilityMeasure μS := by unfold μS; infer_instance

/-- the backward pairs of the first `2K` coordinates: pair `j` is `(ω (2K-1-2j), ω (2K-2-2j))`. -/
def Φ (K : ℕ) (ω : ℕ → Bool) : Fin K → Bool × Bool :=
  fun j => (ω (2 * K - 1 - 2 * j), ω (2 * K - 2 - 2 * j))

/-- the coordinate value forced by a pair pattern. -/
def bit (K : ℕ) (p : Fin K → Bool × Bool) (i : ℕ) : Bool :=
  if h : (2 * K - 1 - i) / 2 < K then
    (if (2 * K - 1 - i) % 2 = 0 then (p ⟨(2 * K - 1 - i) / 2, h⟩).1
      else (p ⟨(2 * K - 1 - i) / 2, h⟩).2)
  else false

lemma Φ_preimage_singleton (K : ℕ) (p : Fin K → Bool × Bool) :
    Φ K ⁻¹' {p} = Set.pi (↑(range (2 * K))) (fun i => {bit K p i}) := by
  ext ω
  simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_pi, coe_range, Set.mem_Iio]
  constructor
  · intro h i hi
    subst h
    unfold bit
    have hlt : (2 * K - 1 - i) / 2 < K := by omega
    rw [dif_pos hlt]
    split_ifs with hpar
    · simp only [Φ]; congr 1; omega
    · simp only [Φ]; congr 1; omega
  · intro h
    funext j
    have hj := j.isLt
    have h1 := h (2 * K - 1 - 2 * j) (by omega)
    have h2 := h (2 * K - 2 - 2 * j) (by omega)
    unfold bit at h1 h2
    have e1 : (2 * K - 1 - (2 * K - 1 - 2 * (j : ℕ))) / 2 = j := by omega
    have e2 : (2 * K - 1 - (2 * K - 2 - 2 * (j : ℕ))) / 2 = j := by omega
    rw [dif_pos (by omega)] at h1 h2
    have p1 : (2 * K - 1 - (2 * K - 1 - 2 * (j : ℕ))) % 2 = 0 := by omega
    have p2 : ¬ (2 * K - 1 - (2 * K - 2 - 2 * (j : ℕ))) % 2 = 0 := by omega
    rw [if_pos p1] at h1
    rw [if_neg p2] at h2
    have f1 : (⟨(2 * K - 1 - (2 * K - 1 - 2 * (j : ℕ))) / 2, by omega⟩ : Fin K) = j := Fin.ext e1
    have f2 : (⟨(2 * K - 1 - (2 * K - 2 - 2 * (j : ℕ))) / 2, by omega⟩ : Fin K) = j := Fin.ext e2
    rw [f1] at h1; rw [f2] at h2
    simp only [Φ]
    rw [h1, h2]

lemma measurableSet_Φ_singleton (K : ℕ) (p : Fin K → Bool × Bool) :
    MeasurableSet (Φ K ⁻¹' {p}) := by
  rw [Φ_preimage_singleton]
  exact MeasurableSet.pi (Finset.countable_toSet _) (fun i _ => measurableSet_singleton _)

lemma μS_Φ_singleton (K : ℕ) (p : Fin K → Bool × Bool) :
    μS (Φ K ⁻¹' {p}) = (4⁻¹ : ℝ≥0∞) ^ K := by
  rw [Φ_preimage_singleton, μS]
  have h := Measure.infinitePi_pi (μ := fun _ : ℕ => ν) (s := range (2 * K))
    (t := fun i => ({bit K p i} : Set Bool)) (fun i _ => measurableSet_singleton _)
  refine h.trans ?_
  simp only [ν_singleton, prod_const, card_range]
  rw [pow_mul]
  congr 1
  rw [← ENNReal.inv_pow]; norm_num

lemma μS_Φ (K : ℕ) (S : Finset (Fin K → Bool × Bool)) :
    μS (Φ K ⁻¹' (S : Set (Fin K → Bool × Bool))) = S.card * (4⁻¹ : ℝ≥0∞) ^ K := by
  have : Φ K ⁻¹' (S : Set (Fin K → Bool × Bool)) = ⋃ p ∈ S, Φ K ⁻¹' {p} := by
    ext ω; simp
  rw [this, measure_biUnion_finset]
  · simp only [μS_Φ_singleton, sum_const, nsmul_eq_mul]
  · intro p _ q _ hpq
    simp only [Function.onFun]
    rw [Set.disjoint_iff]
    intro ω ⟨h1, h2⟩
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at h1 h2
    exact hpq (h1.symm.trans h2)
  · intro p _; exact measurableSet_Φ_singleton K p

lemma μS_Φ_real (K : ℕ) (S : Finset (Fin K → Bool × Bool)) :
    μS.real (Φ K ⁻¹' (S : Set (Fin K → Bool × Bool))) = S.card / 4 ^ K := by
  rw [Measure.real, μS_Φ, ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_inv]
  simp [div_eq_mul_inv]

lemma measurableSet_Φ (K : ℕ) (S : Set (Fin K → Bool × Bool)) : MeasurableSet (Φ K ⁻¹' S) := by
  have : Φ K ⁻¹' S = ⋃ p ∈ (Set.toFinite S).toFinset, Φ K ⁻¹' {p} := by
    ext ω; simp
  rw [this]
  exact Finset.measurableSet_biUnion _ (fun p _ => measurableSet_Φ_singleton K p)

/-! ### the pair sequence of a pattern and its partial sums -/

/-- `a_i`: the `i`-th reversed coefficient read from the pairs. -/
def aS {K : ℕ} (p : Fin K → Bool × Bool) (i : ℕ) : ℤ :=
  if h : i / 2 < K then (if i % 2 = 0 then st (p ⟨i / 2, h⟩).1 else st (p ⟨i / 2, h⟩).2) else 0

def Tk {K : ℕ} (p : Fin K → Bool × Bool) (k : ℕ) : ℤ := ∑ i ∈ range k, aS p i
def Ak {K : ℕ} (p : Fin K → Bool × Bool) (k : ℕ) : ℤ := ∑ i ∈ range k, (-1) ^ i * aS p i

/-- the cone condition on `K` backward pairs. -/
def coneP (K : ℕ) (p : Fin K → Bool × Bool) : Prop :=
  (∀ k ≤ 2 * K, 0 ≤ Tk p k ∧ 0 ≤ Ak p k) ∧ 0 < Tk p (2 * K) ∧ 0 < Ak p (2 * K)

/-- the weak (closed-quadrant) condition on the first `L` pairs. -/
def weakP (L : ℕ) (q : Fin L → Bool × Bool) : Prop := ∀ k ≤ 2 * L, 0 ≤ Tk q k ∧ 0 ≤ Ak q k

instance (K : ℕ) : DecidablePred (coneP K) := fun _ => by unfold coneP; infer_instance
instance (L : ℕ) : DecidablePred (weakP L) := fun _ => by unfold weakP; infer_instance

lemma aS_Φ (K : ℕ) (ω : ℕ → Bool) (i : ℕ) (hi : i < 2 * K) :
    aS (Φ K ω) i = st (ω (2 * K - 1 - i)) := by
  unfold aS
  rw [dif_pos (by omega)]
  split_ifs with h
  · simp only [Φ]; congr 2; omega
  · simp only [Φ]; congr 2; omega

/-- unit partial sums of the axis walk. -/
def Uc {L : ℕ} (q : Fin L → Bool × Bool) (j : ℕ) : ℤ :=
  ∑ i ∈ range j, if h : i < L then dU (q ⟨i, h⟩) else 0
def Vc {L : ℕ} (q : Fin L → Bool × Bool) (j : ℕ) : ℤ :=
  ∑ i ∈ range j, if h : i < L then dV (q ⟨i, h⟩) else 0

lemma st_sq (b : Bool) : st b * st b = 1 := by cases b <;> simp [st]

lemma aS_even {L : ℕ} (q : Fin L → Bool × Bool) (j : ℕ) (hj : j < L) :
    aS q (2 * j) = st (q ⟨j, hj⟩).1 := by
  unfold aS
  have hlt : 2 * j / 2 < L := by omega
  rw [dif_pos hlt, if_pos (by omega)]
  have : (⟨2 * j / 2, hlt⟩ : Fin L) = ⟨j, hj⟩ := Fin.ext (by simp only []; omega)
  rw [this]

lemma aS_odd {L : ℕ} (q : Fin L → Bool × Bool) (j : ℕ) (hj : j < L) :
    aS q (2 * j + 1) = st (q ⟨j, hj⟩).2 := by
  unfold aS
  have hlt : (2 * j + 1) / 2 < L := by omega
  rw [dif_pos hlt, if_neg (by omega)]
  have : (⟨(2 * j + 1) / 2, hlt⟩ : Fin L) = ⟨j, hj⟩ := Fin.ext (by simp only []; omega)
  rw [this]

lemma Tk_even {L : ℕ} (q : Fin L → Bool × Bool) (j : ℕ) (hj : j ≤ L) :
    Tk q (2 * j) = 2 * Uc q j ∧ Ak q (2 * j) = 2 * Vc q j := by
  induction j with
  | zero => simp [Tk, Ak, Uc, Vc]
  | succ j ih =>
    obtain ⟨ih1, ih2⟩ := ih (by omega)
    have hjL : j < L := by omega
    unfold Tk Ak at *
    rw [show 2 * (j + 1) = 2 * j + 1 + 1 by ring, sum_range_succ, sum_range_succ,
      sum_range_succ, sum_range_succ, ih1, ih2]
    unfold Uc Vc
    rw [sum_range_succ, sum_range_succ, dif_pos hjL, dif_pos hjL]
    rw [aS_even q j hjL, aS_odd q j hjL]
    have s1 : ((-1 : ℤ) ^ (2 * j)) = 1 := by rw [pow_mul]; norm_num
    have s2 : ((-1 : ℤ) ^ (2 * j + 1)) = -1 := by rw [pow_succ, s1]; norm_num
    rw [s1, s2]
    constructor
    · rcases q ⟨j, hjL⟩ with ⟨a, b⟩
      cases a <;> cases b <;> simp [dU, st] <;> ring
    · rcases q ⟨j, hjL⟩ with ⟨a, b⟩
      cases a <;> cases b <;> simp [dV, st] <;> ring

lemma Tk_odd {L : ℕ} (q : Fin L → Bool × Bool) (j : ℕ) (hj : j < L) :
    Tk q (2 * j + 1) = Tk q (2 * j) + st (q ⟨j, hj⟩).1 ∧
    Ak q (2 * j + 1) = Ak q (2 * j) + st (q ⟨j, hj⟩).1 := by
  unfold Tk Ak
  rw [sum_range_succ, sum_range_succ]
  have a1 := aS_even q j hj
  have s1 : ((-1 : ℤ) ^ (2 * j)) = 1 := by rw [pow_mul]; norm_num
  rw [a1, s1, one_mul]
  exact ⟨rfl, rfl⟩

/-- `good2` read through partial sums. -/
lemma good2_iff : ∀ (L : ℕ) (u v : ℤ) (q : Fin L → Bool × Bool),
    good2 L u v q ↔ ∀ j ≤ L, 0 ≤ u + Uc q j ∧ 0 ≤ v + Vc q j := by
  intro L
  induction L with
  | zero =>
    intro u v q
    simp [good2, Uc, Vc]
  | succ L ih =>
    intro u v q
    simp only [good2]
    rw [ih]
    have hU : ∀ j, Uc q (j + 1) = dU (q 0) + Uc (Fin.tail q) j := by
      intro j
      unfold Uc
      rw [sum_range_succ']
      rw [dif_pos (by omega), add_comm]
      congr 1
      apply sum_congr rfl
      intro i hi
      by_cases h : i < L
      · rw [dif_pos (by omega), dif_pos h]; rfl
      · rw [dif_neg (by omega), dif_neg h]
    have hV : ∀ j, Vc q (j + 1) = dV (q 0) + Vc (Fin.tail q) j := by
      intro j
      unfold Vc
      rw [sum_range_succ']
      rw [dif_pos (by omega), add_comm]
      congr 1
      apply sum_congr rfl
      intro i hi
      by_cases h : i < L
      · rw [dif_pos (by omega), dif_pos h]; rfl
      · rw [dif_neg (by omega), dif_neg h]
    constructor
    · rintro ⟨hu, hv, h⟩ j hj
      cases j with
      | zero => simp [Uc, Vc, hu, hv]
      | succ j =>
        rw [hU, hV]
        have := h j (by omega)
        constructor <;> linarith [this.1, this.2]
    · intro h
      have h0 := h 0 (by omega)
      simp only [Uc, Vc, range_zero, sum_empty, add_zero] at h0
      refine ⟨h0.1, h0.2, fun j hj => ?_⟩
      have := h (j + 1) (by omega)
      rw [hU, hV] at this
      constructor <;> linarith [this.1, this.2]

lemma weakP_good2 {L : ℕ} (q : Fin L → Bool × Bool) (h : weakP L q) : good2 L 0 0 q := by
  rw [good2_iff]
  intro j hj
  have := h (2 * j) (by omega)
  obtain ⟨e1, e2⟩ := Tk_even q j hj
  rw [e1, e2] at this
  constructor <;> linarith [this.1, this.2]

end E521

end S_C3

-- ===== P1 =====
section S_P1

/-! Cylinder events under the sign measure: measurability, independence of disjoint
coordinate blocks, shift invariance (original). -/

open Finset MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace E521

/-- restriction of `ω` to a finite set of coordinates. -/
def rs (s : Finset ℕ) (ω : ℕ → Bool) : s → Bool := fun i => ω i

lemma measurable_rs (s : Finset ℕ) : Measurable (rs s) := by
  unfold rs; fun_prop

lemma measurableSet_rs (s : Finset ℕ) (P : Set (s → Bool)) : MeasurableSet (rs s ⁻¹' P) :=
  measurable_rs s (Set.toFinite P).measurableSet

lemma iIndep_coords : iIndepFun (fun (i : ℕ) (ω : ℕ → Bool) => ω i) μS := by
  unfold μS
  exact iIndepFun_infinitePi (X := fun _ (b : Bool) => b) (fun _ => measurable_id)

/-- **independence of disjoint coordinate blocks.** -/
lemma indep_blocks {S T : Finset ℕ} (hST : Disjoint S T) (P : Set (S → Bool)) (Q : Set (T → Bool)) :
    μS (rs S ⁻¹' P ∩ rs T ⁻¹' Q) = μS (rs S ⁻¹' P) * μS (rs T ⁻¹' Q) := by
  have h := iIndep_coords.indepFun_finset S T hST (fun i => measurable_pi_apply i)
  exact h.measure_inter_preimage_eq_mul _ _ (Set.toFinite P).measurableSet (Set.toFinite Q).measurableSet

/-- shift invariance. -/
lemma μS_map_shift (d : ℕ) : μS.map (fun ω i => ω (i + d)) = μS := by
  unfold μS
  exact Measure.map_infinitePi_infinitePi_of_inj (f := fun i => i + d) (add_left_injective d)

lemma measurable_shift (d : ℕ) : Measurable (fun (ω : ℕ → Bool) (i : ℕ) => ω (i + d)) := by
  fun_prop

lemma μS_shift_preimage (d : ℕ) {A : Set (ℕ → Bool)} (hA : MeasurableSet A) :
    μS ((fun ω i => ω (i + d)) ⁻¹' A) = μS A := by
  rw [← Measure.map_apply (measurable_shift d) hA, μS_map_shift]

end E521

end S_P1

-- ===== C18 =====
section S_C18

/-! Ballot counts with a terminal condition, and the reflection (ballot) formula (original). -/

open Finset

namespace E521

/-- `±1` paths from `u` staying `≥ 0` whose final height satisfies `F`. -/
def good1F (F : ℤ → Prop) : (L : ℕ) → ℤ → (Fin L → Bool) → Prop
  | 0, u, _ => 0 ≤ u ∧ F u
  | L + 1, u, p => 0 ≤ u ∧ good1F F L (u + st (p 0)) (Fin.tail p)

instance good1F_dec (F : ℤ → Prop) [DecidablePred F] :
    ∀ (L : ℕ) (u : ℤ) (p : Fin L → Bool), Decidable (good1F F L u p)
  | 0, u, _ => by unfold good1F; infer_instance
  | L + 1, u, p => by
    unfold good1F
    haveI := good1F_dec F L (u + st (p 0)) (Fin.tail p)
    infer_instance

def N1F (F : ℤ → Prop) [DecidablePred F] (L : ℕ) (u : ℤ) : ℕ :=
  (univ.filter (fun p : Fin L → Bool => good1F F L u p)).card

lemma N1F_neg (F : ℤ → Prop) [DecidablePred F] (L : ℕ) {u : ℤ} (hu : u < 0) : N1F F L u = 0 := by
  unfold N1F
  rw [card_eq_zero, filter_eq_empty_iff]
  intro p _
  cases L with
  | zero => simp only [good1F]; omega
  | succ L => simp only [good1F]; omega

lemma N1F_succ (F : ℤ → Prop) [DecidablePred F] (L : ℕ) {u : ℤ} (hu : 0 ≤ u) :
    N1F F (L + 1) u = N1F F L (u + 1) + N1F F L (u - 1) := by
  unfold N1F
  rw [card_filter_eq_sum, card_filter_eq_sum, card_filter_eq_sum, sum_cons]
  simp only [Fintype.univ_bool, mem_singleton, Bool.true_eq_false, not_false_eq_true,
    sum_insert, sum_singleton]
  congr 1
  · apply Fintype.sum_congr; intro q
    simp only [good1F, Fin.cons_zero, Fin.tail_cons, st, if_true]
    by_cases h : good1F F L (u + 1) q
    · rw [if_pos ⟨hu, h⟩, if_pos h]
    · rw [if_neg (fun h' => h h'.2), if_neg h]
  · apply Fintype.sum_congr; intro q
    simp only [good1F, Fin.cons_zero, Fin.tail_cons, st]
    have e : u + (if false = true then (1 : ℤ) else -1) = u - 1 := by simp; ring
    rw [e]
    by_cases h : good1F F L (u - 1) q
    · rw [if_pos ⟨hu, h⟩, if_pos h]
    · rw [if_neg (fun h' => h h'.2), if_neg h]

lemma N1F_zero (F : ℤ → Prop) [DecidablePred F] (u : ℤ) :
    N1F F 0 u = if 0 ≤ u ∧ F u then 1 else 0 := by
  unfold N1F
  by_cases h : 0 ≤ u ∧ F u
  · rw [if_pos h, Finset.card_eq_one]
    refine ⟨default, ?_⟩
    ext p
    simp only [mem_filter, mem_univ, true_and, mem_singleton]
    exact ⟨fun _ => Subsingleton.elim _ _, fun _ => by first | exact h | (simp only [Set.mem_setOf_eq]; exact h) | simpa [good1F] using h⟩
  · rw [if_neg h, Finset.card_eq_zero, filter_eq_empty_iff]
    intro p _; simp only [good1F]; exact h

def good2F (F G : ℤ → Prop) : (L : ℕ) → ℤ → ℤ → (Fin L → Bool × Bool) → Prop
  | 0, u, v, _ => 0 ≤ u ∧ 0 ≤ v ∧ F u ∧ G v
  | L + 1, u, v, p => 0 ≤ u ∧ 0 ≤ v ∧ good2F F G L (u + dU (p 0)) (v + dV (p 0)) (Fin.tail p)

instance good2F_dec (F G : ℤ → Prop) [DecidablePred F] [DecidablePred G] :
    ∀ (L : ℕ) (u v : ℤ) (p : Fin L → Bool × Bool), Decidable (good2F F G L u v p)
  | 0, u, v, _ => by unfold good2F; infer_instance
  | L + 1, u, v, p => by
    unfold good2F
    haveI := good2F_dec F G L (u + dU (p 0)) (v + dV (p 0)) (Fin.tail p)
    infer_instance

def N2F (F G : ℤ → Prop) [DecidablePred F] [DecidablePred G] (L : ℕ) (u v : ℤ) : ℕ :=
  (univ.filter (fun p : Fin L → Bool × Bool => good2F F G L u v p)).card

lemma N2F_succ (F G : ℤ → Prop) [DecidablePred F] [DecidablePred G] (L : ℕ) {u v : ℤ}
    (hu : 0 ≤ u) (hv : 0 ≤ v) :
    N2F F G (L + 1) u v = N2F F G L (u + 1) v + N2F F G L (u - 1) v + N2F F G L u (v + 1)
      + N2F F G L u (v - 1) := by
  unfold N2F
  simp only [card_filter_eq_sum]
  rw [sum_cons]
  rw [Fintype.sum_prod_type]
  simp only [Fintype.univ_bool, mem_singleton, Bool.true_eq_false, not_false_eq_true,
    sum_insert, sum_singleton]
  have key : ∀ (a b : Bool) (q : Fin L → Bool × Bool),
      (if good2F F G (L + 1) u v (Fin.cons (a, b) q) then 1 else 0) =
      (if good2F F G L (u + dU (a, b)) (v + dV (a, b)) q then 1 else 0) := by
    intro a b q
    simp only [good2F, Fin.cons_zero, Fin.tail_cons]
    by_cases h : good2F F G L (u + dU (a, b)) (v + dV (a, b)) q
    · rw [if_pos ⟨hu, hv, h⟩, if_pos h]
    · rw [if_neg (fun h' => h h'.2.2), if_neg h]
  simp only [key, dU, dV, st]
  simp only [if_true, Bool.true_eq_false, if_false, Bool.false_eq_true, add_zero]
  have e : u + -1 = u - 1 := by ring
  have e' : v + -1 = v - 1 := by ring
  rw [e, e']
  ring

lemma N2F_neg (F G : ℤ → Prop) [DecidablePred F] [DecidablePred G] {L : ℕ} {u v : ℤ}
    (h : u < 0 ∨ v < 0) : N2F F G L u v = 0 := by
  unfold N2F
  rw [card_eq_zero, filter_eq_empty_iff]
  intro p _
  cases L with
  | zero => simp only [good2F]; omega
  | succ L => simp only [good2F]; omega

lemma N2F_zero (F G : ℤ → Prop) [DecidablePred F] [DecidablePred G] (u v : ℤ) :
    N2F F G 0 u v = if 0 ≤ u ∧ 0 ≤ v ∧ F u ∧ G v then 1 else 0 := by
  unfold N2F
  by_cases h : 0 ≤ u ∧ 0 ≤ v ∧ F u ∧ G v
  · rw [if_pos h, Finset.card_eq_one]
    refine ⟨default, ?_⟩
    ext p
    simp only [mem_filter, mem_univ, true_and, mem_singleton]
    exact ⟨fun _ => Subsingleton.elim _ _, fun _ => by first | exact h | (simp only [Set.mem_setOf_eq]; exact h) | simpa [good2F] using h⟩
  · rw [if_neg h, Finset.card_eq_zero, filter_eq_empty_iff]
    intro p _; simp only [good2F]; exact h

theorem N2F_eq (F G : ℤ → Prop) [DecidablePred F] [DecidablePred G] (L : ℕ) : ∀ u v : ℤ,
    N2F F G L u v = ∑ h ∈ range (L + 1), L.choose h * (N1F F h u * N1F G (L - h) v) := by
  induction L with
  | zero =>
    intro u v
    simp only [zero_add, range_one, sum_singleton, Nat.choose_self, Nat.sub_self, one_mul]
    rw [N1F_zero, N1F_zero, N2F_zero]
    by_cases h1 : 0 ≤ u ∧ F u <;> by_cases h2 : 0 ≤ v ∧ G v
    · rw [if_pos ⟨h1.1, h2.1, h1.2, h2.2⟩, if_pos h1, if_pos h2]
    · rw [if_neg (fun h => h2 ⟨h.2.1, h.2.2.2⟩), if_pos h1, if_neg h2]
    · rw [if_neg (fun h => h1 ⟨h.1, h.2.2.1⟩), if_neg h1, if_pos h2]
    · rw [if_neg (fun h => h1 ⟨h.1, h.2.2.1⟩), if_neg h1, if_neg h2]
  | succ L ih =>
    intro u v
    by_cases huv : 0 ≤ u ∧ 0 ≤ v
    · rw [N2F_succ F G L huv.1 huv.2, ih, ih, ih, ih]
      have r1 : ∀ h, N1F F h (u + 1) + N1F F h (u - 1) = N1F F (h + 1) u := fun h =>
        (N1F_succ F h huv.1).symm
      have r2 : ∀ h, N1F G h (v + 1) + N1F G h (v - 1) = N1F G (h + 1) v := fun h =>
        (N1F_succ G h huv.2).symm
      have A : (∑ h ∈ range (L + 1), L.choose h * (N1F F h (u + 1) * N1F G (L - h) v)) +
          (∑ h ∈ range (L + 1), L.choose h * (N1F F h (u - 1) * N1F G (L - h) v)) =
          ∑ h ∈ range (L + 1), L.choose h * (N1F F (h + 1) u * N1F G (L - h) v) := by
        rw [← sum_add_distrib]; apply sum_congr rfl; intro h _; rw [← r1]; ring
      have B : (∑ h ∈ range (L + 1), L.choose h * (N1F F h u * N1F G (L - h) (v + 1))) +
          (∑ h ∈ range (L + 1), L.choose h * (N1F F h u * N1F G (L - h) (v - 1))) =
          ∑ h ∈ range (L + 1), L.choose h * (N1F F h u * N1F G (L - h + 1) v) := by
        rw [← sum_add_distrib]; apply sum_congr rfl; intro h _; rw [← r2]; ring
      rw [A, add_assoc, B]
      rw [sum_range_succ' _ (L + 1)]
      simp only [Nat.choose_succ_succ', add_mul, sum_add_distrib]
      rw [sum_range_succ (fun h => L.choose (h + 1) * (N1F F (h + 1) u * N1F G (L + 1 - (h + 1)) v)) L]
      simp only [Nat.choose_succ_self, zero_mul, add_zero, Nat.choose_zero_right, one_mul,
        Nat.sub_zero]
      have C1 : ∑ h ∈ range (L + 1), L.choose h * (N1F F (h + 1) u * N1F G (L + 1 - (h + 1)) v) =
          ∑ h ∈ range (L + 1), L.choose h * (N1F F (h + 1) u * N1F G (L - h) v) := by
        apply sum_congr rfl; intro h _; congr 3; omega
      have C2 : ∑ h ∈ range L, L.choose (h + 1) * (N1F F (h + 1) u * N1F G (L + 1 - (h + 1)) v) +
          N1F F 0 u * N1F G (L + 1) v =
          ∑ h ∈ range (L + 1), L.choose h * (N1F F h u * N1F G (L - h + 1) v) := by
        rw [sum_range_succ' (fun h => L.choose h * (N1F F h u * N1F G (L - h + 1) v))]
        simp only [Nat.choose_zero_right, one_mul, Nat.sub_zero]
        congr 1
        apply sum_congr rfl; intro h hh; rw [mem_range] at hh; congr 3; omega
      rw [C1, ← C2]; ring
    · rw [N2F_neg F G (by omega)]
      symm
      apply sum_eq_zero
      intro h _
      rcases not_and_or.mp huv with hu | hv
      · rw [N1F_neg F h (by omega)]; ring
      · rw [N1F_neg G (L + 1 - h) (by omega)]; ring

/-! ### the ballot formula -/

/-- binomial coefficient extended by `0` to negative arguments. -/
def chZ (h : ℕ) (k : ℤ) : ℤ := if k < 0 then 0 else (h.choose k.toNat : ℤ)

lemma chZ_pascal (h : ℕ) (k : ℤ) : chZ (h + 1) k = chZ h k + chZ h (k - 1) := by
  unfold chZ
  by_cases hk : k < 0
  · rw [if_pos hk, if_pos hk, if_pos (by omega)]; ring
  · rw [if_neg hk, if_neg hk]
    by_cases hk0 : k = 0
    · subst hk0; rw [if_pos (by omega)]; simp
    · rw [if_neg (by omega)]
      have : k.toNat = (k - 1).toNat + 1 := by omega
      rw [this, Nat.choose_succ_succ']; push_cast; ring

lemma chZ_zero_of_lt {h : ℕ} {k : ℤ} (hk : (h : ℤ) < k) : chZ h k = 0 := by
  unfold chZ; rw [if_neg (by omega)]
  rw [Nat.choose_eq_zero_of_lt (by omega)]; simp

lemma chZ_zero_pos {k : ℤ} (hk : 0 < k) : chZ 0 k = 0 := chZ_zero_of_lt (by simpa using hk)

/-- **Ballot formula**: paths of length `h` from `u` staying `≥ 0` and ending at
`y = u + 2k - h ≥ 0` number `C(h,k) - C(h,k+u+1)`. -/
theorem ballot (h : ℕ) : ∀ (u : ℕ) (k : ℤ), 0 ≤ (u : ℤ) + 2 * k - h →
    (N1F (· = (u : ℤ) + 2 * k - h) h u : ℤ) = chZ h k - chZ h (k + u + 1) := by
  induction h with
  | zero =>
    intro u k hy
    rw [N1F_zero]
    push_cast
    by_cases hk : k = 0
    · subst hk
      rw [if_pos ⟨by positivity, by ring⟩]
      have hc : chZ 0 (0 + (u : ℤ) + 1) = 0 := chZ_zero_pos (by omega)
      rw [hc]
      simp [chZ]
    · rw [if_neg (fun h' => hk (by omega))]
      rcases lt_or_gt_of_ne hk with hk' | hk'
      · rw [show chZ 0 k = 0 by unfold chZ; rw [if_pos hk'], chZ_zero_pos (by omega)]; simp
      · rw [chZ_zero_pos hk', chZ_zero_pos (by omega)]; simp
  | succ h ih =>
    intro u k hy
    rw [N1F_succ _ h (by positivity)]
    push_cast
    have hup := ih (u + 1) (k - 1) (by push_cast; omega)
    have e1 : ((u + 1 : ℕ) : ℤ) + 2 * (k - 1) - h = (u : ℤ) + 2 * k - (h + 1) := by push_cast; ring
    have e2 : ((u + 1 : ℕ) : ℤ) = (u : ℤ) + 1 := by push_cast; ring
    rw [e1, e2] at hup
    have e3 : k - 1 + ((u : ℤ) + 1) + 1 = k + u + 1 := by ring
    rw [e3] at hup
    rw [hup]
    rcases Nat.eq_zero_or_pos u with hu | hu
    · subst hu
      rw [N1F_neg _ h (by norm_num)]
      push_cast
      rw [chZ_pascal, chZ_pascal]
      ring_nf
    · have hdown := ih (u - 1) k (by
        have : ((u - 1 : ℕ) : ℤ) = (u : ℤ) - 1 := by omega
        rw [this]; omega)
      have e4 : ((u - 1 : ℕ) : ℤ) = (u : ℤ) - 1 := by omega
      rw [e4] at hdown
      have e5 : (u : ℤ) - 1 + 2 * k - h = (u : ℤ) + 2 * k - (h + 1) := by ring
      rw [e5] at hdown
      rw [hdown]
      rw [chZ_pascal, chZ_pascal]
      ring_nf

end E521

end S_C18

-- ===== P2 =====
section S_P2

/-! The cone and top events and their probabilities (original). -/

open Finset MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace E521

/-- `good2F` read through partial sums. -/
lemma good2F_iff (F G : ℤ → Prop) : ∀ (L : ℕ) (u v : ℤ) (q : Fin L → Bool × Bool),
    good2F F G L u v q ↔ (∀ j ≤ L, 0 ≤ u + Uc q j ∧ 0 ≤ v + Vc q j) ∧ F (u + Uc q L) ∧ G (v + Vc q L) := by
  intro L
  induction L with
  | zero => intro u v q; simp [good2F, Uc, Vc]; tauto
  | succ L ih =>
    intro u v q
    simp only [good2F]
    rw [ih]
    have hU : ∀ j, Uc q (j + 1) = dU (q 0) + Uc (Fin.tail q) j := by
      intro j
      unfold Uc
      rw [sum_range_succ', dif_pos (by omega), add_comm]
      congr 1
      apply sum_congr rfl
      intro i _
      by_cases h : i < L
      · rw [dif_pos (by omega), dif_pos h]; rfl
      · rw [dif_neg (by omega), dif_neg h]
    have hV : ∀ j, Vc q (j + 1) = dV (q 0) + Vc (Fin.tail q) j := by
      intro j
      unfold Vc
      rw [sum_range_succ', dif_pos (by omega), add_comm]
      congr 1
      apply sum_congr rfl
      intro i _
      by_cases h : i < L
      · rw [dif_pos (by omega), dif_pos h]; rfl
      · rw [dif_neg (by omega), dif_neg h]
    constructor
    · rintro ⟨hu, hv, ⟨h, hF, hG⟩⟩
      refine ⟨fun j hj => ?_, ?_, ?_⟩
      · cases j with
        | zero => simp [Uc, Vc, hu, hv]
        | succ j =>
          rw [hU, hV]
          have := h j (by omega)
          constructor <;> linarith [this.1, this.2]
      · rw [hU]; convert hF using 1; ring
      · rw [hV]; convert hG using 1; ring
    · rintro ⟨h, hF, hG⟩
      have h0 := h 0 (by omega)
      simp only [Uc, Vc, range_zero, sum_empty, add_zero] at h0
      refine ⟨h0.1, h0.2, fun j hj => ?_, ?_, ?_⟩
      · have := h (j + 1) (by omega)
        rw [hU, hV] at this
        constructor <;> linarith [this.1, this.2]
      · rw [hU] at hF; convert hF using 1; ring
      · rw [hV] at hG; convert hG using 1; ring

/-- the cone event on `K` backward pairs, with final conditions. -/
def coneE (K : ℕ) (F G : ℤ → Prop) : Set (ℕ → Bool) := Φ K ⁻¹' {p | good2F F G K 0 0 p}

lemma coneE_real (K : ℕ) (F G : ℤ → Prop) [DecidablePred F] [DecidablePred G] :
    μS.real (coneE K F G) = (N2F F G K 0 0 : ℝ) / 4 ^ K := by
  have h := μS_Φ_real K (univ.filter (fun p : Fin K → Bool × Bool => good2F F G K 0 0 p))
  unfold coneE N2F
  convert h using 2
  ext p; simp

/-- the closed-quadrant condition on the first `L` backward pairs of level `K`. -/
def topE (K L : ℕ) : Set (ℕ → Bool) :=
  {ω | good2 L 0 0 (fun j : Fin L => (ω (2 * K - 1 - 2 * j), ω (2 * K - 2 - 2 * j)))}

lemma topE_eq (K L : ℕ) (hL : L ≤ K) :
    topE K L = (fun ω i => ω (i + 2 * (K - L))) ⁻¹' (Φ L ⁻¹' {p | good2 L 0 0 p}) := by
  ext ω
  simp only [topE, Set.mem_setOf_eq, Set.mem_preimage, Φ]
  have : (fun j : Fin L => (ω (2 * K - 1 - 2 * j), ω (2 * K - 2 - 2 * j))) =
      (fun j : Fin L => (ω (2 * L - 1 - 2 * j + 2 * (K - L)), ω (2 * L - 2 - 2 * j + 2 * (K - L)))) := by
    funext j; have := j.isLt; congr 2 <;> omega
  rw [this]
  exact Iff.rfl

lemma topE_real (K L : ℕ) (hL : L ≤ K) : μS.real (topE K L) = (N2 L 0 0 : ℝ) / 4 ^ L := by
  rw [Measure.real, topE_eq K L hL, μS_shift_preimage _ (measurableSet_Φ L _)]
  have h := μS_Φ_real L (univ.filter (fun p : Fin L → Bool × Bool => good2 L 0 0 p))
  rw [Measure.real] at h
  unfold N2
  convert h using 3
  ext p; simp

lemma cone_sub_top (K L : ℕ) (hL : L ≤ K) (F G : ℤ → Prop) : coneE K F G ⊆ topE K L := by
  intro ω hω
  simp only [coneE, Set.mem_preimage, Set.mem_setOf_eq] at hω
  rw [good2F_iff] at hω
  simp only [topE, Set.mem_setOf_eq]
  rw [good2_iff]
  intro j hj
  have := hω.1 j (by omega)
  have eU : Uc (fun j : Fin L => (ω (2 * K - 1 - 2 * j), ω (2 * K - 2 - 2 * j))) j = Uc (Φ K ω) j := by
    unfold Uc; apply sum_congr rfl; intro i hi; rw [mem_range] at hi
    rw [dif_pos (by omega), dif_pos (by omega)]; rfl
  have eV : Vc (fun j : Fin L => (ω (2 * K - 1 - 2 * j), ω (2 * K - 2 - 2 * j))) j = Vc (Φ K ω) j := by
    unfold Vc; apply sum_congr rfl; intro i hi; rw [mem_range] at hi
    rw [dif_pos (by omega), dif_pos (by omega)]; rfl
  rw [eU, eV]; simpa using this

/-- `topE K L` only depends on the coordinates `[2K-2L, 2K)`. -/
lemma topE_cyl (K L : ℕ) (hL : L ≤ K) :
    ∃ Q : Set (Ico (2 * K - 2 * L) (2 * K) → Bool), topE K L = rs (Ico (2 * K - 2 * L) (2 * K)) ⁻¹' Q := by
  refine ⟨{r | good2 L 0 0 (fun j : Fin L =>
    (r ⟨2 * K - 1 - 2 * j, by have := j.isLt; simp [mem_Ico]; omega⟩,
     r ⟨2 * K - 2 - 2 * j, by have := j.isLt; simp [mem_Ico]; omega⟩))}, ?_⟩
  ext ω; simp [topE, rs]

end E521

end S_P2


end
