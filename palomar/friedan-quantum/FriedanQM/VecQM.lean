/-
Copyright 2026 Ming-Chih Kao. Licensed under the Apache License, Version 2.0;
see the LICENSE file at the root of this repository.
-/
module

public import FriedanQ.VecQ
public import FriedanMulti.Main

/-! Port: copied from `quantum-lean/FriedanQM/VecQM.lean` of github.com/koolkao/friedan-entropy-inequality (commit 0f4ba65dc126f59e7158fbcbc01548baa78cf21d, Lean v4.36.0, Mathlib fc4f59e, physlib edc607c) and put into the module system (`module` header, `public import`, public section). The proofs are unchanged unless a comment marked `Port` says otherwise. -/

@[expose] public section

/-!
# Theorem QM (vector form): `m` spectra

If `x = log μ` is weakly majorized by `∑ⱼ aⱼ log p⁽ʲ⁾` (all sorted), then
`K² H(μ/K) ≤ ∑ⱼ aⱼ H(p⁽ʲ⁾)`. Same route as `FriedanQ.vecQ` (m = 2): `G_le` (Schur-convexity),
then classical Theorem M (`FriedanMulti.theoremM`) for the aligned spectra.
-/

open Real Finset

namespace FriedanQ

/-- Sorted version, vectors on `range n`. -/
theorem sortedQM {n m : ℕ} (x : ℕ → ℝ) (p : Fin m → ℕ → ℝ) (hp : ∀ j, ∀ i < n, 0 < p j i)
    (hps : ∀ j, ∑ i ∈ range n, p j i = 1) (hpa : ∀ j i k, i ≤ k → k < n → p j k ≤ p j i)
    (hx : ∀ i k, i ≤ k → k < n → x k ≤ x i) (a : Fin m → ℝ) (ha0 : ∀ j, 0 ≤ a j)
    (has : ∑ j, a j = 1)
    (hmaj : ∀ k ≤ n, ∑ i ∈ range k, x i ≤ ∑ j, a j * ∑ i ∈ range k, log (p j i)) :
    G n x ≤ ∑ j, a j * ∑ i ∈ range n, negMulLog (p j i) := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; simp [G, Kx, Ex]
  set y : ℕ → ℝ := fun i => ∑ j, a j * log (p j i) with hydef
  have hy : ∀ i k, i ≤ k → k < n → y k ≤ y i := by
    intro i k hik hk
    simp only [hydef]
    refine Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left ?_ (ha0 j))
    exact log_le_log (hp j k hk) (hpa j i k hik hk)
  have hmaj' : ∀ k ≤ n, ∑ i ∈ range k, x i ≤ ∑ i ∈ range k, y i := by
    intro k hk
    have e : ∑ i ∈ range k, y i = ∑ j, a j * ∑ i ∈ range k, log (p j i) := by
      simp only [hydef]; rw [Finset.sum_comm]; simp only [Finset.mul_sum]
    rw [e]; exact hmaj k hk
  have h1 := G_le n x y hx hy hmaj'
  rw [G_eq hn y] at h1
  have hc : ∀ i < n, exp (y i) = ∏ j, p j i ^ a j := by
    intro i hi
    simp only [hydef]
    rw [exp_sum]
    refine Finset.prod_congr rfl (fun j _ => ?_)
    rw [rpow_def_of_pos (hp j i hi), mul_comm]
  have hK : Kx n y = ∑ i ∈ range n, ∏ j, p j i ^ a j :=
    sum_congr rfl (fun i hi => hc i (mem_range.1 hi))
  have hH : ∑ i ∈ range n, negMulLog (exp (y i) / Kx n y) =
      ∑ i ∈ range n, negMulLog ((∏ j, p j i ^ a j) / ∑ k ∈ range n, ∏ j, p j k ^ a j) :=
    sum_congr rfl (fun i hi => by rw [hc i (mem_range.1 hi), hK])
  rw [hH, hK] at h1
  have hKpos : 0 < ∑ i ∈ range n, ∏ j, p j i ^ a j := by rw [← hK]; exact Kx_pos hn y
  have hcl := FriedanMulti.theoremM n m (fun j (i : Fin n) => p j i)
    (fun j i => (hp j i i.isLt).le)
    (fun j => by rw [Fin.sum_univ_eq_sum_range (p j) n]; exact hps j) a ha0 has
    (by rw [Fin.sum_univ_eq_sum_range (fun i => ∏ j, p j i ^ a j) n]; exact hKpos)
  simp only [FriedanMulti.entropy] at hcl
  rw [Fin.sum_univ_eq_sum_range (fun i => ∏ j, p j i ^ a j) n,
    Fin.sum_univ_eq_sum_range (fun i => negMulLog ((∏ j, p j i ^ a j) /
      ∑ k ∈ range n, ∏ j, p j k ^ a j)) n] at hcl
  have e : ∀ j, ∑ i : Fin n, negMulLog (p j i) = ∑ i ∈ range n, negMulLog (p j i) :=
    fun j => Fin.sum_univ_eq_sum_range (fun i => negMulLog (p j i)) n
  simp only [e] at hcl
  linarith

/-- **Theorem QM, vector form (sorting-free).** -/
theorem vecQM {d : Type*} [Fintype d] [DecidableEq d] {m : ℕ} (x : d → ℝ) (p : Fin m → d → ℝ)
    (hp : ∀ j i, 0 < p j i) (hps : ∀ j, ∑ i, p j i = 1) (a : Fin m → ℝ) (ha0 : ∀ j, 0 ≤ a j)
    (has : ∑ j, a j = 1)
    (hW : ∀ S : Finset d, ∃ T : Fin m → Finset d, (∀ j, (T j).card = S.card) ∧
      ∑ i ∈ S, x i ≤ ∑ j, a j * ∑ i ∈ T j, log (p j i)) :
    (∑ i, exp (x i)) ^ 2 * ∑ i, negMulLog (exp (x i) / ∑ j, exp (x j)) ≤
      ∑ j, a j * ∑ i, negMulLog (p j i) := by
  set n := Fintype.card d
  obtain ⟨ex, hex⟩ := exists_antitone_equiv x
  choose ep hep using fun j => exists_antitone_equiv (p j)
  set x' := ext ex x
  set p' : Fin m → ℕ → ℝ := fun j => ext (ep j) (p j)
  have hsum : ∀ {e : Fin n ≃ d} (f : d → ℝ) (g : ℝ → ℝ),
      ∑ k ∈ range n, g (ext e f k) = ∑ j, g (f j) := by
    intro e f g; rw [sum_toNat e f g univ, toNat_univ]
  have anti : ∀ {e : Fin n ≃ d} {f : d → ℝ}, Antitone (f ∘ e) →
      ∀ i j, i ≤ j → j < n → ext e f j ≤ ext e f i := by
    intro e f hf i j hij hj
    rw [ext_lt e f hj, ext_lt e f (by omega)]
    exact hf (show (⟨i, by omega⟩ : Fin n) ≤ ⟨j, hj⟩ from hij)
  have hpos : ∀ {e : Fin n ≃ d} {f : d → ℝ}, (∀ i, 0 < f i) → ∀ i < n, 0 < ext e f i := by
    intro e f hf i hi; rw [ext_lt e f hi]; exact hf _
  have hlog_anti : ∀ {e : Fin n ≃ d} {f : d → ℝ}, (∀ i, 0 < f i) → Antitone (f ∘ e) →
      ∀ i j, i ≤ j → j < n → log (ext e f j) ≤ log (ext e f i) := by
    intro e f hf ha i j hij hj
    exact log_le_log (hpos hf j hj) (anti ha i j hij hj)
  have hmaj : ∀ k ≤ n, ∑ i ∈ range k, x' i ≤ ∑ j, a j * ∑ i ∈ range k, log (p' j i) := by
    intro k hk
    set S := (univ.filter (fun i : Fin n => i.val < k)).map ex.toEmbedding
    have hS : S.card = k := by
      simp only [S, card_map]
      rw [Fin.card_filter_val_lt]; omega
    obtain ⟨T, hT, hle⟩ := hW S
    have e1 : ∑ i ∈ range k, x' i = ∑ i ∈ S, x i := by
      have h := sum_toNat ex x id S
      simp only [id] at h
      rw [h, toNat_prefix ex hk]
    have b : ∀ j, ∑ i ∈ T j, log (p j i) ≤ ∑ i ∈ range k, log (p' j i) := by
      intro j
      rw [sum_toNat (ep j) (p j) log (T j)]
      have := sum_subset_le_prefix (fun i => log (p' j i)) (hlog_anti (hp j) (hep j)) _
        (toNat_sub (ep j) (T j))
      rwa [toNat_card, hT j, hS] at this
    rw [e1]
    refine hle.trans (Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (b j) (ha0 j)))
  have hQ := sortedQM x' p' (fun j => hpos (hp j))
    (fun j => by have h := hsum (e := ep j) (p j) id; simp only [id] at h; exact h.trans (hps j))
    (fun j => anti (hep j)) (anti hex) a ha0 has hmaj
  have hR : ∀ j, ∑ i ∈ range n, negMulLog (p' j i) = ∑ i, negMulLog (p j i) :=
    fun j => hsum (p j) negMulLog
  simp only [hR] at hQ
  rcases Nat.eq_zero_or_pos n with hn | hn
  · have : IsEmpty d := Fintype.card_eq_zero_iff.1 hn
    have hs : ∑ i, p ⟨0, by
        rcases Nat.eq_zero_or_pos m with hm | hm
        · subst hm; simp at has
        · exact hm⟩ i = 0 := by simp
    rw [hps] at hs
    exact absurd hs one_ne_zero
  rw [G_eq hn] at hQ
  have hK : Kx n x' = ∑ j, exp (x j) := hsum x exp
  rw [hK, hsum x (fun v => negMulLog (exp v / ∑ j, exp (x j)))] at hQ
  exact hQ

end FriedanQ

end
