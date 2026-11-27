/-
Copyright 2026 Ming-Chih Kao. Licensed under the Apache License, Version 2.0;
see the LICENSE file at the root of this repository.
-/
module

public import FriedanQ.Schur

/-! Port: copied from `quantum-lean/FriedanQ/VecQ.lean` of github.com/koolkao/friedan-entropy-inequality (commit 0f4ba65dc126f59e7158fbcbc01548baa78cf21d, Lean v4.36.0, Mathlib fc4f59e, physlib edc607c) and put into the module system (`module` header, `public import`, public section). The proofs are unchanged unless a comment marked `Port` says otherwise. -/

@[expose] public section

/-!
# Theorem Q (vector form)

If `x = log μ` is weakly majorized by `a log p + (1 - a) log q` (sorted), then
`K² H(μ/K) ≤ a H(p) + (1 - a) H(q)`. The sorted, `ℕ`-indexed version is `sortedQ`; the
sorting-free version over a finite type, with hypothesis "every `k`-subset sum of `x` is bounded
by `a ∑_T log p + (1-a) ∑_U log q` for some `k`-subsets `T, U`", is `vecQ`.
-/

open Real Finset

namespace FriedanQ

/-- Sorted version, vectors on `range n`. -/
theorem sortedQ {n : ℕ} (x p q : ℕ → ℝ) (hp : ∀ i < n, 0 < p i) (hq : ∀ i < n, 0 < q i)
    (hps : ∑ i ∈ range n, p i = 1) (hqs : ∑ i ∈ range n, q i = 1)
    (hpa : ∀ i j, i ≤ j → j < n → p j ≤ p i) (hqa : ∀ i j, i ≤ j → j < n → q j ≤ q i)
    (hx : ∀ i j, i ≤ j → j < n → x j ≤ x i) {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hmaj : ∀ k ≤ n, ∑ i ∈ range k, x i ≤
      a * ∑ i ∈ range k, log (p i) + (1 - a) * ∑ i ∈ range k, log (q i)) :
    G n x ≤ a * ∑ i ∈ range n, negMulLog (p i) + (1 - a) * ∑ i ∈ range n, negMulLog (q i) := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; simp [G, Kx, Ex]
  set y : ℕ → ℝ := fun i => a * log (p i) + (1 - a) * log (q i) with hydef
  have hy : ∀ i j, i ≤ j → j < n → y j ≤ y i := by
    intro i j hij hj
    have h1 := log_le_log (hp j hj) (hpa i j hij hj)
    have h2 := log_le_log (hq j hj) (hqa i j hij hj)
    have := mul_le_mul_of_nonneg_left h1 ha0
    have := mul_le_mul_of_nonneg_left h2 (by linarith : (0 : ℝ) ≤ 1 - a)
    simp only [hydef]; linarith
  have hmaj' : ∀ k ≤ n, ∑ i ∈ range k, x i ≤ ∑ i ∈ range k, y i := by
    intro k hk
    simp only [hydef, sum_add_distrib, ← mul_sum]
    exact hmaj k hk
  have h1 := G_le n x y hx hy hmaj'
  rw [G_eq hn y] at h1
  -- `exp (y i) = p i ^ a * q i ^ (1 - a)` on `range n`
  have hc : ∀ i < n, exp (y i) = p i ^ a * q i ^ (1 - a) := by
    intro i hi
    simp only [hydef]
    rw [exp_add, rpow_def_of_pos (hp i hi), rpow_def_of_pos (hq i hi), mul_comm a,
      mul_comm (1 - a)]
  have hK : Kx n y = ∑ i ∈ range n, p i ^ a * q i ^ (1 - a) :=
    sum_congr rfl (fun i hi => hc i (mem_range.1 hi))
  have hH : ∑ i ∈ range n, negMulLog (exp (y i) / Kx n y) =
      ∑ i ∈ range n, negMulLog (p i ^ a * q i ^ (1 - a) / ∑ j ∈ range n, p j ^ a * q j ^ (1 - a)) :=
    sum_congr rfl (fun i hi => by rw [hc i (mem_range.1 hi), hK])
  rw [hH, hK] at h1
  have hKpos : 0 < ∑ i ∈ range n, p i ^ a * q i ^ (1 - a) := by
    rw [← hK]; exact Kx_pos hn y
  have hcl := Friedan.main_proof n (fun i => p i) (fun i => q i)
    (fun i => (hp i i.isLt).le) (by rw [Fin.sum_univ_eq_sum_range p n]; exact hps)
    (fun i => (hq i i.isLt).le) (by rw [Fin.sum_univ_eq_sum_range q n]; exact hqs) a ha0 ha1
    (by rw [Fin.sum_univ_eq_sum_range (fun i => p i ^ a * q i ^ (1 - a)) n]; exact hKpos)
  simp only [OMA.S_mo_138395.entropy] at hcl
  rw [Fin.sum_univ_eq_sum_range (fun i => p i ^ a * q i ^ (1 - a)) n,
    Fin.sum_univ_eq_sum_range (fun i => negMulLog (p i)) n,
    Fin.sum_univ_eq_sum_range (fun i => negMulLog (q i)) n,
    Fin.sum_univ_eq_sum_range (fun i => negMulLog (p i ^ a * q i ^ (1 - a) /
      ∑ j ∈ range n, p j ^ a * q j ^ (1 - a))) n] at hcl
  linarith

/-! ## Sorting a vector on a finite type -/

lemma exists_antitone_equiv {d : Type*} [Fintype d] (f : d → ℝ) :
    ∃ e : Fin (Fintype.card d) ≃ d, Antitone (f ∘ e) := by
  let e0 : Fin (Fintype.card d) ≃ d := (Fintype.equivFin d).symm
  let g : Fin (Fintype.card d) → ℝ := fun i => -(f (e0 i))
  refine ⟨(Tuple.sort g).trans e0, ?_⟩
  intro i j hij
  have := Tuple.monotone_sort g hij
  simp only [Function.comp_apply, g, neg_le_neg_iff] at this
  simpa using this

/-- Extension of `f ∘ e` to `ℕ` (zero beyond `n`). -/
noncomputable def ext {d : Type*} {n : ℕ} (e : Fin n ≃ d) (f : d → ℝ) (k : ℕ) : ℝ :=
  if h : k < n then f (e ⟨k, h⟩) else 0

lemma ext_lt {d : Type*} {n : ℕ} (e : Fin n ≃ d) (f : d → ℝ) {k : ℕ} (h : k < n) :
    ext e f k = f (e ⟨k, h⟩) := dif_pos h

/-- image of a finset of `d` in `ℕ` -/
noncomputable def toNat {d : Type*} {n : ℕ} (e : Fin n ≃ d) (T : Finset d) : Finset ℕ :=
  (T.map e.symm.toEmbedding).map Fin.valEmbedding

lemma toNat_card {d : Type*} {n : ℕ} (e : Fin n ≃ d) (T : Finset d) :
    (toNat e T).card = T.card := by simp [toNat]

lemma toNat_sub {d : Type*} {n : ℕ} (e : Fin n ≃ d) (T : Finset d) : toNat e T ⊆ range n := by
  intro m hm
  simp only [toNat, mem_map, Fin.valEmbedding_apply, Equiv.coe_toEmbedding] at hm
  obtain ⟨i, _, rfl⟩ := hm
  exact mem_range.2 i.isLt

lemma sum_toNat {d : Type*} {n : ℕ} (e : Fin n ≃ d) (f : d → ℝ) (g : ℝ → ℝ) (T : Finset d) :
    ∑ j ∈ T, g (f j) = ∑ k ∈ toNat e T, g (ext e f k) := by
  simp only [toNat, sum_map, Fin.valEmbedding_apply, Equiv.coe_toEmbedding]
  refine sum_congr rfl (fun j _ => ?_)
  rw [ext_lt e f (e.symm j).isLt]
  simp

lemma toNat_univ {d : Type*} [Fintype d] {n : ℕ} (e : Fin n ≃ d) :
    toNat e (univ : Finset d) = range n :=
  eq_of_subset_of_card_le (toNat_sub e univ)
    (by rw [toNat_card, card_range, card_univ, ← Fintype.card_congr e, Fintype.card_fin])

lemma toNat_prefix {d : Type*} {n : ℕ} (e : Fin n ≃ d) {k : ℕ} (hk : k ≤ n) :
    toNat e ((univ.filter (fun i : Fin n => i.val < k)).map e.toEmbedding) = range k := by
  ext m
  simp only [toNat, map_map, mem_map, mem_filter, mem_univ, true_and, Fin.valEmbedding_apply,
    Function.Embedding.trans_apply, Equiv.coe_toEmbedding, Equiv.symm_apply_apply, mem_range]
  constructor
  · rintro ⟨i, h, rfl⟩; exact h
  · intro h; exact ⟨⟨m, by omega⟩, h, rfl⟩

/-- **Theorem Q, vector form (sorting-free).** -/
theorem vecQ {d : Type*} [Fintype d] [DecidableEq d] (x p q : d → ℝ) (hp : ∀ i, 0 < p i)
    (hq : ∀ i, 0 < q i) (hps : ∑ i, p i = 1) (hqs : ∑ i, q i = 1) {a : ℝ} (ha0 : 0 ≤ a)
    (ha1 : a ≤ 1)
    (hW : ∀ S : Finset d, ∃ T U : Finset d, T.card = S.card ∧ U.card = S.card ∧
      ∑ i ∈ S, x i ≤ a * ∑ i ∈ T, log (p i) + (1 - a) * ∑ i ∈ U, log (q i)) :
    (∑ i, exp (x i)) ^ 2 * ∑ i, negMulLog (exp (x i) / ∑ j, exp (x j)) ≤
      a * ∑ i, negMulLog (p i) + (1 - a) * ∑ i, negMulLog (q i) := by
  set n := Fintype.card d
  obtain ⟨ex, hex⟩ := exists_antitone_equiv x
  obtain ⟨ep, hep⟩ := exists_antitone_equiv p
  obtain ⟨eq, heq⟩ := exists_antitone_equiv q
  set x' := ext ex x
  set p' := ext ep p
  set q' := ext eq q
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
  have hmaj : ∀ k ≤ n, ∑ i ∈ range k, x' i ≤
      a * ∑ i ∈ range k, log (p' i) + (1 - a) * ∑ i ∈ range k, log (q' i) := by
    intro k hk
    set S := (univ.filter (fun i : Fin n => i.val < k)).map ex.toEmbedding
    have hS : S.card = k := by
      simp only [S, card_map]
      rw [Fin.card_filter_val_lt]; omega
    obtain ⟨T, U, hT, hU, hle⟩ := hW S
    have e1 : ∑ i ∈ range k, x' i = ∑ i ∈ S, x i := by
      have h := sum_toNat ex x id S
      simp only [id] at h
      rw [h, toNat_prefix ex hk]
    have e2 : ∑ i ∈ T, log (p i) = ∑ i ∈ toNat ep T, log (p' i) := sum_toNat ep p log T
    have e3 : ∑ i ∈ U, log (q i) = ∑ i ∈ toNat eq U, log (q' i) := sum_toNat eq q log U
    have b2 : ∑ i ∈ toNat ep T, log (p' i) ≤ ∑ i ∈ range k, log (p' i) := by
      have := sum_subset_le_prefix (fun i => log (p' i)) (hlog_anti hp hep) _ (toNat_sub ep T)
      rwa [toNat_card, hT, hS] at this
    have b3 : ∑ i ∈ toNat eq U, log (q' i) ≤ ∑ i ∈ range k, log (q' i) := by
      have := sum_subset_le_prefix (fun i => log (q' i)) (hlog_anti hq heq) _ (toNat_sub eq U)
      rwa [toNat_card, hU, hS] at this
    have := mul_le_mul_of_nonneg_left b2 ha0
    have := mul_le_mul_of_nonneg_left b3 (by linarith : (0 : ℝ) ≤ 1 - a)
    rw [e1]; rw [e2, e3] at hle; linarith
  have hQ := sortedQ x' p' q' (hpos hp) (hpos hq)
    (by have h := hsum (e := ep) p id; simp only [id] at h; exact h.trans hps)
    (by have h := hsum (e := eq) q id; simp only [id] at h; exact h.trans hqs)
    (anti hep) (anti heq) (anti hex) ha0 ha1 hmaj
  rw [hsum p negMulLog, hsum q negMulLog] at hQ
  rcases Nat.eq_zero_or_pos n with hn | hn
  · have : IsEmpty d := Fintype.card_eq_zero_iff.1 hn
    simp
  rw [G_eq hn] at hQ
  have hK : Kx n x' = ∑ j, exp (x j) := hsum x exp
  rw [hK, hsum x (fun v => negMulLog (exp v / ∑ j, exp (x j)))] at hQ
  exact hQ

end FriedanQ

end
