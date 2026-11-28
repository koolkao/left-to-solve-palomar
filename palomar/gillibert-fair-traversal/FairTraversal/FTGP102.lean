/-
Copyright 2026 Ming-Chih Kao. Licensed under the Apache License, Version 2.0;
see the LICENSE file at the root of this repository.
Ported from github.com/koolkao/gillibert-fair-traversal-abelian (v1.7.0, commit
06c3a8732759afca38331762b76113135e475ac6) to Lean v4.36.0 and the module system.
-/
module

public import FairTraversal.FTGPNeg

/-!
# Theorem 9 in Lean, case GP(10, 2) (the dodecahedron), and Theorem 9 in full (new in v1.7.0)

GP(10, 2) has a *perfect 1-factorization*: three perfect matchings whose complements `cyc0`, `cyc1`, `cyc2` are
Hamiltonian cycles, so every edge lies on exactly two of the three cycles. Deleting each of the 20 edges of each cycle
gives 60 Hamiltonian paths (`L i`, rotations of the cycles), and every edge lies on exactly 2 · 19 = 38 of them.
All finite facts are checked by `decide` on explicit lists. `ft_gp_all` combines this with `FTGP.ft_gp_cayley`
(k² ≡ 1) and `FTGPN.ft_gp_neg_even` (k² ≡ −1, m even): Theorem 9 in full.
-/

@[expose] public section


open Finset

namespace FTGP102
open FTGP FTGPN

/-- the three Hamiltonian cycles (as vertex lists, closing edge from the last to the first vertex) -/
def cyc0 : List (ZMod 10 × Bool) :=
  [(0, false), (9, false), (9, true), (7, true), (7, false), (8, false), (8, true), (0, true), (2, true), (2, false),
    (3, false), (4, false), (4, true), (6, true), (6, false), (5, false), (5, true), (3, true), (1, true), (1, false)]
def cyc1 : List (ZMod 10 × Bool) :=
  [(0, false), (0, true), (2, true), (4, true), (4, false), (5, false), (5, true), (7, true), (7, false), (6, false),
    (6, true), (8, true), (8, false), (9, false), (9, true), (1, true), (3, true), (3, false), (2, false), (1, false)]
def cyc2 : List (ZMod 10 × Bool) :=
  [(0, false), (0, true), (8, true), (6, true), (4, true), (2, true), (2, false), (1, false), (1, true), (9, true),
    (7, true), (5, true), (3, true), (3, false), (4, false), (5, false), (6, false), (7, false), (8, false), (9, false)]

/-- the 60 paths: cycle `i / 20`, rotated so that it starts after position `i % 20` -/
def L (i : Fin 60) : List (ZMod 10 × Bool) :=
  ((if i.val < 20 then cyc0 else if i.val < 40 then cyc1 else cyc2)).rotate (i.val % 20 + 1)

/-- a Boolean adjacency test for GP(10, 2) -/
def stepB (u v : ZMod 10 × Bool) : Bool :=
  (!u.2 && !v.2 && (v.1 == u.1 + 1 || u.1 == v.1 + 1)) || (u.2 && v.2 && (v.1 == u.1 + 2 || u.1 == v.1 + 2)) ||
    (u.1 == v.1 && u.2 != v.2)

lemma hk0 : ((2 : ℤ) : ZMod 10) ≠ 0 := by decide

lemma step_adj (u v : ZMod 10 × Bool) (h : stepB u v = true) : (gp 10 2).Adj u v := by
  obtain ⟨x, s⟩ := u
  obtain ⟨y, t⟩ := v
  have h3 : 3 ≤ 10 := by norm_num
  cases s <;> cases t <;> simp [stepB] at h
  · rcases h with rfl | rfl
    · exact adjOO h3 hk0 x
    · exact (adjOO h3 hk0 y).symm
  · subst h; exact adjOI x
  · subst h; exact (adjOI x).symm
  · rcases h with rfl | rfl
    · have := adjII (k := 2) h3 hk0 x; simpa using this
    · have := adjII (k := 2) h3 hk0 y; exact (by simpa using this : (gp 10 2).Adj (y, true) (y + 2, true)).symm

lemma chainB : ∀ i : Fin 60, List.IsChain (fun u v => stepB u v = true) (L i) := by decide

lemma chain (i : Fin 60) : List.IsChain (gp 10 2).Adj (L i) :=
  (chainB i).imp (fun u v h => step_adj u v h)

lemma L_cons : ∀ i : Fin 60, ∃ u l, L i = u :: l := by
  intro i; exact ⟨(L i).head (by fin_cases i <;> decide), (L i).tail, (List.cons_head_tail _).symm⟩

lemma nodupL : ∀ i : Fin 60, (L i).Nodup := by decide

lemma allL : ∀ i : Fin 60, ∀ x : ZMod 10 × Bool, x ∈ L i := by decide

/-- every edge kind at every position lies on exactly 38 of the 60 paths -/
lemma countL : ∀ (c : K) (x : ZMod 10), (univ.filter fun i : Fin 60 => E 10 2 c x ∈ eds (L i)).card = 38 := by
  decide

theorem ft_gp_10_2 :
    ∃ (r k' : ℕ), 0 < r ∧ 0 < k' ∧
      ∃ (a b : Fin r → ZMod 10 × Bool) (P : ∀ i, (gp 10 2).Walk (a i) (b i)),
        (∀ i, (P i).IsHamiltonian) ∧
        ∀ e ∈ (gp 10 2).edgeSet, (Finset.univ.filter fun i => e ∈ (P i).edges).card = k' := by
  choose u l hul using L_cons
  have hc : ∀ i, List.IsChain (gp 10 2).Adj (u i :: l i) := fun i => by rw [← hul]; exact chain i
  refine ⟨60, 38, by norm_num, by norm_num, u, fun i => (wk (gp 10 2) (u i) (l i) (hc i)).1,
    fun i => (wk (gp 10 2) (u i) (l i) (hc i)).2, fun i => ?_, ?_⟩
  · refine wk_ham _ _ _ _ (by rw [← hul]; exact nodupL i) (fun x => by rw [← hul]; exact allL i x)
  · intro e he
    obtain ⟨c, x, rfl⟩ := edge_cases e he
    have : ∀ i, (E 10 2 c x ∈ (wk (gp 10 2) (u i) (l i) (hc i)).2.edges) ↔ E 10 2 c x ∈ eds (L i) := by
      intro i; rw [wk_edges, ← hul]
    simp only [this]
    exact countL c x

/-- `gp m k` depends only on `±k mod m`. -/
lemma gp_neg (m : ℕ) (k k' : ℤ) (h : ((k' : ℤ) : ZMod m) = -((k : ℤ) : ZMod m)) : gp m k' = gp m k := by
  ext ⟨x, i⟩ ⟨y, j⟩
  simp only [gp, SimpleGraph.fromRel_adj, gpRel]
  cases i <;> cases j <;> simp only [h, reduceCtorEq, false_and, and_false, or_false, false_or, true_and, and_true,
    Bool.false_eq_true, ne_eq, Prod.mk.injEq, not_and]
  constructor
  · rintro ⟨h1, h2 | h2⟩
    · exact ⟨h1, Or.inr (by rw [h2]; ring)⟩
    · exact ⟨h1, Or.inl (by rw [h2]; ring)⟩
  · rintro ⟨h1, h2 | h2⟩
    · exact ⟨h1, Or.inr (by rw [h2]; ring)⟩
    · exact ⟨h1, Or.inl (by rw [h2]; ring)⟩

/-- **Theorem 9, all cases** (Frucht–Graver–Watkins: these are all vertex-transitive GP(m, k)): k² ≡ 1 (mod m);
k² ≡ −1 (mod m) with m even; m = 10 with k ≡ ±2 (mod 10). -/
theorem ft_gp_all (m : ℕ) [NeZero m] (k : ℤ) (hm : 3 ≤ m)
    (H : (m : ℤ) ∣ k * k - 1 ∨ (Even m ∧ (m : ℤ) ∣ k * k + 1) ∨
      (m = 10 ∧ (((k : ℤ) : ZMod m) = 2 ∨ ((k : ℤ) : ZMod m) = -2))) :
    ∃ (r k' : ℕ), 0 < r ∧ 0 < k' ∧
      ∃ (a b : Fin r → ZMod m × Bool) (P : ∀ i, (gp m k).Walk (a i) (b i)),
        (∀ i, (P i).IsHamiltonian) ∧
        ∀ e ∈ (gp m k).edgeSet, (Finset.univ.filter fun i => e ∈ (P i).edges).card = k' := by
  rcases H with h | ⟨he, h⟩ | ⟨rfl, h⟩
  · exact ft_gp_cayley m k hm h
  · exact ft_gp_neg_even m k hm he h
  · have hg : gp 10 k = gp 10 2 := by
      rcases h with h | h
      · exact (gp_neg 10 (-2) k (by rw [h]; push_cast; ring)).trans (gp_neg 10 2 (-2) (by push_cast; ring))
      · exact gp_neg 10 2 k (by rw [h]; push_cast; ring)
    rw [hg]; exact ft_gp_10_2

end FTGP102

#print axioms FTGP102.ft_gp_10_2
#print axioms FTGP102.ft_gp_all
