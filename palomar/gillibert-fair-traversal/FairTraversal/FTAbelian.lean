/-
Copyright 2026 Ming-Chih Kao. Licensed under the Apache License, Version 2.0;
see the LICENSE file at the root of this repository.
Ported from github.com/koolkao/gillibert-fair-traversal-abelian (v1.7.0, commit
06c3a8732759afca38331762b76113135e475ac6) to Lean v4.36.0 and the module system.
Port: `Walk.IsHamiltonian.map` now takes the graph map implicitly (`(f := …)` added).
-/
module

public import Mathlib

/-!
# Anticore ⊆ convex hull of greedy (marginal) vectors

For any set function `v` (no submodularity needed), a vector `x` supported on `R` with
`x(U) ≤ v(F ∪ U) - v(F)` for all `U ⊆ R` and equality for `U = R` is a convex combination (over `ℚ`)
of the greedy vectors `greedy v F L`, `L` an ordering of `R`. Constructive induction on `|R|`:
split at a proper tight set, or perturb along `e_i - e_j` until a proper set becomes tight.
-/

@[expose] public section


open Finset Pointwise

namespace FTAbelian

section Weber
variable {ι : Type*} [DecidableEq ι] (v : Finset ι → ℚ)

/-- Greedy (marginal) vector of `v` along the ordering `L`, starting from the placed set `F`. -/
def greedy : Finset ι → List ι → ι → ℚ
  | _, [] => 0
  | F, a :: L => Pi.single a (v (insert a F) - v F) + greedy (insert a F) L

@[simp] lemma greedy_nil (F : Finset ι) : greedy v F [] = 0 := rfl

lemma greedy_cons (F : Finset ι) (a : ι) (L : List ι) :
    greedy v F (a :: L) = Pi.single a (v (insert a F) - v F) + greedy v (insert a F) L := rfl

lemma greedy_append (F : Finset ι) (L₁ L₂ : List ι) :
    greedy v F (L₁ ++ L₂) = greedy v F L₁ + greedy v (F ∪ L₁.toFinset) L₂ := by
  induction L₁ generalizing F with
  | nil => simp
  | cons a L ih =>
    rw [List.cons_append, greedy_cons, greedy_cons, ih, add_assoc,
      show insert a F ∪ L.toFinset = F ∪ (a :: L).toFinset by
        ext; simp only [mem_union, mem_insert, List.toFinset_cons]; tauto]

/-- The greedy vectors of orderings of `R` (relative to `F`). -/
def Gset (F R : Finset ι) : Set (ι → ℚ) :=
  {y | ∃ L : List ι, L.Nodup ∧ L.toFinset = R ∧ y = greedy v F L}

/-- `x` lies in the anticore of the contracted game on `R`. -/
def Adm (F R : Finset ι) (x : ι → ℚ) : Prop :=
  (∀ j, j ∉ R → x j = 0) ∧ (∀ U ⊆ R, ∑ j ∈ U, x j ≤ v (F ∪ U) - v F) ∧
    ∑ j ∈ R, x j = v (F ∪ R) - v F

lemma split_step (R : Finset ι)
    (IH : ∀ R' : Finset ι, R'.card < R.card → ∀ F x, Adm v F R' x → x ∈ convexHull ℚ (Gset v F R'))
    (F : Finset ι) (x : ι → ℚ) (hx : Adm v F R x) (U : Finset ι) (hU : U ⊆ R) (hU0 : U.Nonempty)
    (hUR : U ≠ R) (ht : ∑ j ∈ U, x j = v (F ∪ U) - v F) :
    x ∈ convexHull ℚ (Gset v F R) := by
  obtain ⟨hsupp, hle, heq⟩ := hx
  set x₁ : ι → ℚ := fun j => if j ∈ U then x j else 0 with hx₁
  set x₂ : ι → ℚ := fun j => if j ∈ U then 0 else x j with hx₂
  have hsplit : x = x₁ + x₂ := by
    funext j; simp only [Pi.add_apply, hx₁, hx₂]; split_ifs <;> simp
  have hs₁ : ∀ W ⊆ U, ∑ j ∈ W, x₁ j = ∑ j ∈ W, x j := fun W hW =>
    sum_congr rfl fun j hj => by simp [hx₁, hW hj]
  have hs₂ : ∀ W, Disjoint W U → ∑ j ∈ W, x₂ j = ∑ j ∈ W, x j := fun W hW =>
    sum_congr rfl fun j hj => by simp [hx₂, Finset.disjoint_left.1 hW hj]
  have hA₁ : Adm v F U x₁ := by
    refine ⟨fun j hj => by simp [hx₁, hj], fun W hW => ?_, ?_⟩
    · rw [hs₁ W hW]; exact hle W (hW.trans hU)
    · rw [hs₁ U le_rfl, ht]
  have hA₂ : Adm v (F ∪ U) (R \ U) x₂ := by
    refine ⟨fun j hj => ?_, fun W hW => ?_, ?_⟩
    · by_cases hjU : j ∈ U
      · simp [hx₂, hjU]
      · simp only [hx₂, hjU, if_false]
        exact hsupp j (fun hjR => hj (mem_sdiff.2 ⟨hjR, hjU⟩))
    · have hWU : Disjoint W U := disjoint_of_subset_left hW sdiff_disjoint
      rw [hs₂ W hWU]
      have h1 := hle (U ∪ W) (union_subset hU (hW.trans sdiff_subset))
      rw [sum_union hWU.symm, ht, ← union_assoc] at h1
      linarith
    · have hWU : Disjoint (R \ U) U := sdiff_disjoint
      rw [hs₂ _ hWU]
      have h1 := heq
      rw [← union_sdiff_of_subset hU, sum_union hWU.symm, ht, ← union_assoc] at h1
      linarith
  have hc₁ : U.card < R.card := card_lt_card (Finset.ssubset_iff_subset_ne.2 ⟨hU, hUR⟩)
  have hc₂ : (R \ U).card < R.card := by
    rw [card_sdiff_of_subset hU]
    have := hU0.card_pos
    have := card_le_card hU
    omega
  have h₁ := IH U hc₁ F x₁ hA₁
  have h₂ := IH (R \ U) hc₂ (F ∪ U) x₂ hA₂
  have hmem : x ∈ convexHull ℚ (Gset v F U + Gset v (F ∪ U) (R \ U)) := by
    rw [convexHull_add, hsplit]; exact Set.add_mem_add h₁ h₂
  refine convexHull_mono ?_ hmem
  rintro y ⟨y₁, ⟨L₁, hn₁, hL₁, rfl⟩, y₂, ⟨L₂, hn₂, hL₂, rfl⟩, rfl⟩
  refine ⟨L₁ ++ L₂, ?_, ?_, ?_⟩
  · refine List.nodup_append.2 ⟨hn₁, hn₂, ?_⟩
    intro a ha b hb hab
    subst hab
    have h1 : a ∈ U := by rw [← hL₁]; exact List.mem_toFinset.2 ha
    have h2 : a ∈ R \ U := by rw [← hL₂]; exact List.mem_toFinset.2 hb
    exact (mem_sdiff.1 h2).2 h1
  · rw [List.toFinset_append, hL₁, hL₂, union_sdiff_of_subset hU]
  · rw [greedy_append, hL₁]

/-- slack of a set -/
def slack (F : Finset ι) (x : ι → ℚ) (U : Finset ι) : ℚ := v (F ∪ U) - v F - ∑ j ∈ U, x j

/-- `e_i - e_j` -/
def dlt (i j : ι) : ι → ℚ := fun k => (if k = i then 1 else 0) - (if k = j then 1 else 0)

lemma sum_dlt (i j : ι) (U : Finset ι) :
    ∑ k ∈ U, dlt i j k = (if i ∈ U then 1 else 0) - (if j ∈ U then 1 else 0) := by
  simp [dlt, sum_sub_distrib, sum_ite_eq']

lemma perturb (R : Finset ι)
    (IH : ∀ R' : Finset ι, R'.card < R.card → ∀ F x, Adm v F R' x → x ∈ convexHull ℚ (Gset v F R'))
    (F : Finset ι) (x : ι → ℚ) (hx : Adm v F R x)
    (hnt : ∀ U ⊆ R, U.Nonempty → U ≠ R → ∑ j ∈ U, x j < v (F ∪ U) - v F)
    (i j : ι) (hi : i ∈ R) (hj : j ∈ R) (hij : i ≠ j) :
    ∃ ε : ℚ, 0 < ε ∧ x + ε • dlt i j ∈ convexHull ℚ (Gset v F R) := by
  obtain ⟨hsupp, hle, heq⟩ := hx
  set P := R.powerset.filter (fun U => i ∈ U ∧ j ∉ U) with hP
  have hPne : (P.image (slack v F x)).Nonempty := by
    refine (Finset.Nonempty.image ⟨{i}, ?_⟩ _)
    simp [hP, hi, Ne.symm hij]
  set ε := (P.image (slack v F x)).min' hPne with hε
  obtain ⟨U₀, hU₀P, hU₀ε⟩ := Finset.mem_image.1 (min'_mem _ hPne)
  have hU₀ : U₀ ⊆ R ∧ i ∈ U₀ ∧ j ∉ U₀ := by
    simp only [hP, mem_filter, mem_powerset] at hU₀P; exact ⟨hU₀P.1, hU₀P.2⟩
  have hεle : ∀ U ∈ P, ε ≤ slack v F x U := fun U hU =>
    min'_le _ _ (mem_image_of_mem _ hU)
  have hpos : ∀ U ∈ P, 0 < slack v F x U := by
    intro U hU
    simp only [hP, mem_filter, mem_powerset] at hU
    have := hnt U hU.1 ⟨i, hU.2.1⟩ (fun h => hU.2.2 (h ▸ hj))
    simp only [slack]; linarith
  have hεpos : 0 < ε := by
    have h := hpos U₀ hU₀P; rw [hU₀ε] at h; exact h
  refine ⟨ε, hεpos, ?_⟩
  set x' := x + ε • dlt i j with hx'
  have hsum' : ∀ U : Finset ι, ∑ k ∈ U, x' k =
      ∑ k ∈ U, x k + ε * ((if i ∈ U then 1 else 0) - (if j ∈ U then 1 else 0)) := by
    intro U
    simp only [hx', Pi.add_apply, Pi.smul_apply, smul_eq_mul, sum_add_distrib, ← mul_sum, sum_dlt]
  have hA' : Adm v F R x' := by
    refine ⟨fun k hk => ?_, fun U hU => ?_, ?_⟩
    · simp only [hx', Pi.add_apply, Pi.smul_apply, smul_eq_mul, dlt, hsupp k hk]
      have h1 : k ≠ i := fun h => hk (h ▸ hi)
      have h2 : k ≠ j := fun h => hk (h ▸ hj)
      simp [h1, h2]
    · rw [hsum']
      by_cases h1 : i ∈ U
      · by_cases h2 : j ∈ U
        · simp only [h1, h2, if_true, sub_self, mul_zero, add_zero]; exact hle U hU
        · have : U ∈ P := by simp [hP, hU, h1, h2]
          have := hεle U this
          simp only [slack] at this
          simp only [h1, h2, if_true, if_false, sub_zero, mul_one]; linarith
      · by_cases h2 : j ∈ U
        · simp only [h1, h2, if_true, if_false, zero_sub, mul_neg, mul_one]
          linarith [hle U hU]
        · simp only [h1, h2, if_false, sub_self, mul_zero, add_zero]; exact hle U hU
    · rw [hsum']; simp [hi, hj, heq]
  apply split_step v R IH F x' hA' U₀ hU₀.1 ⟨i, hU₀.2.1⟩ (fun h => hU₀.2.2 (h ▸ hj))
  rw [hsum']
  have : slack v F x U₀ = ε := hU₀ε
  simp only [slack] at this
  simp only [hU₀.2.1, hU₀.2.2, if_true, if_false, sub_zero, mul_one]
  linarith

theorem weber : ∀ (n : ℕ) (R : Finset ι), R.card = n → ∀ (F : Finset ι) (x : ι → ℚ),
    Adm v F R x → x ∈ convexHull ℚ (Gset v F R) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ihn =>
  intro R hR F x hx
  have IH : ∀ R' : Finset ι, R'.card < R.card → ∀ F x, Adm v F R' x →
      x ∈ convexHull ℚ (Gset v F R') := fun R' h F x hx => ihn R'.card (hR ▸ h) R' rfl F x hx
  rcases Nat.lt_or_ge R.card 2 with hlt | hge
  · -- |R| ≤ 1
    apply subset_convexHull
    rcases Nat.lt_or_ge R.card 1 with h0 | h1
    · have hR0 : R = ∅ := card_eq_zero.1 (by omega : R.card = 0)
      refine ⟨[], List.nodup_nil, by simp [hR0], ?_⟩
      funext k; simp [hx.1 k (by simp [hR0])]
    · obtain ⟨a, ha⟩ := card_eq_one.1 (by omega : R.card = 1)
      refine ⟨[a], List.nodup_singleton a, by simp [ha], ?_⟩
      have h3 := hx.2.2
      simp only [ha, sum_singleton] at h3
      funext k
      simp only [greedy_cons, greedy_nil, add_zero]
      by_cases hk : k = a
      · subst hk; simp [h3, union_comm, ← insert_eq]
      · simp [Pi.single_apply, hk, hx.1 k (by simp [ha, hk])]
  · by_cases hT : ∃ U ⊆ R, U.Nonempty ∧ U ≠ R ∧ ∑ j ∈ U, x j = v (F ∪ U) - v F
    · obtain ⟨U, hU, hU0, hUR, ht⟩ := hT
      exact split_step v R IH F x hx U hU hU0 hUR ht
    · push Not at hT
      have hnt : ∀ U ⊆ R, U.Nonempty → U ≠ R → ∑ j ∈ U, x j < v (F ∪ U) - v F :=
        fun U hU h0 h1 => lt_of_le_of_ne (hx.2.1 U hU) (hT U hU h0 h1)
      obtain ⟨i, hi, j, hj, hij⟩ := one_lt_card.1 (by omega : 1 < R.card)
      obtain ⟨ε₁, hε₁, h₁⟩ := perturb v R IH F x hx hnt i j hi hj hij
      obtain ⟨ε₂, hε₂, h₂⟩ := perturb v R IH F x hx hnt j i hj hi hij.symm
      have hconv := convex_convexHull ℚ (Gset v F R) h₁ h₂
        (div_nonneg hε₂.le (by linarith) : 0 ≤ ε₂ / (ε₁ + ε₂))
        (div_nonneg hε₁.le (by linarith) : 0 ≤ ε₁ / (ε₁ + ε₂))
        (by field_simp; ring)
      convert hconv using 1
      funext k
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, dlt]
      field_simp
      split_ifs <;> ring

end Weber

end FTAbelian

/-!
# Snake paths in Cayley graphs of finite abelian groups

A path is a start vertex plus a list of steps. `verts a ds` lists its vertices. The snake of `ds`
along `s` concatenates `r` translated copies of the path, alternately reversed, joined by `s`-steps.
-/

namespace FTAbelian

section Snake
variable {A : Type} [AddCommGroup A] [DecidableEq A]

/-- vertices of the path starting at `a` with steps `ds` -/
def verts : A → List A → List A
  | a, [] => [a]
  | a, d :: ds => a :: verts (a + d) ds

@[simp] lemma verts_nil (a : A) : verts a [] = [a] := rfl
@[simp] lemma verts_cons (a d : A) (ds : List A) : verts a (d :: ds) = a :: verts (a + d) ds := rfl

lemma verts_add (a c : A) (ds : List A) : verts (a + c) ds = (verts a ds).map (· + c) := by
  induction ds generalizing a with
  | nil => simp
  | cons d ds ih =>
    simp only [verts_cons, List.map_cons]
    rw [add_right_comm, ih]

lemma verts_shift (c : A) (ds : List A) : verts c ds = (verts 0 ds).map (· + c) := by
  simpa using verts_add 0 c ds

lemma verts_append (a s : A) (ds₁ ds₂ : List A) :
    verts a (ds₁ ++ s :: ds₂) = verts a ds₁ ++ verts (a + ds₁.sum + s) ds₂ := by
  induction ds₁ generalizing a with
  | nil => simp
  | cons d ds ih => simp [ih, add_assoc]

/-- reversed step list -/
def rev (ds : List A) : List A := (ds.map (fun x => -x)).reverse

lemma rev_cons (d : A) (ds : List A) : rev (d :: ds) = rev ds ++ [-d] := by
  simp [rev]

lemma sum_rev (ds : List A) : (rev ds).sum = -ds.sum := by
  induction ds with
  | nil => simp [rev]
  | cons d ds ih => rw [rev_cons, List.sum_append, ih]; simp [add_comm]

lemma verts_rev (a : A) (ds : List A) : verts (a + ds.sum) (rev ds) = (verts a ds).reverse := by
  induction ds generalizing a with
  | nil => simp [rev]
  | cons d ds ih =>
    rw [rev_cons, show (rev ds ++ [-d]) = rev ds ++ (-d) :: [] from rfl, verts_append, verts_nil,
      List.sum_cons, ← add_assoc, ih, sum_rev, verts_cons, List.reverse_cons]
    congr 2
    abel

/-- the snake with `t + 1` blocks -/
def snk (ds : List A) (s : A) : ℕ → List A
  | 0 => ds
  | t + 1 => snk ds s t ++ s :: (if Even (t + 1) then ds else rev ds)

lemma sum_snk (ds : List A) (s : A) (t : ℕ) :
    (snk ds s t).sum = (if Even t then ds.sum else 0) + t • s := by
  induction t with
  | zero => simp [snk]
  | succ t ih =>
    rw [snk, List.sum_append, ih, List.sum_cons]
    by_cases ht : Even t
    · have : ¬ Even (t + 1) := by rw [Nat.even_add_one]; exact not_not.2 ht
      simp only [ht, this, if_true, if_false, sum_rev, succ_nsmul]; abel
    · have : Even (t + 1) := by rw [Nat.even_add_one]; exact ht
      simp only [ht, this, if_true, if_false, succ_nsmul]; abel

/-- block `i` of the snake (as vertices) -/
def blk (V : List A) (s : A) (i : ℕ) : List A :=
  (if Even i then V else V.reverse).map (· + i • s)

lemma verts_snk (ds : List A) (s : A) (t : ℕ) :
    verts 0 (snk ds s t) = (List.range (t + 1)).flatMap (blk (verts 0 ds) s) := by
  induction t with
  | zero => simp [snk, blk]
  | succ t ih =>
    rw [snk, verts_append, ih, sum_snk,
      show List.range (t + 1 + 1) = List.range (t + 1) ++ [t + 1] from List.range_succ,
      List.flatMap_append]
    congr 1
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, blk]
    have key := verts_rev (0 : A) ds
    rw [zero_add] at key
    by_cases ht : Even t
    · have h1 : ¬ Even (t + 1) := by rw [Nat.even_add_one]; exact not_not.2 ht
      simp only [ht, h1, if_true, if_false]
      rw [show (0 : A) + (ds.sum + t • s) + s = ds.sum + (t + 1) • s by rw [succ_nsmul]; abel,
        verts_add, key]
    · have h1 : Even (t + 1) := by rw [Nat.even_add_one]; exact ht
      simp only [ht, h1, if_true, if_false]
      rw [show (0 : A) + (0 + t • s) + s = (t + 1) • s by rw [succ_nsmul]; abel,
        verts_shift ((t + 1) • s) ds]

/-- paired step count -/
def pc (d : A) (ds : List A) : ℕ := ds.count d + ds.count (-d)

lemma count_rev (d : A) (ds : List A) : (rev ds).count d = ds.count (-d) := by
  rw [rev, List.count_reverse]
  have := List.count_map_of_injective ds (fun x : A => -x) neg_injective (-d)
  simpa using this

lemma pc_rev (d : A) (ds : List A) : pc d (rev ds) = pc d ds := by
  simp [pc, count_rev, add_comm]

lemma pc_snk (d : A) (ds : List A) (s : A) (t : ℕ) :
    pc d (snk ds s t) = (t + 1) * pc d ds +
      t * ((if s = d then 1 else 0) + (if s = -d then 1 else 0)) := by
  induction t with
  | zero => simp [snk]
  | succ t ih =>
    have hb : pc d (if Even (t + 1) then ds else rev ds) = pc d ds := by
      split_ifs
      · rfl
      · exact pc_rev d ds
    have : pc d (snk ds s t ++ s :: (if Even (t + 1) then ds else rev ds)) =
        pc d (snk ds s t) + pc d (if Even (t + 1) then ds else rev ds) +
          ((if s = d then 1 else 0) + (if s = -d then 1 else 0)) := by
      simp only [pc, List.count_append, List.count_cons, beq_iff_eq]
      split_ifs <;> omega
    rw [snk, this, ih, hb]
    ring

omit [DecidableEq A] in
lemma mem_snk (S : Finset A) (hneg : ∀ x ∈ S, -x ∈ S) (ds : List A) (hds : ∀ x ∈ ds, x ∈ S)
    (s : A) (hs : s ∈ S) (t : ℕ) : ∀ x ∈ snk ds s t, x ∈ S := by
  induction t with
  | zero => simpa [snk] using hds
  | succ t ih =>
    intro x hx
    simp only [snk, List.mem_append, List.mem_cons] at hx
    rcases hx with hx | rfl | hx
    · exact ih x hx
    · exact hs
    · split_ifs at hx
      · exact hds x hx
      · simp only [rev, List.mem_reverse, List.mem_map] at hx
        obtain ⟨y, hy, rfl⟩ := hx
        exact hneg y (hds y hy)

end Snake

end FTAbelian

namespace FTAbelian

section Graph
variable {A : Type} [AddCommGroup A] [Fintype A] [DecidableEq A]
  (S : Finset A) (G : SimpleGraph A) (hG : ∀ a b, G.Adj a b ↔ b - a ∈ S)

include hG in
lemma neg_mem_of : ∀ x ∈ S, -x ∈ S := by
  intro x hx
  have h1 : G.Adj 0 x := (hG 0 x).2 (by simpa using hx)
  simpa using (hG x 0).1 h1.symm

include hG in
lemma zero_not_mem_of : (0 : A) ∉ S := by
  intro h
  exact G.irrefl ((hG 0 0).2 (by simpa using h))

/-- the walk with start `a` and steps `ds` -/
def walkOf : (a : A) → (ds : List A) → (∀ x ∈ ds, x ∈ S) → Σ b, G.Walk a b
  | a, [], _ => ⟨a, SimpleGraph.Walk.nil⟩
  | a, d :: ds, h =>
    ⟨(walkOf (a + d) ds (fun x hx => h x (List.mem_cons_of_mem d hx))).1,
      SimpleGraph.Walk.cons ((hG a (a + d)).2 (by simpa using h d (by simp)))
        (walkOf (a + d) ds (fun x hx => h x (List.mem_cons_of_mem d hx))).2⟩

/-- edges of that walk -/
def edgesL : A → List A → List (Sym2 A)
  | _, [] => []
  | a, d :: ds => s(a, a + d) :: edgesL (a + d) ds

lemma walkOf_support (a : A) (ds : List A) (h : ∀ x ∈ ds, x ∈ S) :
    (walkOf S G hG a ds h).2.support = verts a ds := by
  induction ds generalizing a with
  | nil => rfl
  | cons d ds ih => simp [walkOf, ih]

lemma walkOf_edges (a : A) (ds : List A) (h : ∀ x ∈ ds, x ∈ S) :
    (walkOf S G hG a ds h).2.edges = edgesL a ds := by
  induction ds generalizing a with
  | nil => rfl
  | cons d ds ih => simp [walkOf, edgesL, ih]

lemma ind_sym2 (u s d c : A) (hs : s ≠ 0) :
    (if s(c, c + d) = s(u, u + s) then 1 else 0 : ℕ) =
      (if c = u ∧ d = s then 1 else 0) + (if c = u + s ∧ d = -s then 1 else 0) := by
  classical
  by_cases h1 : c = u ∧ d = s
  · have h2 : ¬ (c = u + s ∧ d = -s) := by
      rintro ⟨h3, -⟩
      apply hs
      have h4 : u = u + s := h1.1 ▸ h3
      simpa using h4
    rw [if_pos h1, if_neg h2, if_pos (by rw [h1.1, h1.2])]
  · by_cases h2 : c = u + s ∧ d = -s
    · rw [if_neg h1, if_pos h2, if_pos]
      rw [h2.1, h2.2, add_neg_cancel_right, Sym2.eq_swap]
    · rw [if_neg h1, if_neg h2, if_neg]
      rw [Sym2.eq_iff]
      rintro (⟨h3, h4⟩ | ⟨h3, h4⟩)
      · apply h1
        refine ⟨h3, ?_⟩
        rw [h3] at h4
        exact add_left_cancel h4
      · apply h2
        refine ⟨h3, ?_⟩
        rw [h3] at h4
        rw [eq_neg_iff_add_eq_zero]
        calc d + s = (u + s + d) - u := by abel
          _ = 0 := by rw [h4, sub_self]

lemma sum_count_edgesL (u s : A) (hs : s ≠ 0) (ds : List A) :
    ∑ c : A, (edgesL c ds).count s(u, u + s) = pc s ds := by
  induction ds with
  | nil => simp [edgesL, pc]
  | cons d ds ih =>
    have h1 : ∑ c : A, (edgesL (c + d) ds).count s(u, u + s) =
        ∑ c : A, (edgesL c ds).count s(u, u + s) :=
      Fintype.sum_equiv (Equiv.addRight d) (fun c => (edgesL (c + d) ds).count s(u, u + s))
        (fun c => (edgesL c ds).count s(u, u + s)) (fun c => rfl)
    have h2 : ∑ c : A, (if s(c, c + d) = s(u, u + s) then 1 else 0 : ℕ) =
        (if d = s then 1 else 0) + (if d = -s then 1 else 0) := by
      rw [Finset.sum_congr rfl (fun c _ => ind_sym2 u s d c hs), Finset.sum_add_distrib]
      congr 1
      · by_cases hd : d = s <;> simp [hd]
      · by_cases hd : d = -s <;> simp [hd]
    simp only [edgesL, List.count_cons, beq_iff_eq, Finset.sum_add_distrib, h1, ih, h2]
    simp only [pc, List.count_cons, beq_iff_eq]
    omega

/-- the game: `v(T) = n - n/|⟨T⟩|` -/
noncomputable def vfun (T : Finset A) : ℚ :=
  (Fintype.card A : ℚ) - Fintype.card A / (Nat.card (AddSubgroup.closure (T : Set A)) : ℚ)

/-- invariant of the snake construction -/
def Inv (T : Finset A) (ds : List A) (γ : A → ℚ) : Prop :=
  (∀ x ∈ ds, x ∈ S) ∧ (verts 0 ds).Nodup ∧
    (∀ a, a ∈ verts 0 ds ↔ a ∈ AddSubgroup.closure (T : Set A)) ∧
    ∀ d, (pc d ds : ℚ) * Fintype.card A = (verts 0 ds).length * (γ d + γ (-d))

omit [DecidableEq A] in
lemma card_of_list (H : AddSubgroup A) (l : List A) (hl : l.Nodup) (hm : ∀ a, a ∈ l ↔ a ∈ H) :
    Nat.card H = l.length := by
  classical
  rw [← List.toFinset_card_of_nodup hl]
  have e : H ≃ (l.toFinset : Set A) :=
    Equiv.subtypeEquivRight (fun a => by simp [hm])
  rw [Nat.card_congr e, Nat.card_coe_set_eq, Set.ncard_coe_finset]

omit [DecidableEq A] in
lemma card_le_of_subset (H : AddSubgroup A) (F : Finset A) (hF : ∀ a ∈ F, a ∈ H) :
    F.card ≤ Nat.card H := by
  have h1 : Nat.card (F : Set A) = F.card := by rw [Nat.card_coe_set_eq, Set.ncard_coe_finset]
  rw [← h1]
  exact Nat.card_le_card_of_injective (fun a : (F : Set A) => (⟨a.1, hF a.1 a.2⟩ : H))
    (fun a b h => Subtype.ext (by simpa using congrArg Subtype.val h))

include hG in
lemma inv_step (T : Finset A) (ds : List A) (γ : A → ℚ) (hI : Inv S T ds γ) (s : A)
    (hs : s ∈ S) :
    ∃ ds', Inv S (insert s T) ds' (γ + Pi.single s (vfun (insert s T) - vfun T)) := by
  obtain ⟨hst, hnd, hmem, hcnt⟩ := hI
  obtain ⟨H, hH⟩ : ∃ H, H = AddSubgroup.closure (T : Set A) := ⟨_, rfl⟩
  obtain ⟨K, hK⟩ : ∃ K, K = AddSubgroup.closure (insert s (T : Set A)) := ⟨_, rfl⟩
  obtain ⟨V, hV⟩ : ∃ V, V = verts 0 ds := ⟨_, rfl⟩
  rw [← hV] at hnd hmem hcnt
  rw [← hH] at hmem
  obtain ⟨r, hr⟩ : ∃ r, r = addOrderOf ((s : A ⧸ H)) := ⟨_, rfl⟩
  have hr0 : 0 < r := hr ▸ addOrderOf_pos _
  have hsmulH : ∀ m : ℕ, m • s ∈ H ↔ r ∣ m := by
    intro m
    rw [hr, addOrderOf_dvd_iff_nsmul_eq_zero, ← QuotientAddGroup.mk_nsmul,
      QuotientAddGroup.eq_zero_iff]
  have hHK : H ≤ K := by rw [hH, hK]; exact AddSubgroup.closure_mono (Set.subset_insert _ _)
  have hsK : s ∈ K := by rw [hK]; exact AddSubgroup.subset_closure (Set.mem_insert _ _)
  have hv : verts 0 (snk ds s (r - 1)) = (List.range r).flatMap (blk V s) := by
    rw [verts_snk, Nat.sub_add_cancel hr0, hV]
  have hmemblk : ∀ i a, a ∈ blk V s i ↔ ∃ h ∈ V, a = h + i • s := by
    intro i a
    simp only [blk]
    split_ifs <;> simp [List.mem_map, eq_comm]
  have hnd' : (verts 0 (snk ds s (r - 1))).Nodup := by
    rw [hv, List.nodup_flatMap]
    refine ⟨fun i _ => ?_, ?_⟩
    · simp only [blk]
      split_ifs
      · exact hnd.map (add_left_injective _)
      · exact (List.nodup_reverse.2 hnd).map (add_left_injective _)
    · refine (List.pairwise_lt_range (n := r)).imp_of_mem ?_
      intro i j _ hj hij
      rw [Function.onFun, List.disjoint_left]
      intro a ha hb
      obtain ⟨h1, hh1, rfl⟩ := (hmemblk i a).1 ha
      obtain ⟨h2, hh2, he⟩ := (hmemblk j _).1 hb
      have hj' : j < r := List.mem_range.1 hj
      obtain ⟨k, rfl⟩ : ∃ k, j = i + k := ⟨j - i, by omega⟩
      have hk : k • s ∈ H := by
        rw [add_nsmul] at he
        have : k • s = h1 - h2 := by
          calc k • s = (h2 + (i • s + k • s)) - h2 - i • s := by abel
            _ = (h1 + i • s) - h2 - i • s := by rw [he]
            _ = h1 - h2 := by abel
        rw [this]
        exact H.sub_mem ((hmem h1).1 hh1) ((hmem h2).1 hh2)
      have hdvd := (hsmulH k).1 hk
      have hkpos : 0 < k := by omega
      have := Nat.le_of_dvd hkpos hdvd
      omega
  have hmem' : ∀ a, a ∈ verts 0 (snk ds s (r - 1)) ↔ a ∈ K := by
    intro a
    rw [hv, List.mem_flatMap]
    constructor
    · rintro ⟨i, -, ha⟩
      obtain ⟨h, hh, rfl⟩ := (hmemblk i a).1 ha
      exact K.add_mem (hHK ((hmem h).1 hh)) (K.nsmul_mem hsK i)
    · intro ha
      have hKle : K ≤ (AddSubgroup.zmultiples ((s : A ⧸ H))).comap (QuotientAddGroup.mk' H) := by
        rw [hK, AddSubgroup.closure_le]
        intro x hx
        rcases hx with rfl | hx
        · exact AddSubgroup.mem_zmultiples _
        · simp only [SetLike.mem_coe, AddSubgroup.mem_comap, QuotientAddGroup.mk'_apply]
          rw [(QuotientAddGroup.eq_zero_iff x).2 (hH ▸ AddSubgroup.subset_closure hx)]
          exact zero_mem _
      have h1 := hKle ha
      rw [AddSubgroup.mem_comap, QuotientAddGroup.mk'_apply, AddSubgroup.mem_zmultiples_iff] at h1
      obtain ⟨m, hm⟩ := h1
      have hm0 : 0 ≤ m % (r : ℤ) := Int.emod_nonneg m (by exact_mod_cast hr0.ne')
      have hm1 : m % (r : ℤ) < r := Int.emod_lt_of_pos m (by exact_mod_cast hr0)
      obtain ⟨i, hi⟩ : ∃ i : ℕ, (i : ℤ) = m % (r : ℤ) := ⟨_, Int.toNat_of_nonneg hm0⟩
      have hir : i < r := by omega
      have hq : ((a - i • s : A) : A ⧸ H) = 0 := by
        rw [QuotientAddGroup.mk_sub, QuotientAddGroup.mk_nsmul, ← natCast_zsmul, hi, hr,
          mod_addOrderOf_zsmul, hm, sub_self]
      exact ⟨i, List.mem_range.2 hir,
        (hmemblk i a).2 ⟨a - i • s, (hmem _).2 ((QuotientAddGroup.eq_zero_iff _).1 hq), by abel⟩⟩
  have hlen : (verts 0 (snk ds s (r - 1))).length = r * V.length := by
    rw [hv, List.length_flatMap]
    have : ∀ i, (blk V s i).length = V.length := by
      intro i; simp only [blk]; split_ifs <;> simp
    simp only [this, List.map_const', List.length_range, List.sum_replicate, smul_eq_mul]
  have hcH : (Nat.card H : ℚ) = V.length := by exact_mod_cast card_of_list H V hnd hmem
  have hcK : (Nat.card K : ℚ) = r * V.length := by
    have : Nat.card K = r * V.length := by rw [card_of_list K _ hnd' hmem', hlen]
    exact_mod_cast this
  have hvK : vfun (insert s T) = (Fintype.card A : ℚ) - Fintype.card A / (r * V.length) := by
    rw [vfun, Finset.coe_insert, ← hK, hcK]
  have hvH : vfun T = (Fintype.card A : ℚ) - Fintype.card A / V.length := by
    rw [vfun, ← hH, hcH]
  refine ⟨snk ds s (r - 1), mem_snk S (neg_mem_of S G hG) ds hst s hs (r - 1), hnd',
    fun a => by rw [hmem', hK, Finset.coe_insert], ?_⟩
  intro d
  have hpc := pc_snk d ds s (r - 1)
  rw [Nat.sub_add_cancel hr0] at hpc
  have hc := hcnt d
  have hL : (0 : ℚ) < V.length := by
    have : (0 : A) ∈ V := by rw [hV]; cases ds <;> simp
    exact_mod_cast List.length_pos_of_mem this
  have hrq : (0 : ℚ) < r := by exact_mod_cast hr0
  rw [hpc, hlen, hvK, hvH]
  simp only [Pi.add_apply, Pi.single_apply]
  have hi1 : (if s = d then (1 : ℚ) else 0) = if d = s then 1 else 0 := by
    by_cases h : d = s
    · simp [h]
    · simp [h, Ne.symm h]
  have hi2 : (if s = -d then (1 : ℚ) else 0) = if -d = s then 1 else 0 := by
    by_cases h : -d = s
    · simp [h]
    · simp [h, Ne.symm h]
  push_cast [Nat.cast_sub (Nat.one_le_iff_ne_zero.2 hr0.ne')]
  have hcc : (r : ℚ) * V.length * ((Fintype.card A : ℚ) - Fintype.card A / (r * V.length) -
      ((Fintype.card A : ℚ) - Fintype.card A / V.length)) = r * Fintype.card A - Fintype.card A := by
    field_simp
    ring
  generalize ((Fintype.card A : ℚ) - Fintype.card A / (r * V.length) -
      ((Fintype.card A : ℚ) - Fintype.card A / V.length)) = c at hcc ⊢
  rw [hi1, hi2]
  have hs1 : (if d = s then c else 0) = c * (if d = s then 1 else 0) := by split_ifs <;> ring
  have hs2 : (if -d = s then c else 0) = c * (if -d = s then 1 else 0) := by split_ifs <;> ring
  rw [hs1, hs2]
  generalize (if d = s then (1 : ℚ) else 0) = I1
  generalize (if -d = s then (1 : ℚ) else 0) = I2
  linear_combination (r : ℚ) * hc - (I1 + I2) * hcc

include hG in
lemma inv_list (L : List A) (hL : ∀ x ∈ L, x ∈ S) : ∀ (T : Finset A) (ds : List A) (γ : A → ℚ),
    Inv S T ds γ → ∃ ds', Inv S (T ∪ L.toFinset) ds' (γ + greedy vfun T L) := by
  induction L with
  | nil => intro T ds γ h; exact ⟨ds, by simpa using h⟩
  | cons a L ih =>
    intro T ds γ h
    obtain ⟨ds1, h1⟩ := inv_step S G hG T ds γ h a (hL a (by simp))
    obtain ⟨ds2, h2⟩ := ih (fun x hx => hL x (by simp [hx])) (insert a T) ds1 _ h1
    refine ⟨ds2, ?_⟩
    rw [greedy_cons, ← add_assoc,
      show T ∪ (a :: L).toFinset = insert a T ∪ L.toFinset by
        ext; simp only [Finset.mem_union, Finset.mem_insert, List.toFinset_cons]; tauto]
    exact h2

lemma inv_init : Inv S ∅ [] 0 := by
  refine ⟨by simp, by simp, fun a => ?_, fun d => by simp [pc]⟩
  simp [AddSubgroup.closure_empty, AddSubgroup.mem_bot, eq_comm]

omit [DecidableEq A] in
lemma S_nonempty (hgen : AddSubgroup.closure (S : Set A) = ⊤) (hn : 2 ≤ Fintype.card A) :
    S.Nonempty := by
  have : Nontrivial A := Fintype.one_lt_card_iff_nontrivial.1 (by omega)
  obtain ⟨a, ha⟩ := exists_ne (0 : A)
  by_contra hS
  rw [Finset.not_nonempty_iff_eq_empty] at hS
  have h1 : a ∈ AddSubgroup.closure (S : Set A) := by rw [hgen]; exact AddSubgroup.mem_top a
  rw [hS, Finset.coe_empty, AddSubgroup.closure_empty, AddSubgroup.mem_bot] at h1
  exact ha h1

include hG in
lemma adm_x (hgen : AddSubgroup.closure (S : Set A) = ⊤) (hn : 2 ≤ Fintype.card A) :
    Adm vfun ∅ S (fun s => if s ∈ S then ((Fintype.card A : ℚ) - 1) / S.card else 0) := by
  have hv0 : vfun (∅ : Finset A) = 0 := by
    simp [vfun, AddSubgroup.closure_empty, AddSubgroup.card_bot]
  have hσ : (0 : ℚ) < S.card := by exact_mod_cast (S_nonempty S hgen hn).card_pos
  have hn' : (2 : ℚ) ≤ Fintype.card A := by exact_mod_cast hn
  refine ⟨fun j hj => by simp [hj], fun U hU => ?_, ?_⟩
  · rw [Finset.empty_union, hv0, sub_zero,
      Finset.sum_congr rfl (fun j hj => if_pos (hU hj)), Finset.sum_const, nsmul_eq_mul]
    by_cases htop : AddSubgroup.closure (U : Set A) = ⊤
    · have hvU : vfun U = (Fintype.card A : ℚ) - 1 := by
        rw [vfun, htop, AddSubgroup.card_top, Nat.card_eq_fintype_card]
        have : (Fintype.card A : ℚ) ≠ 0 := by positivity
        field_simp
      rw [hvU]
      have hUS : (U.card : ℚ) ≤ S.card := by exact_mod_cast Finset.card_le_card hU
      rw [mul_div_assoc', div_le_iff₀ hσ]
      nlinarith
    · have hUS : U.card + 1 ≤ S.card := by
        have hne : U ≠ S := fun h => htop (h ▸ hgen)
        have := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.2 ⟨hU, hne⟩)
        omega
      have hUh : U.card + 1 ≤ Nat.card (AddSubgroup.closure (U : Set A)) := by
        have h0U : (0 : A) ∉ U := fun h => zero_not_mem_of S G hG (hU h)
        have := card_le_of_subset (AddSubgroup.closure (U : Set A)) (insert 0 U) (by
          intro a ha
          rcases Finset.mem_insert.1 ha with rfl | ha
          · exact zero_mem _
          · exact AddSubgroup.subset_closure ha)
        rwa [Finset.card_insert_of_notMem h0U] at this
      rw [vfun]
      generalize Nat.card (AddSubgroup.closure (U : Set A)) = h at hUh
      have hσ' : (U.card : ℚ) + 1 ≤ S.card := by exact_mod_cast hUS
      have hh' : (U.card : ℚ) + 1 ≤ h := by exact_mod_cast hUh
      have hu : (0 : ℚ) ≤ U.card := by positivity
      have hh : (0 : ℚ) < h := by linarith
      rw [show (Fintype.card A : ℚ) - Fintype.card A / h = Fintype.card A * (h - 1) / h by
        field_simp, mul_div_assoc', div_le_div_iff₀ hσ hh]
      nlinarith [mul_le_mul_of_nonneg_left hσ'
          (by nlinarith : (0 : ℚ) ≤ Fintype.card A * (h - 1)),
        mul_nonneg hu hh.le,
        mul_nonneg (by linarith : (0 : ℚ) ≤ Fintype.card A) (by linarith : (0 : ℚ) ≤ h - U.card - 1)]
  · rw [Finset.empty_union, hv0, sub_zero, Finset.sum_congr rfl (fun j hj => if_pos hj),
      Finset.sum_const, nsmul_eq_mul, vfun, hgen, AddSubgroup.card_top, Nat.card_eq_fintype_card]
    have : (Fintype.card A : ℚ) ≠ 0 := by positivity
    field_simp

include hG in
/-- **Fair Traversal for Cayley graphs of finite abelian groups.** If `G` is the Cayley graph
`a ~ b ↔ b - a ∈ S` of a finite abelian group `A` with generating set `S` and `|A| ≥ 2`, then
there is a nonempty finite family of Hamiltonian paths covering every edge exactly `k ≥ 1` times.
The conclusion is literally that of `OMA.S_gillibert_fair_traversal.main`. -/
theorem fair_traversal_cayley (hgen : AddSubgroup.closure (S : Set A) = ⊤)
    (hn : 2 ≤ Fintype.card A) :
    ∃ (r k : ℕ), 0 < r ∧ 0 < k ∧
      ∃ (a b : Fin r → A) (P : ∀ i, G.Walk (a i) (b i)),
        (∀ i, (P i).IsHamiltonian) ∧
        ∀ e ∈ G.edgeSet, (Finset.univ.filter fun i => e ∈ (P i).edges).card = k := by
  classical
  have hx := weber vfun S.card S rfl ∅ _ (adm_x S G hG hgen hn)
  obtain ⟨ι, hιf, w, z, hw0, hw1, hz, hsum⟩ := mem_convexHull_iff_exists_fintype.1 hx
  have hz' : ∀ i, ∃ L : List A, L.Nodup ∧ L.toFinset = S ∧ z i = greedy vfun ∅ L := hz
  choose L hLn hLS hLz using hz'
  have hLmem : ∀ i, ∀ x ∈ L i, x ∈ S := fun i x hx => by
    rw [← hLS i]; exact List.mem_toFinset.2 hx
  have hds : ∀ i, ∃ ds, Inv S (∅ ∪ (L i).toFinset) ds (0 + greedy vfun ∅ (L i)) :=
    fun i => inv_list S G hG (L i) (hLmem i) ∅ [] 0 (inv_init S)
  choose ds hds using hds
  have hInv : ∀ i, Inv S S (ds i) (z i) := by
    intro i; have := hds i; rw [Finset.empty_union, hLS i, zero_add, ← hLz i] at this; exact this
  have hall : ∀ i a, a ∈ verts 0 (ds i) := fun i a =>
    ((hInv i).2.2.1 a).2 (by rw [hgen]; exact AddSubgroup.mem_top a)
  have hlen : ∀ i, (verts 0 (ds i)).length = Fintype.card A := by
    intro i
    rw [← card_of_list ⊤ _ (hInv i).2.1 (fun a => ⟨fun _ => AddSubgroup.mem_top a,
      fun _ => hall i a⟩), AddSubgroup.card_top, Nat.card_eq_fintype_card]
  have hnpos : (0 : ℚ) < Fintype.card A := by exact_mod_cast (by omega : 0 < Fintype.card A)
  have hpc : ∀ i d, (pc d (ds i) : ℚ) = z i d + z i (-d) := by
    intro i d
    have := (hInv i).2.2.2 d
    rw [hlen i] at this
    have h2 : (Fintype.card A : ℚ) ≠ 0 := hnpos.ne'
    field_simp at this
    linarith
  -- clear denominators
  set D : ℕ := ∏ i, (w i).den with hD
  have hDpos : 0 < D := Finset.prod_pos (fun i _ => (w i).den_pos)
  set m : ι → ℕ := fun i => D / (w i).den * (w i).num.toNat with hmdef
  have hm : ∀ i, (m i : ℚ) = D * w i := by
    intro i
    have hdvd : (w i).den ∣ D := Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
    have hnum : (0 : ℤ) ≤ (w i).num := Rat.num_nonneg.2 (hw0 i)
    have h1 : ((w i).num.toNat : ℚ) = ((w i).num : ℚ) := by
      exact_mod_cast congrArg (Int.cast : ℤ → ℚ) (Int.toNat_of_nonneg hnum)
    have hden : ((w i).den : ℚ) ≠ 0 := by exact_mod_cast (w i).den_ne_zero
    simp only [hmdef]
    rw [Nat.cast_mul, Nat.cast_div hdvd hden, h1]
    conv_rhs => rw [← Rat.num_div_den (w i)]
    field_simp
  -- the family
  let J := Σ i : ι, Fin (m i) × A
  let eqv := Fintype.equivFin J
  let W : (j : J) → Σ b, G.Walk j.2.2 b := fun j => walkOf S G hG j.2.2 (ds j.1) (hInv j.1).1
  have hWsupp : ∀ j, (W j).2.support = (verts 0 (ds j.1)).map (· + j.2.2) := by
    intro j; simp only [W]; rw [walkOf_support, verts_shift]
  have hWnd : ∀ j, (W j).2.support.Nodup := by
    intro j; rw [hWsupp]; exact (hInv j.1).2.1.map (add_left_injective _)
  have hWham : ∀ j, (W j).2.IsHamiltonian := by
    intro j a
    apply List.count_eq_one_of_mem (hWnd j)
    rw [hWsupp, List.mem_map]
    exact ⟨a - j.2.2, hall _ _, by abel⟩
  have hWend : ∀ j e, (if e ∈ (W j).2.edges then 1 else 0 : ℕ) =
      (edgesL j.2.2 (ds j.1)).count e := by
    intro j e
    have hnd := (SimpleGraph.Walk.IsPath.mk' (hWnd j)).isTrail.edges_nodup
    have hWe : (W j).2.edges = edgesL j.2.2 (ds j.1) := walkOf_edges S G hG _ _ _
    rw [← hWe]
    split_ifs with h
    · exact (List.count_eq_one_of_mem hnd h).symm
    · exact (List.count_eq_zero_of_not_mem h).symm
  have hn' : (2 : ℚ) ≤ Fintype.card A := by exact_mod_cast hn
  have hcnt : ∀ u s : A, s ∈ S →
      ((Finset.univ.filter fun t : Fin (Fintype.card J) =>
          s(u, u + s) ∈ (W (eqv.symm t)).2.edges).card : ℚ)
        = 2 * D * ((Fintype.card A : ℚ) - 1) / S.card := by
    intro u s hs
    have hs0 : s ≠ 0 := fun h => zero_not_mem_of S G hG (h ▸ hs)
    rw [Finset.card_filter,
      Equiv.sum_comp eqv.symm (fun j => if s(u, u + s) ∈ (W j).2.edges then 1 else 0)]
    simp only [hWend]
    rw [Fintype.sum_sigma]
    simp only [Fintype.sum_prod_type, sum_count_edgesL u s hs0, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    push_cast
    simp only [hpc, hm]
    have h1 := congrFun hsum s
    have h2 := congrFun hsum (-s)
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h1 h2
    rw [if_pos hs] at h1
    rw [if_pos (neg_mem_of S G hG s hs)] at h2
    rw [show (∑ i, (D : ℚ) * w i * (z i s + z i (-s))) =
        D * (∑ i, w i * z i s) + D * (∑ i, w i * z i (-s)) by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun i _ => by ring), h1, h2]
    ring
  obtain ⟨s0, hs0⟩ := S_nonempty S hgen hn
  obtain ⟨k, hk⟩ : ∃ k, k = (Finset.univ.filter fun t : Fin (Fintype.card J) =>
      s((0 : A), 0 + s0) ∈ (W (eqv.symm t)).2.edges).card := ⟨_, rfl⟩
  have hkq : (k : ℚ) = 2 * D * ((Fintype.card A : ℚ) - 1) / S.card := by
    rw [hk]; exact hcnt 0 s0 hs0
  have hkpos : 0 < k := by
    have hσ : (0 : ℚ) < S.card := by exact_mod_cast (S_nonempty S hgen hn).card_pos
    have hD' : (0 : ℚ) < D := by exact_mod_cast hDpos
    have h3 : (0 : ℚ) < (Fintype.card A : ℚ) - 1 := by linarith
    have : (0 : ℚ) < k := by
      rw [hkq]; exact div_pos (mul_pos (mul_pos two_pos hD') h3) hσ
    exact_mod_cast this
  have hkr : k ≤ Fintype.card J := by
    rw [hk]
    exact (Finset.card_filter_le _ _).trans (by simp)
  refine ⟨Fintype.card J, k, lt_of_lt_of_le hkpos hkr, hkpos,
    fun t => (eqv.symm t).2.2, fun t => (W (eqv.symm t)).1, fun t => (W (eqv.symm t)).2,
    fun t => hWham _, ?_⟩
  intro e he
  revert he
  refine Sym2.ind (fun a b => ?_) e
  intro he
  rw [SimpleGraph.mem_edgeSet, hG] at he
  have hb : s(a, b) = s(a, a + (b - a)) := by congr 1; abel
  rw [hb]
  exact_mod_cast (hcnt a (b - a) he).trans hkq.symm

end Graph

end FTAbelian

namespace FTAbelian

section Extra
variable {A : Type} [AddCommGroup A] [Fintype A] [DecidableEq A]
  (S : Finset A) (G : SimpleGraph A) (hG : ∀ a b, G.Adj a b ↔ b - a ∈ S)

include hG in
lemma closure_eq_top_of_connected (hc : G.Connected) :
    AddSubgroup.closure (S : Set A) = ⊤ := by
  rw [eq_top_iff]
  intro a _
  obtain ⟨p⟩ := hc.preconnected 0 a
  suffices h : ∀ u v (p : G.Walk u v), u ∈ AddSubgroup.closure (S : Set A) →
      v ∈ AddSubgroup.closure (S : Set A) from h 0 a p (zero_mem _)
  intro u v p
  induction p with
  | nil => exact id
  | @cons u v w h p ih =>
    intro hu
    apply ih
    have hs := (hG u v).1 h
    rw [show v = u + (v - u) by abel]
    exact add_mem hu (AddSubgroup.subset_closure hs)

include hG in
/-- The same theorem with connectivity as hypothesis (the form of the Left to Solve statement). -/
theorem fair_traversal_cayley_of_connected (hc : G.Connected) (hn : 2 ≤ Fintype.card A) :
    ∃ (r k : ℕ), 0 < r ∧ 0 < k ∧
      ∃ (a b : Fin r → A) (P : ∀ i, G.Walk (a i) (b i)),
        (∀ i, (P i).IsHamiltonian) ∧
        ∀ e ∈ G.edgeSet, (Finset.univ.filter fun i => e ∈ (P i).edges).card = k :=
  fair_traversal_cayley S G hG (closure_eq_top_of_connected S G hG hc) hn


/-- **Fair Traversal for every connected graph with a regular abelian group of automorphisms**,
given as a labelling `e : V ≃ A` of the vertices by a finite abelian group with
`G.Adj u v ↔ e v - e u ∈ S`. The conclusion is literally that of the Left to Solve statement
`OMA.S_gillibert_fair_traversal.main` for this `G`. -/
theorem fair_traversal_of_abelian_labelling {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (A : Type) [AddCommGroup A] [Fintype A] [DecidableEq A] (e : V ≃ A)
    (S : Finset A) (hG : ∀ u v, G.Adj u v ↔ e v - e u ∈ S) (hc : G.Connected)
    (hn : 2 ≤ Fintype.card V) :
    ∃ (r k : ℕ), 0 < r ∧ 0 < k ∧
      ∃ (a b : Fin r → V) (P : ∀ i, G.Walk (a i) (b i)),
        (∀ i, (P i).IsHamiltonian) ∧
        ∀ e' ∈ G.edgeSet, (Finset.univ.filter fun i => e' ∈ (P i).edges).card = k := by
  classical
  let G' : SimpleGraph A := G.comap e.symm
  have hG' : ∀ a b, G'.Adj a b ↔ b - a ∈ S := by
    intro a b
    simp only [G', SimpleGraph.comap_adj, hG, Equiv.apply_symm_apply]
  let φ : G' ≃g G := { toEquiv := e.symm, map_rel_iff' := by intro a b; rfl }
  have hc' : G'.Connected := φ.connected_iff.2 hc
  have hn' : 2 ≤ Fintype.card A := by rwa [← Fintype.card_congr e]
  obtain ⟨r, k, hr, hk, a, b, P, hP, hcnt⟩ :=
    fair_traversal_cayley_of_connected S G' hG' hc' hn'
  refine ⟨r, k, hr, hk, fun i => φ (a i), fun i => φ (b i),
    fun i => (P i).map φ.toHom, fun i => (hP i).map (f := φ.toHom) φ.bijective, ?_⟩
  intro e' he'
  have he'' : Sym2.map φ.symm e' ∈ G'.edgeSet :=
    (SimpleGraph.Iso.map_mem_edgeSet_iff φ.symm).2 he'
  rw [← hcnt _ he'']
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, SimpleGraph.Walk.edges_map]
  have hinj : Function.Injective (Sym2.map (φ.toHom : A → V)) := Sym2.map.injective φ.injective
  have hback : Sym2.map (φ.toHom : A → V) (Sym2.map φ.symm e') = e' := by
    rw [Sym2.map_map]
    have hid : ((φ.toHom : A → V) ∘ φ.symm) = id := by funext x; simp
    rw [hid, Sym2.map_id]
    rfl
  conv_lhs => rw [← hback]
  exact List.mem_map_of_injective hinj

/-- The vertex-transitivity notion of the Left to Solve statement (copied verbatim). -/
def IsVertexTransitive {V : Type*} (G : SimpleGraph V) : Prop :=
  ∀ u v : V, ∃ φ : G ≃g G, φ u = v

/-- Graphs with an abelian labelling are vertex-transitive (translations), so the class of
`main_abelian_cayley` lies inside the hypotheses of the Left to Solve statement. -/
lemma isVertexTransitive_of_labelling {V : Type} (G : SimpleGraph V) (A : Type) [AddCommGroup A]
    (e : V ≃ A) (S : Finset A) (hG : ∀ u v, G.Adj u v ↔ e v - e u ∈ S) : IsVertexTransitive G := by
  intro u v
  let τ : V ≃ V := (e.trans (Equiv.addRight (e v - e u))).trans e.symm
  refine ⟨{ toEquiv := τ, map_rel_iff' := ?_ }, ?_⟩
  · intro a b
    simp only [τ, Equiv.trans_apply, Equiv.coe_addRight, Equiv.apply_symm_apply, hG]
    rw [show e b + (e v - e u) - (e a + (e v - e u)) = e b - e a by abel]
  · simp [τ]

/-- **The Left to Solve statement of Fair Traversal (`gillibert-fair-traversal`, PR #339),
restricted to graphs that admit a regular abelian group of automorphisms** (equivalently, Cayley
graphs of finite abelian groups). Same conclusion, word for word. -/
theorem main_abelian_cayley :
    ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V),
      G.Connected →
      (∃ (A : Type) (_ : AddCommGroup A) (_ : Fintype A) (_ : DecidableEq A) (e : V ≃ A)
        (S : Finset A), ∀ u v, G.Adj u v ↔ e v - e u ∈ S) →
      2 ≤ Fintype.card V →
      ∃ (r k : ℕ), 0 < r ∧ 0 < k ∧
        ∃ (a b : Fin r → V) (P : ∀ i, G.Walk (a i) (b i)),
          (∀ i, (P i).IsHamiltonian) ∧
          ∀ e ∈ G.edgeSet, (Finset.univ.filter fun i => e ∈ (P i).edges).card = k := by
  intro V _ _ G hc hcay hn
  obtain ⟨A, _, _, _, e, S, hG⟩ := hcay
  exact fair_traversal_of_abelian_labelling G A e S hG hc hn

end Extra

end FTAbelian

#print axioms FTAbelian.main_abelian_cayley
#print axioms FTAbelian.isVertexTransitive_of_labelling
