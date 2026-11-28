/-
Copyright 2026 Ming-Chih Kao. Licensed under the Apache License, Version 2.0;
see the LICENSE file at the root of this repository.
Ported from github.com/koolkao/gillibert-fair-traversal-abelian (v1.7.0, commit
06c3a8732759afca38331762b76113135e475ac6) to Lean v4.36.0 and the module system.
-/
module

public import Mathlib

/-!
# Geodesic Deletion for Cayley graphs of abelian groups (Theorem 5 of NOTE.md)

Gillibert's Geodesic Deletion conjecture (Left to Solve `gillibert-geodesic-deletion`, statement #334):
for a finite connected vertex-transitive graph `G` with at least three vertices and every geodesic `P`
of `G`, the induced subgraph `G − V(P)` is connected.

This file proves it for every connected Cayley graph `Cay(A, S)` of a finite abelian group
(`a ~ b ↔ b - a ∈ S`), all degrees (`gd_abelian`, and `main_abelian_cayley` in the form of #334),
and for `|S| ≥ 6` without finiteness (`gd_abelian_card_ge_six`; Theorem 6 of NOTE.md). See NOTE.md §6.

* `peel` (NOTE.md Lemma 5.1): deleting one more end vertex keeps the rest connected if the neighbours
  of that vertex off the path are joined in the rest (any graph).
* `gd_of_startCond`, `gd_of_startAt_either`: induction along the geodesic, peeling one end, or
  either end (any connected graph).
* Degree ≥ 5 (Lemmas 5.2–5.4): `core_card` (`|S| ≥ 8`, counting), `core_gen` (`|S| ≥ 6`: splits
  2 + 3 and 3 + 3 excluded by `split23`, `split33`), `core5` (`|S| = 5`: `split13`, `split22`, or
  the exceptional configuration `S = {c, ±a, ±(a + c)}` with a geodesic of length 1, handled by
  `exc_walk`).
* Degree 4 (the peeling proof of Theorem 4, NOTE.md §6.3): Lemma W (`word_dist`, `w2`, `w3`, `w4`),
  Lemma C (`cfg4_of_fail`), Lemma D (`startAt_either_long`), and explicit walks for geodesics with
  at most three vertices (`startAt_short`) in place of Watkins' bound.
* Degrees 2 and 3: `gd_abelian_card_two`, `gd_abelian_card_three`.
* The statement #334 forms: `main_abelian_cayley` (all degrees) and
  `main_abelian_cayley_ge_four/five/six/eight`, restricted to graphs with an abelian labelling.

Original work (27 November 2026); only Mathlib is used.
-/

@[expose] public section


namespace GDAbelian

open SimpleGraph

section general

variable {V : Type*} {G : SimpleGraph V}

/-- `x` and `y` are joined by a walk of `G` that avoids `T`. -/
def Av (G : SimpleGraph V) (T : Set V) (x y : V) : Prop :=
  ∃ w : G.Walk x y, ∀ z ∈ w.support, z ∉ T

lemma av_refl {T : Set V} {x : V} (hx : x ∉ T) : Av G T x x :=
  ⟨Walk.nil, by
    intro z hz
    rw [Walk.support_nil, List.mem_singleton] at hz
    exact hz ▸ hx⟩

lemma av_symm {T : Set V} {x y : V} (h : Av G T x y) : Av G T y x := by
  obtain ⟨w, hw⟩ := h
  exact ⟨w.reverse, fun z hz => hw z (by rwa [Walk.support_reverse, List.mem_reverse] at hz)⟩

lemma av_trans {T : Set V} {x y z : V} (h1 : Av G T x y) (h2 : Av G T y z) : Av G T x z := by
  obtain ⟨w1, hw1⟩ := h1
  obtain ⟨w2, hw2⟩ := h2
  refine ⟨w1.append w2, fun v hv => ?_⟩
  rw [Walk.mem_support_append_iff] at hv
  rcases hv with hv | hv
  · exact hw1 v hv
  · exact hw2 v hv

lemma av_adj {T : Set V} {x y : V} (h : G.Adj x y) (hx : x ∉ T) (hy : y ∉ T) : Av G T x y := by
  refine ⟨Walk.cons h Walk.nil, fun z hz => ?_⟩
  rw [Walk.support_cons, Walk.support_nil, List.mem_cons, List.mem_singleton] at hz
  rcases hz with rfl | rfl
  · exact hx
  · exact hy

lemma connected_of_av {T : Set V} {x₀ : V} (hx₀ : x₀ ∉ T)
    (h : ∀ x y, x ∉ T → y ∉ T → Av G T x y) : (G.induce {x | x ∉ T}).Connected := by
  have : Nonempty {x | x ∉ T} := ⟨⟨x₀, hx₀⟩⟩
  refine Connected.mk ?_
  rintro ⟨x, hx⟩ ⟨y, hy⟩
  obtain ⟨w, hw⟩ := h x y hx hy
  exact ⟨w.induce {x | x ∉ T} hw⟩

/-- **Peeling one end vertex.** If `G − T'` is connected and the neighbours of `u` outside
`insert u T'` are pairwise joined in `G − insert u T'`, then `G − insert u T'` is connected. -/
lemma peel {T' : Set V} {u : V}
    (h1 : ∀ x y, x ∉ T' → y ∉ T' → Av G T' x y)
    (h2 : ∀ a b, G.Adj u a → G.Adj u b → a ∉ insert u T' → b ∉ insert u T' →
      Av G (insert u T') a b) :
    ∀ x y, x ∉ insert u T' → y ∉ insert u T' → Av G (insert u T') x y := by
  intro x y hx hy
  have hxT : x ∉ T' := fun h => hx (Set.mem_insert_of_mem u h)
  have hyT : y ∉ T' := fun h => hy (Set.mem_insert_of_mem u h)
  obtain ⟨w, hw⟩ := h1 x y hxT hyT
  have aux : ∀ {a b : V} (w : G.Walk a b), (∀ z ∈ w.support, z ∉ T') → b ∉ insert u T' →
      ((a ∉ insert u T' ∧ Av G (insert u T') x a) ∨
        (a = u ∧ ∃ c, G.Adj u c ∧ c ∉ insert u T' ∧ Av G (insert u T') x c)) →
      Av G (insert u T') x b := by
    intro a b w
    induction w with
    | nil =>
      intro _ hb hP
      rcases hP with ⟨_, h⟩ | ⟨rfl, _⟩
      · exact h
      · exact absurd (Set.mem_insert _ _) hb
    | @cons a a' b h w ih =>
      intro hw hb hP
      have hw' : ∀ z ∈ w.support, z ∉ T' := fun z hz =>
        hw z (by rw [Walk.support_cons]; exact List.mem_cons_of_mem _ hz)
      have ha'T : a' ∉ T' := hw' a' w.start_mem_support
      apply ih hw' hb
      rcases hP with ⟨ha, hxa⟩ | ⟨hau, c, hc, hcT, hxc⟩
      · by_cases ha'u : a' = u
        · refine Or.inr ⟨ha'u, a, ?_, ha, hxa⟩
          rw [← ha'u]
          exact h.symm
        · have : a' ∉ insert u T' := by
            rintro (h' | h')
            · exact ha'u h'
            · exact ha'T h'
          exact Or.inl ⟨this, av_trans hxa (av_adj h ha this)⟩
      · rw [hau] at h
        have ha'u : a' ≠ u := h.ne.symm
        have : a' ∉ insert u T' := by
          rintro (h' | h')
          · exact ha'u h'
          · exact ha'T h'
        exact Or.inl ⟨this, av_trans hxc (h2 c a' hc h hcT this)⟩
  exact aux w hw hy (Or.inl ⟨hx, av_refl hx⟩)

/-- Along a geodesic, the distance between the vertices at positions `i ≤ j` is `j - i`
(as in `GDProduct.lean`). -/
lemma dist_getVert {u v : V} (p : G.Walk u v) (hp : p.length = G.dist u v) {i j : ℕ}
    (hij : i ≤ j) (hj : j ≤ p.length) :
    G.dist (p.getVert i) (p.getVert j) = j - i := by
  have hsub : ((p.drop i).take (j - i)).IsSubwalk p :=
    (Walk.isSubwalk_take _ _).trans (Walk.isSubwalk_drop _ _)
  have h := length_eq_dist_of_subwalk hp hsub
  rw [Walk.take_length, Walk.drop_length, Walk.drop_getVert, Nat.add_sub_cancel' hij] at h
  rw [← h]
  omega

/-- A vertex of a geodesic from `u` sits at the position given by its distance from `u`. -/
lemma eq_getVert_dist {u v : V} (p : G.Walk u v) (hp : p.length = G.dist u v) {z : V}
    (hz : z ∈ p.support) : z = p.getVert (G.dist u z) := by
  obtain ⟨n, hn, hnl⟩ := Walk.mem_support_iff_exists_getVert.1 hz
  have h := dist_getVert p hp (Nat.zero_le n) hnl
  rw [Walk.getVert_zero, hn, Nat.sub_zero] at h
  rw [h, hn]

/-- The start condition: for every geodesic from `u`, any two neighbours of `u` off the geodesic
are joined in `G` minus the geodesic. -/
def StartCond (G : SimpleGraph V) : Prop :=
  ∀ (u v : V) (p : G.Walk u v), p.length = G.dist u v →
    ∀ a b, G.Adj u a → G.Adj u b → a ∉ p.support → b ∉ p.support →
      Av G {z | z ∈ p.support} a b

theorem gd_of_startCond (hc : G.Connected) (hs : StartCond G)
    (hnb : ∀ (u v : V) (p : G.Walk u v), p.length = G.dist u v → ∃ a, G.Adj u a ∧ a ∉ p.support) :
    ∀ (u v : V) (p : G.Walk u v), p.IsPath → p.length = G.dist u v →
      (G.induce {x | x ∉ p.support}).Connected := by
  have key : ∀ (u v : V) (p : G.Walk u v), p.IsPath → p.length = G.dist u v →
      ∀ x y, x ∉ ({z | z ∈ p.support} : Set V) → y ∉ ({z | z ∈ p.support} : Set V) →
        Av G {z | z ∈ p.support} x y := by
    intro u v p
    induction p with
    | @nil u =>
      intro _ hl x y hx hy
      have hT : ({z | z ∈ (Walk.nil : G.Walk u u).support} : Set V) = insert u (∅ : Set V) := by
        ext z; simp
      have h1 : ∀ x y, x ∉ (∅ : Set V) → y ∉ (∅ : Set V) → Av G ∅ x y := by
        intro x y _ _
        obtain ⟨w⟩ := hc.preconnected x y
        exact ⟨w, fun z _ => Set.notMem_empty z⟩
      have h2 : ∀ a b, G.Adj u a → G.Adj u b → a ∉ insert u (∅ : Set V) →
          b ∉ insert u (∅ : Set V) → Av G (insert u ∅) a b := by
        intro a b ha hb ha' hb'
        have := hs u u Walk.nil hl a b ha hb (by rw [← hT] at ha'; exact ha')
          (by rw [← hT] at hb'; exact hb')
        rwa [hT] at this
      rw [hT] at hx hy ⊢
      exact peel h1 h2 x y hx hy
    | @cons u w v h q ih =>
      intro hp hl x y hx hy
      rw [Walk.cons_isPath_iff] at hp
      have hq : q.length = G.dist w v := by
        have h1 := dist_le q
        have h2 : G.dist u v ≤ G.dist u w + G.dist w v := hc.dist_triangle
        have h3 : G.dist u w = 1 := dist_eq_one_iff_adj.2 h
        rw [Walk.length_cons] at hl
        omega
      have hT : ({z | z ∈ (Walk.cons h q).support} : Set V) = insert u {z | z ∈ q.support} := by
        ext z; simp [Walk.support_cons]
      have h1 := ih hp.1 hq
      have h2 : ∀ a b, G.Adj u a → G.Adj u b → a ∉ insert u {z | z ∈ q.support} →
          b ∉ insert u {z | z ∈ q.support} → Av G (insert u {z | z ∈ q.support}) a b := by
        intro a b ha hb ha' hb'
        have := hs u v (Walk.cons h q) hl a b ha hb (by rw [← hT] at ha'; exact ha')
          (by rw [← hT] at hb'; exact hb')
        rwa [hT] at this
      rw [hT] at hx hy ⊢
      exact peel h1 h2 x y hx hy
  intro u v p hp hl
  obtain ⟨a, _, ha⟩ := hnb u v p hl
  exact connected_of_av (T := {z | z ∈ p.support}) (x₀ := a) ha (key u v p hp hl)

/-- The start condition at the first vertex of one walk. -/
def StartAt (G : SimpleGraph V) {u v : V} (p : G.Walk u v) : Prop :=
  ∀ a b, G.Adj u a → G.Adj u b → a ∉ p.support → b ∉ p.support → Av G {z | z ∈ p.support} a b

lemma geodesic_tail (hc : G.Connected) {u w v : V} (h : G.Adj u w) (q : G.Walk w v)
    (hl : (Walk.cons h q).length = G.dist u v) : q.length = G.dist w v := by
  have h1 := dist_le q
  have h2 : G.dist u v ≤ G.dist u w + G.dist w v := hc.dist_triangle
  have h3 : G.dist u w = 1 := dist_eq_one_iff_adj.2 h
  rw [Walk.length_cons] at hl
  omega

/-- **Peeling at either end.** If for every geodesic one of its two ends satisfies the start
condition, deleting any geodesic leaves a connected graph. -/
theorem gd_of_startAt_either (hc : G.Connected)
    (hs : ∀ (u v : V) (p : G.Walk u v), p.IsPath → p.length = G.dist u v →
      StartAt G p ∨ StartAt G p.reverse)
    (hnb : ∀ (u v : V) (p : G.Walk u v), p.length = G.dist u v → ∃ a, G.Adj u a ∧ a ∉ p.support) :
    ∀ (u v : V) (p : G.Walk u v), p.IsPath → p.length = G.dist u v →
      (G.induce {x | x ∉ p.support}).Connected := by
  have key : ∀ n, ∀ (u v : V) (p : G.Walk u v), p.length = n → p.IsPath →
      p.length = G.dist u v →
      ∀ x y, x ∉ ({z | z ∈ p.support} : Set V) → y ∉ ({z | z ∈ p.support} : Set V) →
        Av G {z | z ∈ p.support} x y := by
    intro n
    induction n with
    | zero =>
      intro u v p hn hp hl
      cases p with
      | nil =>
        intro x y hx hy
        have hT : ({z | z ∈ (Walk.nil : G.Walk u u).support} : Set V) = insert u (∅ : Set V) := by
          ext z; simp
        have h1 : ∀ x y, x ∉ (∅ : Set V) → y ∉ (∅ : Set V) → Av G ∅ x y := by
          intro x y _ _
          obtain ⟨w⟩ := hc.preconnected x y
          exact ⟨w, fun z _ => Set.notMem_empty z⟩
        have hs0 : StartAt G (Walk.nil : G.Walk u u) := by
          rcases hs u u Walk.nil hp hl with h | h
          · exact h
          · simpa using h
        have h2 : ∀ a b, G.Adj u a → G.Adj u b → a ∉ insert u (∅ : Set V) →
            b ∉ insert u (∅ : Set V) → Av G (insert u ∅) a b := by
          intro a b ha hb ha' hb'
          have := hs0 a b ha hb (by rw [← hT] at ha'; exact ha')
            (by rw [← hT] at hb'; exact hb')
          rwa [hT] at this
        rw [hT] at hx hy ⊢
        exact peel h1 h2 x y hx hy
      | cons h q => simp at hn
    | succ n ih =>
      intro u v p hn hp hl
      have stepS : ∀ {a b : V} (q : G.Walk a b), q.length = n + 1 → q.IsPath →
          q.length = G.dist a b → StartAt G q →
          ∀ x y, x ∉ ({z | z ∈ q.support} : Set V) → y ∉ ({z | z ∈ q.support} : Set V) →
            Av G {z | z ∈ q.support} x y := by
        intro a b q hqn hq hql hqs
        cases q with
        | nil => simp at hqn
        | @cons _ w _ h q' =>
          intro x y hx hy
          rw [Walk.cons_isPath_iff] at hq
          have hq' := geodesic_tail hc h q' hql
          have hT : ({z | z ∈ (Walk.cons h q').support} : Set V) =
              insert a {z | z ∈ q'.support} := by
            ext z; simp [Walk.support_cons]
          have h1 := ih w b q' (by rw [Walk.length_cons] at hqn; omega) hq.1 hq'
          have h2 : ∀ c d, G.Adj a c → G.Adj a d → c ∉ insert a {z | z ∈ q'.support} →
              d ∉ insert a {z | z ∈ q'.support} → Av G (insert a {z | z ∈ q'.support}) c d := by
            intro c d hc' hd hc'' hd'
            have := hqs c d hc' hd (by rw [← hT] at hc''; exact hc'')
              (by rw [← hT] at hd'; exact hd')
            rwa [hT] at this
          rw [hT] at hx hy ⊢
          exact peel h1 h2 x y hx hy
      rcases hs u v p hp hl with h | h
      · exact stepS p hn hp hl h
      · intro x y hx hy
        have hset : ({z | z ∈ p.reverse.support} : Set V) = {z | z ∈ p.support} := by
          ext z; simp [Walk.support_reverse]
        have hrev := stepS p.reverse (by rw [Walk.length_reverse]; exact hn) hp.reverse
          (by rw [Walk.length_reverse, hl, dist_comm]) h x y (by rw [hset]; exact hx)
          (by rw [hset]; exact hy)
        rwa [hset] at hrev
  intro u v p hp hl
  obtain ⟨a, _, ha⟩ := hnb u v p hl
  exact connected_of_av (T := {z | z ∈ p.support}) (x₀ := a) ha (key _ u v p rfl hp hl)

end general

section abelian

variable {A : Type*} [AddCommGroup A] [DecidableEq A] (S : Finset A) (G : SimpleGraph A)
  (hG : ∀ a b, G.Adj a b ↔ b - a ∈ S)

include hG in
lemma neg_mem_of : ∀ x ∈ S, -x ∈ S := by
  intro x hx
  have h1 : G.Adj 0 x := (hG 0 x).2 (by simpa using hx)
  simpa using (hG x 0).1 h1.symm

include hG in
lemma zero_notMem_of : (0 : A) ∉ S := by
  intro h
  exact G.irrefl ((hG 0 0).2 (by simpa using h))

/-- Two-step neighbour graph at the start of a geodesic, abstractly: `x, y ∈ S.erase g1` are linked
when `x + y ∉ {0, g1, g2}`. With `|S| ≥ 8` any two elements are linked in at most two steps. -/
lemma core_card (h8 : 8 ≤ S.card) (g1 g2 : A) :
    ∀ s ∈ S.erase g1, ∀ t ∈ S.erase g1,
      Relation.ReflTransGen (fun x y => x ∈ S.erase g1 ∧ y ∈ S.erase g1 ∧ x + y ≠ 0 ∧
        x + y ≠ g1 ∧ x + y ≠ g2) s t := by
  intro s hs t ht
  set E : Finset A := {-s, g1 - s, g2 - s, -t, g1 - t, g2 - t} with hE
  have hEc : E.card ≤ 6 := by
    rw [hE]
    refine (Finset.card_insert_le _ _).trans ?_
    refine Nat.succ_le_succ ((Finset.card_insert_le _ _).trans ?_)
    refine Nat.succ_le_succ ((Finset.card_insert_le _ _).trans ?_)
    refine Nat.succ_le_succ ((Finset.card_insert_le _ _).trans ?_)
    refine Nat.succ_le_succ ((Finset.card_insert_le _ _).trans ?_)
    simp
  have hNc : 7 ≤ (S.erase g1).card := by
    have := Finset.pred_card_le_card_erase (s := S) (a := g1)
    omega
  obtain ⟨w, hwN, hwE⟩ := Finset.exists_mem_notMem_of_card_lt_card (s := E) (t := S.erase g1)
    (by omega)
  have hw1 : w ≠ -s := fun e => hwE (by rw [hE]; simp [e])
  have hw2 : w ≠ g1 - s := fun e => hwE (by rw [hE]; simp [e])
  have hw3 : w ≠ g2 - s := fun e => hwE (by rw [hE]; simp [e])
  have hw4 : w ≠ -t := fun e => hwE (by rw [hE]; simp [e])
  have hw5 : w ≠ g1 - t := fun e => hwE (by rw [hE]; simp [e])
  have hw6 : w ≠ g2 - t := fun e => hwE (by rw [hE]; simp [e])
  refine Relation.ReflTransGen.tail (Relation.ReflTransGen.single ⟨hs, hwN, ?_, ?_, ?_⟩)
    ⟨hwN, ht, ?_, ?_, ?_⟩
  · intro e; exact hw1 (by rw [eq_neg_iff_add_eq_zero, add_comm]; exact e)
  · intro e; exact hw2 (by rw [← e]; abel)
  · intro e; exact hw3 (by rw [← e]; abel)
  · intro e; exact hw4 (eq_neg_iff_add_eq_zero.2 e)
  · intro e; exact hw5 (by rw [← e]; abel)
  · intro e; exact hw6 (by rw [← e]; abel)

/-- Facts on `g1 = z₁ - u`, `g2 = z₂ - u` for a geodesic `(u = z₀, z₁, z₂, …)` of length 0, 1
or at least 2. -/
def GF (S : Finset A) (g1 g2 : A) : Prop :=
  (g1 = 0 ∧ g2 = 0) ∨ (g1 ∈ S ∧ g2 = g1) ∨ (g1 ∈ S ∧ g2 ∉ S ∧ g2 ≠ 0 ∧ g2 - g1 ∈ S)

include hG in
lemma gf_of_geodesic (u v : A) (p : G.Walk u v) (hp : p.length = G.dist u v) :
    GF S (p.getVert 1 - u) (p.getVert 2 - u) := by
  rcases Nat.lt_or_ge p.length 2 with hl | hl
  · rcases Nat.lt_or_ge p.length 1 with hl1 | hl1
    · left
      have h0 : p.length = 0 := by omega
      have e1 : p.getVert 1 = v := p.getVert_of_length_le (by omega)
      have e2 : p.getVert 2 = v := p.getVert_of_length_le (by omega)
      have euv : u = v := Walk.eq_of_length_eq_zero h0
      rw [e1, e2, ← euv, sub_self]
      exact ⟨rfl, rfl⟩
    · right; left
      have e1 : p.getVert 1 = v := p.getVert_of_length_le (by omega)
      have e2 : p.getVert 2 = v := p.getVert_of_length_le (by omega)
      have hadj : G.Adj (p.getVert 0) (p.getVert 1) := p.adj_getVert_succ (i := 0) (by omega)
      rw [Walk.getVert_zero] at hadj
      exact ⟨(hG _ _).1 hadj, by rw [e1, e2]⟩
  · right; right
    have hadj : G.Adj (p.getVert 0) (p.getVert 1) := p.adj_getVert_succ (i := 0) (by omega)
    rw [Walk.getVert_zero] at hadj
    have hadj2 : G.Adj (p.getVert 1) (p.getVert 2) := p.adj_getVert_succ (i := 1) (by omega)
    have hd := dist_getVert p hp (i := 0) (j := 2) (by omega) hl
    rw [Walk.getVert_zero] at hd
    refine ⟨(hG _ _).1 hadj, ?_, ?_, ?_⟩
    · intro h
      have h' : G.Adj u (p.getVert 2) := (hG _ _).2 h
      rw [dist_eq_one_iff_adj.2 h'] at hd
      omega
    · intro h
      have h' : p.getVert 2 = u := sub_eq_zero.1 h
      rw [h', dist_self] at hd
      omega
    · have h' := (hG _ _).1 hadj2
      rwa [show p.getVert 2 - u - (p.getVert 1 - u) = p.getVert 2 - p.getVert 1 by abel]

omit [DecidableEq A] in
lemma cross_sub [DecidableEq A] {g1 g2 x : A} {Q : Finset A}
    (h : ∀ y ∈ Q, x + y = 0 ∨ x + y = g1 ∨ x + y = g2) : Q ⊆ {-x, g1 - x, g2 - x} := by
  intro y hy
  rcases h y hy with e | e | e
  · have : y = -x := by rw [eq_neg_iff_add_eq_zero, add_comm]; exact e
    simp [this]
  · have : y = g1 - x := by rw [← e]; abel
    simp [this]
  · have : y = g2 - x := by rw [← e]; abel
    simp [this]

lemma card_T_le (x g1 g2 : A) : ({-x, g1 - x, g2 - x} : Finset A).card ≤ 3 := by
  refine (Finset.card_insert_le _ _).trans ?_
  refine Nat.succ_le_succ ((Finset.card_insert_le _ _).trans ?_)
  simp

lemma eq_T {g1 g2 x : A} {Q : Finset A} (h : ∀ y ∈ Q, x + y = 0 ∨ x + y = g1 ∨ x + y = g2)
    (hQ : Q.card = 3) : Q = {-x, g1 - x, g2 - x} :=
  Finset.eq_of_subset_of_card_le (cross_sub h) (by rw [hQ]; exact card_T_le x g1 g2)

/-- A split of sizes 2 + 3 is impossible (degree 6). -/
lemma split23 (hS0 : (0 : A) ∉ S) (hsym : ∀ s ∈ S, -s ∈ S) {g1 g2 : A} (hg1 : g1 ∈ S)
    (hg2 : g2 ∉ S) (hg20 : g2 ≠ 0) {x x' : A} (hxx : x ≠ x') {Q : Finset A} (hQ : Q.card = 3)
    (hx : ∀ y ∈ Q, x + y = 0 ∨ x + y = g1 ∨ x + y = g2)
    (hx' : ∀ y ∈ Q, x' + y = 0 ∨ x' + y = g1 ∨ x' + y = g2) : False := by
  have hg10 : g1 ≠ 0 := fun e => hS0 (e ▸ hg1)
  have hng1 : -g1 ∈ S := hsym g1 hg1
  have m1 : -x ∈ Q := by rw [eq_T hx hQ]; simp
  have m2 : -x' ∈ Q := by rw [eq_T hx' hQ]; simp
  have m3 : g1 - x' ∈ Q := by rw [eq_T hx' hQ]; simp
  have m4 : g2 - x' ∈ Q := by rw [eq_T hx' hQ]; simp
  rcases hx' _ m1 with e | e | e
  · exact hxx (by linear_combination (norm := module) -e)
  · rcases hx _ m2 with f | f | f
    · exact hxx (by linear_combination (norm := module) f)
    · have h2 : g1 + g1 = 0 := by linear_combination (norm := module) -e - f
      rcases hx _ m4 with k | k | k
      · exact hg2 (by rw [show g2 = g1 by linear_combination (norm := module) k + e]; exact hg1)
      · exact hg20 (by linear_combination (norm := module) k + e + h2)
      · exact hxx (by linear_combination (norm := module) k)
    · exact hg2 (by rw [show g2 = -g1 by linear_combination (norm := module) -f - e]; exact hng1)
  · rcases hx _ m2 with f | f | f
    · exact hxx (by linear_combination (norm := module) f)
    · exact hg2 (by rw [show g2 = -g1 by linear_combination (norm := module) -f - e]; exact hng1)
    · have h2 : g2 + g2 = 0 := by linear_combination (norm := module) -e - f
      rcases hx _ m3 with k | k | k
      · exact hg2 (by rw [show g2 = g1 by linear_combination (norm := module) -k - e]; exact hg1)
      · exact hxx (by linear_combination (norm := module) k)
      · exact hg10 (by linear_combination (norm := module) k + e + h2)

/-- A split of sizes 3 + 3 is impossible (degree 7). -/
lemma split33 (hS0 : (0 : A) ∉ S) (hsym : ∀ s ∈ S, -s ∈ S) {g1 g2 : A} (hg1 : g1 ∈ S)
    {P Q : Finset A} (hP : P.card = 3) (hQ : Q.card = 3) (hPN : P ⊆ S.erase g1)
    (hQN : Q ⊆ S.erase g1) (hcov : ∀ z ∈ S.erase g1, z ∈ P ∨ z ∈ Q)
    (hc : ∀ x ∈ P, ∀ y ∈ Q, x + y = 0 ∨ x + y = g1 ∨ x + y = g2) : False := by
  have hc' : ∀ y ∈ Q, ∀ x ∈ P, y + x = 0 ∨ y + x = g1 ∨ y + x = g2 := fun y hy x hx => by
    rw [add_comm]; exact hc x hx y hy
  have mQ : ∀ x ∈ P, -x ∈ Q ∧ g1 - x ∈ Q := fun x hx => by
    rw [eq_T (hc x hx) hQ]; simp
  have mP : ∀ y ∈ Q, -y ∈ P := fun y hy => by rw [eq_T (hc' y hy) hP]; simp
  have hg10 : g1 ≠ 0 := fun e => hS0 (e ▸ hg1)
  have h2 : g1 + g1 = 0 := by
    by_contra hne
    have hneg : -g1 ∈ S.erase g1 :=
      Finset.mem_erase.2 ⟨fun e => hne (by linear_combination (norm := module) -e), hsym g1 hg1⟩
    rcases hcov _ hneg with h | h
    · have h' := (mQ _ h).1
      rw [neg_neg] at h'
      exact (Finset.mem_erase.1 (hQN h')).1 rfl
    · have h' := mP _ h
      rw [neg_neg] at h'
      exact (Finset.mem_erase.1 (hPN h')).1 rfl
  have hτ : ∀ x ∈ P, x + g1 ∈ P := by
    intro x hx
    have h' := mP _ (mQ x hx).2
    rwa [show -(g1 - x) = x + g1 by linear_combination (norm := module) -h2] at h'
  have himg : P.image (· + g1) = P := by
    refine Finset.eq_of_subset_of_card_le ?_ ?_
    · intro z hz
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hz
      exact hτ x hx
    · rw [Finset.card_image_of_injective _ (add_left_injective g1)]
  have hsum : ∑ x ∈ P, (x + g1) = ∑ x ∈ P, x := by
    conv_rhs => rw [← himg]
    rw [Finset.sum_image (fun a _ b _ h => add_right_cancel h)]
  rw [Finset.sum_add_distrib, Finset.sum_const, hP] at hsum
  have h3 : (3 : ℕ) • g1 = 0 := by linear_combination (norm := module) hsum
  exact hg10 (by linear_combination (norm := module) h3 - h2)

/-- The two-step neighbour graph at the start of a geodesic is connected when `|S| ≥ 6`. -/
lemma core_gen (hS0 : (0 : A) ∉ S) (hsym : ∀ s ∈ S, -s ∈ S) (h6 : 6 ≤ S.card) {g1 g2 : A}
    (hf : GF S g1 g2) :
    ∀ s ∈ S.erase g1, ∀ t ∈ S.erase g1,
      Relation.ReflTransGen (fun x y => x ∈ S.erase g1 ∧ y ∈ S.erase g1 ∧ x + y ≠ 0 ∧
        x + y ≠ g1 ∧ x + y ≠ g2) s t := by
  classical
  intro s hs t ht
  by_contra hst
  set R := (fun x y => x ∈ S.erase g1 ∧ y ∈ S.erase g1 ∧ x + y ≠ 0 ∧ x + y ≠ g1 ∧ x + y ≠ g2)
    with hR
  set X := (S.erase g1).filter (fun y => Relation.ReflTransGen R s y) with hX
  set Y := (S.erase g1).filter (fun y => ¬ Relation.ReflTransGen R s y) with hY
  have hcross : ∀ x ∈ X, ∀ y ∈ Y, x + y = 0 ∨ x + y = g1 ∨ x + y = g2 := by
    intro x hx y hy
    rw [hX, Finset.mem_filter] at hx
    rw [hY, Finset.mem_filter] at hy
    by_contra hcon
    push Not at hcon
    exact hy.2 (hx.2.tail ⟨hx.1, hy.1, hcon.1, hcon.2.1, hcon.2.2⟩)
  have hcard : X.card + Y.card = (S.erase g1).card :=
    Finset.card_filter_add_card_filter_not _
  have hN : 5 ≤ (S.erase g1).card := by
    have := Finset.pred_card_le_card_erase (s := S) (a := g1)
    omega
  have hsX : s ∈ X := Finset.mem_filter.2 ⟨hs, Relation.ReflTransGen.refl⟩
  have htY : t ∈ Y := Finset.mem_filter.2 ⟨ht, hst⟩
  have hcrossY : ∀ y ∈ Y, ∀ x ∈ X, y + x = 0 ∨ y + x = g1 ∨ y + x = g2 := fun y hy x hx => by
    rw [add_comm]; exact hcross x hx y hy
  have hY3 : Y.card ≤ 3 :=
    (Finset.card_le_card (cross_sub (hcross s hsX))).trans (card_T_le _ _ _)
  have hX3 : X.card ≤ 3 :=
    (Finset.card_le_card (cross_sub (hcrossY t htY))).trans (card_T_le _ _ _)
  rcases hf with ⟨h1, h2⟩ | ⟨hg1, h2⟩ | ⟨hg1, hg2, hg20, -⟩
  · have hY1 : Y.card ≤ 1 := (Finset.card_le_card (cross_sub (hcross s hsX))).trans
      (by rw [h1, h2]; simp)
    have hX1 : X.card ≤ 1 := (Finset.card_le_card (cross_sub (hcrossY t htY))).trans
      (by rw [h1, h2]; simp)
    omega
  · have hY2 : Y.card ≤ 2 := (Finset.card_le_card (cross_sub (hcross s hsX))).trans
      (by rw [h2]; exact (Finset.card_insert_le _ _).trans (by simp))
    have hX2 : X.card ≤ 2 := (Finset.card_le_card (cross_sub (hcrossY t htY))).trans
      (by rw [h2]; exact (Finset.card_insert_le _ _).trans (by simp))
    omega
  · have hcov : ∀ z ∈ S.erase g1, z ∈ X ∨ z ∈ Y := by
      intro z hz
      by_cases h : Relation.ReflTransGen R s z
      · exact Or.inl (Finset.mem_filter.2 ⟨hz, h⟩)
      · exact Or.inr (Finset.mem_filter.2 ⟨hz, h⟩)
    have hXN : X ⊆ S.erase g1 := Finset.filter_subset _ _
    have hYN : Y ⊆ S.erase g1 := Finset.filter_subset _ _
    rcases (show (X.card = 2 ∧ Y.card = 3) ∨ (X.card = 3 ∧ Y.card = 2) ∨
        (X.card = 3 ∧ Y.card = 3) by omega) with ⟨hx2, hy3⟩ | ⟨hx3, hy2⟩ | ⟨hx3, hy3⟩
    · obtain ⟨x, x', hxx, hXe⟩ := Finset.card_eq_two.1 hx2
      exact split23 S hS0 hsym hg1 hg2 hg20 hxx hy3 (hcross x (by rw [hXe]; simp))
        (hcross x' (by rw [hXe]; simp))
    · obtain ⟨y, y', hyy, hYe⟩ := Finset.card_eq_two.1 hy2
      exact split23 S hS0 hsym hg1 hg2 hg20 hyy hx3 (hcrossY y (by rw [hYe]; simp))
        (hcrossY y' (by rw [hYe]; simp))
    · exact split33 S hS0 hsym hg1 hx3 hy3 hXN hYN hcov hcross

/-- Degree 5, length ≥ 2: a split of sizes 1 + 3 is impossible. -/
lemma split13 (hS0 : (0 : A) ∉ S) (hsym : ∀ s ∈ S, -s ∈ S) {g1 g2 : A} (hg1 : g1 ∈ S)
    (hg2 : g2 ∉ S) (hg20 : g2 ≠ 0) (hq2 : g2 - g1 ∈ S) {x : A} {Q : Finset A} (hQ : Q.card = 3)
    (hxN : x ∈ S.erase g1) (hQN : Q ⊆ S.erase g1) (hcovS : ∀ z ∈ S, z = g1 ∨ z = x ∨ z ∈ Q)
    (hx : ∀ y ∈ Q, x + y = 0 ∨ x + y = g1 ∨ x + y = g2) : False := by
  have hQe := eq_T hx hQ
  have m1 : -x ∈ Q := by rw [hQe]; simp
  have m2 : g1 - x ∈ Q := by rw [hQe]; simp
  have m3 : g2 - x ∈ Q := by rw [hQe]; simp
  have hm1 := Finset.mem_erase.1 (hQN m1)
  have hm2 := Finset.mem_erase.1 (hQN m2)
  have hm3 := Finset.mem_erase.1 (hQN m3)
  have hxg := (Finset.mem_erase.1 hxN).1
  -- the second letter `q2 = g2 - g1`
  have hAB : g2 = g1 + g1 ∨ g2 = g1 + g1 - x := by
    rcases hcovS _ hq2 with e | e | e
    · left; linear_combination (norm := module) e
    · exact absurd (by linear_combination (norm := module) e) hm3.1
    · rw [hQe] at e
      simp only [Finset.mem_insert, Finset.mem_singleton] at e
      rcases e with e | e | e
      · have hg2' : g2 = g1 - x := by linear_combination (norm := module) e
        exact (hg2 (hg2' ▸ hm2.2)).elim
      · right; linear_combination (norm := module) e
      · exact absurd (by linear_combination (norm := module) e) hxg
  rcases hcovS _ (hsym g1 hg1) with e | e | e
  · rcases hAB with h | h
    · exact hg20 (by linear_combination (norm := module) h - e)
    · exact hg2 (by rw [show g2 = -x by linear_combination (norm := module) h - e]; exact hm1.2)
  · exact hm1.1 (by linear_combination (norm := module) e)
  · rw [hQe] at e
    simp only [Finset.mem_insert, Finset.mem_singleton] at e
    rcases e with e | e | e
    · exact hxg (by linear_combination (norm := module) e)
    · rcases hAB with h | h
      · have hg2' : g2 = x := by linear_combination (norm := module) h - e
        exact hg2 (hg2' ▸ (Finset.mem_erase.1 hxN).2)
      · exact hg20 (by linear_combination (norm := module) h - e)
    · have hg2' : g2 = -(g1 - x) := by linear_combination (norm := module) -e
      exact hg2 (hg2' ▸ hsym _ hm2.2)

/-- Degree 5, length ≥ 2, split 2 + 2, `g1` not an involution and `-g1` on the side `P`. -/
lemma split22_neg {g1 g2 : A} (hS0 : (0 : A) ∉ S) (hsym : ∀ s ∈ S, -s ∈ S) (hg1 : g1 ∈ S)
    (hg2 : g2 ∉ S) (hg20 : g2 ≠ 0) (hq2 : g2 - g1 ∈ S) (hni : g1 + g1 ≠ 0)
    {P Q : Finset A} (hP : P.card = 2) (hQ : Q.card = 2) (hPN : P ⊆ S.erase g1)
    (hQN : Q ⊆ S.erase g1) (hcovS : ∀ z ∈ S, z = g1 ∨ z ∈ P ∨ z ∈ Q)
    (hc : ∀ x ∈ P, ∀ y ∈ Q, x + y = 0 ∨ x + y = g1 ∨ x + y = g2) (hz : -g1 ∈ P) : False := by
  have hg10 : g1 ≠ 0 := fun e => hS0 (e ▸ hg1)
  have hQsub : Q ⊆ {g1 + g1, g2 + g1} := by
    intro y hy
    have hyg := (Finset.mem_erase.1 (hQN hy)).1
    rcases hc _ hz y hy with e | e | e
    · exact absurd (by linear_combination (norm := module) e) hyg
    · simp [show y = g1 + g1 by linear_combination (norm := module) e]
    · simp [show y = g2 + g1 by linear_combination (norm := module) e]
  have hQe : Q = {g1 + g1, g2 + g1} := Finset.eq_of_subset_of_card_le hQsub
    (by rw [hQ]; exact (Finset.card_insert_le _ _).trans (by simp))
  have mA : g1 + g1 ∈ Q := by rw [hQe]; simp
  have mB : g2 + g1 ∈ Q := by rw [hQe]; simp
  obtain ⟨v, hvP, hvne⟩ := Finset.exists_mem_ne (by omega : 1 < P.card) (-g1)
  have hPe : P = {-g1, v} := (Finset.eq_of_subset_of_card_le (by
    intro z hz'; simp only [Finset.mem_insert, Finset.mem_singleton] at hz'
    rcases hz' with rfl | rfl
    · exact hz
    · exact hvP) (by rw [hP, Finset.card_pair (Ne.symm hvne)])).symm
  have hvg := (Finset.mem_erase.1 (hPN hvP)).1
  have hAS := (Finset.mem_erase.1 (hQN mA)).2
  rcases hcovS _ hq2 with e | e | e
  · exact hg2 (by rw [show g2 = g1 + g1 by linear_combination (norm := module) e]; exact hAS)
  · rw [hPe] at e
    simp only [Finset.mem_insert, Finset.mem_singleton] at e
    rcases e with e | e
    · exact hg20 (by linear_combination (norm := module) e)
    · rcases hc _ hvP _ mA with k | k | k
      · have hg2' : g2 = -g1 := by linear_combination (norm := module) k + e
        exact hg2 (hg2' ▸ hsym g1 hg1)
      · exact hg20 (by linear_combination (norm := module) k + e)
      · exact hg10 (by linear_combination (norm := module) k + e)
  · rw [hQe] at e
    simp only [Finset.mem_insert, Finset.mem_singleton] at e
    rcases e with e | e
    · rcases hc _ hvP _ mA with k | k | k
      · rcases hc _ hvP _ mB with l | l | l
        · exact hni (by linear_combination (norm := module) l - k - e)
        · exact hg10 (by linear_combination (norm := module) l - k - e)
        · exact hg10 (by linear_combination (norm := module) k - l)
      · exact hvne (by linear_combination (norm := module) k)
      · exact hvg (by linear_combination (norm := module) k + e)
    · exact hni (by linear_combination (norm := module) -e)

/-- Degree 5, length ≥ 2, split 2 + 2, `g1` an involution and `g2 - g1` on the side `P`. -/
lemma split22_inv {g1 g2 : A} (hsym : ∀ s ∈ S, -s ∈ S) (hg2 : g2 ∉ S) (h2 : g1 + g1 = 0)
    {P Q : Finset A} (hQ : Q.card = 2) (hQN : Q ⊆ S.erase g1)
    (hc : ∀ x ∈ P, ∀ y ∈ Q, x + y = 0 ∨ x + y = g1 ∨ x + y = g2) (hz : g2 - g1 ∈ P) : False := by
  have hQsub : Q ⊆ {-(g2 - g1), g1 - (g2 - g1)} := by
    intro y hy
    have hyg := (Finset.mem_erase.1 (hQN hy)).1
    rcases hc _ hz y hy with e | e | e
    · simp [show y = -(g2 - g1) by linear_combination (norm := module) e]
    · simp [show y = g1 - (g2 - g1) by linear_combination (norm := module) e]
    · exact absurd (by linear_combination (norm := module) e) hyg
  have hQe : Q = {-(g2 - g1), g1 - (g2 - g1)} := Finset.eq_of_subset_of_card_le hQsub
    (by rw [hQ]; exact (Finset.card_insert_le _ _).trans (by simp))
  have m : g1 - (g2 - g1) ∈ Q := by rw [hQe]; simp
  have hm := hsym _ (Finset.mem_erase.1 (hQN m)).2
  exact hg2 (by rw [show g2 = -(g1 - (g2 - g1)) by linear_combination (norm := module) h2]; exact hm)

lemma split22 (hS0 : (0 : A) ∉ S) (hsym : ∀ s ∈ S, -s ∈ S) {g1 g2 : A} (hg1 : g1 ∈ S)
    (hg2 : g2 ∉ S) (hg20 : g2 ≠ 0) (hq2 : g2 - g1 ∈ S)
    {P Q : Finset A} (hP : P.card = 2) (hQ : Q.card = 2) (hPN : P ⊆ S.erase g1)
    (hQN : Q ⊆ S.erase g1) (hcovS : ∀ z ∈ S, z = g1 ∨ z ∈ P ∨ z ∈ Q)
    (hc : ∀ x ∈ P, ∀ y ∈ Q, x + y = 0 ∨ x + y = g1 ∨ x + y = g2) : False := by
  have hc' : ∀ y ∈ Q, ∀ x ∈ P, y + x = 0 ∨ y + x = g1 ∨ y + x = g2 := fun y hy x hx => by
    rw [add_comm]; exact hc x hx y hy
  have hcovS' : ∀ z ∈ S, z = g1 ∨ z ∈ Q ∨ z ∈ P := fun z hz => by
    rcases hcovS z hz with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr h)
    · exact Or.inr (Or.inl h)
  by_cases h2 : g1 + g1 = 0
  · rcases hcovS _ hq2 with e | e | e
    · exact hg20 (by linear_combination (norm := module) e + h2)
    · exact split22_inv S hsym hg2 h2 hQ hQN hc e
    · exact split22_inv S hsym hg2 h2 hP hPN hc' e
  · rcases hcovS _ (hsym g1 hg1) with e | e | e
    · exact h2 (by linear_combination (norm := module) -e)
    · exact split22_neg S hS0 hsym hg1 hg2 hg20 hq2 h2 hP hQ hPN hQN hcovS hc e
    · exact split22_neg S hS0 hsym hg1 hg2 hg20 hq2 h2 hQ hP hQN hPN hcovS' hc' e

/-- `|S| ≥ 5`: either the two-step neighbour graph is connected, or we are in the exceptional
configuration (geodesic of length 1, `S.erase g1 ⊆ {s, s + g1, -s, g1 - s}`). -/
lemma core5 (hS0 : (0 : A) ∉ S) (hsym : ∀ s ∈ S, -s ∈ S) (h5 : 5 ≤ S.card) {g1 g2 : A}
    (hf : GF S g1 g2) :
    (∀ s ∈ S.erase g1, ∀ t ∈ S.erase g1,
      Relation.ReflTransGen (fun x y => x ∈ S.erase g1 ∧ y ∈ S.erase g1 ∧ x + y ≠ 0 ∧
        x + y ≠ g1 ∧ x + y ≠ g2) s t) ∨
    (g1 ∈ S ∧ g2 = g1 ∧ ∃ s ∈ S.erase g1, ∀ z ∈ S.erase g1,
      z = s ∨ z = s + g1 ∨ z = -s ∨ z = g1 - s) := by
  classical
  by_cases h6 : 6 ≤ S.card
  · exact Or.inl (core_gen S hS0 hsym h6 hf)
  by_cases hall : ∀ s ∈ S.erase g1, ∀ t ∈ S.erase g1,
      Relation.ReflTransGen (fun x y => x ∈ S.erase g1 ∧ y ∈ S.erase g1 ∧ x + y ≠ 0 ∧
        x + y ≠ g1 ∧ x + y ≠ g2) s t
  · exact Or.inl hall
  push Not at hall
  obtain ⟨s, hs, t, ht, hst⟩ := hall
  set R := (fun x y => x ∈ S.erase g1 ∧ y ∈ S.erase g1 ∧ x + y ≠ 0 ∧ x + y ≠ g1 ∧ x + y ≠ g2)
    with hR
  set X := (S.erase g1).filter (fun y => Relation.ReflTransGen R s y) with hX
  set Y := (S.erase g1).filter (fun y => ¬ Relation.ReflTransGen R s y) with hY
  have hcross : ∀ x ∈ X, ∀ y ∈ Y, x + y = 0 ∨ x + y = g1 ∨ x + y = g2 := by
    intro x hx y hy
    rw [hX, Finset.mem_filter] at hx
    rw [hY, Finset.mem_filter] at hy
    by_contra hcon
    push Not at hcon
    exact hy.2 (hx.2.tail ⟨hx.1, hy.1, hcon.1, hcon.2.1, hcon.2.2⟩)
  have hcard : X.card + Y.card = (S.erase g1).card :=
    Finset.card_filter_add_card_filter_not _
  have hN : 4 ≤ (S.erase g1).card := by
    have := Finset.pred_card_le_card_erase (s := S) (a := g1)
    omega
  have hsX : s ∈ X := Finset.mem_filter.2 ⟨hs, Relation.ReflTransGen.refl⟩
  have htY : t ∈ Y := Finset.mem_filter.2 ⟨ht, hst⟩
  have hcrossY : ∀ y ∈ Y, ∀ x ∈ X, y + x = 0 ∨ y + x = g1 ∨ y + x = g2 := fun y hy x hx => by
    rw [add_comm]; exact hcross x hx y hy
  have hY3 : Y.card ≤ 3 :=
    (Finset.card_le_card (cross_sub (hcross s hsX))).trans (card_T_le _ _ _)
  have hX3 : X.card ≤ 3 :=
    (Finset.card_le_card (cross_sub (hcrossY t htY))).trans (card_T_le _ _ _)
  have hcov : ∀ z ∈ S.erase g1, z ∈ X ∨ z ∈ Y := by
    intro z hz
    by_cases h : Relation.ReflTransGen R s z
    · exact Or.inl (Finset.mem_filter.2 ⟨hz, h⟩)
    · exact Or.inr (Finset.mem_filter.2 ⟨hz, h⟩)
  have hXN : X ⊆ S.erase g1 := Finset.filter_subset _ _
  have hYN : Y ⊆ S.erase g1 := Finset.filter_subset _ _
  rcases hf with ⟨h1, h2⟩ | ⟨hg1, h2⟩ | ⟨hg1, hg2, hg20, hq2⟩
  · have hY1 : Y.card ≤ 1 := (Finset.card_le_card (cross_sub (hcross s hsX))).trans
      (by rw [h1, h2]; simp)
    have hX1 : X.card ≤ 1 := (Finset.card_le_card (cross_sub (hcrossY t htY))).trans
      (by rw [h1, h2]; simp)
    omega
  · have hYs : Y ⊆ {-s, g1 - s, g2 - s} := cross_sub (hcross s hsX)
    have hY2 : Y.card ≤ 2 := (Finset.card_le_card hYs).trans
      (by rw [h2]; exact (Finset.card_insert_le _ _).trans (by simp))
    have hX2 : X.card ≤ 2 := (Finset.card_le_card (cross_sub (hcrossY t htY))).trans
      (by rw [h2]; exact (Finset.card_insert_le _ _).trans (by simp))
    have hYe : Y = {-s, g1 - s} := Finset.eq_of_subset_of_card_le (by rw [h2] at hYs; simpa using hYs)
      (by have := Finset.card_insert_le (-s) ({g1 - s} : Finset A); simp at this ⊢; omega)
    have hnsY : -s ∈ Y := by rw [hYe]; simp
    have hXs : X ⊆ {-(-s), g1 - -s, g2 - -s} := cross_sub (hcrossY _ hnsY)
    refine Or.inr ⟨hg1, h2, s, hs, fun z hz => ?_⟩
    rcases hcov z hz with h | h
    · have := hXs h
      rw [h2] at this
      simp only [Finset.mem_insert, Finset.mem_singleton] at this
      rcases this with e | e | e
      · left; rw [e, neg_neg]
      · right; left; rw [e]; abel
      · right; left; rw [e]; abel
    · rw [hYe] at h
      simp only [Finset.mem_insert, Finset.mem_singleton] at h
      rcases h with e | e
      · right; right; left; exact e
      · right; right; right; exact e
  · have hcovS : ∀ z ∈ S, z = g1 ∨ z ∈ X ∨ z ∈ Y := by
      intro z hz
      by_cases hzg : z = g1
      · exact Or.inl hzg
      · exact Or.inr (hcov z (Finset.mem_erase.2 ⟨hzg, hz⟩))
    have hN4 : (S.erase g1).card = 4 := by
      rw [Finset.card_erase_of_mem hg1]; omega
    rcases (show (X.card = 1 ∧ Y.card = 3) ∨ (X.card = 3 ∧ Y.card = 1) ∨
        (X.card = 2 ∧ Y.card = 2) by omega) with ⟨hx1, hy3⟩ | ⟨hx3, hy1⟩ | ⟨hx2, hy2⟩
    · obtain ⟨x, hXe⟩ := Finset.card_eq_one.1 hx1
      exact (split13 S hS0 hsym hg1 hg2 hg20 hq2 hy3 (hXN (by rw [hXe]; simp)) hYN
        (fun z hz => by
          rcases hcovS z hz with h | h | h
          · exact Or.inl h
          · rw [hXe, Finset.mem_singleton] at h; exact Or.inr (Or.inl h)
          · exact Or.inr (Or.inr h))
        (hcross x (by rw [hXe]; simp))).elim
    · obtain ⟨y, hYe⟩ := Finset.card_eq_one.1 hy1
      exact (split13 S hS0 hsym hg1 hg2 hg20 hq2 hx3 (hYN (by rw [hYe]; simp)) hXN
        (fun z hz => by
          rcases hcovS z hz with h | h | h
          · exact Or.inl h
          · exact Or.inr (Or.inr h)
          · rw [hYe, Finset.mem_singleton] at h; exact Or.inr (Or.inl h))
        (hcrossY y (by rw [hYe]; simp))).elim
    · exact (split22 S hS0 hsym hg1 hg2 hg20 hq2 hx2 hy2 hXN hYN hcovS hcross).elim

include hG in
lemma dist_add_right (hc : G.Connected) (a b c : A) : G.dist (a + c) (b + c) = G.dist a b := by
  have hφ : ∀ x y : A, G.Adj (x + c) (y + c) ↔ G.Adj x y := by
    intro x y
    rw [hG, hG, add_sub_add_right_eq_sub]
  let φ : G ≃g G := { toEquiv := Equiv.addRight c, map_rel_iff' := fun {x y} => hφ x y }
  have h1 : G.dist (φ a) (φ b) ≤ G.dist a b := by
    obtain ⟨w, hw⟩ := (hc.preconnected a b).exists_walk_length_eq_dist
    calc G.dist (φ a) (φ b) ≤ (w.map φ.toHom).length := dist_le _
      _ = G.dist a b := by rw [Walk.length_map, hw]
  have h2 : G.dist a b ≤ G.dist (φ a) (φ b) := by
    obtain ⟨w, hw⟩ := (hc.preconnected (φ a) (φ b)).exists_walk_length_eq_dist
    calc G.dist a b = G.dist (φ.symm (φ a)) (φ.symm (φ b)) := by simp
      _ ≤ (w.map φ.symm.toHom).length := dist_le _
      _ = G.dist (φ a) (φ b) := by rw [Walk.length_map, hw]
  exact le_antisymm h1 h2

include hG in
lemma dist_eq_dist_zero (hc : G.Connected) (a b : A) : G.dist a b = G.dist 0 (b - a) := by
  have := dist_add_right S G hG hc a b (-a)
  rw [add_neg_cancel, ← sub_eq_add_neg] at this
  exact this.symm

include hG in
lemma dist_zero_add_le (hc : G.Connected) (x y : A) :
    G.dist 0 (x + y) ≤ G.dist 0 x + G.dist 0 y := by
  have h := hc.dist_triangle (u := (0 : A)) (v := x) (w := x + y)
  rwa [dist_eq_dist_zero S G hG hc x (x + y), add_sub_cancel_left] at h

include hG in
lemma dist_zero_sum_le (hc : G.Connected) {ι : Type*} [DecidableEq ι] (f : ι → A) (J : Finset ι)
    (hf : ∀ i ∈ J, f i ∈ S) : G.dist 0 (∑ i ∈ J, f i) ≤ J.card := by
  induction J using Finset.induction_on with
  | empty => simp
  | insert a J ha ih =>
    rw [Finset.sum_insert ha, Finset.card_insert_of_notMem ha]
    have h1 : G.dist 0 (f a) ≤ 1 := by
      have : G.Adj 0 (f a) := (hG _ _).2 (by simpa using hf a (Finset.mem_insert_self a J))
      rw [dist_eq_one_iff_adj.2 this]
    have h2 := ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))
    have h3 := dist_zero_add_le S G hG hc (f a) (∑ i ∈ J, f i)
    omega

include hG in
/-- **Lemma W.** The letters of a geodesic at `k` distinct positions sum to an element at distance
at least `k` from `0`. -/
lemma word_dist (hc : G.Connected) {u v : A} (p : G.Walk u v) (hp : p.length = G.dist u v)
    (I : Finset ℕ) (hI : I ⊆ Finset.range p.length) :
    I.card ≤ G.dist 0 (∑ i ∈ I, (p.getVert (i + 1) - p.getVert i)) := by
  have hlet : ∀ i ∈ Finset.range p.length, p.getVert (i + 1) - p.getVert i ∈ S := by
    intro i hi
    exact (hG _ _).1 (p.adj_getVert_succ (Finset.mem_range.1 hi))
  have htel : ∑ i ∈ Finset.range p.length, (p.getVert (i + 1) - p.getVert i) = v - u := by
    rw [Finset.sum_range_sub (fun i => p.getVert i), Walk.getVert_length, Walk.getVert_zero]
  have hsplit := Finset.sum_sdiff hI (f := fun i => p.getVert (i + 1) - p.getVert i)
  have hd : G.dist u v = G.dist 0 (v - u) := dist_eq_dist_zero S G hG hc u v
  have h1 := dist_zero_add_le S G hG hc (∑ i ∈ Finset.range p.length \ I,
    (p.getVert (i + 1) - p.getVert i)) (∑ i ∈ I, (p.getVert (i + 1) - p.getVert i))
  rw [hsplit, htel, ← hd, ← hp] at h1
  have h2 := dist_zero_sum_le S G hG hc (fun i => p.getVert (i + 1) - p.getVert i)
    (Finset.range p.length \ I) (fun i hi => hlet i (Finset.sdiff_subset hi))
  rw [Finset.card_sdiff_of_subset hI, Finset.card_range] at h2
  have h3 : I.card ≤ p.length := by
    simpa using Finset.card_le_card hI
  omega

include hG in
lemma notMem_of_two_le_dist (hc : G.Connected) {x : A} (h : 2 ≤ G.dist 0 x) : x ∉ S ∧ x ≠ 0 := by
  constructor
  · intro hx
    have : G.Adj 0 x := (hG _ _).2 (by simpa using hx)
    rw [dist_eq_one_iff_adj.2 this] at h
    omega
  · rintro rfl
    rw [dist_self] at h
    omega

include hG in
lemma ne_add_of_three_le_dist (hc : G.Connected) {x : A} (h : 3 ≤ G.dist 0 x) :
    ∀ s ∈ S, ∀ t ∈ S, x ≠ s + t := by
  intro s hs t ht e
  have h1 := dist_zero_add_le S G hG hc s t
  have hs1 : G.dist 0 s ≤ 1 := by
    have : G.Adj 0 s := (hG _ _).2 (by simpa using hs)
    rw [dist_eq_one_iff_adj.2 this]
  have ht1 : G.dist 0 t ≤ 1 := by
    have : G.Adj 0 t := (hG _ _).2 (by simpa using ht)
    rw [dist_eq_one_iff_adj.2 this]
  rw [← e] at h1
  omega

/-! ### Degree 4 -/

/-- The five ways the two-step neighbour graph can fail at the start of a geodesic of degree 4
(`g` = first letter, `q` = second letter): (A), (B1), (B2), and two side cases that force length ≤ 2. -/
def Cfg4 (S : Finset A) (g q : A) : Prop :=
  (g + g ∈ S ∧ ∀ w ∈ S, w = g ∨ w = -g ∨ w = g + g ∨ w = -(g + g)) ∨
  (q = g ∧ g + g + g ∈ S ∧ ∀ w ∈ S, w = g ∨ w = -g ∨ w = g + g + g ∨ w = -(g + g + g)) ∨
  (q + q + g + g = 0 ∧ q ≠ g ∧ q ≠ -g ∧ ∀ w ∈ S, w = g ∨ w = -g ∨ w = q ∨ w = -q) ∨
  (g + g = 0 ∧ ∃ x, x + x + x + x = 0 ∧ q = -x ∧ x ∈ S ∧ g - x - x ∈ S ∧
    ∀ w ∈ S, w = g ∨ w = x ∨ w = -x ∨ w = g - x - x) ∨
  (6 • g = 0 ∧ q = g + g ∧ g + g ∈ S ∧ ∀ w ∈ S, w = g ∨ w = -g ∨ w = g + g ∨ w = -(g + g))

section cfg
variable {S}
variable (hS0 : (0 : A) ∉ S) (hsym : ∀ s ∈ S, -s ∈ S) {g q x y z : A} (hg : g ∈ S) (hq : q ∈ S)
  (hr : g + q ∉ S) (hr0 : g + q ≠ 0)
  (hcov : ∀ w ∈ S, w = g ∨ w = x ∨ w = y ∨ w = z) (hxS : x ∈ S) (hyS : y ∈ S) (hzS : z ∈ S)
  (hxg : x ≠ g) (hyg : y ≠ g) (hzg : z ≠ g) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
include hS0 hsym hg hcov hxS hyS hzS hxg hyg hzg hxy hxz hyz

omit [DecidableEq A] in
lemma cfgα (hy : x + y = 0) (hz : x + z = g) :
    g + g ∈ S ∧ ∀ w ∈ S, w = g ∨ w = -g ∨ w = g + g ∨ w = -(g + g) := by
  rcases hcov _ (hsym g hg) with e | e | e | e
  · have h2 : g + g = 0 := by linear_combination (norm := module) -e
    rcases hcov _ (hsym z hzS) with f | f | f | f
    · exact (hS0 (by have : x = 0 := by linear_combination (norm := module) f + hz + h2
                     rw [← this]; exact hxS)).elim
    · exact ((hS0 (by have : g = 0 := by linear_combination (norm := module) -f - hz
                      rw [← this]; exact hg))).elim
    · exact (hxz (by linear_combination (norm := module) f + hy)).elim
    · exact (hxy (by linear_combination (norm := module) -hy + hz + hz + f + h2)).elim
  · exact (hyg (by linear_combination (norm := module) e + hy)).elim
  · exact (hxg (by linear_combination (norm := module) e + hy)).elim
  · have hx2 : x = g + g := by linear_combination (norm := module) hz + e
    have hy2 : y = -(g + g) := by linear_combination (norm := module) hy - hz - e
    refine ⟨hx2 ▸ hxS, fun w hw => ?_⟩
    rcases hcov w hw with h | h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inl (h.trans hx2)))
    · exact Or.inr (Or.inr (Or.inr (h.trans hy2)))
    · exact Or.inr (Or.inl (h.trans e.symm))

omit [DecidableEq A] in
include hq hr hr0 in
lemma cfgβ (hy : x + y = 0) (hz : x + z = g + q) : Cfg4 S g q := by
  rcases hcov _ (hsym g hg) with e | e | e | e
  · have h2 : g + g = 0 := by linear_combination (norm := module) -e
    rcases hcov q hq with f | f | f | f
    · exact (hr0 (by linear_combination (norm := module) f + h2)).elim
    · exact (hzg (by linear_combination (norm := module) f + hz)).elim
    · rcases hcov _ (hsym z hzS) with k | k | k | k
      · exact (hxy (by linear_combination (norm := module) k + f + hz + h2)).elim
      · exact (hr0 (by linear_combination (norm := module) -k - hz)).elim
      · exact (hxz (by linear_combination (norm := module) k + hy)).elim
      · have hzx : z = g - x - x := by linear_combination (norm := module) hz + f + hy
        refine Or.inr (Or.inr (Or.inr (Or.inl ⟨h2, x, ?_, ?_, hxS, hzx ▸ hzS, fun w hw => ?_⟩)))
        · linear_combination (norm := module) k + f + f + hy + hy + hz + hz + h2
        · linear_combination (norm := module) f + hy
        · rcases hcov w hw with h | h | h | h
          · exact Or.inl h
          · exact Or.inr (Or.inl h)
          · exact Or.inr (Or.inr (Or.inl (by rw [h]; linear_combination (norm := module) hy)))
          · exact Or.inr (Or.inr (Or.inr (by rw [h]; linear_combination (norm := module) hz + f + hy)))
    · exact (hxg (by linear_combination (norm := module) hz + f)).elim
  · exact (hyg (by linear_combination (norm := module) e + hy)).elim
  · exact (hxg (by linear_combination (norm := module) e + hy)).elim
  · rcases hcov q hq with f | f | f | f
    · have hx3 : x = g + g + g := by linear_combination (norm := module) hz + e + f
      refine Or.inr (Or.inl ⟨f, hx3 ▸ hxS, fun w hw => ?_⟩)
      rcases hcov w hw with h | h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inr (Or.inl (h.trans hx3)))
      · exact Or.inr (Or.inr (Or.inr (by rw [h]; linear_combination (norm := module) hy - hx3)))
      · exact Or.inr (Or.inl (h.trans e.symm))
    · exact (hzg (by linear_combination (norm := module) hz + f)).elim
    · refine Or.inr (Or.inr (Or.inl ⟨?_, fun h => hyg (by rw [← f]; exact h),
        fun h => hyz (by rw [← f, h]; exact e), fun w hw => ?_⟩))
      · linear_combination (norm := module) -hz - e + f + hy
      · rcases hcov w hw with h | h | h | h
        · exact Or.inl h
        · exact Or.inr (Or.inr (Or.inr (by rw [h]; linear_combination (norm := module) hy + f)))
        · exact Or.inr (Or.inr (Or.inl (h.trans f.symm)))
        · exact Or.inr (Or.inl (h.trans e.symm))
    · exact (hr0 (by linear_combination (norm := module) f - e)).elim

omit [DecidableEq A] in
include hq hr hr0 in
lemma cfgγ (hy : x + y = g) (hz : x + z = g + q) : Cfg4 S g q := by
  have hg0 : g ≠ 0 := fun e => hS0 (e ▸ hg)
  rcases hcov _ (hsym g hg) with e | e | e | e
  · have h2 : g + g = 0 := by linear_combination (norm := module) -e
    rcases hcov _ (hsym x hxS) with k | k | k | k
    · exact (hxg (by linear_combination (norm := module) -k - h2)).elim
    · rcases hcov _ (hsym y hyS) with k2 | k2 | k2 | k2
      · exact (hS0 (by have : x = 0 := by linear_combination (norm := module) k2 + hy + h2
                       rw [← this]; exact hxS)).elim
      · exact (hg0 (by linear_combination (norm := module) -k2 - hy)).elim
      · rcases hcov _ (hsym z hzS) with k3 | k3 | k3 | k3
        · have : g + q = -y := by linear_combination (norm := module) -k3 + hy - hz
          exact (hr (by rw [this]; exact hsym y hyS)).elim
        · exact (hr0 (by linear_combination (norm := module) -k3 - hz)).elim
        · exact (hS0 (by have : q = 0 := by linear_combination (norm := module) -k3 - hy - hz - k - h2
                         rw [← this]; exact hq)).elim
        · rcases hcov q hq with f | f | f | f
          · exact (hr0 (by linear_combination (norm := module) f + h2)).elim
          · have : g + q = y := by linear_combination (norm := module) f - hy - k
            exact (hr (by rw [this]; exact hyS)).elim
          · have : g + q = x := by linear_combination (norm := module) f + hy + k + h2
            exact (hr (by rw [this]; exact hxS)).elim
          · exact (hxg (by linear_combination (norm := module) hz + f)).elim
      · exact (hS0 (by have : q = 0 := by linear_combination (norm := module) -k2 - hy - hz - k - h2
                       rw [← this]; exact hq)).elim
    · exact (hg0 (by linear_combination (norm := module) -k - hy)).elim
    · exact (hr0 (by linear_combination (norm := module) -k - hz)).elim
  · rcases hcov _ (hsym y hyS) with k | k | k | k
    · exact (hxy (by linear_combination (norm := module) k - e)).elim
    · exact (hg0 (by linear_combination (norm := module) -k - hy)).elim
    · rcases hcov _ (hsym z hzS) with k3 | k3 | k3 | k3
      · have : g + q = y := by linear_combination (norm := module) -k3 - hz + hy + k
        exact (hr (by rw [this]; exact hyS)).elim
      · exact (hr0 (by linear_combination (norm := module) -k3 - hz)).elim
      · exact (hS0 (by have : q = 0 := by linear_combination (norm := module) -k3 - hz + hy + k
                       rw [← this]; exact hq)).elim
      · rcases hcov q hq with f | f | f | f
        · have : g + q = y := by linear_combination (norm := module) f - hy - e
          exact (hr (by rw [this]; exact hyS)).elim
        · exact (hr0 (by linear_combination (norm := module) f - e)).elim
        · have : g + q = x := by linear_combination (norm := module) f - hy - k
          exact (hr (by rw [this]; exact hxS)).elim
        · exact (hxg (by linear_combination (norm := module) hz + f)).elim
    · rcases hcov q hq with f | f | f | f
      · have : g + q = y := by linear_combination (norm := module) f - hy - e
        exact (hr (by rw [this]; exact hyS)).elim
      · exact (hr0 (by linear_combination (norm := module) f - e)).elim
      · have hy2 : y = g + g := by linear_combination (norm := module) hy + e
        refine Or.inr (Or.inr (Or.inr (Or.inr ⟨?_, ?_, hy2 ▸ hyS, fun w hw => ?_⟩)))
        · linear_combination (norm := module) -k - hz - e - e - e - hy - hy - f
        · linear_combination (norm := module) f + hy + e
        · rcases hcov w hw with h | h | h | h
          · exact Or.inl h
          · exact Or.inr (Or.inl (h.trans e.symm))
          · exact Or.inr (Or.inr (Or.inl (by rw [h]; linear_combination (norm := module) hy + e)))
          · exact Or.inr (Or.inr (Or.inr (by rw [h]; linear_combination (norm := module) -k - hy - e)))
      · exact (hxg (by linear_combination (norm := module) hz + f)).elim
  · rcases hcov _ (hsym x hxS) with k | k | k | k
    · exact (hxy (by linear_combination (norm := module) -k + e)).elim
    · rcases hcov _ (hsym z hzS) with k3 | k3 | k3 | k3
      · exact (hS0 (by have : q = 0 := by linear_combination (norm := module) -k3 - hz + e + hy
                       rw [← this]; exact hq)).elim
      · exact (hr0 (by linear_combination (norm := module) -k3 - hz)).elim
      · exact (hzg (by linear_combination (norm := module) -k3 + e)).elim
      · rcases hcov q hq with f | f | f | f
        · have : g + q = x := by linear_combination (norm := module) f - hy - e
          exact (hr (by rw [this]; exact hxS)).elim
        · have : g + q = y := by linear_combination (norm := module) f - hy - k
          exact (hr (by rw [this]; exact hyS)).elim
        · exact (hr0 (by linear_combination (norm := module) f - e)).elim
        · exact (hxg (by linear_combination (norm := module) hz + f)).elim
    · exact (hg0 (by linear_combination (norm := module) -k - hy)).elim
    · exact (hr0 (by linear_combination (norm := module) -k - hz)).elim
  · have : g + q = -y := by linear_combination (norm := module) -e + hy - hz
    exact (hr (by rw [this]; exact hsym y hyS)).elim

end cfg

/-- Failure of the two-step neighbour graph at the start (degree 4): some element is blocked with
the two others. -/
def Fail4 (S : Finset A) (g g2 : A) : Prop :=
  ∃ x ∈ S.erase g, ∀ y ∈ S.erase g, y ≠ x → x + y = 0 ∨ x + y = g ∨ x + y = g2

omit [DecidableEq A] in
lemma cfg4_of_fail [DecidableEq A] (hS0 : (0 : A) ∉ S) (hsym : ∀ s ∈ S, -s ∈ S) (h4 : S.card = 4)
    {g q : A} (hg : g ∈ S) (hq : q ∈ S) (hr : g + q ∉ S) (hr0 : g + q ≠ 0)
    (hf : Fail4 S g (g + q)) : Cfg4 S g q := by
  obtain ⟨x, hxN, hx⟩ := hf
  have hN3 : (S.erase g).card = 3 := by rw [Finset.card_erase_of_mem hg, h4]
  have h2 : ((S.erase g).erase x).card = 2 := by rw [Finset.card_erase_of_mem hxN, hN3]
  obtain ⟨y, z, hyz, he⟩ := Finset.card_eq_two.1 h2
  have hyN : y ∈ (S.erase g).erase x := by rw [he]; simp
  have hzN : z ∈ (S.erase g).erase x := by rw [he]; simp
  rw [Finset.mem_erase, Finset.mem_erase] at hyN hzN
  have hxN' := Finset.mem_erase.1 hxN
  have hcov : ∀ w ∈ S, w = g ∨ w = x ∨ w = y ∨ w = z := by
    intro w hw
    by_cases hwg : w = g
    · exact Or.inl hwg
    by_cases hwx : w = x
    · exact Or.inr (Or.inl hwx)
    have : w ∈ (S.erase g).erase x := by simp [hwg, hwx, hw]
    rw [he] at this
    simp only [Finset.mem_insert, Finset.mem_singleton] at this
    rcases this with h | h
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr h))
  have hcov' : ∀ w ∈ S, w = g ∨ w = x ∨ w = z ∨ w = y := by
    intro w hw
    rcases hcov w hw with h | h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inr h))
    · exact Or.inr (Or.inr (Or.inl h))
  have hxy : x ≠ y := fun h => hyN.1 h.symm
  have hxz : x ≠ z := fun h => hzN.1 h.symm
  rcases hx y (Finset.mem_erase.2 ⟨hyN.2.1, hyN.2.2⟩) hyN.1 with e1 | e1 | e1 <;>
    rcases hx z (Finset.mem_erase.2 ⟨hzN.2.1, hzN.2.2⟩) hzN.1 with e2 | e2 | e2
  · exact (hyz (by linear_combination (norm := module) e1 - e2)).elim
  · exact Or.inl (cfgα hS0 hsym hg hcov hxN'.2 hyN.2.2 hzN.2.2 hxN'.1 hyN.2.1 hzN.2.1 hxy hxz hyz e1 e2)
  · exact cfgβ hS0 hsym hg hq hr hr0 hcov hxN'.2 hyN.2.2 hzN.2.2 hxN'.1 hyN.2.1 hzN.2.1 hxy hxz
      hyz e1 e2
  · exact Or.inl (cfgα hS0 hsym hg hcov' hxN'.2 hzN.2.2 hyN.2.2 hxN'.1 hzN.2.1 hyN.2.1 hxz hxy
      (Ne.symm hyz) e2 e1)
  · exact (hyz (by linear_combination (norm := module) e1 - e2)).elim
  · exact cfgγ hS0 hsym hg hq hr hr0 hcov hxN'.2 hyN.2.2 hzN.2.2 hxN'.1 hyN.2.1 hzN.2.1 hxy hxz
      hyz e1 e2
  · exact cfgβ hS0 hsym hg hq hr hr0 hcov' hxN'.2 hzN.2.2 hyN.2.2 hxN'.1 hzN.2.1 hyN.2.1 hxz hxy
      (Ne.symm hyz) e2 e1
  · exact cfgγ hS0 hsym hg hq hr hr0 hcov' hxN'.2 hzN.2.2 hyN.2.2 hxN'.1 hzN.2.1 hyN.2.1 hxz hxy
      (Ne.symm hyz) e2 e1
  · exact (hyz (by linear_combination (norm := module) e1 - e2)).elim

section pair
variable {S}

/-- `x` is at distance at least 2 from `0`. -/
def N2 (S : Finset A) (x : A) : Prop := x ∉ S ∧ x ≠ 0

/-- `x` is at distance at least 3 from `0`. -/
def N3 (S : Finset A) (x : A) : Prop := x ∉ S ∧ x ≠ 0 ∧ ∀ s ∈ S, ∀ t ∈ S, x ≠ s + t

omit [DecidableEq A] in
lemma N2.neg (hsym : ∀ s ∈ S, -s ∈ S) {x y : A} (h : N2 S (x + y)) : N2 S (-x + -y) := by
  refine ⟨fun hm => h.1 ?_, fun e => h.2 ?_⟩
  · have := hsym _ hm; rwa [show -(-x + -y) = x + y by abel] at this
  · linear_combination (norm := module) -e

omit [DecidableEq A] in
lemma N3.neg (hsym : ∀ s ∈ S, -s ∈ S) {x y z : A} (h : N3 S (x + y + z)) :
    N3 S (-x + -y + -z) := by
  refine ⟨fun hm => h.1 ?_, fun e => h.2.1 ?_,
    fun s hs t ht e => h.2.2 (-s) (hsym s hs) (-t) (hsym t ht) ?_⟩
  · have := hsym _ hm; rwa [show -(-x + -y + -z) = x + y + z by abel] at this
  · linear_combination (norm := module) -e
  · linear_combination (norm := module) -e

omit [DecidableEq A] in
lemma card_le_three_of_cover [DecidableEq A] {p₁ p₂ p₃ : A} (h : ∀ w ∈ S, w = p₁ ∨ w = p₂ ∨ w = p₃) :
    S.card ≤ 3 := by
  have hsub : S ⊆ {p₁, p₂, p₃} := by
    intro w hw
    rcases h w hw with e | e | e <;> simp [e]
  refine (Finset.card_le_card hsub).trans ?_
  refine (Finset.card_insert_le _ _).trans ?_
  refine Nat.succ_le_succ ((Finset.card_insert_le _ _).trans ?_)
  simp

/-- Side configurations are impossible when the geodesic has a third letter `t`. -/
lemma excl_side (hsym : ∀ s ∈ S, -s ∈ S) {g q t : A} (hg : g ∈ S) (ht : t ∈ S)
    (h02 : N2 S (g + t)) (h12 : N2 S (q + t)) (h012 : N3 S (g + q + t))
    (hcf : (g + g = 0 ∧ ∃ x, x + x + x + x = 0 ∧ q = -x ∧ x ∈ S ∧ g - x - x ∈ S ∧
        ∀ w ∈ S, w = g ∨ w = x ∨ w = -x ∨ w = g - x - x) ∨
      (6 • g = 0 ∧ q = g + g ∧ g + g ∈ S ∧
        ∀ w ∈ S, w = g ∨ w = -g ∨ w = g + g ∨ w = -(g + g))) : False := by
  rcases hcf with ⟨h2, x, h4, hq, hxS, hx2S, hcov⟩ | ⟨h6, hq, h2S, hcov⟩
  · rcases hcov t ht with e | e | e | e
    · exact h02.2 (by rw [e]; exact h2)
    · exact h12.2 (by rw [hq, e]; abel)
    · exact h012.1 (by rw [show g + q + t = g - x - x by rw [hq, e]; abel]; exact hx2S)
    · exact h012.1 (by rw [show g + q + t = x by linear_combination (norm := module) hq + e + h2 - h4]
                       exact hxS)
  · rcases hcov t ht with e | e | e | e
    · exact h012.1 (by rw [show g + q + t = -(g + g) by
                         linear_combination (norm := module) hq + e + h6]; exact hsym _ h2S)
    · exact h012.1 (by rw [show g + q + t = g + g by linear_combination (norm := module) hq + e]
                       exact h2S)
    · exact h012.1 (by rw [show g + q + t = -g by linear_combination (norm := module) hq + e + h6]
                       exact hsym g hg)
    · exact h012.1 (by rw [show g + q + t = g by linear_combination (norm := module) hq + e]
                       exact hg)

omit [DecidableEq A] in
lemma two_val {a w : A} (hw : w ∈ S) (haw : N2 S (a + w))
    (hcov : ∀ w ∈ S, w = a ∨ w = -a ∨ w = a + a ∨ w = -(a + a)) (h2 : a + a ∈ S) :
    w = a + a ∨ w = -(a + a) := by
  rcases hcov w hw with e | e | e | e
  · exact (haw.1 (by rw [e]; exact h2)).elim
  · exact (haw.2 (by rw [e]; abel)).elim
  · exact Or.inl e
  · exact Or.inr e

omit [DecidableEq A] in
lemma eq_of_two_val {a c d : A} (hc : c = a + a ∨ c = -(a + a)) (hd : d = a + a ∨ d = -(a + a))
    (hcd : N2 S (c + d)) : c = d := by
  rcases hc with rfl | rfl <;> rcases hd with rfl | rfl
  · rfl
  · exact (hcd.2 (by abel)).elim
  · exact (hcd.2 (by abel)).elim
  · rfl

/-- Pairing, length ≥ 4, configuration (A) at the start. -/
lemma pairA4 (hsym : ∀ s ∈ S, -s ∈ S) {a c d e : A} (hcS : c ∈ S) (hdS : d ∈ S) (heS : e ∈ S)
    (hac : N2 S (a + c)) (had : N2 S (a + d)) (hae : N2 S (a + e))
    (hcd : N2 S (c + d)) (hed : N2 S (e + d)) (hecd : N3 S (e + c + d))
    (hA : a + a ∈ S ∧ ∀ w ∈ S, w = a ∨ w = -a ∨ w = a + a ∨ w = -(a + a))
    (hend : (-d + -d ∈ S ∧ ∀ w ∈ S, w = -d ∨ w = - -d ∨ w = -d + -d ∨ w = -(-d + -d)) ∨
      (-c = -d ∧ -d + -d + -d ∈ S ∧ ∀ w ∈ S, w = -d ∨ w = - -d ∨ w = -d + -d + -d ∨
        w = -(-d + -d + -d)) ∨
      (-c + -c + -d + -d = 0 ∧ -c ≠ -d ∧ -c ≠ - -d ∧ ∀ w ∈ S, w = -d ∨ w = - -d ∨ w = -c ∨
        w = - -c)) : False := by
  have hc2 := two_val hcS hac hA.2 hA.1
  have hd2 := two_val hdS had hA.2 hA.1
  have he2 := two_val heS hae hA.2 hA.1
  have hcd' := eq_of_two_val hc2 hd2 hcd
  have hed' := eq_of_two_val he2 hd2 hed
  rcases hend with ⟨h, -⟩ | ⟨-, h, -⟩ | ⟨-, h, -⟩
  · exact hcd.1 (by rw [hcd', show d + d = -(-d + -d) by abel]; exact hsym _ h)
  · exact hecd.1 (by rw [hcd', hed', show d + d + d = -(-d + -d + -d) by abel]; exact hsym _ h)
  · exact h (by rw [hcd'])

/-- Pairing, length 3, configuration (A) at the start (letters `a, b, d`). -/
lemma pairA3 (hsym : ∀ s ∈ S, -s ∈ S) (h4 : S.card = 4) {a b d : A} (haS : a ∈ S) (hbS : b ∈ S)
    (hdS : d ∈ S) (hab : N2 S (a + b)) (had : N2 S (a + d)) (hbd : N2 S (b + d))
    (habd : N3 S (a + b + d))
    (hA : a + a ∈ S ∧ ∀ w ∈ S, w = a ∨ w = -a ∨ w = a + a ∨ w = -(a + a))
    (hend : (-d + -d ∈ S ∧ ∀ w ∈ S, w = -d ∨ w = - -d ∨ w = -d + -d ∨ w = -(-d + -d)) ∨
      (-b = -d ∧ -d + -d + -d ∈ S ∧ ∀ w ∈ S, w = -d ∨ w = - -d ∨ w = -d + -d + -d ∨
        w = -(-d + -d + -d)) ∨
      (-b + -b + -d + -d = 0 ∧ -b ≠ -d ∧ -b ≠ - -d ∧ ∀ w ∈ S, w = -d ∨ w = - -d ∨ w = -b ∨
        w = - -b)) : False := by
  have hb2 := two_val hbS hab hA.2 hA.1
  have hd2 := two_val hdS had hA.2 hA.1
  have hbd' := eq_of_two_val hb2 hd2 hbd
  rcases hend with ⟨h, -⟩ | ⟨-, h, -⟩ | ⟨-, h, -⟩
  · exact hbd.1 (by rw [hbd', show d + d = -(-d + -d) by abel]; exact hsym _ h)
  · rcases hd2 with e | e
    · rcases hA.2 _ h with f | f | f | f
      · exact habd.1 (by rw [show a + b + d = -(a + a) by
            rw [hbd']; linear_combination (norm := module) -e - f]; exact hsym _ hA.1)
      · exact habd.2.1 (by rw [hbd']; linear_combination (norm := module) -e - f)
      · exact habd.2.2 (-a) (hsym a haS) (-(a + a)) (hsym _ hA.1) (by
          rw [hbd']; linear_combination (norm := module) -e - f)
      · have h22 : a + a = -(a + a) := by linear_combination (norm := module) -e - e - e - f
        have : S.card ≤ 3 := card_le_three_of_cover (p₁ := a) (p₂ := -a) (p₃ := a + a) (by
          intro w hw
          rcases hA.2 w hw with g | g | g | g
          · exact Or.inl g
          · exact Or.inr (Or.inl g)
          · exact Or.inr (Or.inr g)
          · exact Or.inr (Or.inr (g.trans h22.symm)))
        omega
    · exact habd.2.2 (-a) (hsym a haS) (-(a + a)) (hsym _ hA.1) (by
        rw [hbd', e]; abel)
  · exact h (by rw [hbd'])

/-- Pairing (B1)–(B1′), length ≥ 4. -/
lemma pairB1B1_4 (hsym : ∀ s ∈ S, -s ∈ S) (h4 : S.card = 4) {a b c d : A} (haS : a ∈ S)
    (hdS : d ∈ S) (had : N2 S (a + d)) (habd : N3 S (a + b + d)) (hacd : N3 S (a + c + d))
    (hs : b = a ∧ a + a + a ∈ S ∧ ∀ w ∈ S, w = a ∨ w = -a ∨ w = a + a + a ∨ w = -(a + a + a))
    (he : -c = -d ∧ -d + -d + -d ∈ S ∧ ∀ w ∈ S, w = -d ∨ w = - -d ∨ w = -d + -d + -d ∨
        w = -(-d + -d + -d)) : False := by
  obtain ⟨hb, h3, hcov⟩ := hs
  obtain ⟨hcd, -, hcov'⟩ := he
  have hcd' : c = d := neg_injective hcd
  rcases hcov d hdS with e | e | e | e
  · exact habd.1 (by rw [hb, e]; exact h3)
  · exact had.2 (by rw [e]; abel)
  · rcases hcov' a haS with f | f | f | f
    · have h3a : a + a + a = -a := by linear_combination (norm := module) f - e
      have : S.card ≤ 3 := card_le_three_of_cover (p₁ := a) (p₂ := -a) (p₃ := -a) (by
        intro w hw
        rcases hcov w hw with g | g | g | g
        · exact Or.inl g
        · exact Or.inr (Or.inl g)
        · exact Or.inr (Or.inl (g.trans h3a))
        · exact Or.inl (by rw [g, h3a, neg_neg]))
      omega
    · have h2 : a + a = 0 := by linear_combination (norm := module) -f - e
      have : S.card ≤ 3 := card_le_three_of_cover (p₁ := a) (p₂ := a) (p₃ := a) (by
        intro w hw
        rcases hcov w hw with g | g | g | g
        · exact Or.inl g
        · exact Or.inl (by rw [g]; linear_combination (norm := module) -h2)
        · exact Or.inl (by rw [g]; linear_combination (norm := module) h2)
        · exact Or.inl (by rw [g]; linear_combination (norm := module) -h2 - h2))
      omega
    · exact hacd.1 (by rw [hcd', show a + d + d = -(a + a + a) by
        linear_combination (norm := module) f - e]; exact hsym _ h3)
    · exact habd.1 (by rw [hb, show a + a + d = -(a + a + a) by
        linear_combination (norm := module) -f - e - e]; exact hsym _ h3)
  · exact habd.1 (by rw [hb, show a + a + d = -a by linear_combination (norm := module) e]
                     exact hsym a haS)

/-- Pairing (B1)–(B2′), length ≥ 4. -/
lemma pairB1B2_4 {a b c d : A} (hcS : c ∈ S) (hdS : d ∈ S)
    (hac : N2 S (a + c)) (had : N2 S (a + d)) (habc : N3 S (a + b + c)) (habd : N3 S (a + b + d))
    (hs : b = a ∧ a + a + a ∈ S ∧ ∀ w ∈ S, w = a ∨ w = -a ∨ w = a + a + a ∨ w = -(a + a + a))
    (he : -c + -c + -d + -d = 0 ∧ -c ≠ -d ∧ -c ≠ - -d ∧ ∀ w ∈ S, w = -d ∨ w = - -d ∨ w = -c ∨
        w = - -c) : False := by
  obtain ⟨hb, h3, hcov⟩ := hs
  obtain ⟨-, hne1, hne2, -⟩ := he
  rcases hcov c hcS with e | e | e | e
  · exact habc.1 (by rw [hb, e]; exact h3)
  · exact hac.2 (by rw [e]; abel)
  · rcases hcov d hdS with f | f | f | f
    · exact habd.1 (by rw [hb, f]; exact h3)
    · exact had.2 (by rw [f]; abel)
    · exact hne1 (by rw [e, f])
    · exact hne2 (by rw [e, f, neg_neg])
  · rcases hcov d hdS with f | f | f | f
    · exact habd.1 (by rw [hb, f]; exact h3)
    · exact had.2 (by rw [f]; abel)
    · exact hne2 (by rw [e, f, neg_neg])
    · exact hne1 (by rw [e, f])

/-- Pairing (B2)–(B2′), length ≥ 4. -/
lemma pairB2B2_4 {a b c d : A} (hcS : c ∈ S) (hdS : d ∈ S)
    (hac : N2 S (a + c)) (had : N2 S (a + d)) (hbc : N2 S (b + c)) (hbd : N2 S (b + d))
    (habcd : a + b + c + d ≠ 0)
    (hs : b + b + a + a = 0 ∧ b ≠ a ∧ b ≠ -a ∧ ∀ w ∈ S, w = a ∨ w = -a ∨ w = b ∨ w = -b)
    (he : -c + -c + -d + -d = 0 ∧ -c ≠ -d ∧ -c ≠ - -d ∧ ∀ w ∈ S, w = -d ∨ w = - -d ∨ w = -c ∨
        w = - -c) : False := by
  obtain ⟨h2, -, -, hcov⟩ := hs
  obtain ⟨-, hne1, -, -⟩ := he
  have hc' : c = a ∨ c = b := by
    rcases hcov c hcS with e | e | e | e
    · exact Or.inl e
    · exact (hac.2 (by rw [e]; abel)).elim
    · exact Or.inr e
    · exact (hbc.2 (by rw [e]; abel)).elim
  have hd' : d = a ∨ d = b := by
    rcases hcov d hdS with e | e | e | e
    · exact Or.inl e
    · exact (had.2 (by rw [e]; abel)).elim
    · exact Or.inr e
    · exact (hbd.2 (by rw [e]; abel)).elim
  rcases hc' with e | e <;> rcases hd' with f | f
  · exact hne1 (by rw [e, f])
  · exact habcd (by rw [e, f]; linear_combination (norm := module) h2)
  · exact habcd (by rw [e, f]; linear_combination (norm := module) h2)
  · exact hne1 (by rw [e, f])

/-- Length 3: configurations (B1)/(B2) at both ends (letters `a, b, d`, the middle letter is shared). -/
lemma pairB_3 (hsym : ∀ s ∈ S, -s ∈ S) {a b d : A} (haS : a ∈ S) (hbS : b ∈ S) (hdS : d ∈ S)
    (had : N2 S (a + d)) (habd : N3 S (a + b + d))
    (hs : (b = a ∧ a + a + a ∈ S ∧ ∀ w ∈ S, w = a ∨ w = -a ∨ w = a + a + a ∨ w = -(a + a + a)) ∨
      (b + b + a + a = 0 ∧ b ≠ a ∧ b ≠ -a ∧ ∀ w ∈ S, w = a ∨ w = -a ∨ w = b ∨ w = -b))
    (he : (-b = -d ∧ -d + -d + -d ∈ S ∧ ∀ w ∈ S, w = -d ∨ w = - -d ∨ w = -d + -d + -d ∨
        w = -(-d + -d + -d)) ∨
      (-b + -b + -d + -d = 0 ∧ -b ≠ -d ∧ -b ≠ - -d ∧ ∀ w ∈ S, w = -d ∨ w = - -d ∨ w = -b ∨
        w = - -b)) : False := by
  rcases hs with ⟨hb, h3, hcov⟩ | ⟨h2, -, -, hcov⟩
  · rcases he with ⟨hbd, -, -⟩ | ⟨h2', hne1, hne2, -⟩
    · have hda : d = a := by rw [← neg_injective hbd, hb]
      exact habd.1 (by rw [hb, hda]; exact h3)
    · rw [hb] at h2' hne1 hne2
      rcases hcov d hdS with e | e | e | e
      · exact hne1 (by rw [e])
      · exact hne2 (by rw [e, neg_neg])
      · exact habd.1 (by rw [hb, show a + a + d = -(a + a + a) by
          linear_combination (norm := module) -h2' - e]; exact hsym _ h3)
      · exact habd.1 (by rw [hb, show a + a + d = -a by linear_combination (norm := module) e]
                         exact hsym a haS)
  · rcases he with ⟨hbd, -, -⟩ | ⟨-, hne1, hne2, -⟩
    · have hdb : d = b := (neg_injective hbd).symm
      exact habd.1 (by rw [hdb, show a + b + b = -a by linear_combination (norm := module) h2]
                       exact hsym a haS)
    · rcases hcov d hdS with e | e | e | e
      · exact habd.1 (by rw [e, show a + b + a = -b by linear_combination (norm := module) h2]
                         exact hsym b hbS)
      · exact had.2 (by rw [e]; abel)
      · exact hne1 (by rw [e])
      · exact hne2 (by rw [e, neg_neg])

/-- The three long-geodesic configurations (A), (B1), (B2). -/
def CABC (S : Finset A) (g q : A) : Prop :=
  (g + g ∈ S ∧ ∀ w ∈ S, w = g ∨ w = -g ∨ w = g + g ∨ w = -(g + g)) ∨
  (q = g ∧ g + g + g ∈ S ∧ ∀ w ∈ S, w = g ∨ w = -g ∨ w = g + g + g ∨ w = -(g + g + g)) ∨
  (q + q + g + g = 0 ∧ q ≠ g ∧ q ≠ -g ∧ ∀ w ∈ S, w = g ∨ w = -g ∨ w = q ∨ w = -q)

lemma cabc_of_cfg4 (hsym : ∀ s ∈ S, -s ∈ S) {g q t : A} (hg : g ∈ S) (ht : t ∈ S)
    (h02 : N2 S (g + t)) (h12 : N2 S (q + t)) (h012 : N3 S (g + q + t)) (hc : Cfg4 S g q) :
    CABC S g q := by
  rcases hc with h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)
  · exact (excl_side hsym hg ht h02 h12 h012 h).elim

/-- Degree 4: if the two-step neighbour graph does not fail, it is connected. -/
lemma core4 (hS0 : (0 : A) ∉ S) (hsym : ∀ s ∈ S, -s ∈ S) (h4 : S.card = 4) {g1 g2 : A}
    (hf : GF S g1 g2) (hnf : ¬ Fail4 S g1 g2) :
    ∀ s ∈ S.erase g1, ∀ t ∈ S.erase g1,
      Relation.ReflTransGen (fun x y => x ∈ S.erase g1 ∧ y ∈ S.erase g1 ∧ x + y ≠ 0 ∧
        x + y ≠ g1 ∧ x + y ≠ g2) s t := by
  classical
  intro s hs t ht
  by_contra hst
  set R := (fun x y => x ∈ S.erase g1 ∧ y ∈ S.erase g1 ∧ x + y ≠ 0 ∧ x + y ≠ g1 ∧ x + y ≠ g2)
    with hR
  set X := (S.erase g1).filter (fun y => Relation.ReflTransGen R s y) with hX
  set Y := (S.erase g1).filter (fun y => ¬ Relation.ReflTransGen R s y) with hY
  have hcross : ∀ x ∈ X, ∀ y ∈ Y, x + y = 0 ∨ x + y = g1 ∨ x + y = g2 := by
    intro x hx y hy
    rw [hX, Finset.mem_filter] at hx
    rw [hY, Finset.mem_filter] at hy
    by_contra hcon
    push Not at hcon
    exact hy.2 (hx.2.tail ⟨hx.1, hy.1, hcon.1, hcon.2.1, hcon.2.2⟩)
  have hcard : X.card + Y.card = (S.erase g1).card :=
    Finset.card_filter_add_card_filter_not _
  have hsX : s ∈ X := Finset.mem_filter.2 ⟨hs, Relation.ReflTransGen.refl⟩
  have htY : t ∈ Y := Finset.mem_filter.2 ⟨ht, hst⟩
  have hcrossY : ∀ y ∈ Y, ∀ x ∈ X, y + x = 0 ∨ y + x = g1 ∨ y + x = g2 := fun y hy x hx => by
    rw [add_comm]; exact hcross x hx y hy
  have hcov : ∀ z ∈ S.erase g1, z ∈ X ∨ z ∈ Y := by
    intro z hz
    by_cases h : Relation.ReflTransGen R s z
    · exact Or.inl (Finset.mem_filter.2 ⟨hz, h⟩)
    · exact Or.inr (Finset.mem_filter.2 ⟨hz, h⟩)
  have hX0 : 0 < X.card := Finset.card_pos.2 ⟨s, hsX⟩
  have hY0 : 0 < Y.card := Finset.card_pos.2 ⟨t, htY⟩
  rcases hf with ⟨h1, h2⟩ | ⟨hg1, -⟩ | ⟨hg1, -⟩
  · have hY1 : Y.card ≤ 1 := (Finset.card_le_card (cross_sub (hcross s hsX))).trans
      (by rw [h1, h2]; simp)
    have hX1 : X.card ≤ 1 := (Finset.card_le_card (cross_sub (hcrossY t htY))).trans
      (by rw [h1, h2]; simp)
    have : 3 ≤ (S.erase g1).card := by
      have := Finset.pred_card_le_card_erase (s := S) (a := g1); omega
    omega
  all_goals
    have hN3 : (S.erase g1).card = 3 := by rw [Finset.card_erase_of_mem hg1, h4]
    apply hnf
    rcases (show X.card = 1 ∨ Y.card = 1 by omega) with h1 | h1
    · obtain ⟨x, hXe⟩ := Finset.card_eq_one.1 h1
      have hxX : x ∈ X := by rw [hXe]; simp
      refine ⟨x, Finset.filter_subset _ _ hxX, fun y hy hyx => ?_⟩
      rcases hcov y hy with h | h
      · rw [hXe, Finset.mem_singleton] at h; exact absurd h hyx
      · exact hcross x hxX y h
    · obtain ⟨y, hYe⟩ := Finset.card_eq_one.1 h1
      have hyY : y ∈ Y := by rw [hYe]; simp
      refine ⟨y, Finset.filter_subset _ _ hyY, fun w hw hwy => ?_⟩
      rcases hcov w hw with h | h
      · exact hcrossY y hyY w h
      · rw [hYe, Finset.mem_singleton] at h; exact absurd h hwy

omit [DecidableEq A] in
lemma cfgA_of_fail1 [DecidableEq A] (hS0 : (0 : A) ∉ S) (hsym : ∀ s ∈ S, -s ∈ S) (h4 : S.card = 4)
    {g : A} (hg : g ∈ S) (hf : Fail4 S g g) :
    g + g ∈ S ∧ ∀ w ∈ S, w = g ∨ w = -g ∨ w = g + g ∨ w = -(g + g) := by
  obtain ⟨x, hxN, hx⟩ := hf
  have hN3 : (S.erase g).card = 3 := by rw [Finset.card_erase_of_mem hg, h4]
  have h2 : ((S.erase g).erase x).card = 2 := by rw [Finset.card_erase_of_mem hxN, hN3]
  obtain ⟨y, z, hyz, he⟩ := Finset.card_eq_two.1 h2
  have hyN : y ∈ (S.erase g).erase x := by rw [he]; simp
  have hzN : z ∈ (S.erase g).erase x := by rw [he]; simp
  rw [Finset.mem_erase, Finset.mem_erase] at hyN hzN
  have hxN' := Finset.mem_erase.1 hxN
  have hcov : ∀ w ∈ S, w = g ∨ w = x ∨ w = y ∨ w = z := by
    intro w hw
    by_cases hwg : w = g
    · exact Or.inl hwg
    by_cases hwx : w = x
    · exact Or.inr (Or.inl hwx)
    have : w ∈ (S.erase g).erase x := by simp [hwg, hwx, hw]
    rw [he] at this
    simp only [Finset.mem_insert, Finset.mem_singleton] at this
    rcases this with h | h
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr h))
  have hcov' : ∀ w ∈ S, w = g ∨ w = x ∨ w = z ∨ w = y := by
    intro w hw
    rcases hcov w hw with h | h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inr h))
    · exact Or.inr (Or.inr (Or.inl h))
  have hxy : x ≠ y := fun h => hyN.1 h.symm
  have hxz : x ≠ z := fun h => hzN.1 h.symm
  rcases hx y (Finset.mem_erase.2 ⟨hyN.2.1, hyN.2.2⟩) hyN.1 with e1 | e1 | e1 <;>
    rcases hx z (Finset.mem_erase.2 ⟨hzN.2.1, hzN.2.2⟩) hzN.1 with e2 | e2 | e2
  all_goals first
    | exact (hyz (by linear_combination (norm := module) e1 - e2)).elim
    | exact cfgα hS0 hsym hg hcov hxN'.2 hyN.2.2 hzN.2.2 hxN'.1 hyN.2.1 hzN.2.1 hxy hxz
        hyz e1 e2
    | exact cfgα hS0 hsym hg hcov' hxN'.2 hzN.2.2 hyN.2.2 hxN'.1 hzN.2.1 hyN.2.1 hxz hxy
        (Ne.symm hyz) e2 e1

end pair

include hG in
/-- From an abstract link chain to walks avoiding the geodesic. -/
lemma av_of_chain (u v : A) (p : G.Walk u v) (hp : p.length = G.dist u v) (s : A)
    (hsS : s ∈ S.erase (p.getVert 1 - u)) :
    ∀ t, Relation.ReflTransGen (fun x y => x ∈ S.erase (p.getVert 1 - u) ∧
        y ∈ S.erase (p.getVert 1 - u) ∧ x + y ≠ 0 ∧ x + y ≠ p.getVert 1 - u ∧
        x + y ≠ p.getVert 2 - u) s t →
      Av G {z | z ∈ p.support} (u + s) (u + t) := by
  -- vertices `u + x`, `x ∈ S.erase g1`, are off the geodesic
  have off : ∀ x ∈ S.erase (p.getVert 1 - u), u + x ∉ ({z | z ∈ p.support} : Set A) := by
    intro x hx hmem
    rw [Finset.mem_erase] at hx
    have hadj : G.Adj u (u + x) := (hG _ _).2 (by simpa using hx.2)
    have h1 := eq_getVert_dist p hp hmem
    rw [dist_eq_one_iff_adj.2 hadj] at h1
    exact hx.1 (by rw [← h1]; abel)
  intro t ht
  induction ht with
  | refl => exact av_refl (off s hsS)
  | @tail b c _ hbc ih =>
    obtain ⟨hb, hc, h0, h1, h2⟩ := hbc
    have hbS : b ∈ S := (Finset.mem_erase.1 hb).2
    have hcS : c ∈ S := (Finset.mem_erase.1 hc).2
    have hm1 : G.Adj (u + b) (u + b + c) := (hG _ _).2 (by simpa using hcS)
    have hm2 : G.Adj (u + b + c) (u + c) :=
      (hG _ _).2 (by rw [show u + c - (u + b + c) = -b by abel]; exact neg_mem_of S G hG b hbS)
    have hmid : u + b + c ∉ ({z | z ∈ p.support} : Set A) := by
      intro hmem
      have hd : G.dist u (u + b + c) ≤ 2 := by
        have hu1 : G.Adj u (u + b) := (hG _ _).2 (by simpa using hbS)
        have := dist_le ((Walk.nil : G.Walk (u + b + c) (u + b + c)).cons hm1 |>.cons hu1)
        simpa using this
      have hz := eq_getVert_dist p hp hmem
      interval_cases hk : G.dist u (u + b + c)
      · rw [Walk.getVert_zero] at hz
        exact h0 (by
          have : b + c = (u + b + c) - u := by abel
          rw [this, hz, sub_self])
      · exact h1 (by
          have : b + c = (u + b + c) - u := by abel
          rw [this, ← hz])
      · exact h2 (by
          have : b + c = (u + b + c) - u := by abel
          rw [this, ← hz])
    exact av_trans ih (av_trans (av_adj hm1 (off b hb) hmid) (av_adj hm2 hmid (off c hc)))

include hG in
theorem startCond_of_card_six (h6 : 6 ≤ S.card) : StartCond G := by
  intro u v p hp a b ha hb ha' hb'
  have hs : a - u ∈ S := (hG u a).1 ha
  have ht : b - u ∈ S := (hG u b).1 hb
  have hne : ∀ x, G.Adj u x → x ∉ p.support → x - u ≠ p.getVert 1 - u := by
    intro x hx hx' e
    apply hx'
    rw [show x = p.getVert 1 by simpa using e]
    exact p.getVert_mem_support 1
  have hsE : a - u ∈ S.erase (p.getVert 1 - u) := Finset.mem_erase.2 ⟨hne a ha ha', hs⟩
  have htE : b - u ∈ S.erase (p.getVert 1 - u) := Finset.mem_erase.2 ⟨hne b hb hb', ht⟩
  have := av_of_chain S G hG u v p hp (a - u) hsE (b - u)
    (core_gen S (zero_notMem_of S G hG) (neg_mem_of S G hG) h6
      (gf_of_geodesic S G hG u v p hp) _ hsE _ htE)
  simpa using this

include hG in
/-- The exceptional configuration (degree 5, geodesic of length 1): walk through the pairs
`{k • s, k • s + c}`. Needs `A` finite (it fails for `ℤ × ℤ/2`). -/
lemma exc_walk [Finite A] (u v : A) (p : G.Walk u v) (hl : p.length = 1) {s : A}
    (hsN : s ∈ S.erase (p.getVert 1 - u))
    (hcov : ∀ z ∈ S.erase (p.getVert 1 - u),
      z = s ∨ z = s + (p.getVert 1 - u) ∨ z = -s ∨ z = (p.getVert 1 - u) - s) :
    ∀ z ∈ S.erase (p.getVert 1 - u), Av G {x | x ∈ p.support} (u + s) (u + z) := by
  classical
  have hcS : p.getVert 1 - u ∈ S := by
    have hadj : G.Adj (p.getVert 0) (p.getVert 1) := p.adj_getVert_succ (i := 0) (by omega)
    rw [Walk.getVert_zero] at hadj
    exact (hG _ _).1 hadj
  set c := p.getVert 1 - u with hcdef
  have hT : ∀ x ∈ p.support, x = u ∨ x = u + c := by
    intro x hx
    obtain ⟨n, hn, hnl⟩ := Walk.mem_support_iff_exists_getVert.1 hx
    rw [hl] at hnl
    interval_cases n
    · left; rw [← hn, Walk.getVert_zero]
    · right; rw [← hn, hcdef]; abel
  have hS0 := zero_notMem_of S G hG
  have hsym := neg_mem_of S G hG
  have offN : ∀ z ∈ S.erase c, u + z ∉ ({x | x ∈ p.support} : Set A) := by
    intro z hz hmem
    rcases hT _ hmem with e | e
    · have hz0 : z = 0 := by linear_combination (norm := module) e
      exact hS0 (hz0 ▸ (Finset.mem_erase.1 hz).2)
    · exact (Finset.mem_erase.1 hz).1 (by linear_combination (norm := module) e)
  have adjS : ∀ x z, z ∈ S → G.Adj x (x + z) := fun x z hz => (hG _ _).2 (by simpa using hz)
  have hsS := (Finset.mem_erase.1 hsN).2
  have hsc := (Finset.mem_erase.1 hsN).1
  have hex : ∃ k, 0 < k ∧ (k • s = 0 ∨ k • s = c) :=
    ⟨addOrderOf s, addOrderOf_pos s, Or.inl (addOrderOf_nsmul_eq_zero s)⟩
  set m := Nat.find hex with hmdef
  have hm : 0 < m ∧ (m • s = 0 ∨ m • s = c) := Nat.find_spec hex
  have hmin : ∀ k, 0 < k → k < m → k • s ≠ 0 ∧ k • s ≠ c := fun k hk hkm => by
    have h := Nat.find_min hex hkm
    exact ⟨fun e => h ⟨hk, Or.inl e⟩, fun e => h ⟨hk, Or.inr e⟩⟩
  have hoff : ∀ k, 0 < k → k < m → u + k • s ∉ ({x | x ∈ p.support} : Set A) := by
    intro k hk hkm hmem
    rcases hT _ hmem with e | e
    · exact (hmin k hk hkm).1 (by linear_combination (norm := module) e)
    · exact (hmin k hk hkm).2 (by linear_combination (norm := module) e)
  have hm2 : 2 ≤ m := by
    by_contra h
    have hm1 : m = 1 := by omega
    rcases hm.2 with e | e <;> rw [hm1, one_smul] at e
    · exact hS0 (e ▸ hsS)
    · exact hsc e
  have chain : ∀ k, 0 < k → k < m → Av G {x | x ∈ p.support} (u + s) (u + k • s) := by
    intro k
    induction k with
    | zero => intro h; omega
    | succ k ih =>
      intro _ hkm
      rcases Nat.eq_zero_or_pos k with hk0 | hk
      · rw [hk0, zero_add, one_smul]
        exact av_refl (offN s hsN)
      · have h1 := ih hk (by omega)
        refine av_trans h1 (av_adj ?_ (hoff k hk (by omega)) (hoff (k + 1) (by omega) hkm))
        rw [succ_nsmul, ← add_assoc]
        exact adjS _ _ hsS
  have hend := chain (m - 1) (by omega) (by omega)
  have hmm : (m - 1) • s + s = m • s := by
    rw [← succ_nsmul]
    congr 1
    omega
  have hoffm := hoff (m - 1) (by omega) (by omega)
  intro z hz
  have hzoff := offN z hz
  rcases hcov z hz with rfl | rfl | rfl | rfl
  · exact av_refl hzoff
  · exact av_adj (by rw [← add_assoc]; exact adjS _ _ hcS) (offN _ hsN) hzoff
  · rcases hm.2 with e | e
    · have h' : (m - 1) • s = -s := by linear_combination (norm := module) hmm + e
      rw [h'] at hend
      exact hend
    · have h' : (m - 1) • s = c - s := by linear_combination (norm := module) hmm + e
      rw [h'] at hend hoffm
      refine av_trans hend (av_adj ?_ hoffm hzoff)
      exact (hG _ _).2 (by rw [show u + -s - (u + (c - s)) = -c by abel]; exact hsym c hcS)
  · rcases hm.2 with e | e
    · have h' : (m - 1) • s = -s := by linear_combination (norm := module) hmm + e
      rw [h'] at hend hoffm
      refine av_trans hend (av_adj ?_ hoffm hzoff)
      exact (hG _ _).2 (by rw [show u + (c - s) - (u + -s) = c by abel]; exact hcS)
    · have h' : (m - 1) • s = c - s := by linear_combination (norm := module) hmm + e
      rw [h'] at hend
      exact hend

include hG in
theorem startCond_of_card_five [Finite A] (h5 : 5 ≤ S.card) : StartCond G := by
  intro u v p hp a b ha hb ha' hb'
  have hs : a - u ∈ S := (hG u a).1 ha
  have ht : b - u ∈ S := (hG u b).1 hb
  have hne : ∀ x, G.Adj u x → x ∉ p.support → x - u ≠ p.getVert 1 - u := by
    intro x hx hx' e
    apply hx'
    rw [show x = p.getVert 1 by simpa using e]
    exact p.getVert_mem_support 1
  have hsE : a - u ∈ S.erase (p.getVert 1 - u) := Finset.mem_erase.2 ⟨hne a ha ha', hs⟩
  have htE : b - u ∈ S.erase (p.getVert 1 - u) := Finset.mem_erase.2 ⟨hne b hb hb', ht⟩
  rcases core5 S (zero_notMem_of S G hG) (neg_mem_of S G hG) h5 (gf_of_geodesic S G hG u v p hp)
    with hall | ⟨hg1, h21, s0, hs0, hcov⟩
  · have := av_of_chain S G hG u v p hp (a - u) hsE (b - u) (hall _ hsE _ htE)
    simpa using this
  · have hl : p.length = 1 := by
      by_contra hl
      rcases Nat.lt_or_ge p.length 1 with h0 | h2
      · have h0' : p.length = 0 := by omega
        have e1 : p.getVert 1 = v := p.getVert_of_length_le (by omega)
        have euv : u = v := Walk.eq_of_length_eq_zero h0'
        rw [e1, ← euv, sub_self] at hg1
        exact zero_notMem_of S G hG hg1
      · have h2' : 2 ≤ p.length := by omega
        have hd := dist_getVert p hp (i := 0) (j := 2) (by omega) h2'
        rw [Walk.getVert_zero] at hd
        have hadj : G.Adj u (p.getVert 2) := (hG _ _).2 (by rw [h21]; exact hg1)
        rw [dist_eq_one_iff_adj.2 hadj] at hd
        omega
    have h1 := exc_walk S G hG u v p hl hs0 hcov (a - u) hsE
    have h2 := exc_walk S G hG u v p hl hs0 hcov (b - u) htE
    have := av_trans (av_symm h1) h2
    simpa using this

include hG in
theorem startAt_of_not_fail4 (h4 : S.card = 4) {u v : A} (p : G.Walk u v)
    (hp : p.length = G.dist u v) (hnf : ¬ Fail4 S (p.getVert 1 - u) (p.getVert 2 - u)) :
    StartAt G p := by
  intro a b ha hb ha' hb'
  have hs : a - u ∈ S := (hG u a).1 ha
  have ht : b - u ∈ S := (hG u b).1 hb
  have hne : ∀ x, G.Adj u x → x ∉ p.support → x - u ≠ p.getVert 1 - u := by
    intro x hx hx' e
    apply hx'
    rw [show x = p.getVert 1 by simpa using e]
    exact p.getVert_mem_support 1
  have hsE : a - u ∈ S.erase (p.getVert 1 - u) := Finset.mem_erase.2 ⟨hne a ha ha', hs⟩
  have htE : b - u ∈ S.erase (p.getVert 1 - u) := Finset.mem_erase.2 ⟨hne b hb hb', ht⟩
  have := av_of_chain S G hG u v p hp (a - u) hsE (b - u)
    (core4 (zero_notMem_of S G hG) (neg_mem_of S G hG) h4
      (gf_of_geodesic S G hG u v p hp) hnf _ hsE _ htE)
  simpa using this

include hG in
lemma w2 (hc : G.Connected) {u v : A} (p : G.Walk u v) (hp : p.length = G.dist u v) {i j : ℕ}
    (hij : i ≠ j) (hi : i < p.length) (hj : j < p.length) :
    N2 S ((p.getVert (i + 1) - p.getVert i) + (p.getVert (j + 1) - p.getVert j)) := by
  have h := word_dist S G hG hc p hp {i, j} (by
    intro k hk; simp only [Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with rfl | rfl <;> simpa)
  rw [Finset.card_pair hij, Finset.sum_pair hij] at h
  exact notMem_of_two_le_dist S G hG hc h

include hG in
lemma w3 (hc : G.Connected) {u v : A} (p : G.Walk u v) (hp : p.length = G.dist u v) {i j k : ℕ}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (hi : i < p.length) (hj : j < p.length)
    (hk : k < p.length) :
    N3 S ((p.getVert (i + 1) - p.getVert i) + (p.getVert (j + 1) - p.getVert j) +
      (p.getVert (k + 1) - p.getVert k)) := by
  have h := word_dist S G hG hc p hp {i, j, k} (by
    intro l hl; simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl | rfl <;> simpa)
  have hnot : i ∉ ({j, k} : Finset ℕ) := by simp [hij, hik]
  rw [Finset.card_insert_of_notMem hnot, Finset.card_pair hjk, Finset.sum_insert hnot,
    Finset.sum_pair hjk, ← add_assoc] at h
  exact ⟨(notMem_of_two_le_dist S G hG hc (by omega)).1,
    (notMem_of_two_le_dist S G hG hc (by omega)).2, ne_add_of_three_le_dist S G hG hc h⟩

include hG in
lemma w4 (hc : G.Connected) {u v : A} (p : G.Walk u v) (hp : p.length = G.dist u v)
    {i j k l : ℕ} (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l)
    (hkl : k ≠ l) (hi : i < p.length) (hj : j < p.length) (hk : k < p.length) (hl : l < p.length) :
    (p.getVert (i + 1) - p.getVert i) + (p.getVert (j + 1) - p.getVert j) +
      (p.getVert (k + 1) - p.getVert k) + (p.getVert (l + 1) - p.getVert l) ≠ 0 := by
  have h := word_dist S G hG hc p hp {i, j, k, l} (by
    intro m hm; simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with rfl | rfl | rfl | rfl <;> simpa)
  have hn1 : i ∉ ({j, k, l} : Finset ℕ) := by simp [hij, hik, hil]
  have hn2 : j ∉ ({k, l} : Finset ℕ) := by simp [hjk, hjl]
  rw [Finset.card_insert_of_notMem hn1, Finset.card_insert_of_notMem hn2, Finset.card_pair hkl,
    Finset.sum_insert hn1, Finset.sum_insert hn2, Finset.sum_pair hkl, ← add_assoc,
    ← add_assoc] at h
  intro e
  rw [e, dist_self] at h
  omega

include hG in
/-- **Degree 4, geodesics with at least 4 vertices:** one of the two ends satisfies the start
condition (Lemma D of NOTE.md §6.3). -/
theorem startAt_either_long (h4 : S.card = 4) (hc : G.Connected) {u v : A} (p : G.Walk u v)
    (hp : p.length = G.dist u v) (hL : 3 ≤ p.length) : StartAt G p ∨ StartAt G p.reverse := by
  have hS0 := zero_notMem_of S G hG
  have hsym := neg_mem_of S G hG
  by_cases h1 : Fail4 S (p.getVert 1 - u) (p.getVert 2 - u)
  swap
  · exact Or.inl (startAt_of_not_fail4 S G hG h4 p hp h1)
  have hpr : p.reverse.length = G.dist v u := by rw [Walk.length_reverse, hp, dist_comm]
  by_cases h2 : Fail4 S (p.reverse.getVert 1 - v) (p.reverse.getVert 2 - v)
  swap
  · exact Or.inr (startAt_of_not_fail4 S G hG h4 p.reverse hpr h2)
  exfalso
  set L := p.length with hLdef
  set ℓ : ℕ → A := fun i => p.getVert (i + 1) - p.getVert i with hℓ
  have hℓS : ∀ i, i < L → ℓ i ∈ S := fun i hi => (hG _ _).1 (p.adj_getVert_succ hi)
  have W2 : ∀ i j, i ≠ j → i < L → j < L → N2 S (ℓ i + ℓ j) :=
    fun i j hij hi hj => w2 S G hG hc p hp hij hi hj
  have W3 : ∀ i j k, i ≠ j → i ≠ k → j ≠ k → i < L → j < L → k < L → N3 S (ℓ i + ℓ j + ℓ k) :=
    fun i j k hij hik hjk hi hj hk => w3 S G hG hc p hp hij hik hjk hi hj hk
  -- start letters
  have hs1 : p.getVert 1 - u = ℓ 0 := by simp [hℓ]
  have hs2 : p.getVert 2 - u = ℓ 0 + ℓ 1 := by simp only [hℓ, Walk.getVert_zero]; abel
  rw [hs1, hs2] at h1
  have hc1 := cfg4_of_fail S hS0 hsym h4 (hℓS 0 (by omega)) (hℓS 1 (by omega))
    (W2 0 1 (by omega) (by omega) (by omega)).1 (W2 0 1 (by omega) (by omega) (by omega)).2 h1
  have hC1 := cabc_of_cfg4 hsym (hℓS 0 (by omega)) (hℓS 2 (by omega))
    (W2 0 2 (by omega) (by omega) (by omega)) (W2 1 2 (by omega) (by omega) (by omega))
    (W3 0 1 2 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)) hc1
  -- end letters
  have hv : p.getVert L = v := Walk.getVert_length p
  have hv1 : p.getVert (L - 1 + 1) = v := by rw [show L - 1 + 1 = L by omega]; exact hv
  have hv2 : p.getVert (L - 2 + 1) = p.getVert (L - 1) := by congr 1; omega
  have he1 : p.reverse.getVert 1 - v = -ℓ (L - 1) := by
    rw [Walk.getVert_reverse]; simp only [hℓ, hv1]; abel
  have he2 : p.reverse.getVert 2 - v = -ℓ (L - 1) + -ℓ (L - 2) := by
    rw [Walk.getVert_reverse]; simp only [hℓ, hv1, hv2]; abel
  rw [he1, he2] at h2
  have hd2 := W2 (L - 1) (L - 2) (by omega) (by omega) (by omega)
  have hc2 := cfg4_of_fail S hS0 hsym h4 (hsym _ (hℓS (L - 1) (by omega)))
    (hsym _ (hℓS (L - 2) (by omega))) (N2.neg hsym hd2).1 (N2.neg hsym hd2).2 h2
  have hC2 := cabc_of_cfg4 hsym (hsym _ (hℓS (L - 1) (by omega))) (hsym _ (hℓS (L - 3) (by omega)))
    (N2.neg hsym (W2 (L - 1) (L - 3) (by omega) (by omega) (by omega)))
    (N2.neg hsym (W2 (L - 2) (L - 3) (by omega) (by omega) (by omega)))
    (N3.neg hsym (W3 (L - 1) (L - 2) (L - 3) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega))) hc2
  have hC1' : CABC S (- -ℓ 0) (- -ℓ 1) := by simpa only [neg_neg] using hC1
  rcases Nat.lt_or_ge L 4 with hL4 | hL4
  · -- L = 3
    have hL3 : L = 3 := by omega
    have e1 : L - 1 = 2 := by omega
    have e2 : L - 2 = 1 := by omega
    rw [e1, e2] at hC2
    have hab := W2 0 1 (by omega) (by omega) (by omega)
    have had := W2 0 2 (by omega) (by omega) (by omega)
    have hbd := W2 1 2 (by omega) (by omega) (by omega)
    have habd := W3 0 1 2 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    have haS := hℓS 0 (by omega)
    have hbS := hℓS 1 (by omega)
    have hdS := hℓS 2 (by omega)
    rcases hC1 with hA | hB
    · exact pairA3 hsym h4 haS hbS hdS hab had hbd habd hA hC2
    rcases hC2 with hA' | hB'
    · have := pairA3 hsym h4 (hsym _ hdS) (hsym _ hbS) (hsym _ haS)
        (N2.neg hsym (W2 2 1 (by omega) (by omega) (by omega)))
        (N2.neg hsym (W2 2 0 (by omega) (by omega) (by omega)))
        (N2.neg hsym (W2 1 0 (by omega) (by omega) (by omega)))
        (N3.neg hsym (W3 2 1 0 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)))
        hA' (by simpa only [neg_neg] using (Or.inr hB : CABC S (ℓ 0) (ℓ 1)))
      exact this
    · exact pairB_3 hsym haS hbS hdS had habd hB hB'
  · -- L ≥ 4
    have haS := hℓS 0 (by omega)
    have hbS := hℓS 1 (by omega)
    have hcS := hℓS (L - 2) (by omega)
    have hdS := hℓS (L - 1) (by omega)
    have heS := hℓS (L - 3) (by omega)
    have hfS := hℓS 2 (by omega)
    rcases hC1 with hA | hB1 | hB2
    · exact pairA4 hsym hcS hdS heS (W2 0 (L - 2) (by omega) (by omega) (by omega))
        (W2 0 (L - 1) (by omega) (by omega) (by omega)) (W2 0 (L - 3) (by omega) (by omega) (by omega))
        (W2 (L - 2) (L - 1) (by omega) (by omega) (by omega))
        (W2 (L - 3) (L - 1) (by omega) (by omega) (by omega))
        (W3 (L - 3) (L - 2) (L - 1) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega))
        hA hC2
    all_goals rcases hC2 with hA' | hB1' | hB2'
    · exact pairA4 hsym (hsym _ hbS) (hsym _ haS) (hsym _ hfS)
        (N2.neg hsym (W2 (L - 1) 1 (by omega) (by omega) (by omega)))
        (N2.neg hsym (W2 (L - 1) 0 (by omega) (by omega) (by omega)))
        (N2.neg hsym (W2 (L - 1) 2 (by omega) (by omega) (by omega)))
        (N2.neg hsym (W2 1 0 (by omega) (by omega) (by omega)))
        (N2.neg hsym (W2 2 0 (by omega) (by omega) (by omega)))
        (N3.neg hsym (W3 2 1 0 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)))
        hA' (by simpa only [neg_neg] using (Or.inr (Or.inl hB1) : CABC S (ℓ 0) (ℓ 1)))
    · exact pairB1B1_4 hsym h4 haS hdS (W2 0 (L - 1) (by omega) (by omega) (by omega))
        (W3 0 1 (L - 1) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega))
        (W3 0 (L - 2) (L - 1) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega))
        hB1 hB1'
    · exact pairB1B2_4 hcS hdS (W2 0 (L - 2) (by omega) (by omega) (by omega))
        (W2 0 (L - 1) (by omega) (by omega) (by omega))
        (W3 0 1 (L - 2) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega))
        (W3 0 1 (L - 1) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega))
        hB1 hB2'
    · exact pairA4 hsym (hsym _ hbS) (hsym _ haS) (hsym _ hfS)
        (N2.neg hsym (W2 (L - 1) 1 (by omega) (by omega) (by omega)))
        (N2.neg hsym (W2 (L - 1) 0 (by omega) (by omega) (by omega)))
        (N2.neg hsym (W2 (L - 1) 2 (by omega) (by omega) (by omega)))
        (N2.neg hsym (W2 1 0 (by omega) (by omega) (by omega)))
        (N2.neg hsym (W2 2 0 (by omega) (by omega) (by omega)))
        (N3.neg hsym (W3 2 1 0 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)))
        hA' (by simpa only [neg_neg] using (Or.inr (Or.inr hB2) : CABC S (ℓ 0) (ℓ 1)))
    · exact pairB1B2_4 (hsym _ hbS) (hsym _ haS)
        (N2.neg hsym (W2 (L - 1) 1 (by omega) (by omega) (by omega)))
        (N2.neg hsym (W2 (L - 1) 0 (by omega) (by omega) (by omega)))
        (N3.neg hsym (W3 (L - 1) (L - 2) 1 (by omega) (by omega) (by omega) (by omega) (by omega)
          (by omega)))
        (N3.neg hsym (W3 (L - 1) (L - 2) 0 (by omega) (by omega) (by omega) (by omega) (by omega)
          (by omega)))
        hB1' (by simpa only [neg_neg] using hB2)
    · exact pairB2B2_4 hcS hdS (W2 0 (L - 2) (by omega) (by omega) (by omega))
        (W2 0 (L - 1) (by omega) (by omega) (by omega)) (W2 1 (L - 2) (by omega) (by omega) (by omega))
        (W2 1 (L - 1) (by omega) (by omega) (by omega))
        (w4 S G hG hc p hp (i := 0) (j := 1) (k := L - 2) (l := L - 1) (by omega) (by omega)
          (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega))
        hB2 hB2'

include hG in
lemma chain_av {T : Set A} {g : A} (hgS : g ∈ S) (x : A) (k₀ : ℕ) :
    ∀ k₁, k₀ ≤ k₁ → (∀ k, k₀ ≤ k → k ≤ k₁ → x + k • g ∉ T) →
      Av G T (x + k₀ • g) (x + k₁ • g) := by
  intro k₁ hk
  induction k₁, hk using Nat.le_induction with
  | base => intro h; exact av_refl (h k₀ le_rfl le_rfl)
  | succ n hn ih =>
    intro h
    refine av_trans (ih fun k h1 h2 => h k h1 (by omega))
      (av_adj ?_ (h n hn (by omega)) (h (n + 1) (by omega) le_rfl))
    exact (hG _ _).2 (by rw [show x + (n + 1) • g - (x + n • g) = g by rw [succ_nsmul]; abel]
                         exact hgS)

omit [DecidableEq A] in
lemma nsmul_inj_lt [Finite A] {g : A} {j k : ℕ} (hj : j < addOrderOf g) (hk : k < addOrderOf g)
    (h : j • g = k • g) : j = k :=
  nsmul_injOn_Iio_addOrderOf hj hk h

omit [DecidableEq A] in
lemma nsmul_sub_eq [Finite A] (g : A) {k : ℕ} (hk : k ≤ addOrderOf g) :
    (addOrderOf g - k) • g = -(k • g) := by
  have h := addOrderOf_nsmul_eq_zero g
  rw [← Nat.sub_add_cancel hk, add_nsmul] at h
  exact eq_neg_of_add_eq_zero_left h

include hG in
/-- A neighbour of `u` off a geodesic, written `u + w`: `w ∈ S` and `u + w ∉ support`. -/
lemma av_cycle [Finite A] {T : Set A} {g u : A} (hgS : g ∈ S) {k₀ k₁ : ℕ} (hk : k₀ ≤ k₁)
    (hk1 : k₁ < addOrderOf g) (hT : ∀ k, k₀ ≤ k → k ≤ k₁ → u + k • g ∉ T) :
    Av G T (u + k₀ • g) (u + k₁ • g) :=
  chain_av S G hG hgS u k₀ k₁ hk hT

include hG in
/-- Degree 4, short geodesics: the start condition holds at the first vertex. -/
theorem startAt_short [Finite A] (h4 : S.card = 4) {u v : A} (p : G.Walk u v)
    (hp : p.length = G.dist u v) (hL : p.length ≤ 2) : StartAt G p := by
  classical
  have hS0 := zero_notMem_of S G hG
  have hsym := neg_mem_of S G hG
  by_cases hf : Fail4 S (p.getVert 1 - u) (p.getVert 2 - u)
  swap
  · exact startAt_of_not_fail4 S G hG h4 p hp hf
  -- support description
  have hsupp : ∀ z ∈ p.support, z = u ∨ z = p.getVert 1 ∨ z = p.getVert 2 := by
    intro z hz
    obtain ⟨n, hn, hnl⟩ := Walk.mem_support_iff_exists_getVert.1 hz
    have hn2 : n ≤ 2 := by omega
    interval_cases n
    · left; rw [← hn, Walk.getVert_zero]
    · right; left; exact hn.symm
    · right; right; exact hn.symm
  have hadj : ∀ w, G.Adj u w → w - u ∈ S := fun w h => (hG _ _).1 h
  intro a b ha hb ha' hb'
  rcases Nat.lt_or_ge p.length 1 with hl0 | hl1
  · -- length 0: no failure
    exfalso
    have h0 : p.length = 0 := by omega
    have e1 : p.getVert 1 = v := p.getVert_of_length_le (by omega)
    have e2 : p.getVert 2 = v := p.getVert_of_length_le (by omega)
    have euv : u = v := Walk.eq_of_length_eq_zero h0
    rw [e1, e2, ← euv, sub_self] at hf
    obtain ⟨x, hxN, hx⟩ := hf
    have hxS := (Finset.mem_erase.1 hxN).2
    have h3 : 1 < (S.erase x).card := by rw [Finset.card_erase_of_mem hxS, h4]; omega
    obtain ⟨y, hy, z, hz, hyz⟩ := Finset.one_lt_card.1 h3
    have hy' := Finset.mem_erase.1 hy
    have hz' := Finset.mem_erase.1 hz
    have ey := hx y (Finset.mem_erase.2 ⟨fun h => hS0 (h ▸ hy'.2), hy'.2⟩) hy'.1
    have ez := hx z (Finset.mem_erase.2 ⟨fun h => hS0 (h ▸ hz'.2), hz'.2⟩) hz'.1
    have ey' : x + y = 0 := by rcases ey with e | e | e <;> exact e
    have ez' : x + z = 0 := by rcases ez with e | e | e <;> exact e
    exact hyz (by linear_combination (norm := module) ey' - ez')
  set g := p.getVert 1 - u with hgdef
  have hg1 : p.getVert 1 = u + g := by rw [hgdef]; abel
  have hgS : g ∈ S := by
    have h := p.adj_getVert_succ (i := 0) (by omega)
    rw [Walk.getVert_zero] at h
    exact hadj _ h
  have hg1mem : u + g ∈ p.support := hg1 ▸ p.getVert_mem_support 1
  have hag : a - u ≠ g := fun e => ha' (by rw [show a = u + g by rw [← e]; abel]; exact hg1mem)
  have hbg : b - u ≠ g := fun e => hb' (by rw [show b = u + g by rw [← e]; abel]; exact hg1mem)
  have hn0 : 0 < addOrderOf g := addOrderOf_pos g
  -- reduce to: every neighbour off the path is joined to a fixed vertex `c0`
  suffices key : ∃ c0, ∀ w, G.Adj u w → w ∉ p.support → Av G {z | z ∈ p.support} w c0 by
    obtain ⟨c0, hc0⟩ := key
    exact av_trans (hc0 a ha ha') (av_symm (hc0 b hb hb'))
  rcases Nat.lt_or_ge p.length 2 with hl1' | hl2
  · -- length 1: configuration (A)
    have e2 : p.getVert 2 = p.getVert 1 := by
      rw [p.getVert_of_length_le (by omega), p.getVert_of_length_le (by omega)]
    rw [e2] at hf hsupp
    obtain ⟨h2S, hcov⟩ := cfgA_of_fail1 hS0 hsym h4 hgS hf
    set n := addOrderOf g with hn
    have hn5 : 5 ≤ n := by
      by_contra hlt
      have hng := addOrderOf_nsmul_eq_zero g
      rw [← hn] at hng
      interval_cases n
      · exact hS0 (by rw [← one_nsmul g, hng] at hgS; exact hgS)
      · exact hS0 (by rw [two_nsmul] at hng; rw [← hng]; exact h2S)
      · have hm : g + g = -g := by
          have : (3 : ℕ) • g = 0 := hng
          rw [succ_nsmul, two_nsmul] at this; exact eq_neg_of_add_eq_zero_left this
        have : S.card ≤ 3 := card_le_three_of_cover (p₁ := g) (p₂ := -g) (p₃ := -g) (by
          intro w hw
          rcases hcov w hw with e | e | e | e
          · exact Or.inl e
          · exact Or.inr (Or.inl e)
          · exact Or.inr (Or.inl (e.trans hm))
          · exact Or.inl (by rw [e, hm, neg_neg]))
        omega
      · have hm : g + g = -(g + g) := by
          have : (4 : ℕ) • g = 0 := hng
          rw [show (4 : ℕ) • g = (g + g) + (g + g) by simp [succ_nsmul] <;> abel] at this
          exact eq_neg_of_add_eq_zero_left this
        have : S.card ≤ 3 := card_le_three_of_cover (p₁ := g) (p₂ := -g) (p₃ := g + g) (by
          intro w hw
          rcases hcov w hw with e | e | e | e
          · exact Or.inl e
          · exact Or.inr (Or.inl e)
          · exact Or.inr (Or.inr e)
          · exact Or.inr (Or.inr (e.trans hm.symm)))
        omega
    have hT : ∀ k, 2 ≤ k → k ≤ n - 1 → u + k • g ∉ ({z | z ∈ p.support} : Set A) := by
      intro k hk2 hk hmem
      rcases hsupp _ hmem with e | e | e
      · have : k • g = 0 • g := by rw [zero_nsmul]; linear_combination (norm := module) e
        have := nsmul_inj_lt (by omega) hn0 this; omega
      · rw [hg1] at e
        have : k • g = 1 • g := by rw [one_nsmul]; linear_combination (norm := module) e
        have := nsmul_inj_lt (by omega) (by omega) this; omega
      · rw [hg1] at e
        have : k • g = 1 • g := by rw [one_nsmul]; linear_combination (norm := module) e
        have := nsmul_inj_lt (by omega) (by omega) this; omega
    refine ⟨u + (n - 1) • g, fun w hw hw' => ?_⟩
    have hwS := hadj w hw
    have hwg : w - u ≠ g := fun e => hw' (by rw [show w = u + g by rw [← e]; abel]; exact hg1mem)
    rcases hcov _ hwS with e | e | e | e
    · exact absurd e hwg
    · have : w = u + (n - 1) • g := by
        rw [nsmul_sub_eq g (by omega), one_nsmul, ← e]; abel
      rw [this]; exact av_refl (hT _ (by omega) le_rfl)
    · have : w = u + 2 • g := by rw [two_nsmul, ← e]; abel
      rw [this]; exact av_cycle S G hG hgS (by omega) (by omega) (fun k h1 h2 => hT k h1 h2)
    · have : w = u + (n - 2) • g := by rw [nsmul_sub_eq g (by omega), two_nsmul, ← e]; abel
      rw [this]; exact av_cycle S G hG hgS (by omega) (by omega) (fun k h1 h2 => hT k (by omega) h2)
  · -- length 2
    have hL2 : p.length = 2 := by omega
    set q := p.getVert 2 - p.getVert 1 with hqdef
    have hg2 : p.getVert 2 = u + g + q := by rw [hqdef, hgdef]; abel
    have hqS : q ∈ S := (hG _ _).1 (p.adj_getVert_succ (i := 1) (by omega))
    have hd2 : G.dist u (p.getVert 2) = 2 := by
      have := dist_getVert p hp (i := 0) (j := 2) (by omega) (by omega)
      rwa [Walk.getVert_zero] at this
    have hr : g + q ∉ S := by
      intro h
      have : G.Adj u (p.getVert 2) := (hG _ _).2 (by rw [hg2]; simpa [add_assoc] using h)
      rw [dist_eq_one_iff_adj.2 this] at hd2; omega
    have hr0 : g + q ≠ 0 := by
      intro h
      have : p.getVert 2 = u := by rw [hg2, add_assoc, h, add_zero]
      rw [this, SimpleGraph.dist_self] at hd2; omega
    have hf' : Fail4 S g (g + q) := by
      rw [show g + q = p.getVert 2 - u by rw [hg2]; abel]; exact hf
    have hsupp' : ∀ z ∈ p.support, z = u ∨ z = u + g ∨ z = u + g + q := by
      intro z hz
      rcases hsupp z hz with e | e | e
      · exact Or.inl e
      · exact Or.inr (Or.inl (e.trans hg1))
      · exact Or.inr (Or.inr (e.trans hg2))
    have hcf := cfg4_of_fail S hS0 hsym h4 hgS hqS hr hr0 hf'
    -- configurations (A) and (K): S = {±g, ±2g}, q = 2g
    have caseA : g + g ∈ S → (∀ w ∈ S, w = g ∨ w = -g ∨ w = g + g ∨ w = -(g + g)) →
        ∃ c0, ∀ w, G.Adj u w → w ∉ p.support → Av G {z | z ∈ p.support} w c0 := by
      intro h2S hcov
      have hq2 : q = g + g := by
        rcases hcov q hqS with e | e | e | e
        · exact (hr (by rw [e]; exact h2S)).elim
        · exact (hr0 (by rw [e]; abel)).elim
        · exact e
        · exact (hr (by rw [show g + q = -g by rw [e]; abel]; exact hsym g hgS)).elim
      set n := addOrderOf g with hn
      have hn6 : 6 ≤ n := by
        by_contra hlt
        have hng := addOrderOf_nsmul_eq_zero g
        rw [← hn] at hng
        interval_cases n
        · exact hS0 (by rw [← one_nsmul g, hng] at hgS; exact hgS)
        · exact hS0 (by rw [two_nsmul] at hng; rw [← hng]; exact h2S)
        · have hm : g + g = -g := by
            have : (3 : ℕ) • g = 0 := hng
            rw [succ_nsmul, two_nsmul] at this; exact eq_neg_of_add_eq_zero_left this
          have : S.card ≤ 3 := card_le_three_of_cover (p₁ := g) (p₂ := -g) (p₃ := -g) (by
            intro w hw
            rcases hcov w hw with e | e | e | e
            · exact Or.inl e
            · exact Or.inr (Or.inl e)
            · exact Or.inr (Or.inl (e.trans hm))
            · exact Or.inl (by rw [e, hm, neg_neg]))
          omega
        · have hm : g + g = -(g + g) := by
            have : (4 : ℕ) • g = 0 := hng
            rw [show (4 : ℕ) • g = (g + g) + (g + g) by simp [succ_nsmul] <;> abel] at this
            exact eq_neg_of_add_eq_zero_left this
          have : S.card ≤ 3 := card_le_three_of_cover (p₁ := g) (p₂ := -g) (p₃ := g + g) (by
            intro w hw
            rcases hcov w hw with e | e | e | e
            · exact Or.inl e
            · exact Or.inr (Or.inl e)
            · exact Or.inr (Or.inr e)
            · exact Or.inr (Or.inr (e.trans hm.symm)))
          omega
        · have h5 : (5 : ℕ) • g = 0 := hng
          exact hr (by
            rw [show g + q = -(g + g) by
              rw [hq2, show (5 : ℕ) • g = g + g + g + g + g by simp [succ_nsmul] <;> abel] at *
              linear_combination (norm := module) h5]
            exact hsym _ h2S)
      have hT : ∀ k, 4 ≤ k → k ≤ n - 1 → u + k • g ∉ ({z | z ∈ p.support} : Set A) := by
        intro k hk4 hk hmem
        rcases hsupp' _ hmem with e | e | e
        · have : k • g = 0 • g := by rw [zero_nsmul]; linear_combination (norm := module) e
          have := nsmul_inj_lt (by omega) hn0 this; omega
        · have : k • g = 1 • g := by rw [one_nsmul]; linear_combination (norm := module) e
          have := nsmul_inj_lt (by omega) (by omega) this; omega
        · have : k • g = 3 • g := by
            rw [show (3 : ℕ) • g = g + g + g by simp [succ_nsmul] <;> abel]
            rw [hq2] at e; linear_combination (norm := module) e
          have := nsmul_inj_lt (by omega) (by omega) this; omega
      refine ⟨u + (n - 1) • g, fun w hw hw' => ?_⟩
      have hwS := hadj w hw
      have hwg : w - u ≠ g := fun e => hw' (by rw [show w = u + g by rw [← e]; abel]; exact hg1mem)
      rcases hcov _ hwS with e | e | e | e
      · exact absurd e hwg
      · have : w = u + (n - 1) • g := by rw [nsmul_sub_eq g (by omega), one_nsmul, ← e]; abel
        rw [this]; exact av_refl (hT _ (by omega) le_rfl)
      · have h24 : G.Adj w (u + 4 • g) := (hG _ _).2 (by
          rw [show u + 4 • g - w = g + g by
            rw [show (4 : ℕ) • g = g + g + g + g by simp [succ_nsmul] <;> abel,
              show w = u + (g + g) by rw [← e]; abel]; abel]
          exact h2S)
        exact av_trans (av_adj h24 hw' (hT 4 le_rfl (by omega)))
          (av_cycle S G hG hgS (by omega) (by omega) (fun k h1 h2 => hT k h1 h2))
      · have : w = u + (n - 2) • g := by rw [nsmul_sub_eq g (by omega), two_nsmul, ← e]; abel
        rw [this]; exact av_cycle S G hG hgS (by omega) (by omega) (fun k h1 h2 => hT k (by omega) h2)
    rcases hcf with ⟨h2S, hcov⟩ | ⟨hqg, h3S, hcov⟩ | ⟨h22, hqg, hqng, hcov⟩ |
        ⟨hgg, x, h4x, hqx, hxS, hx2S, hcov⟩ | ⟨-, -, h2S, hcov⟩
    · exact caseA h2S hcov
    · -- (B1): q = g, S = {±g, ±3g}
      set n := addOrderOf g with hn
      have hn6 : 6 ≤ n := by
        by_contra hlt
        have hng := addOrderOf_nsmul_eq_zero g
        rw [← hn] at hng
        interval_cases n
        · exact hS0 (by rw [← one_nsmul g, hng] at hgS; exact hgS)
        · exact hr0 (by rw [hqg, ← two_nsmul]; exact hng)
        · exact hS0 (by
            rw [show (3 : ℕ) • g = g + g + g by simp [succ_nsmul] <;> abel] at hng
            rw [← hng]; exact h3S)
        · have hm : g + g + g = -g := by
            have : (4 : ℕ) • g = 0 := hng
            rw [show (4 : ℕ) • g = (g + g + g) + g by simp [succ_nsmul] <;> abel] at this
            exact eq_neg_of_add_eq_zero_left this
          have : S.card ≤ 3 := card_le_three_of_cover (p₁ := g) (p₂ := -g) (p₃ := -g) (by
            intro w hw
            rcases hcov w hw with e | e | e | e
            · exact Or.inl e
            · exact Or.inr (Or.inl e)
            · exact Or.inr (Or.inl (e.trans hm))
            · exact Or.inl (by rw [e, hm, neg_neg]))
          omega
        · have h5 : (5 : ℕ) • g = 0 := hng
          exact hr (by
            rw [show g + q = -(g + g + g) by
              rw [hqg, show (5 : ℕ) • g = g + g + g + g + g by simp [succ_nsmul] <;> abel] at *
              linear_combination (norm := module) h5]
            exact hsym _ h3S)
      have hT : ∀ k, 3 ≤ k → k ≤ n - 1 → u + k • g ∉ ({z | z ∈ p.support} : Set A) := by
        intro k hk3 hk hmem
        rcases hsupp' _ hmem with e | e | e
        · have : k • g = 0 • g := by rw [zero_nsmul]; linear_combination (norm := module) e
          have := nsmul_inj_lt (by omega) hn0 this; omega
        · have : k • g = 1 • g := by rw [one_nsmul]; linear_combination (norm := module) e
          have := nsmul_inj_lt (by omega) (by omega) this; omega
        · have : k • g = 2 • g := by
            rw [two_nsmul]; rw [hqg] at e; linear_combination (norm := module) e
          have := nsmul_inj_lt (by omega) (by omega) this; omega
      refine ⟨u + (n - 1) • g, fun w hw hw' => ?_⟩
      have hwS := hadj w hw
      have hwg : w - u ≠ g := fun e => hw' (by rw [show w = u + g by rw [← e]; abel]; exact hg1mem)
      rcases hcov _ hwS with e | e | e | e
      · exact absurd e hwg
      · have : w = u + (n - 1) • g := by rw [nsmul_sub_eq g (by omega), one_nsmul, ← e]; abel
        rw [this]; exact av_refl (hT _ (by omega) le_rfl)
      · have : w = u + 3 • g := by
          rw [show (3 : ℕ) • g = g + g + g by simp [succ_nsmul] <;> abel, ← e]; abel
        rw [this]; exact av_cycle S G hG hgS (by omega) (by omega) (fun k h1 h2 => hT k h1 h2)
      · have : w = u + (n - 3) • g := by
          rw [nsmul_sub_eq g (by omega), show (3 : ℕ) • g = g + g + g by simp [succ_nsmul] <;> abel,
            ← e]; abel
        rw [this]; exact av_cycle S G hG hgS (by omega) (by omega) (fun k h1 h2 => hT k (by omega) h2)
    · -- (B2): pairs
      set c := g + q with hcdef
      have hcc : c + c = 0 := by rw [hcdef]; linear_combination (norm := module) h22
      have hgng : g ≠ -g := by
        intro e
        have : S.card ≤ 3 := card_le_three_of_cover (p₁ := g) (p₂ := q) (p₃ := -q) (by
          intro w hw
          rcases hcov w hw with f | f | f | f
          · exact Or.inl f
          · exact Or.inl (f.trans e.symm)
          · exact Or.inr (Or.inl f)
          · exact Or.inr (Or.inr f))
        omega
      have hex : ∃ k, 0 < k ∧ (k • g = 0 ∨ k • g = c) :=
        ⟨addOrderOf g, addOrderOf_pos g, Or.inl (addOrderOf_nsmul_eq_zero g)⟩
      set m := Nat.find hex with hmdef
      have hm : 0 < m ∧ (m • g = 0 ∨ m • g = c) := Nat.find_spec hex
      have hmin : ∀ k, 0 < k → k < m → k • g ≠ 0 ∧ k • g ≠ c := fun k hk hkm => by
        have h := Nat.find_min hex hkm
        exact ⟨fun e => h ⟨hk, Or.inl e⟩, fun e => h ⟨hk, Or.inr e⟩⟩
      have hm3 : 3 ≤ m := by
        by_contra hlt
        rcases (show m = 1 ∨ m = 2 by omega) with h1 | h1 <;> rw [h1] at hm
        · rcases hm.2 with e | e <;> rw [one_nsmul] at e
          · exact hS0 (e ▸ hgS)
          · exact (hS0 (by have : q = 0 := by rw [hcdef] at e; linear_combination (norm := module) -e
                           rw [← this]; exact hqS)).elim
        · rcases hm.2 with e | e <;> rw [two_nsmul] at e
          · exact hgng (eq_neg_of_add_eq_zero_left e)
          · exact hqg (by rw [hcdef] at e; linear_combination (norm := module) -e)
      have hoff : ∀ k ε, 1 ≤ k → k < m → (ε = 0 ∨ ε = c) → (k = 1 → ε = c) →
          u + k • g + ε ∉ ({z | z ∈ p.support} : Set A) := by
        intro k ε hk1 hkm hε hk1c hmem
        rcases hsupp' _ hmem with e | e | e
        · rcases hε with rfl | rfl
          · exact (hmin k (by omega) hkm).1 (by linear_combination (norm := module) e)
          · exact (hmin k (by omega) hkm).2 (by linear_combination (norm := module) e - hcc)
        · rcases Nat.lt_or_ge k 2 with hk | hk
          · have hk' : k = 1 := by omega
            have hεc := hk1c hk'
            rw [hk', one_nsmul, hεc] at e
            exact hr0 (by linear_combination (norm := module) e)
          · have hk1' : (k - 1) • g + g = k • g := by rw [← succ_nsmul]; congr 1; omega
            rcases hε with rfl | rfl
            · exact (hmin (k - 1) (by omega) (by omega)).1 (by
                linear_combination (norm := module) e + hk1')
            · exact (hmin (k - 1) (by omega) (by omega)).2 (by
                linear_combination (norm := module) e + hk1' - hcc)
        · rcases hε with rfl | rfl
          · exact (hmin k (by omega) hkm).2 (by linear_combination (norm := module) e - hcdef)
          · exact (hmin k (by omega) hkm).1 (by linear_combination (norm := module) e - hcdef)
      have hnq : -q ∈ S := hsym q hqS
      have hclaim : ∀ k, 1 ≤ k → k < m → ∀ ε, (ε = 0 ∨ ε = c) → (k = 1 → ε = c) →
          Av G {z | z ∈ p.support} (u + 1 • g + c) (u + k • g + ε) := by
        intro k hk
        induction k, hk using Nat.le_induction with
        | base =>
          intro _ ε _ hεc
          rw [hεc rfl]
          exact av_refl (hoff 1 c le_rfl (by omega) (Or.inr rfl) (fun _ => rfl))
        | succ k hk ih =>
          intro hkm ε hε _
          have h1 := ih (by omega) c (Or.inr rfl) (fun _ => rfl)
          refine av_trans h1 (av_adj ?_ (hoff k c hk (by omega) (Or.inr rfl) (fun _ => rfl))
            (hoff (k + 1) ε (by omega) hkm hε (fun h => by omega)))
          rcases hε with rfl | rfl
          · exact (hG _ _).2 (by
              rw [show u + (k + 1) • g + 0 - (u + k • g + c) = -q by
                rw [succ_nsmul]; linear_combination (norm := module) -hcdef]
              exact hnq)
          · exact (hG _ _).2 (by
              rw [show u + (k + 1) • g + c - (u + k • g + c) = g by rw [succ_nsmul]; abel]
              exact hgS)
      have hmm : (m - 1) • g + g = m • g := by rw [← succ_nsmul]; congr 1; omega
      refine ⟨u + 1 • g + c, fun w hw hw' => ?_⟩
      have hwS := hadj w hw
      have hwg : w - u ≠ g := fun e => hw' (by rw [show w = u + g by rw [← e]; abel]; exact hg1mem)
      apply av_symm
      rcases hcov _ hwS with e | e | e | e
      · exact absurd e hwg
      · rcases hm.2 with f | f
        · have : w = u + (m - 1) • g + 0 := by linear_combination (norm := module) e - hmm - f
          rw [this]; exact hclaim (m - 1) (by omega) (by omega) 0 (Or.inl rfl) (fun h => by omega)
        · have : w = u + (m - 1) • g + c := by linear_combination (norm := module) e - hmm - f - hcc
          rw [this]; exact hclaim (m - 1) (by omega) (by omega) c (Or.inr rfl) (fun _ => rfl)
      · rcases hm.2 with f | f
        · have : w = u + (m - 1) • g + c := by
            linear_combination (norm := module) e - hmm - f - hcdef
          rw [this]; exact hclaim (m - 1) (by omega) (by omega) c (Or.inr rfl) (fun _ => rfl)
        · have : w = u + (m - 1) • g + 0 := by
            linear_combination (norm := module) e - hmm - f - hcdef
          rw [this]; exact hclaim (m - 1) (by omega) (by omega) 0 (Or.inl rfl) (fun h => by omega)
      · have : w = u + 1 • g + c := by linear_combination (norm := module) e + hcdef - hcc
        rw [this]; exact av_refl (hoff 1 c le_rfl (by omega) (Or.inr rfl) (fun _ => rfl))
    · -- (β2): local three-step routes
      have hx0 : x ≠ 0 := fun e => hS0 (e ▸ hxS)
      have h2x : x + x ≠ 0 := by
        intro e
        have : S.card ≤ 3 := card_le_three_of_cover (p₁ := g) (p₂ := x) (p₃ := -x) (by
          intro w hw
          rcases hcov w hw with f | f | f | f
          · exact Or.inl f
          · exact Or.inr (Or.inl f)
          · exact Or.inr (Or.inr f)
          · exact Or.inl (by rw [f]; linear_combination (norm := module) -e))
        omega
      have hy1 : u + x + g ∉ ({z | z ∈ p.support} : Set A) := by
        intro hmem
        rcases hsupp' _ hmem with e | e | e
        · exact hr0 (by linear_combination (norm := module) -e + hgg + hqx)
        · exact hx0 (by linear_combination (norm := module) e)
        · exact h2x (by linear_combination (norm := module) e + hqx)
      have hy2 : u + g - x - x - x ∉ ({z | z ∈ p.support} : Set A) := by
        intro hmem
        rcases hsupp' _ hmem with e | e | e
        · exact hr0 (by linear_combination (norm := module) -e - h4x + hqx + hgg)
        · exact hx0 (by linear_combination (norm := module) e + h4x)
        · exact h2x (by linear_combination (norm := module) -e - hqx)
      have hc0 : u + -x ∉ ({z | z ∈ p.support} : Set A) := by
        intro hmem
        rcases hsupp' _ hmem with e | e | e
        · exact hx0 (by linear_combination (norm := module) -e)
        · exact hr0 (by linear_combination (norm := module) e + hqx + hgg)
        · exact (hS0 (by have : g = 0 := by linear_combination (norm := module) -e - hqx
                         rw [← this]; exact hgS)).elim
      refine ⟨u + -x, fun w hw hw' => ?_⟩
      have hwS := hadj w hw
      have hwg : w - u ≠ g := fun e => hw' (by rw [show w = u + g by rw [← e]; abel]; exact hg1mem)
      rcases hcov _ hwS with e | e | e | e
      · exact absurd e hwg
      · have hw1 : w = u + x := by rw [← e]; abel
        refine av_trans (av_adj ?_ hw' hy1) (av_adj ?_ hy1 hc0)
        · exact (hG _ _).2 (by rw [hw1, show u + x + g - (u + x) = g by abel]; exact hgS)
        · exact (hG _ _).2 (by
            rw [show u + -x - (u + x + g) = g - x - x by linear_combination (norm := module) -hgg]
            exact hx2S)
      · have : w = u + -x := by rw [← e]; abel
        rw [this]; exact av_refl hc0
      · have hw1 : w = u + (g - x - x) := by rw [← e]; abel
        apply av_symm
        refine av_trans (av_adj ?_ hc0 hy2) (av_adj ?_ hy2 hw')
        · exact (hG _ _).2 (by
            rw [show u + g - x - x - x - (u + -x) = g - x - x by abel]; exact hx2S)
        · exact (hG _ _).2 (by
            rw [hw1, show u + (g - x - x) - (u + g - x - x - x) = x by abel]; exact hxS)
    · exact caseA h2S hcov

include hG in
theorem startCond_of_card (h8 : 8 ≤ S.card) : StartCond G := by
  intro u v p hp a b ha hb ha' hb'
  have hs : a - u ∈ S := (hG u a).1 ha
  have ht : b - u ∈ S := (hG u b).1 hb
  have hne : ∀ x, G.Adj u x → x ∉ p.support → x - u ≠ p.getVert 1 - u := by
    intro x hx hx' e
    apply hx'
    rw [show x = p.getVert 1 by simpa using e]
    exact p.getVert_mem_support 1
  have hsE : a - u ∈ S.erase (p.getVert 1 - u) := Finset.mem_erase.2 ⟨hne a ha ha', hs⟩
  have htE : b - u ∈ S.erase (p.getVert 1 - u) := Finset.mem_erase.2 ⟨hne b hb hb', ht⟩
  have := av_of_chain S G hG u v p hp (a - u) hsE (b - u)
    (core_card S h8 (p.getVert 1 - u) (p.getVert 2 - u) _ hsE _ htE)
  simpa using this

include hG in
lemma nb_of_card (h2 : 2 ≤ S.card) : ∀ (u v : A) (p : G.Walk u v), p.length = G.dist u v →
    ∃ a, G.Adj u a ∧ a ∉ p.support := by
  intro u v p hp
  have : 1 ≤ (S.erase (p.getVert 1 - u)).card := by
    have := Finset.pred_card_le_card_erase (s := S) (a := p.getVert 1 - u)
    omega
  obtain ⟨s, hs⟩ := Finset.card_pos.1 this
  rw [Finset.mem_erase] at hs
  have hadj : G.Adj u (u + s) := (hG _ _).2 (by simpa using hs.2)
  refine ⟨u + s, hadj, fun hmem => hs.1 ?_⟩
  have h1 := eq_getVert_dist p hp hmem
  rw [dist_eq_one_iff_adj.2 hadj] at h1
  rw [← h1]; abel

include hG in
/-- **Geodesic Deletion for abelian Cayley graphs of degree at least 8** (any abelian group). -/
theorem gd_abelian_card_ge_eight (hc : G.Connected) (h8 : 8 ≤ S.card) :
    ∀ (u v : A) (p : G.Walk u v), p.IsPath → p.length = G.dist u v →
      (G.induce {x | x ∉ p.support}).Connected :=
  gd_of_startCond hc (startCond_of_card S G hG h8) (nb_of_card S G hG (by omega))

include hG in
/-- **Geodesic Deletion for Cayley graphs of finite abelian groups of degree at least 5.** -/
theorem gd_abelian_card_ge_five [Finite A] (hc : G.Connected) (h5 : 5 ≤ S.card) :
    ∀ (u v : A) (p : G.Walk u v), p.IsPath → p.length = G.dist u v →
      (G.induce {x | x ∉ p.support}).Connected :=
  gd_of_startCond hc (startCond_of_card_five S G hG h5) (nb_of_card S G hG (by omega))

/-! ### Degrees 2 and 3 -/

include hG in
/-- At the start of a geodesic of length ≥ 1, if the two other neighbours are adjacent or joined
in two steps, the start condition holds (any degree, used for degree 3). -/
theorem startAt_of_pair {u v : A} (p : G.Walk u v) (hp : p.length = G.dist u v)
    (hok : ∀ s ∈ S.erase (p.getVert 1 - u), ∀ t ∈ S.erase (p.getVert 1 - u), s ≠ t →
      t - s ∈ S ∨ (s + t ≠ 0 ∧ s + t ≠ p.getVert 1 - u ∧ s + t ≠ p.getVert 2 - u)) :
    StartAt G p := by
  intro a b ha hb ha' hb'
  have hs : a - u ∈ S := (hG u a).1 ha
  have ht : b - u ∈ S := (hG u b).1 hb
  have hne : ∀ x, G.Adj u x → x ∉ p.support → x - u ≠ p.getVert 1 - u := by
    intro x hx hx' e
    apply hx'
    rw [show x = p.getVert 1 by simpa using e]
    exact p.getVert_mem_support 1
  have hsE : a - u ∈ S.erase (p.getVert 1 - u) := Finset.mem_erase.2 ⟨hne a ha ha', hs⟩
  have htE : b - u ∈ S.erase (p.getVert 1 - u) := Finset.mem_erase.2 ⟨hne b hb hb', ht⟩
  by_cases hab : a - u = b - u
  · have : a = b := by simpa using hab
    rw [this]; exact av_refl hb'
  rcases hok _ hsE _ htE hab with h | ⟨h0, h1, h2⟩
  · exact av_adj ((hG _ _).2 (by rw [show b - a = b - u - (a - u) by abel]; exact h)) ha' hb'
  · have := av_of_chain S G hG u v p hp (a - u) hsE (b - u)
      (Relation.ReflTransGen.single ⟨hsE, htE, h0, h1, h2⟩)
    simpa using this

include hG in
/-- Degree 2. -/
theorem gd_abelian_card_two [Finite A] (hc : G.Connected) (h2 : S.card = 2) :
    ∀ (u v : A) (p : G.Walk u v), p.IsPath → p.length = G.dist u v →
      (G.induce {x | x ∉ p.support}).Connected := by
  classical
  have hS0 := zero_notMem_of S G hG
  have hsym := neg_mem_of S G hG
  refine gd_of_startAt_either hc (fun u v p _ hp => Or.inl ?_) (nb_of_card S G hG (by omega))
  rcases Nat.lt_or_ge p.length 1 with hl0 | hl1
  · -- length 0: T = {u}
    have h0 : p.length = 0 := by omega
    have hsupp : ∀ z ∈ p.support, z = u := by
      intro z hz
      obtain ⟨n, hn, hnl⟩ := Walk.mem_support_iff_exists_getVert.1 hz
      have : n = 0 := by omega
      rw [this, Walk.getVert_zero] at hn; exact hn.symm
    intro a b ha hb ha' hb'
    have hs : a - u ∈ S := (hG u a).1 ha
    have ht : b - u ∈ S := (hG u b).1 hb
    by_cases hab : a - u = b - u
    · have : a = b := by simpa using hab
      rw [this]; exact av_refl hb'
    by_cases hneg : b - u = -(a - u)
    · -- chain along multiples of `a - u`
      set g := a - u with hgdef
      set n := addOrderOf g with hn
      have hn0 : 0 < n := addOrderOf_pos g
      have hg0 : g ≠ 0 := fun e => hS0 (e ▸ hs)
      have hn2 : 2 ≤ n := by
        by_contra h
        have : n = 1 := by omega
        have hng := addOrderOf_nsmul_eq_zero g
        rw [← hn, this, one_nsmul] at hng; exact hg0 hng
      have hT : ∀ k, 1 ≤ k → k ≤ n - 1 → u + k • g ∉ ({z | z ∈ p.support} : Set A) := by
        intro k hk1 hk hmem
        have e := hsupp _ hmem
        have : k • g = 0 • g := by rw [zero_nsmul]; linear_combination (norm := module) e
        have := nsmul_inj_lt (by omega) hn0 this; omega
      have h1 : a = u + 1 • g := by rw [one_nsmul, hgdef]; abel
      have h2' : b = u + (n - 1) • g := by
        rw [nsmul_sub_eq g (by omega), one_nsmul, ← hneg]; abel
      rw [h1, h2']
      exact av_cycle S G hG hs (by omega) (by omega) (fun k h1 h2 => hT k h1 h2)
    · -- two-step route through `a + (b - u)`
      have hmid : a + (b - u) ∉ ({z | z ∈ p.support} : Set A) := by
        intro hmem
        have e := hsupp _ hmem
        exact hneg (by linear_combination (norm := module) e)
      refine av_trans (av_adj ?_ ha' hmid) (av_adj ?_ hmid hb')
      · exact (hG _ _).2 (by rw [show a + (b - u) - a = b - u by abel]; exact ht)
      · exact (hG _ _).2 (by rw [show b - (a + (b - u)) = -(a - u) by abel]; exact hsym _ hs)
  · -- length ≥ 1: only one other neighbour
    intro a b ha hb ha' hb'
    have hs : a - u ∈ S := (hG u a).1 ha
    have ht : b - u ∈ S := (hG u b).1 hb
    have hne : ∀ x, G.Adj u x → x ∉ p.support → x - u ≠ p.getVert 1 - u := by
      intro x hx hx' e
      apply hx'
      rw [show x = p.getVert 1 by simpa using e]
      exact p.getVert_mem_support 1
    have hgS : p.getVert 1 - u ∈ S := by
      have h := p.adj_getVert_succ (i := 0) (by omega)
      rw [Walk.getVert_zero] at h
      exact (hG _ _).1 h
    have hc1 : (S.erase (p.getVert 1 - u)).card = 1 := by
      rw [Finset.card_erase_of_mem hgS, h2]
    obtain ⟨w, hw⟩ := Finset.card_eq_one.1 hc1
    have ha1 : a - u ∈ S.erase (p.getVert 1 - u) := Finset.mem_erase.2 ⟨hne a ha ha', hs⟩
    have hb1 : b - u ∈ S.erase (p.getVert 1 - u) := Finset.mem_erase.2 ⟨hne b hb hb', ht⟩
    rw [hw, Finset.mem_singleton] at ha1 hb1
    have : a = b := by
      have : a - u = b - u := ha1.trans hb1.symm
      simpa using this
    rw [this]; exact av_refl hb'

/-- Degree 3: the two ways the start test can fail. -/
def Fail3 (S : Finset A) (g g2 : A) : Prop :=
  (g + g ≠ 0 ∧ g2 = g + g ∧ g + g + g ∈ S ∧ (g + g + g) + (g + g + g) = 0 ∧
    ∀ w ∈ S, w = g ∨ w = -g ∨ w = g + g + g) ∨
  (g + g = 0 ∧ ∃ s ∈ S, s + s ≠ 0 ∧ -s - s ∉ S ∧ ∀ w ∈ S, w = g ∨ w = s ∨ w = -s)

omit [DecidableEq A] in
lemma fail3_aux [DecidableEq A] (hS0 : (0 : A) ∉ S) (hsym : ∀ s ∈ S, -s ∈ S) {g g2 s t : A}
    (hg : g ∈ S) (hf : GF S g g2) (hsS : s ∈ S) (htS : t ∈ S) (hsg : s ≠ g) (htg : t ≠ g)
    (hst : s ≠ t) (hcov : ∀ w ∈ S, w = g ∨ w = s ∨ w = t) (hts : t - s ∉ S)
    (hsum : s + t = 0 ∨ s + t = g ∨ s + t = g2) : Fail3 S g g2 := by
  have hg0 : g ≠ 0 := fun e => hS0 (e ▸ hg)
  have hgf : g2 = g ∨ (g2 ∉ S ∧ g2 ≠ 0 ∧ g2 - g ∈ S) := by
    rcases hf with ⟨h1, -⟩ | ⟨-, h1⟩ | ⟨-, h1, h2, h3⟩
    · exact (hg0 h1).elim
    · exact Or.inl h1
    · exact Or.inr ⟨h1, h2, h3⟩
  by_cases hgg : g + g = 0
  · rcases hcov _ (hsym s hsS) with e | e | e
    · exact (hsg (by linear_combination (norm := module) -e - hgg)).elim
    · rcases hcov _ (hsym t htS) with f | f | f
      · exact (htg (by linear_combination (norm := module) -f - hgg)).elim
      · exact (hst (by linear_combination (norm := module) -e + f)).elim
      · rcases hsum with h | h | h
        · exact (hst (by linear_combination (norm := module) h + f)).elim
        · exact (hts (by rw [show t - s = g by linear_combination (norm := module) h + e]; exact hg)).elim
        · rcases hgf with h' | ⟨h1, h2, h3⟩
          · exact (hts (by rw [show t - s = g by linear_combination (norm := module) h + e + h']
                           exact hg)).elim
          · rcases hcov _ h3 with k | k | k
            · exact (h2 (by linear_combination (norm := module) k + hgg)).elim
            · exact (htg (by linear_combination (norm := module) k + h)).elim
            · exact (hsg (by linear_combination (norm := module) k + h)).elim
    · refine Or.inr ⟨hgg, s, hsS, fun h => hst (by linear_combination (norm := module) h + e), ?_,
        fun w hw => ?_⟩
      · intro hm; exact hts (by rw [show t - s = -s - s by rw [← e]]; exact hm)
      · rcases hcov w hw with f | f | f
        · exact Or.inl f
        · exact Or.inr (Or.inl f)
        · exact Or.inr (Or.inr (f.trans e.symm))
  · have key : ∀ {s t : A}, s ∈ S → t ∈ S → s ≠ g → t ≠ g → s ≠ t →
        (∀ w ∈ S, w = g ∨ w = s ∨ w = t) → t - s ∉ S →
        (s + t = 0 ∨ s + t = g ∨ s + t = g2) → -g = s → Fail3 S g g2 := by
      intro s t hsS htS hsg htg hst hcov hts hsum hs
      rcases hcov _ (hsym t htS) with f | f | f
      · exact (hst (by linear_combination (norm := module) -hs + f)).elim
      · exact (htg (by linear_combination (norm := module) -f + hs)).elim
      · have htt : t + t = 0 := by linear_combination (norm := module) -f
        rcases hsum with h | h | h
        · exact (htg (by linear_combination (norm := module) h + hs)).elim
        · exact (hts (by rw [show t - s = -g by linear_combination (norm := module) -h + htt]
                         exact hsym g hg)).elim
        · rcases hgf with h' | ⟨h1, h2, h3⟩
          · exact (hts (by rw [show t - s = -g by linear_combination (norm := module) -h - h' + htt]
                           exact hsym g hg)).elim
          · rcases hcov _ h3 with k | k | k
            · have ht3 : t = g + g + g := by linear_combination (norm := module) k + h + hs
              refine Or.inl ⟨hgg, by linear_combination (norm := module) k, ht3 ▸ htS,
                by rw [← ht3]; exact htt, fun w hw => ?_⟩
              rcases hcov w hw with e | e | e
              · exact Or.inl e
              · exact Or.inr (Or.inl (e.trans hs.symm))
              · exact Or.inr (Or.inr (e.trans ht3))
            · exact (h2 (by linear_combination (norm := module) k - hs)).elim
            · exact (hgg (by linear_combination (norm := module) -k - h - hs)).elim
    rcases hcov _ (hsym g hg) with e | e | e
    · exact (hgg (by linear_combination (norm := module) -e)).elim
    · exact key hsS htS hsg htg hst hcov hts hsum e
    · exact key htS hsS htg hsg (Ne.symm hst) (fun w hw => by
        rcases hcov w hw with f | f | f
        · exact Or.inl f
        · exact Or.inr (Or.inr f)
        · exact Or.inr (Or.inl f))
        (fun hm => hts (by rw [show t - s = -(s - t) by abel]; exact hsym _ hm))
        (by rcases hsum with h | h | h
            · exact Or.inl (by rw [add_comm]; exact h)
            · exact Or.inr (Or.inl (by rw [add_comm]; exact h))
            · exact Or.inr (Or.inr (by rw [add_comm]; exact h))) e

include hG in
/-- Degree 3: the start test fails only in the configurations of `Fail3`. -/
lemma fail3_of_not_ok (h3 : S.card = 3) {u v : A} (p : G.Walk u v) (hp : p.length = G.dist u v)
    (hL : 1 ≤ p.length)
    (hnot : ¬ ∀ s ∈ S.erase (p.getVert 1 - u), ∀ t ∈ S.erase (p.getVert 1 - u), s ≠ t →
      t - s ∈ S ∨ (s + t ≠ 0 ∧ s + t ≠ p.getVert 1 - u ∧ s + t ≠ p.getVert 2 - u)) :
    Fail3 S (p.getVert 1 - u) (p.getVert 2 - u) := by
  classical
  have hgS : p.getVert 1 - u ∈ S := by
    have h := p.adj_getVert_succ (i := 0) (by omega)
    rw [Walk.getVert_zero] at h
    exact (hG _ _).1 h
  obtain ⟨s, hs, t, ht, hst, hfail⟩ : ∃ s ∈ S.erase (p.getVert 1 - u), ∃ t ∈ S.erase (p.getVert 1 - u),
      s ≠ t ∧ ¬ (t - s ∈ S ∨ (s + t ≠ 0 ∧ s + t ≠ p.getVert 1 - u ∧ s + t ≠ p.getVert 2 - u)) := by
    by_contra hcon
    apply hnot
    intro s hs t ht hst
    by_contra h
    exact hcon ⟨s, hs, t, ht, hst, h⟩
  have hts : t - s ∉ S := fun h => hfail (Or.inl h)
  have hsum' : s + t = 0 ∨ s + t = p.getVert 1 - u ∨ s + t = p.getVert 2 - u := by
    by_contra hc
    push Not at hc
    exact hfail (Or.inr hc)
  have hs' := Finset.mem_erase.1 hs
  have ht' := Finset.mem_erase.1 ht
  have hc2 : (S.erase (p.getVert 1 - u)).card = 2 := by rw [Finset.card_erase_of_mem hgS, h3]
  have hcov : ∀ w ∈ S, w = p.getVert 1 - u ∨ w = s ∨ w = t := by
    intro w hw
    by_cases hwg : w = p.getVert 1 - u
    · exact Or.inl hwg
    have hwN : w ∈ S.erase (p.getVert 1 - u) := Finset.mem_erase.2 ⟨hwg, hw⟩
    have hsub : ({s, t} : Finset A) = S.erase (p.getVert 1 - u) :=
      Finset.eq_of_subset_of_card_le (by
        intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl
        · exact hs
        · exact ht) (by rw [hc2, Finset.card_pair hst])
    rw [← hsub] at hwN
    simp only [Finset.mem_insert, Finset.mem_singleton] at hwN
    exact Or.inr hwN
  exact fail3_aux S (zero_notMem_of S G hG) (neg_mem_of S G hG) hgS (gf_of_geodesic S G hG u v p hp)
    hs'.2 ht'.2 hs'.1 ht'.1 hst hcov hts hsum'

include hG in
/-- Degree 3. -/
theorem gd_abelian_card_three [Finite A] (hc : G.Connected) (h3 : S.card = 3) :
    ∀ (u v : A) (p : G.Walk u v), p.IsPath → p.length = G.dist u v →
      (G.induce {x | x ∉ p.support}).Connected := by
  classical
  have hS0 := zero_notMem_of S G hG
  have hsym := neg_mem_of S G hG
  refine gd_of_startAt_either hc (fun u v p _ hp => ?_) (nb_of_card S G hG (by omega))
  rcases Nat.lt_or_ge p.length 1 with hl0 | hl1
  · -- length 0
    left
    have h0 : p.length = 0 := by omega
    have hsupp : ∀ z ∈ p.support, z = u := by
      intro z hz
      obtain ⟨n, hn, hnl⟩ := Walk.mem_support_iff_exists_getVert.1 hz
      have : n = 0 := by omega
      rw [this, Walk.getVert_zero] at hn; exact hn.symm
    intro a b ha hb ha' hb'
    have hs : a - u ∈ S := (hG u a).1 ha
    have ht : b - u ∈ S := (hG u b).1 hb
    by_cases hab : a - u = b - u
    · have : a = b := by simpa using hab
      rw [this]; exact av_refl hb'
    by_cases hneg : b - u = -(a - u)
    · -- route through the third element `c`
      have h2 : 1 < (S.erase (a - u)).card := by rw [Finset.card_erase_of_mem hs, h3]; omega
      obtain ⟨c, hcS', hcb⟩ := Finset.exists_mem_ne h2 (b - u)
      have hcS := (Finset.mem_erase.1 hcS').2
      have hca := (Finset.mem_erase.1 hcS').1
      have hnot : ∀ y, y ≠ u → y ∉ ({z | z ∈ p.support} : Set A) := fun y hy hm => hy (hsupp y hm)
      have m1 : a + c ≠ u := fun e => hcb (by linear_combination (norm := module) e - hneg)
      have m2 : u + c ≠ u := by
        intro e
        have h : c = 0 := by linear_combination (norm := module) e
        exact hS0 (h ▸ hcS)
      have m3 : u + c + (b - u) ≠ u := fun e => hca (by linear_combination (norm := module) e - hneg)
      refine av_trans (av_adj ?_ ha' (hnot _ m1)) (av_trans (av_adj ?_ (hnot _ m1) (hnot _ m2))
        (av_trans (av_adj ?_ (hnot _ m2) (hnot _ m3)) (av_adj ?_ (hnot _ m3) hb')))
      · exact (hG _ _).2 (by rw [show a + c - a = c by abel]; exact hcS)
      · exact (hG _ _).2 (by rw [show u + c - (a + c) = -(a - u) by abel]; exact hsym _ hs)
      · exact (hG _ _).2 (by rw [show u + c + (b - u) - (u + c) = b - u by abel]; exact ht)
      · exact (hG _ _).2 (by rw [show b - (u + c + (b - u)) = -c by abel]; exact hsym _ hcS)
    · have hmid : a + (b - u) ∉ ({z | z ∈ p.support} : Set A) := by
        intro hmem
        have e := hsupp _ hmem
        exact hneg (by linear_combination (norm := module) e)
      refine av_trans (av_adj ?_ ha' hmid) (av_adj ?_ hmid hb')
      · exact (hG _ _).2 (by rw [show a + (b - u) - a = b - u by abel]; exact ht)
      · exact (hG _ _).2 (by rw [show b - (a + (b - u)) = -(a - u) by abel]; exact hsym _ hs)
  -- length ≥ 1
  by_cases hok : ∀ s ∈ S.erase (p.getVert 1 - u), ∀ t ∈ S.erase (p.getVert 1 - u), s ≠ t →
      t - s ∈ S ∨ (s + t ≠ 0 ∧ s + t ≠ p.getVert 1 - u ∧ s + t ≠ p.getVert 2 - u)
  · exact Or.inl (startAt_of_pair S G hG p hp hok)
  have hf := fail3_of_not_ok S G hG h3 p hp hl1 hok
  set L := p.length with hLdef
  set ℓ : ℕ → A := fun i => p.getVert (i + 1) - p.getVert i with hℓ
  have hℓS : ∀ i, i < L → ℓ i ∈ S := fun i hi => (hG _ _).1 (p.adj_getVert_succ hi)
  have W2 : ∀ i j, i ≠ j → i < L → j < L → N2 S (ℓ i + ℓ j) :=
    fun i j hij hi hj => w2 S G hG hc p hp hij hi hj
  have W3 : ∀ i j k, i ≠ j → i ≠ k → j ≠ k → i < L → j < L → k < L → N3 S (ℓ i + ℓ j + ℓ k) :=
    fun i j k hij hik hjk hi hj hk => w3 S G hG hc p hp hij hik hjk hi hj hk
  have hs1 : p.getVert 1 - u = ℓ 0 := by simp [hℓ]
  rcases hf with ⟨hgg, hg2, h3S, h33, hcov⟩ | ⟨hgg, s, hsS, hss, hns, hcov⟩
  · -- (K33): length 2 only
    rcases Nat.lt_or_ge L 3 with hL3 | hL3
    · rcases Nat.lt_or_ge L 2 with hL2 | hL2
      · exfalso
        have e2 : p.getVert 2 = p.getVert 1 := by
          rw [p.getVert_of_length_le (by omega), p.getVert_of_length_le (by omega)]
        rw [e2] at hg2
        exact hgg (by linear_combination (norm := module) -hg2 - hg2)
      · -- length 2: explicit route u - g, u - 2g, u + 3g
        left
        set g := p.getVert 1 - u with hgdef
        have hg1 : p.getVert 1 = u + g := by rw [hgdef]; abel
        have hg2' : p.getVert 2 = u + (g + g) := by rw [← hg2]; abel
        have hsupp : ∀ z ∈ p.support, z = u ∨ z = u + g ∨ z = u + (g + g) := by
          intro z hz
          obtain ⟨n, hn, hnl⟩ := Walk.mem_support_iff_exists_getVert.1 hz
          have hn2 : n ≤ 2 := by omega
          interval_cases n
          · left; rw [← hn, Walk.getVert_zero]
          · right; left; rw [← hn, hg1]
          · right; right; rw [← hn, hg2']
        have hgS : g ∈ S := hs1 ▸ hℓS 0 (by omega)
        have hx : u - g - g ∉ ({z | z ∈ p.support} : Set A) := by
          intro hmem
          rcases hsupp _ hmem with e | e | e
          · exact hgg (by linear_combination (norm := module) -e)
          · exact hS0 (by rw [show (0 : A) = g + g + g by linear_combination (norm := module) e]
                          exact h3S)
          · exact hgg (by linear_combination (norm := module) e + h33)
        intro a b ha hb ha' hb'
        have hne : ∀ x, G.Adj u x → x ∉ p.support → x - u ≠ g := by
          intro x hx' hx'' e
          exact hx'' (by rw [show x = u + g by rw [← e]; abel]; exact hg1 ▸ p.getVert_mem_support 1)
        have hval : ∀ x, G.Adj u x → x ∉ p.support → x = u - g ∨ x = u + (g + g + g) := by
          intro x hx' hx''
          rcases hcov _ ((hG _ _).1 hx') with e | e | e
          · exact absurd e (hne x hx' hx'')
          · left; linear_combination (norm := module) e
          · right; linear_combination (norm := module) e
        have hcm : u - g ∉ p.support := by
          intro hmem
          rcases hsupp _ hmem with e | e | e
          · exact hS0 (by rw [show (0 : A) = g by linear_combination (norm := module) e]; exact hgS)
          · exact hgg (by linear_combination (norm := module) -e)
          · exact hS0 (by rw [show (0 : A) = g + g + g by linear_combination (norm := module) e]
                          exact h3S)
        have h3m : u + (g + g + g) ∉ p.support := by
          intro hmem
          rcases hsupp _ hmem with e | e | e
          · exact hS0 (by rw [show (0 : A) = g + g + g by linear_combination (norm := module) -e]
                          exact h3S)
          · exact hgg (by linear_combination (norm := module) e)
          · exact hS0 (by rw [show (0 : A) = g by linear_combination (norm := module) -e]; exact hgS)
        have hjoin : Av G {z | z ∈ p.support} (u - g) (u + (g + g + g)) := by
          refine av_trans (av_adj ?_ hcm hx) (av_adj ?_ hx h3m)
          · exact (hG _ _).2 (by rw [show u - g - g - (u - g) = -g by abel]; exact hsym g hgS)
          · exact (hG _ _).2 (by
              rw [show u + (g + g + g) - (u - g - g) = -g by linear_combination (norm := module) h33]
              exact hsym g hgS)
        rcases hval a ha ha' with e | e <;> rcases hval b hb hb' with f | f <;> rw [e, f]
        · exact av_refl hcm
        · exact hjoin
        · exact av_symm hjoin
        · exact av_refl h3m
    · -- length ≥ 3: impossible
      exfalso
      have hq : ℓ 1 = ℓ 0 := by
        have : p.getVert 2 - u = ℓ 0 + ℓ 1 := by simp only [hℓ, Walk.getVert_zero]; abel
        rw [this, hs1] at hg2
        linear_combination (norm := module) hg2
      rw [hs1] at hgg hcov h3S h33
      rcases hcov _ (hℓS 2 (by omega)) with e | e | e
      · exact (W3 0 1 2 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)).1
          (by rw [hq, e]; exact h3S)
      · exact (W2 1 2 (by omega) (by omega) (by omega)).2 (by rw [hq, e]; abel)
      · exact (W3 0 1 2 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)).1
          (by rw [hq, e, show ℓ 0 + ℓ 0 + (ℓ 0 + ℓ 0 + ℓ 0) = -ℓ 0 by
                linear_combination (norm := module) h33]
              exact hsym _ (hℓS 0 (by omega)))
  · -- (Inv): g involution, the other two neighbours `±s` not adjacent
    rcases Nat.lt_or_ge L 2 with hL2 | hL2
    · left
      have hl : p.length = 1 := by omega
      have hsN : s ∈ S.erase (p.getVert 1 - u) := Finset.mem_erase.2 ⟨fun e => hss (by
        rw [e]; exact hgg), hsS⟩
      have hcov' : ∀ z ∈ S.erase (p.getVert 1 - u),
          z = s ∨ z = s + (p.getVert 1 - u) ∨ z = -s ∨ z = (p.getVert 1 - u) - s := by
        intro z hz
        rcases hcov z (Finset.mem_erase.1 hz).2 with e | e | e
        · exact absurd e (Finset.mem_erase.1 hz).1
        · exact Or.inl e
        · exact Or.inr (Or.inr (Or.inl e))
      have hw := exc_walk S G hG u v p hl hsN hcov'
      intro a b ha hb ha' hb'
      have hne : ∀ x, G.Adj u x → x ∉ p.support → x - u ∈ S.erase (p.getVert 1 - u) := by
        intro x hx hx'
        refine Finset.mem_erase.2 ⟨fun e => hx' ?_, (hG _ _).1 hx⟩
        rw [show x = p.getVert 1 by simpa using e]
        exact p.getVert_mem_support 1
      have h1 := hw _ (hne a ha ha')
      have h2 := hw _ (hne b hb hb')
      simpa using av_trans (av_symm h1) h2
    · -- the other end passes the test
      right
      have hpr : p.reverse.length = G.dist v u := by rw [Walk.length_reverse, dist_comm]; exact hp
      refine startAt_of_pair S G hG p.reverse hpr ?_
      by_contra hno
      have hf' := fail3_of_not_ok S G hG h3 p.reverse hpr (by rw [Walk.length_reverse]; omega) hno
      have hv : p.getVert L = v := Walk.getVert_length p
      have hv1 : p.getVert (L - 1 + 1) = v := by rw [show L - 1 + 1 = L by omega]; exact hv
      have hv2 : p.getVert (L - 2 + 1) = p.getVert (L - 1) := by congr 1; omega
      have he1 : p.reverse.getVert 1 - v = -ℓ (L - 1) := by
        rw [Walk.getVert_reverse]; simp only [hℓ, hv1]; abel
      have he2 : p.reverse.getVert 2 - v = -ℓ (L - 1) + -ℓ (L - 2) := by
        rw [Walk.getVert_reverse]; simp only [hℓ, hv1, hv2]; abel
      rw [he1, he2] at hf'
      rw [hs1] at hgg hcov
      rcases hf' with ⟨hdd, hd2, -, -, hcov'⟩ | ⟨hdd, -⟩
      · have hcd : ℓ (L - 2) = ℓ (L - 1) := by linear_combination (norm := module) -hd2
        rcases hcov' _ (hℓS 0 (by omega)) with e | e | e
        · exact hdd (by linear_combination (norm := module) hgg - e - e)
        · exact hdd (by linear_combination (norm := module) -hgg + e + e)
        · rcases Nat.lt_or_ge L 3 with hL3 | hL3
          · have h1 : L - 2 = 0 := by omega
            rw [h1] at hcd
            exact (W2 0 (L - 1) (by omega) (by omega) (by omega)).2 (by rw [← hcd]; exact hgg)
          · exact (W3 0 (L - 2) (L - 1) (by omega) (by omega) (by omega) (by omega) (by omega)
              (by omega)).1 (by
                rw [hcd, e, show -ℓ (L - 1) + -ℓ (L - 1) + -ℓ (L - 1) + ℓ (L - 1) + ℓ (L - 1) =
                  -ℓ (L - 1) by abel]
                exact hsym _ (hℓS _ (by omega)))
      · rcases hcov _ (hℓS (L - 1) (by omega)) with e | e | e
        · exact (W2 0 (L - 1) (by omega) (by omega) (by omega)).2 (by rw [e]; exact hgg)
        · exact hss (by linear_combination (norm := module) -hdd - e - e)
        · exact hss (by linear_combination (norm := module) hdd + e + e)

include hG in
/-- **Geodesic Deletion for 4-regular Cayley graphs of finite abelian groups** (Theorem 4, proved
by peeling at a suitable end; NOTE.md §6.3, with explicit walks for short
geodesics instead of Watkins' bound). -/
theorem gd_abelian_card_four [Finite A] (hc : G.Connected) (h4 : S.card = 4) :
    ∀ (u v : A) (p : G.Walk u v), p.IsPath → p.length = G.dist u v →
      (G.induce {x | x ∉ p.support}).Connected := by
  refine gd_of_startAt_either hc (fun u v p _ hp => ?_) (nb_of_card S G hG (by omega))
  rcases Nat.lt_or_ge p.length 3 with hL | hL
  · exact Or.inl (startAt_short S G hG h4 p hp (by omega))
  · exact startAt_either_long S G hG h4 hc p hp hL

include hG in
/-- **Geodesic Deletion for Cayley graphs of finite abelian groups of degree at least 4.** -/
theorem gd_abelian_card_ge_four [Finite A] (hc : G.Connected) (h4 : 4 ≤ S.card) :
    ∀ (u v : A) (p : G.Walk u v), p.IsPath → p.length = G.dist u v →
      (G.induce {x | x ∉ p.support}).Connected := by
  rcases Nat.lt_or_ge S.card 5 with h | h
  · exact gd_abelian_card_four S G hG hc (by omega)
  · exact gd_abelian_card_ge_five S G hG hc h

include hG in
/-- A connected Cayley graph of an abelian group with at least 3 vertices has degree at least 2. -/
lemma two_le_card_of_connected [Fintype A] (hc : G.Connected) (h3 : 3 ≤ Fintype.card A) :
    2 ≤ S.card := by
  classical
  by_contra hlt
  have hle : S.card ≤ 1 := by omega
  obtain ⟨c, hc'⟩ : ∃ c, ∀ s ∈ S, s = c := by
    rcases Finset.card_le_one.1 hle with h
    by_cases hS : S.Nonempty
    · obtain ⟨c, hcS⟩ := hS
      exact ⟨c, fun s hs => Finset.card_le_one.1 hle s hs c hcS⟩
    · exact ⟨0, fun s hs => (hS ⟨s, hs⟩).elim⟩
  have hreach : ∀ x, x = 0 ∨ x = c := by
    intro x
    obtain ⟨w⟩ := hc.preconnected 0 x
    suffices h : ∀ {y z : A} (w : G.Walk y z), (y = 0 ∨ y = c) → (z = 0 ∨ z = c) from h w (Or.inl rfl)
    intro y z w
    induction w with
    | nil => exact id
    | @cons a b d hab w ih =>
      intro ha
      apply ih
      have hb : b - a ∈ S := (hG _ _).1 hab
      have hbc : b - a = c := hc' _ hb
      have hnc : -c = c := hc' _ (neg_mem_of S G hG _ (hbc ▸ hb))
      rcases ha with rfl | rfl
      · right; linear_combination (norm := module) hbc
      · left; linear_combination (norm := module) hbc - hnc
  have : Fintype.card A ≤ 2 := by
    have hsub : (Finset.univ : Finset A) ⊆ {0, c} := by
      intro x _; rcases hreach x with h | h <;> simp [h]
    calc Fintype.card A = (Finset.univ : Finset A).card := rfl
      _ ≤ ({0, c} : Finset A).card := Finset.card_le_card hsub
      _ ≤ 2 := Finset.card_le_two
  omega

include hG in
/-- **Geodesic Deletion for every connected Cayley graph of a finite abelian group with at least
three vertices.** -/
theorem gd_abelian [Fintype A] (hc : G.Connected) (h3 : 3 ≤ Fintype.card A) :
    ∀ (u v : A) (p : G.Walk u v), p.IsPath → p.length = G.dist u v →
      (G.induce {x | x ∉ p.support}).Connected := by
  have h2 := two_le_card_of_connected S G hG hc h3
  rcases Nat.lt_or_ge S.card 4 with h | h
  · rcases (show S.card = 2 ∨ S.card = 3 by omega) with h' | h'
    · exact gd_abelian_card_two S G hG hc h'
    · exact gd_abelian_card_three S G hG hc h'
  · exact gd_abelian_card_ge_four S G hG hc h

include hG in
/-- **Geodesic Deletion for abelian Cayley graphs of degree at least 6** (any abelian group). -/
theorem gd_abelian_card_ge_six (hc : G.Connected) (h6 : 6 ≤ S.card) :
    ∀ (u v : A) (p : G.Walk u v), p.IsPath → p.length = G.dist u v →
      (G.induce {x | x ∉ p.support}).Connected :=
  gd_of_startCond hc (startCond_of_card_six S G hG h6) (nb_of_card S G hG (by omega))

end abelian

section statement

/-- Same definition as in statement #334. -/
def IsVertexTransitive {V : Type*} (G : SimpleGraph V) : Prop :=
  ∀ u v : V, ∃ φ : G ≃g G, φ u = v

/-- Graphs with an abelian labelling are vertex-transitive (translations). -/
lemma isVertexTransitive_of_labelling {V : Type} (G : SimpleGraph V) (A : Type) [AddCommGroup A]
    (e : V ≃ A) (S : Finset A) (hG : ∀ u v, G.Adj u v ↔ e v - e u ∈ S) : IsVertexTransitive G := by
  intro u v
  let τ : V ≃ V := (e.trans (Equiv.addRight (e v - e u))).trans e.symm
  refine ⟨{ toEquiv := τ, map_rel_iff' := ?_ }, ?_⟩
  · intro a b
    simp only [τ, Equiv.trans_apply, Equiv.coe_addRight, Equiv.apply_symm_apply, hG]
    rw [show e b + (e v - e u) - (e a + (e v - e u)) = e b - e a by abel]
  · simp [τ]

lemma dist_iso_le {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W} (φ : G ≃g H) {a b : V}
    (hr : G.Reachable a b) : H.dist (φ a) (φ b) ≤ G.dist a b := by
  obtain ⟨w, hw⟩ := hr.exists_walk_length_eq_dist
  calc H.dist (φ a) (φ b) ≤ (w.map φ.toHom).length := dist_le _
    _ = G.dist a b := by rw [Walk.length_map, hw]

/-- Transport of the conclusion of #334 along a graph isomorphism. -/
lemma gd_of_iso {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W} (φ : G ≃g H)
    (hG : ∀ (u v : V) (p : G.Walk u v), p.IsPath → p.length = G.dist u v →
      (G.induce {x | x ∉ p.support}).Connected) :
    ∀ (u v : W) (p : H.Walk u v), p.IsPath → p.length = H.dist u v →
      (H.induce {x | x ∉ p.support}).Connected := by
  intro u v p hp hl
  let q : G.Walk (φ.symm u) (φ.symm v) := p.map φ.symm.toHom
  have hq : q.IsPath := hp.map φ.symm.injective
  have hql : q.length = G.dist (φ.symm u) (φ.symm v) := by
    rw [Walk.length_map, hl]
    refine le_antisymm ?_ (dist_iso_le φ.symm p.reachable)
    have h := dist_iso_le φ q.reachable
    simpa using h
  have hconn := hG _ _ q hq hql
  -- the induced subgraphs are isomorphic via φ
  have hset : ∀ x, x ∉ q.support ↔ φ x ∉ p.support := by
    intro x
    simp only [q, Walk.support_map, List.mem_map]
    constructor
    · intro h h'
      exact h ⟨φ x, h', by simp⟩
    · rintro h ⟨y, hy, rfl⟩
      exact h (by simpa using hy)
  let ψ : G.induce {x | x ∉ q.support} ≃g H.induce {x | x ∉ p.support} :=
    { toFun := fun x => ⟨φ x.1, (hset x.1).1 x.2⟩
      invFun := fun y => ⟨φ.symm y.1, (hset _).2 (by rw [RelIso.apply_symm_apply]; exact y.2)⟩
      left_inv := fun x => by simp
      right_inv := fun y => by simp
      map_rel_iff' := by
        intro x y
        simp only [Equiv.coe_fn_mk, comap_adj, Function.Embedding.coe_subtype]
        exact φ.map_rel_iff }
  exact ψ.connected_iff.1 hconn

/-- **The Left to Solve statement of Geodesic Deletion (`gillibert-geodesic-deletion`, #334),
restricted to graphs with an abelian labelling** (= Cayley graphs of finite abelian groups, any
degree). Hypotheses and conclusion as in #334. -/
theorem main_abelian_cayley :
    ∀ {V : Type} [Fintype V] (G : SimpleGraph V),
      G.Connected → IsVertexTransitive G → 3 ≤ Fintype.card V →
      (∃ (A : Type) (_ : AddCommGroup A) (_ : DecidableEq A) (e : V ≃ A) (S : Finset A),
        ∀ u v, G.Adj u v ↔ e v - e u ∈ S) →
      ∀ (u v : V) (p : G.Walk u v), p.IsPath → p.length = G.dist u v →
        (G.induce {x | x ∉ p.support}).Connected := by
  intro V _ G hc _ hV hcay
  obtain ⟨A, _, _, e, S, hG⟩ := hcay
  have : Fintype A := Fintype.ofEquiv V e
  let G' : SimpleGraph A := G.comap e.symm
  have hG' : ∀ a b, G'.Adj a b ↔ b - a ∈ S := by
    intro a b
    simp only [G', SimpleGraph.comap_adj, hG, Equiv.apply_symm_apply]
  let φ : G' ≃g G := { toEquiv := e.symm, map_rel_iff' := by intro a b; rfl }
  have hc' : G'.Connected := φ.connected_iff.2 hc
  have hA : 3 ≤ Fintype.card A := by rwa [← Fintype.card_congr e]
  exact gd_of_iso φ (gd_abelian S G' hG' hc' hA)

/-- **The Left to Solve statement of Geodesic Deletion (`gillibert-geodesic-deletion`, #334),
restricted to graphs with an abelian labelling of degree at least 4** (Cayley graphs of finite
abelian groups `Cay(A, S)`, `|S| ≥ 4`). Hypotheses and conclusion as in #334. -/
theorem main_abelian_cayley_ge_four :
    ∀ {V : Type} [Fintype V] (G : SimpleGraph V),
      G.Connected → IsVertexTransitive G → 3 ≤ Fintype.card V →
      (∃ (A : Type) (_ : AddCommGroup A) (_ : DecidableEq A) (e : V ≃ A) (S : Finset A),
        4 ≤ S.card ∧ ∀ u v, G.Adj u v ↔ e v - e u ∈ S) →
      ∀ (u v : V) (p : G.Walk u v), p.IsPath → p.length = G.dist u v →
        (G.induce {x | x ∉ p.support}).Connected := by
  intro V _ G hc _ _ hcay
  obtain ⟨A, _, _, e, S, h4, hG⟩ := hcay
  have : Finite A := Finite.of_equiv V e
  let G' : SimpleGraph A := G.comap e.symm
  have hG' : ∀ a b, G'.Adj a b ↔ b - a ∈ S := by
    intro a b
    simp only [G', SimpleGraph.comap_adj, hG, Equiv.apply_symm_apply]
  let φ : G' ≃g G := { toEquiv := e.symm, map_rel_iff' := by intro a b; rfl }
  have hc' : G'.Connected := φ.connected_iff.2 hc
  exact gd_of_iso φ (gd_abelian_card_ge_four S G' hG' hc' h4)

/-- **The Left to Solve statement of Geodesic Deletion (`gillibert-geodesic-deletion`, #334),
restricted to graphs with an abelian labelling of degree at least 5** (Cayley graphs of finite
abelian groups `Cay(A, S)`, `|S| ≥ 5`). Hypotheses and conclusion as in #334. -/
theorem main_abelian_cayley_ge_five :
    ∀ {V : Type} [Fintype V] (G : SimpleGraph V),
      G.Connected → IsVertexTransitive G → 3 ≤ Fintype.card V →
      (∃ (A : Type) (_ : AddCommGroup A) (_ : DecidableEq A) (e : V ≃ A) (S : Finset A),
        5 ≤ S.card ∧ ∀ u v, G.Adj u v ↔ e v - e u ∈ S) →
      ∀ (u v : V) (p : G.Walk u v), p.IsPath → p.length = G.dist u v →
        (G.induce {x | x ∉ p.support}).Connected := by
  intro V _ G hc _ _ hcay
  obtain ⟨A, _, _, e, S, h5, hG⟩ := hcay
  have : Finite A := Finite.of_equiv V e
  let G' : SimpleGraph A := G.comap e.symm
  have hG' : ∀ a b, G'.Adj a b ↔ b - a ∈ S := by
    intro a b
    simp only [G', SimpleGraph.comap_adj, hG, Equiv.apply_symm_apply]
  let φ : G' ≃g G := { toEquiv := e.symm, map_rel_iff' := by intro a b; rfl }
  have hc' : G'.Connected := φ.connected_iff.2 hc
  exact gd_of_iso φ (gd_abelian_card_ge_five S G' hG' hc' h5)

/-- **The Left to Solve statement of Geodesic Deletion (`gillibert-geodesic-deletion`, #334),
restricted to graphs with an abelian labelling of degree at least 6** (Cayley graphs of finite
abelian groups `Cay(A, S)`, `|S| ≥ 6`; for any abelian group see `gd_abelian_card_ge_six`). Hypotheses and conclusion as in #334. -/
theorem main_abelian_cayley_ge_six :
    ∀ {V : Type} [Fintype V] (G : SimpleGraph V),
      G.Connected → IsVertexTransitive G → 3 ≤ Fintype.card V →
      (∃ (A : Type) (_ : AddCommGroup A) (_ : DecidableEq A) (e : V ≃ A) (S : Finset A),
        6 ≤ S.card ∧ ∀ u v, G.Adj u v ↔ e v - e u ∈ S) →
      ∀ (u v : V) (p : G.Walk u v), p.IsPath → p.length = G.dist u v →
        (G.induce {x | x ∉ p.support}).Connected := by
  intro V _ G hc _ _ hcay
  obtain ⟨A, _, _, e, S, h6, hG⟩ := hcay
  let G' : SimpleGraph A := G.comap e.symm
  have hG' : ∀ a b, G'.Adj a b ↔ b - a ∈ S := by
    intro a b
    simp only [G', SimpleGraph.comap_adj, hG, Equiv.apply_symm_apply]
  let φ : G' ≃g G := { toEquiv := e.symm, map_rel_iff' := by intro a b; rfl }
  have hc' : G'.Connected := φ.connected_iff.2 hc
  exact gd_of_iso φ (gd_abelian_card_ge_six S G' hG' hc' h6)

/-- **The Left to Solve statement of Geodesic Deletion (`gillibert-geodesic-deletion`, #334),
restricted to graphs with an abelian labelling of degree at least 8** (Cayley graphs of finite
abelian groups `Cay(A, S)`, `|S| ≥ 8`; for any abelian group see `gd_abelian_card_ge_eight`). Hypotheses and conclusion as in #334. -/
theorem main_abelian_cayley_ge_eight :
    ∀ {V : Type} [Fintype V] (G : SimpleGraph V),
      G.Connected → IsVertexTransitive G → 3 ≤ Fintype.card V →
      (∃ (A : Type) (_ : AddCommGroup A) (_ : DecidableEq A) (e : V ≃ A) (S : Finset A),
        8 ≤ S.card ∧ ∀ u v, G.Adj u v ↔ e v - e u ∈ S) →
      ∀ (u v : V) (p : G.Walk u v), p.IsPath → p.length = G.dist u v →
        (G.induce {x | x ∉ p.support}).Connected := by
  intro V _ G hc _ _ hcay
  obtain ⟨A, _, _, e, S, h8, hG⟩ := hcay
  let G' : SimpleGraph A := G.comap e.symm
  have hG' : ∀ a b, G'.Adj a b ↔ b - a ∈ S := by
    intro a b
    simp only [G', SimpleGraph.comap_adj, hG, Equiv.apply_symm_apply]
  let φ : G' ≃g G := { toEquiv := e.symm, map_rel_iff' := by intro a b; rfl }
  have hc' : G'.Connected := φ.connected_iff.2 hc
  exact gd_of_iso φ (gd_abelian_card_ge_eight S G' hG' hc' h8)

end statement

end GDAbelian

#print axioms GDAbelian.main_abelian_cayley_ge_eight
#print axioms GDAbelian.gd_abelian_card_ge_eight
#print axioms GDAbelian.main_abelian_cayley_ge_six
#print axioms GDAbelian.main_abelian_cayley_ge_five
#print axioms GDAbelian.main_abelian_cayley_ge_four
#print axioms GDAbelian.main_abelian_cayley
