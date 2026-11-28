/-
Copyright 2026 Ming-Chih Kao. Licensed under the Apache License, Version 2.0;
see the LICENSE file at the root of this repository.
Ported from github.com/koolkao/gillibert-fair-traversal-abelian (v1.7.0, commit
06c3a8732759afca38331762b76113135e475ac6) to Lean v4.36.0 and the module system.
-/
module

public import Mathlib

/-!
# Geodesic Deletion is closed under Cartesian products (Theorem 2 of `NOTE.md`)

Gillibert's Geodesic Deletion conjecture (Left to Solve `gillibert-geodesic-deletion`, statement #334):
for a finite connected vertex-transitive graph `G` with at least three vertices and every geodesic `P`
of `G`, the induced subgraph `G − V(P)` is connected.

`GDPlus H` is the conclusion of that statement for a single graph `H` (Mathlib's `Connected` includes
`Nonempty`, so `H − V(P)` is also nonempty). This is property GD+ of `NOTE.md` §3.

* **Theorem 2** (the faithful one-sided theorem): `gdPlus_boxProd`. If `G₁` is connected, `G₂` is
  connected and `GDPlus G₂`, then `GDPlus (G₁ □ G₂)`. No finiteness and no vertex-transitivity is
  assumed.
* Corollaries with **extra hypotheses** (they are not the one-sided theorem):
  `geodesicDeletion_boxProd` (both factors finite and vertex-transitive, `|W| ≥ 3`; it also concludes
  that `G □ H` satisfies the hypotheses of #334) and `gd_boxProd` (the conditional form `GD` of #334
  assumed for both factors, both finite and vertex-transitive, one of them with at least three
  vertices).
* Other corollaries: `GDPlus.of_iso`, `gdPlus_boxProd_left`, `gdPlus_top` (K_q, q ≥ 3),
  `gdPlus_hamming` (H(d,q), q ≥ 3), `gdPlus_Q2`, `gdPlus_hypercube` (Q_d, d ≥ 2).

27 November 2026. Original proof; only Mathlib is used. `Check.lean` restates the main results
against the definitions of #334, copied verbatim.
-/

@[expose] public section


namespace GDProduct

open SimpleGraph

/-- The conclusion of the Geodesic Deletion conjecture (#334) for one graph: deleting the vertices of any
geodesic (one-vertex geodesics included) leaves a connected, nonempty induced subgraph. -/
def GDPlus {V : Type*} (H : SimpleGraph V) : Prop :=
  ∀ (u v : V) (p : H.Walk u v), p.IsPath → p.length = H.dist u v →
    (H.induce {x | x ∉ p.support}).Connected

section general

variable {V : Type*} {G : SimpleGraph V}

lemma length_induce {s : Set V} {u v : V} (w : G.Walk u v) (hw : ∀ x ∈ w.support, x ∈ s) :
    (w.induce s hw).length = w.length := by
  have h := congrArg Walk.length (Walk.map_induce w hw)
  rwa [Walk.length_map] at h

/-- Along a geodesic, the distance between the vertices at positions `i ≤ j` is `j - i`. -/
lemma dist_getVert {u v : V} (p : G.Walk u v) (hp : p.length = G.dist u v) {i j : ℕ}
    (hij : i ≤ j) (hj : j ≤ p.length) :
    G.dist (p.getVert i) (p.getVert j) = j - i := by
  have hsub : ((p.drop i).take (j - i)).IsSubwalk p :=
    (Walk.isSubwalk_take _ _).trans (Walk.isSubwalk_drop _ _)
  have h := length_eq_dist_of_subwalk hp hsub
  rw [Walk.take_length, Walk.drop_length, Walk.drop_getVert, Nat.add_sub_cancel' hij] at h
  rw [← h]
  omega

end general

variable {α β : Type*} {G₁ : SimpleGraph α} {G₂ : SimpleGraph β}

lemma dist_boxProd (h₁ : G₁.Connected) (h₂ : G₂.Connected) (x y : α × β) :
    (G₁ □ G₂).dist x y = G₁.dist x.1 y.1 + G₂.dist x.2 y.2 := by
  have ha : G₁.edist x.1 y.1 ≠ ⊤ := edist_ne_top_iff_reachable.2 (h₁.preconnected x.1 y.1)
  have hb : G₂.edist x.2 y.2 ≠ ⊤ := edist_ne_top_iff_reachable.2 (h₂.preconnected x.2 y.2)
  simp only [SimpleGraph.dist, edist_boxProd]
  exact ENat.toNat_add ha hb

/-- Every second coordinate of a vertex of `w` is a vertex of the projected walk `w.ofBoxProdRight`. -/
lemma snd_mem_support_ofBoxProdRight [DecidableEq α] [DecidableRel G₂.Adj] {x y : α × β}
    (w : (G₁ □ G₂).Walk x y) : ∀ {z : α × β}, z ∈ w.support → z.2 ∈ w.ofBoxProdRight.support := by
  induction w with
  | nil =>
    intro z hz
    rw [Walk.support_nil, List.mem_singleton] at hz
    subst hz
    simp [Walk.ofBoxProdRight]
  | @cons x c y h w ih =>
    intro z hz
    rw [Walk.support_cons, List.mem_cons] at hz
    rcases x with ⟨x₁, x₂⟩
    rcases c with ⟨c₁, c₂⟩
    unfold Walk.ofBoxProdRight Or.by_cases
    split
    · rename_i hH
      rw [Walk.support_cons, List.mem_cons]
      rcases hz with rfl | hz
      · exact Or.inl rfl
      · exact Or.inr (ih hz)
    · rename_i hH
      have hx : x₂ = c₂ := by
        rw [boxProd_adj] at h
        rcases h with h | h
        · exact h.2
        · exact absurd h hH
      subst hx
      rcases hz with rfl | hz
      · exact (w.ofBoxProdRight.start_mem_support : _)
      · exact (ih hz : _)

lemma mem_support_map_iff {V W : Type*} {G : SimpleGraph V} {G' : SimpleGraph W} (f : G →g G')
    {u v : V} (p : G.Walk u v) (y : W) : y ∈ (p.map f).support ↔ ∃ x ∈ p.support, f x = y := by
  rw [Walk.support_map, List.mem_map]

lemma mem_support_induce_iff {V : Type*} {G : SimpleGraph V} {s : Set V} {u v : V} (w : G.Walk u v)
    (hw : ∀ x ∈ w.support, x ∈ s) (x : s) : x ∈ (w.induce s hw).support ↔ (x : V) ∈ w.support := by
  rw [Walk.support_induce, List.mem_attachWith]

/-- Projection of the fibre `{a} × β` of `G₁ □ G₂` onto `G₂`. -/
def fibreHom (a : α) : (G₁ □ G₂).induce {z : α × β | z.1 = a} →g G₂ where
  toFun z := z.1.2
  map_rel' {z z'} h := by
    obtain ⟨⟨z₁, z₂⟩, hz⟩ := z
    obtain ⟨⟨z₁', z₂'⟩, hz'⟩ := z'
    have hz1 : z₁ = a := hz
    have hz1' : z₁' = a := hz'
    subst hz1 hz1'
    have h' := SimpleGraph.induce_adj.1 h
    rw [boxProd_adj] at h'
    rcases h' with h' | h'
    · exact (G₁.irrefl h'.1).elim
    · exact h'.1

@[simp] lemma fibreHom_apply (a : α) (z) : (fibreHom (G₁ := G₁) (G₂ := G₂) a) z = z.1.2 := rfl

/-- The vertices of a geodesic of `G₁ □ G₂` in the fibre over `a` form (if any) the vertex set of a
geodesic of `G₂`. -/
lemma fibre_geodesic (h₁ : G₁.Connected) (h₂ : G₂.Connected) {x y : α × β}
    (p : (G₁ □ G₂).Walk x y) (hp : p.length = (G₁ □ G₂).dist x y) (a : α)
    (hS : ∃ z ∈ p.support, z.1 = a) :
    ∃ (c d : β) (q : G₂.Walk c d), q.length = G₂.dist c d ∧
      ∀ b, b ∈ q.support ↔ (a, b) ∈ p.support := by
  classical
  let P : ℕ → Prop := fun i => (p.getVert i).1 = a
  have hex : ∃ i, i ≤ p.length ∧ P i := by
    obtain ⟨z, hz, hza⟩ := hS
    obtain ⟨n, hn, hnL⟩ := Walk.mem_support_iff_exists_getVert.1 hz
    refine ⟨n, hnL, ?_⟩
    show (p.getVert n).1 = a
    rw [hn]
    exact hza
  set i₀ := Nat.find hex with hi₀def
  have hi₀ : i₀ ≤ p.length ∧ P i₀ := Nat.find_spec hex
  have hmin : ∀ n, n ≤ p.length → P n → i₀ ≤ n := fun n hn hP => Nat.find_min' hex ⟨hn, hP⟩
  set i₁ := Nat.findGreatest P p.length with hi₁def
  have hi₁P : P i₁ := Nat.findGreatest_spec (P := P) hi₀.1 hi₀.2
  have hi₁L : i₁ ≤ p.length := Nat.findGreatest_le p.length
  have hmax : ∀ n, n ≤ p.length → P n → n ≤ i₁ := fun n hn hP => Nat.le_findGreatest hn hP
  have h01 : i₀ ≤ i₁ := hmax _ hi₀.1 hi₀.2
  have hA0 : (p.getVert i₀).1 = a := hi₀.2
  have hA1 : (p.getVert i₁).1 = a := hi₁P
  -- every position between `i₀` and `i₁` lies in the fibre over `a`
  have hconv : ∀ i, i₀ ≤ i → i ≤ i₁ → P i := by
    intro i hi0 hi1
    have e1 := dist_getVert p hp h01 hi₁L
    have e2 := dist_getVert p hp hi0 (hi1.trans hi₁L)
    have e3 := dist_getVert p hp hi1 hi₁L
    rw [dist_boxProd h₁ h₂] at e1
    rw [dist_boxProd h₁ h₂] at e2
    rw [dist_boxProd h₁ h₂] at e3
    rw [hA0, hA1, SimpleGraph.dist_self, zero_add] at e1
    rw [hA0] at e2
    rw [hA1] at e3
    have tri := h₂.dist_triangle (u := (p.getVert i₀).2) (v := (p.getVert i).2)
      (w := (p.getVert i₁).2)
    have hz : G₁.dist a (p.getVert i).1 = 0 := by omega
    exact ((h₁.dist_eq_zero_iff).1 hz).symm
  -- the segment of `p` from `i₀` to `i₁`
  let q' := (p.drop i₀).take (i₁ - i₀)
  have hq'sub : q'.IsSubwalk p := (Walk.isSubwalk_take _ _).trans (Walk.isSubwalk_drop _ _)
  have hq'get : ∀ k, q'.getVert k = p.getVert (i₀ + min (i₁ - i₀) k) := by
    intro k
    simp only [q', Walk.take_getVert, Walk.drop_getVert]
  have hq'len : q'.length = i₁ - i₀ := by
    simp only [q', Walk.take_length, Walk.drop_length]
    omega
  have hq'F : ∀ z ∈ q'.support, z ∈ {z : α × β | z.1 = a} := by
    intro z hz
    obtain ⟨k, rfl, hk⟩ := Walk.mem_support_iff_exists_getVert.1 hz
    rw [hq'get]
    exact hconv _ (by omega) (by omega)
  let q := (q'.induce _ hq'F).map (fibreHom a)
  refine ⟨_, _, q, ?_, ?_⟩
  · have hlq : q.length = q'.length := by
      simp only [q, Walk.length_map, length_induce]
    have h := length_eq_dist_of_subwalk hp hq'sub
    rw [dist_boxProd h₁ h₂] at h
    have e1 : ((p.drop i₀).getVert (i₁ - i₀)).1 = a := by
      rw [Walk.drop_getVert, Nat.add_sub_cancel' h01]
      exact hA1
    rw [hA0, e1, SimpleGraph.dist_self, zero_add] at h
    rw [hlq]
    exact h
  · intro b
    constructor
    · intro hb
      obtain ⟨⟨z, hzF⟩, hz, hzb⟩ := (mem_support_map_iff (fibreHom a) _ b).1 hb
      have hz' : z ∈ q'.support := (mem_support_induce_iff q' hq'F ⟨z, hzF⟩).1 hz
      have hzp : z ∈ p.support := hq'sub.support_subset hz'
      rw [fibreHom_apply] at hzb
      have hzF' : z.1 = a := hzF
      have hz'' : (a, b) = z := Prod.ext hzF'.symm hzb.symm
      rw [hz'']
      exact hzp
    · intro hb
      obtain ⟨n, hn, hnL⟩ := Walk.mem_support_iff_exists_getVert.1 hb
      have hPn : P n := by
        show (p.getVert n).1 = a
        rw [hn]
      have h0 := hmin n hnL hPn
      have h1 := hmax n hnL hPn
      have hget : q'.getVert (n - i₀) = (a, b) := by
        rw [hq'get, show i₀ + min (i₁ - i₀) (n - i₀) = n by omega, hn]
      have hmem : (a, b) ∈ q'.support := by
        rw [← hget]
        exact Walk.getVert_mem_support _ _
      exact (mem_support_map_iff (fibreHom a) _ b).2
        ⟨⟨(a, b), rfl⟩, (mem_support_induce_iff q' hq'F ⟨(a, b), rfl⟩).2 hmem, rfl⟩

/-- **Theorem 2.** Geodesic Deletion (in the form `GDPlus`) passes from `G₂` to `G₁ □ G₂` for every
connected `G₁`. -/
theorem gdPlus_boxProd (h₁ : G₁.Connected) (h₂ : G₂.Connected) (hgd : GDPlus G₂) :
    GDPlus (G₁ □ G₂) := by
  classical
  intro x y p _hpath hp
  -- a row `α × {b*}` that misses `p`
  obtain ⟨bs, hbs⟩ : ∃ b, ∀ z ∈ p.support, z.2 ≠ b := by
    have hlen := Walk.length_boxProd p
    have hd := dist_boxProd h₁ h₂ x y
    have l1 := dist_le p.ofBoxProdLeft
    have l2 := dist_le p.ofBoxProdRight
    have hp2 : p.ofBoxProdRight.length = G₂.dist x.2 y.2 := by omega
    obtain ⟨⟨b, hb⟩⟩ := (hgd _ _ _ (p.ofBoxProdRight.isPath_of_length_eq_dist hp2) hp2).nonempty
    exact ⟨b, fun z hz h => hb (h ▸ snd_mem_support_ofBoxProdRight p hz)⟩
  have hrow : ∀ a : α, (a, bs) ∉ p.support := fun a h => hbs _ h rfl
  obtain ⟨a₀⟩ := h₁.nonempty
  rw [connected_iff_exists_forall_reachable]
  refine ⟨⟨(a₀, bs), hrow a₀⟩, ?_⟩
  rintro ⟨⟨a, b⟩, hab⟩
  -- a walk in the fibre over `a` from `bs` to `b` that misses `p`
  obtain ⟨w, hw⟩ : ∃ w : G₂.Walk bs b, ∀ c ∈ w.support, (a, c) ∉ p.support := by
    by_cases hS : ∃ z ∈ p.support, z.1 = a
    · obtain ⟨c, d, q, hq, hqs⟩ := fibre_geodesic h₁ h₂ p hp a hS
      have hconn := hgd c d q (q.isPath_of_length_eq_dist hq) hq
      have hbs' : bs ∉ q.support := fun h => hrow a ((hqs bs).1 h)
      have hb' : b ∉ q.support := fun h => hab ((hqs b).1 h)
      obtain ⟨w'⟩ := hconn.preconnected ⟨bs, hbs'⟩ ⟨b, hb'⟩
      let w'' := w'.map (Embedding.induce _).toHom
      have hw'' : ∀ c ∈ w''.support, (a, c) ∉ p.support := by
        intro c hc
        obtain ⟨⟨c', hc'⟩, _, hcc⟩ := (mem_support_map_iff _ w' c).1 hc
        have hcc' : c' = c := hcc
        subst hcc'
        exact fun h => hc' ((hqs c').2 h)
      exact ⟨w'', hw''⟩
    · obtain ⟨w⟩ := h₂.preconnected bs b
      exact ⟨w, fun c _ h => hS ⟨_, h, rfl⟩⟩
  obtain ⟨u⟩ := h₁.preconnected a₀ a
  let W := (u.boxProdLeft G₂ bs).append (w.boxProdRight G₁ a)
  have hW : ∀ z ∈ W.support, z ∈ {z | z ∉ p.support} := by
    intro z hz
    rw [Walk.mem_support_append_iff] at hz
    rcases hz with hz | hz
    · obtain ⟨a', _, rfl⟩ := (mem_support_map_iff _ u z).1 hz
      exact hrow a'
    · obtain ⟨c, hc, rfl⟩ := (mem_support_map_iff _ w z).1 hz
      exact hw c hc
  exact ⟨W.induce _ hW⟩

end GDProduct

/-! ## Corollaries: isomorphism invariance, both factors, statement #334, Hamming graphs, hypercubes -/

namespace GDProduct

open SimpleGraph

section iso

variable {V W : Type*} {G : SimpleGraph V} {G' : SimpleGraph W}

lemma dist_le_of_iso (e : G ≃g G') (u v : V) : G'.dist (e u) (e v) ≤ G.dist u v := by
  by_cases h : G.Reachable u v
  · obtain ⟨w, hw⟩ := h.exists_walk_length_eq_dist
    rw [← hw]
    exact (dist_le (w.map e.toHom)).trans_eq (Walk.length_map _ _)
  · have h' : ¬ G'.Reachable (e u) (e v) := fun h' => h (Iso.reachable_iff.1 h')
    rw [dist_eq_zero_of_not_reachable h']
    exact Nat.zero_le _

lemma dist_iso (e : G ≃g G') (u v : V) : G'.dist (e u) (e v) = G.dist u v := by
  refine le_antisymm (dist_le_of_iso e u v) ?_
  simpa using dist_le_of_iso e.symm (e u) (e v)

/-- `GDPlus` is invariant under graph isomorphism. -/
theorem GDPlus.of_iso (e : G ≃g G') (h : GDPlus G) : GDPlus G' := by
  intro u v p _ hp
  let q := p.map e.symm.toHom
  have hq : q.length = G.dist (e.symm.toHom u) (e.symm.toHom v) := by
    simp only [q, Walk.length_map, hp]
    exact (dist_iso e.symm u v).symm
  have hc := h _ _ q (q.isPath_of_length_eq_dist hq) hq
  have hbij : Set.BijOn e {x | x ∉ q.support} {y | y ∉ p.support} := by
    refine ⟨?_, e.injective.injOn, ?_⟩
    · intro x hx h'
      apply hx
      exact (mem_support_map_iff _ p x).2 ⟨e x, h', by simp⟩
    · intro y hy
      refine ⟨e.symm y, ?_, by simp⟩
      intro hmem
      obtain ⟨z, hz, hzy⟩ := (mem_support_map_iff _ p _).1 hmem
      have : z = y := by simpa using congrArg e hzy
      exact hy (this ▸ hz)
  exact (Iso.induce e hbij).connected_iff.1 hc

end iso

variable {α β : Type*} {G₁ : SimpleGraph α} {G₂ : SimpleGraph β}

/-- Theorem 2 with the roles of the factors exchanged. -/
theorem gdPlus_boxProd_left (h₁ : G₁.Connected) (h₂ : G₂.Connected) (hgd : GDPlus G₁) :
    GDPlus (G₁ □ G₂) :=
  (gdPlus_boxProd h₂ h₁ hgd).of_iso (boxProdComm G₂ G₁)

/-- `GDPlus G ∧ GDPlus H → GDPlus (G □ H)` for connected factors (only one factor needs `GDPlus`). -/
theorem gdPlus_boxProd_of_both (h₁ : G₁.Connected) (h₂ : G₂.Connected)
    (hgd : GDPlus G₁ ∧ GDPlus G₂) : GDPlus (G₁ □ G₂) :=
  gdPlus_boxProd h₁ h₂ hgd.2

/-! ### Link with the Left to Solve statement #334 -/

/-- Same definition as in statement #334 (`OMA.S_gillibert_geodesic_deletion.IsVertexTransitive`). -/
def IsVertexTransitive {V : Type*} (G : SimpleGraph V) : Prop :=
  ∀ u v : V, ∃ φ : G ≃g G, φ u = v

/-- The Cartesian product of vertex-transitive graphs is vertex-transitive. -/
theorem isVertexTransitive_boxProd (h₁ : IsVertexTransitive G₁) (h₂ : IsVertexTransitive G₂) :
    IsVertexTransitive (G₁ □ G₂) := by
  rintro ⟨a, b⟩ ⟨a', b'⟩
  obtain ⟨φ, hφ⟩ := h₁ a a'
  obtain ⟨ψ, hψ⟩ := h₂ b b'
  refine ⟨⟨Equiv.prodCongr φ.toEquiv ψ.toEquiv, ?_⟩, ?_⟩
  · intro x y
    obtain ⟨x₁, x₂⟩ := x
    obtain ⟨y₁, y₂⟩ := y
    show (G₁ □ G₂).Adj (φ x₁, ψ x₂) (φ y₁, ψ y₂) ↔ (G₁ □ G₂).Adj (x₁, x₂) (y₁, y₂)
    simp only [boxProd_adj, Iso.map_adj_iff, EmbeddingLike.apply_eq_iff_eq]
  · show (φ a, ψ b) = (a', b')
    rw [hφ, hψ]

/-- The conjecture of statement #334, for one fixed finite graph `G`. -/
def GD {V : Type} [Fintype V] (G : SimpleGraph V) : Prop :=
  G.Connected → IsVertexTransitive G → 3 ≤ Fintype.card V → GDPlus G

/-- **Corollary of Theorem 2 with extra hypotheses** (not the one-sided theorem, which is
`gdPlus_boxProd`): if `G` and `H` are finite, connected and vertex-transitive, `H` has at least three
vertices and satisfies the conclusion of #334, then `G □ H` satisfies all hypotheses of #334 and its
conclusion. The vertex-transitivity of `G` and `H` is used only for the conjunct
`IsVertexTransitive (G □ H)`; `3 ≤ Fintype.card W` is implied by `hH` and `hgd`. -/
theorem geodesicDeletion_boxProd {V W : Type} [Fintype V] [Fintype W]
    (G : SimpleGraph V) (H : SimpleGraph W) (hG : G.Connected) (hGt : IsVertexTransitive G)
    (hH : H.Connected) (hHt : IsVertexTransitive H) (hW : 3 ≤ Fintype.card W)
    (hgd : ∀ (u v : W) (p : H.Walk u v), p.IsPath → p.length = H.dist u v →
      (H.induce {x | x ∉ p.support}).Connected) :
    (G □ H).Connected ∧ IsVertexTransitive (G □ H) ∧ 3 ≤ Fintype.card (V × W) ∧
      ∀ (u v : V × W) (p : (G □ H).Walk u v), p.IsPath → p.length = (G □ H).dist u v →
        ((G □ H).induce {x | x ∉ p.support}).Connected := by
  refine ⟨hG.boxProd hH, isVertexTransitive_boxProd hGt hHt, ?_, gdPlus_boxProd hG hH hgd⟩
  have : 1 ≤ Fintype.card V := Fintype.card_pos_iff.2 hG.nonempty
  rw [Fintype.card_prod]
  nlinarith

/-- **Corollary of Theorem 2 with extra hypotheses** (not the one-sided theorem): `GD G ∧ GD H →
GD (G □ H)` in the sense of statement #334, for finite connected vertex-transitive factors one of
which has at least three vertices. `GD` is the conditional form of #334 for one graph, so it holds
vacuously for graphs with fewer than three vertices (e.g. `K₂`, for which `GDPlus` fails); the proof
uses `GD` of one factor only. (Two-vertex factors: `K₂ □ K₂ = Q₂`, see `gdPlus_Q2` and
`gdPlus_hypercube`.) -/
theorem gd_boxProd {V W : Type} [Fintype V] [Fintype W] (G : SimpleGraph V) (H : SimpleGraph W)
    (hG : G.Connected) (hGt : IsVertexTransitive G) (hH : H.Connected) (hHt : IsVertexTransitive H)
    (hcard : 3 ≤ Fintype.card V ∨ 3 ≤ Fintype.card W) (hgd : GD G ∧ GD H) : GD (G □ H) := by
  intro _ _ _
  rcases hcard with hV | hW
  · exact gdPlus_boxProd_left hG hH (hgd.1 hG hGt hV)
  · exact gdPlus_boxProd hG hH (hgd.2 hH hHt hW)

/-! ### Base cases: complete graphs and the 4-cycle -/

/-- Complete graphs on at least three vertices satisfy `GDPlus`. -/
theorem gdPlus_top {V : Type*} [Fintype V] (hV : 3 ≤ Fintype.card V) :
    GDPlus (⊤ : SimpleGraph V) := by
  classical
  intro u v p hpath hp
  have hle : p.length ≤ 1 := by
    rw [hp]
    by_cases huv : u = v
    · simp [huv]
    · simp [dist_top_of_ne huv]
  have hsupp : p.support.toFinset.card ≤ 2 := by
    calc p.support.toFinset.card ≤ p.support.length := List.toFinset_card_le _
      _ = p.length + 1 := Walk.length_support _
      _ ≤ 2 := by omega
  have hne : ∃ x, x ∉ p.support := by
    by_contra hcon
    simp only [not_exists, not_not] at hcon
    have : (Finset.univ : Finset V) ⊆ p.support.toFinset := fun x _ => List.mem_toFinset.2 (hcon x)
    have := Finset.card_le_card this
    rw [Finset.card_univ] at this
    omega
  obtain ⟨x, hx⟩ := hne
  rw [connected_iff_exists_forall_reachable]
  refine ⟨⟨x, hx⟩, fun y => ?_⟩
  by_cases hxy : (⟨x, hx⟩ : {x | x ∉ p.support}) = y
  · rw [hxy]
  · exact Adj.reachable ((top_adj _ _).2 fun h => hxy (Subtype.ext h))

/-- A connected induced subgraph criterion: every vertex of `T` is within distance two of `t₀`
inside `T`. -/
lemma connected_induce_of_radius_two {V : Type*} {G : SimpleGraph V} {T : Set V} (t₀ : V)
    (ht₀ : t₀ ∈ T)
    (h : ∀ t ∈ T, t = t₀ ∨ G.Adj t₀ t ∨ ∃ s ∈ T, G.Adj t₀ s ∧ G.Adj s t) :
    (G.induce T).Connected := by
  rw [connected_iff_exists_forall_reachable]
  refine ⟨⟨t₀, ht₀⟩, ?_⟩
  rintro ⟨t, ht⟩
  rcases h t ht with rfl | hadj | ⟨s, hs, h1, h2⟩
  · exact Reachable.refl _
  · exact Adj.reachable (show (G.induce T).Adj ⟨t₀, ht₀⟩ ⟨t, ht⟩ from hadj)
  · exact (Adj.reachable (show (G.induce T).Adj ⟨t₀, ht₀⟩ ⟨s, hs⟩ from h1)).trans
      (Adj.reachable (show (G.induce T).Adj ⟨s, hs⟩ ⟨t, ht⟩ from h2))

/-! ### Hamming graphs and hypercubes -/

/-- The Hamming graph `H(d, q)`: words of length `d` over `Fin q`, adjacent iff they differ in exactly
one coordinate. `H(d, 2)` is the hypercube `Q_d`. -/
def hammingGraph (d q : ℕ) : SimpleGraph (Fin d → Fin q) where
  Adj x y := hammingDist x y = 1
  symm := ⟨fun x y (h : hammingDist x y = 1) => (hammingDist_comm y x).trans h⟩
  loopless := ⟨fun x (h : hammingDist x x = 1) => by simp at h⟩

instance (d q : ℕ) : DecidableRel (hammingGraph d q).Adj := fun x y =>
  inferInstanceAs (Decidable (hammingDist x y = 1))

lemma hammingDist_cons {d q : ℕ} (a b : Fin q) (x y : Fin d → Fin q) :
    hammingDist (Fin.cons a x : Fin (d + 1) → Fin q) (Fin.cons b y) =
      (if a = b then 0 else 1) + hammingDist x y := by
  simp only [hammingDist, Finset.card_filter, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]
  split_ifs <;> simp_all

/-- `H(d + 1, q) ≅ K_q □ H(d, q)`. -/
def hammingIso (d q : ℕ) :
    SimpleGraph.boxProd (⊤ : SimpleGraph (Fin q)) (hammingGraph d q) ≃g hammingGraph (d + 1) q where
  toEquiv := Fin.consEquiv (fun _ => Fin q)
  map_rel_iff' {x y} := by
    obtain ⟨a, x⟩ := x
    obtain ⟨b, y⟩ := y
    show hammingDist (Fin.cons a x : Fin (d + 1) → Fin q) (Fin.cons b y) = 1 ↔
      (SimpleGraph.boxProd (⊤ : SimpleGraph (Fin q)) (hammingGraph d q)).Adj (a, x) (b, y)
    rw [hammingDist_cons, boxProd_adj, top_adj]
    dsimp only
    by_cases hab : a = b
    · subst hab
      rw [if_pos rfl, zero_add]
      constructor
      · intro h
        exact Or.inr ⟨h, rfl⟩
      · rintro (⟨h, -⟩ | ⟨h, -⟩)
        · exact absurd rfl h
        · exact h
    · rw [if_neg hab]
      constructor
      · intro h
        exact Or.inl ⟨hab, hammingDist_eq_zero.1 (by omega)⟩
      · rintro (⟨-, rfl⟩ | ⟨-, h⟩)
        · rw [hammingDist_self]
        · exact absurd h hab

lemma hammingGraph_connected (d q : ℕ) (hq : 1 ≤ q) : (hammingGraph d q).Connected := by
  induction d with
  | zero =>
    have : Nonempty (Fin 0 → Fin q) := ⟨Fin.elim0⟩
    exact Connected.of_subsingleton
  | succ d ih =>
    have : Nonempty (Fin q) := ⟨⟨0, hq⟩⟩
    exact (hammingIso d q).connected_iff.1 (connected_top.boxProd ih)

/-- Hamming graphs `H(d, q)`, `d ≥ 1`, `q ≥ 3`, satisfy Geodesic Deletion. -/
theorem gdPlus_hamming (d q : ℕ) (hq : 3 ≤ q) : GDPlus (hammingGraph (d + 1) q) := by
  have : Nonempty (Fin q) := ⟨⟨0, by omega⟩⟩
  exact (gdPlus_boxProd_left connected_top (hammingGraph_connected d q (by omega))
    (gdPlus_top (V := Fin q) (by simpa using hq))).of_iso (hammingIso d q)

/-- The finite fact behind the base case `Q₂`: after deleting the vertices `u, w, v` of a geodesic,
some remaining vertex `t₀` reaches every remaining vertex in at most two steps inside the remainder.
(Stated with `∨` only, so that `decide` finds the instances.) -/
def Q2Ok (u w v t₀ : Fin 2 → Fin 2) : Prop :=
  ¬ (t₀ = u ∨ t₀ = w ∨ t₀ = v) ∧ ∀ t, t = u ∨ t = w ∨ t = v ∨
    t = t₀ ∨ (hammingGraph 2 2).Adj t₀ t ∨
      ∃ s, ¬ (s = u ∨ s = w ∨ s = v) ∧ (hammingGraph 2 2).Adj t₀ s ∧ (hammingGraph 2 2).Adj s t

instance (u w v t₀ : Fin 2 → Fin 2) : Decidable (Q2Ok u w v t₀) :=
  inferInstanceAs (Decidable (¬ (t₀ = u ∨ t₀ = w ∨ t₀ = v) ∧ ∀ t, t = u ∨ t = w ∨ t = v ∨
    t = t₀ ∨ (hammingGraph 2 2).Adj t₀ t ∨
      ∃ s, ¬ (s = u ∨ s = w ∨ s = v) ∧ (hammingGraph 2 2).Adj t₀ s ∧ (hammingGraph 2 2).Adj s t))

/-- The shapes of the vertex lists `[u, w, v]` of geodesics with at most three vertices. -/
def Q2Hyp (u w v : Fin 2 → Fin 2) : Prop :=
  ((hammingGraph 2 2).Adj u w ∧ (hammingGraph 2 2).Adj w v ∧ ¬ u = v) ∨ (u = w ∧ w = v) ∨
    ((hammingGraph 2 2).Adj u w ∧ w = v)

instance (u w v : Fin 2 → Fin 2) : Decidable (Q2Hyp u w v) :=
  inferInstanceAs (Decidable (((hammingGraph 2 2).Adj u w ∧ (hammingGraph 2 2).Adj w v ∧ ¬ u = v) ∨
    (u = w ∧ w = v) ∨ ((hammingGraph 2 2).Adj u w ∧ w = v)))

lemma q2_key : ∀ u w v : Fin 2 → Fin 2, ¬ Q2Hyp u w v ∨ ∃ t₀, Q2Ok u w v t₀ := by
  decide

lemma q2_rad : ∀ u v : Fin 2 → Fin 2, ∃ w, (u = w ∨ (hammingGraph 2 2).Adj u w) ∧
    (w = v ∨ (hammingGraph 2 2).Adj w v) := by
  decide

/-- Base case `Q_2 = C_4`. -/
theorem gdPlus_Q2 : GDPlus (hammingGraph 2 2) := by
  intro u v p hpath hp
  have hd : (hammingGraph 2 2).dist u v ≤ 2 := by
    obtain ⟨w, h1, h2⟩ := q2_rad u v
    rcases h1 with rfl | h1 <;> rcases h2 with rfl | h2
    · simp
    · exact (dist_le h2.toWalk).trans (by simp)
    · exact (dist_le h1.toWalk).trans (by simp)
    · exact (dist_le (Walk.cons h1 h2.toWalk)).trans (by simp)
  have hl : p.length ≤ 2 := by rw [hp]; exact hd
  -- read off the (at most three) vertices of `p`
  obtain ⟨a, b, c, hsupp, hcase⟩ : ∃ a b c, (∀ x, x ∈ p.support ↔ x = a ∨ x = b ∨ x = c) ∧
      (((hammingGraph 2 2).Adj a b ∧ (hammingGraph 2 2).Adj b c ∧ a ≠ c) ∨ (a = b ∧ b = c) ∨
        ((hammingGraph 2 2).Adj a b ∧ b = c)) := by
    match p, hpath, hl with
    | .nil, _, _ => exact ⟨u, u, u, by simp, Or.inr (Or.inl ⟨rfl, rfl⟩)⟩
    | .cons h .nil, _, _ => exact ⟨_, _, _, by simp, Or.inr (Or.inr ⟨h, rfl⟩)⟩
    | .cons h (.cons h' .nil), hpath, _ =>
      refine ⟨_, _, _, by simp, Or.inl ⟨h, h', ?_⟩⟩
      intro hac
      subst hac
      simp [Walk.cons_isPath_iff] at hpath
    | .cons _ (.cons _ (.cons _ _)), _, hl =>
      simp only [Walk.length_cons] at hl
      omega
  obtain ⟨t₀, h0, ht⟩ := (q2_key a b c).resolve_left (not_not.2 hcase)
  refine connected_induce_of_radius_two t₀ (by simpa [hsupp] using h0) ?_
  intro t htT
  have htT' : ¬ (t = a ∨ t = b ∨ t = c) := fun h => htT ((hsupp t).2 h)
  rcases ht t with h | h | h | h | h | ⟨s, hs, h1, h2⟩
  · exact absurd (Or.inl h) htT'
  · exact absurd (Or.inr (Or.inl h)) htT'
  · exact absurd (Or.inr (Or.inr h)) htT'
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr ⟨s, (show s ∉ p.support from fun h => hs ((hsupp s).1 h)), h1, h2⟩)

/-- Hypercubes `Q_d`, `d ≥ 2`, satisfy Geodesic Deletion. -/
theorem gdPlus_hypercube (d : ℕ) : GDPlus (hammingGraph (d + 2) 2) := by
  induction d with
  | zero => exact gdPlus_Q2
  | succ d ih =>
    have : Nonempty (Fin 2) := ⟨0⟩
    show GDPlus (hammingGraph (d + 2 + 1) 2)
    exact (gdPlus_boxProd connected_top (hammingGraph_connected (d + 2) 2 (by omega)) ih).of_iso
      (hammingIso (d + 2) 2)

end GDProduct

#print axioms GDProduct.gdPlus_boxProd
#print axioms GDProduct.geodesicDeletion_boxProd
#print axioms GDProduct.gd_boxProd
#print axioms GDProduct.gdPlus_hamming
#print axioms GDProduct.gdPlus_hypercube
