/-
Copyright 2026 Ming-Chih Kao. Licensed under the Apache License, Version 2.0;
see the LICENSE file at the root of this repository.
Ported from github.com/koolkao/gillibert-fair-traversal-abelian (v1.7.0, commit
06c3a8732759afca38331762b76113135e475ac6) to Lean v4.36.0 and the module system.
Port: a local `walk_support_eq_cons` replaces `SimpleGraph.Walk.support_eq_cons`, which Mathlib fc4f59e lacks.
-/
module

public import Mathlib

/-!
# Fair Traversal is closed under Cartesian products (Theorem 3 of `NOTE.md`)

Main result: `ft_boxProd`. If `G` and `H` are finite vertex-transitive graphs with at least two vertices
and both satisfy the conclusion of Left to Solve statement #339 (`gillibert-fair-traversal`), copied word
for word as `FTConcl`, then so does `G □ H`. (Connectivity is not needed.) No sorry; axioms propext,
Classical.choice, Quot.sound. `Check.lean` restates `ft_boxProd` against the definitions of #339.
27 November 2026; original proof using only Mathlib. Proof route: Fable's "balanced" counting
(brainstorm, 27 Nov): average over automorphisms to make each family balanced, snakes over all pairs,
mix the two snake families with natural-number weights.

Hamiltonian paths are handled as lists (`Nodup`, covering, `IsChain G.Adj`); their edges are `ledges`.
Snake: `snake l₁ l₂` runs through the fibres `{a} × V₂` in the order of `l₁`, alternately along `l₂` and
its reverse. Counting (Fable's "balanced" version): if a family on `G₁` is fair with multiplicity `k₁` and
a family on `G₂` is fair (`k₂`) and balanced (every vertex starts `s₂` paths and ends `s₂` paths), the
snakes over all pairs use every `G₂`-edge `N₁ k₂` times and every `G₁`-edge `k₁ s₂` times.
-/

@[expose] public section


namespace FTProduct

open SimpleGraph

section lists

variable {V W : Type*}

/-- Unordered consecutive pairs of a list. -/
def ledges : List V → List (Sym2 V)
  | a :: b :: l => s(a, b) :: ledges (b :: l)
  | _ => []

@[simp] lemma ledges_nil : ledges ([] : List V) = [] := rfl
@[simp] lemma ledges_single (a : V) : ledges [a] = [] := rfl
@[simp] lemma ledges_cons_cons (a b : V) (l : List V) :
    ledges (a :: b :: l) = s(a, b) :: ledges (b :: l) := rfl

lemma mem_ledges_cons (a : V) (l : List V) (e : Sym2 V) :
    e ∈ ledges (a :: l) ↔ (∃ b, l.head? = some b ∧ e = s(a, b)) ∨ e ∈ ledges l := by
  cases l with
  | nil => simp
  | cons b l => simp

lemma mem_ledges_append (l₁ l₂ : List V) (e : Sym2 V) :
    e ∈ ledges (l₁ ++ l₂) ↔ e ∈ ledges l₁ ∨ e ∈ ledges l₂ ∨
      ∃ x y, l₁.getLast? = some x ∧ l₂.head? = some y ∧ e = s(x, y) := by
  induction l₁ with
  | nil => simp
  | cons a t ih =>
    rw [List.cons_append, mem_ledges_cons, mem_ledges_cons, ih]
    cases t with
    | nil =>
      simp
      exact or_comm
    | cons b t =>
      simp [List.getLast?_cons_cons]
      exact or_assoc.symm

lemma mem_of_mem_ledges : ∀ {l : List V} {e : Sym2 V}, e ∈ ledges l → ∀ x ∈ e, x ∈ l
  | a :: b :: l, e, h, x, hx => by
      rw [ledges_cons_cons, List.mem_cons] at h
      rcases h with rfl | h
      · rw [Sym2.mem_iff] at hx
        rcases hx with rfl | rfl <;> simp
      · exact List.mem_cons_of_mem _ (mem_of_mem_ledges h x hx)
  | [], e, h, _, _ => by simp at h
  | [_], e, h, _, _ => by simp at h

lemma mem_ledges_map (f : V → W) : ∀ (l : List V) (e : Sym2 W),
    e ∈ ledges (l.map f) ↔ ∃ x y, s(x, y) ∈ ledges l ∧ e = s(f x, f y)
  | [], e => by simp
  | [a], e => by simp
  | a :: b :: l, e => by
      have ih := mem_ledges_map f (b :: l) e
      simp only [List.map_cons] at ih ⊢
      simp only [ledges_cons_cons, List.mem_cons, ih]
      constructor
      · rintro (rfl | ⟨x, y, hxy, rfl⟩)
        · exact ⟨a, b, Or.inl rfl, rfl⟩
        · exact ⟨x, y, Or.inr hxy, rfl⟩
      · rintro ⟨x, y, hxy | hxy, rfl⟩
        · left
          rcases Sym2.eq_iff.1 hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · rfl
          · exact Sym2.eq_swap
        · exact Or.inr ⟨x, y, hxy, rfl⟩

lemma mem_ledges_map_of_injective {f : V → W} (hf : Function.Injective f) (l : List V) (x y : V) :
    s(f x, f y) ∈ ledges (l.map f) ↔ s(x, y) ∈ ledges l := by
  rw [mem_ledges_map]
  constructor
  · rintro ⟨x', y', h, he⟩
    rcases Sym2.eq_iff.1 he with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [hf h1, hf h2]
      exact h
    · rw [hf h1, hf h2, Sym2.eq_swap]
      exact h
  · intro h
    exact ⟨x, y, h, rfl⟩

lemma mem_ledges_reverse (l : List V) (e : Sym2 V) : e ∈ ledges l.reverse ↔ e ∈ ledges l := by
  induction l with
  | nil => simp
  | cons a t ih =>
    rw [List.reverse_cons, mem_ledges_append, ih, mem_ledges_cons a t e]
    constructor
    · rintro (h | h | ⟨x, y, hx, hy, rfl⟩)
      · exact Or.inr h
      · simp at h
      · simp only [List.head?_cons, Option.some.injEq] at hy
        subst hy
        rw [List.getLast?_reverse] at hx
        exact Or.inl ⟨x, hx, Sym2.eq_swap⟩
    · rintro (⟨b, hb, rfl⟩ | h)
      · exact Or.inr (Or.inr ⟨b, a, by rw [List.getLast?_reverse]; exact hb, rfl, Sym2.eq_swap⟩)
      · exact Or.inl h

lemma ledges_nodup : ∀ {l : List V}, l.Nodup → (ledges l).Nodup
  | a :: b :: l, h => by
      rw [ledges_cons_cons, List.nodup_cons]
      refine ⟨fun hm => ?_, ledges_nodup (List.nodup_cons.1 h).2⟩
      exact (List.nodup_cons.1 h).1 (mem_of_mem_ledges hm a (Sym2.mem_mk_left a b))
  | [], _ => List.nodup_nil
  | [_], _ => List.nodup_nil

lemma length_ledges : ∀ l : List V, (ledges l).length = l.length - 1
  | [] => rfl
  | [_] => rfl
  | a :: b :: l => by
      rw [ledges_cons_cons, List.length_cons, length_ledges (b :: l)]
      simp

lemma ledges_sub {G : SimpleGraph V} : ∀ {l : List V}, l.IsChain G.Adj → ∀ e ∈ ledges l, e ∈ G.edgeSet
  | a :: b :: l, h, e, he => by
      rw [List.isChain_cons_cons] at h
      rw [ledges_cons_cons, List.mem_cons] at he
      rcases he with rfl | he
      · exact G.mem_edgeSet.2 h.1
      · exact ledges_sub h.2 e he
  | [], _, e, he => by simp at he
  | [_], _, e, he => by simp at he

end lists

section snake

variable {V₁ V₂ : Type*}

/-- The snake: fibres over `l₁` in order, alternately along `l₂` and its reverse. -/
def snake : List V₁ → List V₂ → List (V₁ × V₂)
  | [], _ => []
  | a :: l₁, l₂ => l₂.map (a, ·) ++ snake l₁ l₂.reverse

lemma snake_cons (a : V₁) (l₁ : List V₁) (l₂ : List V₂) :
    snake (a :: l₁) l₂ = l₂.map (a, ·) ++ snake l₁ l₂.reverse := rfl

lemma mem_snake : ∀ (l₁ : List V₁) (l₂ : List V₂) (x : V₁ × V₂), x ∈ snake l₁ l₂ ↔ x.1 ∈ l₁ ∧ x.2 ∈ l₂
  | [], l₂, x => by simp [snake]
  | a :: l₁, l₂, x => by
      rw [snake_cons, List.mem_append, mem_snake l₁ l₂.reverse x, List.mem_reverse, List.mem_map,
        List.mem_cons]
      constructor
      · rintro (⟨y, hy, rfl⟩ | ⟨h1, h2⟩)
        · exact ⟨Or.inl rfl, hy⟩
        · exact ⟨Or.inr h1, h2⟩
      · rintro ⟨h1 | h1, h2⟩
        · exact Or.inl ⟨x.2, h2, Prod.ext h1.symm rfl⟩
        · exact Or.inr ⟨h1, h2⟩

lemma snake_nodup : ∀ {l₁ : List V₁} {l₂ : List V₂}, l₁.Nodup → l₂.Nodup → (snake l₁ l₂).Nodup
  | [], _, _, _ => List.nodup_nil
  | a :: l₁, l₂, h₁, h₂ => by
      rw [snake_cons]
      refine List.Nodup.append ?_ (snake_nodup (List.nodup_cons.1 h₁).2 (List.nodup_reverse.2 h₂)) ?_
      · exact h₂.map (fun x y h => by simpa using h)
      · intro x hx hx'
        rw [List.mem_map] at hx
        obtain ⟨y, _, rfl⟩ := hx
        exact (List.nodup_cons.1 h₁).1 ((mem_snake _ _ _).1 hx').1

lemma head?_snake_cons (a : V₁) (l₁ : List V₁) {l₂ : List V₂} (h : l₂ ≠ []) :
    (snake (a :: l₁) l₂).head? = l₂.head?.map (a, ·) := by
  rw [snake_cons, List.head?_append_of_ne_nil _ (by simpa using h), List.head?_map]

lemma isChain_snake {G₁ : SimpleGraph V₁} {G₂ : SimpleGraph V₂} :
    ∀ {l₁ : List V₁} {l₂ : List V₂}, l₁.IsChain G₁.Adj → l₂.IsChain G₂.Adj → l₂ ≠ [] →
      (snake l₁ l₂).IsChain (G₁ □ G₂).Adj
  | [], _, _, _, _ => by simp [snake]
  | a :: l₁, l₂, h₁, h₂, hne => by
      rw [snake_cons]
      have h₂r : l₂.reverse.IsChain G₂.Adj := by
        rw [List.isChain_reverse]
        exact h₂.imp (fun x y h => h.symm)
      refine List.IsChain.append ?_ (isChain_snake (List.IsChain.tail h₁ : _) h₂r
        (by simpa using hne)) ?_
      · rw [List.isChain_map]
        exact h₂.imp (fun x y h => (boxProd_adj).2 (Or.inr ⟨h, rfl⟩))
      · intro x hx y hy
        cases l₁ with
        | nil => simp [snake] at hy
        | cons a' l₁ =>
          rw [head?_snake_cons _ _ (by simpa using hne), List.head?_reverse] at hy
          rw [List.getLast?_map] at hx
          obtain ⟨z, hz, rfl⟩ := Option.mem_map.1 hx
          obtain ⟨z', hz', rfl⟩ := Option.mem_map.1 hy
          have hzz : z = z' :=
            Option.some_injective _ ((Option.mem_def.1 hz).symm.trans (Option.mem_def.1 hz'))
          subst hzz
          rw [List.isChain_cons_cons] at h₁
          exact (boxProd_adj).2 (Or.inl ⟨h₁.1, rfl⟩)

/-- Every edge of a snake inside a fibre comes from an edge of `l₂`. -/
lemma mem_ledges_snake_fibre :
    ∀ {l₁ : List V₁} (l₂ : List V₂), l₁.Nodup → ∀ (a : V₁) (b b' : V₂),
      (s((a, b), (a, b')) ∈ ledges (snake l₁ l₂) ↔ a ∈ l₁ ∧ s(b, b') ∈ ledges l₂)
  | [], l₂, _, a, b, b' => by simp [snake]
  | c :: l₁, l₂, h₁, a, b, b' => by
      rw [snake_cons, mem_ledges_append, mem_ledges_snake_fibre l₂.reverse (List.nodup_cons.1 h₁).2,
        mem_ledges_reverse, mem_ledges_map, List.mem_cons]
      have hc : c ∉ l₁ := (List.nodup_cons.1 h₁).1
      constructor
      · rintro (⟨x, y, hxy, he⟩ | ⟨ha, hb⟩ | ⟨x, y, hx, hy, he⟩)
        · rcases Sym2.eq_iff.1 he with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · simp only [Prod.mk.injEq] at h1 h2
            obtain ⟨rfl, rfl⟩ := h1
            obtain ⟨-, rfl⟩ := h2
            exact ⟨Or.inl rfl, hxy⟩
          · simp only [Prod.mk.injEq] at h1 h2
            obtain ⟨rfl, rfl⟩ := h1
            obtain ⟨-, rfl⟩ := h2
            exact ⟨Or.inl rfl, by rw [Sym2.eq_swap]; exact hxy⟩
        · exact ⟨Or.inr ha, hb⟩
        · exfalso
          cases l₁ with
          | nil => simp [snake] at hy
          | cons c' l₁ =>
            have hy' := hy
            rw [head?_snake_cons] at hy'
            · rw [List.getLast?_map] at hx
              obtain ⟨z, _, rfl⟩ := Option.mem_map.1 (show x ∈ _ from hx)
              obtain ⟨z', _, rfl⟩ := Option.mem_map.1 (show y ∈ _ from hy')
              rcases Sym2.eq_iff.1 he with ⟨h1, h2⟩ | ⟨h1, h2⟩
              · simp only [Prod.mk.injEq] at h1 h2
                exact hc (by rw [show c = c' from h1.1.symm.trans h2.1]; exact List.mem_cons_self ..)
              · simp only [Prod.mk.injEq] at h1 h2
                exact hc (by rw [show c = c' from h2.1.symm.trans h1.1]; exact List.mem_cons_self ..)
            · intro hnil
              simp [List.reverse_eq_nil_iff.1 hnil] at hx
      · rintro ⟨rfl | ha, hb⟩
        · exact Or.inl ⟨b, b', hb, rfl⟩
        · exact Or.inr (Or.inl ⟨ha, hb⟩)

end snake

section snake2

variable {V₁ V₂ : Type*}

lemma sym2_fst {a a' c c' : V₁} {b b' z z' : V₂} (h : s((a, b), (a', b')) = s((c, z), (c', z'))) :
    s(a, a') = s(c, c') := by
  have := congrArg (Sym2.map Prod.fst) h
  simpa using this

lemma sym2_snd {a a' c c' : V₁} {b b' z z' : V₂} (h : s((a, b), (a', b')) = s((c, z), (c', z'))) :
    s(b, b') = s(z, z') := by
  have := congrArg (Sym2.map Prod.snd) h
  simpa using this

/-- Edges of a snake between two fibres: they sit at the junctions, and the second coordinate is the
last or the first vertex of `l₂` according to a parity that depends only on `l₁` and the edge. -/
lemma mem_ledges_snake_cross :
    ∀ {l₁ : List V₁}, l₁.Nodup → ∀ {a a' : V₁}, a ≠ a' → ∃ c : Bool, ∀ (l₂ : List V₂), l₂ ≠ [] →
      ∀ b, (s((a, b), (a', b)) ∈ ledges (snake l₁ l₂) ↔
        s(a, a') ∈ ledges l₁ ∧ (if c then l₂.getLast? else l₂.head?) = some b)
  | [], _, a, a', _ => ⟨true, fun l₂ _ b => by simp [snake]⟩
  | c₀ :: t, h₁, a, a', haa => by
      have hc₀ : c₀ ∉ t := (List.nodup_cons.1 h₁).1
      obtain ⟨c', hc'⟩ := mem_ledges_snake_cross (List.nodup_cons.1 h₁).2 haa
      -- edges inside the first fibre are never of this form
      have hblock : ∀ (l₂ : List V₂) (b : V₂),
          s((a, b), (a', b)) ∉ ledges (l₂.map (c₀, ·)) := by
        intro l₂ b hm
        rw [mem_ledges_map] at hm
        obtain ⟨x, y, _, he⟩ := hm
        have := sym2_fst he
        rcases Sym2.eq_iff.1 this with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact haa (h1.trans h2.symm)
        · exact haa (h1.trans h2.symm)
      by_cases hj : ∃ c₁, t.head? = some c₁ ∧ s(a, a') = s(c₀, c₁)
      · obtain ⟨c₁, hc₁, hs⟩ := hj
        refine ⟨true, fun l₂ hl₂ b => ?_⟩
        have hin : s(a, a') ∈ ledges (c₀ :: t) := (mem_ledges_cons _ _ _).2 (Or.inl ⟨c₁, hc₁, hs⟩)
        rw [if_pos rfl, and_iff_right hin]
        obtain ⟨t', rfl⟩ : ∃ t', t = c₁ :: t' := by
          cases t with
          | nil => simp at hc₁
          | cons x t' =>
            simp only [List.head?_cons, Option.some.injEq] at hc₁
            exact ⟨t', by rw [hc₁]⟩
        rw [snake_cons, mem_ledges_append]
        have hrev : l₂.reverse ≠ [] := by simpa using hl₂
        rw [head?_snake_cons _ _ hrev, List.head?_reverse, List.getLast?_map]
        constructor
        · rintro (h | h | ⟨x, y, hx, hy, he⟩)
          · exact absurd h (hblock l₂ b)
          · exfalso
            have hm := mem_of_mem_ledges h (a, b) (Sym2.mem_mk_left _ _)
            have hm' := mem_of_mem_ledges h (a', b) (Sym2.mem_mk_right _ _)
            rw [mem_snake] at hm hm'
            rcases Sym2.eq_iff.1 hs with ⟨h1, _⟩ | ⟨_, h2⟩
            · exact hc₀ (by rw [← h1]; exact hm.1)
            · exact hc₀ (by rw [← h2]; exact hm'.1)
          · obtain ⟨z, hz, rfl⟩ := Option.mem_map.1 (show x ∈ _ from hx)
            obtain ⟨z', hz', rfl⟩ := Option.mem_map.1 (show y ∈ _ from hy)
            have h2 := sym2_snd he
            have hb : b = z := by
              rcases Sym2.eq_iff.1 h2 with ⟨h, _⟩ | ⟨_, h⟩ <;> exact h
            rw [hb]
            exact Option.mem_def.1 hz
        · intro hb
          refine Or.inr (Or.inr ⟨(c₀, b), (c₁, b), ?_, ?_, ?_⟩)
          · rw [hb]; rfl
          · rw [hb]; rfl
          · rcases Sym2.eq_iff.1 hs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
            · rfl
            · exact Sym2.eq_swap
      · refine ⟨!c', fun l₂ hl₂ b => ?_⟩
        have hrev : l₂.reverse ≠ [] := by simpa using hl₂
        have hin : s(a, a') ∈ ledges (c₀ :: t) ↔ s(a, a') ∈ ledges t := by
          rw [mem_ledges_cons]
          constructor
          · rintro (h | h)
            · exact absurd h hj
            · exact h
          · exact Or.inr
        rw [hin, snake_cons, mem_ledges_append, hc' l₂.reverse hrev b, List.getLast?_reverse,
          List.head?_reverse]
        have hjun : ¬ ∃ x y, (l₂.map (c₀, ·)).getLast? = some x ∧ (snake t l₂.reverse).head? = some y ∧
            s((a, b), (a', b)) = s(x, y) := by
          rintro ⟨x, y, hx, hy, he⟩
          cases t with
          | nil => simp [snake] at hy
          | cons c₁ t' =>
            rw [head?_snake_cons _ _ hrev] at hy
            rw [List.getLast?_map] at hx
            obtain ⟨z, _, rfl⟩ := Option.mem_map.1 (show x ∈ _ from hx)
            obtain ⟨z', _, rfl⟩ := Option.mem_map.1 (show y ∈ _ from hy)
            exact hj ⟨c₁, rfl, sym2_fst he⟩
        constructor
        · rintro (h | h | h)
          · exact absurd h (hblock l₂ b)
          · cases c' <;> simpa using h
          · exact absurd h hjun
        · intro h
          refine Or.inr (Or.inl ?_)
          cases c' <;> simpa using h

end snake2

section family

variable {V : Type*} [DecidableEq V]

/-- A Hamiltonian path of `G`, as a list. -/
def IsHamList (G : SimpleGraph V) (l : List V) : Prop :=
  l.Nodup ∧ (∀ v, v ∈ l) ∧ l.IsChain G.Adj

lemma IsHamList.ne_nil {G : SimpleGraph V} {l : List V} (h : IsHamList G l) (v : V) : l ≠ [] :=
  fun he => by simpa [he] using h.2.1 v

/-- The family `L` uses every edge of `G` exactly `k` times. -/
def Fair {ι : Type*} [Fintype ι] (G : SimpleGraph V) (L : ι → List V) (k : ℕ) : Prop :=
  ∀ e ∈ G.edgeSet, (Finset.univ.filter fun i => e ∈ ledges (L i)).card = k

/-- Every vertex is the first vertex of exactly `s` paths and the last vertex of exactly `s` paths. -/
def Balanced {ι : Type*} [Fintype ι] (L : ι → List V) (s : ℕ) : Prop :=
  ∀ v, (Finset.univ.filter fun i => (L i).head? = some v).card = s ∧
    (Finset.univ.filter fun i => (L i).getLast? = some v).card = s

end family

section count

variable {V₁ V₂ : Type*} [DecidableEq V₁] [DecidableEq V₂]
variable {ι₁ ι₂ : Type*} [Fintype ι₁] [Fintype ι₂]

/-- Snakes over all pairs use every edge inside a fibre `N₁ k₂` times. -/
theorem snake_count_fibre {G₁ : SimpleGraph V₁} {G₂ : SimpleGraph V₂} {L₁ : ι₁ → List V₁}
    {L₂ : ι₂ → List V₂} (h₁ : ∀ i, IsHamList G₁ (L₁ i)) {k₂ : ℕ} (hf₂ : Fair G₂ L₂ k₂) (a : V₁)
    {b b' : V₂} (hbb : G₂.Adj b b') :
    (Finset.univ.filter fun p : ι₁ × ι₂ =>
      s((a, b), (a, b')) ∈ ledges (snake (L₁ p.1) (L₂ p.2))).card = Fintype.card ι₁ * k₂ := by
  have : (Finset.univ.filter fun p : ι₁ × ι₂ =>
      s((a, b), (a, b')) ∈ ledges (snake (L₁ p.1) (L₂ p.2))) =
      (Finset.univ : Finset ι₁) ×ˢ (Finset.univ.filter fun j => s(b, b') ∈ ledges (L₂ j)) := by
    ext ⟨i, j⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product]
    rw [mem_ledges_snake_fibre _ (h₁ i).1]
    exact ⟨fun h => h.2, fun h => ⟨(h₁ i).2.1 a, h⟩⟩
  rw [this, Finset.card_product, Finset.card_univ, hf₂ _ (G₂.mem_edgeSet.2 hbb)]

/-- Snakes over all pairs use every edge between two fibres `k₁ s₂` times. -/
theorem snake_count_cross {G₁ : SimpleGraph V₁} {G₂ : SimpleGraph V₂} {L₁ : ι₁ → List V₁}
    {L₂ : ι₂ → List V₂} (h₁ : ∀ i, IsHamList G₁ (L₁ i)) (h₂ : ∀ j, IsHamList G₂ (L₂ j))
    {k₁ s₂ : ℕ} (hf₁ : Fair G₁ L₁ k₁) (hb₂ : Balanced L₂ s₂) {a a' : V₁} (haa : G₁.Adj a a')
    (b : V₂) :
    (Finset.univ.filter fun p : ι₁ × ι₂ =>
      s((a, b), (a', b)) ∈ ledges (snake (L₁ p.1) (L₂ p.2))).card = k₁ * s₂ := by
  have hne : ∀ j, L₂ j ≠ [] := fun j h => by simpa [h] using (h₂ j).2.1 b
  rw [Finset.card_filter, Fintype.sum_prod_type]
  have key : ∀ i, (∑ j, if s((a, b), (a', b)) ∈ ledges (snake (L₁ i) (L₂ j)) then 1 else 0) =
      if s(a, a') ∈ ledges (L₁ i) then s₂ else 0 := by
    intro i
    obtain ⟨c, hc⟩ := mem_ledges_snake_cross (V₂ := V₂) (h₁ i).1 haa.ne
    by_cases hA : s(a, a') ∈ ledges (L₁ i)
    · rw [if_pos hA]
      have e : ∀ j, (s((a, b), (a', b)) ∈ ledges (snake (L₁ i) (L₂ j))) ↔
          (if c then (L₂ j).getLast? else (L₂ j).head?) = some b := fun j => by
        rw [hc _ (hne j) b]
        exact ⟨fun h => h.2, fun h => ⟨hA, h⟩⟩
      simp_rw [e]
      rw [← Finset.card_filter]
      cases c
      · simpa using (hb₂ b).1
      · simpa using (hb₂ b).2
    · rw [if_neg hA]
      refine Finset.sum_eq_zero fun j _ => ?_
      rw [if_neg]
      rw [hc _ (hne j) b]
      exact fun h => hA h.1
  refine (Finset.sum_congr rfl (fun i _ => key i)).trans ?_
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, smul_eq_mul,
    hf₁ _ (G₁.mem_edgeSet.2 haa)]

end count

section relations

variable {V : Type*} [Fintype V] [DecidableEq V] {ι : Type*} [Fintype ι]

lemma IsHamList.length {G : SimpleGraph V} {l : List V} (h : IsHamList G l) :
    l.length = Fintype.card V := by
  rw [← List.toFinset_card_of_nodup h.1, ← Finset.card_univ]
  congr 1
  ext v
  simp [h.2.1 v]

lemma card_eq_of_balanced {G : SimpleGraph V} {L : ι → List V} (hL : ∀ i, IsHamList G (L i)) {s : ℕ}
    (hb : Balanced L s) [Nonempty V] : Fintype.card ι = Fintype.card V * s := by
  have hh : ∀ i, ∃ h, (L i).head? = some h :=
    fun i => ⟨_, List.head?_eq_head ((hL i).ne_nil (Classical.arbitrary V))⟩
  calc Fintype.card ι = ∑ i : ι, ∑ v : V, (if (L i).head? = some v then 1 else 0) := by
        rw [← Finset.card_univ, Finset.card_eq_sum_ones]
        refine Finset.sum_congr rfl fun i _ => ?_
        obtain ⟨h, hh⟩ := hh i
        simp [hh]
    _ = ∑ v : V, ∑ i : ι, (if (L i).head? = some v then 1 else 0) := Finset.sum_comm
    _ = ∑ _v : V, s := Finset.sum_congr rfl fun v _ => by rw [← Finset.card_filter]; exact (hb v).1
    _ = Fintype.card V * s := by simp

lemma ledges_toFinset {G : SimpleGraph V} [DecidableRel G.Adj] {l : List V} (h : IsHamList G l) :
    G.edgeFinset.filter (fun e => e ∈ ledges l) = (ledges l).toFinset := by
  ext e
  simp only [Finset.mem_filter, mem_edgeFinset, List.mem_toFinset]
  exact ⟨fun h' => h'.2, fun h' => ⟨ledges_sub h.2.2 e h', h'⟩⟩

lemma card_ledges {G : SimpleGraph V} {l : List V} (h : IsHamList G l) :
    (ledges l).toFinset.card = Fintype.card V - 1 := by
  rw [List.toFinset_card_of_nodup (ledges_nodup h.1), length_ledges, h.length]

lemma fair_count {G : SimpleGraph V} [DecidableRel G.Adj] {L : ι → List V}
    (hL : ∀ i, IsHamList G (L i)) {k : ℕ} (hf : Fair G L k) :
    k * G.edgeFinset.card = Fintype.card ι * (Fintype.card V - 1) := by
  calc k * G.edgeFinset.card = ∑ e ∈ G.edgeFinset, k := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
    _ = ∑ e ∈ G.edgeFinset, ∑ i : ι, (if e ∈ ledges (L i) then 1 else 0) := by
        refine Finset.sum_congr rfl fun e he => ?_
        rw [← Finset.card_filter, hf e ((mem_edgeFinset).1 he)]
    _ = ∑ i : ι, ∑ e ∈ G.edgeFinset, (if e ∈ ledges (L i) then 1 else 0) := Finset.sum_comm
    _ = ∑ _i : ι, (Fintype.card V - 1) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← Finset.card_filter, ledges_toFinset (hL i), card_ledges (hL i)]
    _ = Fintype.card ι * (Fintype.card V - 1) := by simp

lemma card_edges_ge {G : SimpleGraph V} [DecidableRel G.Adj] {l : List V} (h : IsHamList G l) :
    Fintype.card V - 1 ≤ G.edgeFinset.card := by
  rw [← card_ledges h, ← ledges_toFinset h]
  exact Finset.card_filter_le _ _

lemma card_edges_le (G : SimpleGraph V) [DecidableRel G.Adj] :
    2 * G.edgeFinset.card ≤ Fintype.card V * (Fintype.card V - 1) := by
  have h := G.card_edgeFinset_le_card_choose_two
  rw [Nat.choose_two_right] at h
  calc 2 * G.edgeFinset.card ≤ 2 * (Fintype.card V * (Fintype.card V - 1) / 2) := by omega
    _ ≤ Fintype.card V * (Fintype.card V - 1) := Nat.mul_div_le _ _

end relations

/-- The arithmetic behind the positivity of the mixing weights. -/
lemma pos_aux {n₁ m₁ m₂ s₁ N₁ N₂ k₁ k₂ E₁ E₂ : ℕ} (hn₁ : n₁ = m₁ + 1) (hm₁ : 1 ≤ m₁)
    (hm₂ : 1 ≤ m₂) (hN₁ : N₁ = n₁ * s₁) (hN₂ : 0 < N₂) (hk₁ : k₁ * E₁ = N₁ * m₁)
    (hk₂ : k₂ * E₂ = N₂ * m₂) (hE₁ : m₁ ≤ E₁) (hE₂ : m₂ ≤ E₂) (hE₁' : 2 * E₁ ≤ n₁ * m₁)
    (hs₁ : 0 < s₁) : k₂ * s₁ < N₂ * k₁ := by
  have hE₁p : 0 < E₁ := by omega
  have hE₂p : 0 < E₂ := by omega
  have key : (k₂ * s₁) * (E₁ * E₂) < (N₂ * k₁) * (E₁ * E₂) := by
    have l : (k₂ * s₁) * (E₁ * E₂) = (s₁ * N₂) * (E₁ * m₂) := by
      calc (k₂ * s₁) * (E₁ * E₂) = s₁ * E₁ * (k₂ * E₂) := by ring
        _ = (s₁ * N₂) * (E₁ * m₂) := by rw [hk₂]; ring
    have r : (N₂ * k₁) * (E₁ * E₂) = (s₁ * N₂) * (E₂ * (n₁ * m₁)) := by
      calc (N₂ * k₁) * (E₁ * E₂) = N₂ * E₂ * (k₁ * E₁) := by ring
        _ = (s₁ * N₂) * (E₂ * (n₁ * m₁)) := by rw [hk₁, hN₁]; ring
    have hlt : E₁ * m₂ < E₂ * (n₁ * m₁) := by
      have a1 : E₁ * m₂ ≤ E₁ * E₂ := Nat.mul_le_mul_left _ hE₂
      have a2 : 2 * E₁ * E₂ ≤ n₁ * m₁ * E₂ := Nat.mul_le_mul_right _ hE₁'
      have a3 : 0 < E₁ * E₂ := Nat.mul_pos hE₁p hE₂p
      nlinarith
    rw [l, r]
    exact Nat.mul_lt_mul_of_pos_left hlt (Nat.mul_pos hs₁ hN₂)
  exact Nat.lt_of_mul_lt_mul_right key

section mixed

variable {V₁ V₂ : Type*} [DecidableEq V₁] [DecidableEq V₂]
variable {ι₁ ι₂ : Type*} [Fintype ι₁] [Fintype ι₂]

lemma mem_ledges_map_swap (l : List (V₂ × V₁)) (a : V₁) (b : V₂) (a' : V₁) (b' : V₂) :
    s((a, b), (a', b')) ∈ ledges (l.map Prod.swap) ↔ s((b, a), (b', a')) ∈ ledges l :=
  mem_ledges_map_of_injective Prod.swap_injective l (b, a) (b', a')

lemma sum_fin_prod {c : ℕ} {κ : Type*} [Fintype κ] (g : κ → ℕ) :
    ∑ x : Fin c × κ, g x.2 = c * ∑ y, g y := by
  rw [Fintype.sum_prod_type]
  simp

/-- `cA` copies of the snakes of `(L₁, L₂)` and `cB` swapped copies of the snakes of `(L₂, L₁)`. -/
def mixed (L₁ : ι₁ → List V₁) (L₂ : ι₂ → List V₂) (cA cB : ℕ) :
    (Fin cA × (ι₁ × ι₂)) ⊕ (Fin cB × (ι₂ × ι₁)) → List (V₁ × V₂) :=
  Sum.elim (fun x => snake (L₁ x.2.1) (L₂ x.2.2))
    (fun y => (snake (L₂ y.2.1) (L₁ y.2.2)).map Prod.swap)

theorem mixed_ham {G₁ : SimpleGraph V₁} {G₂ : SimpleGraph V₂} {L₁ : ι₁ → List V₁} {L₂ : ι₂ → List V₂}
    (h₁ : ∀ i, IsHamList G₁ (L₁ i)) (h₂ : ∀ j, IsHamList G₂ (L₂ j)) [Nonempty V₁] [Nonempty V₂]
    (cA cB : ℕ) : ∀ x, IsHamList (G₁ □ G₂) (mixed L₁ L₂ cA cB x) := by
  rintro (⟨_, i, j⟩ | ⟨_, j, i⟩)
  · refine ⟨snake_nodup (h₁ i).1 (h₂ j).1, fun v => (mem_snake _ _ _).2 ⟨(h₁ i).2.1 _, (h₂ j).2.1 _⟩,
      isChain_snake (h₁ i).2.2 (h₂ j).2.2 ((h₂ j).ne_nil (Classical.arbitrary V₂))⟩
  · refine ⟨(snake_nodup (h₂ j).1 (h₁ i).1).map Prod.swap_injective, fun v => ?_, ?_⟩
    · exact List.mem_map.2 ⟨v.swap, (mem_snake _ _ _).2 ⟨(h₂ j).2.1 _, (h₁ i).2.1 _⟩, Prod.swap_swap v⟩
    · show List.IsChain _ ((snake (L₂ j) (L₁ i)).map Prod.swap)
      rw [List.isChain_map]
      exact (isChain_snake (h₂ j).2.2 (h₁ i).2.2 ((h₁ i).ne_nil (Classical.arbitrary V₁))).imp
        (fun p q h => (boxProdComm G₂ G₁).map_adj_iff.2 h)

theorem mixed_fair {G₁ : SimpleGraph V₁} {G₂ : SimpleGraph V₂} {L₁ : ι₁ → List V₁}
    {L₂ : ι₂ → List V₂} (h₁ : ∀ i, IsHamList G₁ (L₁ i)) (h₂ : ∀ j, IsHamList G₂ (L₂ j))
    {k₁ s₁ k₂ s₂ : ℕ} (hf₁ : Fair G₁ L₁ k₁) (hb₁ : Balanced L₁ s₁) (hf₂ : Fair G₂ L₂ k₂)
    (hb₂ : Balanced L₂ s₂) {cA cB : ℕ} (hA : k₂ * s₁ + cA = Fintype.card ι₂ * k₁)
    (hB : k₁ * s₂ + cB = Fintype.card ι₁ * k₂) :
    Fair (G₁ □ G₂) (mixed L₁ L₂ cA cB) (cA * (Fintype.card ι₁ * k₂) + cB * (k₂ * s₁)) := by
  intro e he
  have hsplit : (Finset.univ.filter fun x => e ∈ ledges (mixed L₁ L₂ cA cB x)).card =
      cA * (Finset.univ.filter fun p : ι₁ × ι₂ => e ∈ ledges (snake (L₁ p.1) (L₂ p.2))).card +
      cB * (Finset.univ.filter fun q : ι₂ × ι₁ =>
        e ∈ ledges ((snake (L₂ q.1) (L₁ q.2)).map Prod.swap)).card := by
    rw [Finset.card_filter, Finset.card_filter, Finset.card_filter, Fintype.sum_sum_type]
    congr 1
    · exact sum_fin_prod (fun p : ι₁ × ι₂ => if e ∈ ledges (snake (L₁ p.1) (L₂ p.2)) then 1 else 0)
    · exact sum_fin_prod (fun q : ι₂ × ι₁ =>
        if e ∈ ledges ((snake (L₂ q.1) (L₁ q.2)).map Prod.swap) then 1 else 0)
  rw [hsplit]
  induction e using Sym2.ind with
  | _ x y =>
  obtain ⟨a, b⟩ := x
  obtain ⟨a', b'⟩ := y
  rw [mem_edgeSet, boxProd_adj] at he
  rcases he with ⟨haa, hbb⟩ | ⟨hbb, haa⟩
  · -- an edge between two fibres
    simp only at haa hbb
    subst hbb
    rw [snake_count_cross h₁ h₂ hf₁ hb₂ haa b]
    have hB' : (Finset.univ.filter fun q : ι₂ × ι₁ =>
        s((a, b), (a', b)) ∈ ledges ((snake (L₂ q.1) (L₁ q.2)).map Prod.swap)).card =
        Fintype.card ι₂ * k₁ := by
      simp_rw [mem_ledges_map_swap]
      exact snake_count_fibre h₂ hf₁ b haa
    rw [hB', ← hA, ← hB]
    ring
  · -- an edge inside a fibre
    simp only at haa hbb
    subst haa
    rw [snake_count_fibre h₁ hf₂ a hbb]
    have hB' : (Finset.univ.filter fun q : ι₂ × ι₁ =>
        s((a, b), (a, b')) ∈ ledges ((snake (L₂ q.1) (L₁ q.2)).map Prod.swap)).card =
        k₂ * s₁ := by
      simp_rw [mem_ledges_map_swap]
      exact snake_count_cross h₂ h₁ hf₂ hb₁ hbb a
    rw [hB']

end mixed

section aut

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Automorphisms of `G` as permutations. -/
abbrev AutG (G : SimpleGraph V) := {σ : Equiv.Perm V // ∀ a b, G.Adj (σ a) (σ b) ↔ G.Adj a b}

noncomputable instance (G : SimpleGraph V) : Fintype (AutG G) :=
  Fintype.ofFinite _

instance (G : SimpleGraph V) : Nonempty (AutG G) := ⟨⟨Equiv.refl V, fun _ _ => Iff.rfl⟩⟩

lemma aut_symm {G : SimpleGraph V} (σ : AutG G) (a b : V) :
    G.Adj (σ.1.symm a) (σ.1.symm b) ↔ G.Adj a b := by
  rw [← σ.2 (σ.1.symm a) (σ.1.symm b)]
  simp

/-- `ψ⁻¹ ∘ σ ∘ φ`. -/
def autConj {G : SimpleGraph V} (φ ψ σ : AutG G) : AutG G :=
  ⟨φ.1.trans (σ.1.trans ψ.1.symm), fun a b => by
    simp only [Equiv.trans_apply]
    rw [aut_symm ψ, σ.2, φ.2]⟩

def autInv {G : SimpleGraph V} (σ : AutG G) : AutG G := ⟨σ.1.symm, aut_symm σ⟩

/-- Defined by the same formula as in statement #339 / #334. -/
def IsVertexTransitive (G : SimpleGraph V) : Prop :=
  ∀ u v : V, ∃ φ : G ≃g G, φ u = v

lemma stab_card {G : SimpleGraph V} (hvt : IsVertexTransitive G) (x v x₀ : V) :
    (Finset.univ.filter fun σ : AutG G => σ.1 x = v).card =
      (Finset.univ.filter fun σ : AutG G => σ.1 x₀ = x₀).card := by
  obtain ⟨φ, hφ⟩ := hvt x₀ x
  obtain ⟨ψ, hψ⟩ := hvt x₀ v
  let φ' : AutG G := ⟨φ.toEquiv, fun a b => φ.map_adj_iff⟩
  let ψ' : AutG G := ⟨ψ.toEquiv, fun a b => ψ.map_adj_iff⟩
  refine Finset.card_nbij' (autConj φ' ψ') (autConj (autInv φ') (autInv ψ')) ?_ ?_ ?_ ?_
  · intro σ hσ
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hσ ⊢
    show ψ.symm (σ.1 (φ x₀)) = x₀
    rw [hφ, hσ, ← hψ]
    exact ψ.symm_apply_apply x₀
  · intro τ hτ
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hτ ⊢
    show ψ (τ.1 (φ.symm x)) = v
    rw [← hφ, φ.symm_apply_apply, hτ, hψ]
  · intro σ _
    apply Subtype.ext
    ext y
    show ψ (ψ.symm (σ.1 (φ (φ.symm y)))) = σ.1 y
    simp
  · intro τ _
    apply Subtype.ext
    ext y
    show ψ.symm (ψ (τ.1 (φ.symm (φ y)))) = τ.1 y
    simp

variable {ι : Type*} [Fintype ι]

/-- All images of a family under automorphisms. -/
def balancedFam (G : SimpleGraph V) (L : ι → List V) : ι × AutG G → List V :=
  fun p => (L p.1).map p.2.1

lemma balancedFam_ham {G : SimpleGraph V} {L : ι → List V} (hL : ∀ i, IsHamList G (L i)) :
    ∀ p, IsHamList G (balancedFam G L p) := by
  rintro ⟨i, σ⟩
  refine ⟨(hL i).1.map σ.1.injective, fun v => List.mem_map.2 ⟨σ.1.symm v, (hL i).2.1 _, by simp⟩, ?_⟩
  rw [balancedFam, List.isChain_map]
  exact (hL i).2.2.imp (fun x y h => (σ.2 x y).2 h)

lemma balancedFam_fair {G : SimpleGraph V} {L : ι → List V} {k : ℕ} (hf : Fair G L k) :
    Fair G (balancedFam G L) (Fintype.card (AutG G) * k) := by
  intro e he
  induction e using Sym2.ind with
  | _ x y =>
  rw [Finset.card_filter, Fintype.sum_prod_type, Finset.sum_comm]
  have key : ∀ σ : AutG G, (∑ i : ι, if s(x, y) ∈ ledges (balancedFam G L (i, σ)) then 1 else 0) = k := by
    intro σ
    have e1 : ∀ i, s(x, y) ∈ ledges (balancedFam G L (i, σ)) ↔
        s(σ.1.symm x, σ.1.symm y) ∈ ledges (L i) := by
      intro i
      have := mem_ledges_map_of_injective σ.1.injective (L i) (σ.1.symm x) (σ.1.symm y)
      simp only [Equiv.apply_symm_apply] at this
      exact this
    simp_rw [e1]
    rw [← Finset.card_filter]
    exact hf _ ((mem_edgeSet G).2 ((aut_symm σ x y).2 ((mem_edgeSet G).1 he)))
  rw [Finset.sum_congr rfl (fun σ _ => key σ)]
  simp

lemma balancedFam_balanced {G : SimpleGraph V} (hvt : IsVertexTransitive G) {L : ι → List V}
    (hL : ∀ i, IsHamList G (L i)) [Nonempty V] (x₀ : V) :
    Balanced (balancedFam G L)
      (Fintype.card ι * (Finset.univ.filter fun σ : AutG G => σ.1 x₀ = x₀).card) := by
  intro v
  have hne : ∀ i, L i ≠ [] := fun i => (hL i).ne_nil (Classical.arbitrary V)
  constructor
  · rw [Finset.card_filter, Fintype.sum_prod_type]
    have key : ∀ i, (∑ σ : AutG G, if (balancedFam G L (i, σ)).head? = some v then 1 else 0) =
        (Finset.univ.filter fun σ : AutG G => σ.1 x₀ = x₀).card := by
      intro i
      have e1 : ∀ σ : AutG G, (balancedFam G L (i, σ)).head? = some v ↔
          σ.1 ((L i).head (hne i)) = v := by
        intro σ
        rw [balancedFam, List.head?_map, List.head?_eq_head (hne i)]
        simp
      simp_rw [e1]
      rw [← Finset.card_filter]
      exact stab_card hvt _ _ _
    rw [Finset.sum_congr rfl (fun i _ => key i)]
    simp
  · rw [Finset.card_filter, Fintype.sum_prod_type]
    have key : ∀ i, (∑ σ : AutG G, if (balancedFam G L (i, σ)).getLast? = some v then 1 else 0) =
        (Finset.univ.filter fun σ : AutG G => σ.1 x₀ = x₀).card := by
      intro i
      have e1 : ∀ σ : AutG G, (balancedFam G L (i, σ)).getLast? = some v ↔
          σ.1 ((L i).getLast (hne i)) = v := by
        intro σ
        rw [balancedFam, List.getLast?_map, List.getLast?_eq_getLast (hne i)]
        simp
      simp_rw [e1]
      rw [← Finset.card_filter]
      exact stab_card hvt _ _ _
    rw [Finset.sum_congr rfl (fun i _ => key i)]
    simp

end aut

section walks

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

-- Port: `SimpleGraph.Walk.support_eq_cons` is not in Mathlib fc4f59e; this is its statement.
lemma walk_support_eq_cons {u v : V} (p : G.Walk u v) : p.support = u :: p.support.tail := by
  cases p <;> rfl

lemma mem_edges_iff_ledges : ∀ {u v : V} (p : G.Walk u v) (e : Sym2 V),
    e ∈ p.edges ↔ e ∈ ledges p.support
  | _, _, .nil, e => by simp
  | _, _, .cons h p, e => by
      rw [Walk.edges_cons, Walk.support_cons, List.mem_cons, mem_edges_iff_ledges p e,
        walk_support_eq_cons p, ledges_cons_cons, List.mem_cons]

lemma support_ofSupport : ∀ (l : List V) (hne : l ≠ []) (hc : l.IsChain G.Adj),
    (Walk.ofSupport l hne hc).support = l
  | [], hne, _ => absurd rfl hne
  | [_], _, _ => rfl
  | a :: b :: l, _, hc => by
      have ih := support_ofSupport (b :: l) (List.cons_ne_nil b l) hc.of_cons
      exact (congrArg (a :: ·) ih : _)

end walks

section final

variable {V : Type} [Fintype V] [DecidableEq V]

/-- The conclusion of statement #339 (Fair Traversal) for one graph, word for word. -/
def FTConcl (G : SimpleGraph V) : Prop :=
  ∃ (r k : ℕ), 0 < r ∧ 0 < k ∧
    ∃ (a b : Fin r → V) (P : ∀ i, G.Walk (a i) (b i)),
      (∀ i, (P i).IsHamiltonian) ∧
      ∀ e ∈ G.edgeSet, (Finset.univ.filter fun i => e ∈ (P i).edges).card = k

lemma toLists {G : SimpleGraph V} (h : FTConcl G) :
    ∃ (r k : ℕ), 0 < r ∧ 0 < k ∧ ∃ L : Fin r → List V, (∀ i, IsHamList G (L i)) ∧ Fair G L k := by
  obtain ⟨r, k, hr, hk, a, b, P, hP, hc⟩ := h
  refine ⟨r, k, hr, hk, fun i => (P i).support,
    fun i => ⟨(hP i).isPath.support_nodup, (hP i).mem_support, (P i).isChain_adj_support⟩,
    fun e he => ?_⟩
  rw [← hc e he]
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact (mem_edges_iff_ledges (P i) e).symm

lemma card_filter_equiv {ι κ : Type*} [Fintype ι] [Fintype κ] (eqv : κ ≃ ι) (p : ι → Prop)
    [DecidablePred p] :
    (Finset.univ.filter fun j => p (eqv j)).card = (Finset.univ.filter p).card := by
  rw [← Fintype.card_subtype, ← Fintype.card_subtype]
  exact Fintype.card_congr (eqv.subtypeEquiv fun _ => Iff.rfl)

lemma ofLists {G : SimpleGraph V} {ι : Type*} [Fintype ι] [Nonempty ι] (L : ι → List V)
    (hL : ∀ i, IsHamList G (L i)) {k : ℕ} (hf : Fair G L k) (hk : 0 < k) [Nonempty V] :
    FTConcl G := by
  let eqv := Fintype.equivFin ι
  have hne : ∀ i, L i ≠ [] := fun i => (hL i).ne_nil (Classical.arbitrary V)
  refine ⟨Fintype.card ι, k, Fintype.card_pos, hk, fun j => (L (eqv.symm j)).head (hne _),
    fun j => (L (eqv.symm j)).getLast (hne _), fun j => Walk.ofSupport _ (hne _) (hL _).2.2, ?_, ?_⟩
  · intro j v
    rw [support_ofSupport]
    exact List.count_eq_one_of_mem (hL _).1 ((hL _).2.1 v)
  · intro e he
    rw [← hf e he]
    have : ∀ j, e ∈ (Walk.ofSupport _ (hne (eqv.symm j)) (hL (eqv.symm j)).2.2).edges ↔
        e ∈ ledges (L (eqv.symm j)) := fun j => by
      rw [mem_edges_iff_ledges, support_ofSupport]
    simp_rw [this]
    exact card_filter_equiv eqv.symm (fun i => e ∈ ledges (L i))

/-- **Theorem 3.** Fair Traversal (the conclusion of statement #339) passes to Cartesian products of
vertex-transitive graphs with at least two vertices. -/
theorem ft_boxProd {W : Type} [Fintype W] [DecidableEq W] (G : SimpleGraph V) (H : SimpleGraph W)
    (hGv : IsVertexTransitive G) (hHv : IsVertexTransitive H) (hV : 2 ≤ Fintype.card V)
    (hW : 2 ≤ Fintype.card W) (hG : FTConcl G) (hH : FTConcl H) : FTConcl (G □ H) := by
  classical
  have : Nonempty V := Fintype.card_pos_iff.1 (by omega)
  have : Nonempty W := Fintype.card_pos_iff.1 (by omega)
  obtain ⟨r₁, k₁, hr₁, hk₁, L₁, hL₁, hf₁⟩ := toLists hG
  obtain ⟨r₂, k₂, hr₂, hk₂, L₂, hL₂, hf₂⟩ := toLists hH
  have : Nonempty (Fin r₁) := ⟨⟨0, hr₁⟩⟩
  have : Nonempty (Fin r₂) := ⟨⟨0, hr₂⟩⟩
  let x₀ : V := Classical.arbitrary V
  let y₀ : W := Classical.arbitrary W
  set c₁ := (Finset.univ.filter fun σ : AutG G => σ.1 x₀ = x₀).card
  set c₂ := (Finset.univ.filter fun σ : AutG H => σ.1 y₀ = y₀).card
  set M₁ := balancedFam G L₁
  set M₂ := balancedFam H L₂
  have hM₁ := balancedFam_ham hL₁
  have hM₂ := balancedFam_ham hL₂
  have hfM₁ := balancedFam_fair (G := G) hf₁
  have hfM₂ := balancedFam_fair (G := H) hf₂
  have hbM₁ := balancedFam_balanced hGv hL₁ x₀
  have hbM₂ := balancedFam_balanced hHv hL₂ y₀
  set N₁ := Fintype.card (Fin r₁ × AutG G)
  set N₂ := Fintype.card (Fin r₂ × AutG H)
  set K₁ := Fintype.card (AutG G) * k₁
  set K₂ := Fintype.card (AutG H) * k₂
  set S₁ := Fintype.card (Fin r₁) * c₁
  set S₂ := Fintype.card (Fin r₂) * c₂
  have hAut₁ : 0 < Fintype.card (AutG G) := Fintype.card_pos_iff.2 ⟨⟨Equiv.refl V, fun _ _ => Iff.rfl⟩⟩
  have hAut₂ : 0 < Fintype.card (AutG H) := Fintype.card_pos_iff.2 ⟨⟨Equiv.refl W, fun _ _ => Iff.rfl⟩⟩
  have hN₁p : 0 < N₁ := Fintype.card_pos
  have hN₂p : 0 < N₂ := Fintype.card_pos
  have hK₁p : 0 < K₁ := Nat.mul_pos hAut₁ hk₁
  have hK₂p : 0 < K₂ := Nat.mul_pos hAut₂ hk₂
  have hN₁ : N₁ = Fintype.card V * S₁ := card_eq_of_balanced hM₁ hbM₁
  have hN₂ : N₂ = Fintype.card W * S₂ := card_eq_of_balanced hM₂ hbM₂
  have hS₁p : 0 < S₁ := by
    rcases Nat.eq_zero_or_pos S₁ with h | h
    · rw [h, mul_zero] at hN₁; omega
    · exact h
  have hS₂p : 0 < S₂ := by
    rcases Nat.eq_zero_or_pos S₂ with h | h
    · rw [h, mul_zero] at hN₂; omega
    · exact h
  have hE₁ := fair_count hM₁ hfM₁
  have hE₂ := fair_count hM₂ hfM₂
  have hEg₁ := card_edges_ge (hM₁ (Classical.arbitrary _))
  have hEg₂ := card_edges_ge (hM₂ (Classical.arbitrary _))
  have hEl₁ := card_edges_le G
  have hEl₂ := card_edges_le H
  have hlt₁ : K₂ * S₁ < N₂ * K₁ :=
    pos_aux (n₁ := Fintype.card V) (m₁ := Fintype.card V - 1) (m₂ := Fintype.card W - 1)
      (by omega) (by omega) (by omega) hN₁ hN₂p hE₁ hE₂ hEg₁ hEg₂ hEl₁ hS₁p
  have hlt₂ : K₁ * S₂ < N₁ * K₂ :=
    pos_aux (n₁ := Fintype.card W) (m₁ := Fintype.card W - 1) (m₂ := Fintype.card V - 1)
      (by omega) (by omega) (by omega) hN₂ hN₁p hE₂ hE₁ hEg₂ hEg₁ hEl₂ hS₂p
  obtain ⟨cA, hcA⟩ := Nat.exists_eq_add_of_lt hlt₁
  obtain ⟨cB, hcB⟩ := Nat.exists_eq_add_of_lt hlt₂
  have hA : K₂ * S₁ + (cA + 1) = N₂ * K₁ := by omega
  have hB : K₁ * S₂ + (cB + 1) = N₁ * K₂ := by omega
  have : Nonempty ((Fin (cA + 1) × ((Fin r₁ × AutG G) × (Fin r₂ × AutG H))) ⊕
      (Fin (cB + 1) × ((Fin r₂ × AutG H) × (Fin r₁ × AutG G)))) :=
    ⟨Sum.inl (0, Classical.arbitrary _, Classical.arbitrary _)⟩
  exact ofLists (mixed M₁ M₂ (cA + 1) (cB + 1)) (mixed_ham hM₁ hM₂ _ _)
    (mixed_fair hM₁ hM₂ hfM₁ hbM₁ hfM₂ hbM₂ hA hB)
    (Nat.add_pos_left (Nat.mul_pos (Nat.succ_pos _) (Nat.mul_pos hN₁p hK₂p)) _)

end final

end FTProduct

#print axioms FTProduct.ft_boxProd
