/-
Copyright 2026 Ming-Chih Kao. Licensed under the Apache License, Version 2.0;
see the LICENSE file at the root of this repository.
Ported from github.com/koolkao/gillibert-fair-traversal-abelian (v1.7.0, commit
06c3a8732759afca38331762b76113135e475ac6) to Lean v4.36.0 and the module system.
Port: `Walk.IsHamiltonian.map` now takes the graph map implicitly (`(f := …)` added).
-/
module

public import FairTraversal.FTGP

/-!
# Theorem 9 in Lean, case k² ≡ −1 (mod m), m even (new in v1.6.0)

For k² ≡ −1, GP(m, k) is not a Cayley graph (Nedela–Škoviera), so the Cayley machinery of `FTGP.lean` does not apply.
We symmetrise directly over the group H of NOTE.md §9.1 (translations and φ : O_x ↦ I_{kx}, I_x ↦ O_{kx}), written as
the 4m maps `act (t, p, n) : (x, s) ↦ (c(p, n) x + t, s xor p)`, `c(p, n) = (−1)^n k^p`, each an automorphism (`aut`).

* Edge kinds `E c x` (outer rim, inner rim, spoke); `map_E`: `act g` maps kind c to kind `kap p c`; `sum_E`, `weight`:
  for edges f, e the number of g with g·f = e is 2 (both rims), 4 (both spokes) or 0.
* `orbit_path`: for a path P and an edge e of kind c', ∑_g [e ∈ g·P] = Σ_{f ∈ P} weight; `assemble2`: two Hamiltonian
  paths with multiplicities A, B balancing 2(A r₁ + B r₂) = 4(A s₁ + B s₂) > 0 give the #339 conclusion (any m ≥ 3 with
  k² ≡ −1; parts up to here do not use m even).
* m even: m = 2p, 1 + k = 2e, gcd(e, p) = 1; the band path `bandL` (rows 0, 1 of NOTE.md §9.2, m spokes) and the low
  path O_0 … O_{m−1} I_{m−1} I_{m−1+k} … (1 spoke), with A = 4p', B = 2p' + 3 (m = 2p' + 2): `ft_gp_neg_even`.
-/

@[expose] public section


open Finset

namespace FTGPN
open FTGP

section Edges
variable (m : ℕ) (k : ℤ)

/-- edge kinds: outer rim, inner rim, spoke -/
inductive K | out | inn | sp
  deriving DecidableEq

instance : Fintype K := ⟨{.out, .inn, .sp}, by intro x; cases x <;> simp⟩

/-- the edge of kind `c` at `x` -/
def E : K → ZMod m → Sym2 (ZMod m × Bool)
  | .out, x => s((x, false), (x + 1, false))
  | .inn, x => s((x, true), (x + k, true))
  | .sp, x => s((x, false), (x, true))

/-- the coefficient `(−1)^n k^p` -/
def cf (p n : Bool) : ZMod m := (if n then -1 else 1) * (if p then (k : ZMod m) else 1)

/-- the map `(x, s) ↦ (c x + t, s xor p)` -/
def act (g : ZMod m × Bool × Bool) (v : ZMod m × Bool) : ZMod m × Bool :=
  (cf m k g.2.1 g.2.2 * v.1 + g.1, xor v.2 g.2.1)

/-- kind after `act` -/
def kap (p : Bool) : K → K
  | .out => if p then .inn else .out
  | .inn => if p then .out else .inn
  | .sp => .sp

end Edges

section Neg
variable {m : ℕ} [NeZero m] {k : ℤ} (hkk : (k : ZMod m) * k = -1)
include hkk

omit hkk in
lemma s_eq {a b c d : ZMod m × Bool} (h1 : a = c) (h2 : b = d) : s(a, b) = s(c, d) := by rw [h1, h2]

omit hkk in
lemma s_eq' {a b c d : ZMod m × Bool} (h1 : a = d) (h2 : b = c) : s(a, b) = s(c, d) := by
  rw [h1, h2, Sym2.eq_swap]

lemma map_E (p n : Bool) (c : K) (x : ZMod m) :
    ∃ y : ZMod m, ∀ t : ZMod m, Sym2.map (act m k (t, p, n)) (E m k c x) = E m k (kap p c) (y + t) := by
  have h2 : (k : ZMod m) ^ 2 = -1 := by rw [sq]; exact hkk
  cases c <;> cases p <;> cases n
  · exact ⟨x, fun t => by
      simp only [E, act, cf, kap, Sym2.map_mk]; apply s_eq <;> ext <;> simp <;> ring⟩
  · exact ⟨-x - 1, fun t => by
      simp only [E, act, cf, kap, Sym2.map_mk]; apply s_eq' <;> ext <;> simp <;> ring⟩
  · exact ⟨k * x, fun t => by
      simp only [E, act, cf, kap, Sym2.map_mk]; apply s_eq <;> ext <;> simp <;> ring⟩
  · exact ⟨-(k * x) - k, fun t => by
      simp only [E, act, cf, kap, Sym2.map_mk]; apply s_eq' <;> ext <;> simp <;> ring⟩
  · exact ⟨x, fun t => by
      simp only [E, act, cf, kap, Sym2.map_mk]; apply s_eq <;> ext <;> simp <;> ring⟩
  · exact ⟨-x - k, fun t => by
      simp only [E, act, cf, kap, Sym2.map_mk]; apply s_eq' <;> ext <;> simp <;> ring⟩
  · exact ⟨k * x - 1, fun t => by
      simp only [E, act, cf, kap, Sym2.map_mk]
      apply s_eq' <;> ext <;> simp <;> first | ring1 | linear_combination h2 | linear_combination -h2 | linear_combination (-2) * h2 | linear_combination 2 * h2⟩
  · exact ⟨-(k * x), fun t => by
      simp only [E, act, cf, kap, Sym2.map_mk]
      apply s_eq <;> ext <;> simp <;> first | ring1 | linear_combination h2 | linear_combination -h2 | linear_combination (-2) * h2 | linear_combination 2 * h2⟩
  · exact ⟨x, fun t => by
      simp only [E, act, cf, kap, Sym2.map_mk]; apply s_eq <;> ext <;> simp <;> ring⟩
  · exact ⟨-x, fun t => by
      simp only [E, act, cf, kap, Sym2.map_mk]; apply s_eq <;> ext <;> simp <;> ring⟩
  · exact ⟨k * x, fun t => by
      simp only [E, act, cf, kap, Sym2.map_mk]; apply s_eq' <;> ext <;> simp <;> ring⟩
  · exact ⟨-(k * x), fun t => by
      simp only [E, act, cf, kap, Sym2.map_mk]; apply s_eq' <;> ext <;> simp <;> ring⟩

end Neg

/-! ### the graph, its edges, and the maps `act g` as automorphisms -/

section Graph
variable {m : ℕ} [NeZero m] {k : ℤ} (hkk : (k : ZMod m) * k = -1) (hm : 3 ≤ m)

omit [NeZero m] in
lemma two_ne (hm : 3 ≤ m) : (1 : ZMod m) + 1 ≠ 0 := by
  intro h
  have h2 : ((2 : ℕ) : ZMod m) = 0 := by rw [Nat.cast_ofNat, ← one_add_one_eq_two]; exact h
  have := Nat.le_of_dvd (by norm_num) ((ZMod.natCast_eq_zero_iff 2 m).1 h2)
  omega

include hkk hm in
lemma twok_ne : (k : ZMod m) + k ≠ 0 := by
  intro h
  apply two_ne hm
  have : ((k : ZMod m) + k) * k = 0 := by rw [h, zero_mul]
  linear_combination -this + 2 * hkk

include hkk hm in
lemma k_ne : (k : ZMod m) ≠ 0 := by
  intro h
  have h0 := hkk
  rw [h, zero_mul] at h0
  have h1 : (1 : ZMod m) = 0 := by linear_combination h0
  exact two_ne hm (by rw [h1, add_zero])

omit [NeZero m] in
lemma one_ne (hm : 3 ≤ m) : (1 : ZMod m) ≠ 0 := fun h => two_ne hm (by rw [h, add_zero])

include hkk hm in
lemma E_inj {c c' : K} {a b : ZMod m} : E m k c a = E m k c' b ↔ c = c' ∧ a = b := by
  constructor
  · intro h
    have h2 := two_ne hm
    have h2k := twok_ne hkk hm
    cases c <;> cases c' <;> simp only [E, Sym2.eq_iff, Prod.mk.injEq, and_true, true_and] at h
    all_goals (try (simp at h; done))
    · refine ⟨rfl, ?_⟩
      rcases h with ⟨h1, -⟩ | ⟨h1, h3⟩
      · exact h1
      · exfalso; apply h2; rw [h1] at h3; linear_combination h3
    · refine ⟨rfl, ?_⟩
      rcases h with ⟨h1, -⟩ | ⟨h1, h3⟩
      · exact h1
      · exfalso; apply h2k; rw [h1] at h3; linear_combination h3
    · refine ⟨rfl, ?_⟩
      rcases h with h1 | h1
      · exact h1.1
      · simp at h1
  · rintro ⟨rfl, rfl⟩; rfl

omit [NeZero m] in
lemma E_mem (hm : 3 ≤ m) (hk0 : (k : ZMod m) ≠ 0) (c : K) (x : ZMod m) : E m k c x ∈ (gp m k).edgeSet := by
  cases c <;> simp only [E, SimpleGraph.mem_edgeSet, gp, SimpleGraph.fromRel_adj, gpRel]
  · refine ⟨fun h => ?_, by simp⟩
    have := congrArg Prod.fst h; simp at this
    exact one_ne hm this
  · refine ⟨fun h => ?_, by simp⟩
    have := congrArg Prod.fst h; simp at this
    exact hk0 this
  · refine ⟨fun h => ?_, by simp⟩
    have := congrArg Prod.snd h; simp at this

omit [NeZero m] in
lemma edge_cases (e : Sym2 (ZMod m × Bool)) (he : e ∈ (gp m k).edgeSet) : ∃ c x, e = E m k c x := by
  induction e using Sym2.ind with
  | h u v =>
    obtain ⟨x, i⟩ := u
    obtain ⟨y, j⟩ := v
    simp only [SimpleGraph.mem_edgeSet, gp, SimpleGraph.fromRel_adj, gpRel] at he
    obtain ⟨-, h | h⟩ := he
    · rcases h with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ <;> subst h1 h2 h3
      · exact ⟨.out, _, rfl⟩
      · exact ⟨.inn, _, rfl⟩
      · exact ⟨.sp, _, rfl⟩
    · rcases h with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ <;> subst h1 h2 h3
      · exact ⟨.out, _, Sym2.eq_swap⟩
      · exact ⟨.inn, _, Sym2.eq_swap⟩
      · exact ⟨.sp, _, Sym2.eq_swap⟩

/-- the inverse parameters -/
def ginv (k : ℤ) (g : ZMod m × Bool × Bool) : ZMod m × Bool × Bool :=
  (-(cf m k g.2.1 (xor g.2.2 g.2.1) * g.1), g.2.1, xor g.2.2 g.2.1)

include hkk in
lemma cf_inv (p n : Bool) : cf m k p (xor n p) * cf m k p n = 1 := by
  cases p <;> cases n <;> simp [cf] <;> linear_combination -hkk

include hkk in
lemma act_ginv (g : ZMod m × Bool × Bool) (v : ZMod m × Bool) : act m k (ginv k g) (act m k g v) = v := by
  obtain ⟨t, p, n⟩ := g
  obtain ⟨x, s⟩ := v
  have h := cf_inv hkk p n
  simp only [act, ginv, Prod.mk.injEq]
  constructor
  · linear_combination x * h
  · cases s <;> cases p <;> rfl

include hkk in
lemma ginv_ginv_act (g : ZMod m × Bool × Bool) (v : ZMod m × Bool) : act m k g (act m k (ginv k g) v) = v := by
  obtain ⟨t, p, n⟩ := g
  obtain ⟨x, s⟩ := v
  have h := cf_inv hkk p n
  simp only [act, ginv, Prod.mk.injEq]
  constructor
  · linear_combination (x - t) * h
  · cases s <;> cases p <;> rfl

include hkk hm in
lemma act_adj (g : ZMod m × Bool × Bool) (u v : ZMod m × Bool) (h : (gp m k).Adj u v) :
    (gp m k).Adj (act m k g u) (act m k g v) := by
  have he : s(u, v) ∈ (gp m k).edgeSet := h
  obtain ⟨c, x, hcx⟩ := edge_cases s(u, v) he
  obtain ⟨t, p, n⟩ := g
  obtain ⟨y, hy⟩ := map_E hkk p n c x
  have h1 : s(act m k (t, p, n) u, act m k (t, p, n) v) = E m k (kap p c) (y + t) := by
    rw [← hy t, ← hcx]
    rfl
  have := E_mem hm (k_ne hkk hm) (kap p c) (y + t)
  rw [← h1] at this
  exact this

/-- `act g` as an automorphism of `gp m k` -/
def aut (g : ZMod m × Bool × Bool) : gp m k ≃g gp m k where
  toFun := act m k g
  invFun := act m k (ginv k g)
  left_inv v := act_ginv hkk g v
  right_inv v := ginv_ginv_act hkk g v
  map_rel_iff' := by
    intro u v
    constructor
    · intro h
      change (gp m k).Adj (act m k g u) (act m k g v) at h
      have := act_adj hkk hm (ginv k g) _ _ h
      rwa [act_ginv hkk, act_ginv hkk] at this
    · intro h; exact act_adj hkk hm g u v h

@[simp] lemma aut_apply (g : ZMod m × Bool × Bool) (v : ZMod m × Bool) : aut hkk hm g v = act m k g v := rfl

/-! ### orbit counts -/

include hkk hm in
lemma sum_E (c c' : K) (x y : ZMod m) :
    ∑ g : ZMod m × Bool × Bool, (if Sym2.map (act m k g) (E m k c x) = E m k c' y then 1 else 0 : ℕ) =
      ∑ p : Bool, ∑ _n : Bool, (if kap p c = c' then 1 else 0 : ℕ) := by
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun p _ => Finset.sum_congr rfl (fun n _ => ?_))
  obtain ⟨y0, hy⟩ := map_E hkk p n c x
  simp only [hy, E_inj hkk hm]
  by_cases hc : kap p c = c'
  · simp only [hc, true_and, if_true]
    rw [Finset.sum_eq_single (y - y0)]
    · simp
    · intro t _ ht; rw [if_neg]; intro h; apply ht; rw [← h]; ring
    · simp
  · simp [hc]

lemma weight (c c' : K) : (∑ p : Bool, ∑ _n : Bool, (if kap p c = c' then 1 else 0 : ℕ)) =
    if c' = .sp then (if c = .sp then 4 else 0) else (if c = .sp then 0 else 2) := by
  cases c <;> cases c' <;> simp [kap]

end Graph

/-! ### symmetrisation of a path -/

section Sym
variable {m : ℕ} [NeZero m] {k : ℤ} (hkk : (k : ZMod m) * k = -1) (hm : 3 ≤ m)

/-- spokes -/
def spk (m : ℕ) (k : ℤ) (f : Sym2 (ZMod m × Bool)) : Prop := ∃ x, f = E m k .sp x

open Classical in
/-- the orbit weight of a path edge `f` at an edge of kind `c'` -/
noncomputable def wt (m : ℕ) (k : ℤ) (c' : K) (f : Sym2 (ZMod m × Bool)) : ℕ :=
  if spk m k f then (if c' = .sp then 4 else 0) else (if c' = .sp then 0 else 2)

omit [NeZero m] in
lemma ind_map {α β : Type} [DecidableEq β] (F : α → β) (hF : Function.Injective F) (e : β) :
    ∀ l : List α, l.Nodup → (if e ∈ l.map F then 1 else 0 : ℕ) = (l.map fun f => if F f = e then 1 else 0).sum
  | [], _ => by simp
  | a :: l, h => by
    rw [List.nodup_cons] at h
    rw [List.map_cons, List.map_cons, List.sum_cons, ← ind_map F hF e l h.2]
    by_cases ha : F a = e
    · have : e ∉ l.map F := by
        rw [← ha]; intro h'; obtain ⟨b, hb, hb'⟩ := List.mem_map.1 h'; exact h.1 (hF hb' ▸ hb)
      have hm : e ∈ F a :: l.map F := by rw [ha]; exact List.mem_cons_self
      rw [if_pos hm, if_pos ha, if_neg this]
    · have : ¬ e = F a := fun h' => ha h'.symm
      rw [if_neg ha, zero_add]
      by_cases hl : e ∈ l.map F
      · rw [if_pos hl, if_pos (List.mem_cons_of_mem _ hl)]
      · rw [if_neg hl, if_neg]; rw [List.mem_cons]; tauto

omit [NeZero m] in
lemma sum_list_comm {α ι : Type} [Fintype ι] (h : ι → α → ℕ) :
    ∀ l : List α, ∑ g, (l.map (h g)).sum = (l.map fun f => ∑ g, h g f).sum
  | [] => by simp
  | a :: l => by simp [List.sum_cons, Finset.sum_add_distrib, sum_list_comm h l]

include hkk hm in
lemma orbit_path {u v : ZMod m × Bool} (P : (gp m k).Walk u v) (hP : P.IsPath) (c' : K) (y : ZMod m) :
    ∑ g : ZMod m × Bool × Bool, (if E m k c' y ∈ (P.map (aut hkk hm g).toHom).edges then 1 else 0 : ℕ) =
      (P.edges.map (wt m k c')).sum := by
  classical
  have hnd := hP.isTrail.edges_nodup
  have h1 : ∀ g : ZMod m × Bool × Bool,
      (if E m k c' y ∈ (P.map (aut hkk hm g).toHom).edges then 1 else 0 : ℕ) =
        (P.edges.map fun f => if Sym2.map (act m k g) f = E m k c' y then 1 else 0).sum := by
    intro g
    rw [SimpleGraph.Walk.edges_map]
    exact ind_map (Sym2.map (aut hkk hm g).toHom) (Sym2.map.injective (aut hkk hm g).injective) _ _ hnd
  simp only [h1]
  rw [sum_list_comm (fun g f => if Sym2.map (act m k g) f = E m k c' y then 1 else 0)]
  congr 1
  apply List.map_congr_left
  intro f hf
  obtain ⟨c, x, rfl⟩ := edge_cases f (SimpleGraph.Walk.edges_subset_edgeSet P hf)
  rw [sum_E hkk hm, weight]
  have hs : spk m k (E m k c x) ↔ c = .sp := by
    constructor
    · rintro ⟨z, hz⟩; exact ((E_inj hkk hm).1 hz).1
    · rintro rfl; exact ⟨x, rfl⟩
  unfold wt
  by_cases hc : c = .sp
  · rw [if_pos (hs.2 hc)]; simp [hc]
  · rw [if_neg (fun h => hc (hs.1 h))]; simp [hc]

open Classical in
omit [NeZero m] in
lemma sum_wt (c' : K) : ∀ l : List (Sym2 (ZMod m × Bool)),
    (l.map (wt m k c')).sum = if c' = .sp then 4 * l.countP (fun f => decide (spk m k f))
      else 2 * l.countP (fun f => decide (¬ spk m k f))
  | [] => by simp
  | a :: l => by
    rw [List.map_cons, List.sum_cons, sum_wt c' l, List.countP_cons, List.countP_cons]
    unfold wt
    by_cases ha : spk m k a <;> by_cases hc : c' = .sp <;> simp [ha, hc] <;> ring

/-- indicator of an edge on a walk -/
def indE (m : ℕ) (k : ℤ) (e : Sym2 (ZMod m × Bool)) (w : Σ u v : ZMod m × Bool, (gp m k).Walk u v) : ℕ :=
  if e ∈ w.2.2.edges then 1 else 0

open Classical in
include hkk hm in
/-- **Assembly.** Two Hamiltonian paths with spoke counts `s₁, s₂` and rim counts `r₁, r₂`, and multiplicities
`A, B` balancing `2(A r₁ + B r₂) = 4(A s₁ + B s₂) > 0`, give the #339 conclusion. -/
theorem assemble2 {a1 b1 a2 b2 : ZMod m × Bool} (P1 : (gp m k).Walk a1 b1) (P2 : (gp m k).Walk a2 b2)
    (h1 : P1.IsHamiltonian) (h2 : P2.IsHamiltonian) (A B : ℕ)
    (hbal : 2 * (A * P1.edges.countP (fun f => decide (¬ spk m k f)) +
        B * P2.edges.countP (fun f => decide (¬ spk m k f))) =
      4 * (A * P1.edges.countP (fun f => decide (spk m k f)) + B * P2.edges.countP (fun f => decide (spk m k f))))
    (hpos : 0 < A * P1.edges.countP (fun f => decide (spk m k f)) +
      B * P2.edges.countP (fun f => decide (spk m k f))) :
    ∃ (r k' : ℕ), 0 < r ∧ 0 < k' ∧
      ∃ (a b : Fin r → ZMod m × Bool) (P : ∀ i, (gp m k).Walk (a i) (b i)),
        (∀ i, (P i).IsHamiltonian) ∧
        ∀ e ∈ (gp m k).edgeSet, (Finset.univ.filter fun i => e ∈ (P i).edges).card = k' := by
  let ι := (Fin A × (ZMod m × Bool × Bool)) ⊕ (Fin B × (ZMod m × Bool × Bool))
  let W : ι → Σ u v : ZMod m × Bool, (gp m k).Walk u v :=
    Sum.elim (fun q => ⟨_, _, P1.map (aut hkk hm q.2).toHom⟩) (fun q => ⟨_, _, P2.map (aut hkk hm q.2).toHom⟩)
  have hW : ∀ i, (W i).2.2.IsHamiltonian := by
    intro i; rcases i with ⟨_, g⟩ | ⟨_, g⟩
    · exact h1.map (f := (aut hkk hm g).toHom) (aut hkk hm g).bijective
    · exact h2.map (f := (aut hkk hm g).toHom) (aut hkk hm g).bijective
  let eqv := Fintype.equivFin ι
  set S1 := P1.edges.countP (fun f => decide (spk m k f))
  set S2 := P2.edges.countP (fun f => decide (spk m k f))
  have key : ∀ (n : ℕ) (F : ZMod m × Bool × Bool → ℕ), ∑ _x : Fin n, ∑ g, F g = n * ∑ g, F g :=
    fun n F => by simp
  have hcnt : ∀ e ∈ (gp m k).edgeSet,
      (Finset.univ.filter fun t : Fin (Fintype.card ι) => e ∈ (W (eqv.symm t)).2.2.edges).card =
        4 * (A * S1 + B * S2) := by
    intro e he
    obtain ⟨c', y, rfl⟩ := edge_cases e he
    rw [Finset.card_filter]
    show ∑ t, indE m k (E m k c' y) (W (eqv.symm t)) = _
    rw [Equiv.sum_comp eqv.symm (fun i => indE m k (E m k c' y) (W i))]
    rw [Fintype.sum_sum_type, Fintype.sum_prod_type, Fintype.sum_prod_type]
    simp only [W, Sum.elim_inl, Sum.elim_inr]
    rw [key A, key B]
    simp only [indE]
    rw [orbit_path hkk hm P1 h1.isPath c' y, orbit_path hkk hm P2 h2.isPath c' y, sum_wt, sum_wt]
    by_cases hc : c' = .sp
    · simp only [hc, if_true]; ring
    · simp only [hc, if_false]; rw [← hbal]; ring
  refine ⟨Fintype.card ι, 4 * (A * S1 + B * S2), ?_, by omega, fun t => (W (eqv.symm t)).1,
    fun t => (W (eqv.symm t)).2.1, fun t => (W (eqv.symm t)).2.2, fun t => hW _, hcnt⟩
  rcases Nat.eq_zero_or_pos A with hA | hA
  · have hB : 0 < B := by
      rcases Nat.eq_zero_or_pos B with hB | hB
      · rw [hA, hB] at hpos; simp at hpos
      · exact hB
    exact Fintype.card_pos_iff.2 ⟨.inr ⟨⟨0, hB⟩, 0⟩⟩
  · exact Fintype.card_pos_iff.2 ⟨.inl ⟨⟨0, hA⟩, 0⟩⟩

end Sym

/-! ### walks from vertex lists -/

section Walks
variable {V : Type} (G : SimpleGraph V)

/-- the walk through `u :: l` -/
def wk : (u : V) → (l : List V) → List.IsChain G.Adj (u :: l) → Σ w, G.Walk u w
  | u, [], _ => ⟨u, .nil⟩
  | u, v :: l, h => ⟨(wk v l (List.isChain_cons_cons.1 h).2).1,
      .cons (List.isChain_cons_cons.1 h).1 (wk v l (List.isChain_cons_cons.1 h).2).2⟩

/-- consecutive pairs -/
def eds : List V → List (Sym2 V)
  | a :: b :: l => s(a, b) :: eds (b :: l)
  | _ => []

lemma wk_support : ∀ (u : V) (l : List V) (h : List.IsChain G.Adj (u :: l)), (wk G u l h).2.support = u :: l
  | _, [], _ => rfl
  | u, v :: l, h => by
    simp only [wk, SimpleGraph.Walk.support_cons]; rw [wk_support]

lemma wk_edges : ∀ (u : V) (l : List V) (h : List.IsChain G.Adj (u :: l)), (wk G u l h).2.edges = eds (u :: l)
  | _, [], _ => rfl
  | u, v :: l, h => by
    simp only [wk, SimpleGraph.Walk.edges_cons, eds]; rw [wk_edges]

lemma wk_ham [Fintype V] [DecidableEq V] (u : V) (l : List V) (h : List.IsChain G.Adj (u :: l)) (hnd : (u :: l).Nodup)
    (hall : ∀ x, x ∈ u :: l) : (wk G u l h).2.IsHamiltonian := by
  intro x
  rw [wk_support]
  exact List.count_eq_one_of_mem hnd (hall x)

end Walks

/-! ### the two paths (k² ≡ −1, m even) -/

section Paths
variable {m : ℕ} [NeZero m] {k : ℤ}

/-- `O_{r − n(1+k)}` -/
def EOn (m : ℕ) (k : ℤ) (r n : ℤ) : ZMod m × Bool := (((r - n * (1 + k) : ℤ) : ZMod m), false)
/-- `I_{r − n(1+k)}` -/
def EIn (m : ℕ) (k : ℤ) (r n : ℤ) : ZMod m × Bool := (((r - n * (1 + k) : ℤ) : ZMod m), true)

/-- the square band (rows 0, 1) traversed from `O_0` -/
def bandL (m : ℕ) (k : ℤ) : ℕ → ℤ → List (ZMod m × Bool)
  | 0, _ => []
  | i + 1, n => [EOn m k 0 n, EIn m k 0 n, EIn m k 1 (n + 1), EOn m k 1 (n + 1)] ++ bandL m k i (n + 1)

/-- `O_x, O_{x+1}, …` -/
def oL (m : ℕ) : ℕ → ℤ → List (ZMod m × Bool)
  | 0, _ => []
  | n + 1, x => ((x : ZMod m), false) :: oL m n (x + 1)

/-- `I_x, I_{x+k}, …` -/
def iL (m : ℕ) (k : ℤ) : ℕ → ℤ → List (ZMod m × Bool)
  | 0, _ => []
  | n + 1, x => ((x : ZMod m), true) :: iL m k n (x + k)

variable (hm : 3 ≤ m) (hk0 : (k : ZMod m) ≠ 0)
include hm hk0

omit [NeZero m] in
lemma adjOO (x : ZMod m) : (gp m k).Adj (x, false) (x + 1, false) := by
  simp only [gp, SimpleGraph.fromRel_adj, gpRel]
  refine ⟨fun h => one_ne hm ?_, by simp⟩
  have := congrArg Prod.fst h; simpa using this

omit [NeZero m] in
lemma adjII (x : ZMod m) : (gp m k).Adj (x, true) (x + k, true) := by
  simp only [gp, SimpleGraph.fromRel_adj, gpRel]
  refine ⟨fun h => hk0 ?_, by simp⟩
  have := congrArg Prod.fst h; simpa using this

omit hm hk0 [NeZero m] in
lemma adjOI (x : ZMod m) : (gp m k).Adj (x, false) (x, true) := by
  simp only [gp, SimpleGraph.fromRel_adj, gpRel]
  exact ⟨fun h => by simp at h, by simp⟩

omit [NeZero m] in
lemma band_chain : ∀ (i : ℕ) (n : ℤ), List.IsChain (gp m k).Adj (bandL m k (i + 1) n)
  | 0, n => by
    simp only [bandL, List.cons_append, List.nil_append, List.append_nil, List.isChain_cons_cons,
      List.isChain_singleton, and_true]
    refine ⟨adjOI _, ?_, (adjOI _).symm⟩
    have := (adjII hm hk0 (((1 - (n + 1) * (1 + k) : ℤ) : ZMod m))).symm
    convert this using 3 <;> simp only [EOn, EIn] <;> push_cast <;> ring
  | i + 1, n => by
    have ih := band_chain i (n + 1)
    simp only [bandL, List.cons_append, List.nil_append] at ih ⊢
    rw [List.isChain_cons_cons, List.isChain_cons_cons, List.isChain_cons_cons, List.isChain_cons_cons]
    refine ⟨adjOI _, ?_, (adjOI _).symm, ?_, ih⟩
    · have := (adjII hm hk0 (((1 - (n + 1) * (1 + k) : ℤ) : ZMod m))).symm
      convert this using 3 <;> simp only [EOn, EIn] <;> push_cast <;> ring
    · have := (adjOO hm hk0 (((0 - (n + 1) * (1 + k) : ℤ) : ZMod m))).symm
      convert this using 3 <;> simp only [EOn, EIn] <;> push_cast <;> ring

omit [NeZero m] in
lemma iL_chain : ∀ (n : ℕ) (x : ℤ), List.IsChain (gp m k).Adj (iL m k n x)
  | 0, _ => by simp [iL, List.isChain_nil]
  | 1, _ => by simp [iL, List.isChain_singleton]
  | n + 2, x => by
    have ih := iL_chain (n + 1) (x + k)
    simp only [iL] at ih ⊢
    rw [List.isChain_cons_cons]
    refine ⟨?_, ih⟩
    have := adjII hm hk0 ((x : ZMod m)); convert this using 3; push_cast; ring

omit [NeZero m] in
lemma oL_chain : ∀ (n : ℕ) (x : ℤ) (t : List (ZMod m × Bool)),
    List.IsChain (gp m k).Adj ((((x + n : ℤ) : ZMod m), false) :: t) → List.IsChain (gp m k).Adj (oL m (n + 1) x ++ t)
  | 0, x, t, h => by simpa [oL] using h
  | n + 1, x, t, h => by
    have ih := oL_chain n (x + 1) t (by convert h using 4; push_cast; ring)
    simp only [oL, List.cons_append] at ih ⊢
    rw [List.isChain_cons_cons]
    refine ⟨?_, ih⟩
    have := adjOO hm hk0 ((x : ZMod m)); convert this using 3; push_cast; ring

end Paths

/-! ### distinctness and spoke counts -/

section Count
variable {m : ℕ} [NeZero m] {k : ℤ}

omit [NeZero m] in
lemma keyN {d p : ℕ} {e : ℤ} (hm : (m : ℤ) = d * p) (he : 1 + k = d * e) (hcop : IsCoprime e (p : ℤ))
    (hd : 0 < d) {r n r' n' : ℤ} (hr : 0 ≤ r ∧ r < d) (hr' : 0 ≤ r' ∧ r' < d)
    (h : (((r - n * (1 + k) : ℤ)) : ZMod m) = (((r' - n' * (1 + k) : ℤ)) : ZMod m)) :
    r = r' ∧ (p : ℤ) ∣ n - n' := by
  have h0 : (((r - n * (1 + k)) - (r' - n' * (1 + k)) : ℤ) : ZMod m) = 0 := by
    push_cast; push_cast at h; rw [h, sub_self]
  have hdv := (ZMod.intCast_zmod_eq_zero_iff_dvd _ m).1 h0
  rw [hm, he] at hdv
  have hdr : (d : ℤ) ∣ r - r' := by
    have h1 : (d : ℤ) ∣ (r - n * (d * e)) - (r' - n' * (d * e)) := dvd_trans (dvd_mul_right _ _) hdv
    have e1 : (r - n * (d * e)) - (r' - n' * (d * e)) = (r - r') + (d : ℤ) * ((n' - n) * e) := by ring
    rw [e1] at h1
    have := dvd_sub h1 (dvd_mul_right (d : ℤ) ((n' - n) * e))
    rwa [add_sub_cancel_right] at this
  have hrr : r = r' := by
    have := Int.eq_zero_of_abs_lt_dvd hdr (by rw [abs_lt]; constructor <;> omega)
    omega
  refine ⟨hrr, ?_⟩
  subst hrr
  have e2 : (r - n * (d * e)) - (r - n' * (d * e)) = (d : ℤ) * ((n' - n) * e) := by ring
  rw [e2] at hdv
  have hd0 : (d : ℤ) ≠ 0 := by exact_mod_cast hd.ne'
  have h3 := Int.dvd_of_mul_dvd_mul_left hd0 hdv
  have h4 : (p : ℤ) ∣ n' - n := hcop.symm.dvd_of_dvd_mul_right h3
  rw [← dvd_neg, neg_sub]; exact h4

omit [NeZero m] in
lemma neN {d p : ℕ} {e : ℤ} (hm : (m : ℤ) = d * p) (he : 1 + k = d * e) (hcop : IsCoprime e (p : ℤ))
    (hd : 0 < d) {r n r' n' : ℤ} (t : ℤ)
    (H : 0 ≤ r ∧ r < d ∧ 0 ≤ r' ∧ r' < d ∧ (r ≠ r' ∨ (n - n' = t ∧ t ≠ 0 ∧ -(p : ℤ) < t ∧ t < p)))
    (h : (((r - n * (1 + k) : ℤ)) : ZMod m) = (((r' - n' * (1 + k) : ℤ)) : ZMod m)) : False := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := H
  obtain ⟨hrr, hp⟩ := keyN hm he hcop hd ⟨h1, h2⟩ ⟨h3, h4⟩ h
  rcases h5 with h5 | ⟨hn, ht0, ht1, ht2⟩
  · exact h5 hrr
  · rw [hn] at hp
    exact ht0 (Int.eq_zero_of_abs_lt_dvd hp (by rw [abs_lt]; constructor <;> omega))

omit [NeZero m] in
lemma neO' {d p : ℕ} {e : ℤ} (hm : (m : ℤ) = d * p) (he : 1 + k = d * e) (hcop : IsCoprime e (p : ℤ))
    (hd : 0 < d) {r n r' n' : ℤ} (t : ℤ)
    (H : 0 ≤ r ∧ r < d ∧ 0 ≤ r' ∧ r' < d ∧ (r ≠ r' ∨ (n - n' = t ∧ t ≠ 0 ∧ -(p : ℤ) < t ∧ t < p)))
    (h : EOn m k r n = EOn m k r' n') : False :=
  neN hm he hcop hd t H (congrArg Prod.fst h)

omit [NeZero m] in
lemma neI' {d p : ℕ} {e : ℤ} (hm : (m : ℤ) = d * p) (he : 1 + k = d * e) (hcop : IsCoprime e (p : ℤ))
    (hd : 0 < d) {r n r' n' : ℤ} (t : ℤ)
    (H : 0 ≤ r ∧ r < d ∧ 0 ≤ r' ∧ r' < d ∧ (r ≠ r' ∨ (n - n' = t ∧ t ≠ 0 ∧ -(p : ℤ) < t ∧ t < p)))
    (h : EIn m k r n = EIn m k r' n') : False :=
  neN hm he hcop hd t H (congrArg Prod.fst h)

omit [NeZero m] in
lemma EOn_ne_EIn (r n r' n' : ℤ) : EOn m k r n ≠ EIn m k r' n' := by
  intro h; have := congrArg Prod.snd h; simp [EOn, EIn] at this

omit [NeZero m] in
lemma EOn_eq {r r' n n' : ℤ} (h1 : r = r') (h2 : n = n') : EOn m k r n = EOn m k r' n' := by subst h1 h2; rfl
omit [NeZero m] in
lemma EIn_eq {r r' n n' : ℤ} (h1 : r = r') (h2 : n = n') : EIn m k r n = EIn m k r' n' := by subst h1 h2; rfl

omit [NeZero m] in
lemma mem_band : ∀ (i : ℕ) (n : ℤ) (x : ZMod m × Bool), x ∈ bandL m k i n →
    ∃ j : ℕ, j < i ∧ (x = EOn m k 0 (n + j) ∨ x = EIn m k 0 (n + j) ∨ x = EIn m k 1 (n + j + 1) ∨
      x = EOn m k 1 (n + j + 1))
  | 0, n, x, h => by simp [bandL] at h
  | i + 1, n, x, h => by
    simp only [bandL, List.cons_append, List.nil_append, List.mem_cons] at h
    rcases h with h | h | h | h | h
    · exact ⟨0, by omega, Or.inl (by rw [h]; simp)⟩
    · exact ⟨0, by omega, Or.inr (Or.inl (by rw [h]; simp))⟩
    · exact ⟨0, by omega, Or.inr (Or.inr (Or.inl (by rw [h]; simp)))⟩
    · exact ⟨0, by omega, Or.inr (Or.inr (Or.inr (by rw [h]; simp)))⟩
    · obtain ⟨j, hj, hx⟩ := mem_band i (n + 1) x h
      refine ⟨j + 1, by omega, ?_⟩
      rcases hx with h | h | h | h
      · exact Or.inl (h.trans (EOn_eq rfl (by push_cast; ring)))
      · exact Or.inr (Or.inl (h.trans (EIn_eq rfl (by push_cast; ring))))
      · exact Or.inr (Or.inr (Or.inl (h.trans (EIn_eq rfl (by push_cast; ring)))))
      · exact Or.inr (Or.inr (Or.inr (h.trans (EOn_eq rfl (by push_cast; ring)))))

section Distinct
variable {p : ℕ} {e : ℤ} (hm : (m : ℤ) = 2 * p) (he : 1 + k = 2 * e) (hcop : IsCoprime e (p : ℤ))
include hm he hcop

omit [NeZero m] in
lemma band_nodup : ∀ (i : ℕ) (n : ℤ), i ≤ p → (bandL m k i n).Nodup
  | 0, n, _ => by simp [bandL]
  | i + 1, n, hi => by
    have hm' : (m : ℤ) = ((2 : ℕ) : ℤ) * p := by rw [hm]; norm_num
    have he' : 1 + k = ((2 : ℕ) : ℤ) * e := by rw [he]; norm_num
    have h2 : 0 < 2 := by norm_num
    have ih := band_nodup i (n + 1) (by omega)
    simp only [bandL, List.cons_append, List.nil_append, List.nodup_cons, List.mem_cons, not_or]
    refine ⟨⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ih⟩⟩
    all_goals first
      | (intro h; first
          | exact EOn_ne_EIn _ _ _ _ h
          | exact EOn_ne_EIn _ _ _ _ h.symm
          | exact neO' hm' he' hcop h2 0 (by omega) h
          | exact neI' hm' he' hcop h2 0 (by omega) h)
      | (intro hx
         obtain ⟨j, hj, hx⟩ := mem_band i (n + 1) _ hx
         rcases hx with h | h | h | h <;> first
          | exact EOn_ne_EIn _ _ _ _ h
          | exact EOn_ne_EIn _ _ _ _ h.symm
          | exact neO' hm' he' hcop h2 (-((j : ℤ) + 1)) (by omega) h
          | exact neI' hm' he' hcop h2 (-((j : ℤ) + 1)) (by omega) h)

end Distinct

omit [NeZero m] in
lemma band_length : ∀ (i : ℕ) (n : ℤ), (bandL m k i n).length = 4 * i
  | 0, _ => rfl
  | i + 1, n => by simp only [bandL, List.length_append, band_length i (n + 1)]; simp; ring

omit [NeZero m] in
lemma oL_length : ∀ (n : ℕ) (x : ℤ), (oL m n x).length = n
  | 0, _ => rfl
  | n + 1, x => by simp [oL, oL_length n (x + 1)]

omit [NeZero m] in
lemma iL_length : ∀ (n : ℕ) (x : ℤ), (iL m k n x).length = n
  | 0, _ => rfl
  | n + 1, x => by simp [iL, iL_length n (x + k)]

omit [NeZero m] in
lemma mem_oL : ∀ (n : ℕ) (x : ℤ) (v : ZMod m × Bool), v ∈ oL m n x →
    ∃ i : ℕ, i < n ∧ v = (((x + i : ℤ) : ZMod m), false)
  | 0, _, _, h => by simp [oL] at h
  | n + 1, x, v, h => by
    simp only [oL, List.mem_cons] at h
    rcases h with h | h
    · exact ⟨0, by omega, by rw [h]; simp⟩
    · obtain ⟨i, hi, hv⟩ := mem_oL n (x + 1) v h
      exact ⟨i + 1, by omega, by rw [hv]; push_cast; ring_nf⟩

omit [NeZero m] in
lemma mem_iL : ∀ (n : ℕ) (x : ℤ) (v : ZMod m × Bool), v ∈ iL m k n x →
    ∃ i : ℕ, i < n ∧ v = (((x + i * k : ℤ) : ZMod m), true)
  | 0, _, _, h => by simp [iL] at h
  | n + 1, x, v, h => by
    simp only [iL, List.mem_cons] at h
    rcases h with h | h
    · exact ⟨0, by omega, by rw [h]; simp⟩
    · obtain ⟨i, hi, hv⟩ := mem_iL n (x + k) v h
      exact ⟨i + 1, by omega, by rw [hv]; push_cast; ring_nf⟩

omit [NeZero m] in
lemma ne_of_lt_m {a : ℕ} (ha0 : 0 < a) (ham : a < m) : ((a : ℤ) : ZMod m) ≠ 0 := by
  intro h
  have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ m).1 h
  have h2 := Int.le_of_dvd (by omega) this
  omega

omit [NeZero m] in
lemma oL_nodup : ∀ (n : ℕ) (x : ℤ), n ≤ m → (oL m n x).Nodup
  | 0, _, _ => by simp [oL]
  | n + 1, x, hn => by
    simp only [oL, List.nodup_cons]
    refine ⟨fun h => ?_, oL_nodup n (x + 1) (by omega)⟩
    obtain ⟨i, hi, hv⟩ := mem_oL n (x + 1) _ h
    have := congrArg Prod.fst hv
    exact ne_of_lt_m (m := m) (a := i + 1) (by omega) (by omega) (by push_cast at this ⊢; linear_combination -this)

lemma iL_nodup (hkk : (k : ZMod m) * k = -1) : ∀ (n : ℕ) (x : ℤ), n ≤ m → (iL m k n x).Nodup
  | 0, _, _ => by simp [iL]
  | n + 1, x, hn => by
    simp only [iL, List.nodup_cons]
    refine ⟨fun h => ?_, iL_nodup hkk n (x + k) (by omega)⟩
    obtain ⟨i, hi, hv⟩ := mem_iL n (x + k) _ h
    have := congrArg Prod.fst hv
    refine ne_of_lt_m (m := m) (a := i + 1) (by omega) (by omega) ?_
    push_cast at this ⊢
    have h1 : ((i : ZMod m) + 1) * k = 0 := by linear_combination -this
    have h2 : ((i : ZMod m) + 1) * k * k = 0 := by rw [h1, zero_mul]
    rw [mul_assoc, hkk] at h2
    linear_combination -h2

open Classical in
omit [NeZero m] in
lemma spk_OO (a b : ZMod m) : ¬ spk m k s((a, false), (b, false)) := by
  rintro ⟨x, hx⟩; simp [E, Sym2.eq_iff] at hx

open Classical in
omit [NeZero m] in
lemma spk_II (a b : ZMod m) : ¬ spk m k s((a, true), (b, true)) := by
  rintro ⟨x, hx⟩; simp [E, Sym2.eq_iff] at hx

omit [NeZero m] in
lemma spk_OI (a : ZMod m) : spk m k s((a, false), (a, true)) := ⟨a, rfl⟩

omit [NeZero m] in
lemma spk_IO (a : ZMod m) : spk m k s((a, true), (a, false)) := ⟨a, Sym2.eq_swap⟩

open Classical in
omit [NeZero m] in
lemma band_counts : ∀ (i : ℕ) (n : ℤ),
    (eds (bandL m k (i + 1) n)).countP (fun f => decide (spk m k f)) = 2 * (i + 1) ∧
    (eds (bandL m k (i + 1) n)).countP (fun f => decide (¬ spk m k f)) = 2 * i + 1
  | 0, n => by
    simp only [bandL, List.cons_append, List.nil_append, List.append_nil, eds, EOn, EIn]
    simp [List.countP_cons, spk_OI, spk_IO, spk_II]
  | i + 1, n => by
    obtain ⟨h1, h2⟩ := band_counts i (n + 1)
    simp only [bandL, List.cons_append, List.nil_append] at h1 h2 ⊢
    simp only [eds] at h1 h2 ⊢
    simp only [EOn, EIn] at h1 h2 ⊢
    simp only [List.countP_cons, spk_OI, spk_IO, spk_II, spk_OO, decide_true, decide_false,
      not_true_eq_false, not_false_eq_true, if_true, if_false, Bool.false_eq_true] at h1 h2 ⊢
    omega

open Classical in
omit [NeZero m] in
lemma iL_counts : ∀ (n : ℕ) (x : ℤ),
    (eds (iL m k (n + 1) x)).countP (fun f => decide (spk m k f)) = 0 ∧
    (eds (iL m k (n + 1) x)).countP (fun f => decide (¬ spk m k f)) = n
  | 0, x => by simp [iL, eds]
  | n + 1, x => by
    obtain ⟨h1, h2⟩ := iL_counts n (x + k)
    simp only [iL] at h1 h2 ⊢
    simp only [eds] at h1 h2 ⊢
    simp only [List.countP_cons, spk_II, decide_false, not_false_eq_true, decide_true, if_true, if_false,
      Bool.false_eq_true] at h1 h2 ⊢
    omega

open Classical in
omit [NeZero m] in
lemma oL_counts : ∀ (n : ℕ) (x : ℤ) (t : List (ZMod m × Bool)),
    (eds (oL m (n + 1) x ++ t)).countP (fun f => decide (spk m k f)) =
      (eds ((((x + n : ℤ) : ZMod m), false) :: t)).countP (fun f => decide (spk m k f)) ∧
    (eds (oL m (n + 1) x ++ t)).countP (fun f => decide (¬ spk m k f)) =
      n + (eds ((((x + n : ℤ) : ZMod m), false) :: t)).countP (fun f => decide (¬ spk m k f))
  | 0, x, t => by simp [oL]
  | n + 1, x, t => by
    obtain ⟨h1, h2⟩ := oL_counts n (x + 1) t
    have e1 : x + 1 + (n : ℤ) = x + ((n + 1 : ℕ) : ℤ) := by push_cast; ring
    rw [e1] at h1 h2
    simp only [oL, List.cons_append] at h1 h2 ⊢
    simp only [eds] at h1 h2 ⊢
    simp only [List.countP_cons, spk_OO, decide_false, not_false_eq_true, decide_true, if_true, if_false,
      Bool.false_eq_true] at h1 h2 ⊢
    omega

end Count

/-! ### the theorem -/

open Classical in
/-- **Theorem 9, case k² ≡ −1 (mod m), m even.** -/
theorem ft_gp_neg_even (m : ℕ) [NeZero m] (k : ℤ) (hm : 3 ≤ m) (hev : Even m) (hk : (m : ℤ) ∣ k * k + 1) :
    ∃ (r k' : ℕ), 0 < r ∧ 0 < k' ∧
      ∃ (a b : Fin r → ZMod m × Bool) (P : ∀ i, (gp m k).Walk (a i) (b i)),
        (∀ i, (P i).IsHamiltonian) ∧
        ∀ e ∈ (gp m k).edgeSet, (Finset.univ.filter fun i => e ∈ (P i).edges).card = k' := by
  have hkk : (k : ZMod m) * k = -1 := by
    have h := (ZMod.intCast_zmod_eq_zero_iff_dvd (k * k + 1) m).2 hk
    push_cast at h; linear_combination h
  have hk0 := k_ne hkk hm
  -- m = 2p, 1 + k = 2e, gcd(e, p) = 1
  obtain ⟨p, hp⟩ := hev
  have hmp : (m : ℤ) = 2 * p := by rw [hp]; push_cast; ring
  have hkodd : (2 : ℤ) ∣ 1 + k := by
    have h2 : (2 : ℤ) ∣ k * k + 1 := dvd_trans ⟨p, by rw [hmp]⟩ hk
    rcases Int.emod_two_eq_zero_or_one k with h0 | h1
    · exfalso
      have := Int.emod_eq_zero_of_dvd h2
      rw [Int.add_emod, Int.mul_emod, h0] at this; norm_num at this
    · omega
  obtain ⟨e, he⟩ := hkodd
  have hcop : IsCoprime e (p : ℤ) := by
    rw [Int.isCoprime_iff_gcd_eq_one]
    set g := Int.gcd e p with hg
    have hge : (g : ℤ) ∣ e := Int.gcd_dvd_left _ _
    have hgp : (g : ℤ) ∣ (p : ℤ) := Int.gcd_dvd_right _ _
    have h1 : (2 * g : ℤ) ∣ k * k + 1 := dvd_trans (by rw [hmp]; exact mul_dvd_mul_left 2 hgp) hk
    have h2 : (2 * g : ℤ) ∣ k * k - 1 := by
      have : k * k - 1 = (1 + k) * (k - 1) := by ring
      rw [this, he]; exact dvd_mul_of_dvd_left (mul_dvd_mul_left 2 hge) _
    have h3 : (2 * g : ℤ) ∣ 2 := by
      have := dvd_sub h1 h2
      rwa [show k * k + 1 - (k * k - 1) = (2 : ℤ) by ring] at this
    have hp0 : 0 < p := by omega
    have hg0 : 0 < g := Int.gcd_pos_of_ne_zero_right _ (by exact_mod_cast hp0.ne')
    have := Int.le_of_dvd (by norm_num) h3
    omega
  -- the band path (m spokes)
  obtain ⟨p', rfl⟩ : ∃ p', p = p' + 1 := ⟨p - 1, by omega⟩
  have hb := band_chain hm hk0 p' 0
  have hbnd := band_nodup (k := k) hmp he hcop (p' + 1) 0 le_rfl
  have hbL : bandL m k (p' + 1) 0 = EOn m k 0 0 :: ([EIn m k 0 0, EIn m k 1 (0 + 1), EOn m k 1 (0 + 1)] ++
      bandL m k p' (0 + 1)) := rfl
  rw [hbL] at hb hbnd
  have hbc := band_counts (m := m) (k := k) p' 0
  rw [hbL] at hbc
  let P1 := wk (gp m k) _ _ hb
  have hP1 : P1.2.IsHamiltonian := by
    refine wk_ham _ _ _ hb hbnd (FTGP.all_of_nodup _ hbnd ?_)
    have := band_length (m := m) (k := k) (p' + 1) 0
    rw [hbL] at this
    rw [this]; simp [ZMod.card]; omega
  -- the low path (1 spoke)
  obtain ⟨m', hm'⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  have hcnt : ∀ x : ℤ, iL m k m x = iL m k (m' + 1) x := fun x => by rw [← hm']
  have hiL : iL m k m ((m : ℤ) - 1) = (((m - 1 : ℤ) : ZMod m), true) :: iL m k m' ((m : ℤ) - 1 + k) := by
    rw [hcnt]; rfl
  have hco : ((((0 : ℤ) + (m' : ℕ) : ℤ)) : ZMod m) = (((m : ℤ) - 1 : ℤ) : ZMod m) := by
    congr 1; rw [hm']; push_cast; ring
  have hlow : List.IsChain (gp m k).Adj (oL m (m' + 1) 0 ++ iL m k m ((m : ℤ) - 1)) := by
    apply oL_chain hm hk0 m' 0
    rw [hiL, List.isChain_cons_cons]
    refine ⟨?_, ?_⟩
    · rw [hco]; exact adjOI _
    · rw [← hiL]; exact iL_chain hm hk0 m _
  have hlowL : oL m (m' + 1) 0 ++ iL m k m ((m : ℤ) - 1) =
      (((0 : ℤ) : ZMod m), false) :: (oL m m' (0 + 1) ++ iL m k m ((m : ℤ) - 1)) := rfl
  have hlnd : (oL m (m' + 1) 0 ++ iL m k m ((m : ℤ) - 1)).Nodup := by
    rw [List.nodup_append]
    refine ⟨oL_nodup (m' + 1) 0 (by omega), iL_nodup hkk m _ le_rfl, ?_⟩
    intro x hx y hy hxy
    obtain ⟨i, -, hi⟩ := mem_oL (m := m) _ _ _ hx
    obtain ⟨j, -, hj⟩ := mem_iL _ _ _ hy
    rw [← hxy, hi] at hj
    have := congrArg Prod.snd hj; simp at this
  have hllen : (oL m (m' + 1) 0 ++ iL m k m ((m : ℤ) - 1)).length = Fintype.card (ZMod m × Bool) := by
    rw [List.length_append, oL_length, iL_length]; simp [ZMod.card]; omega
  rw [hlowL] at hlow hlnd hllen
  let P2 := wk (gp m k) _ _ hlow
  have hP2 : P2.2.IsHamiltonian := wk_ham _ _ _ hlow hlnd (FTGP.all_of_nodup _ hlnd hllen)
  -- counts
  obtain ⟨hs2, hr2⟩ := oL_counts (m := m) (k := k) m' 0 (iL m k m ((m : ℤ) - 1))
  rw [hlowL] at hs2 hr2
  rw [hiL] at hs2 hr2
  obtain ⟨hs3, hr3⟩ := iL_counts (m := m) (k := k) m' ((m : ℤ) - 1)
  rw [← hcnt, hiL] at hs3 hr3
  rw [hco] at hs2 hr2
  simp only [eds] at hs2 hr2
  simp only [List.countP_cons, spk_OI, decide_true, not_true_eq_false, decide_false, if_true, if_false,
    Bool.false_eq_true] at hs2 hr2
  rw [hs3] at hs2
  rw [hr3] at hr2
  obtain ⟨hs1, hr1⟩ := hbc
  have hE1 : P1.2.edges = eds (EOn m k 0 0 :: ([EIn m k 0 0, EIn m k 1 (0 + 1), EOn m k 1 (0 + 1)] ++
      bandL m k p' (0 + 1))) := wk_edges _ _ _ hb
  have hE2 : P2.2.edges = eds ((((0 : ℤ) : ZMod m), false) :: (oL m m' (0 + 1) ++ iL m k m ((m : ℤ) - 1))) :=
    wk_edges _ _ _ hlow
  refine assemble2 hkk hm P1.2 P2.2 hP1 hP2 (4 * p') (2 * p' + 3) ?_ ?_
  · rw [hE1, hE2, hiL, hs1, hr1, hs2, hr2]
    have : m' = 2 * p' + 1 := by omega
    subst this; ring
  · rw [hE1, hE2, hiL, hs1, hs2]; positivity

end FTGPN

#print axioms FTGPN.ft_gp_neg_even
