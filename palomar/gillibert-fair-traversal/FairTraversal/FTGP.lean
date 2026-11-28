/-
Copyright 2026 Ming-Chih Kao. Licensed under the Apache License, Version 2.0;
see the LICENSE file at the root of this repository.
Ported from github.com/koolkao/gillibert-fair-traversal-abelian (v1.7.0, commit
06c3a8732759afca38331762b76113135e475ac6) to Lean v4.36.0 and the module system.
-/
module

public import FairTraversal.FTPower

/-!
# Theorem 9 in Lean: generalized Petersen graphs GP(m, k) with k² ≡ 1 (mod m) (new in v1.4.0; all m in v1.5.0)

`gp m k` is GP(m, k) on `ZMod m × Bool` (`false`: outer O_x, `true`: inner I_x): rims O_x O_{x+1},
I_x I_{x+k}, spokes O_x I_x. For k² ≡ 1 it is the Cayley graph of `Γ(ℤ_m, k, 0) = FTDih.Pw (ZMod m) k 0`
with `S = {ρ, ρ⁻¹, τ}` (ρ = ⟨1, 0⟩, τ = ⟨0, 1⟩), under the identity labelling (`adj_iff`).

* The reduction of NOTE.md §9.1 (`ft_gp_of_word`): if some Hamiltonian word (a Hamiltonian path from 1
  given by its steps in S) has `3 · #τ ≥ 2m − 1` spokes, then GP(m, k) satisfies the #339 conclusion. The
  low path O_0 … O_{m−1} I_{m−1} … (one spoke) is `lowWord`; the two are mixed with `FTDih.assemble`.
* m even (v1.4.0): the all-spoke Hamiltonian word comes from the alternating sequence of `FTDih.lemmaA`
  (FTPower.lean, Lemma 8.A); `ft_gp_even`.
* m odd (v1.5.0): if k ≡ 1 (mod m), Lemma 8.A (a) again (`ft_gp_of_alt`); otherwise d = gcd(1 + k, m) is odd
  and ≥ 3, and the band word of NOTE.md §9.2 (B = (d − 3)/2 square bands and one hexagon band) has
  (d − 1)m/d spokes (`ft_gp_band`); `ft_gp_odd`.
* `ft_gp_cayley`: m ≥ 3 and m ∣ k² − 1 ⇒ GP(m, k) satisfies the #339 conclusion.

Not covered here: k² ≡ −1 with m even (`FTGPNeg.lean`, v1.6.0) and GP(10, 2) (`FTGP102.lean`, v1.7.0).
-/

@[expose] public section


open Finset

namespace FTGP
open FTDih

instance fact_kz (m : ℕ) (k : ℤ) : Fact (k • (0 : ZMod m) = 0) := ⟨smul_zero _⟩

/-- the relation generating GP(m, k): O_x → O_{x+1}, I_x → I_{x+k}, O_x → I_x -/
def gpRel (m : ℕ) (k : ℤ) (u v : ZMod m × Bool) : Prop :=
  (u.2 = false ∧ v.2 = false ∧ v.1 = u.1 + 1) ∨ (u.2 = true ∧ v.2 = true ∧ v.1 = u.1 + k) ∨
    (u.2 = false ∧ v.2 = true ∧ v.1 = u.1)

/-- GP(m, k) on `ZMod m × Bool` (`false`: outer, `true`: inner). -/
def gp (m : ℕ) (k : ℤ) : SimpleGraph (ZMod m × Bool) := SimpleGraph.fromRel (gpRel m k)

lemma gpRel_ff (m : ℕ) (k : ℤ) (x y : ZMod m) : gpRel m k (x, false) (y, false) ↔ y = x + 1 := by
  simp [gpRel]
lemma gpRel_tt (m : ℕ) (k : ℤ) (x y : ZMod m) : gpRel m k (x, true) (y, true) ↔ y = x + k := by
  simp [gpRel]
lemma gpRel_ft (m : ℕ) (k : ℤ) (x y : ZMod m) : gpRel m k (x, false) (y, true) ↔ y = x := by
  simp [gpRel]
lemma gpRel_tf (m : ℕ) (k : ℤ) (x y : ZMod m) : gpRel m k (x, true) (y, false) ↔ False := by
  simp [gpRel]

section Cayley
variable (m : ℕ) [NeZero m] (k : ℤ) [Fact (∀ a : ZMod m, k • k • a = a)]

/-- the group Γ(ℤ_m, k, 0) -/
abbrev Γ := Pw (ZMod m) k 0

/-- ρ = ⟨1, 0⟩ -/
def ρ : Γ m k := prot 1
/-- τ = ⟨0, 1⟩ -/
def τ : Γ m k := pref 0

/-- the generating set {ρ, ρ⁻¹, τ} -/
def Sg : Finset (Γ m k) := {ρ m k, (ρ m k)⁻¹, τ m k}

/-- the identity labelling -/
def lab : ZMod m × Bool ≃ Γ m k where
  toFun p := ⟨p.1, p.2⟩
  invFun g := (g.r, g.s)
  left_inv _ := rfl
  right_inv _ := rfl

lemma ksmul (a : ZMod m) : k • a = (k : ZMod m) * a := zsmul_eq_mul a k

lemma kk' : (k : ZMod m) * k = 1 := by
  have h := (Fact.out : ∀ a : ZMod m, k • k • a = a) 1
  rwa [ksmul, ksmul, mul_one] at h

lemma τ_inv : (τ m k)⁻¹ = τ m k := by
  rw [τ, pref_inv]; simp

lemma ρ_inv : (ρ m k)⁻¹ = prot (-1) := by rw [ρ, prot_inv]

variable {m} in
lemma one_ne_neg_one (hm : 3 ≤ m) : (1 : ZMod m) ≠ -1 := by
  intro h
  have h1 : (1 : ZMod m) + 1 = 0 :=
    calc (1 : ZMod m) + 1 = 1 + -1 := by rw [← h]
      _ = 0 := add_neg_cancel 1
  have h2 : ((2 : ℕ) : ZMod m) = 0 := by rw [Nat.cast_ofNat, ← one_add_one_eq_two]; exact h1
  have := Nat.le_of_dvd (by norm_num) ((ZMod.natCast_eq_zero_iff 2 m).1 h2)
  omega

variable {m} in
lemma one_ne_zero' (hm : 3 ≤ m) : (1 : ZMod m) ≠ 0 := by
  have : Fact (1 < m) := ⟨by omega⟩
  exact one_ne_zero

lemma ρ_ne_τ : ρ m k ≠ τ m k := by
  intro h; have := congrArg Pw.s h; simp [ρ, τ, prot, pref] at this

lemma ρinv_ne_τ : (ρ m k)⁻¹ ≠ τ m k := by
  rw [ρ_inv]; intro h; have := congrArg Pw.s h; simp [τ, prot, pref] at this

variable {m} in
lemma ρ_ne_ρinv (hm : 3 ≤ m) : ρ m k ≠ (ρ m k)⁻¹ := by
  rw [ρ_inv]; intro h; have := congrArg Pw.r h
  exact one_ne_neg_one hm (by simpa [ρ, prot] using this)

lemma mem_Sg (g : Γ m k) : g ∈ Sg m k ↔ g = prot 1 ∨ g = prot (-1) ∨ g = pref 0 := by
  simp [Sg, ρ, τ, prot_inv]

lemma pw_ext_iff (g h : Γ m k) : g = h ↔ g.r = h.r ∧ g.s = h.s := by
  constructor
  · rintro rfl; exact ⟨rfl, rfl⟩
  · rintro ⟨h1, h2⟩; cases g; cases h; simp_all

lemma prot_mem (a : ZMod m) : (prot a : Γ m k) ∈ Sg m k ↔ a = 1 ∨ a = -1 := by
  simp [mem_Sg, pw_ext_iff, prot, pref]

lemma pref_mem (a : ZMod m) : (pref a : Γ m k) ∈ Sg m k ↔ a = 0 := by
  simp [mem_Sg, pw_ext_iff, prot, pref]

lemma lab_oo (x y : ZMod m) : (lab m k (x, false))⁻¹ * lab m k (y, false) = prot (y - x) := by
  show (prot x : Γ m k)⁻¹ * prot y = prot (y - x)
  rw [prot_inv, prot_mul_prot, neg_add_eq_sub]

lemma lab_ft (x y : ZMod m) : (lab m k (x, false))⁻¹ * lab m k (y, true) = pref (y - x) := by
  show (prot x : Γ m k)⁻¹ * pref y = pref (y - x)
  rw [prot_inv, prot_mul_pref, neg_add_eq_sub]

lemma lab_tf (x y : ZMod m) : (lab m k (x, true))⁻¹ * lab m k (y, false) = pref (k • (y - x)) := by
  show (pref x : Γ m k)⁻¹ * prot y = pref (k • (y - x))
  rw [pref_inv, pref_mul_prot]
  congr 1
  rw [smul_sub, sub_zero]; abel

lemma lab_tt (x y : ZMod m) : (lab m k (x, true))⁻¹ * lab m k (y, true) = prot (k • (y - x)) := by
  show (pref x : Γ m k)⁻¹ * pref y = prot (k • (y - x))
  rw [pref_inv, pref_mul_pref]
  congr 1
  rw [smul_sub, sub_zero, add_zero]; abel

/-- GP(m, k) is the Cayley graph of Γ(ℤ_m, k, 0) with respect to {ρ, ρ⁻¹, τ}. -/
lemma adj_iff (hm : 3 ≤ m) (u v : ZMod m × Bool) :
    (gp m k).Adj u v ↔ (lab m k u)⁻¹ * lab m k v ∈ Sg m k := by
  obtain ⟨x, i⟩ := u
  obtain ⟨y, j⟩ := v
  have hkk := kk' m k
  have h10 := one_ne_zero' hm
  rw [gp, SimpleGraph.fromRel_adj]
  cases i <;> cases j
  · rw [gpRel_ff, gpRel_ff, lab_oo, prot_mem]
    constructor
    · rintro ⟨-, h | h⟩
      · left; rw [h]; ring
      · right; rw [h]; ring
    · rintro (h | h)
      · refine ⟨fun e => ?_, Or.inl (by linear_combination h)⟩
        have hxy : x = y := congrArg Prod.fst e
        rw [hxy, sub_self] at h; exact h10 h.symm
      · refine ⟨fun e => ?_, Or.inr (by linear_combination -h)⟩
        have hxy : x = y := congrArg Prod.fst e
        rw [hxy, sub_self] at h; exact h10 (neg_eq_zero.1 h.symm)
  · rw [gpRel_ft, gpRel_tf, or_false, lab_ft, pref_mem]
    constructor
    · rintro ⟨-, h⟩; rw [h, sub_self]
    · intro h
      exact ⟨fun e => Bool.false_ne_true (congrArg Prod.snd e), by linear_combination h⟩
  · rw [gpRel_tf, gpRel_ft, false_or, lab_tf, pref_mem]
    constructor
    · rintro ⟨-, h⟩; rw [h, sub_self, smul_zero]
    · intro h
      rw [ksmul] at h
      have h2 : y - x = 0 := by
        have := congrArg ((k : ZMod m) * ·) h
        simpa [← mul_assoc, hkk] using this
      exact ⟨fun e => Bool.false_ne_true (congrArg Prod.snd e).symm, by linear_combination -h2⟩
  · rw [gpRel_tt, gpRel_tt, lab_tt, prot_mem, ksmul]
    constructor
    · rintro ⟨-, h | h⟩
      · left; rw [h]; linear_combination hkk
      · right; rw [h]; linear_combination -hkk
    · rintro (h | h)
      · refine ⟨fun e => ?_, Or.inl (by linear_combination (k : ZMod m) * h - (y - x) * hkk)⟩
        have hxy : x = y := congrArg Prod.fst e
        rw [hxy, sub_self, mul_zero] at h; exact h10 h.symm
      · refine ⟨fun e => ?_, Or.inr (by linear_combination (-(k : ZMod m)) * h + (y - x) * hkk)⟩
        have hxy : x = y := congrArg Prod.fst e
        rw [hxy, sub_self, mul_zero] at h; exact h10 (neg_eq_zero.1 h.symm)

end Cayley

/-! ## Words, their vectors, and the reduction (NOTE.md §9.1) -/

section Reduction
variable (m : ℕ) [NeZero m] (k : ℤ) [Fact (∀ a : ZMod m, k • k • a = a)]

lemma len_split {α : Type} [DecidableEq α] (a b c : α) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ∀ ds : List α, (∀ d ∈ ds, d = a ∨ d = b ∨ d = c) →
      ds.length = ds.count a + ds.count b + ds.count c
  | [], _ => rfl
  | d :: ds, h => by
    have ih := len_split a b c hab hac hbc ds (fun x hx => h x (List.mem_cons_of_mem _ hx))
    rcases h d (by simp) with rfl | rfl | rfl <;>
      simp [List.count_cons, hab, hac, hbc, hab.symm, hac.symm, hbc.symm, ih] <;> omega

lemma all_of_nodup {α : Type} [Fintype α] [DecidableEq α] (l : List α) (h : l.Nodup)
    (hl : l.length = Fintype.card α) : ∀ g, g ∈ l := by
  intro g
  have h1 := List.toFinset_card_of_nodup h
  have h2 : l.toFinset = Finset.univ := Finset.eq_univ_of_card _ (by rw [h1, hl])
  have : g ∈ l.toFinset := by rw [h2]; exact Finset.mem_univ g
  exact List.mem_toFinset.1 this

lemma card_Γ : Fintype.card (Γ m k) = 2 * m := by
  rw [card_pw, card_dih, ZMod.card]

lemma length_of_ham (ds : List (Γ m k)) (hnd : (verts 1 ds).Nodup) (hall : ∀ g, g ∈ verts 1 ds) :
    ds.length + 1 = 2 * m := by
  rw [← length_verts (1 : Γ m k) ds, ← card_Γ m k, ← List.toFinset_card_of_nodup hnd]
  congr 1
  exact Finset.eq_univ_of_forall (fun g => List.mem_toFinset.2 (hall g))

/-- the vector of a word with `s` spokes: `τ ↦ s`, everything else `↦ (2m − 1 − s)/2` -/
def gam (s : ℕ) : Γ m k → ℚ := fun g => if g = τ m k then (s : ℚ) else (2 * (m : ℚ) - 1 - s) / 2

lemma mem_Sg' (d : Γ m k) : d ∈ Sg m k ↔ d = ρ m k ∨ d = (ρ m k)⁻¹ ∨ d = τ m k := by
  simp [Sg]

lemma gam_real (hm : 3 ≤ m) (ds : List (Γ m k)) (hS : ∀ d ∈ ds, d ∈ Sg m k)
    (hnd : (verts 1 ds).Nodup) (hall : ∀ g, g ∈ verts 1 ds) :
    gam m k (ds.count (τ m k)) ∈ Real (Sg m k) := by
  refine ⟨ds, hS, hnd, hall, fun d hd => ?_⟩
  have hlen := length_of_ham m k ds hnd hall
  have hsplit := len_split (ρ m k) (ρ m k)⁻¹ (τ m k) (ρ_ne_ρinv k hm) (ρ_ne_τ m k)
    (ρinv_ne_τ m k) ds (fun d hd => (mem_Sg' m k d).1 (hS d hd))
  have hq : ((ds.count (ρ m k) + ds.count (ρ m k)⁻¹ : ℕ) : ℚ) =
      2 * (m : ℚ) - 1 - (ds.count (τ m k) : ℕ) := by
    have : ds.count (ρ m k) + ds.count (ρ m k)⁻¹ + ds.count (τ m k) + 1 = 2 * m := by omega
    have : ((ds.count (ρ m k) + ds.count (ρ m k)⁻¹ + ds.count (τ m k) + 1 : ℕ) : ℚ) =
        ((2 * m : ℕ) : ℚ) := by rw [this]
    push_cast at this ⊢; linarith
  rcases (mem_Sg' m k d).1 hd with rfl | rfl | rfl
  · simp only [pc, gam, if_neg (ρ_ne_τ m k), if_neg (ρinv_ne_τ m k)]
    rw [← hq]; push_cast; ring
  · simp only [pc, gam, inv_inv, if_neg (ρ_ne_τ m k), if_neg (ρinv_ne_τ m k)]
    rw [← hq]; push_cast; ring
  · simp only [pc, gam, τ_inv, if_pos rfl]
    push_cast; ring

/-- the low word O_0 … O_{m−1} I_{m−1} I_{m−1+k} … (one spoke) -/
def lowWord : List (Γ m k) :=
  List.replicate (m - 1) (ρ m k) ++ τ m k :: List.replicate (m - 1) (ρ m k)

lemma verts_rep (x : Γ m k) (n : ℕ) :
    verts x (List.replicate n (ρ m k)) = (List.range (n + 1)).map (fun i => x * ρ m k ^ i) := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    rw [List.replicate_succ, verts_cons, ih, List.range_succ_eq_map (n := n + 1), List.map_cons,
      List.map_map, pow_zero, mul_one]
    congr 1
    apply List.map_congr_left
    intro i _
    simp only [Function.comp, pow_succ', mul_assoc]

lemma natCast_inj_lt {i j : ℕ} (hi : i < m) (hj : j < m) (h : (i : ZMod m) = j) : i = j := by
  have := congrArg ZMod.val h
  rwa [ZMod.val_natCast, ZMod.val_natCast, Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] at this

lemma lowWord_ham (hm : 3 ≤ m) :
    (verts 1 (lowWord m k)).Nodup ∧ ∀ g, g ∈ verts 1 (lowWord m k) := by
  have hkk := kk' m k
  have hnd : (verts 1 (lowWord m k)).Nodup := by
    rw [lowWord, verts_append, verts_rep, verts_rep, List.prod_replicate, one_mul]
    have hm1 : m - 1 + 1 = m := by omega
    rw [hm1]
    refine List.Nodup.append ?_ ?_ ?_
    · refine List.Nodup.map_on ?_ List.nodup_range
      intro i hi j hj hij
      rw [List.mem_range] at hi hj
      simp only [one_mul, ρ, prot_pow] at hij
      have := congrArg Pw.r hij
      simp only [prot, nsmul_eq_mul, mul_one] at this
      exact natCast_inj_lt m hi hj this
    · refine List.Nodup.map_on ?_ List.nodup_range
      intro i hi j hj hij
      rw [List.mem_range] at hi hj
      simp only [ρ, τ, prot_pow, prot_mul_pref, pref_mul_prot] at hij
      have := congrArg Pw.r hij
      simp only [pref, nsmul_eq_mul, mul_one, add_zero, ksmul, add_right_inj] at this
      have h2 := congrArg ((k : ZMod m) * ·) this
      simp only [← mul_assoc, hkk, one_mul] at h2
      exact natCast_inj_lt m hi hj h2
    · intro g h1 h2
      simp only [List.mem_map, List.mem_range] at h1 h2
      obtain ⟨i, -, rfl⟩ := h1
      obtain ⟨j, -, hj⟩ := h2
      simp only [ρ, τ, prot_pow, prot_mul_pref, pref_mul_prot, one_mul] at hj
      have := congrArg Pw.s hj
      simp [prot, pref] at this
  refine ⟨hnd, all_of_nodup _ hnd ?_⟩
  rw [length_verts, card_Γ, lowWord, List.length_append, List.length_cons, List.length_replicate]
  omega

lemma lowWord_S : ∀ d ∈ lowWord m k, d ∈ Sg m k := by
  intro d hd
  simp only [lowWord, List.mem_append, List.mem_cons, List.mem_replicate] at hd
  rw [mem_Sg']
  rcases hd with ⟨-, rfl⟩ | rfl | ⟨-, rfl⟩ <;> simp

lemma lowWord_count : (lowWord m k).count (τ m k) = 1 := by
  simp [lowWord, List.count_replicate, ρ_ne_τ m k]

/-- **Reduction (NOTE.md §9.1).** A Hamiltonian word with `3 · #τ ≥ 2m − 1` gives the #339 conclusion for
every Cayley graph of Γ(ℤ_m, k, 0) with respect to {ρ, ρ⁻¹, τ}. -/
theorem ft_cay_of_word (hm : 3 ≤ m) (ds : List (Γ m k)) (hS : ∀ d ∈ ds, d ∈ Sg m k)
    (hnd : (verts 1 ds).Nodup) (hall : ∀ g, g ∈ verts 1 ds) (hs : 2 * m - 1 ≤ 3 * ds.count (τ m k))
    (G : SimpleGraph (Γ m k)) (hG : ∀ x y, G.Adj x y ↔ x⁻¹ * y ∈ Sg m k) :
    ∃ (r k' : ℕ), 0 < r ∧ 0 < k' ∧
      ∃ (a b : Fin r → Γ m k) (P : ∀ i, G.Walk (a i) (b i)),
        (∀ i, (P i).IsHamiltonian) ∧
        ∀ e ∈ G.edgeSet, (Finset.univ.filter fun i => e ∈ (P i).edges).card = k' := by
  classical
  set s := ds.count (τ m k) with hsdef
  have hm' : (3 : ℚ) ≤ m := by exact_mod_cast hm
  have hsq : (2 * (m : ℚ) - 1) ≤ 3 * s := by
    have : ((2 * m - 1 : ℕ) : ℚ) ≤ ((3 * s : ℕ) : ℚ) := by exact_mod_cast hs
    push_cast [Nat.cast_sub (by omega : 1 ≤ 2 * m)] at this; linarith
  set T : ℚ := (2 * (m : ℚ) - 1) / 3 with hT
  have hs1 : (1 : ℚ) < s := by linarith
  set lam : ℚ := (T - 1) / (s - 1) with hlamdef
  have hlam : lam * (s - 1) = T - 1 := by
    rw [hlamdef]; exact div_mul_cancel₀ _ (sub_pos.2 hs1).ne'
  have hlam0 : 0 ≤ lam := by rw [hlamdef]; apply div_nonneg <;> linarith
  have hlam1 : lam ≤ 1 := by rw [hlamdef, div_le_one (by linarith)]; linarith
  have hlow := lowWord_ham m k hm
  have h1 := gam_real m k hm ds hS hnd hall
  have h2 := gam_real m k hm (lowWord m k) (lowWord_S m k) hlow.1 hlow.2
  rw [lowWord_count] at h2
  set x : Γ m k → ℚ := lam • gam m k s + (1 - lam) • gam m k 1 with hx
  have hxc : x ∈ convexHull ℚ (Real (Sg m k)) :=
    convex_convexHull ℚ _ (subset_convexHull ℚ _ h1) (subset_convexHull ℚ _ h2) hlam0
      (by linarith) (by ring)
  refine assemble (Sg m k) G hG x hxc (2 * T) (by rw [hT]; linarith) (fun d hd => ?_) (τ m k)
    (by rw [mem_Sg']; right; right; rfl)
  simp only [hx, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rcases (mem_Sg' m k d).1 hd with rfl | rfl | rfl
  · simp only [gam, inv_inv, if_neg (ρ_ne_τ m k), if_neg (ρinv_ne_τ m k)]
    push_cast
    linear_combination -hlam
  · simp only [gam, inv_inv, if_neg (ρ_ne_τ m k), if_neg (ρinv_ne_τ m k)]
    push_cast
    linear_combination -hlam
  · simp only [gam, τ_inv, if_pos rfl]
    push_cast
    linear_combination 2 * hlam

/-- **Reduction, GP form.** If Γ(ℤ_m, k, 0) has a Hamiltonian word with `3 · #τ ≥ 2m − 1`, then GP(m, k)
satisfies the conclusion of #339. -/
theorem ft_gp_of_word (hm : 3 ≤ m) (ds : List (Γ m k)) (hS : ∀ d ∈ ds, d ∈ Sg m k)
    (hnd : (verts 1 ds).Nodup) (hall : ∀ g, g ∈ verts 1 ds) (hs : 2 * m - 1 ≤ 3 * ds.count (τ m k)) :
    ∃ (r k' : ℕ), 0 < r ∧ 0 < k' ∧
      ∃ (a b : Fin r → ZMod m × Bool) (P : ∀ i, (gp m k).Walk (a i) (b i)),
        (∀ i, (P i).IsHamiltonian) ∧
        ∀ e ∈ (gp m k).edgeSet, (Finset.univ.filter fun i => e ∈ (P i).edges).card = k' := by
  classical
  have hadj := adj_iff m k hm
  -- connectivity of gp, from the Cayley side
  let G'' : SimpleGraph (Γ m k) := (gp m k).comap (lab m k).symm
  have hG'' : ∀ x y, G''.Adj x y ↔ x⁻¹ * y ∈ Sg m k := by
    intro x y
    show (gp m k).Adj ((lab m k).symm x) ((lab m k).symm y) ↔ _
    rw [hadj]; simp
  obtain ⟨r, -, hr, -, a, b, P, hP, -⟩ := ft_cay_of_word m k hm ds hS hnd hall hs G'' hG''
  have hc'' : G''.Connected := by
    rw [SimpleGraph.connected_iff]
    refine ⟨fun u v => ?_, ⟨1⟩⟩
    have hu := ((P ⟨0, hr⟩).takeUntil u ((hP ⟨0, hr⟩).mem_support u)).reachable
    have hv := ((P ⟨0, hr⟩).takeUntil v ((hP ⟨0, hr⟩).mem_support v)).reachable
    exact hu.symm.trans hv
  have hc : (gp m k).Connected := by
    let f : G'' →g gp m k := ⟨(lab m k).symm, fun h => h⟩
    rw [SimpleGraph.connected_iff]
    refine ⟨fun u v => ?_, ⟨(0, false)⟩⟩
    obtain ⟨w⟩ := hc''.preconnected (lab m k u) (lab m k v)
    convert (w.map f).reachable <;> exact ((lab m k).symm_apply_apply _).symm
  exact transfer (gp m k) (lab m k) (Sg m k) hadj
    (fun G' hG' _ => ft_cay_of_word m k hm ds hS hnd hall hs G' hG') hc

end Reduction


/-! ## m even: the all-spoke path from an alternating sequence (FTPower's Lemma A) -/

section AltWord
variable (m : ℕ) [NeZero m] (k : ℤ) [Fact (∀ a : ZMod m, k • k • a = a)] (c : ℕ → ℤ)

/-- first vertex of block `t`: O_{c t} for even `t`, I_{c t} for odd `t` -/
def gv (t : ℕ) : Γ m k := if Even t then prot (c t : ZMod m) else pref (c t : ZMod m)
/-- second vertex of block `t` (across the spoke) -/
def hv (t : ℕ) : Γ m k := if Even t then pref (c t : ZMod m) else prot (c t : ZMod m)

/-- the rim letter after block `t` -/
def eL (t : ℕ) : Γ m k := if c (t + 1) - c t = (if Even t then k else 1) then ρ m k else (ρ m k)⁻¹

/-- the word τ e₀ τ e₁ … τ, starting at block `t`, with `r` rim letters -/
def aw : ℕ → ℕ → List (Γ m k)
  | _, 0 => [τ m k]
  | t, r + 1 => τ m k :: eL m k c t :: aw (t + 1) r

/-- the vertex list of blocks `t, …, t + r` -/
def bl : ℕ → ℕ → List (Γ m k)
  | t, 0 => [gv m k c t, hv m k c t]
  | t, r + 1 => gv m k c t :: hv m k c t :: bl (t + 1) r

lemma gv_mul_τ (t : ℕ) : gv m k c t * τ m k = hv m k c t := by
  unfold gv hv τ
  split_ifs
  · rw [prot_mul_pref, add_zero]
  · rw [pref_mul_pref]; simp [ksmul]

variable {m k c} in
lemma hv_mul_e (hc : IsAlt k m c) (t : ℕ) : hv m k c t * eL m k c t = gv m k c (t + 1) := by
  obtain ⟨-, hev, hodd, -⟩ := hc
  unfold hv gv eL ρ
  by_cases ht : Even t
  · have ht1 : ¬ Even (t + 1) := by rw [Nat.even_add_one]; exact not_not.2 ht
    simp only [if_pos ht, if_neg ht1]
    rcases hev t ht with h | h
    · rw [if_pos h, pref_mul_prot]
      congr 1
      rw [ksmul, mul_one, show c (t + 1) = c t + k by linarith]; push_cast; ring
    · split_ifs with h'
      · rw [pref_mul_prot]; congr 1
        rw [ksmul, mul_one, show c (t + 1) = c t + k by linarith]; push_cast; ring
      · rw [prot_inv, pref_mul_prot]; congr 1
        rw [ksmul, show c (t + 1) = c t - k by linarith]; push_cast; ring
  · have ht1 : Even (t + 1) := by rw [Nat.even_add_one]; exact ht
    simp only [if_neg ht, if_pos ht1]
    rcases hodd t ht with h | h
    · rw [if_pos h, prot_mul_prot]
      congr 1
      rw [show c (t + 1) = c t + 1 by linarith]; push_cast; ring
    · have h' : ¬ c (t + 1) - c t = 1 := by rw [h]; omega
      rw [if_neg h', prot_inv, prot_mul_prot]
      congr 1
      rw [show c (t + 1) = c t - 1 by linarith]; push_cast; ring

variable {m k c} in
lemma verts_aw (hc : IsAlt k m c) : ∀ r t, verts (gv m k c t) (aw m k c t r) = bl m k c t r
  | 0, t => by
    simp only [aw, bl, verts_cons, verts_nil, gv_mul_τ]
  | r + 1, t => by
    simp only [aw, bl, verts_cons, gv_mul_τ, hv_mul_e hc, verts_aw hc r (t + 1)]

lemma mem_bl : ∀ r t x, x ∈ bl m k c t r → ∃ i, t ≤ i ∧ i ≤ t + r ∧ (x = gv m k c i ∨ x = hv m k c i)
  | 0, t, x, h => by
    simp only [bl, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at h
    exact ⟨t, le_rfl, by omega, h⟩
  | r + 1, t, x, h => by
    simp only [bl, List.mem_cons] at h
    rcases h with h | h | h
    · exact ⟨t, le_rfl, by omega, Or.inl h⟩
    · exact ⟨t, le_rfl, by omega, Or.inr h⟩
    · obtain ⟨i, h1, h2, h3⟩ := mem_bl r (t + 1) x h
      exact ⟨i, by omega, by omega, h3⟩

lemma gv_r (t : ℕ) : (gv m k c t).r = (c t : ZMod m) := by unfold gv; split_ifs <;> rfl
lemma hv_r (t : ℕ) : (hv m k c t).r = (c t : ZMod m) := by unfold hv; split_ifs <;> rfl
lemma gv_ne_hv (t : ℕ) : gv m k c t ≠ hv m k c t := by
  unfold gv hv; split_ifs <;> intro h <;> have := congrArg Pw.s h <;> simp [prot, pref] at this

variable {m k c} in
lemma eq_of_r (hc : IsAlt k m c) {i j : ℕ} (hi : i < m) (hj : j < m)
    (h : (c i : ZMod m) = (c j : ZMod m)) : i = j := by
  apply hc.2.2.2 i j hi hj
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]; push_cast; rw [h, sub_self]

variable {m k c} in
lemma bl_nodup (hc : IsAlt k m c) : ∀ r t, t + r < m → (bl m k c t r).Nodup
  | 0, t, h => by
    simp only [bl, List.nodup_cons, List.mem_singleton, List.not_mem_nil, not_false_eq_true,
      List.nodup_nil, and_true]
    exact gv_ne_hv m k c t
  | r + 1, t, h => by
    have ih := bl_nodup hc r (t + 1) (by omega)
    have key : ∀ x, x ∈ bl m k c (t + 1) r → x.r ≠ (c t : ZMod m) := by
      intro x hx hxr
      obtain ⟨i, h1, h2, h3⟩ := mem_bl m k c r (t + 1) x hx
      have : (c i : ZMod m) = (c t : ZMod m) := by
        rcases h3 with rfl | rfl
        · rw [← gv_r m k c i]; exact hxr
        · rw [← hv_r m k c i]; exact hxr
      have := eq_of_r hc (by omega) (by omega) this
      omega
    simp only [bl, List.nodup_cons, List.mem_cons, not_or]
    refine ⟨⟨gv_ne_hv m k c t, fun hx => key _ hx (gv_r m k c t)⟩,
      fun hx => key _ hx (hv_r m k c t), ih⟩

lemma aw_S : ∀ r t, ∀ d ∈ aw m k c t r, d ∈ Sg m k
  | 0, t, d, h => by
    simp only [aw, List.mem_singleton] at h; rw [h, mem_Sg']; right; right; rfl
  | r + 1, t, d, h => by
    simp only [aw, List.mem_cons] at h
    rcases h with rfl | rfl | h
    · rw [mem_Sg']; right; right; rfl
    · unfold eL; split_ifs <;> simp [mem_Sg']
    · exact aw_S r (t + 1) d h

lemma aw_count (hm : 3 ≤ m) : ∀ r t, (aw m k c t r).count (τ m k) = r + 1
  | 0, t => by simp [aw]
  | r + 1, t => by
    have he : eL m k c t ≠ τ m k := by
      unfold eL; split_ifs <;> first | exact ρ_ne_τ m k | exact ρinv_ne_τ m k
    simp only [aw, List.count_cons_self, List.count_cons, beq_iff_eq, he, if_false,
      aw_count hm r (t + 1)]
    all_goals omega

lemma length_aw : ∀ r t, (aw m k c t r).length = 2 * r + 1
  | 0, t => by simp [aw]
  | r + 1, t => by simp only [aw, List.length_cons, length_aw r (t + 1)]; ring

end AltWord

/-- **Theorem 9, Cayley case with m even (Lean).** If m ≥ 4 is even and k² ≡ 1 (mod m), then GP(m, k)
satisfies the conclusion of #339. -/
theorem ft_gp_even (m : ℕ) [NeZero m] (k : ℤ) (hm : 3 ≤ m) (he : Even m) (hk : (m : ℤ) ∣ k * k - 1) :
    ∃ (r k' : ℕ), 0 < r ∧ 0 < k' ∧
      ∃ (a b : Fin r → ZMod m × Bool) (P : ∀ i, (gp m k).Walk (a i) (b i)),
        (∀ i, (P i).IsHamiltonian) ∧
        ∀ e ∈ (gp m k).edgeSet, (Finset.univ.filter fun i => e ∈ (P i).edges).card = k' := by
  haveI : Fact (∀ a : ZMod m, k • k • a = a) := ⟨fun a => by
    rw [smul_smul, zsmul_eq_mul]
    have : ((k * k : ℤ) : ZMod m) = 1 := by
      have h := (ZMod.intCast_zmod_eq_zero_iff_dvd (k * k - 1) m).2 hk
      push_cast at h ⊢; linear_combination h
    rw [this, one_mul]⟩
  obtain ⟨c, hc⟩ := lemmaA k m (by omega) (Or.inr ⟨he, hk⟩)
  have h0 : gv m k c 0 = 1 := by
    have he0 : Even 0 := ⟨0, rfl⟩
    unfold gv; rw [if_pos he0, hc.1, Int.cast_zero]; rfl
  have hv := verts_aw hc (m - 1) 0
  rw [h0] at hv
  have hnd : (verts 1 (aw m k c 0 (m - 1))).Nodup := by
    rw [hv]; exact bl_nodup hc (m - 1) 0 (by omega)
  have hall : ∀ g, g ∈ verts 1 (aw m k c 0 (m - 1)) := by
    refine all_of_nodup _ hnd ?_
    rw [length_verts, length_aw, card_Γ]; omega
  refine ft_gp_of_word m k hm (aw m k c 0 (m - 1)) (aw_S m k c (m - 1) 0) hnd hall ?_
  rw [aw_count m k c hm]; omega

end FTGP

#print axioms FTGP.ft_gp_of_word
#print axioms FTGP.adj_iff
#print axioms FTGP.lowWord_ham
#print axioms FTGP.ft_gp_even

/-!
## m odd, k² ≡ 1 (mod m): the band path of NOTE.md §9.2 (new in v1.5.0)

Throughout this section k² ≡ 1 (mod m) (the section's `Fact`). With `a = 1 + k`, `d = 2B + 3` (odd, ≥ 3),
`m = d p`, `a = d e`, `gcd(e, p) = 1`, `p` odd, write `EO r n = O_{r − n a}` and `EI r n = I_{r − n a}`. Rows
`r ∈ [0, d)` and `n mod p` determine a vertex (`key_core`; used through `neO`, `neI`). The word `fullW m k p B`
(B square bands on rows {2b, 2b+1}, then one hexagon band on the
last three rows) is a Hamiltonian word from `1 = O_0` with `2p(B + 1)` spokes, and
`3 · 2p(B + 1) ≥ 2m − 1`. With `ft_gp_of_word` this gives the #339 conclusion.
-/


namespace FTGP
open FTDih

section Band
variable (m : ℕ) [NeZero m] (k : ℤ) [Fact (∀ a : ZMod m, k • k • a = a)]

/-- `O_{r − n(1+k)}` -/
def EO (r n : ℤ) : Γ m k := prot (((r - n * (1 + k) : ℤ)) : ZMod m)
/-- `I_{r − n(1+k)}` -/
def EI (r n : ℤ) : Γ m k := pref (((r - n * (1 + k) : ℤ)) : ZMod m)

variable {m k}

lemma EO_eq {r r' n n' : ℤ} (h1 : r = r') (h2 : n = n') : EO m k r n = EO m k r' n' := by
  subst h1 h2; rfl
lemma EI_eq {r r' n n' : ℤ} (h1 : r = r') (h2 : n = n') : EI m k r n = EI m k r' n' := by
  subst h1 h2; rfl

lemma EO_ne_EI (r n r' n' : ℤ) : EO m k r n ≠ EI m k r' n' := by
  intro h; have := congrArg Pw.s h; simp [EO, EI] at this

lemma EO_τ (r n : ℤ) : EO m k r n * τ m k = EI m k r n := by
  unfold EO EI τ; rw [prot_mul_pref, add_zero]
lemma EI_τ (r n : ℤ) : EI m k r n * τ m k = EO m k r n := by
  unfold EO EI τ; rw [pref_mul_pref]; simp
lemma EI_ρi (r n : ℤ) : EI m k r n * (ρ m k)⁻¹ = EI m k (r + 1) (n + 1) := by
  rw [ρ_inv]; unfold EI; rw [pref_mul_prot]; congr 1; rw [ksmul]; push_cast; ring
lemma EO_ρi (r n : ℤ) : EO m k r n * (ρ m k)⁻¹ = EO m k (r - 1) n := by
  rw [ρ_inv]; unfold EO; rw [prot_mul_prot]; congr 1; push_cast; ring
lemma EO_ρ (r n : ℤ) : EO m k r n * ρ m k = EO m k (r + 1) n := by
  unfold EO ρ; rw [prot_mul_prot]; congr 1; push_cast; ring

lemma EO_zero : EO m k 0 0 = 1 := by
  rw [pw_ext_iff]; simp [EO]

/-- the coordinate of `EO`/`EI` determines `r` (in `[0, d)`) and `n mod p` -/
lemma key_core {d p : ℕ} {e : ℤ} (hm : (m : ℤ) = d * p) (he : 1 + k = d * e) (hcop : IsCoprime e (p : ℤ))
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

lemma two_dvd_odd {p : ℕ} (hp : Odd p) {x : ℤ} (h : (p : ℤ) ∣ 2 * x) : (p : ℤ) ∣ x := by
  obtain ⟨t, ht⟩ := hp
  have hc : IsCoprime (p : ℤ) 2 := ⟨1, -(t : ℤ), by rw [ht]; push_cast; ring⟩
  exact hc.dvd_of_dvd_mul_left h

/-- distinctness of two outer (or two inner) vertices -/
lemma ne_core {d p : ℕ} {e : ℤ} (hm : (m : ℤ) = d * p) (he : 1 + k = d * e) (hcop : IsCoprime e (p : ℤ))
    (hd : 0 < d) (hpo : Odd p) {r n r' n' : ℤ} (c t : ℤ)
    (H : 0 ≤ r ∧ r < d ∧ 0 ≤ r' ∧ r' < d ∧ (r ≠ r' ∨ ((c = 1 ∨ c = 2) ∧ n - n' = c * t ∧ t ≠ 0 ∧
      -(p : ℤ) < t ∧ t < p)))
    (h : (((r - n * (1 + k) : ℤ)) : ZMod m) = (((r' - n' * (1 + k) : ℤ)) : ZMod m)) : False := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := H
  obtain ⟨hrr, hp⟩ := key_core hm he hcop hd ⟨h1, h2⟩ ⟨h3, h4⟩ h
  rcases h5 with h5 | ⟨hc, hn, ht0, ht1, ht2⟩
  · exact h5 hrr
  · rw [hn] at hp
    have hpt : (p : ℤ) ∣ t := by
      rcases hc with rfl | rfl
      · simpa using hp
      · exact two_dvd_odd hpo hp
    have := Int.eq_zero_of_abs_lt_dvd hpt (by rw [abs_lt]; constructor <;> omega)
    exact ht0 this

lemma neO {d p : ℕ} {e : ℤ} (hm : (m : ℤ) = d * p) (he : 1 + k = d * e) (hcop : IsCoprime e (p : ℤ))
    (hd : 0 < d) (hpo : Odd p) {r n r' n' : ℤ} (c t : ℤ)
    (H : 0 ≤ r ∧ r < d ∧ 0 ≤ r' ∧ r' < d ∧ (r ≠ r' ∨ ((c = 1 ∨ c = 2) ∧ n - n' = c * t ∧ t ≠ 0 ∧
      -(p : ℤ) < t ∧ t < p)))
    (h : EO m k r n = EO m k r' n') : False :=
  ne_core hm he hcop hd hpo c t H (by have := congrArg Pw.r h; simpa [EO] using this)

lemma neI {d p : ℕ} {e : ℤ} (hm : (m : ℤ) = d * p) (he : 1 + k = d * e) (hcop : IsCoprime e (p : ℤ))
    (hd : 0 < d) (hpo : Odd p) {r n r' n' : ℤ} (c t : ℤ)
    (H : 0 ≤ r ∧ r < d ∧ 0 ≤ r' ∧ r' < d ∧ (r ≠ r' ∨ ((c = 1 ∨ c = 2) ∧ n - n' = c * t ∧ t ≠ 0 ∧
      -(p : ℤ) < t ∧ t < p)))
    (h : EI m k r n = EI m k r' n') : False :=
  ne_core hm he hcop hd hpo c t H (by have := congrArg Pw.r h; simpa [EI] using this)

lemma EO_period {d p : ℕ} {e : ℤ} (hm : (m : ℤ) = d * p) (he : 1 + k = d * e) (r n : ℤ) :
    EO m k r (n + p) = EO m k r n := by
  unfold EO; congr 1
  have h0 : ((((p : ℤ) * (1 + k)) : ℤ) : ZMod m) = 0 := by
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd, he, hm]
    exact ⟨e, by ring⟩
  have : ((r - (n + p) * (1 + k) : ℤ) : ZMod m) = ((r - n * (1 + k) : ℤ) : ZMod m) -
      ((((p : ℤ) * (1 + k)) : ℤ) : ZMod m) := by push_cast; ring
  rw [this, h0, sub_zero]

variable (m k)

/-- square band word, `i` periods; the last period ends with the connector ρ -/
def sqW : ℕ → List (Γ m k)
  | 0 => []
  | 1 => [τ m k, (ρ m k)⁻¹, τ m k, ρ m k]
  | i + 2 => [τ m k, (ρ m k)⁻¹, τ m k, (ρ m k)⁻¹] ++ sqW (i + 1)

/-- hexagon band word, `i` periods; the last letter is dropped -/
def hexW : ℕ → List (Γ m k)
  | 0 => []
  | 1 => [τ m k, (ρ m k)⁻¹, (ρ m k)⁻¹, τ m k, (ρ m k)⁻¹]
  | i + 2 => [τ m k, (ρ m k)⁻¹, (ρ m k)⁻¹, τ m k, (ρ m k)⁻¹, (ρ m k)⁻¹] ++ hexW (i + 1)

/-- square band vertices -/
def sqL (r : ℤ) : ℤ → ℕ → List (Γ m k)
  | _, 0 => []
  | n, i + 1 => [EO m k r n, EI m k r n, EI m k (r + 1) (n + 1), EO m k (r + 1) (n + 1)] ++ sqL r (n + 1) i

/-- hexagon band vertices -/
def hexL (r : ℤ) : ℤ → ℕ → List (Γ m k)
  | _, 0 => []
  | n, i + 1 => [EO m k r n, EI m k r n, EI m k (r + 1) (n + 1), EI m k (r + 2) (n + 2), EO m k (r + 2) (n + 2),
      EO m k (r + 1) (n + 2)] ++ hexL r (n + 2) i

variable {m k}

lemma sq_verts (r : ℤ) : ∀ (i : ℕ) (n : ℤ) (rest : List (Γ m k)),
    verts (EO m k r n) (sqW m k (i + 1) ++ rest) = sqL m k r n (i + 1) ++ verts (EO m k (r + 2) (n + (i + 1))) rest
  | 0, n, rest => by
    simp only [sqW, sqL, List.cons_append, List.nil_append, List.append_nil, verts_cons, EO_τ, EI_ρi, EI_τ,
      EO_ρ]
    simp only [List.cons.injEq, true_and]
    congr 1; apply EO_eq <;> push_cast <;> ring
  | i + 1, n, rest => by
    have ih := sq_verts r i (n + 1) rest
    simp only [sqW, sqL, List.cons_append, List.nil_append, List.append_assoc, verts_cons, EO_τ, EI_ρi, EI_τ,
      EO_ρi] at ih ⊢
    rw [show EO m k (r + 1 - 1) (n + 1) = EO m k r (n + 1) from EO_eq (by ring) rfl, ih,
      show n + 1 + ((i : ℤ) + 1) = n + (((i + 1 : ℕ) : ℤ) + 1) by push_cast; ring]

lemma hex_verts (r : ℤ) : ∀ (i : ℕ) (n : ℤ), verts (EO m k r n) (hexW m k (i + 1)) = hexL m k r n (i + 1)
  | 0, n => by
    simp only [hexW, hexL, List.cons_append, List.nil_append, List.append_nil, verts_cons, verts_nil, EO_τ,
      EI_ρi, EI_τ, EO_ρi, List.cons.injEq, true_and, and_true]
    refine ⟨EI_eq (by ring) (by ring), EO_eq (by ring) (by ring), EO_eq (by ring) (by ring)⟩
  | i + 1, n => by
    have ih := hex_verts r i (n + 2)
    simp only [hexW, hexL, List.cons_append, List.nil_append, verts_cons, EO_τ, EI_ρi, EI_τ, EO_ρi] at ih ⊢
    rw [show EO m k (r + 1 + 1 - 1 - 1) (n + 1 + 1) = EO m k r (n + 2) from EO_eq (by ring) (by ring), ih]
    simp only [List.cons.injEq, true_and]
    refine ⟨EI_eq (by ring) (by ring), EO_eq (by ring) (by ring), EO_eq (by ring) (by ring), trivial⟩

variable (m k)

/-- the whole word: `B` square bands, then the hexagon band -/
def fullW (p : ℕ) : ℕ → List (Γ m k)
  | 0 => hexW m k p
  | b + 1 => sqW m k p ++ fullW p b

/-- the whole vertex list, from row `r` -/
def fullL (p : ℕ) : ℤ → ℕ → List (Γ m k)
  | r, 0 => hexL m k r 0 p
  | r, b + 1 => sqL m k r 0 p ++ fullL p (r + 2) b

variable {m k}

lemma full_verts {d p : ℕ} {e : ℤ} (hm : (m : ℤ) = d * p) (he : 1 + k = d * e) (hp : 0 < p) :
    ∀ (B : ℕ) (r : ℤ), verts (EO m k r 0) (fullW m k p B) = fullL m k p r B
  | 0, r => by
    obtain ⟨i, rfl⟩ : ∃ i, p = i + 1 := ⟨p - 1, by omega⟩
    exact hex_verts r i 0
  | b + 1, r => by
    obtain ⟨i, hi⟩ : ∃ i, p = i + 1 := ⟨p - 1, by omega⟩
    simp only [fullW, fullL]
    rw [hi, sq_verts r i 0, ← hi]
    have : EO m k (r + 2) (0 + ((i : ℤ) + 1)) = EO m k (r + 2) 0 := by
      have h := EO_period hm he (r + 2) 0
      rw [hi] at h; push_cast at h; simpa using h
    rw [this, full_verts hm he hp b (r + 2)]

/-! ### membership -/

lemma mem_sqL (r : ℤ) : ∀ (i : ℕ) (n : ℤ) (x : Γ m k), x ∈ sqL m k r n i →
    ∃ j : ℕ, j < i ∧ (x = EO m k r (n + j) ∨ x = EI m k r (n + j) ∨ x = EI m k (r + 1) (n + j + 1) ∨
      x = EO m k (r + 1) (n + j + 1))
  | 0, n, x, h => by simp [sqL] at h
  | i + 1, n, x, h => by
    simp only [sqL, List.cons_append, List.nil_append, List.mem_cons] at h
    rcases h with h | h | h | h | h
    · exact ⟨0, by omega, Or.inl (by rw [h]; simp)⟩
    · exact ⟨0, by omega, Or.inr (Or.inl (by rw [h]; simp))⟩
    · exact ⟨0, by omega, Or.inr (Or.inr (Or.inl (by rw [h]; simp)))⟩
    · exact ⟨0, by omega, Or.inr (Or.inr (Or.inr (by rw [h]; simp)))⟩
    · obtain ⟨j, hj, hx⟩ := mem_sqL r i (n + 1) x h
      refine ⟨j + 1, by omega, ?_⟩
      rcases hx with h | h | h | h
      · exact Or.inl (h.trans (EO_eq rfl (by push_cast; ring)))
      · exact Or.inr (Or.inl (h.trans (EI_eq rfl (by push_cast; ring))))
      · exact Or.inr (Or.inr (Or.inl (h.trans (EI_eq rfl (by push_cast; ring)))))
      · exact Or.inr (Or.inr (Or.inr (h.trans (EO_eq rfl (by push_cast; ring)))))

lemma mem_hexL (r : ℤ) : ∀ (i : ℕ) (n : ℤ) (x : Γ m k), x ∈ hexL m k r n i →
    ∃ j : ℕ, j < i ∧ (x = EO m k r (n + 2 * j) ∨ x = EI m k r (n + 2 * j) ∨
      x = EI m k (r + 1) (n + 2 * j + 1) ∨ x = EI m k (r + 2) (n + 2 * j + 2) ∨
      x = EO m k (r + 2) (n + 2 * j + 2) ∨ x = EO m k (r + 1) (n + 2 * j + 2))
  | 0, n, x, h => by simp [hexL] at h
  | i + 1, n, x, h => by
    simp only [hexL, List.cons_append, List.nil_append, List.mem_cons] at h
    rcases h with h | h | h | h | h | h | h
    · exact ⟨0, by omega, Or.inl (by rw [h]; simp)⟩
    · exact ⟨0, by omega, Or.inr (Or.inl (by rw [h]; simp))⟩
    · exact ⟨0, by omega, Or.inr (Or.inr (Or.inl (by rw [h]; simp)))⟩
    · exact ⟨0, by omega, Or.inr (Or.inr (Or.inr (Or.inl (by rw [h]; simp))))⟩
    · exact ⟨0, by omega, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by rw [h]; simp)))))⟩
    · exact ⟨0, by omega, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by rw [h]; simp)))))⟩
    · obtain ⟨j, hj, hx⟩ := mem_hexL r i (n + 2) x h
      refine ⟨j + 1, by omega, ?_⟩
      rcases hx with h | h | h | h | h | h
      · exact Or.inl (h.trans (EO_eq rfl (by push_cast; ring)))
      · exact Or.inr (Or.inl (h.trans (EI_eq rfl (by push_cast; ring))))
      · exact Or.inr (Or.inr (Or.inl (h.trans (EI_eq rfl (by push_cast; ring)))))
      · exact Or.inr (Or.inr (Or.inr (Or.inl (h.trans (EI_eq rfl (by push_cast; ring))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (h.trans (EO_eq rfl (by push_cast; ring)))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (h.trans (EO_eq rfl (by push_cast; ring)))))))

/-- rows of `fullL` -/
lemma mem_fullL (p : ℕ) : ∀ (B : ℕ) (r : ℤ) (x : Γ m k), x ∈ fullL m k p r B →
    ∃ r' n : ℤ, r ≤ r' ∧ r' ≤ r + 2 * B + 2 ∧ (x = EO m k r' n ∨ x = EI m k r' n)
  | 0, r, x, h => by
    simp only [fullL] at h
    obtain ⟨j, -, hx⟩ := mem_hexL r p 0 x h
    rcases hx with hx | hx | hx | hx | hx | hx
    · exact ⟨_, _, le_rfl, by omega, Or.inl hx⟩
    · exact ⟨_, _, le_rfl, by omega, Or.inr hx⟩
    · exact ⟨_, _, by omega, by omega, Or.inr hx⟩
    · exact ⟨_, _, by omega, by omega, Or.inr hx⟩
    · exact ⟨_, _, by omega, by omega, Or.inl hx⟩
    · exact ⟨_, _, by omega, by omega, Or.inl hx⟩
  | b + 1, r, x, h => by
    simp only [fullL, List.mem_append] at h
    rcases h with h | h
    · obtain ⟨j, -, hx⟩ := mem_sqL r p 0 x h
      rcases hx with hx | hx | hx | hx
      · exact ⟨_, _, le_rfl, by omega, Or.inl hx⟩
      · exact ⟨_, _, le_rfl, by omega, Or.inr hx⟩
      · exact ⟨_, _, by omega, by push_cast; omega, Or.inr hx⟩
      · exact ⟨_, _, by omega, by push_cast; omega, Or.inl hx⟩
    · obtain ⟨r', n, h1, h2, hx⟩ := mem_fullL p b (r + 2) x h
      exact ⟨r', n, by omega, by push_cast; omega, hx⟩

/-! ### distinctness -/

section Distinct
variable {d p : ℕ} {e : ℤ} (hm : (m : ℤ) = d * p) (he : 1 + k = d * e) (hcop : IsCoprime e (p : ℤ))
  (hd : 0 < d) (hpo : Odd p)
include hm he hcop hd hpo

lemma sqL_nodup (r : ℤ) (hr0 : 0 ≤ r) (hr1 : r + 1 < d) :
    ∀ (i : ℕ) (n : ℤ), i ≤ p → (sqL m k r n i).Nodup
  | 0, n, _ => by simp [sqL]
  | i + 1, n, hi => by
    have ih := sqL_nodup r hr0 hr1 i (n + 1) (by omega)
    simp only [sqL, List.cons_append, List.nil_append, List.nodup_cons, List.mem_cons, not_or]
    refine ⟨⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ih⟩⟩
    · intro h; exact EO_ne_EI _ _ _ _ h
    · intro h; exact EO_ne_EI _ _ _ _ h
    · intro h; exact neO hm he hcop hd hpo 1 0 (by omega) h
    · intro hx
      obtain ⟨j, hj, hx⟩ := mem_sqL r i (n + 1) _ hx
      rcases hx with h | h | h | h
      · exact neO hm he hcop hd hpo 1 (-((j : ℤ) + 1)) (by omega) h
      · exact EO_ne_EI _ _ _ _ h
      · exact EO_ne_EI _ _ _ _ h
      · exact neO hm he hcop hd hpo 1 0 (by omega) h
    · intro h; exact neI hm he hcop hd hpo 1 0 (by omega) h
    · intro h; exact EO_ne_EI _ _ _ _ h.symm
    · intro hx
      obtain ⟨j, hj, hx⟩ := mem_sqL r i (n + 1) _ hx
      rcases hx with h | h | h | h
      · exact EO_ne_EI _ _ _ _ h.symm
      · exact neI hm he hcop hd hpo 1 (-((j : ℤ) + 1)) (by omega) h
      · exact neI hm he hcop hd hpo 1 0 (by omega) h
      · exact EO_ne_EI _ _ _ _ h.symm
    · intro h; exact EO_ne_EI _ _ _ _ h.symm
    · intro hx
      obtain ⟨j, hj, hx⟩ := mem_sqL r i (n + 1) _ hx
      rcases hx with h | h | h | h
      · exact EO_ne_EI _ _ _ _ h.symm
      · exact neI hm he hcop hd hpo 1 0 (by omega) h
      · exact neI hm he hcop hd hpo 1 (-((j : ℤ) + 1)) (by omega) h
      · exact EO_ne_EI _ _ _ _ h.symm
    · intro hx
      obtain ⟨j, hj, hx⟩ := mem_sqL r i (n + 1) _ hx
      rcases hx with h | h | h | h
      · exact neO hm he hcop hd hpo 1 0 (by omega) h
      · exact EO_ne_EI _ _ _ _ h
      · exact EO_ne_EI _ _ _ _ h
      · exact neO hm he hcop hd hpo 1 (-((j : ℤ) + 1)) (by omega) h

lemma hexL_nodup (r : ℤ) (hr0 : 0 ≤ r) (hr1 : r + 2 < d) :
    ∀ (i : ℕ) (n : ℤ), i ≤ p → (hexL m k r n i).Nodup
  | 0, n, _ => by simp [hexL]
  | i + 1, n, hi => by
    have ih := hexL_nodup r hr0 hr1 i (n + 2) (by omega)
    simp only [hexL, List.cons_append, List.nil_append, List.nodup_cons, List.mem_cons, not_or]
    refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ⟨?_, ?_⟩,
      ⟨?_, ih⟩⟩
    all_goals first
      | (intro h; first
          | exact EO_ne_EI _ _ _ _ h
          | exact EO_ne_EI _ _ _ _ h.symm
          | exact neO hm he hcop hd hpo 1 0 (by omega) h
          | exact neI hm he hcop hd hpo 1 0 (by omega) h)
      | (intro hx
         obtain ⟨j, hj, hx⟩ := mem_hexL r i (n + 2) _ hx
         rcases hx with h | h | h | h | h | h <;> first
          | exact EO_ne_EI _ _ _ _ h
          | exact EO_ne_EI _ _ _ _ h.symm
          | exact neO hm he hcop hd hpo 2 (-((j : ℤ) + 1)) (by omega) h
          | exact neI hm he hcop hd hpo 2 (-((j : ℤ) + 1)) (by omega) h)

lemma fullL_nodup : ∀ (B : ℕ) (r : ℤ), 0 ≤ r → r + 2 * B + 2 < d → (fullL m k p r B).Nodup
  | 0, r, h0, h1 => by
    simp only [fullL]; exact hexL_nodup hm he hcop hd hpo r h0 (by omega) p 0 le_rfl
  | b + 1, r, h0, h1 => by
    simp only [fullL]
    rw [List.nodup_append]
    refine ⟨sqL_nodup hm he hcop hd hpo r h0 (by push_cast at h1; omega) p 0 le_rfl,
      fullL_nodup b (r + 2) (by omega) (by push_cast at h1 ⊢; omega), ?_⟩
    intro x hx y hy hxy
    subst hxy
    obtain ⟨j, -, hx⟩ := mem_sqL r p 0 x hx
    obtain ⟨r', n', h1', h2', hy⟩ := mem_fullL p b (r + 2) x hy
    push_cast at h1
    rcases hx with hx | hx | hx | hx <;> rcases hy with hy | hy <;> rw [hx] at hy <;> first
      | exact EO_ne_EI _ _ _ _ hy
      | exact EO_ne_EI _ _ _ _ hy.symm
      | exact neO hm he hcop hd hpo 1 0 (by omega) hy
      | exact neI hm he hcop hd hpo 1 0 (by omega) hy

end Distinct

/-! ### counts -/

lemma sqL_length (r : ℤ) : ∀ (i : ℕ) (n : ℤ), (sqL m k r n i).length = 4 * i
  | 0, _ => rfl
  | i + 1, n => by simp only [sqL, List.length_append, sqL_length r i (n + 1)]; simp; ring

lemma hexL_length (r : ℤ) : ∀ (i : ℕ) (n : ℤ), (hexL m k r n i).length = 6 * i
  | 0, _ => rfl
  | i + 1, n => by simp only [hexL, List.length_append, hexL_length r i (n + 2)]; simp; ring

lemma fullL_length (p : ℕ) : ∀ (B : ℕ) (r : ℤ), (fullL m k p r B).length = 4 * p * B + 6 * p
  | 0, r => by simp only [fullL, hexL_length]; ring
  | b + 1, r => by simp only [fullL, List.length_append, sqL_length, fullL_length p b]; ring

lemma sqW_count : ∀ i : ℕ, (sqW m k i).count (τ m k) = 2 * i
  | 0 => rfl
  | 1 => by simp [sqW, List.count_cons, ρ_ne_τ, ρinv_ne_τ]
  | i + 2 => by
    simp only [sqW, List.count_append, sqW_count (i + 1)]
    simp [List.count_cons, ρ_ne_τ, ρinv_ne_τ]; ring

lemma hexW_count : ∀ i : ℕ, (hexW m k i).count (τ m k) = 2 * i
  | 0 => rfl
  | 1 => by simp [hexW, List.count_cons, ρ_ne_τ, ρinv_ne_τ]
  | i + 2 => by
    simp only [hexW, List.count_append, hexW_count (i + 1)]
    simp [List.count_cons, ρ_ne_τ, ρinv_ne_τ]; ring

lemma fullW_count (p : ℕ) : ∀ B : ℕ, (fullW m k p B).count (τ m k) = 2 * p * B + 2 * p
  | 0 => by simp only [fullW, hexW_count]; ring
  | b + 1 => by simp only [fullW, List.count_append, sqW_count, fullW_count p b]; ring

lemma sqW_S : ∀ i, ∀ x ∈ sqW m k i, x ∈ Sg m k
  | 0 => by simp [sqW]
  | 1 => by intro x hx; simp only [sqW, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hx
            rw [mem_Sg']; tauto
  | i + 2 => by
    intro x hx
    simp only [sqW, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with hx | hx
    · rw [mem_Sg']; tauto
    · exact sqW_S (i + 1) x hx

lemma hexW_S : ∀ i, ∀ x ∈ hexW m k i, x ∈ Sg m k
  | 0 => by simp [hexW]
  | 1 => by intro x hx; simp only [hexW, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hx
            rw [mem_Sg']; tauto
  | i + 2 => by
    intro x hx
    simp only [hexW, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with hx | hx
    · rw [mem_Sg']; tauto
    · exact hexW_S (i + 1) x hx

lemma fullW_S (p : ℕ) : ∀ B, ∀ x ∈ fullW m k p B, x ∈ Sg m k
  | 0 => hexW_S p
  | b + 1 => by
    intro x hx
    simp only [fullW, List.mem_append] at hx
    rcases hx with hx | hx
    · exact sqW_S p x hx
    · exact fullW_S p b x hx

variable (m k)

/-- **Band case.** Under the standing hypothesis k² ≡ 1 (mod m) (the section's `Fact`), and `m = (2B + 3) p`,
`1 + k = (2B + 3) e`, `gcd(e, p) = 1`, `p` odd: GP(m, k) satisfies the #339 conclusion. -/
theorem ft_gp_band (hm3 : 3 ≤ m) (B p : ℕ) (e : ℤ) (hm : (m : ℤ) = (2 * B + 3 : ℕ) * p)
    (he : 1 + k = (2 * B + 3 : ℕ) * e) (hcop : IsCoprime e (p : ℤ)) (hpo : Odd p) :
    ∃ (r k' : ℕ), 0 < r ∧ 0 < k' ∧
      ∃ (a b : Fin r → ZMod m × Bool) (P : ∀ i, (gp m k).Walk (a i) (b i)),
        (∀ i, (P i).IsHamiltonian) ∧
        ∀ e ∈ (gp m k).edgeSet, (Finset.univ.filter fun i => e ∈ (P i).edges).card = k' := by
  have hp : 0 < p := by obtain ⟨t, ht⟩ := hpo; omega
  have hd : 0 < 2 * B + 3 := by omega
  have hv := full_verts (m := m) (k := k) hm he hp B 0
  rw [EO_zero] at hv
  have hnd : (verts 1 (fullW m k p B)).Nodup := by
    rw [hv]; exact fullL_nodup hm he hcop hd hpo B 0 le_rfl (by push_cast; omega)
  have hmN : m = (2 * B + 3) * p := by exact_mod_cast hm
  have hall : ∀ g, g ∈ verts 1 (fullW m k p B) := by
    refine all_of_nodup _ hnd ?_
    rw [hv, fullL_length, card_Γ, hmN]; ring
  refine ft_gp_of_word m k hm3 (fullW m k p B) (fullW_S p B) hnd hall ?_
  rw [fullW_count, hmN]
  have : 2 * ((2 * B + 3) * p) ≤ 3 * (2 * p * B + 2 * p) + 1 := by nlinarith
  omega

end Band

/-- An alternating sequence for `(m, k)` gives the #339 conclusion (the end of `ft_gp_even`). -/
theorem ft_gp_of_alt (m : ℕ) [NeZero m] (k : ℤ) [Fact (∀ a : ZMod m, k • k • a = a)] (hm : 3 ≤ m)
    (c : ℕ → ℤ) (hc : IsAlt k m c) :
    ∃ (r k' : ℕ), 0 < r ∧ 0 < k' ∧
      ∃ (a b : Fin r → ZMod m × Bool) (P : ∀ i, (gp m k).Walk (a i) (b i)),
        (∀ i, (P i).IsHamiltonian) ∧
        ∀ e ∈ (gp m k).edgeSet, (Finset.univ.filter fun i => e ∈ (P i).edges).card = k' := by
  have h0 : gv m k c 0 = 1 := by
    have he0 : Even 0 := ⟨0, rfl⟩
    unfold gv; rw [if_pos he0, hc.1, Int.cast_zero]; rfl
  have hv := verts_aw hc (m - 1) 0
  rw [h0] at hv
  have hnd : (verts 1 (aw m k c 0 (m - 1))).Nodup := by
    rw [hv]; exact bl_nodup hc (m - 1) 0 (by omega)
  have hall : ∀ g, g ∈ verts 1 (aw m k c 0 (m - 1)) := by
    refine all_of_nodup _ hnd ?_
    rw [length_verts, length_aw, card_Γ]; omega
  refine ft_gp_of_word m k hm (aw m k c 0 (m - 1)) (aw_S m k c (m - 1) 0) hnd hall ?_
  rw [aw_count m k c hm]; omega

/-- **Theorem 9, case m odd, k² ≡ 1 (mod m).** -/
theorem ft_gp_odd (m : ℕ) [NeZero m] (k : ℤ) (hm : 3 ≤ m) (ho : Odd m) (hk : (m : ℤ) ∣ k * k - 1) :
    ∃ (r k' : ℕ), 0 < r ∧ 0 < k' ∧
      ∃ (a b : Fin r → ZMod m × Bool) (P : ∀ i, (gp m k).Walk (a i) (b i)),
        (∀ i, (P i).IsHamiltonian) ∧
        ∀ e ∈ (gp m k).edgeSet, (Finset.univ.filter fun i => e ∈ (P i).edges).card = k' := by
  haveI : Fact (∀ a : ZMod m, k • k • a = a) := ⟨fun a => by
    rw [smul_smul, zsmul_eq_mul]
    have : ((k * k : ℤ) : ZMod m) = 1 := by
      have h := (ZMod.intCast_zmod_eq_zero_iff_dvd (k * k - 1) m).2 hk
      push_cast at h ⊢; linear_combination h
    rw [this, one_mul]⟩
  set d := Int.gcd (1 + k) m with hddef
  have hdk : (d : ℤ) ∣ 1 + k := Int.gcd_dvd_left _ _
  have hdm : (d : ℤ) ∣ (m : ℤ) := Int.gcd_dvd_right _ _
  have hd0 : 0 < d := Int.gcd_pos_of_ne_zero_right _ (by exact_mod_cast (NeZero.ne m))
  obtain ⟨p, hp⟩ : d ∣ m := by exact_mod_cast hdm
  obtain ⟨e, he⟩ := hdk
  have hcop : Int.gcd e p = 1 := by
    have h1 : Int.gcd (1 + k) m = Int.gcd ((d : ℤ) * e) ((d : ℤ) * p) := by
      rw [← he, hp]; push_cast; rfl
    rw [Int.gcd_mul_left, Int.natAbs_natCast, ← hddef] at h1
    have : d * 1 = d * Int.gcd e p := by rw [mul_one]; exact h1
    exact (Nat.eq_of_mul_eq_mul_left hd0 this).symm
  have hdo : Odd d := Odd.of_dvd_nat ho ⟨p, hp⟩
  have hpo : Odd p := Odd.of_dvd_nat ho ⟨d, by rw [hp, mul_comm]⟩
  by_cases hd1 : d = 1
  · -- k ≡ 1 (mod m): an alternating sequence (Lemma 8.A (a))
    have hc1 : IsCoprime (m : ℤ) (1 + k) := by
      rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd_comm, ← hddef, hd1]
    have hk' : (m : ℤ) ∣ (k - 1) * (1 + k) := by
      have : (k - 1) * (1 + k) = k * k - 1 := by ring
      rw [this]; exact hk
    have hk1 : (m : ℤ) ∣ k - 1 := hc1.dvd_of_dvd_mul_right hk'
    obtain ⟨c, hc⟩ := lemmaA k m (by omega) (Or.inl ⟨1, Or.inl rfl, hk1⟩)
    exact ft_gp_of_alt m k hm c hc
  · obtain ⟨B, hB⟩ : ∃ B, d = 2 * B + 3 := by
      obtain ⟨t, ht⟩ := hdo
      exact ⟨t - 1, by omega⟩
    refine ft_gp_band m k hm B p e ?_ ?_ (Int.isCoprime_iff_gcd_eq_one.2 hcop) hpo
    · rw [← hB]; exact_mod_cast hp
    · rw [← hB]; exact he

/-- **Theorem 9 for every Cayley generalized Petersen graph**: m ≥ 3 and k² ≡ 1 (mod m). -/
theorem ft_gp_cayley (m : ℕ) [NeZero m] (k : ℤ) (hm : 3 ≤ m) (hk : (m : ℤ) ∣ k * k - 1) :
    ∃ (r k' : ℕ), 0 < r ∧ 0 < k' ∧
      ∃ (a b : Fin r → ZMod m × Bool) (P : ∀ i, (gp m k).Walk (a i) (b i)),
        (∀ i, (P i).IsHamiltonian) ∧
        ∀ e ∈ (gp m k).edgeSet, (Finset.univ.filter fun i => e ∈ (P i).edges).card = k' := by
  rcases Nat.even_or_odd m with he | ho
  · exact ft_gp_even m k hm he hk
  · exact ft_gp_odd m k hm ho hk

end FTGP

#print axioms FTGP.ft_gp_band
#print axioms FTGP.ft_gp_odd
#print axioms FTGP.ft_gp_cayley
