/-
Copyright 2026 Ming-Chih Kao. Licensed under the Apache License, Version 2.0;
see the LICENSE file at the root of this repository.
Ported from github.com/koolkao/gillibert-fair-traversal-abelian (v1.7.0, commit
06c3a8732759afca38331762b76113135e475ac6) to Lean v4.36.0 and the module system.
Port: `Walk.IsHamiltonian.map` now takes the graph map implicitly (`(f := …)` added).
-/
module

public import Mathlib
public import FairTraversal.FTAbelian

/-!
# Theorem 7 (Lean): Fair Traversal for Cayley graphs of generalized dihedral groups

New in v1.3.0. Main theorems (namespace `FTDih`); each conclusion is the conclusion of the Left to Solve
statement of Fair Traversal (#339), word for word:

* `main_dih_cayley`: #339 for every graph carrying a labelling `e : V ≃ Dih A` by a generalized dihedral
  group `Dih A = A ⋊ ⟨τ⟩` (`A` finite abelian, `τ a τ = -a`), `G.Adj u v ↔ (e u)⁻¹ * e v ∈ S`, any `S`;
* `main_dihedralGroup_cayley n`: the same for Mathlib's `DihedralGroup n`;
* `main_quaternionGroup_cayley n`: the same for Mathlib's dicyclic group `QuaternionGroup n`
  (generalized quaternion groups for `n` a power of 2), via Corollary 7′.

Not covered: the generalized dicyclic groups `Dic(A, z)` for non-cyclic `A` (paper only, NOTE.md §7.5).

This file uses `FTAbelian.lean` (Weber's lemma `FTAbelian.weber`, `FTAbelian.greedy` and two counting
lemmas). In the authors' workspace it was compiled as one 3,584-line file containing a verbatim copy of
`FTAbelian.lean`; here the copy is replaced by `import FTAbelian`, and nothing else is changed.
-/

@[expose] public section


open Finset Pointwise

-- ===== DihBase.lean =====

/-!
# Generalized dihedral groups; Hamiltonian paths in Cayley graphs of arbitrary finite groups

`Dih A` is the generalized dihedral group `A ⋊ ⟨τ⟩` (`τ² = 1`, `τ a τ = -a`) on `A × Bool`:
`⟨a, i⟩ * ⟨b, j⟩ = ⟨a + (±b), i xor j⟩` (`-b` iff `i = true`).

For any finite group `Γ` and Cayley graph `x ~ y ↔ x⁻¹ * y ∈ S`, a path is a start vertex and a list
of steps (right multiplications). Left translates of a Hamiltonian path are Hamiltonian, and an edge
`{u, u s}` lies on exactly `count s + count s⁻¹` of the `|Γ|` translates (`sum_count_edgesL`).
`assemble`: a rational convex combination of step lists whose paired counts are constant on `S`
gives the Fair Traversal conclusion (#339) word for word.
-/

open Finset

namespace FTDih

@[ext] structure Dih (A : Type) where
  r : A
  s : Bool
deriving DecidableEq

section DihGroup
variable {A : Type} [AddCommGroup A]

/-- `sg false b = b`, `sg true b = -b` -/
def sg : Bool → A → A
  | false, b => b
  | true, b => -b

@[simp] lemma sg_false (b : A) : sg false b = b := rfl
@[simp] lemma sg_true (b : A) : sg true b = -b := rfl

instance : Mul (Dih A) := ⟨fun x y => ⟨x.r + sg x.s y.r, xor x.s y.s⟩⟩
instance : One (Dih A) := ⟨⟨0, false⟩⟩
instance : Inv (Dih A) := ⟨fun x => ⟨-(sg x.s x.r), x.s⟩⟩

@[simp] lemma mul_r' (x y : Dih A) : (x * y).r = x.r + sg x.s y.r := rfl
@[simp] lemma mul_s' (x y : Dih A) : (x * y).s = xor x.s y.s := rfl
@[simp] lemma one_r' : (1 : Dih A).r = 0 := rfl
@[simp] lemma one_s' : (1 : Dih A).s = false := rfl
@[simp] lemma inv_r' (x : Dih A) : x⁻¹.r = -(sg x.s x.r) := rfl
@[simp] lemma inv_s' (x : Dih A) : x⁻¹.s = x.s := rfl

instance : Group (Dih A) where
  mul := (· * ·)
  one := 1
  inv := (·⁻¹)
  mul_assoc x y z := by
    rcases x with ⟨a, i⟩; rcases y with ⟨b, j⟩; rcases z with ⟨c, k⟩
    ext
    · cases i <;> cases j <;> simp <;> abel
    · cases i <;> cases j <;> cases k <;> rfl
  one_mul x := by
    rcases x with ⟨a, i⟩; ext <;> simp
  mul_one x := by
    rcases x with ⟨a, i⟩; cases i <;> ext <;> simp
  inv_mul_cancel x := by
    rcases x with ⟨a, i⟩; cases i <;> ext <;> simp

/-- rotation -/
def rot (a : A) : Dih A := ⟨a, false⟩
/-- reflection -/
def ref (b : A) : Dih A := ⟨b, true⟩

@[simp] lemma rot_r (a : A) : (rot a).r = a := rfl
@[simp] lemma rot_s (a : A) : (rot a).s = false := rfl
@[simp] lemma ref_r (a : A) : (ref a).r = a := rfl
@[simp] lemma ref_s (a : A) : (ref a).s = true := rfl

lemma rot_mul_rot (a b : A) : rot a * rot b = rot (a + b) := by ext <;> simp [rot]
lemma rot_mul_ref (a b : A) : rot a * ref b = ref (a + b) := by ext <;> simp [rot, ref]
lemma ref_mul_rot (a b : A) : ref a * rot b = ref (a - b) := by
  ext <;> simp [rot, ref, sub_eq_add_neg]
lemma ref_mul_ref (a b : A) : ref a * ref b = rot (a - b) := by
  ext <;> simp [rot, ref, sub_eq_add_neg]
lemma rot_inv (a : A) : (rot a)⁻¹ = rot (-a) := by ext <;> simp [rot]
lemma ref_inv (a : A) : (ref a)⁻¹ = ref a := by ext <;> simp [ref]
lemma one_eq_rot : (1 : Dih A) = rot 0 := rfl
lemma rot_injective : Function.Injective (rot : A → Dih A) := fun a b h => by
  simpa using congrArg Dih.r h
lemma ref_injective : Function.Injective (ref : A → Dih A) := fun a b h => by
  simpa using congrArg Dih.r h
lemma rot_ne_ref (a b : A) : rot a ≠ ref b := fun h => by simpa using congrArg Dih.s h
lemma eq_rot_or_ref (x : Dih A) : x = rot x.r ∨ x = ref x.r := by
  rcases x with ⟨a, i⟩; cases i
  · left; rfl
  · right; rfl
lemma rot_pow (a : A) (k : ℕ) : rot a ^ k = rot (k • a) := by
  induction k with
  | zero => rw [pow_zero, zero_nsmul]; rfl
  | succ k ih => rw [pow_succ, ih, rot_mul_rot, succ_nsmul]

def dihEquiv : A × Bool ≃ Dih A :=
  ⟨fun p => ⟨p.1, p.2⟩, fun x => (x.r, x.s), fun _ => rfl, fun _ => rfl⟩

instance [Fintype A] : Fintype (Dih A) := Fintype.ofEquiv (A × Bool) dihEquiv

lemma card_dih [Fintype A] : Fintype.card (Dih A) = 2 * Fintype.card A := by
  rw [← Fintype.card_congr (dihEquiv (A := A)), Fintype.card_prod, Fintype.card_bool, mul_comm]

end DihGroup

/-! ## Paths as step lists in an arbitrary group -/

section Paths
variable {Γ : Type} [Group Γ] [DecidableEq Γ]

/-- vertices of the path starting at `x` with steps `ds` (right multiplications) -/
def verts : Γ → List Γ → List Γ
  | x, [] => [x]
  | x, d :: ds => x :: verts (x * d) ds

@[simp] lemma verts_nil (x : Γ) : verts x [] = [x] := rfl
@[simp] lemma verts_cons (x d : Γ) (ds : List Γ) : verts x (d :: ds) = x :: verts (x * d) ds := rfl

lemma verts_mul (g x : Γ) (ds : List Γ) : verts (g * x) ds = (verts x ds).map (g * ·) := by
  induction ds generalizing x with
  | nil => simp
  | cons d ds ih => simp only [verts_cons, List.map_cons, mul_assoc, ih]

lemma verts_eq (x : Γ) (ds : List Γ) : verts x ds = (verts 1 ds).map (x * ·) := by
  simpa using verts_mul x 1 ds

lemma verts_append (x c : Γ) (ds₁ ds₂ : List Γ) :
    verts x (ds₁ ++ c :: ds₂) = verts x ds₁ ++ verts (x * ds₁.prod * c) ds₂ := by
  induction ds₁ generalizing x with
  | nil => simp
  | cons d ds ih => simp [ih, mul_assoc]

lemma length_verts (x : Γ) (ds : List Γ) : (verts x ds).length = ds.length + 1 := by
  induction ds generalizing x with
  | nil => simp
  | cons d ds ih => simp [ih]

lemma mem_verts_self (x : Γ) (ds : List Γ) : x ∈ verts x ds := by
  cases ds <;> simp

/-- reversed step list -/
def rev (ds : List Γ) : List Γ := (ds.map (·⁻¹)).reverse

lemma rev_cons (d : Γ) (ds : List Γ) : rev (d :: ds) = rev ds ++ [d⁻¹] := by simp [rev]

lemma prod_rev (ds : List Γ) : (rev ds).prod = ds.prod⁻¹ := by
  rw [rev, List.prod_inv_reverse]

lemma verts_rev (x : Γ) (ds : List Γ) : verts (x * ds.prod) (rev ds) = (verts x ds).reverse := by
  induction ds generalizing x with
  | nil => simp [rev]
  | cons d ds ih =>
    rw [rev_cons, show (rev ds ++ [d⁻¹]) = rev ds ++ d⁻¹ :: [] from rfl, verts_append, verts_nil,
      List.prod_cons, ← mul_assoc, ih, prod_rev, verts_cons, List.reverse_cons]
    congr 2
    group

lemma mem_rev {S : Finset Γ} (hinv : ∀ s ∈ S, s⁻¹ ∈ S) (ds : List Γ) (h : ∀ d ∈ ds, d ∈ S) :
    ∀ d ∈ rev ds, d ∈ S := by
  intro d hd
  simp only [rev, List.mem_reverse, List.mem_map] at hd
  obtain ⟨y, hy, rfl⟩ := hd
  exact hinv y (h y hy)

/-- paired step count -/
def pc (d : Γ) (ds : List Γ) : ℕ := ds.count d + ds.count d⁻¹

lemma count_rev (d : Γ) (ds : List Γ) : (rev ds).count d = ds.count d⁻¹ := by
  rw [rev, List.count_reverse]
  have := List.count_map_of_injective ds (fun x : Γ => x⁻¹) inv_injective d⁻¹
  simpa using this

lemma pc_rev (d : Γ) (ds : List Γ) : pc d (rev ds) = pc d ds := by
  simp [pc, count_rev, add_comm]

lemma pc_append (d c : Γ) (l₁ l₂ : List Γ) :
    pc d (l₁ ++ c :: l₂) = pc d l₁ + pc d l₂ + pc d [c] := by
  simp only [pc, List.count_append, List.count_cons, List.count_nil]
  omega

lemma pc_inv (d c : Γ) : pc d [c⁻¹] = pc d [c] := by
  have e1 : c⁻¹ = d ↔ c = d⁻¹ := inv_eq_iff_eq_inv
  have e2 : c⁻¹ = d⁻¹ ↔ c = d := inv_inj
  simp only [pc, List.count_cons, List.count_nil, beq_iff_eq, e1, e2]
  split_ifs <;> omega

lemma pc_nil (d : Γ) : pc d [] = 0 := rfl

end Paths

/-! ## Cayley graphs of finite groups: walks, translation counting, assembly -/

section Graph
variable {Γ : Type} [Group Γ] [Fintype Γ] [DecidableEq Γ]
  (S : Finset Γ) (G : SimpleGraph Γ) (hG : ∀ x y, G.Adj x y ↔ x⁻¹ * y ∈ S)

include hG in
lemma inv_mem_of : ∀ s ∈ S, s⁻¹ ∈ S := by
  intro s hs
  have h1 : G.Adj 1 s := (hG 1 s).2 (by simpa using hs)
  simpa using (hG s 1).1 h1.symm

include hG in
lemma one_not_mem_of : (1 : Γ) ∉ S := by
  intro h
  exact G.irrefl ((hG 1 1).2 (by simpa using h))

/-- the walk with start `x` and steps `ds` -/
def walkOf : (x : Γ) → (ds : List Γ) → (∀ d ∈ ds, d ∈ S) → Σ y, G.Walk x y
  | x, [], _ => ⟨x, SimpleGraph.Walk.nil⟩
  | x, d :: ds, h =>
    ⟨(walkOf (x * d) ds (fun y hy => h y (List.mem_cons_of_mem d hy))).1,
      SimpleGraph.Walk.cons ((hG x (x * d)).2 (by simpa using h d (by simp)))
        (walkOf (x * d) ds (fun y hy => h y (List.mem_cons_of_mem d hy))).2⟩

/-- edges of that walk -/
def edgesL : Γ → List Γ → List (Sym2 Γ)
  | _, [] => []
  | x, d :: ds => s(x, x * d) :: edgesL (x * d) ds

lemma walkOf_support (x : Γ) (ds : List Γ) (h : ∀ d ∈ ds, d ∈ S) :
    (walkOf S G hG x ds h).2.support = verts x ds := by
  induction ds generalizing x with
  | nil => rfl
  | cons d ds ih => simp [walkOf, ih]

lemma walkOf_edges (x : Γ) (ds : List Γ) (h : ∀ d ∈ ds, d ∈ S) :
    (walkOf S G hG x ds h).2.edges = edgesL x ds := by
  induction ds generalizing x with
  | nil => rfl
  | cons d ds ih => simp [walkOf, edgesL, ih]

omit [Fintype Γ] in
lemma ind_sym2 (u s d c : Γ) (hs : s ≠ 1) :
    (if s(c, c * d) = s(u, u * s) then 1 else 0 : ℕ) =
      (if c = u ∧ d = s then 1 else 0) + (if c = u * s ∧ d = s⁻¹ then 1 else 0) := by
  by_cases h1 : c = u ∧ d = s
  · have h2 : ¬ (c = u * s ∧ d = s⁻¹) := by
      rintro ⟨h3, -⟩
      apply hs
      have h4 : u = u * s := h1.1 ▸ h3
      simpa using h4
    rw [if_pos h1, if_neg h2, if_pos (by rw [h1.1, h1.2])]
  · by_cases h2 : c = u * s ∧ d = s⁻¹
    · rw [if_neg h1, if_pos h2, if_pos]
      rw [h2.1, h2.2, mul_inv_cancel_right, Sym2.eq_swap]
    · rw [if_neg h1, if_neg h2, if_neg]
      rw [Sym2.eq_iff]
      rintro (⟨h3, h4⟩ | ⟨h3, h4⟩)
      · apply h1
        refine ⟨h3, ?_⟩
        rw [h3] at h4
        exact mul_left_cancel h4
      · apply h2
        refine ⟨h3, ?_⟩
        rw [h3, mul_assoc] at h4
        have h5 : s * d = 1 := by simpa using h4
        exact eq_inv_of_mul_eq_one_right h5

omit [DecidableEq Γ] in
lemma sum_count_edgesL [DecidableEq Γ] (u s : Γ) (hs : s ≠ 1) (ds : List Γ) :
    ∑ c : Γ, (edgesL c ds).count s(u, u * s) = pc s ds := by
  induction ds with
  | nil => simp [edgesL, pc]
  | cons d ds ih =>
    have h1 : ∑ c : Γ, (edgesL (c * d) ds).count s(u, u * s) =
        ∑ c : Γ, (edgesL c ds).count s(u, u * s) :=
      Fintype.sum_equiv (Equiv.mulRight d) (fun c => (edgesL (c * d) ds).count s(u, u * s))
        (fun c => (edgesL c ds).count s(u, u * s)) (fun c => rfl)
    have h2 : ∑ c : Γ, (if s(c, c * d) = s(u, u * s) then 1 else 0 : ℕ) =
        (if d = s then 1 else 0) + (if d = s⁻¹ then 1 else 0) := by
      rw [Finset.sum_congr rfl (fun c _ => ind_sym2 u s d c hs), Finset.sum_add_distrib]
      congr 1
      · by_cases hd : d = s <;> simp [hd]
      · by_cases hd : d = s⁻¹ <;> simp [hd]
    simp only [edgesL, List.count_cons, beq_iff_eq, Finset.sum_add_distrib, h1, ih, h2]
    simp only [pc, List.count_cons, beq_iff_eq]
    omega

/-- step lists of Hamiltonian paths from `1` with labels in `S` whose paired counts realise `γ` -/
def Real : Set (Γ → ℚ) :=
  {γ | ∃ ds : List Γ, (∀ d ∈ ds, d ∈ S) ∧ (verts 1 ds).Nodup ∧ (∀ g, g ∈ verts 1 ds) ∧
    ∀ d ∈ S, (pc d ds : ℚ) = γ d + γ d⁻¹}

include hG in
/-- **Assembly.** A rational convex combination of realisable vectors whose paired values are a
positive constant on `S` gives the Fair Traversal conclusion. -/
theorem assemble (x : Γ → ℚ) (hx : x ∈ convexHull ℚ (Real S)) (C : ℚ) (hC : 0 < C)
    (hxs : ∀ s ∈ S, x s + x s⁻¹ = C) (s0 : Γ) (hs0 : s0 ∈ S) :
    ∃ (r k : ℕ), 0 < r ∧ 0 < k ∧
      ∃ (a b : Fin r → Γ) (P : ∀ i, G.Walk (a i) (b i)),
        (∀ i, (P i).IsHamiltonian) ∧
        ∀ e ∈ G.edgeSet, (Finset.univ.filter fun i => e ∈ (P i).edges).card = k := by
  classical
  obtain ⟨ι, hιf, w, z, hw0, hw1, hz, hsum⟩ := mem_convexHull_iff_exists_fintype.1 hx
  have hz' : ∀ i, ∃ ds : List Γ, (∀ d ∈ ds, d ∈ S) ∧ (verts 1 ds).Nodup ∧
      (∀ g, g ∈ verts 1 ds) ∧ ∀ d ∈ S, (pc d ds : ℚ) = z i d + z i d⁻¹ := hz
  choose ds hdsS hdsN hdsA hdsC using hz'
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
  let J := Σ i : ι, Fin (m i) × Γ
  let eqv := Fintype.equivFin J
  let W : (j : J) → Σ b, G.Walk j.2.2 b := fun j => walkOf S G hG j.2.2 (ds j.1) (hdsS j.1)
  have hWsupp : ∀ j, (W j).2.support = (verts 1 (ds j.1)).map (j.2.2 * ·) := by
    intro j; simp only [W]; rw [walkOf_support, verts_eq]
  have hWnd : ∀ j, (W j).2.support.Nodup := by
    intro j; rw [hWsupp]; exact (hdsN j.1).map (mul_right_injective _)
  have hWham : ∀ j, (W j).2.IsHamiltonian := by
    intro j g
    apply List.count_eq_one_of_mem (hWnd j)
    rw [hWsupp, List.mem_map]
    exact ⟨j.2.2⁻¹ * g, hdsA _ _, by group⟩
  have hWend : ∀ j e, (if e ∈ (W j).2.edges then 1 else 0 : ℕ) =
      (edgesL j.2.2 (ds j.1)).count e := by
    intro j e
    have hnd := (SimpleGraph.Walk.IsPath.mk' (hWnd j)).isTrail.edges_nodup
    have hWe : (W j).2.edges = edgesL j.2.2 (ds j.1) := walkOf_edges S G hG _ _ _
    rw [← hWe]
    split_ifs with h
    · exact (List.count_eq_one_of_mem hnd h).symm
    · exact (List.count_eq_zero_of_not_mem h).symm
  have hcnt : ∀ u s : Γ, s ∈ S →
      ((Finset.univ.filter fun t : Fin (Fintype.card J) =>
          s(u, u * s) ∈ (W (eqv.symm t)).2.edges).card : ℚ) = D * C := by
    intro u s hs
    have hs1 : s ≠ 1 := fun h => one_not_mem_of S G hG (h ▸ hs)
    rw [Finset.card_filter,
      Equiv.sum_comp eqv.symm (fun j => if s(u, u * s) ∈ (W j).2.edges then 1 else 0)]
    simp only [hWend]
    rw [Fintype.sum_sigma]
    simp only [Fintype.sum_prod_type, sum_count_edgesL u s hs1, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    push_cast
    simp only [fun i => hdsC i s hs, hm]
    have h1 := congrFun hsum s
    have h2 := congrFun hsum s⁻¹
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h1 h2
    rw [show (∑ i, (D : ℚ) * w i * (z i s + z i s⁻¹)) =
        D * (∑ i, w i * z i s) + D * (∑ i, w i * z i s⁻¹) by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun i _ => by ring), h1, h2, ← mul_add, hxs s hs]
  obtain ⟨k, hk⟩ : ∃ k, k = (Finset.univ.filter fun t : Fin (Fintype.card J) =>
      s((1 : Γ), 1 * s0) ∈ (W (eqv.symm t)).2.edges).card := ⟨_, rfl⟩
  have hkq : (k : ℚ) = D * C := by rw [hk]; exact hcnt 1 s0 hs0
  have hkpos : 0 < k := by
    have hD' : (0 : ℚ) < D := by exact_mod_cast hDpos
    have : (0 : ℚ) < k := by rw [hkq]; exact mul_pos hD' hC
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
  have hb : s(a, b) = s(a, a * (a⁻¹ * b)) := by congr 1; group
  rw [hb]
  exact_mod_cast (hcnt a (a⁻¹ * b) he).trans hkq.symm

include hG in
/-- In a connected Cayley graph, a set containing `1` and closed under right multiplication by `S`
is everything. -/
lemma all_of_connected (hc : G.Connected) (X : Γ → Prop) (h1 : X 1)
    (hX : ∀ x s, X x → s ∈ S → X (x * s)) : ∀ g, X g := by
  intro g
  obtain ⟨p⟩ := hc.preconnected 1 g
  suffices h : ∀ u v (p : G.Walk u v), X u → X v from h 1 g p h1
  intro u v p
  induction p with
  | nil => exact id
  | @cons u v w h p ih =>
    intro hu
    apply ih
    have hs := (hG u v).1 h
    have := hX u _ hu hs
    rwa [mul_inv_cancel_left] at this

end Graph

/-- Transfer along a labelling `e : V ≃ Γ` with `G.Adj u v ↔ (e u)⁻¹ * e v ∈ S`. -/
theorem transfer {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    {Γ : Type} [Group Γ] [Fintype Γ] [DecidableEq Γ] (e : V ≃ Γ) (S : Finset Γ)
    (hG : ∀ u v, G.Adj u v ↔ (e u)⁻¹ * e v ∈ S)
    (H : ∀ G' : SimpleGraph Γ, (∀ x y, G'.Adj x y ↔ x⁻¹ * y ∈ S) → G'.Connected →
      ∃ (r k : ℕ), 0 < r ∧ 0 < k ∧
        ∃ (a b : Fin r → Γ) (P : ∀ i, G'.Walk (a i) (b i)),
          (∀ i, (P i).IsHamiltonian) ∧
          ∀ e ∈ G'.edgeSet, (Finset.univ.filter fun i => e ∈ (P i).edges).card = k)
    (hc : G.Connected) :
    ∃ (r k : ℕ), 0 < r ∧ 0 < k ∧
      ∃ (a b : Fin r → V) (P : ∀ i, G.Walk (a i) (b i)),
        (∀ i, (P i).IsHamiltonian) ∧
        ∀ e' ∈ G.edgeSet, (Finset.univ.filter fun i => e' ∈ (P i).edges).card = k := by
  classical
  let G' : SimpleGraph Γ := G.comap e.symm
  have hG' : ∀ a b, G'.Adj a b ↔ a⁻¹ * b ∈ S := by
    intro a b
    simp only [G', SimpleGraph.comap_adj, hG, Equiv.apply_symm_apply]
  let φ : G' ≃g G := { toEquiv := e.symm, map_rel_iff' := by intro a b; rfl }
  have hc' : G'.Connected := φ.connected_iff.2 hc
  obtain ⟨r, k, hr, hk, a, b, P, hP, hcnt⟩ := H G' hG' hc'
  refine ⟨r, k, hr, hk, fun i => φ (a i), fun i => φ (b i),
    fun i => (P i).map φ.toHom, fun i => (hP i).map (f := φ.toHom) φ.bijective, ?_⟩
  intro e' he'
  have he'' : Sym2.map φ.symm e' ∈ G'.edgeSet :=
    (SimpleGraph.Iso.map_mem_edgeSet_iff φ.symm).2 he'
  rw [← hcnt _ he'']
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, SimpleGraph.Walk.edges_map]
  have hinj : Function.Injective (Sym2.map (φ.toHom : Γ → V)) := Sym2.map.injective φ.injective
  have hback : Sym2.map (φ.toHom : Γ → V) (Sym2.map φ.symm e') = e' := by
    rw [Sym2.map_map]
    have hid : ((φ.toHom : Γ → V) ∘ φ.symm) = id := by funext x; simp
    rw [hid, Sym2.map_id]
    rfl
  conv_lhs => rw [← hback]
  exact List.mem_map_of_injective hinj

end FTDih

-- ===== DihCons.lean =====

/-!
# Constructions for Theorem 7: realisable greedy vectors in Cayley graphs of `Dih A`

Vertex sets are "type sets" `XP hb K b₁ = K × {0} ∪ (K + b₁) × {1}` (second part only if `hb`).
Snakes: `dsnk` (directed: blocks joined by a fixed step) and `asnk` (alternating block / reversed
block). Steps S1–S4 of FT-DIHEDRAL.md §3: first reflection, further reflection (reflection end),
rotation (rotation end), rotation (reflection end). `real1` / `real2`: for every ordering `L` of
`S`, the greedy vector of `vD` along "rotations first" / "reflections first" is realised by a
Hamiltonian path.
-/

open Finset

namespace FTDih

section Snakes
variable {Γ : Type} [Group Γ] [DecidableEq Γ]

/-- directed snake: `t + 1` copies of `ds` joined by `c` -/
def dsnk (ds : List Γ) (c : Γ) : ℕ → List Γ
  | 0 => ds
  | t + 1 => dsnk ds c t ++ c :: ds

lemma prod_dsnk (ds : List Γ) (c : Γ) (t : ℕ) :
    (dsnk ds c t).prod = (ds.prod * c) ^ t * ds.prod := by
  induction t with
  | zero => simp [dsnk]
  | succ t ih => rw [dsnk, List.prod_append, List.prod_cons, ih, pow_succ]; simp only [mul_assoc]

lemma verts_dsnk (ds : List Γ) (c : Γ) (t : ℕ) :
    verts 1 (dsnk ds c t) =
      (List.range (t + 1)).flatMap (fun i => (verts 1 ds).map ((ds.prod * c) ^ i * ·)) := by
  induction t with
  | zero => simp [dsnk]
  | succ t ih =>
    rw [dsnk, verts_append, ih, prod_dsnk, List.range_succ (n := t + 1), List.flatMap_append]
    congr 1
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    rw [verts_eq, show 1 * ((ds.prod * c) ^ t * ds.prod) * c = (ds.prod * c) ^ (t + 1) by
      rw [pow_succ]; simp only [one_mul, mul_assoc]]

lemma pc_dsnk (d : Γ) (ds : List Γ) (c : Γ) (t : ℕ) :
    pc d (dsnk ds c t) = (t + 1) * pc d ds + t * pc d [c] := by
  induction t with
  | zero => simp [dsnk]
  | succ t ih => rw [dsnk, pc_append, ih]; ring

lemma mem_dsnk {S : Finset Γ} (ds : List Γ) (hds : ∀ d ∈ ds, d ∈ S) (c : Γ) (hc : c ∈ S) (t : ℕ) :
    ∀ d ∈ dsnk ds c t, d ∈ S := by
  induction t with
  | zero => simpa [dsnk] using hds
  | succ t ih =>
    intro d hd
    simp only [dsnk, List.mem_append, List.mem_cons] at hd
    rcases hd with hd | rfl | hd
    · exact ih d hd
    · exact hc
    · exact hds d hd

/-- alternating snake: block, join `c₁`, reversed block, join `c₂`, block, ... -/
def asnk (ds : List Γ) (c₁ c₂ : Γ) : ℕ → List Γ
  | 0 => ds
  | t + 1 => asnk ds c₁ c₂ t ++ (if Even t then c₁ else c₂) :: (if Even t then rev ds else ds)

lemma asnk_spec (ds : List Γ) (c₁ w : Γ) (hw : ds.prod * c₁ * ds.prod⁻¹ = w) (t : ℕ) :
    (asnk ds c₁ w t).prod = (if Even t then w ^ t * ds.prod else w ^ t) ∧
    verts 1 (asnk ds c₁ w t) = (List.range (t + 1)).flatMap
      (fun i => (if Even i then verts 1 ds else (verts 1 ds).reverse).map (w ^ i * ·)) := by
  have hw' : ds.prod * c₁ = w * ds.prod := by rw [← hw]; group
  induction t with
  | zero => simp [asnk]
  | succ t ih =>
    obtain ⟨ih1, ih2⟩ := ih
    rw [List.range_succ (n := t + 1), List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
      List.append_nil, asnk]
    beta_reduce
    by_cases ht : Even t
    · have ht1 : ¬ Even (t + 1) := by rw [Nat.even_add_one]; exact not_not.2 ht
      rw [if_pos ht] at ih1
      rw [if_pos ht, if_pos ht, if_neg ht1, if_neg ht1]
      refine ⟨?_, ?_⟩
      · rw [List.prod_append, List.prod_cons, prod_rev, ih1, mul_assoc, ← mul_assoc ds.prod, hw,
          pow_succ]
      · rw [verts_append, ih2, ih1]
        congr 1
        rw [show 1 * (w ^ t * ds.prod) * c₁ = w ^ (t + 1) * ds.prod by
          rw [one_mul, mul_assoc, hw', ← mul_assoc, pow_succ], verts_rev, verts_eq (w ^ (t + 1)) ds]
        simp [List.map_reverse]
    · have ht1 : Even (t + 1) := by rw [Nat.even_add_one]; exact ht
      rw [if_neg ht] at ih1
      rw [if_neg ht, if_neg ht, if_pos ht1, if_pos ht1]
      refine ⟨?_, ?_⟩
      · rw [List.prod_append, List.prod_cons, ih1, pow_succ, mul_assoc]
      · rw [verts_append, ih2, ih1]
        congr 1
        rw [show 1 * w ^ t * w = w ^ (t + 1) by rw [one_mul, pow_succ], verts_eq (w ^ (t + 1)) ds]

lemma pc_asnk (d : Γ) (ds : List Γ) (c₁ c₂ : Γ) (hc : ∀ d, pc d [c₁] = pc d [c₂]) (t : ℕ) :
    pc d (asnk ds c₁ c₂ t) = (t + 1) * pc d ds + t * pc d [c₂] := by
  induction t with
  | zero => simp [asnk]
  | succ t ih =>
    rw [asnk, pc_append, ih]
    by_cases ht : Even t
    · rw [if_pos ht, if_pos ht, pc_rev, hc]; ring
    · rw [if_neg ht, if_neg ht]; ring

lemma mem_asnk {S : Finset Γ} (hinv : ∀ s ∈ S, s⁻¹ ∈ S) (ds : List Γ) (hds : ∀ d ∈ ds, d ∈ S)
    (c₁ c₂ : Γ) (hc₁ : c₁ ∈ S) (hc₂ : c₂ ∈ S) (t : ℕ) : ∀ d ∈ asnk ds c₁ c₂ t, d ∈ S := by
  induction t with
  | zero => simpa [asnk] using hds
  | succ t ih =>
    intro d hd
    simp only [asnk, List.mem_append, List.mem_cons] at hd
    rcases hd with hd | hd | hd
    · exact ih d hd
    · split_ifs at hd <;> (subst hd; assumption)
    · split_ifs at hd
      · exact mem_rev hinv ds hds d hd
      · exact hds d hd

lemma mem_map_mul (g x : Γ) (V : List Γ) : x ∈ V.map (g * ·) ↔ g⁻¹ * x ∈ V := by
  constructor
  · intro h
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 h
    simpa using hy
  · intro h
    exact List.mem_map.2 ⟨g⁻¹ * x, h, by group⟩

lemma prod_mem_verts (x : Γ) (ds : List Γ) : x * ds.prod ∈ verts x ds := by
  induction ds generalizing x with
  | nil => simp
  | cons d ds ih =>
    simp only [verts_cons, List.prod_cons, List.mem_cons]
    right; rw [← mul_assoc]; exact ih (x * d)

end Snakes

section Blocks
variable {A : Type} [AddCommGroup A] [Fintype A] [DecidableEq A]

lemma zq_mem (K : AddSubgroup A) (δ a : A) :
    a ∈ K ⊔ AddSubgroup.zmultiples δ ↔ ∃ i < addOrderOf ((δ : A ⧸ K)), a - i • δ ∈ K := by
  constructor
  · intro ha
    obtain ⟨k, hk, z, hz, rfl⟩ := AddSubgroup.mem_sup.1 ha
    obtain ⟨j, rfl⟩ := AddSubgroup.mem_zmultiples_iff.1 hz
    obtain ⟨q, hq⟩ : ∃ q, q = addOrderOf ((δ : A ⧸ K)) := ⟨_, rfl⟩
    have hq0 : 0 < q := hq ▸ addOrderOf_pos _
    have hm0 : 0 ≤ j % (q : ℤ) := Int.emod_nonneg j (by exact_mod_cast hq0.ne')
    have hm1 : j % (q : ℤ) < q := Int.emod_lt_of_pos j (by exact_mod_cast hq0)
    obtain ⟨i, hi⟩ : ∃ i : ℕ, (i : ℤ) = j % (q : ℤ) := ⟨_, Int.toNat_of_nonneg hm0⟩
    refine ⟨i, by rw [← hq]; omega, ?_⟩
    rw [← QuotientAddGroup.eq_zero_iff]
    rw [QuotientAddGroup.mk_sub, QuotientAddGroup.mk_add, (QuotientAddGroup.eq_zero_iff k).2 hk,
      zero_add, QuotientAddGroup.mk_nsmul, QuotientAddGroup.mk_zsmul, ← natCast_zsmul, hi, hq,
      mod_addOrderOf_zsmul, sub_self]
  · rintro ⟨i, -, hi⟩
    rw [show a = (a - i • δ) + i • δ by abel]
    exact AddSubgroup.add_mem_sup hi (AddSubgroup.nsmul_mem _ (AddSubgroup.mem_zmultiples δ) i)

lemma zq_inj (K : AddSubgroup A) (δ : A) (i j : ℕ) (hi : i < addOrderOf ((δ : A ⧸ K)))
    (hj : j < addOrderOf ((δ : A ⧸ K))) (h : i • δ - j • δ ∈ K) : i = j := by
  have h1 : ((i • δ - j • δ : A) : A ⧸ K) = 0 := (QuotientAddGroup.eq_zero_iff _).2 h
  rw [QuotientAddGroup.mk_sub, QuotientAddGroup.mk_nsmul, QuotientAddGroup.mk_nsmul,
    sub_eq_zero] at h1
  exact nsmul_injOn_Iio_addOrderOf hi hj h1

/-- the type set `K × {0} ∪ (K + b₁) × {1}` (second part only if `hb`) -/
def XP (hb : Bool) (K : AddSubgroup A) (b₁ : A) (x : Dih A) : Prop :=
  if x.s then (hb = true ∧ x.r - b₁ ∈ K) else x.r ∈ K

lemma xp_rot_mul (hb : Bool) (K : AddSubgroup A) (b₁ c : A) (x : Dih A) :
    XP hb K b₁ (rot c * x) ↔ (if x.s then (hb = true ∧ (x.r - b₁) + c ∈ K) else x.r + c ∈ K) := by
  rcases x with ⟨a, i⟩
  have e1 : rot c * (⟨a, i⟩ : Dih A) = ⟨a + c, i⟩ := by
    ext
    · simp [add_comm]
    · simp
  rw [e1]
  cases i
  · simp [XP]
  · simp only [XP, if_true]
    rw [show a + c - b₁ = a - b₁ + c by abel]

lemma blocks (hb : Bool) (K : AddSubgroup A) (b₁ δ : A) (V : List (Dih A)) (hV : V.Nodup)
    (hVm : ∀ x, x ∈ V ↔ XP hb K b₁ x) (f : ℕ → List (Dih A))
    (hf : ∀ i, f i = V.map (rot (i • δ) * ·) ∨ f i = V.reverse.map (rot (i • δ) * ·)) :
    ((List.range (addOrderOf ((δ : A ⧸ K)))).flatMap f).Nodup ∧
    (∀ x, x ∈ (List.range (addOrderOf ((δ : A ⧸ K)))).flatMap f ↔
      XP hb (K ⊔ AddSubgroup.zmultiples δ) b₁ x) ∧
    ((List.range (addOrderOf ((δ : A ⧸ K)))).flatMap f).length =
      addOrderOf ((δ : A ⧸ K)) * V.length := by
  set q := addOrderOf ((δ : A ⧸ K)) with hq
  have hmemf : ∀ i x, x ∈ f i ↔ XP hb K b₁ (rot (-(i • δ)) * x) := by
    intro i x
    rcases hf i with h | h <;> rw [h, mem_map_mul, rot_inv]
    · exact hVm _
    · rw [List.mem_reverse]; exact hVm _
  have hmemf' : ∀ i x, x ∈ f i ↔
      (if x.s then (hb = true ∧ (x.r - b₁) - i • δ ∈ K) else x.r - i • δ ∈ K) := by
    intro i x
    rw [hmemf, xp_rot_mul]
    simp only [← sub_eq_add_neg]
  refine ⟨?_, ?_, ?_⟩
  · rw [List.nodup_flatMap]
    refine ⟨fun i _ => ?_, ?_⟩
    · rcases hf i with h | h <;> rw [h]
      · exact hV.map (mul_right_injective _)
      · exact (List.nodup_reverse.2 hV).map (mul_right_injective _)
    · refine List.Nodup.pairwise_of_forall_ne List.nodup_range ?_
      intro i hi j hj hij
      rw [Function.onFun, List.disjoint_left]
      intro x hx1 hx2
      rw [hmemf'] at hx1 hx2
      apply hij
      refine zq_inj K δ i j (List.mem_range.1 hi) (List.mem_range.1 hj) ?_
      split_ifs at hx1 hx2
      · have := K.sub_mem hx2.2 hx1.2
        rw [show (x.r - b₁ - j • δ) - (x.r - b₁ - i • δ) = i • δ - j • δ by abel] at this
        exact this
      · have := K.sub_mem hx2 hx1
        rw [show (x.r - j • δ) - (x.r - i • δ) = i • δ - j • δ by abel] at this
        exact this
  · intro x
    rw [List.mem_flatMap]
    simp only [List.mem_range, hmemf', XP]
    split_ifs
    · constructor
      · rintro ⟨i, hi, hb', h⟩; exact ⟨hb', (zq_mem K δ _).2 ⟨i, hi, h⟩⟩
      · rintro ⟨hb', h⟩
        obtain ⟨i, hi, h⟩ := (zq_mem K δ _).1 h
        exact ⟨i, hi, hb', h⟩
    · constructor
      · rintro ⟨i, hi, h⟩; exact (zq_mem K δ _).2 ⟨i, hi, h⟩
      · intro h; exact (zq_mem K δ _).1 h
  · rw [List.length_flatMap]
    have : ∀ i, (f i).length = V.length := by
      intro i; rcases hf i with h | h <;> rw [h] <;> simp
    simp only [this, List.map_const', List.length_range, List.sum_replicate, smul_eq_mul]

end Blocks

section Problem
variable {A : Type} [AddCommGroup A] [Fintype A] [DecidableEq A]

/-- does `T` contain a reflection -/
def hasRef (T : Finset (Dih A)) : Bool := decide (∃ x ∈ T, x.s = true)
/-- rotation part (as elements of `A`) -/
def rotS (T : Finset (Dih A)) : Set A := {a | rot a ∈ T}
/-- reflection part -/
def refS (T : Finset (Dih A)) : Set A := {b | ref b ∈ T}
/-- generators of `⟨T⟩ ∩ A`: rotations and differences of reflections -/
def genS (T : Finset (Dih A)) : Set A := rotS T ∪ Set.image2 (· - ·) (refS T) (refS T)
/-- `⟨T⟩ ∩ A` -/
def KT (T : Finset (Dih A)) : AddSubgroup A := AddSubgroup.closure (genS T)
/-- `|⟨T⟩|` -/
noncomputable def sz (T : Finset (Dih A)) : ℕ := (if hasRef T then 2 else 1) * Nat.card (KT T)
/-- the game `v(T) = n - n/|⟨T⟩|` (`n = |Dih A|`) -/
noncomputable def vD (T : Finset (Dih A)) : ℚ :=
  (Fintype.card (Dih A) : ℚ) - Fintype.card (Dih A) / sz T
/-- the vertex set `⟨T⟩` described as a type set (`b₁` a reflection of `T`, if any) -/
def PT (T : Finset (Dih A)) (b₁ : A) (x : Dih A) : Prop := XP (hasRef T) (KT T) b₁ x

@[simp] lemma xp_rot (hb : Bool) (K : AddSubgroup A) (b₁ y : A) :
    XP hb K b₁ (rot y) ↔ y ∈ K := by simp [XP]

@[simp] lemma xp_ref (hb : Bool) (K : AddSubgroup A) (b₁ y : A) :
    XP hb K b₁ (ref y) ↔ (hb = true ∧ y - b₁ ∈ K) := by simp [XP]

lemma pt_rot (T : Finset (Dih A)) (b₁ y : A) : PT T b₁ (rot y) ↔ y ∈ KT T := by simp [PT]

lemma pt_ref (T : Finset (Dih A)) (b₁ y : A) :
    PT T b₁ (ref y) ↔ (hasRef T = true ∧ y - b₁ ∈ KT T) := by simp [PT]

lemma hasRef_insert_rot (T : Finset (Dih A)) (r : A) : hasRef (insert (rot r) T) = hasRef T := by
  simp [hasRef, rot]

lemma hasRef_insert_ref (T : Finset (Dih A)) (b : A) : hasRef (insert (ref b) T) = true := by
  simp [hasRef, ref]

lemma hasRef_of_mem (T : Finset (Dih A)) (b : A) (h : ref b ∈ T) : hasRef T = true := by
  simp only [hasRef, decide_eq_true_eq]; exact ⟨ref b, h, rfl⟩

lemma refS_empty_of (T : Finset (Dih A)) (h : hasRef T = false) : refS T = ∅ := by
  ext b
  simp only [refS, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
  intro hb
  rw [hasRef_of_mem T b hb] at h
  exact Bool.noConfusion h

lemma genS_insert_rot (T : Finset (Dih A)) (r : A) :
    genS (insert (rot r) T) = insert r (genS T) := by
  have h1 : rotS (insert (rot r) T) = insert r (rotS T) := by
    ext a; simp [rotS, rot_injective.eq_iff]
  have h2 : refS (insert (rot r) T) = refS T := by
    ext a; simp [refS, (rot_ne_ref r a).symm]
  rw [genS, genS, h1, h2, Set.insert_union]

lemma KT_insert_rot (T : Finset (Dih A)) (r : A) :
    KT (insert (rot r) T) = KT T ⊔ AddSubgroup.zmultiples r := by
  rw [KT, KT, genS_insert_rot, Set.insert_eq, AddSubgroup.closure_union,
    ← AddSubgroup.zmultiples_eq_closure, sup_comm]

lemma KT_empty : KT (∅ : Finset (Dih A)) = ⊥ := by
  have : genS (∅ : Finset (Dih A)) = ∅ := by
    ext a; simp [genS, rotS, refS]
  rw [KT, this, AddSubgroup.closure_empty]

lemma KT_insert_ref_first (T : Finset (Dih A)) (b : A) (h : hasRef T = false) :
    KT (insert (ref b) T) = KT T := by
  have h1 : rotS (insert (ref b) T) = rotS T := by
    ext a; simp [rotS, rot_ne_ref a b]
  have h2 : refS (insert (ref b) T) = {b} := by
    ext a; simp only [refS, Set.mem_setOf_eq, Finset.mem_insert, ref_injective.eq_iff,
      Set.mem_singleton_iff]
    constructor
    · rintro (h' | h')
      · exact h'
      · rw [hasRef_of_mem T a h'] at h; exact Bool.noConfusion h
    · intro h'; exact Or.inl h'
  rw [KT, KT, genS, genS, h1, h2, refS_empty_of T h, Set.image2_singleton, sub_self,
    Set.image2_empty_left, Set.union_empty]
  apply le_antisymm
  · rw [AddSubgroup.closure_le]
    intro a ha
    rcases ha with ha | ha
    · exact AddSubgroup.subset_closure ha
    · rw [Set.mem_singleton_iff.1 ha]; exact zero_mem _
  · exact AddSubgroup.closure_mono Set.subset_union_left

lemma KT_insert_ref (T : Finset (Dih A)) (b b₁ w : A) (hb₁ : ref b₁ ∈ T) (hw : w - b₁ ∈ KT T) :
    KT (insert (ref b) T) = KT T ⊔ AddSubgroup.zmultiples (w - b) := by
  have h1 : rotS (insert (ref b) T) = rotS T := by
    ext a; simp [rotS, rot_ne_ref a b]
  have h2 : refS (insert (ref b) T) = insert b (refS T) := by
    ext a; simp [refS, ref_injective.eq_iff]
  have hb₁' : b₁ ∈ refS T := hb₁
  have hsub : genS T ⊆ genS (insert (ref b) T) := by
    rw [genS, genS, h1, h2]
    exact Set.union_subset_union_right _ (Set.image2_subset (Set.subset_insert _ _)
      (Set.subset_insert _ _))
  have hdiff : ∀ x ∈ refS T, ∀ y ∈ refS T, x - y ∈ KT T := fun x hx y hy =>
    AddSubgroup.subset_closure (Or.inr ⟨x, hx, y, hy, rfl⟩)
  apply le_antisymm
  · rw [KT, AddSubgroup.closure_le]
    intro a ha
    rw [genS, h1, h2] at ha
    have hK : ∀ z ∈ KT T, z ∈ (KT T ⊔ AddSubgroup.zmultiples (w - b) : AddSubgroup A) :=
      fun z hz => AddSubgroup.mem_sup_left hz
    have hZ : w - b ∈ (KT T ⊔ AddSubgroup.zmultiples (w - b) : AddSubgroup A) :=
      AddSubgroup.mem_sup_right (AddSubgroup.mem_zmultiples _)
    rcases ha with ha | ⟨x, hx, y, hy, rfl⟩
    · exact hK _ (AddSubgroup.subset_closure (Or.inl ha))
    · have key : ∀ x ∈ refS T, x - b ∈ (KT T ⊔ AddSubgroup.zmultiples (w - b) : AddSubgroup A) := by
        intro x hx
        rw [show x - b = ((x - b₁) - (w - b₁)) + (w - b) by abel]
        exact add_mem (hK _ (sub_mem (hdiff x hx b₁ hb₁') hw)) hZ
      show x - y ∈ _
      rcases Set.mem_insert_iff.1 hx with hxb | hx' <;>
        rcases Set.mem_insert_iff.1 hy with hyb | hy'
      · rw [hxb, hyb, sub_self]; exact zero_mem _
      · rw [hxb, show b - y = -(y - b) by abel]; exact neg_mem (key y hy')
      · rw [hyb]; exact key x hx'
      · exact hK _ (hdiff x hx' y hy')
  · apply sup_le (AddSubgroup.closure_mono hsub)
    rw [AddSubgroup.zmultiples_le]
    rw [show w - b = (w - b₁) + (b₁ - b) by abel]
    refine add_mem (AddSubgroup.closure_mono hsub hw) (AddSubgroup.subset_closure ?_)
    rw [genS, h1, h2]
    exact Or.inr ⟨b₁, Set.mem_insert_of_mem _ hb₁', b, Set.mem_insert _ _, rfl⟩

variable (S : Finset (Dih A))

/-- invariant: a Hamiltonian path of `⟨T⟩` from `1`, labels in `S`, counts `γ` (scaled) -/
def Inv (T : Finset (Dih A)) (b₁ : A) (ds : List (Dih A)) (γ : Dih A → ℚ) : Prop :=
  (∀ d ∈ ds, d ∈ S) ∧ (verts 1 ds).Nodup ∧ (∀ x, x ∈ verts 1 ds ↔ PT T b₁ x) ∧
    ∀ d, (pc d ds : ℚ) * Fintype.card (Dih A) = (verts 1 ds).length * (γ d + γ d⁻¹)

lemma len_of_xp (hb : Bool) (K : AddSubgroup A) (b₁ : A) (V : List (Dih A)) (hV : V.Nodup)
    (hm : ∀ x, x ∈ V ↔ XP hb K b₁ x) : V.length = (if hb then 2 else 1) * Nat.card K := by
  have e0 : (V.filter (fun x => !x.s)).length = Nat.card K := by
    have hnd : ((V.filter (fun x => !x.s)).map Dih.r).Nodup := by
      refine List.Nodup.map_on ?_ (hV.filter _)
      intro x hx y hy hxy
      have hx' := (List.mem_filter.1 hx).2
      have hy' := (List.mem_filter.1 hy).2
      ext
      · exact hxy
      · simp only [Bool.not_eq_true'] at hx' hy'; rw [hx', hy']
    rw [← List.length_map (f := Dih.r)]
    refine (FTAbelian.card_of_list K _ hnd ?_).symm
    intro a
    simp only [List.mem_map, List.mem_filter]
    constructor
    · rintro ⟨x, ⟨hx, hs⟩, rfl⟩
      have := (hm x).1 hx
      simp only [Bool.not_eq_true'] at hs
      simpa [XP, hs] using this
    · intro ha
      exact ⟨rot a, ⟨(hm _).2 (by simpa [XP] using ha), by simp⟩, rfl⟩
  have e1 : (V.filter (fun x => x.s)).length = (if hb then 1 else 0) * Nat.card K := by
    cases hb
    · simp only [Bool.false_eq_true, if_false, zero_mul, List.length_eq_zero_iff]
      rw [List.filter_eq_nil_iff]
      intro x hx hs
      have := (hm x).1 hx
      simp [XP, hs] at this
    · simp only [if_true, one_mul]
      have hnd : ((V.filter (fun x => x.s)).map (fun x => x.r - b₁)).Nodup := by
        refine List.Nodup.map_on ?_ (hV.filter _)
        intro x hx y hy hxy
        have hx' := (List.mem_filter.1 hx).2
        have hy' := (List.mem_filter.1 hy).2
        ext
        · exact sub_left_injective hxy
        · rw [hx', hy']
      rw [← List.length_map (f := fun x => x.r - b₁)]
      refine (FTAbelian.card_of_list K _ hnd ?_).symm
      intro a
      simp only [List.mem_map, List.mem_filter]
      constructor
      · rintro ⟨x, ⟨hx, hs⟩, rfl⟩
        have := (hm x).1 hx
        simpa [XP, hs] using this
      · intro ha
        exact ⟨ref (a + b₁), ⟨(hm _).2 (by simpa [XP] using ha), by simp⟩, by simp⟩
  have hsplit := List.length_eq_length_filter_add (l := V) (fun x => x.s)
  rw [hsplit, e1]
  have : (List.filter (fun x => !x.s) V).length = Nat.card K := e0
  rw [this]
  cases hb <;> simp <;> ring

lemma vD_eq (T : Finset (Dih A)) (b₁ : A) (V : List (Dih A)) (hV : V.Nodup)
    (hm : ∀ x, x ∈ V ↔ PT T b₁ x) :
    vD T = (Fintype.card (Dih A) : ℚ) - Fintype.card (Dih A) / V.length := by
  rw [vD, sz, len_of_xp _ _ _ V hV hm]

lemma pc_single (d s : Dih A) : (pc d [s] : ℚ) =
    (Pi.single s (1 : ℚ) : Dih A → ℚ) d + (Pi.single s (1 : ℚ) : Dih A → ℚ) d⁻¹ := by
  simp only [pc, List.count_cons, List.count_nil, beq_iff_eq, Pi.single_apply, zero_add]
  by_cases h1 : s = d
  · rw [if_pos h1, if_pos h1.symm]
    by_cases h2 : s = d⁻¹
    · rw [if_pos h2, if_pos h2.symm]; norm_num
    · rw [if_neg h2, if_neg (show ¬ d⁻¹ = s from fun h => h2 h.symm)]; norm_num
  · rw [if_neg h1, if_neg (show ¬ d = s from fun h => h1 h.symm)]
    by_cases h2 : s = d⁻¹
    · rw [if_pos h2, if_pos h2.symm]; norm_num
    · rw [if_neg h2, if_neg (show ¬ d⁻¹ = s from fun h => h2 h.symm)]; norm_num

/-- generic count update -/
lemma inv_update (T : Finset (Dih A)) (b₁ : A) (ds : List (Dih A)) (γ : Dih A → ℚ)
    (h : Inv S T b₁ ds γ) (s : Dih A) (ds' : List (Dih A)) (q : ℕ) (hq : 0 < q)
    (hS' : ∀ d ∈ ds', d ∈ S) (hN : (verts 1 ds').Nodup)
    (hM : ∀ x, x ∈ verts 1 ds' ↔ PT (insert s T) b₁ x)
    (hlen : (verts 1 ds').length = q * (verts 1 ds).length)
    (hpc : ∀ d, pc d ds' = q * pc d ds + (q - 1) * pc d [s]) :
    Inv S (insert s T) b₁ ds' (γ + Pi.single s (vD (insert s T) - vD T)) := by
  obtain ⟨-, hnd, hmem, hcnt⟩ := h
  refine ⟨hS', hN, hM, ?_⟩
  intro d
  have hv1 := vD_eq T b₁ _ hnd hmem
  have hv2 := vD_eq (insert s T) b₁ _ hN hM
  rw [hv1, hv2, hlen, hpc]
  have hL : (0 : ℚ) < (verts 1 ds).length := by
    exact_mod_cast List.length_pos_of_mem (mem_verts_self 1 ds)
  have hqq : (0 : ℚ) < q := by exact_mod_cast hq
  have hc := hcnt d
  have hps := pc_single d s
  simp only [Pi.add_apply]
  rw [show (Pi.single s (((Fintype.card (Dih A) : ℚ) - Fintype.card (Dih A) / ((q * (verts 1 ds).length : ℕ) : ℚ)) -
      ((Fintype.card (Dih A) : ℚ) - Fintype.card (Dih A) / ((verts 1 ds).length : ℚ))) : Dih A → ℚ) =
      (((Fintype.card (Dih A) : ℚ) - Fintype.card (Dih A) / ((q * (verts 1 ds).length : ℕ) : ℚ)) -
      ((Fintype.card (Dih A) : ℚ) - Fintype.card (Dih A) / ((verts 1 ds).length : ℚ))) •
        (Pi.single s (1 : ℚ) : Dih A → ℚ) by rw [← Pi.single_smul, smul_eq_mul, mul_one]]
  simp only [Pi.smul_apply, smul_eq_mul]
  push_cast [Nat.cast_sub (Nat.one_le_iff_ne_zero.2 hq.ne')]
  generalize ((verts 1 ds).length : ℚ) = L at hL hc ⊢
  generalize (Fintype.card (Dih A) : ℚ) = N at hc ⊢
  generalize (Pi.single s (1 : ℚ) : Dih A → ℚ) d = I1 at hps ⊢
  generalize (Pi.single s (1 : ℚ) : Dih A → ℚ) d⁻¹ = I2 at hps ⊢
  rw [hps]
  have hcc : (q : ℚ) * L * (N - N / (q * L) - (N - N / L)) = q * N - N := by
    field_simp; ring
  linear_combination (q : ℚ) * hc - (I1 + I2) * hcc

end Problem

end FTDih

-- ===== DihArith.lean =====

/-!
# The rational inequalities behind the λ-blend (FT-DIHEDRAL.md §4, Lemmas 3–4)

Notation (all rationals): `m = |A|`, `r = |R|`, `f = |F|`, `a = [A : K₀]`, `b = [A : K_F]`,
`Nl = r(2m - b) - f(b - 1)`, `Nb = f(2m - 2a) - r(2a - 1)` (λ = Nl/(Nl+Nb)).
For a rotation set `U` (`u = |U|`, `i = [A : ⟨U⟩]`, `j = [A : ⟨U, K_F⟩]`) condition (R) reads
`Nb·(u(b-1) - r(b-j)) ≤ Nl·(r(2m-2i) - u(2m-2a))`; for a reflection set `W`
(`w = |W|`, `k = [A : ⟨K₀, W-W⟩]`, `l = [A : ⟨W-W⟩]`) condition (F) reads
`Nl·(w(2a-1) - f(2a-k)) ≤ Nb·(f(2m-l) - w(2m-b))`.
-/

namespace FTDih

lemma Nl_pos (m r f a b hF : ℚ) (hr : 1 ≤ r) (hf : 1 ≤ f) (hb : 1 ≤ b) (hF1 : 1 ≤ hF)
    (hbhF : b * hF = m) (hfF : f ≤ hF) : 0 < r * (2 * m - b) - f * (b - 1) := by
  have hb0 : 0 ≤ b := by linarith
  have hbm : b ≤ m := by
    have := mul_le_mul_of_nonneg_left hF1 hb0
    linarith
  have h1 : 0 ≤ (r - 1) * (2 * m - b) := mul_nonneg (by linarith) (by linarith)
  have h2 : f * (b - 1) ≤ hF * (b - 1) := mul_le_mul_of_nonneg_right hfF (by linarith)
  linarith

lemma Nb_nonneg (m r f a hR : ℚ) (hr : 0 ≤ r) (hrR : r ≤ hR - 1) (hf : 1 ≤ f) (ha : 1 ≤ a)
    (hahR : a * hR = m) : 0 ≤ f * (2 * m - 2 * a) - r * (2 * a - 1) := by
  have hR1 : 1 ≤ hR := by linarith
  have ham : a ≤ m := by
    have := mul_le_mul_of_nonneg_left hR1 (by linarith : (0 : ℚ) ≤ a)
    linarith
  have h1 : 0 ≤ (f - 1) * (2 * m - 2 * a) := mul_nonneg (by linarith) (by linarith)
  have h2 : r * (2 * a - 1) ≤ (hR - 1) * (2 * a - 1) := mul_le_mul_of_nonneg_right hrR (by linarith)
  linarith

/-- (R) when `⟨U⟩ = K₀` -/
lemma arithA (m r u a b j Nl Nb : ℚ) (hNl : 0 ≤ Nl) (hNb : 0 ≤ Nb) (hru : u ≤ r) (ha : a ≤ m)
    (hb : 1 ≤ b) (hj : j = 1) :
    Nb * (u * (b - 1) - r * (b - j)) ≤ Nl * (r * (2 * m - 2 * a) - u * (2 * m - 2 * a)) := by
  subst hj
  have h1 : 0 ≤ Nl * ((r - u) * (2 * m - 2 * a)) :=
    mul_nonneg hNl (mul_nonneg (by linarith) (by linarith))
  have h2 : 0 ≤ Nb * ((r - u) * (b - 1)) := mul_nonneg hNb (mul_nonneg (by linarith) (by linarith))
  linarith

set_option maxHeartbeats 1000000 in
/-- (R) when `⟨U⟩ ≠ K₀` (paper Lemma 3) -/
lemma arithB (m r f u a b i j h hF Nl Nb : ℚ)
    (hNl : Nl = r * (2 * m - b) - f * (b - 1)) (hNb : Nb = f * (2 * m - 2 * a) - r * (2 * a - 1))
    (hNl0 : 0 ≤ Nl) (hNb0 : 0 ≤ Nb)
    (hu : 1 ≤ u) (hru : u + 1 ≤ r) (ha : 1 ≤ a) (hb : 1 ≤ b) (hm : 0 < m)
    (hih : i * h = m) (hh : u + 1 ≤ h) (hia : a ≤ i) (hjb : j ≤ b)
    (hbhF : b * hF = m) (hfF : f ≤ hF) (hf : 1 ≤ f)
    (hcase : (b = m ∧ a = 1 ∧ j = i) ∨
      (2 ≤ f ∧ (u + 2 ≤ r ∨ (r = u + 1 ∧ i = 2 * a ∧ (2 * j ≤ b ∨ (j = b ∧ b ≤ 2)))))) :
    Nb * (u * (b - 1) - r * (b - j)) ≤ Nl * (r * (2 * m - 2 * i) - u * (2 * m - 2 * a)) := by
  have hi0 : 0 ≤ i := by linarith
  have hu0 : 0 ≤ u := by linarith
  have hr0 : 0 ≤ r := by linarith
  have ha0 : 0 ≤ a := by linarith
  have hf0 : 0 ≤ f := by linarith
  have hm0 : 0 ≤ m := hm.le
  have hi_le : i * (u + 1) ≤ m := by rw [← hih]; exact mul_le_mul_of_nonneg_left hh hi0
  have hiu : 0 ≤ i * u := mul_nonneg hi0 hu0
  have hua : 0 ≤ u * a := mul_nonneg hu0 ha0
  have e1 : (u + 1) * (2 * m - 2 * i) ≤ r * (2 * m - 2 * i) :=
    mul_le_mul_of_nonneg_right hru (by linarith)
  obtain ⟨D1, hD1def⟩ : ∃ D1, D1 = r * (2 * m - 2 * i) - u * (2 * m - 2 * a) := ⟨_, rfl⟩
  obtain ⟨D2, hD2def⟩ : ∃ D2, D2 = u * (b - 1) - r * (b - j) := ⟨_, rfl⟩
  rw [← hD1def, ← hD2def]
  have hD1 : 0 ≤ D1 := by rw [hD1def]; linarith
  by_cases hD2 : D2 ≤ 0
  · have := mul_nonneg hNl0 hD1
    have := mul_nonpos_of_nonneg_of_nonpos hNb0 hD2
    linarith
  push_neg at hD2
  rcases hcase with ⟨hbm, ha1, hji⟩ | ⟨hf2, hq⟩
  · exfalso
    have : D1 = -2 * D2 := by rw [hD1def, hD2def, hbm, ha1, hji]; ring
    linarith
  have hF2 : 2 ≤ hF := le_trans hf2 hfF
  have hb0 : 0 ≤ b := by linarith
  have hb2 : 2 * b ≤ m := by
    have := mul_le_mul_of_nonneg_left hF2 hb0
    linarith
  have hfb : f * b ≤ m := by
    have := mul_le_mul_of_nonneg_right hfF hb0
    linarith
  have hNl2 : m * (3 * r - 2) ≤ 2 * Nl := by
    have := mul_le_mul_of_nonneg_left hb2 hr0
    rw [hNl]; linarith
  have hNb2 : Nb ≤ 2 * f * m := by
    have := mul_nonneg hf0 ha0
    have := mul_nonneg hr0 (by linarith : (0 : ℚ) ≤ a - 1)
    rw [hNb]; linarith
  have hNbD : Nb * D2 ≤ 2 * f * m * D2 := mul_le_mul_of_nonneg_right hNb2 hD2.le
  have hu1 : 0 < u + 1 := by linarith
  rcases hq with hq2 | ⟨hr1, hi2, hsub⟩
  · -- q ≥ 2
    have hfD : f * D2 ≤ m * u := by
      have h1 : D2 ≤ u * b := by
        have : r * j ≤ r * b := mul_le_mul_of_nonneg_left hjb hr0
        rw [hD2def]; linarith
      have h2 : f * D2 ≤ f * (u * b) := mul_le_mul_of_nonneg_left h1 hf0
      have h3 := mul_le_mul_of_nonneg_right hfb hu0
      linarith
    have hd1 : 2 * m * u * (r - u - 1) ≤ (u + 1) * D1 := by
      have := mul_le_mul_of_nonneg_left hi_le hr0
      have := mul_nonneg hua (by linarith : (0 : ℚ) ≤ u + 1)
      rw [hD1def]; linarith
    have hp : 0 ≤ r - u - 1 := by linarith
    have hpos : 0 ≤ 2 * m * u * (r - u - 1) :=
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hm0) hu0) hp
    have s3 := mul_le_mul hNl2 hd1 hpos (by linarith : 0 ≤ 2 * Nl)
    have s1 : 2 * (u + 1) ≤ (3 * r - 2) * (r - u - 1) := by
      have := mul_le_mul_of_nonneg_left (by linarith : (1 : ℚ) ≤ r - u - 1)
        (by linarith : (0 : ℚ) ≤ 3 * r - 2)
      linarith
    have s4 := mul_le_mul_of_nonneg_left s1
      (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0 : ℚ) ≤ 2) hm0) hm0) hu0)
    have s5 : Nb * D2 ≤ 2 * m * (m * u) := by
      have := mul_le_mul_of_nonneg_left hfD (by linarith : (0 : ℚ) ≤ 2 * m)
      linarith
    have s6 := mul_le_mul_of_nonneg_left s5 hu1.le
    have key : (u + 1) * (Nb * D2) ≤ (u + 1) * (Nl * D1) := by linarith
    exact le_of_mul_le_mul_left key hu1
  · -- q = 1
    have hm2 : 2 * a * (u + 1) ≤ m := by
      have := mul_le_mul_of_nonneg_left hh (by linarith : (0 : ℚ) ≤ 2 * a)
      rw [← hih, hi2]; linarith
    have hd1 : m * u ≤ (u + 1) * D1 := by
      have := mul_le_mul_of_nonneg_right hm2 (by linarith : (0 : ℚ) ≤ u + 2)
      rw [hD1def, hr1, hi2]; linarith
    have hmu : 0 ≤ m * u := mul_nonneg hm0 hu0
    rcases hsub with hj2 | ⟨hjb', hb2'⟩
    · have h2D : 2 * D2 ≤ b * (u - 1) := by
        have := mul_le_mul_of_nonneg_left hj2 hu1.le
        rw [hD2def, hr1]; linarith
      have hfD : 2 * (f * D2) ≤ m * (u - 1) := by
        have h1 := mul_le_mul_of_nonneg_left h2D hf0
        have h3 := mul_le_mul_of_nonneg_right hfb (by linarith : (0 : ℚ) ≤ u - 1)
        linarith
      have s5 : Nb * D2 ≤ m * (m * (u - 1)) := by
        have := mul_le_mul_of_nonneg_left hfD hm0
        linarith
      have s3 := mul_le_mul hNl2 hd1 hmu (by linarith : 0 ≤ 2 * Nl)
      rw [hr1] at s3
      have s6 : 2 * (u + 1) * (u - 1) ≤ (3 * (u + 1) - 2) * u := by nlinarith [sq_nonneg u]
      have s7 := mul_le_mul_of_nonneg_left s6 (mul_nonneg hm0 hm0)
      have s8 := mul_le_mul_of_nonneg_left s5 hu1.le
      have key : (u + 1) * (Nb * D2) ≤ (u + 1) * (Nl * D1) := by linarith
      exact le_of_mul_le_mul_left key hu1
    · have hD2' : D2 = u * (b - 1) := by rw [hD2def, hjb']; ring
      have hm4 : 2 * (u + 1) ≤ m := by
        have := mul_le_mul_of_nonneg_right (by linarith : (2 : ℚ) ≤ 2 * a) hu1.le
        linarith
      have hfb2 : 2 * (f * (b - 1)) ≤ m := by
        have := mul_nonpos_of_nonneg_of_nonpos hf0 (by linarith : b - 2 ≤ 0)
        linarith
      have hNbD' : Nb * D2 ≤ m * m * u := by
        have hub : 0 ≤ u * (b - 1) := by rw [← hD2']; exact hD2.le
        have h1 : Nb * (u * (b - 1)) ≤ 2 * f * m * (u * (b - 1)) :=
          mul_le_mul_of_nonneg_right hNb2 hub
        have h2 := mul_le_mul_of_nonneg_left hfb2 hmu
        rw [hD2']; linarith
      have hNlm : (u + 1) * m ≤ Nl := by
        have h1 : 2 * (m - 2) ≤ (u + 1) * (m - 2) :=
          mul_le_mul_of_nonneg_right (by linarith) (by linarith)
        have h2 : (u + 1) * (2 * m - 2) ≤ (u + 1) * (2 * m - b) :=
          mul_le_mul_of_nonneg_left (by linarith) hu1.le
        rw [hNl, hr1]; linarith
      have s3 : (u + 1) * m * (m * u) ≤ Nl * ((u + 1) * D1) := mul_le_mul hNlm hd1 hmu hNl0
      have s8 := mul_le_mul_of_nonneg_left hNbD' hu1.le
      have key : (u + 1) * (Nb * D2) ≤ (u + 1) * (Nl * D1) := by linarith
      exact le_of_mul_le_mul_left key hu1

set_option maxHeartbeats 1000000 in
/-- (F) for a proper nonempty reflection set (paper Lemma 4) -/
lemma arithF (m r f w a b k l hR Nl Nb : ℚ)
    (hNl : Nl = r * (2 * m - b) - f * (b - 1)) (hNb : Nb = f * (2 * m - 2 * a) - r * (2 * a - 1))
    (hNl0 : 0 ≤ Nl) (hNb0 : 0 ≤ Nb)
    (hw : 1 ≤ w) (hwf : w + 1 ≤ f) (hr : 1 ≤ r) (hrR : r ≤ hR - 1) (hahR : a * hR = m)
    (ha : 1 ≤ a) (hb : 1 ≤ b) (hm : 0 < m) (hk : k ≤ a) (hl : l * w ≤ m) :
    Nl * (w * (2 * a - 1) - f * (2 * a - k)) ≤ Nb * (f * (2 * m - l) - w * (2 * m - b)) := by
  obtain ⟨q, hq⟩ : ∃ q, q = f - w := ⟨_, rfl⟩
  have hq1 : 1 ≤ q := by linarith
  have hf' : f = w + q := by linarith
  subst hf'
  have hw0 : 0 ≤ w := by linarith
  have hq0 : 0 ≤ q := by linarith
  have hf0 : 0 ≤ w + q := by linarith
  have hm0 : 0 ≤ m := hm.le
  have hr0 : 0 ≤ r := by linarith
  have ha0 : 0 ≤ a := by linarith
  have hR0 : 0 ≤ hR := by linarith
  obtain ⟨G1, hG1⟩ : ∃ G1, G1 = w * (2 * a - 1) - (w + q) * (2 * a - k) := ⟨_, rfl⟩
  obtain ⟨G2, hG2⟩ : ∃ G2, G2 = (w + q) * (2 * m - l) - w * (2 * m - b) := ⟨_, rfl⟩
  rw [← hG1, ← hG2]
  have hG1le : G1 ≤ a * (w - q) - w := by
    have : (w + q) * a ≤ (w + q) * (2 * a - k) := mul_le_mul_of_nonneg_left (by linarith) hf0
    rw [hG1]; linarith
  obtain ⟨X, hX⟩ : ∃ X, X = 2 * q * w - w - q := ⟨_, rfl⟩
  have hX0 : 0 ≤ X := by
    have := mul_nonneg (by linarith : (0 : ℚ) ≤ 2 * q - 1) (by linarith : (0 : ℚ) ≤ w - 1)
    rw [hX]; linarith
  have hwG2 : m * X ≤ w * G2 := by
    have e : w * G2 - m * X = (w + q) * (m - l * w) + w * w * b := by rw [hG2, hX]; ring
    have h1 := mul_nonneg hf0 (by linarith : (0 : ℚ) ≤ m - l * w)
    have h2 := mul_nonneg (mul_nonneg hw0 hw0) (by linarith : (0 : ℚ) ≤ b)
    linarith
  have hmX : 0 ≤ m * X := mul_nonneg hm0 hX0
  have hG2_0 : 0 ≤ G2 := by
    by_contra hc; push_neg at hc
    have := mul_neg_of_pos_of_neg (by linarith : (0 : ℚ) < w) hc
    linarith
  by_cases hG1p : G1 ≤ 0
  · have := mul_nonpos_of_nonneg_of_nonpos hNl0 hG1p
    have := mul_nonneg hNb0 hG2_0
    linarith
  push_neg at hG1p
  have hwq : q < w := by
    by_contra hc; push_neg at hc
    have : a * (w - q) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ha0 (by linarith)
    linarith
  have hrm : 0 ≤ 2 * r * m := mul_nonneg (mul_nonneg (by norm_num) hr0) hm0
  have hNl2 : Nl ≤ 2 * r * m := by
    have := mul_nonneg hf0 (by linarith : (0 : ℚ) ≤ b - 1)
    have := mul_nonneg hr0 (by linarith : (0 : ℚ) ≤ b - 1)
    rw [hNl]; linarith
  have hL : Nl * G1 ≤ 2 * r * m * (a * (w - q)) := by
    have h1 : Nl * G1 ≤ 2 * r * m * G1 := mul_le_mul_of_nonneg_right hNl2 hG1p.le
    have h2 : 2 * r * m * G1 ≤ 2 * r * m * (a * (w - q)) :=
      mul_le_mul_of_nonneg_left (by linarith) hrm
    linarith
  have hRNb : 2 * m * ((w + q) * hR - (w + q) - r) ≤ hR * Nb := by
    have e1 : (w + q) * (a * hR) = (w + q) * m := by rw [hahR]
    have e2 : r * (a * hR) = r * m := by rw [hahR]
    have := mul_nonneg hr0 hR0
    rw [hNb]; linarith
  -- key polynomial inequality
  have hP : r * w * (w - q) ≤ ((w + q) * hR - (w + q) - r) * X := by
    have hP0 : 0 ≤ (q - 1) * (w + q) * (2 * w - 1) :=
      mul_nonneg (mul_nonneg (by linarith) hf0) (by linarith)
    have hY : 0 ≤ X + w * (w - q) := by
      have := mul_nonneg hw0 (by linarith : (0 : ℚ) ≤ w - q)
      linarith
    have h1 := mul_nonneg (by linarith : (0 : ℚ) ≤ hR - 1) hP0
    have h2 := mul_nonneg (by linarith : (0 : ℚ) ≤ hR - 1 - r) hY
    have e : ((w + q) * hR - (w + q) - r) * X - r * w * (w - q) =
        (hR - 1) * ((q - 1) * (w + q) * (2 * w - 1)) + (hR - 1 - r) * (X + w * (w - q)) := by
      rw [hX]; ring
    linarith
  have hNbR : 0 ≤ hR * Nb := mul_nonneg hR0 hNb0
  have hA : hR * Nb * (m * X) ≤ hR * Nb * (w * G2) := mul_le_mul_of_nonneg_left hwG2 hNbR
  have hB : 2 * m * ((w + q) * hR - (w + q) - r) * (m * X) ≤ hR * Nb * (m * X) :=
    mul_le_mul_of_nonneg_right hRNb hmX
  have hC : 2 * m * m * (r * w * (w - q)) ≤ 2 * m * m * (((w + q) * hR - (w + q) - r) * X) :=
    mul_le_mul_of_nonneg_left hP (mul_nonneg (mul_nonneg (by norm_num) hm0) hm0)
  have hwR0 : 0 ≤ w * hR := mul_nonneg hw0 hR0
  have hD : w * hR * (Nl * G1) ≤ w * hR * (2 * r * m * (a * (w - q))) :=
    mul_le_mul_of_nonneg_left hL hwR0
  have hE : w * hR * (2 * r * m * (a * (w - q))) = 2 * m * m * (r * w * (w - q)) := by
    rw [← hahR]; ring
  have hwR : 0 < w * hR := mul_pos (by linarith) (by linarith)
  have key : w * hR * (Nl * G1) ≤ w * hR * (Nb * G2) := by
    calc w * hR * (Nl * G1) ≤ w * hR * (2 * r * m * (a * (w - q))) := hD
      _ = 2 * m * m * (r * w * (w - q)) := hE
      _ ≤ 2 * m * m * (((w + q) * hR - (w + q) - r) * X) := hC
      _ = 2 * m * ((w + q) * hR - (w + q) - r) * (m * X) := by ring
      _ ≤ hR * Nb * (m * X) := hB
      _ ≤ hR * Nb * (w * G2) := hA
      _ = w * hR * (Nb * G2) := by ring
  exact le_of_mul_le_mul_left key hwR

end FTDih

-- ===== DihSteps.lean =====

/-!
# Steps S1–S4 and the two realisable families (FT-DIHEDRAL.md §3, Lemma 2)
-/

open Finset

namespace FTDih

section Steps
variable {A : Type} [AddCommGroup A] [Fintype A] [DecidableEq A]
  (S : Finset (Dih A)) (hinv : ∀ s ∈ S, s⁻¹ ∈ S)

lemma sup_zmult_add (K : AddSubgroup A) (w r : A) (hw : w ∈ K) :
    K ⊔ AddSubgroup.zmultiples r = K ⊔ AddSubgroup.zmultiples (w + r) := by
  apply le_antisymm
  · refine sup_le le_sup_left ?_
    rw [AddSubgroup.zmultiples_le]
    have := sub_mem (AddSubgroup.mem_sup_right (AddSubgroup.mem_zmultiples (w + r)))
      (AddSubgroup.mem_sup_left hw : w ∈ K ⊔ AddSubgroup.zmultiples (w + r))
    simpa using this
  · refine sup_le le_sup_left ?_
    rw [AddSubgroup.zmultiples_le]
    exact add_mem (AddSubgroup.mem_sup_left hw)
      (AddSubgroup.mem_sup_right (AddSubgroup.mem_zmultiples _))

lemma prod_mem (ds : List (Dih A)) : ds.prod ∈ verts 1 ds := by
  simpa using prod_mem_verts (1 : Dih A) ds

/-- S3: add a rotation when the path ends on side 0 (directed snake) -/
lemma stepS3 (T : Finset (Dih A)) (b₁ : A) (ds : List (Dih A)) (γ : Dih A → ℚ)
    (h : Inv S T b₁ ds γ) (he : ds.prod.s = false) (r : A) (hr : rot r ∈ S) :
    ∃ ds', Inv S (insert (rot r) T) b₁ ds'
      (γ + Pi.single (rot r) (vD (insert (rot r) T) - vD T)) ∧ ds'.prod.s = false := by
  have h' := h
  obtain ⟨hS, hnd, hmem, -⟩ := h'
  have heq : ds.prod = rot ds.prod.r := by
    rcases eq_rot_or_ref ds.prod with h1 | h1
    · exact h1
    · rw [h1] at he; exact absurd he (by simp)
  have hw : ds.prod.r ∈ KT T := by
    have := (hmem _).1 (prod_mem ds)
    rw [heq, pt_rot] at this
    exact this
  obtain ⟨δ, hδ⟩ : ∃ δ, δ = ds.prod.r + r := ⟨_, rfl⟩
  obtain ⟨q, hq⟩ : ∃ q, q = addOrderOf ((δ : A ⧸ KT T)) := ⟨_, rfl⟩
  have hq0 : 0 < q := hq ▸ addOrderOf_pos _
  have hg : ∀ i : ℕ, (ds.prod * rot r) ^ i = rot (i • δ) := by
    intro i; rw [heq, rot_mul_rot, rot_pow, ← hδ]
  have hverts : verts 1 (dsnk ds (rot r) (q - 1)) =
      (List.range q).flatMap (fun i => (verts 1 ds).map (rot (i • δ) * ·)) := by
    rw [verts_dsnk, Nat.sub_add_cancel hq0]
    simp only [hg]
  obtain ⟨hN, hM, hL⟩ := blocks (hasRef T) (KT T) b₁ δ (verts 1 ds) hnd hmem
    (fun i => (verts 1 ds).map (rot (i • δ) * ·)) (fun i => Or.inl rfl)
  rw [← hq] at hN hM hL
  refine ⟨dsnk ds (rot r) (q - 1), inv_update S T b₁ ds γ h (rot r) _ q hq0
    (mem_dsnk ds hS (rot r) hr _) (by rw [hverts]; exact hN) ?_ ?_ ?_, ?_⟩
  · intro x
    rw [hverts, hM, PT, hasRef_insert_rot, KT_insert_rot, sup_zmult_add (KT T) _ r hw, ← hδ]
  · rw [hverts, hL]
  · intro d; rw [pc_dsnk, Nat.sub_add_cancel hq0]
  · rw [prod_dsnk, hg, heq, rot_mul_rot]; rfl

/-- S2: add a reflection when the path ends on side 1 (directed snake) -/
lemma stepS2 (T : Finset (Dih A)) (b₁ : A) (ds : List (Dih A)) (γ : Dih A → ℚ)
    (h : Inv S T b₁ ds γ) (hb₁ : ref b₁ ∈ T) (he : ds.prod.s = true) (b : A) (hb : ref b ∈ S) :
    ∃ ds', Inv S (insert (ref b) T) b₁ ds'
      (γ + Pi.single (ref b) (vD (insert (ref b) T) - vD T)) ∧ ds'.prod.s = true := by
  have h' := h
  obtain ⟨hS, hnd, hmem, -⟩ := h'
  have heq : ds.prod = ref ds.prod.r := by
    rcases eq_rot_or_ref ds.prod with h1 | h1
    · rw [h1] at he; exact absurd he (by simp)
    · exact h1
  have hT : hasRef T = true := hasRef_of_mem T b₁ hb₁
  have hw : ds.prod.r - b₁ ∈ KT T := by
    have := (hmem _).1 (prod_mem ds)
    rw [heq, pt_ref] at this
    exact this.2
  obtain ⟨δ, hδ⟩ : ∃ δ, δ = ds.prod.r - b := ⟨_, rfl⟩
  obtain ⟨q, hq⟩ : ∃ q, q = addOrderOf ((δ : A ⧸ KT T)) := ⟨_, rfl⟩
  have hq0 : 0 < q := hq ▸ addOrderOf_pos _
  have hg : ∀ i : ℕ, (ds.prod * ref b) ^ i = rot (i • δ) := by
    intro i; rw [heq, ref_mul_ref, rot_pow, ← hδ]
  have hverts : verts 1 (dsnk ds (ref b) (q - 1)) =
      (List.range q).flatMap (fun i => (verts 1 ds).map (rot (i • δ) * ·)) := by
    rw [verts_dsnk, Nat.sub_add_cancel hq0]
    simp only [hg]
  obtain ⟨hN, hM, hL⟩ := blocks (hasRef T) (KT T) b₁ δ (verts 1 ds) hnd hmem
    (fun i => (verts 1 ds).map (rot (i • δ) * ·)) (fun i => Or.inl rfl)
  rw [← hq] at hN hM hL
  refine ⟨dsnk ds (ref b) (q - 1), inv_update S T b₁ ds γ h (ref b) _ q hq0
    (mem_dsnk ds hS (ref b) hb _) (by rw [hverts]; exact hN) ?_ ?_ ?_, ?_⟩
  · intro x
    rw [hverts, hM, PT, hasRef_insert_ref, hT, KT_insert_ref T b b₁ _ hb₁ hw, ← hδ]
  · rw [hverts, hL]
  · intro d; rw [pc_dsnk, Nat.sub_add_cancel hq0]
  · rw [prod_dsnk, hg, heq, rot_mul_ref]; rfl

/-- S1: the first reflection (two blocks) -/
lemma stepS1 (T : Finset (Dih A)) (b₁ : A) (ds : List (Dih A)) (γ : Dih A → ℚ)
    (h : Inv S T b₁ ds γ) (hT : hasRef T = false) (he : ds.prod.s = false) (hb : ref b₁ ∈ S) :
    ∃ ds', Inv S (insert (ref b₁) T) b₁ ds'
      (γ + Pi.single (ref b₁) (vD (insert (ref b₁) T) - vD T)) ∧ ds'.prod.s = true := by
  have h' := h
  obtain ⟨hS, hnd, hmem, -⟩ := h'
  have heq : ds.prod = rot ds.prod.r := by
    rcases eq_rot_or_ref ds.prod with h1 | h1
    · exact h1
    · rw [h1] at he; exact absurd he (by simp)
  have hw : ds.prod.r ∈ KT T := by
    have := (hmem _).1 (prod_mem ds)
    rw [heq, pt_rot] at this
    exact this
  have hg : ds.prod * ref b₁ = ref (ds.prod.r + b₁) := by rw [heq, rot_mul_ref]; rfl
  have hverts : verts 1 (ds ++ ref b₁ :: ds) =
      verts 1 ds ++ (verts 1 ds).map (ref (ds.prod.r + b₁) * ·) := by
    rw [verts_append, one_mul, hg, verts_eq (ref (ds.prod.r + b₁)) ds]
  have hside : ∀ x ∈ verts 1 ds, x.s = false := by
    intro x hx
    have := (hmem x).1 hx
    rcases eq_rot_or_ref x with h1 | h1
    · rw [h1]; rfl
    · rw [h1, pt_ref, hT] at this; exact absurd this.1 (by simp)
  have hM : ∀ x, x ∈ verts 1 (ds ++ ref b₁ :: ds) ↔ PT (insert (ref b₁) T) b₁ x := by
    intro x
    rw [hverts, List.mem_append, mem_map_mul, ref_inv, hmem, hmem]
    simp only [PT]
    rw [hasRef_insert_ref, KT_insert_ref_first T b₁ hT, hT]
    rcases eq_rot_or_ref x with hx | hx <;> rw [hx]
    · rw [ref_mul_rot, xp_rot, xp_ref, xp_rot]; simp
    · rw [ref_mul_ref, xp_ref, xp_rot, xp_ref]
      simp only [Bool.false_eq_true, false_and, false_or, true_and]
      constructor
      · intro h2
        rw [show x.r - b₁ = ds.prod.r - (ds.prod.r + b₁ - x.r) by abel]
        exact sub_mem hw h2
      · intro h2
        rw [show ds.prod.r + b₁ - x.r = ds.prod.r - (x.r - b₁) by abel]
        exact sub_mem hw h2
  refine ⟨ds ++ ref b₁ :: ds, inv_update S T b₁ ds γ h (ref b₁) _ 2 (by norm_num) ?_ ?_ hM ?_ ?_, ?_⟩
  · intro d hd
    simp only [List.mem_append, List.mem_cons] at hd
    rcases hd with hd | rfl | hd
    · exact hS d hd
    · exact hb
    · exact hS d hd
  · rw [hverts, List.nodup_append]
    refine ⟨hnd, hnd.map (mul_right_injective _), ?_⟩
    intro x hx y hy hxy
    subst hxy
    have h1 := hside x hx
    obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hy
    have h2 := hside z hz
    simp [ref, h2] at h1
  · rw [hverts, List.length_append, List.length_map]; ring
  · intro d; rw [pc_append]; omega
  · rw [List.prod_append, List.prod_cons, ← mul_assoc, hg, heq]; rfl

include hinv in
/-- S4: add a rotation when the path ends on side 1 (alternating snake) -/
lemma stepS4 (T : Finset (Dih A)) (b₁ : A) (ds : List (Dih A)) (γ : Dih A → ℚ)
    (h : Inv S T b₁ ds γ) (he : ds.prod.s = true) (r : A) (hr : rot r ∈ S) :
    ∃ ds', Inv S (insert (rot r) T) b₁ ds'
      (γ + Pi.single (rot r) (vD (insert (rot r) T) - vD T)) := by
  have h' := h
  obtain ⟨hS, hnd, hmem, -⟩ := h'
  have heq : ds.prod = ref ds.prod.r := by
    rcases eq_rot_or_ref ds.prod with h1 | h1
    · rw [h1] at he; exact absurd he (by simp)
    · exact h1
  obtain ⟨q, hq⟩ : ∃ q, q = addOrderOf ((r : A ⧸ KT T)) := ⟨_, rfl⟩
  have hq0 : 0 < q := hq ▸ addOrderOf_pos _
  have hw : ds.prod * rot (-r) * ds.prod⁻¹ = rot r := by
    rw [heq, ref_mul_rot, ref_inv, ref_mul_ref]; congr 1; abel
  have hverts : verts 1 (asnk ds (rot (-r)) (rot r) (q - 1)) =
      (List.range q).flatMap (fun i =>
        (if Even i then verts 1 ds else (verts 1 ds).reverse).map (rot (i • r) * ·)) := by
    rw [(asnk_spec ds (rot (-r)) (rot r) hw (q - 1)).2, Nat.sub_add_cancel hq0]
    simp only [rot_pow]
  obtain ⟨hN, hM, hL⟩ := blocks (hasRef T) (KT T) b₁ r (verts 1 ds) hnd hmem
    (fun i => (if Even i then verts 1 ds else (verts 1 ds).reverse).map (rot (i • r) * ·))
    (fun i => by by_cases hi : Even i <;> simp [hi])
  rw [← hq] at hN hM hL
  have hrS : rot (-r) ∈ S := by rw [← rot_inv]; exact hinv _ hr
  refine ⟨asnk ds (rot (-r)) (rot r) (q - 1), inv_update S T b₁ ds γ h (rot r) _ q hq0
    (mem_asnk hinv ds hS _ _ hrS hr _) (by rw [hverts]; exact hN) ?_ ?_ ?_⟩
  · intro x
    rw [hverts, hM, PT, hasRef_insert_rot, KT_insert_rot]
  · rw [hverts, hL]
  · intro d
    rw [pc_asnk d ds _ _ (fun d => by rw [← rot_inv, pc_inv]), Nat.sub_add_cancel hq0]

lemma inv_init (b₁ : A) : Inv S ∅ b₁ [] 0 := by
  refine ⟨by simp, by simp, fun x => ?_, fun d => by simp [pc]⟩
  have h0 : hasRef (∅ : Finset (Dih A)) = false := by simp [hasRef]
  rw [PT, h0, KT_empty]
  rcases x with ⟨a, i⟩
  cases i <;> simp [XP, Dih.ext_iff]

lemma union_insert_eq (T : Finset (Dih A)) (x : Dih A) (L : List (Dih A)) :
    T ∪ (x :: L).toFinset = insert x T ∪ L.toFinset := by
  ext; simp only [Finset.mem_union, Finset.mem_insert, List.toFinset_cons]; tauto

lemma phaseR1 (b₁ : A) : ∀ (L : List (Dih A)), (∀ x ∈ L, x ∈ S ∧ x.s = false) →
    ∀ T ds γ, Inv S T b₁ ds γ → ds.prod.s = false →
    ∃ ds', Inv S (T ∪ L.toFinset) b₁ ds' (γ + FTAbelian.greedy vD T L) ∧ ds'.prod.s = false := by
  intro L
  induction L with
  | nil => intro _ T ds γ h he; exact ⟨ds, by simpa using h, he⟩
  | cons x L ih =>
    intro hL T ds γ h he
    obtain ⟨hxS, hxs⟩ := hL x (by simp)
    have hx : x = rot x.r := by
      rcases eq_rot_or_ref x with h1 | h1
      · exact h1
      · rw [h1] at hxs; exact absurd hxs (by simp)
    rw [hx] at hxS
    obtain ⟨ds1, h1, he1⟩ := stepS3 S T b₁ ds γ h he x.r hxS
    rw [← hx] at h1
    obtain ⟨ds2, h2, he2⟩ := ih (fun y hy => hL y (by simp [hy])) _ ds1 _ h1 he1
    refine ⟨ds2, ?_, he2⟩
    rw [FTAbelian.greedy_cons, ← add_assoc, union_insert_eq]
    exact h2

lemma phaseF (b₁ : A) : ∀ (L : List (Dih A)), (∀ x ∈ L, x ∈ S ∧ x.s = true) →
    ∀ T ds γ, Inv S T b₁ ds γ → ref b₁ ∈ T → ds.prod.s = true →
    ∃ ds', Inv S (T ∪ L.toFinset) b₁ ds' (γ + FTAbelian.greedy vD T L) ∧ ds'.prod.s = true := by
  intro L
  induction L with
  | nil => intro _ T ds γ h _ he; exact ⟨ds, by simpa using h, he⟩
  | cons x L ih =>
    intro hL T ds γ h hb₁ he
    obtain ⟨hxS, hxs⟩ := hL x (by simp)
    have hx : x = ref x.r := by
      rcases eq_rot_or_ref x with h1 | h1
      · rw [h1] at hxs; exact absurd hxs (by simp)
      · exact h1
    rw [hx] at hxS
    obtain ⟨ds1, h1, he1⟩ := stepS2 S T b₁ ds γ h hb₁ he x.r hxS
    rw [← hx] at h1
    obtain ⟨ds2, h2, he2⟩ := ih (fun y hy => hL y (by simp [hy])) _ ds1 _ h1
      (Finset.mem_insert_of_mem hb₁) he1
    refine ⟨ds2, ?_, he2⟩
    rw [FTAbelian.greedy_cons, ← add_assoc, union_insert_eq]
    exact h2

include hinv in
lemma phaseR2 (b₁ : A) : ∀ (L : List (Dih A)), (∀ x ∈ L, x ∈ S ∧ x.s = false) →
    ∀ T ds γ, Inv S T b₁ ds γ →
    ∃ ds', Inv S (T ∪ L.toFinset) b₁ ds' (γ + FTAbelian.greedy vD T L) := by
  intro L
  induction L with
  | nil => intro _ T ds γ h; exact ⟨ds, by simpa using h⟩
  | cons x L ih =>
    intro hL T ds γ h
    obtain ⟨hxS, hxs⟩ := hL x (by simp)
    have hx : x = rot x.r := by
      rcases eq_rot_or_ref x with h1 | h1
      · exact h1
      · rw [h1] at hxs; exact absurd hxs (by simp)
    rw [hx] at hxS
    obtain ⟨ds1, h1⟩ : ∃ ds1, Inv S (insert (rot x.r) T) b₁ ds1
        (γ + Pi.single (rot x.r) (vD (insert (rot x.r) T) - vD T)) := by
      cases he : ds.prod.s
      · exact (stepS3 S T b₁ ds γ h he x.r hxS).imp fun _ h => h.1
      · exact stepS4 S hinv T b₁ ds γ h he x.r hxS
    rw [← hx] at h1
    obtain ⟨ds2, h2⟩ := ih (fun y hy => hL y (by simp [hy])) _ ds1 _ h1
    refine ⟨ds2, ?_⟩
    rw [FTAbelian.greedy_cons, ← add_assoc, union_insert_eq]
    exact h2

/-- final step: an invariant for `S` itself gives a realisable vector -/
lemma real_of_inv (b₁ : A) (ds : List (Dih A)) (γ : Dih A → ℚ) (h : Inv S S b₁ ds γ)
    (hall : ∀ g, PT S b₁ g) : γ ∈ Real S := by
  obtain ⟨hS, hnd, hmem, hcnt⟩ := h
  have hall' : ∀ g, g ∈ verts 1 ds := fun g => (hmem g).2 (hall g)
  have hlen : (verts 1 ds).length = Fintype.card (Dih A) := by
    rw [← List.toFinset_card_of_nodup hnd]
    congr 1
    ext g; simp [hall' g]
  refine ⟨ds, hS, hnd, hall', fun d _ => ?_⟩
  have := hcnt d
  rw [hlen] at this
  have hN : (0 : ℚ) < Fintype.card (Dih A) := by
    have : 0 < Fintype.card (Dih A) := Fintype.card_pos
    exact_mod_cast this
  have h2 : (Fintype.card (Dih A) : ℚ) ≠ 0 := hN.ne'
  field_simp at this
  linarith

/-- rotations / reflections of a list -/
def lR (L : List (Dih A)) : List (Dih A) := L.filter (fun x => !x.s)
def lF (L : List (Dih A)) : List (Dih A) := L.filter (fun x => x.s)

lemma lR_spec (L : List (Dih A)) (hL : L.toFinset = S) : ∀ x ∈ lR L, x ∈ S ∧ x.s = false := by
  intro x hx
  simp only [lR, List.mem_filter, Bool.not_eq_true'] at hx
  exact ⟨by rw [← hL]; exact List.mem_toFinset.2 hx.1, hx.2⟩

lemma lF_spec (L : List (Dih A)) (hL : L.toFinset = S) : ∀ x ∈ lF L, x ∈ S ∧ x.s = true := by
  intro x hx
  simp only [lF, List.mem_filter] at hx
  exact ⟨by rw [← hL]; exact List.mem_toFinset.2 hx.1, hx.2⟩

lemma mem_lRF (L : List (Dih A)) (x : Dih A) : x ∈ L ↔ x ∈ lR L ∨ x ∈ lF L := by
  simp only [lR, lF, List.mem_filter]
  cases x.s <;> simp

lemma hasRef_lR (L : List (Dih A)) : hasRef (∅ ∪ (lR L).toFinset) = false := by
  simp only [hasRef, decide_eq_false_iff_not, not_exists, not_and, Finset.empty_union,
    List.mem_toFinset]
  intro x hx
  simp only [lR, List.mem_filter, Bool.not_eq_true'] at hx
  simp [hx.2]

lemma lF_cons (L : List (Dih A)) (hL : L.toFinset = S) (hF : ∃ x ∈ S, x.s = true) :
    ∃ b₁ L', lF L = ref b₁ :: L' := by
  obtain ⟨x, hxS, hxs⟩ := hF
  have hx : x ∈ lF L := by
    simp only [lF, List.mem_filter]
    exact ⟨List.mem_toFinset.1 (hL ▸ hxS), hxs⟩
  cases hc : lF L with
  | nil => rw [hc] at hx; simp at hx
  | cons y L' =>
    have hy := (lF_spec S L hL y (by rw [hc]; simp)).2
    rcases eq_rot_or_ref y with h1 | h1
    · rw [h1] at hy; exact absurd hy (by simp)
    · exact ⟨y.r, L', by rw [← h1]⟩

/-- **Family 1** (rotations first) -/
theorem real1 (L : List (Dih A)) (hL : L.toFinset = S) (hF : ∃ x ∈ S, x.s = true)
    (hall : ∀ b₁, ref b₁ ∈ S → ∀ g, PT S b₁ g) :
    FTAbelian.greedy vD ∅ (lR L ++ lF L) ∈ Real S := by
  obtain ⟨b₁, L', hLF⟩ := lF_cons S L hL hF
  have hb₁S : ref b₁ ∈ S := (lF_spec S L hL (ref b₁) (by rw [hLF]; simp)).1
  obtain ⟨ds1, h1, he1⟩ := phaseR1 S b₁ (lR L) (lR_spec S L hL) ∅ [] 0 (inv_init S b₁) (by simp)
  obtain ⟨ds2, h2, he2⟩ := stepS1 S _ b₁ ds1 _ h1 (hasRef_lR L) he1 hb₁S
  obtain ⟨ds3, h3, -⟩ := phaseF S b₁ L' (fun x hx => lF_spec S L hL x (by rw [hLF]; simp [hx]))
    _ ds2 _ h2 (Finset.mem_insert_self _ _) he2
  have hT : insert (ref b₁) (∅ ∪ (lR L).toFinset) ∪ L'.toFinset = S := by
    rw [← hL]; ext x
    simp only [Finset.mem_union, Finset.mem_insert, Finset.empty_union, List.mem_toFinset,
      Finset.notMem_empty, false_or]
    rw [mem_lRF L x, hLF]; simp; tauto
  rw [hT] at h3
  have hγ : FTAbelian.greedy vD ∅ (lR L ++ lF L) =
      0 + FTAbelian.greedy vD ∅ (lR L) +
        Pi.single (ref b₁) (vD (insert (ref b₁) (∅ ∪ (lR L).toFinset)) - vD (∅ ∪ (lR L).toFinset)) +
        FTAbelian.greedy vD (insert (ref b₁) (∅ ∪ (lR L).toFinset)) L' := by
    rw [FTAbelian.greedy_append, hLF, FTAbelian.greedy_cons, zero_add, add_assoc]
  rw [hγ]
  exact real_of_inv S b₁ ds3 _ h3 (hall b₁ hb₁S)

include hinv in
/-- **Family 2** (reflections first) -/
theorem real2 (L : List (Dih A)) (hL : L.toFinset = S) (hF : ∃ x ∈ S, x.s = true)
    (hall : ∀ b₁, ref b₁ ∈ S → ∀ g, PT S b₁ g) :
    FTAbelian.greedy vD ∅ (lF L ++ lR L) ∈ Real S := by
  obtain ⟨b₁, L', hLF⟩ := lF_cons S L hL hF
  have hb₁S : ref b₁ ∈ S := (lF_spec S L hL (ref b₁) (by rw [hLF]; simp)).1
  obtain ⟨ds1, h1, he1⟩ := stepS1 S ∅ b₁ [] 0 (inv_init S b₁) (by simp [hasRef]) (by simp) hb₁S
  obtain ⟨ds2, h2, -⟩ := phaseF S b₁ L' (fun x hx => lF_spec S L hL x (by rw [hLF]; simp [hx]))
    _ ds1 _ h1 (Finset.mem_insert_self _ _) he1
  obtain ⟨ds3, h3⟩ := phaseR2 S hinv b₁ (lR L) (lR_spec S L hL) _ ds2 _ h2
  have hT : insert (ref b₁) (∅ : Finset (Dih A)) ∪ L'.toFinset ∪ (lR L).toFinset = S := by
    rw [← hL]; ext x
    simp only [Finset.mem_union, Finset.mem_insert, List.mem_toFinset,
      Finset.notMem_empty, or_false]
    rw [mem_lRF L x, hLF]; simp; tauto
  rw [hT] at h3
  have hγ : FTAbelian.greedy vD ∅ (lF L ++ lR L) =
      0 + Pi.single (ref b₁) (vD (insert (ref b₁) (∅ : Finset (Dih A))) - vD (∅ : Finset (Dih A))) +
        FTAbelian.greedy vD (insert (ref b₁) ∅) L' +
        FTAbelian.greedy vD (insert (ref b₁) ∅ ∪ L'.toFinset) (lR L) := by
    rw [FTAbelian.greedy_append, hLF, FTAbelian.greedy_cons, zero_add,
      show (∅ : Finset (Dih A)) ∪ (ref b₁ :: L').toFinset = insert (ref b₁) ∅ ∪ L'.toFinset by
        ext; simp]
  rw [hγ]
  exact real_of_inv S b₁ ds3 _ h3 (hall b₁ hb₁S)

end Steps

end FTDih

-- ===== DihIneq.lean =====

/-!
# Conditions (R) and (F): the uniform vector lies in the λ-blended anticore

Group-theoretic inputs (subgroup sizes) are turned into the rational parameters of `DihArith`.
-/

open Finset

namespace FTDih

section Ineq
variable {A : Type} [AddCommGroup A] [Fintype A] [DecidableEq A]

lemma genS_mono {T T' : Finset (Dih A)} (h : T ⊆ T') : genS T ⊆ genS T' := by
  intro a ha
  rcases ha with ha | ⟨x, hx, y, hy, rfl⟩
  · exact Or.inl (h ha)
  · exact Or.inr ⟨x, h hx, y, h hy, rfl⟩

lemma KT_mono {T T' : Finset (Dih A)} (h : T ⊆ T') : KT T ≤ KT T' :=
  AddSubgroup.closure_mono (genS_mono h)

/-- `|⟨T⟩ ∩ A|` -/
noncomputable abbrev cl (T : Finset (Dih A)) : ℕ := Nat.card (KT T)

lemma cl_pos (T : Finset (Dih A)) : 0 < cl T := Nat.card_pos

lemma cl_dvd {T T' : Finset (Dih A)} (h : T ⊆ T') : cl T ∣ cl T' :=
  AddSubgroup.card_dvd_of_le (KT_mono h)

lemma cl_le {T T' : Finset (Dih A)} (h : T ⊆ T') : cl T ≤ cl T' :=
  Nat.le_of_dvd (cl_pos T') (cl_dvd h)

omit [DecidableEq A] in
lemma natcard_A : Nat.card A = Fintype.card A := Nat.card_eq_fintype_card

lemma card_le_m (K : AddSubgroup A) : Nat.card K ≤ Fintype.card A := by
  have := AddSubgroup.card_dvd_of_le (le_top : K ≤ ⊤)
  rw [AddSubgroup.card_top, (natcard_A (A := A))] at this
  exact Nat.le_of_dvd Fintype.card_pos this

lemma cl_empty : cl (∅ : Finset (Dih A)) = 1 := by
  rw [cl, KT_empty, AddSubgroup.card_bot]

lemma vD_rot (U : Finset (Dih A)) (hU : ∀ x ∈ U, x.s = false) :
    vD U = 2 * (Fintype.card A : ℚ) - 2 * Fintype.card A / cl U := by
  have h : hasRef U = false := by
    simp only [hasRef, decide_eq_false_iff_not, not_exists, not_and]
    intro x hx; simp [hU x hx]
  rw [vD, sz, h, card_dih]; push_cast; simp

lemma vD_ref (W : Finset (Dih A)) (hW : ∃ x ∈ W, x.s = true) :
    vD W = 2 * (Fintype.card A : ℚ) - Fintype.card A / cl W := by
  have h : hasRef W = true := by simpa [hasRef] using hW
  rw [vD, sz, h, card_dih]; push_cast; simp only [if_true]
  have : (0 : ℚ) < cl W := by exact_mod_cast cl_pos W
  field_simp

lemma KT_union (U W : Finset (Dih A)) (hU : ∀ x ∈ U, x.s = false) (hW : ∀ x ∈ W, x.s = true) :
    KT (W ∪ U) = KT U ⊔ KT W := by
  have e1 : rotS (W ∪ U) = rotS U := by
    ext a; simp only [rotS, Set.mem_setOf_eq, Finset.mem_union]
    constructor
    · rintro (h | h)
      · exact absurd (hW _ h) (by simp)
      · exact h
    · exact Or.inr
  have e2 : refS (W ∪ U) = refS W := by
    ext a; simp only [refS, Set.mem_setOf_eq, Finset.mem_union]
    constructor
    · rintro (h | h)
      · exact h
      · exact absurd (hU _ h) (by simp)
    · exact Or.inl
  have e3 : refS U = ∅ := by
    ext a; simp only [refS, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    intro h; exact absurd (hU _ h) (by simp)
  have e4 : rotS W = ∅ := by
    ext a; simp only [rotS, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    intro h; exact absurd (hW _ h) (by simp)
  rw [KT, KT, KT, genS, genS, genS, e1, e2, e3, e4, Set.image2_empty_left, Set.union_empty,
    Set.empty_union, AddSubgroup.closure_union]

lemma card_rot_lb (S U : Finset (Dih A)) (hS1 : (1 : Dih A) ∉ S) (hUS : U ⊆ S)
    (hU : ∀ x ∈ U, x.s = false) : U.card + 1 ≤ cl U := by
  have h0 : (0 : A) ∉ U.image Dih.r := by
    intro h
    obtain ⟨x, hx, hx0⟩ := Finset.mem_image.1 h
    apply hS1
    have : x = 1 := Dih.ext hx0 (by simp [hU x hx])
    rw [← this]; exact hUS hx
  have hinj : (U.image Dih.r).card = U.card := by
    apply Finset.card_image_of_injOn
    intro x hx y hy hxy
    ext
    · exact hxy
    · rw [hU x hx, hU y hy]
  have := FTAbelian.card_le_of_subset (KT U) (insert 0 (U.image Dih.r)) (by
    intro a ha
    rcases Finset.mem_insert.1 ha with rfl | ha
    · exact zero_mem _
    · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 ha
      apply AddSubgroup.subset_closure
      left
      show rot x.r ∈ U
      have : x = rot x.r := Dih.ext rfl (by simp [hU x hx])
      rw [← this]; exact hx)
  rw [Finset.card_insert_of_notMem h0, hinj] at this
  exact this

lemma card_ref_lb (W : Finset (Dih A)) (hW : ∀ x ∈ W, x.s = true) (hne : W.Nonempty) :
    W.card ≤ cl W := by
  obtain ⟨x0, hx0⟩ := hne
  have hinj : (W.image (fun x => x.r - x0.r)).card = W.card := by
    apply Finset.card_image_of_injOn
    intro x hx y hy hxy
    ext
    · exact sub_left_injective hxy
    · rw [hW x hx, hW y hy]
  have hmemR : ∀ x ∈ W, x.r ∈ refS W := by
    intro x hx
    show ref x.r ∈ W
    have : x = ref x.r := Dih.ext rfl (by simp [hW x hx])
    rw [← this]; exact hx
  have := FTAbelian.card_le_of_subset (KT W) (W.image (fun x => x.r - x0.r)) (by
    intro a ha
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 ha
    exact AddSubgroup.subset_closure (Or.inr ⟨x.r, hmemR x hx, x0.r, hmemR x0 hx0, rfl⟩))
  rw [hinj] at this
  exact this

lemma KT_single_ref (W : Finset (Dih A)) (hW : ∀ x ∈ W, x.s = true) (h1 : W.card = 1) :
    KT W = ⊥ := by
  obtain ⟨x0, rfl⟩ := Finset.card_eq_one.1 h1
  have e1 : rotS ({x0} : Finset (Dih A)) = ∅ := by
    ext a; simp only [rotS, Set.mem_setOf_eq, Finset.mem_singleton, Set.mem_empty_iff_false,
      iff_false]
    intro h; have := hW x0 (by simp); rw [← h] at this; simp at this
  have e2 : refS ({x0} : Finset (Dih A)) = {x0.r} := by
    ext a; simp only [refS, Set.mem_setOf_eq, Finset.mem_singleton, Set.mem_singleton_iff]
    constructor
    · intro h; rw [← h]; rfl
    · intro h; rw [h]; exact Dih.ext rfl (by simp [hW x0 (by simp)])
  rw [KT, genS, e1, e2, Set.image2_singleton, sub_self, Set.empty_union,
    AddSubgroup.closure_singleton_zero]

lemma card_sup_zmult (K : AddSubgroup A) (δ : A) :
    Nat.card (K ⊔ AddSubgroup.zmultiples δ : AddSubgroup A) =
      addOrderOf ((δ : A ⧸ K)) * Nat.card K := by
  classical
  set V : List (Dih A) := ((Finset.univ.filter (· ∈ K)).toList).map rot with hVdef
  have hV : V.Nodup := (Finset.nodup_toList _).map rot_injective
  have hVm : ∀ x, x ∈ V ↔ XP false K 0 x := by
    intro x
    rw [hVdef, List.mem_map]
    simp only [Finset.mem_toList, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨a, ha, rfl⟩; simpa [XP] using ha
    · intro h
      rcases eq_rot_or_ref x with hx | hx
      · rw [hx] at h ⊢; exact ⟨x.r, by simpa [XP] using h, rfl⟩
      · rw [hx] at h; simp [XP] at h
  obtain ⟨hN, hM, hL⟩ := blocks false K 0 δ V hV hVm (fun i => V.map (rot (i • δ) * ·))
    (fun i => Or.inl rfl)
  have h1 := len_of_xp false _ 0 _ hN hM
  have h2 := len_of_xp false K 0 V hV hVm
  simp only [Bool.false_eq_true, if_false, one_mul] at h1 h2
  rw [← h1, hL, h2]

/-! ## The parameters -/

variable (S : Finset (Dih A))

def Rs : Finset (Dih A) := S.filter (fun x => x.s = false)
def Fs : Finset (Dih A) := S.filter (fun x => x.s = true)

lemma Rs_rot : ∀ x ∈ Rs S, x.s = false := fun x hx => (Finset.mem_filter.1 hx).2
lemma Fs_ref : ∀ x ∈ Fs S, x.s = true := fun x hx => (Finset.mem_filter.1 hx).2
lemma Rs_sub : Rs S ⊆ S := Finset.filter_subset _ _
lemma Fs_sub : Fs S ⊆ S := Finset.filter_subset _ _

lemma Fs_union_Rs : Fs S ∪ Rs S = S := by
  ext x; simp only [Fs, Rs, Finset.mem_union, Finset.mem_filter]
  cases x.s <;> simp

lemma card_RF : (Rs S).card + (Fs S).card = S.card := by
  have hd : Disjoint (Fs S) (Rs S) := by
    rw [Finset.disjoint_left]
    intro x h1 h2
    have := Fs_ref S x h1; rw [Rs_rot S x h2] at this; exact Bool.noConfusion this
  have := Finset.card_union_of_disjoint hd
  rw [Fs_union_Rs] at this
  omega

noncomputable def pm : ℚ := Fintype.card A
noncomputable def pr : ℚ := (Rs S).card
noncomputable def pf : ℚ := (Fs S).card
noncomputable def pa : ℚ := pm (A := A) / cl (Rs S)
noncomputable def pb : ℚ := pm (A := A) / cl (Fs S)
noncomputable def pNl : ℚ := pr S * (2 * pm (A := A) - pb S) - pf S * (pb S - 1)
noncomputable def pNb : ℚ := pf S * (2 * pm (A := A) - 2 * pa S) - pr S * (2 * pa S - 1)
/-- the blending weight λ -/
noncomputable def lam : ℚ := if (Rs S).card = 0 then 1 else pNl S / (pNl S + pNb S)
/-- the target value per element of `S` -/
noncomputable def tgt : ℚ := (2 * pm (A := A) - 1) / S.card

lemma pr_nonneg : (0 : ℚ) ≤ pr S := by unfold pr; exact Nat.cast_nonneg _

variable (hS1 : (1 : Dih A) ∉ S) (hinv : ∀ s ∈ S, s⁻¹ ∈ S) (hKS : KT S = ⊤)
  (hFne : (Fs S).Nonempty)

include hKS in
lemma cl_S : cl S = Fintype.card A := by
  rw [cl, hKS, AddSubgroup.card_top, (natcard_A (A := A))]

include hKS in
lemma vD_S (hF : ∃ x ∈ S, x.s = true) : vD S = 2 * pm (A := A) - 1 := by
  rw [vD_ref S hF, cl_S S hKS, pm]
  have : (0 : ℚ) < Fintype.card A := by exact_mod_cast Fintype.card_pos
  field_simp

/-- basic facts about the parameters -/
structure Facts : Prop where
  hm : 0 < pm (A := A)
  hR1 : (1 : ℚ) ≤ cl (Rs S)
  hF1 : (1 : ℚ) ≤ cl (Fs S)
  hahR : pa S * cl (Rs S) = pm (A := A)
  hbhF : pb S * cl (Fs S) = pm (A := A)
  ha : 1 ≤ pa S
  hb : 1 ≤ pb S
  hrR : pr S + 1 ≤ cl (Rs S)
  hf1 : 1 ≤ pf S
  hfF : pf S ≤ cl (Fs S)
  hcard : (S.card : ℚ) = pr S + pf S

include hS1 hFne in
lemma facts : Facts S := by
  have hm : (0 : ℚ) < Fintype.card A := by exact_mod_cast Fintype.card_pos
  have hR0 : (0 : ℚ) < cl (Rs S) := by exact_mod_cast cl_pos _
  have hF0 : (0 : ℚ) < cl (Fs S) := by exact_mod_cast cl_pos _
  have hRm : (cl (Rs S) : ℚ) ≤ Fintype.card A := by exact_mod_cast card_le_m _
  have hFm : (cl (Fs S) : ℚ) ≤ Fintype.card A := by exact_mod_cast card_le_m _
  refine ⟨hm, by exact_mod_cast cl_pos _, by exact_mod_cast cl_pos _, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [pa, pm]; field_simp
  · rw [pb, pm]; field_simp
  · rw [pa, pm, le_div_iff₀ hR0]; linarith
  · rw [pb, pm, le_div_iff₀ hF0]; linarith
  · rw [pr]; exact_mod_cast card_rot_lb S (Rs S) hS1 (Rs_sub S) (Rs_rot S)
  · rw [pf]; exact_mod_cast hFne.card_pos
  · rw [pf]; exact_mod_cast card_ref_lb (Fs S) (Fs_ref S) hFne
  · rw [pr, pf]; exact_mod_cast (card_RF S).symm

lemma vD_Rs : vD (Rs S) = 2 * pm (A := A) - 2 * pa S := by
  rw [vD_rot _ (Rs_rot S), pa, pm]; ring

include hFne in
lemma vD_Fs : vD (Fs S) = 2 * pm (A := A) - pb S := by
  obtain ⟨x, hx⟩ := hFne
  rw [vD_ref _ ⟨x, hx, Fs_ref S x hx⟩, pb, pm]

/-- the two totals -/
lemma totals (Fa : Facts S) :
    lam S * (2 * pm (A := A) - 2 * pa S) + (1 - lam S) * (pb S - 1) = pr S * tgt S ∧
    lam S * (2 * pa S - 1) + (1 - lam S) * (2 * pm (A := A) - pb S) = pf S * tgt S := by
  have hS0 : (0 : ℚ) < S.card := by rw [Fa.hcard]; linarith [Fa.hf1, pr_nonneg S]
  by_cases hr : (Rs S).card = 0
  · have hpr : pr S = 0 := by rw [pr, hr]; simp
    have hRe : Rs S = ∅ := Finset.card_eq_zero.1 hr
    have hpa : pa S = pm (A := A) := by rw [pa, hRe, cl_empty]; simp
    have hlam : lam S = 1 := by rw [lam, if_pos hr]
    rw [hlam, hpa, hpr, tgt, Fa.hcard, hpr, zero_add]
    have : pf S ≠ 0 := by linarith [Fa.hf1]
    have e : pf S * ((2 * pm (A := A) - 1) / pf S) = 2 * pm (A := A) - 1 := by field_simp
    constructor
    · ring
    · rw [e]; ring
  · have hr1 : (1 : ℚ) ≤ pr S := by
      rw [pr]; exact_mod_cast Nat.one_le_iff_ne_zero.2 hr
    have hNl := Nl_pos (pm (A := A)) (pr S) (pf S) (pa S) (pb S) (cl (Fs S)) hr1 Fa.hf1 Fa.hb Fa.hF1
      Fa.hbhF Fa.hfF
    have hNb := Nb_nonneg (pm (A := A)) (pr S) (pf S) (pa S) (cl (Rs S)) (by linarith) (by linarith [Fa.hrR])
      Fa.hf1 Fa.ha Fa.hahR
    have hlam : lam S = pNl S / (pNl S + pNb S) := by rw [lam, if_neg hr]
    have hD : 0 < pNl S + pNb S := by rw [pNl, pNb]; linarith
    have hX : pNl S + pNb S = (pr S + pf S) * (2 * pm (A := A) - 2 * pa S - pb S + 1) := by
      rw [pNl, pNb]; ring
    have hX0 : 0 < 2 * pm (A := A) - 2 * pa S - pb S + 1 := by
      have : 0 < pr S + pf S := by linarith [Fa.hf1]
      rw [hX] at hD
      exact pos_of_mul_pos_right hD this.le
    have h1m : 1 - lam S = pNb S / (pNl S + pNb S) := by
      rw [hlam]; field_simp; ring
    rw [h1m, hlam, tgt, Fa.hcard]
    have : pr S + pf S ≠ 0 := by linarith [Fa.hf1]
    constructor
    · rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, div_eq_iff hD.ne', hX]
      field_simp
      rw [pNl, pNb]; ring
    · rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, div_eq_iff hD.ne', hX]
      field_simp
      rw [pNl, pNb]; ring

include hS1 hinv hKS hFne in
/-- **Condition (R)** -/
theorem ineqR (U : Finset (Dih A)) (hU : U ⊆ Rs S) :
    (U.card : ℚ) * tgt S ≤ lam S * vD U + (1 - lam S) * (vD (Fs S ∪ U) - vD (Fs S)) := by
  have Fa := facts S hS1 hFne
  obtain ⟨totR, -⟩ := totals S Fa
  have hUrot : ∀ x ∈ U, x.s = false := fun x hx => Rs_rot S x (hU hx)
  have hFU : ∃ x ∈ Fs S ∪ U, x.s = true := by
    obtain ⟨x, hx⟩ := hFne; exact ⟨x, Finset.mem_union_left _ hx, Fs_ref S x hx⟩
  rcases U.eq_empty_or_nonempty with hU0 | hUne
  · subst hU0
    have : vD (∅ : Finset (Dih A)) = 0 := by rw [vD_rot ∅ (by simp), cl_empty]; simp
    simp [this]
  have hr : (Rs S).card ≠ 0 := by
    intro h; rw [Finset.card_eq_zero.1 h] at hU
    obtain ⟨x, hx⟩ := hUne; exact absurd (hU hx) (by simp)
  have hr1 : (1 : ℚ) ≤ pr S := by rw [pr]; exact_mod_cast Nat.one_le_iff_ne_zero.2 hr
  have hNl := Nl_pos (pm (A := A)) (pr S) (pf S) (pa S) (pb S) (cl (Fs S)) hr1 Fa.hf1 Fa.hb Fa.hF1
    Fa.hbhF Fa.hfF
  have hNb := Nb_nonneg (pm (A := A)) (pr S) (pf S) (pa S) (cl (Rs S)) (by linarith)
    (by linarith [Fa.hrR]) Fa.hf1 Fa.ha Fa.hahR
  have hD : 0 < pNl S + pNb S := by rw [pNl, pNb]; linarith
  have hlam : lam S = pNl S / (pNl S + pNb S) := by rw [lam, if_neg hr]
  have h1m : 1 - lam S = pNb S / (pNl S + pNb S) := by rw [hlam]; field_simp; ring
  -- values
  set h := cl U with hh
  set d := cl (Fs S ∪ U) with hd
  have hh0 : (0 : ℚ) < h := by exact_mod_cast cl_pos U
  have hd0 : (0 : ℚ) < d := by exact_mod_cast cl_pos _
  set i := pm (A := A) / h with hi
  set j := pm (A := A) / d with hj
  have hvU : vD U = 2 * pm (A := A) - 2 * i := by rw [vD_rot U hUrot, hi, pm]; ring
  have hvFU : vD (Fs S ∪ U) = 2 * pm (A := A) - j := by rw [vD_ref _ hFU, hj, pm]
  rw [hvU, hvFU, vD_Fs S hFne]
  -- reduction to the arithmetic inequality
  suffices key : pNb S * (U.card * (pb S - 1) - pr S * (pb S - j)) ≤
      pNl S * (pr S * (2 * pm (A := A) - 2 * i) - U.card * (2 * pm (A := A) - 2 * pa S)) by
    have e : pr S * (lam S * (2 * pm (A := A) - 2 * i) + (1 - lam S) * (2 * pm (A := A) - j -
        (2 * pm (A := A) - pb S))) - U.card * (pr S * tgt S) =
        (pNl S * (pr S * (2 * pm (A := A) - 2 * i) - U.card * (2 * pm (A := A) - 2 * pa S)) -
         pNb S * (U.card * (pb S - 1) - pr S * (pb S - j))) / (pNl S + pNb S) := by
      rw [← totR, h1m, hlam]; field_simp; ring
    have h2 : 0 ≤ pr S * (lam S * (2 * pm (A := A) - 2 * i) + (1 - lam S) * (2 * pm (A := A) - j -
        (2 * pm (A := A) - pb S))) - U.card * (pr S * tgt S) := by
      rw [e]; exact div_nonneg (by linarith) hD.le
    have hpr0 : 0 < pr S := by linarith
    nlinarith
  have hmpos := Fa.hm
  have hih : i * h = pm (A := A) := by rw [hi]; field_simp
  have hjd : j * d = pm (A := A) := by rw [hj]; field_simp
  have hjb : j ≤ pb S := by
    rw [hj, pb]
    apply div_le_div_of_nonneg_left hmpos.le (by exact_mod_cast cl_pos _)
    exact_mod_cast cl_le (Finset.subset_union_left)
  have hia : pa S ≤ i := by
    rw [hi, pa]
    apply div_le_div_of_nonneg_left hmpos.le hh0
    exact_mod_cast cl_le hU
  have hKFU : KT (Fs S ∪ U) = KT U ⊔ KT (Fs S) := KT_union U (Fs S) hUrot (Fs_ref S)
  have hKS' : KT S = KT (Rs S) ⊔ KT (Fs S) := by
    rw [← KT_union (Rs S) (Fs S) (Rs_rot S) (Fs_ref S), Fs_union_Rs]
  by_cases hA : KT U = KT (Rs S)
  · -- case A
    have hi' : i = pa S := by rw [hi, pa, hh, cl, hA]
    have hj' : j = 1 := by
      rw [hj, hd, cl, hKFU, hA, ← hKS', hKS, AddSubgroup.card_top, (natcard_A (A := A)), pm]
      field_simp
    rw [hi']
    have hum : (U.card : ℚ) ≤ pr S := by rw [pr]; exact_mod_cast Finset.card_le_card hU
    have ham : pa S ≤ pm (A := A) := by
      have := mul_le_mul_of_nonneg_left Fa.hR1 (by linarith [Fa.ha] : (0 : ℚ) ≤ pa S)
      linarith [Fa.hahR]
    exact arithA _ _ _ _ _ _ _ _ hNl.le hNb hum ham Fa.hb hj'
  -- case B
  have hUR : U ≠ Rs S := fun h' => hA (by rw [h'])
  have hssub : U ⊂ Rs S := Finset.ssubset_iff_subset_ne.2 ⟨hU, hUR⟩
  have hcardlt := Finset.card_lt_card hssub
  have hu1 : (1 : ℚ) ≤ U.card := by exact_mod_cast hUne.card_pos
  have hru : (U.card : ℚ) + 1 ≤ pr S := by rw [pr]; exact_mod_cast hcardlt
  have hhu : (U.card : ℚ) + 1 ≤ h := by
    rw [hh]; exact_mod_cast card_rot_lb S U hS1 (hU.trans (Rs_sub S)) hUrot
  refine arithB _ _ (pf S) _ _ _ _ _ h (cl (Fs S)) _ _ rfl rfl hNl.le hNb hu1 hru Fa.ha Fa.hb
    hmpos hih hhu hia hjb Fa.hbhF Fa.hfF Fa.hf1 ?_
  by_cases hf1 : (Fs S).card = 1
  · left
    have hKF : KT (Fs S) = ⊥ := KT_single_ref _ (Fs_ref S) hf1
    refine ⟨?_, ?_, ?_⟩
    · rw [pb, cl, hKF, AddSubgroup.card_bot]; simp
    · rw [pa, cl, ← sup_bot_eq (KT (Rs S)), ← hKF, ← hKS', hKS, AddSubgroup.card_top,
        (natcard_A (A := A)), pm]
      field_simp
    · rw [hj, hi, hd, hh, cl, hKFU, hKF, sup_bot_eq]
  right
  have hf2 : (2 : ℚ) ≤ pf S := by
    rw [pf]; have : 2 ≤ (Fs S).card := by have := hFne.card_pos; omega
    exact_mod_cast this
  refine ⟨hf2, ?_⟩
  by_cases hq : U.card + 2 ≤ (Rs S).card
  · left; rw [pr]; exact_mod_cast hq
  right
  have hr_eq : (Rs S).card = U.card + 1 := by omega
  -- the missing rotation ι
  have hsd : (Rs S \ U).card = 1 := by rw [Finset.card_sdiff_of_subset hU]; omega
  obtain ⟨ι, hι⟩ := Finset.card_eq_one.1 hsd
  have hιR : ι ∈ Rs S := (Finset.mem_sdiff.1 (hι ▸ Finset.mem_singleton_self ι)).1
  have hιU : ι ∉ U := (Finset.mem_sdiff.1 (hι ▸ Finset.mem_singleton_self ι)).2
  have hRins : Rs S = insert ι U := by
    ext x
    rw [Finset.mem_insert]
    constructor
    · intro hx
      by_cases hxU : x ∈ U
      · exact Or.inr hxU
      · left; have : x ∈ Rs S \ U := Finset.mem_sdiff.2 ⟨hx, hxU⟩
        rw [hι] at this; exact Finset.mem_singleton.1 this
    · rintro (rfl | hx)
      · exact hιR
      · exact hU hx
  have hιrot : ι = rot ι.r := Dih.ext rfl (by simp [Rs_rot S ι hιR])
  set c0 := ι.r with hc0
  have hK0 : KT (Rs S) = KT U ⊔ AddSubgroup.zmultiples c0 := by
    rw [hRins, hιrot, KT_insert_rot]
  have hc0U : c0 ∉ KT U := by
    intro hc
    apply hA
    rw [hK0, sup_eq_left.2 ((AddSubgroup.zmultiples_le).2 hc)]
  have h2c0 : c0 + c0 = 0 := by
    have hinvι : rot (-c0) ∈ Rs S := by
      have h1 : ι⁻¹ ∈ S := hinv ι (Rs_sub S hιR)
      rw [hιrot, rot_inv] at h1
      exact Finset.mem_filter.2 ⟨h1, rfl⟩
    rw [hRins, Finset.mem_insert] at hinvι
    rcases hinvι with h1 | h1
    · rw [hιrot] at h1
      have h3 : -c0 = c0 := rot_injective h1
      calc c0 + c0 = -c0 + c0 := by rw [h3]
        _ = 0 := neg_add_cancel c0
    · exfalso; apply hc0U
      have : -c0 ∈ KT U := AddSubgroup.subset_closure (Or.inl h1)
      simpa using neg_mem this
  have hord : ∀ K : AddSubgroup A, addOrderOf ((c0 : A ⧸ K)) ≤ 2 := by
    intro K
    apply addOrderOf_le_of_nsmul_eq_zero (by norm_num)
    rw [← QuotientAddGroup.mk_nsmul, two_nsmul, h2c0, QuotientAddGroup.mk_zero]
  have hord2 : addOrderOf ((c0 : A ⧸ KT U)) = 2 := by
    have h1 := hord (KT U)
    have h2 : addOrderOf ((c0 : A ⧸ KT U)) ≠ 1 := by
      intro h; rw [AddMonoid.addOrderOf_eq_one_iff, QuotientAddGroup.eq_zero_iff] at h; exact hc0U h
    have h3 : 0 < addOrderOf ((c0 : A ⧸ KT U)) := addOrderOf_pos _
    omega
  have hhR : (cl (Rs S) : ℚ) = 2 * h := by
    rw [hh, cl, cl, hK0, card_sup_zmult, hord2]; push_cast; ring
  have hi2 : i = 2 * pa S := by
    rw [hi, pa, hhR]; field_simp
  refine ⟨by simp [pr, hr_eq], hi2, ?_⟩
  -- the subcases on [⟨U, K_F⟩ : K_F]
  obtain ⟨t, ht⟩ : cl (Fs S) ∣ cl (Fs S ∪ U) := cl_dvd Finset.subset_union_left
  have hFpos := cl_pos (Fs S)
  by_cases ht1 : t = 1
  · right
    rw [ht1, mul_one] at ht
    have hjb' : j = pb S := by rw [hj, hd, ht, pb]
    refine ⟨hjb', ?_⟩
    have heq : KT (Fs S ∪ U) = KT (Fs S) := by
      symm
      apply AddSubgroup.eq_of_le_of_card_ge (KT_mono Finset.subset_union_left)
      rw [← cl, ← cl, ht]
    have hUF : KT U ≤ KT (Fs S) := by rw [← heq, hKFU]; exact le_sup_left
    have htop : KT (Fs S) ⊔ AddSubgroup.zmultiples c0 = ⊤ := by
      rw [← hKS, hKS', hK0, sup_comm (KT U), sup_assoc, sup_eq_right.2 hUF, sup_comm]
    have hm2 : Fintype.card A ≤ 2 * cl (Fs S) := by
      have := card_sup_zmult (KT (Fs S)) c0
      rw [htop, AddSubgroup.card_top, (natcard_A (A := A))] at this
      rw [this, cl]
      exact Nat.mul_le_mul_right _ (hord _)
    rw [pb, pm, div_le_iff₀ (by exact_mod_cast hFpos)]
    exact_mod_cast hm2
  · left
    have ht2 : 2 ≤ t := by
      rcases Nat.lt_or_ge t 2 with h' | h'
      · interval_cases t
        · rw [mul_zero] at ht; exact absurd ht (cl_pos _).ne'
        · exact absurd rfl ht1
      · exact h'
    have hd2 : 2 * (cl (Fs S) : ℚ) ≤ d := by
      rw [hd, ht]; push_cast
      have h2t : (2 : ℚ) ≤ t := by exact_mod_cast ht2
      have hc : (0 : ℚ) ≤ cl (Fs S) := by positivity
      nlinarith
    rw [hj, pb]
    have hF0 : (0 : ℚ) < cl (Fs S) := by exact_mod_cast hFpos
    rw [mul_div_assoc', div_le_div_iff₀ hd0 hF0]
    nlinarith

include hS1 hKS hFne in
/-- **Condition (F)** -/
theorem ineqF (W : Finset (Dih A)) (hW : W ⊆ Fs S) :
    (W.card : ℚ) * tgt S ≤ lam S * (vD (Rs S ∪ W) - vD (Rs S)) + (1 - lam S) * vD W := by
  have Fa := facts S hS1 hFne
  obtain ⟨-, totF⟩ := totals S Fa
  have hWref : ∀ x ∈ W, x.s = true := fun x hx => Fs_ref S x (hW hx)
  rcases W.eq_empty_or_nonempty with hW0 | hWne
  · subst hW0
    have : vD (∅ : Finset (Dih A)) = 0 := by rw [vD_rot ∅ (by simp), cl_empty]; simp
    simp [this]
  have hWR : ∃ x ∈ Rs S ∪ W, x.s = true := by
    obtain ⟨x, hx⟩ := hWne; exact ⟨x, Finset.mem_union_right _ hx, hWref x hx⟩
  have hWW : ∃ x ∈ W, x.s = true := by obtain ⟨x, hx⟩ := hWne; exact ⟨x, hx, hWref x hx⟩
  set e := cl (Rs S ∪ W) with he
  set g := cl W with hg
  have he0 : (0 : ℚ) < e := by exact_mod_cast cl_pos _
  have hg0 : (0 : ℚ) < g := by exact_mod_cast cl_pos _
  set k := pm (A := A) / e with hk
  set l := pm (A := A) / g with hl
  have hv1 : vD (Rs S ∪ W) = 2 * pm (A := A) - k := by rw [vD_ref _ hWR, hk, pm]
  have hv2 : vD W = 2 * pm (A := A) - l := by rw [vD_ref _ hWW, hl, pm]
  rw [hv1, hv2, vD_Rs S]
  have hmpos := Fa.hm
  by_cases hWF : W = Fs S
  · -- equality
    have hk1 : k = 1 := by
      rw [hk, he, hWF, cl, show Rs S ∪ Fs S = S by rw [Finset.union_comm, Fs_union_Rs], hKS,
        AddSubgroup.card_top, (natcard_A (A := A)), pm]; field_simp
    have hl' : l = pb S := by rw [hl, hg, hWF, pb]
    rw [hk1, hl', hWF, ← pf, ← totF]
    linarith
  have hssub : W ⊂ Fs S := Finset.ssubset_iff_subset_ne.2 ⟨hW, hWF⟩
  have hw1 : (1 : ℚ) ≤ W.card := by exact_mod_cast hWne.card_pos
  have hwf : (W.card : ℚ) + 1 ≤ pf S := by rw [pf]; exact_mod_cast Finset.card_lt_card hssub
  have hlw : l * W.card ≤ pm (A := A) := by
    rw [hl, div_mul_eq_mul_div, div_le_iff₀ hg0]
    have : (W.card : ℚ) ≤ g := by rw [hg]; exact_mod_cast card_ref_lb W hWref hWne
    nlinarith
  have hka : k ≤ pa S := by
    rw [hk, pa]
    apply div_le_div_of_nonneg_left hmpos.le (by exact_mod_cast cl_pos _)
    exact_mod_cast cl_le (Finset.subset_union_left)
  by_cases hr : (Rs S).card = 0
  · -- no rotations: λ = 1
    have hlam : lam S = 1 := by rw [lam, if_pos hr]
    have hRe : Rs S = ∅ := Finset.card_eq_zero.1 hr
    have hpa : pa S = pm (A := A) := by rw [pa, hRe, cl_empty]; simp
    have hkl : k = l := by rw [hk, hl, he, hg, hRe, Finset.empty_union]
    rw [hlam, hpa, hkl, tgt, Fa.hcard, show pr S = 0 by rw [pr, hr]; simp, zero_add]
    have hf0 : 0 < pf S := by linarith
    rw [div_eq_mul_inv]
    have hl1 : l ≤ pm (A := A) := by nlinarith
    have key : (W.card : ℚ) * (2 * pm (A := A) - 1) ≤ pf S * (2 * pm (A := A) - l) := by
      have := mul_le_mul_of_nonneg_right hwf (by linarith : (0 : ℚ) ≤ 2 * pm (A := A) - l)
      nlinarith
    have : (W.card : ℚ) * ((2 * pm (A := A) - 1) * (pf S)⁻¹) =
        W.card * (2 * pm (A := A) - 1) / pf S := by field_simp
    rw [this, div_le_iff₀ hf0]
    nlinarith
  have hr1 : (1 : ℚ) ≤ pr S := by rw [pr]; exact_mod_cast Nat.one_le_iff_ne_zero.2 hr
  have hNl := Nl_pos (pm (A := A)) (pr S) (pf S) (pa S) (pb S) (cl (Fs S)) hr1 Fa.hf1 Fa.hb Fa.hF1
    Fa.hbhF Fa.hfF
  have hNb := Nb_nonneg (pm (A := A)) (pr S) (pf S) (pa S) (cl (Rs S)) (by linarith)
    (by linarith [Fa.hrR]) Fa.hf1 Fa.ha Fa.hahR
  have hD : 0 < pNl S + pNb S := by rw [pNl, pNb]; linarith
  have hlam : lam S = pNl S / (pNl S + pNb S) := by rw [lam, if_neg hr]
  have h1m : 1 - lam S = pNb S / (pNl S + pNb S) := by rw [hlam]; field_simp; ring
  have key := arithF (pm (A := A)) (pr S) (pf S) W.card (pa S) (pb S) k l (cl (Rs S)) (pNl S) (pNb S)
    rfl rfl hNl.le hNb hw1 hwf hr1 (by linarith [Fa.hrR]) Fa.hahR Fa.ha Fa.hb hmpos hka hlw
  have e : pf S * (lam S * (2 * pm (A := A) - k - (2 * pm (A := A) - 2 * pa S)) +
      (1 - lam S) * (2 * pm (A := A) - l)) - W.card * (pf S * tgt S) =
      (pNb S * (pf S * (2 * pm (A := A) - l) - W.card * (2 * pm (A := A) - pb S)) -
       pNl S * (W.card * (2 * pa S - 1) - pf S * (2 * pa S - k))) / (pNl S + pNb S) := by
    rw [← totF, h1m, hlam]; field_simp; ring
  have h2 : 0 ≤ pf S * (lam S * (2 * pm (A := A) - k - (2 * pm (A := A) - 2 * pa S)) +
      (1 - lam S) * (2 * pm (A := A) - l)) - W.card * (pf S * tgt S) := by
    rw [e]; exact div_nonneg (by linarith) hD.le
  have hpf0 : 0 < pf S := by linarith [Fa.hf1]
  nlinarith

end Ineq

end FTDih

-- ===== DihMain.lean =====

/-!
# Theorem 7: Fair Traversal for Cayley graphs of generalized dihedral groups

`ft_dih`: for every finite abelian group `A` and every `S ⊆ Dih A` with `G.Adj x y ↔ x⁻¹ * y ∈ S`
and `G` connected, the #339 conclusion holds. `main_dih_cayley` is the #339 statement restricted to
graphs that admit such a labelling (conclusion word for word), and
`isVertexTransitive_of_group_labelling` shows that every such graph is vertex-transitive.

Proof: Weber (FTAbelian.weber) for the blended game `λ·v₁ + (1-λ)·v₂`; its greedy vectors are
`λ·(rotations-first greedy) + (1-λ)·(reflections-first greedy)`, both realised by Hamiltonian
paths (`real1`, `real2`); the uniform vector lies in the blended anticore (`ineqR`, `ineqF`);
`assemble` clears denominators and takes all left translates.
-/

open Finset

namespace FTDih

section Greedy
variable {ι : Type*} [DecidableEq ι]

lemma greedy_lin (f g : Finset ι → ℚ) (t u : ℚ) (P : Finset ι) (L : List ι) :
    FTAbelian.greedy (fun X => t * f X + u * g X) P L =
      t • FTAbelian.greedy f P L + u • FTAbelian.greedy g P L := by
  induction L generalizing P with
  | nil => simp
  | cons a L ih =>
    rw [FTAbelian.greedy_cons, FTAbelian.greedy_cons, FTAbelian.greedy_cons, ih]
    funext k
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
    split_ifs <;> ring

lemma greedy_shift (k : Finset ι → ℚ) (C Q : Finset ι) (L : List ι) :
    FTAbelian.greedy (fun Y => k (C ∪ Y) - k C) Q L = FTAbelian.greedy k (C ∪ Q) L := by
  induction L generalizing Q with
  | nil => simp
  | cons a L ih =>
    rw [FTAbelian.greedy_cons, FTAbelian.greedy_cons, ih, Finset.union_insert]
    congr 2
    ring

lemma greedy_sep (p : ι → Prop) [DecidablePred p] (g h : Finset ι → ℚ) (P : Finset ι)
    (L : List ι) :
    FTAbelian.greedy (fun X => g (X.filter p) + h (X.filter (fun x => ¬ p x))) P L =
      FTAbelian.greedy g (P.filter p) (L.filter (fun x => decide (p x))) +
        FTAbelian.greedy h (P.filter (fun x => ¬ p x)) (L.filter (fun x => decide (¬ p x))) := by
  induction L generalizing P with
  | nil => simp
  | cons a L ih =>
    rw [FTAbelian.greedy_cons, ih]
    by_cases hp : p a
    · rw [List.filter_cons_of_pos (by simpa using hp), List.filter_cons_of_neg (by simpa using hp),
        FTAbelian.greedy_cons, Finset.filter_insert, if_pos hp, Finset.filter_insert,
        if_neg (not_not.2 hp)]
      rw [show g (insert a (P.filter p)) + h (P.filter (fun x => ¬ p x)) -
          (g (P.filter p) + h (P.filter (fun x => ¬ p x))) =
          g (insert a (P.filter p)) - g (P.filter p) by ring]
      abel
    · rw [List.filter_cons_of_neg (by simpa using hp), List.filter_cons_of_pos (by simpa using hp),
        FTAbelian.greedy_cons (L := List.filter _ L), Finset.filter_insert, if_neg hp,
        Finset.filter_insert, if_pos hp]
      rw [show g (P.filter p) + h (insert a (P.filter (fun x => ¬ p x))) -
          (g (P.filter p) + h (P.filter (fun x => ¬ p x))) =
          h (insert a (P.filter (fun x => ¬ p x))) - h (P.filter (fun x => ¬ p x)) by ring]
      abel

end Greedy

section Main
variable {A : Type} [AddCommGroup A] [Fintype A] [DecidableEq A]

/-- rotations-first game -/
noncomputable def v1 (S : Finset (Dih A)) (X : Finset (Dih A)) : ℚ :=
  vD (X.filter (fun x => x.s = false)) +
    (vD (Rs S ∪ X.filter (fun x => ¬ x.s = false)) - vD (Rs S))
/-- reflections-first game -/
noncomputable def v2 (S : Finset (Dih A)) (X : Finset (Dih A)) : ℚ :=
  (vD (Fs S ∪ X.filter (fun x => x.s = false)) - vD (Fs S)) +
    vD (X.filter (fun x => ¬ x.s = false))

lemma lR_eq (L : List (Dih A)) : lR L = L.filter (fun x => decide (x.s = false)) := by
  apply List.filter_congr; intro x _; cases x.s <;> rfl

lemma lF_eq (L : List (Dih A)) : lF L = L.filter (fun x => decide (¬ x.s = false)) := by
  apply List.filter_congr; intro x _; cases x.s <;> rfl

lemma toFinset_lR (S : Finset (Dih A)) (L : List (Dih A)) (hL : L.toFinset = S) :
    (lR L).toFinset = Rs S := by
  ext x; simp only [List.mem_toFinset, lR, List.mem_filter, Rs, Finset.mem_filter, ← hL,
    Bool.not_eq_true']

lemma toFinset_lF (S : Finset (Dih A)) (L : List (Dih A)) (hL : L.toFinset = S) :
    (lF L).toFinset = Fs S := by
  ext x; simp only [List.mem_toFinset, lF, List.mem_filter, Fs, Finset.mem_filter, ← hL]

lemma greedy_v1 (S : Finset (Dih A)) (L : List (Dih A)) (hL : L.toFinset = S) :
    FTAbelian.greedy (v1 S) ∅ L = FTAbelian.greedy vD ∅ (lR L ++ lF L) := by
  have h1 : FTAbelian.greedy (v1 S) ∅ L =
      FTAbelian.greedy vD ((∅ : Finset (Dih A)).filter (fun x => x.s = false))
        (L.filter (fun x => decide (x.s = false))) +
      FTAbelian.greedy (fun Y => vD (Rs S ∪ Y) - vD (Rs S))
        ((∅ : Finset (Dih A)).filter (fun x => ¬ x.s = false))
        (L.filter (fun x => decide (¬ x.s = false))) :=
    greedy_sep (fun x : Dih A => x.s = false) vD (fun Y => vD (Rs S ∪ Y) - vD (Rs S)) ∅ L
  rw [h1, greedy_shift, FTAbelian.greedy_append, ← lR_eq, ← lF_eq, toFinset_lR S L hL]
  simp

lemma greedy_v2 (S : Finset (Dih A)) (L : List (Dih A)) (hL : L.toFinset = S) :
    FTAbelian.greedy (v2 S) ∅ L = FTAbelian.greedy vD ∅ (lF L ++ lR L) := by
  have h1 : FTAbelian.greedy (v2 S) ∅ L =
      FTAbelian.greedy (fun Y => vD (Fs S ∪ Y) - vD (Fs S))
        ((∅ : Finset (Dih A)).filter (fun x => x.s = false))
        (L.filter (fun x => decide (x.s = false))) +
      FTAbelian.greedy vD ((∅ : Finset (Dih A)).filter (fun x => ¬ x.s = false))
        (L.filter (fun x => decide (¬ x.s = false))) :=
    greedy_sep (fun x : Dih A => x.s = false) (fun Y => vD (Fs S ∪ Y) - vD (Fs S)) vD ∅ L
  rw [h1, greedy_shift, FTAbelian.greedy_append, ← lR_eq, ← lF_eq, toFinset_lF S L hL, add_comm]
  simp

lemma pt_closed (S : Finset (Dih A)) (b₁ : A) (hb₁ : ref b₁ ∈ S) (x s : Dih A) (hx : PT S b₁ x)
    (hs : s ∈ S) : PT S b₁ (x * s) := by
  have hR : hasRef S = true := hasRef_of_mem S b₁ hb₁
  have hrot : ∀ c, rot c ∈ S → c ∈ KT S := fun c hc => AddSubgroup.subset_closure (Or.inl hc)
  have href : ∀ c, ref c ∈ S → c - b₁ ∈ KT S := fun c hc =>
    AddSubgroup.subset_closure (Or.inr ⟨c, hc, b₁, hb₁, rfl⟩)
  rcases eq_rot_or_ref x with hx' | hx' <;> rcases eq_rot_or_ref s with hs' | hs' <;>
    rw [hx'] at hx <;> rw [hs'] at hs <;> rw [hx', hs']
  · rw [rot_mul_rot, pt_rot]; rw [pt_rot] at hx; exact add_mem hx (hrot _ hs)
  · rw [rot_mul_ref, pt_ref]; rw [pt_rot] at hx
    exact ⟨hR, by rw [add_sub_assoc]; exact add_mem hx (href _ hs)⟩
  · rw [ref_mul_rot, pt_ref]; rw [pt_ref] at hx
    exact ⟨hR, by rw [show x.r - s.r - b₁ = (x.r - b₁) - s.r by abel]; exact sub_mem hx.2 (hrot _ hs)⟩
  · rw [ref_mul_ref, pt_rot]; rw [pt_ref] at hx
    rw [show x.r - s.r = (x.r - b₁) - (s.r - b₁) by abel]
    exact sub_mem hx.2 (href _ hs)

/-- **Theorem 7 (Fair Traversal for Cayley graphs of generalized dihedral groups).** -/
theorem ft_dih (S : Finset (Dih A)) (G : SimpleGraph (Dih A))
    (hG : ∀ x y, G.Adj x y ↔ x⁻¹ * y ∈ S) (hc : G.Connected) :
    ∃ (r k : ℕ), 0 < r ∧ 0 < k ∧
      ∃ (a b : Fin r → Dih A) (P : ∀ i, G.Walk (a i) (b i)),
        (∀ i, (P i).IsHamiltonian) ∧
        ∀ e ∈ G.edgeSet, (Finset.univ.filter fun i => e ∈ (P i).edges).card = k := by
  classical
  have hinv := inv_mem_of S G hG
  have hS1 := one_not_mem_of S G hG
  have hF : ∃ x ∈ S, x.s = true := by
    by_contra hno
    push_neg at hno
    have := all_of_connected S G hG hc (fun g => g.s = false) rfl (fun x s hx hs => by
      have := hno s hs
      simp only [Bool.not_eq_true] at this
      simp [hx, this]) (ref 0)
    simp at this
  obtain ⟨x0, hx0S, hx0s⟩ := hF
  have hx0 : x0 = ref x0.r := by
    rcases eq_rot_or_ref x0 with h | h
    · rw [h] at hx0s; exact absurd hx0s (by simp)
    · exact h
  set b₁ := x0.r
  have hb₁ : ref b₁ ∈ S := hx0 ▸ hx0S
  have hall : ∀ b, ref b ∈ S → ∀ g, PT S b g := fun b hb =>
    all_of_connected S G hG hc (PT S b) (by simp [PT, XP, one_eq_rot])
      (fun x s hx hs => pt_closed S b hb x s hx hs)
  have hKS : KT S = ⊤ := by
    rw [eq_top_iff]
    intro a _
    have := hall b₁ hb₁ (rot a)
    simpa [PT, XP] using this
  have hFne : (Fs S).Nonempty := ⟨x0, Finset.mem_filter.2 ⟨hx0S, hx0s⟩⟩
  have Fa := facts S hS1 hFne
  -- the blending weight
  set t := lam S with ht
  have ht01 : 0 ≤ t ∧ t ≤ 1 := by
    by_cases hr : (Rs S).card = 0
    · rw [ht, lam, if_pos hr]; norm_num
    · have hr1 : (1 : ℚ) ≤ pr S := by rw [pr]; exact_mod_cast Nat.one_le_iff_ne_zero.2 hr
      have hNl := Nl_pos (pm (A := A)) (pr S) (pf S) (pa S) (pb S) (cl (Fs S)) hr1 Fa.hf1 Fa.hb
        Fa.hF1 Fa.hbhF Fa.hfF
      have hNb := Nb_nonneg (pm (A := A)) (pr S) (pf S) (pa S) (cl (Rs S)) (by linarith)
        (by linarith [Fa.hrR]) Fa.hf1 Fa.ha Fa.hahR
      have hD : 0 < pNl S + pNb S := by rw [pNl, pNb]; linarith
      rw [ht, lam, if_neg hr]
      refine ⟨div_nonneg (by rw [pNl]; linarith) hD.le, ?_⟩
      rw [div_le_one hD]; rw [pNl, pNb] at *; linarith
  -- the target and the blended game
  set x : Dih A → ℚ := fun s => if s ∈ S then tgt S else 0 with hxdef
  set vl : Finset (Dih A) → ℚ := fun X => t * v1 S X + (1 - t) * v2 S X with hvl
  have hv0 : vD (∅ : Finset (Dih A)) = 0 := by rw [vD_rot ∅ (by simp), cl_empty]; simp
  have hvl0 : vl ∅ = 0 := by simp [hvl, v1, v2, hv0]
  have hSR : S.filter (fun x => x.s = false) = Rs S := rfl
  have hSF : S.filter (fun x => ¬ x.s = false) = Fs S := by
    apply Finset.filter_congr; intro x _; cases x.s <;> simp
  have hvS : vD S = 2 * pm (A := A) - 1 := vD_S S hKS ⟨x0, hx0S, hx0s⟩
  have hadm : FTAbelian.Adm vl ∅ S x := by
    refine ⟨fun j hj => by simp [hxdef, hj], fun U hU => ?_, ?_⟩
    · rw [Finset.empty_union, hvl0, sub_zero,
        Finset.sum_congr rfl (fun j hj => if_pos (hU hj)), Finset.sum_const, nsmul_eq_mul]
      have hUR : U.filter (fun x => x.s = false) ⊆ Rs S := by
        intro y hy; rw [Finset.mem_filter] at hy; exact Finset.mem_filter.2 ⟨hU hy.1, hy.2⟩
      have hUF : U.filter (fun x => ¬ x.s = false) ⊆ Fs S := by
        intro y hy; rw [Finset.mem_filter] at hy
        exact Finset.mem_filter.2 ⟨hU hy.1, by simpa using hy.2⟩
      have h1 := ineqR S hS1 hinv hKS hFne _ hUR
      have h2 := ineqF S hS1 hKS hFne _ hUF
      have hc : (U.card : ℚ) = (U.filter (fun x => x.s = false)).card +
          (U.filter (fun x => ¬ x.s = false)).card := by
        exact_mod_cast (Finset.card_filter_add_card_filter_not _).symm
      simp only [hvl, v1, v2]
      rw [hc]
      rw [← ht] at h1 h2
      nlinarith
    · rw [Finset.empty_union, hvl0, sub_zero,
        Finset.sum_congr rfl (fun j hj => if_pos hj), Finset.sum_const, nsmul_eq_mul]
      simp only [hvl, v1, v2, hSR, hSF]
      rw [Finset.union_comm (Rs S) (Fs S), Fs_union_Rs, hvS, tgt]
      have : (S.card : ℚ) ≠ 0 := by rw [Fa.hcard]; linarith [Fa.hf1, pr_nonneg S]
      field_simp
      ring
  have hx := FTAbelian.weber vl S.card S rfl ∅ x hadm
  have hsub : FTAbelian.Gset vl ∅ S ⊆ convexHull ℚ (Real S) := by
    rintro y ⟨L, -, hLS, rfl⟩
    rw [hvl, greedy_lin, greedy_v1 S L hLS, greedy_v2 S L hLS]
    exact convex_convexHull ℚ _
      (subset_convexHull ℚ _ (real1 S L hLS ⟨x0, hx0S, hx0s⟩ hall))
      (subset_convexHull ℚ _ (real2 S hinv L hLS ⟨x0, hx0S, hx0s⟩ hall))
      ht01.1 (by linarith [ht01.2]) (by ring)
  have hx' : x ∈ convexHull ℚ (Real S) := convexHull_min hsub (convex_convexHull ℚ _) hx
  have htgt : 0 < tgt S := by
    rw [tgt]
    apply div_pos
    · linarith [Fa.hm, show (1 : ℚ) ≤ pm (A := A) by rw [pm]; exact_mod_cast Fintype.card_pos]
    · rw [Fa.hcard]; linarith [Fa.hf1, pr_nonneg S]
  refine assemble S G hG x hx' (2 * tgt S) (by linarith) (fun s hs => ?_) _ hx0S
  simp only [hxdef, if_pos hs, if_pos (hinv s hs)]
  ring

/-- **Fair Traversal for every connected graph with a labelling by a generalized dihedral group**
`e : V ≃ Dih A`, `G.Adj u v ↔ (e u)⁻¹ * e v ∈ S` (i.e. `G ≅ Cay(Dih A, S)`). -/
theorem fair_traversal_of_dih_labelling {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (A : Type) [AddCommGroup A] [Fintype A] [DecidableEq A] (e : V ≃ Dih A)
    (S : Finset (Dih A)) (hG : ∀ u v, G.Adj u v ↔ (e u)⁻¹ * e v ∈ S) (hc : G.Connected) :
    ∃ (r k : ℕ), 0 < r ∧ 0 < k ∧
      ∃ (a b : Fin r → V) (P : ∀ i, G.Walk (a i) (b i)),
        (∀ i, (P i).IsHamiltonian) ∧
        ∀ e' ∈ G.edgeSet, (Finset.univ.filter fun i => e' ∈ (P i).edges).card = k :=
  transfer G e S hG (fun G' hG' hc' => ft_dih S G' hG' hc') hc

/-- The vertex-transitivity notion of the Left to Solve statement (copied verbatim). -/
def IsVertexTransitive {V : Type*} (G : SimpleGraph V) : Prop :=
  ∀ u v : V, ∃ φ : G ≃g G, φ u = v

/-- Graphs with a group labelling (Cayley graphs) are vertex-transitive (left translations). -/
lemma isVertexTransitive_of_group_labelling {V : Type} (G : SimpleGraph V) (Γ : Type) [Group Γ]
    (e : V ≃ Γ) (S : Set Γ) (hG : ∀ u v, G.Adj u v ↔ (e u)⁻¹ * e v ∈ S) :
    IsVertexTransitive G := by
  intro u v
  let τ : V ≃ V := (e.trans (Equiv.mulLeft (e v * (e u)⁻¹))).trans e.symm
  refine ⟨{ toEquiv := τ, map_rel_iff' := ?_ }, ?_⟩
  · intro a b
    simp only [τ, Equiv.trans_apply, Equiv.coe_mulLeft, Equiv.apply_symm_apply, hG]
    rw [show (e v * (e u)⁻¹ * e a)⁻¹ * (e v * (e u)⁻¹ * e b) = (e a)⁻¹ * e b by group]
  · simp [τ]

/-- **The Left to Solve statement of Fair Traversal (`gillibert-fair-traversal`, PR #339),
restricted to Cayley graphs of generalized dihedral groups** `Dih A = A ⋊ ⟨τ⟩` (`A` finite abelian,
`τ a τ = -a`), any connection set. Same conclusion, word for word. -/
theorem main_dih_cayley :
    ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V),
      G.Connected →
      (∃ (A : Type) (_ : AddCommGroup A) (_ : Fintype A) (_ : DecidableEq A) (e : V ≃ Dih A)
        (S : Finset (Dih A)), ∀ u v, G.Adj u v ↔ (e u)⁻¹ * e v ∈ S) →
      2 ≤ Fintype.card V →
      ∃ (r k : ℕ), 0 < r ∧ 0 < k ∧
        ∃ (a b : Fin r → V) (P : ∀ i, G.Walk (a i) (b i)),
          (∀ i, (P i).IsHamiltonian) ∧
          ∀ e ∈ G.edgeSet, (Finset.univ.filter fun i => e ∈ (P i).edges).card = k := by
  intro V _ _ G hc hcay _
  obtain ⟨A, _, _, _, e, S, hG⟩ := hcay
  exact fair_traversal_of_dih_labelling G A e S hG hc

end Main

end FTDih

#print axioms FTDih.main_dih_cayley
#print axioms FTDih.isVertexTransitive_of_group_labelling

-- ===== DihExtra.lean =====

/-!
# Corollaries: Mathlib's dihedral groups `DihedralGroup n` and dicyclic groups `QuaternionGroup n`

* `dihZMod n : Dih (ZMod n) ≃* DihedralGroup n`, hence `main_dihedralGroup_cayley`: the #339
  conclusion for every connected Cayley graph of `DihedralGroup n` (`n ≥ 1`).
* `main_quaternionGroup_cayley`: the same for every connected Cayley graph of the dicyclic group
  `QuaternionGroup n` (order `4n`; generalized quaternion groups for `n` a power of 2). Its Cayley
  graphs are literally Cayley graphs of `Dih (ZMod (2n))` (FT-DIHEDRAL.md Corollary 7′): the vertex
  bijection `a i ↦ rot i`, `xa i ↦ ref (-i)` carries `Cay(Q, S)` onto `Cay(Dih, σ(S))`.
-/

open Finset

namespace FTDih

lemma mk_mul_mk {A : Type} [AddCommGroup A] (a b : A) (i j : Bool) :
    (⟨a, i⟩ : Dih A) * ⟨b, j⟩ = ⟨a + sg i b, xor i j⟩ := rfl

/-- the elements of `Dih (ZMod n)` as elements of Mathlib's `DihedralGroup n` -/
def toDG (n : ℕ) : Dih (ZMod n) → DihedralGroup n
  | ⟨a, false⟩ => DihedralGroup.r a
  | ⟨b, true⟩ => DihedralGroup.sr (-b)

/-- inverse map -/
def ofDG (n : ℕ) : DihedralGroup n → Dih (ZMod n)
  | DihedralGroup.r i => ⟨i, false⟩
  | DihedralGroup.sr i => ⟨-i, true⟩

/-- `Dih (ZMod n)` is Mathlib's dihedral group of order `2n`. -/
def dihZMod (n : ℕ) : Dih (ZMod n) ≃* DihedralGroup n where
  toFun := toDG n
  invFun := ofDG n
  left_inv x := by rcases x with ⟨a, i⟩; cases i <;> simp [toDG, ofDG]
  right_inv g := by cases g <;> simp [toDG, ofDG]
  map_mul' x y := by
    rcases x with ⟨a, i⟩; rcases y with ⟨b, j⟩
    cases i <;> cases j <;>
      simp only [mk_mul_mk, toDG, sg_false, sg_true, Bool.xor_false, Bool.false_xor,
        Bool.xor_true, Bool.true_xor, Bool.not_false, Bool.not_true,
        DihedralGroup.r_mul_r, DihedralGroup.r_mul_sr, DihedralGroup.sr_mul_r,
        DihedralGroup.sr_mul_sr] <;> congr 1 <;> ring

/-- **Fair Traversal for every connected Cayley graph of the dihedral group `DihedralGroup n`**
(Mathlib's dihedral group of order `2n`), as a labelling `e : V ≃ DihedralGroup n`. -/
theorem main_dihedralGroup_cayley (n : ℕ) [NeZero n] :
    ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V),
      G.Connected →
      (∃ (e : V ≃ DihedralGroup n) (S : Finset (DihedralGroup n)),
        ∀ u v, G.Adj u v ↔ (e u)⁻¹ * e v ∈ S) →
      2 ≤ Fintype.card V →
      ∃ (r k : ℕ), 0 < r ∧ 0 < k ∧
        ∃ (a b : Fin r → V) (P : ∀ i, G.Walk (a i) (b i)),
          (∀ i, (P i).IsHamiltonian) ∧
          ∀ e ∈ G.edgeSet, (Finset.univ.filter fun i => e ∈ (P i).edges).card = k := by
  intro V _ _ G hc hcay _
  obtain ⟨e, S, hG⟩ := hcay
  let φ := dihZMod n
  refine fair_traversal_of_dih_labelling G (ZMod n) (e.trans φ.symm.toEquiv)
    (S.map φ.symm.toEquiv.toEmbedding) ?_ hc
  have key : ∀ g h : DihedralGroup n, (φ.symm.toEquiv).symm ((φ.symm g)⁻¹ * φ.symm h) = g⁻¹ * h := by
    intro g h
    change φ ((φ.symm g)⁻¹ * φ.symm h) = g⁻¹ * h
    simp
  intro u v
  rw [hG, Finset.mem_map_equiv]
  simp only [Equiv.trans_apply]
  rw [show φ.symm.toEquiv (e u) = φ.symm (e u) from rfl,
    show φ.symm.toEquiv (e v) = φ.symm (e v) from rfl, key]

/-! ## Dicyclic groups -/

lemma two_n_eq_zero (n : ℕ) : ((n : ZMod (2 * n)) + n) = 0 := by
  rw [← two_mul]; exact_mod_cast ZMod.natCast_self (2 * n)

lemma q_inv_a {n : ℕ} (i : ZMod (2 * n)) :
    (QuaternionGroup.a i : QuaternionGroup n)⁻¹ = QuaternionGroup.a (-i) := by
  apply inv_eq_of_mul_eq_one_right
  rw [QuaternionGroup.a_mul_a, add_neg_cancel, QuaternionGroup.a_zero]

lemma q_inv_xa {n : ℕ} (i : ZMod (2 * n)) :
    (QuaternionGroup.xa i : QuaternionGroup n)⁻¹ = QuaternionGroup.xa ((n : ZMod (2 * n)) + i) := by
  apply inv_eq_of_mul_eq_one_right
  rw [QuaternionGroup.xa_mul_xa, ← QuaternionGroup.a_zero]
  congr 1
  rw [show (n : ZMod (2 * n)) + ((n : ZMod (2 * n)) + i) - i = (n : ZMod (2 * n)) + n by ring,
    two_n_eq_zero]

/-- vertex bijection `QuaternionGroup n → Dih (ZMod (2n))` -/
def ofQ (n : ℕ) : QuaternionGroup n → Dih (ZMod (2 * n))
  | QuaternionGroup.a i => rot i
  | QuaternionGroup.xa i => ref (-i)

/-- its inverse -/
def toQ (n : ℕ) : Dih (ZMod (2 * n)) → QuaternionGroup n
  | ⟨a, false⟩ => QuaternionGroup.a a
  | ⟨b, true⟩ => QuaternionGroup.xa (-b)

@[simp] lemma ofQ_a (n : ℕ) (i : ZMod (2 * n)) : ofQ n (QuaternionGroup.a i) = rot i := rfl
@[simp] lemma ofQ_xa (n : ℕ) (i : ZMod (2 * n)) : ofQ n (QuaternionGroup.xa i) = ref (-i) := rfl
@[simp] lemma toQ_rot (n : ℕ) (i : ZMod (2 * n)) : toQ n (rot i) = QuaternionGroup.a i := rfl
@[simp] lemma toQ_ref (n : ℕ) (i : ZMod (2 * n)) : toQ n (ref i) = QuaternionGroup.xa (-i) := rfl

def qEquiv (n : ℕ) : QuaternionGroup n ≃ Dih (ZMod (2 * n)) where
  toFun := ofQ n
  invFun := toQ n
  left_inv g := by cases g <;> simp
  right_inv x := by
    rcases eq_rot_or_ref x with h | h <;> rw [h] <;> simp

/-- adjacency transfer (FT-DIHEDRAL.md Corollary 7′): for `S` closed under inverses,
`(ofQ x)⁻¹ * ofQ y ∈ σ(S) ↔ x⁻¹ * y ∈ S` -/
lemma adj_transfer (n : ℕ) (S : Finset (QuaternionGroup n)) (hinv : ∀ s ∈ S, s⁻¹ ∈ S)
    (x y : QuaternionGroup n) :
    (ofQ n x)⁻¹ * ofQ n y ∈ S.map (qEquiv n).toEmbedding ↔ x⁻¹ * y ∈ S := by
  have hmem : ∀ z : Dih (ZMod (2 * n)), z ∈ S.map (qEquiv n).toEmbedding ↔ toQ n z ∈ S := by
    intro z
    rw [Finset.mem_map_equiv]
    rfl
  rw [hmem]
  cases x with
  | a i =>
    cases y with
    | a j =>
      rw [ofQ_a, ofQ_a, rot_inv, rot_mul_rot, toQ_rot, q_inv_a, QuaternionGroup.a_mul_a]
    | xa j =>
      rw [ofQ_a, ofQ_xa, rot_inv, rot_mul_ref, toQ_ref, q_inv_a, QuaternionGroup.a_mul_xa]
      rw [show -(-i + -j) = j - -i by ring]
  | xa i =>
    cases y with
    | a j =>
      -- here the two labels differ by the central element `a n`; use `S = S⁻¹`
      have e1 : toQ n ((ofQ n (QuaternionGroup.xa i))⁻¹ * ofQ n (QuaternionGroup.a j)) =
          QuaternionGroup.xa (i + j) := by
        rw [ofQ_xa, ofQ_a, ref_inv, ref_mul_rot, toQ_ref]; congr 1; ring
      have e2 : (QuaternionGroup.xa i)⁻¹ * QuaternionGroup.a j =
          QuaternionGroup.xa ((n : ZMod (2 * n)) + i + j) := by
        rw [q_inv_xa, QuaternionGroup.xa_mul_a]
      rw [e1, e2]
      have e3 : (QuaternionGroup.xa ((n : ZMod (2 * n)) + i + j))⁻¹ =
          QuaternionGroup.xa (i + j) := by
        rw [q_inv_xa]; congr 1
        rw [show (n : ZMod (2 * n)) + ((n : ZMod (2 * n)) + i + j) =
          ((n : ZMod (2 * n)) + n) + (i + j) by ring, two_n_eq_zero, zero_add]
      have e4 : (QuaternionGroup.xa (i + j))⁻¹ =
          QuaternionGroup.xa ((n : ZMod (2 * n)) + i + j) := by
        rw [q_inv_xa]; congr 1; ring
      constructor
      · intro h; have := hinv _ h; rwa [e4] at this
      · intro h; have := hinv _ h; rwa [e3] at this
    | xa j =>
      rw [ofQ_xa, ofQ_xa, ref_inv, ref_mul_ref, toQ_rot, q_inv_xa, QuaternionGroup.xa_mul_xa]
      rw [show (n : ZMod (2 * n)) + j - ((n : ZMod (2 * n)) + i) = -i - -j by ring]

/-- **Fair Traversal for every connected Cayley graph of the dicyclic group `QuaternionGroup n`**
(order `4n`; e.g. the generalized quaternion groups `Q_{2^k}`). -/
theorem main_quaternionGroup_cayley (n : ℕ) [NeZero n] :
    ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V),
      G.Connected →
      (∃ (e : V ≃ QuaternionGroup n) (S : Finset (QuaternionGroup n)),
        ∀ u v, G.Adj u v ↔ (e u)⁻¹ * e v ∈ S) →
      2 ≤ Fintype.card V →
      ∃ (r k : ℕ), 0 < r ∧ 0 < k ∧
        ∃ (a b : Fin r → V) (P : ∀ i, G.Walk (a i) (b i)),
          (∀ i, (P i).IsHamiltonian) ∧
          ∀ e ∈ G.edgeSet, (Finset.univ.filter fun i => e ∈ (P i).edges).card = k := by
  intro V _ _ G hc hcay _
  obtain ⟨e, S, hG⟩ := hcay
  -- `S` is closed under inverses (the graph is symmetric)
  have hinv : ∀ s ∈ S, s⁻¹ ∈ S := by
    intro s hs
    have h1 : G.Adj (e.symm 1) (e.symm s) := (hG _ _).2 (by simpa using hs)
    have := (hG _ _).1 h1.symm
    simpa using this
  refine fair_traversal_of_dih_labelling G (ZMod (2 * n)) (e.trans (qEquiv n))
    (S.map (qEquiv n).toEmbedding) ?_ hc
  intro u v
  rw [hG]
  exact (adj_transfer n S hinv (e u) (e v)).symm

end FTDih

#print axioms FTDih.main_dihedralGroup_cayley
#print axioms FTDih.main_quaternionGroup_cayley
