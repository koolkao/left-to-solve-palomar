/-
Copyright 2026 Ming-Chih Kao. Licensed under the Apache License, Version 2.0;
see the LICENSE file at the root of this repository.
Ported from github.com/koolkao/gillibert-fair-traversal-abelian (v1.7.0, commit
06c3a8732759afca38331762b76113135e475ac6) to Lean v4.36.0 and the module system.
-/
module

public import Mathlib
public import FairTraversal.FTDihedral

/-!
# Theorem 8 (Lean): Fair Traversal for Cayley graphs of the index-2 extensions Γ(A, k, z)

New in v1.3.1. `Γ(A, k, z) = A ∪ Aτ` with `A` finite abelian, `τ a τ⁻¹ = k a`, `τ² = z`, where
`k • k • a = a` for all `a` and `k • z = z`; modelled as `FTDih.Pw A k z` (data `A × Bool`). Main theorems
(namespace `FTDih`); the conclusion of each Fair Traversal theorem below is the conclusion of the Left to Solve
statement of Fair Traversal (#339), word for word (up to the name of the bound multiplicity):

* `ft_pow`: Fair Traversal for every connected Cayley graph `Cay(Γ(A, k, z), S)` under condition (O):
  `∃ ε = ±1, ∀ a : A, Odd (addOrderOf a) → k • a = ε • a` (k ≡ ε modulo the odd part of exp A);
* `main_pow_cayley`: the #339 form (a labelling `V ≃ Pw A k z`, `u ~ v ↔ (e u)⁻¹ * e v ∈ S`);
* `main_semidihedral_cayley n`, `main_modular_cayley n`: the models `Γ(ℤ_{2^(n+2)}, 2^(n+1) ∓ 1, 0)` of order
  `2^(n+3)`, for which (O) is automatic (`O_of_two_group`); for `n ≥ 1` these are the semidihedral and modular
  groups (`n = 1`: SD₁₆, M₁₆); for `n = 0` they are `C₄ × C₂` and the dihedral group of order 8;
* `pw_relations` (an algebraic lemma, not a Fair Traversal theorem): the defining relations
  `ρ^(2^(n+2)) = 1`, `τ² = 1`, `τ ρ τ⁻¹ = ρ^k` hold in these models.

Not covered in Lean: the sharper form of Theorem 8 (NOTE.md §8.7) and Corollary 8′ for abstract groups
(it would need: every group of order 2^a p^b with a cyclic subgroup of index 2 is isomorphic to some
Γ(C, k, z)); only the explicit models are covered.

This file uses `FTDihedral.lean` (Theorem 7: the dihedral game `vD`, the inequalities, the realisation
steps) and, through it, `FTAbelian.lean` (Weber's lemma). In the authors' workspace it was compiled as one
4,894-line file (`FTPowerAll.lean`) containing verbatim copies of `FTAbelian.lean` and of the Theorem 7
modules except `DihExtra`; here those copies are replaced by `import FTDihedral`, and nothing else is changed.
-/

@[expose] public section

-- ===== FTPowerBase.lean =====

/-!
# Theorem 8 (FT-POWER.md): the groups Γ(A, k, z)

`Pw A k z = A × Bool` with `(a,0)(b,0) = (a+b,0)`, `(a,0)(b,1) = (a+b,1)`, `(a,1)(b,0) = (a+k•b,1)`,
`(a,1)(b,1) = (a+k•b+z,0)`; a group when `k•k•a = a` for all `a` and `k•z = z` (Fact instances).
`toD : Pw A k z ≃ Dih A` is the identity on the underlying data; vertex sets, the game `vD` and
the inequalities are taken from the Dih development through it.
-/

open Finset

namespace FTDih

@[ext] structure Pw (A : Type) (k : ℤ) (z : A) where
  r : A
  s : Bool
deriving DecidableEq

section PwGroup
variable {A : Type} [AddCommGroup A] {k : ℤ} {z : A}

/-- `tw false b = b`, `tw true b = k • b` -/
def tw (k : ℤ) : Bool → A → A
  | false, b => b
  | true, b => k • b

/-- the `z`-correction -/
def zc (z : A) : Bool → Bool → A
  | true, true => z
  | _, _ => 0

@[simp] lemma tw_false (b : A) : tw k false b = b := rfl
@[simp] lemma tw_true (b : A) : tw k true b = k • b := rfl
@[simp] lemma zc_tt : zc z true true = z := rfl
@[simp] lemma zc_f (j : Bool) : zc z false j = 0 := rfl
@[simp] lemma zc_tf : zc z true false = 0 := rfl

instance : Mul (Pw A k z) := ⟨fun x y => ⟨x.r + tw k x.s y.r + zc z x.s y.s, xor x.s y.s⟩⟩
instance : One (Pw A k z) := ⟨⟨0, false⟩⟩
/-- inverse -/
def pinv (k : ℤ) (z : A) : Pw A k z → Pw A k z
  | ⟨a, false⟩ => ⟨-a, false⟩
  | ⟨a, true⟩ => ⟨-(k • a) - z, true⟩

instance : _root_.Inv (Pw A k z) := ⟨pinv k z⟩

lemma pmk_mul (a b : A) (i j : Bool) :
    (⟨a, i⟩ : Pw A k z) * ⟨b, j⟩ = ⟨a + tw k i b + zc z i j, xor i j⟩ := rfl
@[simp] lemma pone_r : (1 : Pw A k z).r = 0 := rfl
@[simp] lemma pone_s : (1 : Pw A k z).s = false := rfl

variable [hk : Fact (∀ a : A, k • k • a = a)] [hz : Fact (k • z = z)]

include hk in
lemma kk (a : A) : k • k • a = a := hk.out a

include hz in
lemma kz : k • z = z := hz.out

instance : Group (Pw A k z) where
  mul := (· * ·)
  one := 1
  inv := (·⁻¹)
  mul_assoc x y w := by
    rcases x with ⟨a, i⟩; rcases y with ⟨b, j⟩; rcases w with ⟨c, l⟩
    show (⟨a, i⟩ * ⟨b, j⟩ : Pw A k z) * ⟨c, l⟩ = ⟨a, i⟩ * (⟨b, j⟩ * ⟨c, l⟩)
    simp only [pmk_mul]
    ext
    · cases i <;> cases j <;> cases l <;>
        simp [tw, zc, smul_add, kk, kz (z := z)] <;> abel
    · cases i <;> cases j <;> cases l <;> rfl
  one_mul x := by
    rcases x with ⟨a, i⟩
    show (⟨0, false⟩ * ⟨a, i⟩ : Pw A k z) = ⟨a, i⟩
    simp [pmk_mul]
  mul_one x := by
    rcases x with ⟨a, i⟩
    show (⟨a, i⟩ * ⟨0, false⟩ : Pw A k z) = ⟨a, i⟩
    cases i <;> simp [pmk_mul, tw, zc]
  inv_mul_cancel x := by
    rcases x with ⟨a, i⟩
    cases i
    · show (⟨-a, false⟩ * ⟨a, false⟩ : Pw A k z) = ⟨0, false⟩
      simp [pmk_mul]
    · show (⟨-(k • a) - z, true⟩ * ⟨a, true⟩ : Pw A k z) = ⟨0, false⟩
      simp only [pmk_mul, tw_true, zc_tt]
      ext
      · show -(k • a) - z + k • a + z = 0
        abel
      · rfl

/-- rotation -/
def prot (a : A) : Pw A k z := ⟨a, false⟩
/-- reflection -/
def pref (b : A) : Pw A k z := ⟨b, true⟩

omit hk hz in
@[simp] lemma prot_r (a : A) : (prot a : Pw A k z).r = a := rfl
omit hk hz in
@[simp] lemma prot_s (a : A) : (prot a : Pw A k z).s = false := rfl
omit hk hz in
@[simp] lemma pref_r (a : A) : (pref a : Pw A k z).r = a := rfl
omit hk hz in
@[simp] lemma pref_s (a : A) : (pref a : Pw A k z).s = true := rfl

lemma prot_mul_prot (a b : A) : (prot a : Pw A k z) * prot b = prot (a + b) := by
  show (⟨a, false⟩ * ⟨b, false⟩ : Pw A k z) = ⟨a + b, false⟩; simp [pmk_mul]
lemma prot_mul_pref (a b : A) : (prot a : Pw A k z) * pref b = pref (a + b) := by
  show (⟨a, false⟩ * ⟨b, true⟩ : Pw A k z) = ⟨a + b, true⟩; simp [pmk_mul]
lemma pref_mul_prot (a b : A) : (pref a : Pw A k z) * prot b = pref (a + k • b) := by
  show (⟨a, true⟩ * ⟨b, false⟩ : Pw A k z) = ⟨a + k • b, true⟩; simp [pmk_mul]
lemma pref_mul_pref (a b : A) : (pref a : Pw A k z) * pref b = prot (a + k • b + z) := by
  show (⟨a, true⟩ * ⟨b, true⟩ : Pw A k z) = ⟨a + k • b + z, false⟩; simp [pmk_mul]
lemma prot_inv (a : A) : (prot a : Pw A k z)⁻¹ = prot (-a) := rfl
lemma pref_inv (a : A) : (pref a : Pw A k z)⁻¹ = pref (-(k • a) - z) := rfl
omit hk hz in
lemma prot_injective : Function.Injective (prot : A → Pw A k z) := fun a b h => by
  simpa using congrArg Pw.r h
omit hk hz in
lemma peq_rot_or_ref (x : Pw A k z) : x = prot x.r ∨ x = pref x.r := by
  rcases x with ⟨a, i⟩; cases i
  · left; rfl
  · right; rfl
lemma prot_pow (a : A) (n : ℕ) : (prot a : Pw A k z) ^ n = prot (n • a) := by
  induction n with
  | zero => rw [pow_zero, zero_nsmul]; rfl
  | succ n ih => rw [pow_succ, ih, prot_mul_prot, succ_nsmul]

/-- conjugating a rotation by a reflection multiplies it by `k` -/
lemma pref_conj (w c : A) : (pref w : Pw A k z) * prot c * (pref w)⁻¹ = prot (k • c) := by
  rw [pref_mul_prot, pref_inv, pref_mul_pref]
  congr 1
  rw [smul_sub, smul_neg, kk, kz (z := z)]; abel

/-- `ref w · (ref b)⁻¹ = rot (w - b)` -/
lemma pref_mul_pref_inv (w b : A) : (pref w : Pw A k z) * (pref b)⁻¹ = prot (w - b) := by
  rw [pref_inv, pref_mul_pref]
  congr 1
  rw [smul_sub, smul_neg, kk, kz (z := z)]; abel

omit hk hz in
lemma k_mem (K : AddSubgroup A) (a : A) (ha : a ∈ K) : k • a ∈ K := zsmul_mem ha k

omit hz in
lemma k_mem_iff (K : AddSubgroup A) (a : A) : k • a ∈ K ↔ a ∈ K := by
  constructor
  · intro h; have := k_mem (k := k) K _ h; rwa [kk] at this
  · exact k_mem K a

/-- the identity on underlying data -/
def toD : Pw A k z ≃ Dih A :=
  ⟨fun x => ⟨x.r, x.s⟩, fun x => ⟨x.r, x.s⟩, fun _ => rfl, fun _ => rfl⟩

omit hk hz in
@[simp] lemma toD_r (x : Pw A k z) : (toD x).r = x.r := rfl
omit hk hz in
@[simp] lemma toD_s (x : Pw A k z) : (toD x).s = x.s := rfl
omit hk hz in
@[simp] lemma toD_prot (a : A) : toD (prot a : Pw A k z) = rot a := rfl
omit hk hz in
@[simp] lemma toD_pref (a : A) : toD (pref a : Pw A k z) = ref a := rfl
omit hk hz in
@[simp] lemma toD_symm_rot (a : A) : (toD (k := k) (z := z)).symm (rot a) = prot a := rfl
omit hk hz in
@[simp] lemma toD_symm_ref (a : A) : (toD (k := k) (z := z)).symm (ref a) = pref a := rfl

/-- left translation by a rotation is the same in both models -/
lemma toD_rot_mul (c : A) (x : Pw A k z) : toD (prot c * x) = rot c * toD x := by
  rcases peq_rot_or_ref x with h | h <;> rw [h]
  · rw [prot_mul_prot, toD_prot, toD_prot, rot_mul_rot]
  · rw [prot_mul_pref, toD_pref, toD_pref, rot_mul_ref]

omit hk hz in
instance [Fintype A] : Fintype (Pw A k z) := Fintype.ofEquiv (Dih A) toD.symm

omit hk hz in
lemma card_pw [Fintype A] : Fintype.card (Pw A k z) = Fintype.card (Dih A) :=
  Fintype.card_congr toD

end PwGroup

section Generic
variable {Γ : Type} [Group Γ] [DecidableEq Γ]

lemma pc_single_g (d s : Γ) : (pc d [s] : ℚ) =
    (Pi.single s (1 : ℚ) : Γ → ℚ) d + (Pi.single s (1 : ℚ) : Γ → ℚ) d⁻¹ := by
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

/-- generalized alternating snake: block, join, reversed block, join, … with arbitrary joins -/
def gsn (ds : List Γ) (jn : ℕ → Γ) : ℕ → List Γ
  | 0 => ds
  | t + 1 => gsn ds jn t ++ jn t :: (if Even (t + 1) then ds else rev ds)

/-- bases of the blocks of `gsn` -/
def gbase (e : Γ) (jn : ℕ → Γ) : ℕ → Γ
  | 0 => 1
  | t + 1 => if Even t then gbase e jn t * e * jn t * e⁻¹ else gbase e jn t * jn t

lemma gsn_spec (ds : List Γ) (jn : ℕ → Γ) (t : ℕ) :
    (gsn ds jn t).prod =
        (if Even t then gbase ds.prod jn t * ds.prod else gbase ds.prod jn t) ∧
    verts 1 (gsn ds jn t) = (List.range (t + 1)).flatMap
      (fun i => (if Even i then verts 1 ds else (verts 1 ds).reverse).map
        (gbase ds.prod jn i * ·)) := by
  induction t with
  | zero => simp [gsn, gbase]
  | succ t ih =>
    obtain ⟨ih1, ih2⟩ := ih
    rw [List.range_succ (n := t + 1), List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
      List.append_nil, gsn]
    beta_reduce
    by_cases ht : Even t
    · have ht1 : ¬ Even (t + 1) := by rw [Nat.even_add_one]; exact not_not.2 ht
      rw [if_pos ht] at ih1
      rw [if_neg ht1, if_neg ht1, if_neg ht1]
      have hb : gbase ds.prod jn (t + 1) = gbase ds.prod jn t * ds.prod * jn t * ds.prod⁻¹ := by
        rw [gbase, if_pos ht]
      refine ⟨?_, ?_⟩
      · rw [List.prod_append, List.prod_cons, prod_rev, ih1, hb]; group
      · rw [verts_append, ih2, ih1]
        congr 1
        rw [show 1 * (gbase ds.prod jn t * ds.prod) * jn t =
            gbase ds.prod jn (t + 1) * ds.prod by rw [hb]; group, verts_rev,
          verts_eq (gbase ds.prod jn (t + 1)) ds]
        simp [List.map_reverse]
    · have ht1 : Even (t + 1) := by rw [Nat.even_add_one]; exact ht
      rw [if_neg ht] at ih1
      rw [if_pos ht1, if_pos ht1, if_pos ht1]
      have hb : gbase ds.prod jn (t + 1) = gbase ds.prod jn t * jn t := by
        rw [gbase, if_neg ht]
      refine ⟨?_, ?_⟩
      · rw [List.prod_append, List.prod_cons, ih1, hb, mul_assoc]
      · rw [verts_append, ih2, ih1]
        congr 1
        rw [show 1 * gbase ds.prod jn t * jn t = gbase ds.prod jn (t + 1) by rw [hb, one_mul],
          verts_eq (gbase ds.prod jn (t + 1)) ds]

lemma pc_gsn (d : Γ) (ds : List Γ) (jn : ℕ → Γ) (c : Γ) (hc : ∀ t, pc d [jn t] = pc d [c])
    (t : ℕ) : pc d (gsn ds jn t) = (t + 1) * pc d ds + t * pc d [c] := by
  induction t with
  | zero => simp [gsn]
  | succ t ih =>
    rw [gsn, pc_append, ih, hc]
    by_cases ht : Even (t + 1)
    · rw [if_pos ht]; ring
    · rw [if_neg ht, pc_rev]; ring

lemma mem_gsn {S : Finset Γ} (hinv : ∀ s ∈ S, s⁻¹ ∈ S) (ds : List Γ) (hds : ∀ d ∈ ds, d ∈ S)
    (jn : ℕ → Γ) (hj : ∀ t, jn t ∈ S) (t : ℕ) : ∀ d ∈ gsn ds jn t, d ∈ S := by
  induction t with
  | zero => simpa [gsn] using hds
  | succ t ih =>
    intro d hd
    simp only [gsn, List.mem_append, List.mem_cons] at hd
    rcases hd with hd | hd | hd
    · exact ih d hd
    · rw [hd]; exact hj t
    · split_ifs at hd
      · exact hds d hd
      · exact mem_rev hinv ds hds d hd

end Generic

end FTDih

-- ===== FTPowerLemA.lean =====

/-!
# Lemma A of FT-POWER.md (alternating sequences)

`IsAlt k q c`: `c 0 = 0`, steps `c (t+1) - c t ∈ {k, -k}` for even `t` and `∈ {1, -1}` for odd `t`,
and `c 0, …, c (q-1)` pairwise distinct mod `q`.
(a) `q ∣ k - ε`, `ε = ±1`: `cA`.  (b) `q` even and `q ∣ k² - 1`: super-blocks `cB`.
-/

namespace FTDih

/-- an alternating sequence for `(q, k)` -/
def IsAlt (k : ℤ) (q : ℕ) (c : ℕ → ℤ) : Prop :=
  c 0 = 0 ∧ (∀ t, Even t → (c (t + 1) - c t = k ∨ c (t + 1) - c t = -k)) ∧
    (∀ t, ¬ Even t → (c (t + 1) - c t = 1 ∨ c (t + 1) - c t = -1)) ∧
    ∀ t t', t < q → t' < q → (q : ℤ) ∣ c t - c t' → t = t'

lemma eq_of_dvd_sub_lt (q t t' : ℕ) (ht : t < q) (ht' : t' < q)
    (h : (q : ℤ) ∣ (t : ℤ) - t') : t = t' := by
  have := Int.eq_zero_of_abs_lt_dvd h (by rw [abs_lt]; constructor <;> omega)
  omega

lemma even_succ_div (m : ℕ) : (m + m + 1) / 2 = m ∧ (m + m + 1) % 2 = 1 ∧ (m + m) / 2 = m ∧
    (m + m) % 2 = 0 := by omega

lemma odd_succ_div (m : ℕ) : (2 * m + 1 + 1) / 2 = m + 1 ∧ (2 * m + 1 + 1) % 2 = 0 ∧
    (2 * m + 1) / 2 = m ∧ (2 * m + 1) % 2 = 1 := by omega

/-- case (a) -/
def cA (k ε : ℤ) (t : ℕ) : ℤ := ((t / 2 : ℕ) : ℤ) * (ε * k + 1) + ((t % 2 : ℕ) : ℤ) * (ε * k)

lemma lemmaA_a (k ε : ℤ) (hε : ε = 1 ∨ ε = -1) (q : ℕ) (hq : (q : ℤ) ∣ k - ε) :
    IsAlt k q (cA k ε) := by
  refine ⟨by simp [cA], ?_, ?_, ?_⟩
  · intro t ht
    obtain ⟨m, rfl⟩ := ht
    obtain ⟨h1, h2, h3, h4⟩ := even_succ_div m
    simp only [cA, h1, h2, h3, h4]; push_cast
    rcases hε with rfl | rfl
    · left; ring
    · right; ring
  · intro t ht
    rw [Nat.not_even_iff_odd] at ht
    obtain ⟨m, rfl⟩ := ht
    obtain ⟨h1, h2, h3, h4⟩ := odd_succ_div m
    simp only [cA, h1, h2, h3, h4]; push_cast
    left; ring
  · intro t t' ht ht' hd
    apply eq_of_dvd_sub_lt q t t' ht ht'
    have hεk : (q : ℤ) ∣ ε * k - 1 := by
      have := dvd_mul_of_dvd_right hq ε
      rcases hε with rfl | rfl
      · simpa using this
      · have e : (-1 : ℤ) * k - 1 = -(k - -1) := by ring
        rw [e]; exact (dvd_neg).2 hq
    have key : ∀ t : ℕ, (q : ℤ) ∣ cA k ε t - t := by
      intro t
      have ht2 : (t : ℤ) = 2 * ((t / 2 : ℕ) : ℤ) + ((t % 2 : ℕ) : ℤ) := by
        exact_mod_cast (Nat.div_add_mod t 2).symm
      have e : cA k ε t - t = (((t / 2 : ℕ) : ℤ) + ((t % 2 : ℕ) : ℤ)) * (ε * k - 1) := by
        rw [cA]; linear_combination (-1 : ℤ) * ht2
      rw [e]; exact dvd_mul_of_dvd_right hεk _
    have := dvd_sub hd (dvd_sub (key t) (key t'))
    have e : cA k ε t - cA k ε t' - (cA k ε t - t - (cA k ε t' - t')) = (t : ℤ) - t' := by ring
    rwa [e] at this

/-- case (b): super-blocks of length `2h` -/
def cB (k : ℤ) (h : ℕ) (t : ℕ) : ℤ :=
  (((t / 2) / h : ℕ) : ℤ) * ((h : ℤ) * (k + 1) - 2) + (((t / 2) % h : ℕ) : ℤ) * (k + 1) +
    ((t % 2 : ℕ) : ℤ) * k

lemma div_mod_succ (s h : ℕ) (hh : 0 < h) :
    ((s % h + 1 < h) → (s + 1) / h = s / h ∧ (s + 1) % h = s % h + 1) ∧
    ((s % h + 1 = h) → (s + 1) / h = s / h + 1 ∧ (s + 1) % h = 0) := by
  have hs := Nat.div_add_mod s h
  have hlt := Nat.mod_lt s hh
  constructor
  · intro h1
    exact (Nat.div_mod_unique hh).2 ⟨by rw [← hs] at *; ring_nf; omega, h1⟩
  · intro h1
    refine (Nat.div_mod_unique hh).2 ⟨?_, hh⟩
    have : h * (s / h) + h = s + 1 := by omega
    rw [mul_add, mul_one]; omega

set_option maxHeartbeats 1000000 in
lemma lemmaA_b (k : ℤ) (q : ℕ) (hq0 : 0 < q) (hq : Even q) (hk : (q : ℤ) ∣ k * k - 1) :
    ∃ c, IsAlt k q c := by
  -- parity of k
  have hk2 : (2 : ℤ) ∣ k * k - 1 :=
    dvd_trans (by exact_mod_cast (even_iff_two_dvd.1 hq)) hk
  have hkodd : k % 2 = 1 := by
    rcases Int.emod_two_eq_zero_or_one k with h0 | h1
    · exfalso
      have := Int.emod_eq_zero_of_dvd hk2
      rw [Int.sub_emod, Int.mul_emod, h0] at this; norm_num at this
    · exact h1
  -- g = gcd(k+1, q), h = q / g
  set g := Int.gcd (k + 1) q with hgdef
  have hgk : (g : ℤ) ∣ k + 1 := Int.gcd_dvd_left _ _
  have hgq : (g : ℤ) ∣ (q : ℤ) := Int.gcd_dvd_right _ _
  have hg0 : 0 < g := Int.gcd_pos_of_ne_zero_right _ (by exact_mod_cast hq0.ne')
  have hgq' : g ∣ q := by exact_mod_cast hgq
  obtain ⟨h, hqgh⟩ := hgq'
  have hh0 : 0 < h := by
    rcases Nat.eq_zero_or_pos h with h0 | h0
    · rw [h0, mul_zero] at hqgh; omega
    · exact h0
  obtain ⟨κ, hκ⟩ := hgk
  -- g even
  have h2g : 2 ∣ g := by
    have h1 : (2 : ℤ) ∣ k + 1 := by omega
    have h2 : (2 : ℤ) ∣ (q : ℤ) := by exact_mod_cast (even_iff_two_dvd.1 hq)
    have := Int.dvd_gcd h1 h2
    rw [← hgdef] at this
    exact_mod_cast this
  obtain ⟨g2, hg2⟩ := h2g
  -- gcd(κ, h) = 1
  have hcop : Int.gcd κ h = 1 := by
    have e : Int.gcd (k + 1) q = Int.gcd ((g : ℤ) * κ) ((g : ℤ) * h) := by
      rw [← hκ, hqgh]; push_cast; rfl
    rw [Int.gcd_mul_left, Int.natAbs_natCast, ← hgdef] at e
    have : g * 1 = g * Int.gcd κ h := by rw [mul_one]; exact e
    exact (Nat.eq_of_mul_eq_mul_left hg0 this).symm
  refine ⟨cB k h, by simp [cB], ?_, ?_, ?_⟩
  · -- even steps: +k
    intro t ht
    obtain ⟨m, rfl⟩ := ht
    obtain ⟨h1, h2, h3, h4⟩ := even_succ_div m
    simp only [cB, h1, h2, h3, h4, Nat.cast_one, Nat.cast_zero]
    left; ring
  · -- odd steps: +1 inside a super-block, -1 between super-blocks
    intro t ht
    rw [Nat.not_even_iff_odd] at ht
    obtain ⟨m, rfl⟩ := ht
    obtain ⟨h1, h2, h3, h4⟩ := odd_succ_div m
    simp only [cB, h1, h2, h3, h4]
    obtain ⟨hA, hB⟩ := div_mod_succ m h hh0
    have hlt := Nat.mod_lt m hh0
    by_cases hi : m % h + 1 < h
    · obtain ⟨e1, e2⟩ := hA hi
      rw [e1, e2]; simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero]; left; ring
    · have hi' : m % h + 1 = h := by omega
      obtain ⟨e1, e2⟩ := hB hi'
      rw [e1, e2]
      have : ((m % h : ℕ) : ℤ) = (h : ℤ) - 1 := by
        have := congrArg (Nat.cast : ℕ → ℤ) hi'
        rw [Nat.cast_add, Nat.cast_one] at this; linarith
      simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero]; rw [this]; right; ring
  · -- distinctness
    intro t t' ht ht' hd
    -- decompose
    set s := t / 2 with hs
    set s' := t' / 2 with hs'
    set p := t % 2 with hp
    set p' := t' % 2 with hp'
    set j := s / h with hj
    set j' := s' / h with hj'
    set i := s % h with hi
    set i' := s' % h with hi'
    have hp2 : p < 2 := Nat.mod_lt _ (by norm_num)
    have hp2' : p' < 2 := Nat.mod_lt _ (by norm_num)
    have hih : i < h := Nat.mod_lt _ hh0
    have hih' : i' < h := Nat.mod_lt _ hh0
    have hst : 2 * s + p = t := Nat.div_add_mod t 2
    have hst' : 2 * s' + p' = t' := Nat.div_add_mod t' 2
    have hsj : h * j + i = s := Nat.div_add_mod s h
    have hsj' : h * j' + i' = s' := Nat.div_add_mod s' h
    have hq2 : q = 2 * g2 * h := by rw [hqgh, hg2]
    have hjg : j < g2 := by
      by_contra hc; push_neg at hc
      have : h * g2 ≤ h * j := Nat.mul_le_mul_left _ hc
      have : 2 * (h * g2) ≤ t := by omega
      rw [hq2] at ht; nlinarith
    have hjg' : j' < g2 := by
      by_contra hc; push_neg at hc
      have : h * g2 ≤ h * j' := Nat.mul_le_mul_left _ hc
      have : 2 * (h * g2) ≤ t' := by omega
      rw [hq2] at ht'; nlinarith
    -- the difference
    have hct : cB k h t = (j : ℤ) * ((h : ℤ) * (k + 1) - 2) + (i : ℤ) * (k + 1) + (p : ℤ) * k := by
      simp only [cB]; rw [← hs, ← hj, ← hi, ← hp]
    have hct' : cB k h t' = (j' : ℤ) * ((h : ℤ) * (k + 1) - 2) + (i' : ℤ) * (k + 1) +
        (p' : ℤ) * k := by
      simp only [cB]; rw [← hs', ← hj', ← hi', ← hp']
    have hdiff : cB k h t - cB k h t' = ((j : ℤ) - j') * ((h : ℤ) * (k + 1) - 2) +
        ((i : ℤ) - i') * (k + 1) + ((p : ℤ) - p') * k := by
      rw [hct, hct']; ring
    rw [hdiff] at hd
    clear_value s s' p p' j j' i i'
    -- k + 1 = g κ, g = 2 g2
    have hk1 : k + 1 = 2 * (g2 : ℤ) * κ := by rw [hκ, hg2]; push_cast; ring
    have hqZ : (q : ℤ) = 2 * (g2 : ℤ) * h := by exact_mod_cast hq2
    -- reduce mod g: g ∣ -(2 j + p) + (2 j' + p')
    have hmodg : (2 * (g2 : ℤ)) ∣ (2 * (j' : ℤ) + p') - (2 * j + p) := by
      have h1 : (2 * (g2 : ℤ)) ∣ (q : ℤ) := ⟨h, by rw [hqZ]⟩
      have h2 := dvd_trans h1 hd
      have e : ((j : ℤ) - j') * ((h : ℤ) * (k + 1) - 2) + ((i : ℤ) - i') * (k + 1) +
          ((p : ℤ) - p') * k = (2 * (g2 : ℤ)) * (((j : ℤ) - j') * h * κ + ((i : ℤ) - i') * κ +
          ((p : ℤ) - p') * κ) + ((2 * (j' : ℤ) + p') - (2 * j + p)) := by
        have hk' : k = 2 * (g2 : ℤ) * κ - 1 := by linarith
        rw [hk']; ring
      rw [e] at h2
      have h3 := dvd_sub h2 (dvd_mul_right (2 * (g2 : ℤ)) (((j : ℤ) - j') * h * κ +
        ((i : ℤ) - i') * κ + ((p : ℤ) - p') * κ))
      rwa [add_sub_cancel_left] at h3
    have hjp : 2 * j + p = 2 * j' + p' := by
      have := Int.eq_zero_of_abs_lt_dvd hmodg (by rw [abs_lt]; constructor <;> push_cast <;> omega)
      omega
    have hpp : p = p' := by omega
    have hjj : j = j' := by omega
    -- then q ∣ (i - i')(k+1), so h ∣ (i - i') κ, so h ∣ i - i'
    have hd2 : (q : ℤ) ∣ ((i : ℤ) - i') * (k + 1) := by
      have e : ((j : ℤ) - j') * ((h : ℤ) * (k + 1) - 2) + ((i : ℤ) - i') * (k + 1) +
          ((p : ℤ) - p') * k = ((i : ℤ) - i') * (k + 1) := by rw [hpp, hjj]; ring
      rwa [e] at hd
    have hd3 : (h : ℤ) ∣ ((i : ℤ) - i') * κ := by
      rw [hqZ, hk1] at hd2
      have e : ((i : ℤ) - i') * (2 * (g2 : ℤ) * κ) = (2 * (g2 : ℤ)) * (((i : ℤ) - i') * κ) := by ring
      rw [e] at hd2
      have hg2pos : (2 * (g2 : ℤ)) ≠ 0 := by
        have : 0 < g2 := by omega
        positivity
      exact Int.dvd_of_mul_dvd_mul_left hg2pos hd2
    have hd4 : (h : ℤ) ∣ (i : ℤ) - i' := by
      apply Int.dvd_of_dvd_mul_left_of_gcd_one hd3
      rw [Int.gcd_comm]; exact hcop
    have hii : i = i' := eq_of_dvd_sub_lt h i i' hih hih' hd4
    have hss : s = s' := by rw [← hsj, ← hsj', hjj, hii]
    omega

/-- Lemma A, both cases -/
lemma lemmaA (k : ℤ) (q : ℕ) (hq0 : 0 < q)
    (H : (∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ (q : ℤ) ∣ k - ε) ∨ (Even q ∧ (q : ℤ) ∣ k * k - 1)) :
    ∃ c, IsAlt k q c := by
  rcases H with ⟨ε, hε, hq⟩ | ⟨he, hk⟩
  · exact ⟨_, lemmaA_a k ε hε q hq⟩
  · exact lemmaA_b k q hq0 he hk

end FTDih

-- ===== FTPowerSteps.lean =====

/-!
# Theorem 8: the two realisable families in Γ(A, k, z) (FT-POWER.md Lemma B)

Paths are step lists in `Pw A k z`; their vertex sets are the type sets of the Dih development read
through `toD`, so the game `vD`, `KT`, `PT` are reused verbatim. Changes from the dihedral steps:
reflection joins use `(ref b)⁻¹ = ref b*` (S2), side-1 rotation steps move by `k • r` (S1, S4), and
S4 uses an alternating sequence (Lemma A) for the block translations.
-/

open Finset

namespace FTDih

/-- the hypothesis of Lemma A for a block count `q` -/
def Hq (k : ℤ) (q : ℕ) : Prop :=
  (∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ (q : ℤ) ∣ k - ε) ∨ (Even q ∧ (q : ℤ) ∣ k * k - 1)

section BlocksC
variable {A : Type} [AddCommGroup A] [Fintype A] [DecidableEq A]

/-- blocks translated by `rot (c i • δ)`, `c` injective mod `q` on `[0, q)` -/
lemma blocksC (hb : Bool) (K : AddSubgroup A) (b₁ δ : A) (c : ℕ → ℤ)
    (hc : ∀ t t', t < addOrderOf ((δ : A ⧸ K)) → t' < addOrderOf ((δ : A ⧸ K)) →
      ((addOrderOf ((δ : A ⧸ K)) : ℕ) : ℤ) ∣ c t - c t' → t = t')
    (V : List (Dih A)) (hV : V.Nodup)
    (hVm : ∀ x, x ∈ V ↔ XP hb K b₁ x) (f : ℕ → List (Dih A))
    (hf : ∀ i, f i = V.map (rot (c i • δ) * ·) ∨ f i = V.reverse.map (rot (c i • δ) * ·)) :
    ((List.range (addOrderOf ((δ : A ⧸ K)))).flatMap f).Nodup ∧
    (∀ x, x ∈ (List.range (addOrderOf ((δ : A ⧸ K)))).flatMap f ↔
      XP hb (K ⊔ AddSubgroup.zmultiples δ) b₁ x) ∧
    ((List.range (addOrderOf ((δ : A ⧸ K)))).flatMap f).length =
      addOrderOf ((δ : A ⧸ K)) * V.length := by
  set q := addOrderOf ((δ : A ⧸ K)) with hq
  have hq0 : 0 < q := addOrderOf_pos _
  have hmemf' : ∀ i x, x ∈ f i ↔
      (if x.s then (hb = true ∧ (x.r - b₁) - c i • δ ∈ K) else x.r - c i • δ ∈ K) := by
    intro i x
    have : x ∈ f i ↔ XP hb K b₁ (rot (-(c i • δ)) * x) := by
      rcases hf i with h | h <;> rw [h, mem_map_mul, rot_inv]
      · exact hVm _
      · rw [List.mem_reverse]; exact hVm _
    rw [this, xp_rot_mul]
    simp only [← sub_eq_add_neg]
  -- `q ∣ c t - c t'` from membership in `K`
  have hdvd : ∀ t t' : ℕ, c t • δ - c t' • δ ∈ K → (q : ℤ) ∣ c t - c t' := by
    intro t t' h0
    have h : (c t - c t') • δ ∈ K := by
      have e : (c t - c t') • δ = c t • δ - c t' • δ := sub_smul _ _ _
      rw [e]; exact h0
    have h1 : ((c t - c t') • (δ : A ⧸ K)) = 0 := by
      rw [← QuotientAddGroup.mk_zsmul, QuotientAddGroup.eq_zero_iff]; exact h
    exact (addOrderOf_dvd_iff_zsmul_eq_zero).2 h1
  -- surjectivity of `t ↦ c t mod q`
  have hsurj : ∀ i : ℕ, i < q → ∃ t < q, (q : ℤ) ∣ c t - i := by
    intro i hi
    haveI : NeZero q := ⟨hq0.ne'⟩
    let F : Fin q → ZMod q := fun t => (c t : ZMod q)
    have hF : Function.Injective F := by
      intro t t' h
      have : (q : ℤ) ∣ c t - c t' := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).1 h.symm
      exact Fin.ext (hc t t' t.2 t'.2 this)
    have hbij := (Fintype.bijective_iff_injective_and_card F).2 ⟨hF, by simp⟩
    obtain ⟨t, ht⟩ := hbij.2 (i : ZMod q)
    refine ⟨t, t.2, ?_⟩
    have : ((c t : ℤ) : ZMod q) = ((i : ℤ) : ZMod q) := by simpa [F] using ht
    exact (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).1 this.symm
  have hcover : ∀ y : A, y ∈ K ⊔ AddSubgroup.zmultiples δ ↔ ∃ t < q, y - c t • δ ∈ K := by
    intro y
    rw [zq_mem]
    constructor
    · rintro ⟨i, hi, hy⟩
      obtain ⟨t, ht, hd⟩ := hsurj i hi
      refine ⟨t, ht, ?_⟩
      obtain ⟨m, hm⟩ := hd
      have hqδ : (q : ℤ) • δ ∈ K := by
        have : (q • (δ : A ⧸ K)) = 0 := addOrderOf_nsmul_eq_zero _
        rw [← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff] at this
        rwa [natCast_zsmul]
      have e : y - c t • δ = (y - i • δ) - m • ((q : ℤ) • δ) := by
        rw [← mul_zsmul, mul_comm, ← hm, sub_zsmul, natCast_zsmul]; abel
      rw [e]; exact sub_mem hy (zsmul_mem hqδ m)
    · rintro ⟨t, ht, hy⟩
      rw [← zq_mem]
      rw [show y = (y - c t • δ) + c t • δ by abel]
      exact AddSubgroup.add_mem_sup hy (AddSubgroup.zsmul_mem _ (AddSubgroup.mem_zmultiples δ) _)
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
      refine hc i j (List.mem_range.1 hi) (List.mem_range.1 hj) (hdvd i j ?_)
      split_ifs at hx1 hx2
      · have := K.sub_mem hx2.2 hx1.2
        rw [show (x.r - b₁ - c j • δ) - (x.r - b₁ - c i • δ) = c i • δ - c j • δ by abel] at this
        exact this
      · have := K.sub_mem hx2 hx1
        rw [show (x.r - c j • δ) - (x.r - c i • δ) = c i • δ - c j • δ by abel] at this
        exact this
  · intro x
    rw [List.mem_flatMap]
    simp only [List.mem_range, hmemf', XP]
    split_ifs
    · constructor
      · rintro ⟨i, hi, hb', h⟩; exact ⟨hb', (hcover _).2 ⟨i, hi, h⟩⟩
      · rintro ⟨hb', h⟩
        obtain ⟨i, hi, h⟩ := (hcover _).1 h
        exact ⟨i, hi, hb', h⟩
    · constructor
      · rintro ⟨i, hi, h⟩; exact (hcover _).2 ⟨i, hi, h⟩
      · intro h; exact (hcover _).1 h
  · rw [List.length_flatMap]
    have : ∀ i, (f i).length = V.length := by
      intro i; rcases hf i with h | h <;> rw [h] <;> simp
    simp only [this, List.map_const', List.length_range, List.sum_replicate, smul_eq_mul]

end BlocksC

section Steps
variable {A : Type} [AddCommGroup A] [Fintype A] [DecidableEq A] {k : ℤ} {z : A}
  [Fact (∀ a : A, k • k • a = a)] [Fact (k • z = z)]
  (S : Finset (Pw A k z)) (hinv : ∀ s ∈ S, s⁻¹ ∈ S)

omit [Fintype A] [DecidableEq A] [Fact (∀ a : A, k • k • a = a)] [Fact (k • z = z)] in
@[simp] lemma toD_mk (a : A) (i : Bool) : toD (⟨a, i⟩ : Pw A k z) = ⟨a, i⟩ := rfl

/-- the Γ-version of the blocks lemma (through `toD`) -/
lemma blocksP (hb : Bool) (K : AddSubgroup A) (b₁ δ : A) (c : ℕ → ℤ)
    (hc : ∀ t t', t < addOrderOf ((δ : A ⧸ K)) → t' < addOrderOf ((δ : A ⧸ K)) →
      ((addOrderOf ((δ : A ⧸ K)) : ℕ) : ℤ) ∣ c t - c t' → t = t')
    (V : List (Pw A k z)) (hV : V.Nodup)
    (hVm : ∀ x, x ∈ V ↔ XP hb K b₁ (toD x)) (f : ℕ → List (Pw A k z))
    (hf : ∀ i, f i = V.map (prot (c i • δ) * ·) ∨ f i = V.reverse.map (prot (c i • δ) * ·)) :
    ((List.range (addOrderOf ((δ : A ⧸ K)))).flatMap f).Nodup ∧
    (∀ x, x ∈ (List.range (addOrderOf ((δ : A ⧸ K)))).flatMap f ↔
      XP hb (K ⊔ AddSubgroup.zmultiples δ) b₁ (toD x)) ∧
    ((List.range (addOrderOf ((δ : A ⧸ K)))).flatMap f).length =
      addOrderOf ((δ : A ⧸ K)) * V.length := by
  have hinj : Function.Injective (toD : Pw A k z → Dih A) := toD.injective
  have hV' : (V.map toD).Nodup := hV.map hinj
  have hVm' : ∀ y, y ∈ V.map toD ↔ XP hb K b₁ y := by
    intro y
    rw [show y = toD (toD.symm y) by simp, List.mem_map_of_injective hinj, hVm]
  have hmapf : ∀ c' : A, (V.map (prot c' * ·)).map toD = (V.map toD).map (rot c' * ·) := by
    intro c'; simp only [List.map_map]; congr 1; funext x; exact toD_rot_mul c' x
  obtain ⟨hN, hM, hL⟩ := blocksC hb K b₁ δ c hc (V.map toD) hV' hVm' (fun i => (f i).map toD)
    (fun i => by
      rcases hf i with h | h
      · left; rw [h, hmapf]
      · right; rw [h]; simp only [List.map_reverse, hmapf])
  rw [← List.map_flatMap] at hN hM hL
  refine ⟨List.Nodup.of_map _ hN, fun x => ?_, by rw [List.length_map] at hL; rw [hL, List.length_map]⟩
  rw [← hM, List.mem_map_of_injective hinj]

/-- invariant (Γ version): a path of `⟨T⟩` (read through `toD`) from `1`, labels in `S` -/
def InvP (T : Finset (Dih A)) (b₁ : A) (ds : List (Pw A k z)) (γ : Dih A → ℚ) : Prop :=
  (∀ d ∈ ds, d ∈ S) ∧ (verts 1 ds).Nodup ∧ (∀ x, x ∈ verts 1 ds ↔ PT T b₁ (toD x)) ∧
    ∀ d, (pc d ds : ℚ) * Fintype.card (Dih A) = (verts 1 ds).length * (γ (toD d) + γ (toD d⁻¹))

omit [Fact (∀ a : A, k • k • a = a)] [Fact (k • z = z)] in
lemma vD_eqP (T : Finset (Dih A)) (b₁ : A) (V : List (Pw A k z)) (hV : V.Nodup)
    (hm : ∀ x, x ∈ V ↔ PT T b₁ (toD x)) :
    vD T = (Fintype.card (Dih A) : ℚ) - Fintype.card (Dih A) / V.length := by
  have hinj : Function.Injective (toD : Pw A k z → Dih A) := toD.injective
  have := vD_eq T b₁ (V.map toD) (hV.map hinj) (fun y => by
    rw [show y = toD (toD.symm y) by simp, List.mem_map_of_injective hinj, hm])
  rwa [List.length_map] at this

omit [Fintype A] [Fact (∀ a : A, k • k • a = a)] [Fact (k • z = z)] in
lemma single_toD (s : Dih A) (d : Pw A k z) (c : ℚ) :
    (Pi.single (toD.symm s) c : Pw A k z → ℚ) d = (Pi.single s c : Dih A → ℚ) (toD d) := by
  simp only [Pi.single_apply, Equiv.eq_symm_apply]

/-- generic count update (Γ version) -/
lemma inv_updateP (T : Finset (Dih A)) (b₁ : A) (ds : List (Pw A k z)) (γ : Dih A → ℚ)
    (h : InvP S T b₁ ds γ) (s : Dih A) (ds' : List (Pw A k z)) (q : ℕ) (hq : 0 < q)
    (hS' : ∀ d ∈ ds', d ∈ S) (hN : (verts 1 ds').Nodup)
    (hM : ∀ x, x ∈ verts 1 ds' ↔ PT (insert s T) b₁ (toD x))
    (hlen : (verts 1 ds').length = q * (verts 1 ds).length)
    (hpc : ∀ d, pc d ds' = q * pc d ds + (q - 1) * pc d [toD.symm s]) :
    InvP S (insert s T) b₁ ds' (γ + Pi.single s (vD (insert s T) - vD T)) := by
  obtain ⟨-, hnd, hmem, hcnt⟩ := h
  refine ⟨hS', hN, hM, ?_⟩
  intro d
  have hv1 := vD_eqP T b₁ _ hnd hmem
  have hv2 := vD_eqP (insert s T) b₁ _ hN hM
  rw [hv1, hv2, hlen, hpc]
  have hL : (0 : ℚ) < (verts 1 ds).length := by
    exact_mod_cast List.length_pos_of_mem (mem_verts_self 1 ds)
  have hqq : (0 : ℚ) < q := by exact_mod_cast hq
  have hc := hcnt d
  have hps := pc_single_g d (toD.symm s)
  rw [single_toD, single_toD] at hps
  simp only [Pi.add_apply]
  rw [show (Pi.single s (((Fintype.card (Dih A) : ℚ) - Fintype.card (Dih A) /
      ((q * (verts 1 ds).length : ℕ) : ℚ)) -
      ((Fintype.card (Dih A) : ℚ) - Fintype.card (Dih A) / ((verts 1 ds).length : ℚ))) :
        Dih A → ℚ) =
      (((Fintype.card (Dih A) : ℚ) - Fintype.card (Dih A) / ((q * (verts 1 ds).length : ℕ) : ℚ)) -
      ((Fintype.card (Dih A) : ℚ) - Fintype.card (Dih A) / ((verts 1 ds).length : ℚ))) •
        (Pi.single s (1 : ℚ) : Dih A → ℚ) by rw [← Pi.single_smul, smul_eq_mul, mul_one]]
  simp only [Pi.smul_apply, smul_eq_mul]
  push_cast [Nat.cast_sub (Nat.one_le_iff_ne_zero.2 hq.ne')]
  generalize ((verts 1 ds).length : ℚ) = L at hL hc ⊢
  generalize (Fintype.card (Dih A) : ℚ) = N at hc ⊢
  generalize (Pi.single s (1 : ℚ) : Dih A → ℚ) (toD d) = I1 at hps ⊢
  generalize (Pi.single s (1 : ℚ) : Dih A → ℚ) (toD d⁻¹) = I2 at hps ⊢
  rw [hps]
  have hcc : (q : ℚ) * L * (N - N / (q * L) - (N - N / L)) = q * N - N := by
    field_simp; ring
  linear_combination (q : ℚ) * hc - (I1 + I2) * hcc

omit [Fintype A] in
lemma prod_memP (ds : List (Pw A k z)) : ds.prod ∈ verts 1 ds := by
  simpa using prod_mem_verts (1 : Pw A k z) ds

omit [Fintype A] [DecidableEq A] in
lemma peq_rot (x : Pw A k z) (h : x.s = false) : x = prot x.r := by
  rcases peq_rot_or_ref x with h1 | h1
  · exact h1
  · rw [h1] at h; exact absurd h (by simp)

omit [Fintype A] [DecidableEq A] in
lemma peq_ref (x : Pw A k z) (h : x.s = true) : x = pref x.r := by
  rcases peq_rot_or_ref x with h1 | h1
  · rw [h1] at h; exact absurd h (by simp)
  · exact h1

lemma natc_inj (q : ℕ) : ∀ t t', t < q → t' < q → (q : ℤ) ∣ ((t : ℤ)) - (t' : ℤ) → t = t' :=
  fun t t' ht ht' h => eq_of_dvd_sub_lt q t t' ht ht' h

/-- S3: add a rotation when the path ends on side 0 (directed snake) -/
lemma stepS3P (T : Finset (Dih A)) (b₁ : A) (ds : List (Pw A k z)) (γ : Dih A → ℚ)
    (h : InvP S T b₁ ds γ) (he : ds.prod.s = false) (r : A) (hr : prot r ∈ S) :
    ∃ ds', InvP S (insert (rot r) T) b₁ ds'
      (γ + Pi.single (rot r) (vD (insert (rot r) T) - vD T)) ∧ ds'.prod.s = false := by
  have h' := h
  obtain ⟨hS, hnd, hmem, -⟩ := h'
  have heq := peq_rot ds.prod he
  have hw : ds.prod.r ∈ KT T := by
    have := (hmem _).1 (prod_memP ds)
    rw [heq, toD_prot, pt_rot] at this
    exact this
  obtain ⟨δ, hδ⟩ : ∃ δ, δ = ds.prod.r + r := ⟨_, rfl⟩
  obtain ⟨q, hq⟩ : ∃ q, q = addOrderOf ((δ : A ⧸ KT T)) := ⟨_, rfl⟩
  have hq0 : 0 < q := hq ▸ addOrderOf_pos _
  have hg : ∀ i : ℕ, (ds.prod * prot r) ^ i = prot (((i : ℕ) : ℤ) • δ) := by
    intro i; rw [heq, prot_mul_prot, prot_pow, ← hδ, natCast_zsmul]
  have hverts : verts 1 (dsnk ds (prot r) (q - 1)) =
      (List.range q).flatMap (fun i => (verts 1 ds).map (prot (((i : ℕ) : ℤ) • δ) * ·)) := by
    rw [verts_dsnk, Nat.sub_add_cancel hq0]
    simp only [hg]
  obtain ⟨hN, hM, hL⟩ := blocksP (hasRef T) (KT T) b₁ δ (fun i => (i : ℤ)) (natc_inj _)
    (verts 1 ds) hnd hmem (fun i => (verts 1 ds).map (prot (((i : ℕ) : ℤ) • δ) * ·))
    (fun i => Or.inl rfl)
  rw [← hq] at hN hM hL
  refine ⟨dsnk ds (prot r) (q - 1), inv_updateP S T b₁ ds γ h (rot r) _ q hq0
    (mem_dsnk ds hS (prot r) hr _) (by rw [hverts]; exact hN) ?_ ?_ ?_, ?_⟩
  · intro x
    rw [hverts, hM, PT, hasRef_insert_rot, KT_insert_rot, sup_zmult_add (KT T) _ r hw, ← hδ]
  · rw [hverts, hL]
  · intro d; rw [pc_dsnk, Nat.sub_add_cancel hq0, toD_symm_rot]
  · rw [prod_dsnk, hg, heq, prot_mul_prot]; rfl

include hinv in
/-- S2: add a reflection when the path ends on side 1; the joins use `(ref b)⁻¹` -/
lemma stepS2P (T : Finset (Dih A)) (b₁ : A) (ds : List (Pw A k z)) (γ : Dih A → ℚ)
    (h : InvP S T b₁ ds γ) (hb₁ : ref b₁ ∈ T) (he : ds.prod.s = true) (b : A)
    (hb : pref b ∈ S) :
    ∃ ds', InvP S (insert (ref b) T) b₁ ds'
      (γ + Pi.single (ref b) (vD (insert (ref b) T) - vD T)) ∧ ds'.prod.s = true := by
  have h' := h
  obtain ⟨hS, hnd, hmem, -⟩ := h'
  have heq := peq_ref ds.prod he
  have hT : hasRef T = true := hasRef_of_mem T b₁ hb₁
  have hw : ds.prod.r - b₁ ∈ KT T := by
    have := (hmem _).1 (prod_memP ds)
    rw [heq, toD_pref, pt_ref] at this
    exact this.2
  obtain ⟨δ, hδ⟩ : ∃ δ, δ = ds.prod.r - b := ⟨_, rfl⟩
  obtain ⟨q, hq⟩ : ∃ q, q = addOrderOf ((δ : A ⧸ KT T)) := ⟨_, rfl⟩
  have hq0 : 0 < q := hq ▸ addOrderOf_pos _
  have hj : (pref b : Pw A k z)⁻¹ ∈ S := hinv _ hb
  have hg : ∀ i : ℕ, (ds.prod * (pref b)⁻¹) ^ i = prot (((i : ℕ) : ℤ) • δ) := by
    intro i; rw [heq, pref_mul_pref_inv, prot_pow, ← hδ, natCast_zsmul]
  have hverts : verts 1 (dsnk ds (pref b)⁻¹ (q - 1)) =
      (List.range q).flatMap (fun i => (verts 1 ds).map (prot (((i : ℕ) : ℤ) • δ) * ·)) := by
    rw [verts_dsnk, Nat.sub_add_cancel hq0]
    simp only [hg]
  obtain ⟨hN, hM, hL⟩ := blocksP (hasRef T) (KT T) b₁ δ (fun i => (i : ℤ)) (natc_inj _)
    (verts 1 ds) hnd hmem (fun i => (verts 1 ds).map (prot (((i : ℕ) : ℤ) • δ) * ·))
    (fun i => Or.inl rfl)
  rw [← hq] at hN hM hL
  refine ⟨dsnk ds (pref b)⁻¹ (q - 1), inv_updateP S T b₁ ds γ h (ref b) _ q hq0
    (mem_dsnk ds hS _ hj _) (by rw [hverts]; exact hN) ?_ ?_ ?_, ?_⟩
  · intro x
    rw [hverts, hM, PT, hasRef_insert_ref, hT, KT_insert_ref T b b₁ _ hb₁ hw, ← hδ]
  · rw [hverts, hL]
  · intro d; rw [pc_dsnk, Nat.sub_add_cancel hq0, toD_symm_ref, pc_inv]
  · rw [prod_dsnk, hg, heq, prot_mul_pref]; rfl

/-- S1: the first reflection (two blocks; side-1 block moves by `k •`) -/
lemma stepS1P (T : Finset (Dih A)) (b₁ : A) (ds : List (Pw A k z)) (γ : Dih A → ℚ)
    (h : InvP S T b₁ ds γ) (hT : hasRef T = false) (he : ds.prod.s = false) (hb : pref b₁ ∈ S) :
    ∃ ds', InvP S (insert (ref b₁) T) b₁ ds'
      (γ + Pi.single (ref b₁) (vD (insert (ref b₁) T) - vD T)) ∧ ds'.prod.s = true := by
  have h' := h
  obtain ⟨hS, hnd, hmem, -⟩ := h'
  have heq := peq_rot ds.prod he
  have hw : ds.prod.r ∈ KT T := by
    have := (hmem _).1 (prod_memP ds)
    rw [heq, toD_prot, pt_rot] at this
    exact this
  have hg : ds.prod * pref b₁ = pref (ds.prod.r + b₁) := by rw [heq, prot_mul_pref]; rfl
  have hverts : verts 1 (ds ++ pref b₁ :: ds) =
      verts 1 ds ++ (verts 1 ds).map (pref (ds.prod.r + b₁) * ·) := by
    rw [verts_append, one_mul, hg, verts_eq (pref (ds.prod.r + b₁)) ds]
  have hside : ∀ x ∈ verts 1 ds, x.s = false := by
    intro x hx
    have := (hmem x).1 hx
    rcases peq_rot_or_ref x with h1 | h1
    · rw [h1]; rfl
    · rw [h1, toD_pref, pt_ref, hT] at this; exact absurd this.1 (by simp)
  have hM : ∀ x, x ∈ verts 1 (ds ++ pref b₁ :: ds) ↔ PT (insert (ref b₁) T) b₁ (toD x) := by
    intro x
    rw [hverts, List.mem_append, mem_map_mul, hmem, hmem]
    simp only [PT]
    rw [hasRef_insert_ref, KT_insert_ref_first T b₁ hT, hT]
    rcases peq_rot_or_ref x with hx | hx <;> rw [hx]
    · rw [pref_inv, pref_mul_prot, toD_prot, toD_pref, xp_rot, xp_ref, xp_rot]; simp
    · rw [pref_inv, pref_mul_pref, toD_pref, toD_prot, xp_ref, xp_rot, xp_ref]
      simp only [Bool.false_eq_true, false_and, false_or, true_and]
      rw [show -(k • (ds.prod.r + b₁)) - z + k • x.r + z = k • (x.r - b₁ - ds.prod.r) by
        rw [smul_sub, smul_sub, smul_add]; abel, k_mem_iff]
      constructor
      · intro h2
        rw [show x.r - b₁ = (x.r - b₁ - ds.prod.r) + ds.prod.r by abel]
        exact add_mem h2 hw
      · intro h2
        exact sub_mem h2 hw
  refine ⟨ds ++ pref b₁ :: ds, inv_updateP S T b₁ ds γ h (ref b₁) _ 2 (by norm_num) ?_ ?_ hM ?_ ?_, ?_⟩
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
    obtain ⟨w, hwm, rfl⟩ := List.mem_map.1 hy
    have h2 := hside w hwm
    rw [peq_rot w h2, pref_mul_prot] at h1
    simp at h1
  · rw [hverts, List.length_append, List.length_map]; ring
  · intro d; rw [pc_append, toD_symm_ref]; omega
  · rw [List.prod_append, List.prod_cons, ← mul_assoc, hg, heq, pref_mul_prot]; rfl

include hinv in
/-- S4: add a rotation when the path ends on side 1 (alternating snake, Lemma A) -/
lemma stepS4P (T : Finset (Dih A)) (b₁ : A) (ds : List (Pw A k z)) (γ : Dih A → ℚ)
    (h : InvP S T b₁ ds γ) (he : ds.prod.s = true) (r : A) (hr : prot r ∈ S)
    (hH : Hq k (addOrderOf ((r : A ⧸ KT T)))) :
    ∃ ds', InvP S (insert (rot r) T) b₁ ds'
      (γ + Pi.single (rot r) (vD (insert (rot r) T) - vD T)) := by
  have h' := h
  obtain ⟨hS, hnd, hmem, -⟩ := h'
  have heq := peq_ref ds.prod he
  obtain ⟨q, hq⟩ : ∃ q, q = addOrderOf ((r : A ⧸ KT T)) := ⟨_, rfl⟩
  have hq0 : 0 < q := hq ▸ addOrderOf_pos _
  rw [← hq] at hH
  obtain ⟨c, hc0, hceven, hcodd, hcinj⟩ := lemmaA k q hq0 hH
  -- the joins
  let jn : ℕ → Pw A k z := fun t =>
    if Even t then (if c (t + 1) - c t = k then prot r else prot (-r))
    else prot ((c (t + 1) - c t) • r)
  have hrS : prot (-r) ∈ S := by rw [← prot_inv (k := k) (z := z) r]; exact hinv _ hr
  have hjnS : ∀ t, jn t ∈ S := by
    intro t
    simp only [jn]
    by_cases ht : Even t
    · rw [if_pos ht]; split_ifs
      · exact hr
      · exact hrS
    · rw [if_neg ht]
      rcases hcodd t ht with h1 | h1 <;> rw [h1]
      · rw [one_zsmul]; exact hr
      · rw [neg_one_zsmul]; exact hrS
  have hjnpc : ∀ d t, pc d [jn t] = pc d [prot r] := by
    have hm : ∀ d, pc d [prot (-r)] = pc d [prot r] := fun d => by
      rw [← prot_inv (k := k) (z := z) r, pc_inv]
    intro d t
    simp only [jn]
    by_cases ht : Even t
    · rw [if_pos ht]; split_ifs
      · rfl
      · exact hm d
    · rw [if_neg ht]
      rcases hcodd t ht with h1 | h1 <;> rw [h1]
      · rw [one_zsmul]
      · rw [neg_one_zsmul]; exact hm d
  -- the bases
  have hbase : ∀ t, gbase ds.prod jn t = prot (c t • r) := by
    intro t
    induction t with
    | zero => rw [hc0, zero_zsmul]; rfl
    | succ t ih =>
      rw [gbase]
      by_cases ht : Even t
      · rw [if_pos ht, ih, mul_assoc, mul_assoc, ← mul_assoc ds.prod]
        have hj : ds.prod * jn t * ds.prod⁻¹ = prot ((c (t + 1) - c t) • r) := by
          simp only [jn, if_pos ht]
          rw [heq]
          rcases hceven t ht with h1 | h1
          · rw [if_pos h1, pref_conj, h1]
          · by_cases hck : c (t + 1) - c t = k
            · rw [if_pos hck, pref_conj, hck]
            · rw [if_neg hck, pref_conj, h1, smul_neg, neg_zsmul]
        rw [hj, prot_mul_prot, ← add_zsmul]; congr 2; ring
      · rw [if_neg ht, ih]
        simp only [jn, if_neg ht]
        rw [prot_mul_prot, ← add_zsmul]; congr 2; ring
  have hverts : verts 1 (gsn ds jn (q - 1)) =
      (List.range q).flatMap (fun i =>
        (if Even i then verts 1 ds else (verts 1 ds).reverse).map (prot (c i • r) * ·)) := by
    rw [(gsn_spec ds jn (q - 1)).2, Nat.sub_add_cancel hq0]
    simp only [hbase]
  obtain ⟨hN, hM, hL⟩ := blocksP (hasRef T) (KT T) b₁ r c (by rw [← hq]; exact hcinj)
    (verts 1 ds) hnd hmem
    (fun i => (if Even i then verts 1 ds else (verts 1 ds).reverse).map (prot (c i • r) * ·))
    (fun i => by by_cases hi : Even i <;> simp [hi])
  rw [← hq] at hN hM hL
  refine ⟨gsn ds jn (q - 1), inv_updateP S T b₁ ds γ h (rot r) _ q hq0
    (mem_gsn hinv ds hS jn hjnS _) (by rw [hverts]; exact hN) ?_ ?_ ?_⟩
  · intro x
    rw [hverts, hM, PT, hasRef_insert_rot, KT_insert_rot]
  · rw [hverts, hL]
  · intro d
    rw [pc_gsn d ds jn (prot r) (hjnpc d), Nat.sub_add_cancel hq0, toD_symm_rot]

end Steps

end FTDih

-- ===== FTPowerMain.lean =====

/-!
# Theorem 8 (FT-POWER.md): Fair Traversal for Cayley graphs of Γ(A, k, z)

Hypotheses: `A` finite abelian, `k • k • a = a` for all `a`, `k • z = z`, and
(O) `∃ ε = ±1, ∀ a, Odd (addOrderOf a) → k • a = ε • a` (equivalent to `k ≡ ε` mod the odd part of
the exponent). Conclusion: #339 word for word.

The Weber step and the inequalities are done in the Dih model on `S_D = toD '' S` (same `A`, `R`, `F`;
by Lemma 0 the game is the same); greedy vectors are pulled back along `toD` (`LinearMap.funLeft`).
-/

open Finset

namespace FTDih

section Phases
variable {A : Type} [AddCommGroup A] [Fintype A] [DecidableEq A] {k : ℤ} {z : A}
  [Fact (∀ a : A, k • k • a = a)] [Fact (k • z = z)]
  (S : Finset (Pw A k z)) (hinv : ∀ s ∈ S, s⁻¹ ∈ S)

/-- the Dih image of `S` -/
def SD : Finset (Dih A) := S.map (toD : Pw A k z ≃ Dih A).toEmbedding

omit [Fintype A] [Fact (∀ a : A, k • k • a = a)] [Fact (k • z = z)] in
lemma mem_SD (x : Dih A) : x ∈ SD S ↔ toD.symm x ∈ S := by
  rw [SD, Finset.mem_map_equiv]

lemma inv_initP (b₁ : A) : InvP S ∅ b₁ [] 0 := by
  refine ⟨by simp, by simp, fun x => ?_, fun d => by simp [pc]⟩
  have h0 : hasRef (∅ : Finset (Dih A)) = false := by simp [hasRef]
  rw [PT, h0, KT_empty]
  rcases x with ⟨a, i⟩
  cases i <;> simp [XP, Pw.ext_iff]

lemma phaseR1P (b₁ : A) : ∀ (L : List (Dih A)), (∀ x ∈ L, x ∈ SD S ∧ x.s = false) →
    ∀ T ds γ, InvP S T b₁ ds γ → ds.prod.s = false →
    ∃ ds', InvP S (T ∪ L.toFinset) b₁ ds' (γ + FTAbelian.greedy vD T L) ∧ ds'.prod.s = false := by
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
    rw [hx, mem_SD, toD_symm_rot] at hxS
    obtain ⟨ds1, h1, he1⟩ := stepS3P S T b₁ ds γ h he x.r hxS
    rw [← hx] at h1
    obtain ⟨ds2, h2, he2⟩ := ih (fun y hy => hL y (by simp [hy])) _ ds1 _ h1 he1
    refine ⟨ds2, ?_, he2⟩
    rw [FTAbelian.greedy_cons, ← add_assoc, union_insert_eq]
    exact h2

include hinv in
lemma phaseFP (b₁ : A) : ∀ (L : List (Dih A)), (∀ x ∈ L, x ∈ SD S ∧ x.s = true) →
    ∀ T ds γ, InvP S T b₁ ds γ → ref b₁ ∈ T → ds.prod.s = true →
    ∃ ds', InvP S (T ∪ L.toFinset) b₁ ds' (γ + FTAbelian.greedy vD T L) ∧ ds'.prod.s = true := by
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
    rw [hx, mem_SD, toD_symm_ref] at hxS
    obtain ⟨ds1, h1, he1⟩ := stepS2P S hinv T b₁ ds γ h hb₁ he x.r hxS
    rw [← hx] at h1
    obtain ⟨ds2, h2, he2⟩ := ih (fun y hy => hL y (by simp [hy])) _ ds1 _ h1
      (Finset.mem_insert_of_mem hb₁) he1
    refine ⟨ds2, ?_, he2⟩
    rw [FTAbelian.greedy_cons, ← add_assoc, union_insert_eq]
    exact h2

include hinv in
lemma phaseR2P (hH : ∀ (K : AddSubgroup A) (r : A), Hq k (addOrderOf ((r : A ⧸ K))))
    (b₁ : A) : ∀ (L : List (Dih A)), (∀ x ∈ L, x ∈ SD S ∧ x.s = false) →
    ∀ T ds γ, InvP S T b₁ ds γ →
    ∃ ds', InvP S (T ∪ L.toFinset) b₁ ds' (γ + FTAbelian.greedy vD T L) := by
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
    rw [hx, mem_SD, toD_symm_rot] at hxS
    obtain ⟨ds1, h1⟩ : ∃ ds1, InvP S (insert (rot x.r) T) b₁ ds1
        (γ + Pi.single (rot x.r) (vD (insert (rot x.r) T) - vD T)) := by
      cases he : ds.prod.s
      · exact (stepS3P S T b₁ ds γ h he x.r hxS).imp fun _ h => h.1
      · exact stepS4P S hinv T b₁ ds γ h he x.r hxS (hH _ _)
    rw [← hx] at h1
    obtain ⟨ds2, h2⟩ := ih (fun y hy => hL y (by simp [hy])) _ ds1 _ h1
    refine ⟨ds2, ?_⟩
    rw [FTAbelian.greedy_cons, ← add_assoc, union_insert_eq]
    exact h2

lemma real_of_invP (b₁ : A) (ds : List (Pw A k z)) (γ : Dih A → ℚ) (h : InvP S (SD S) b₁ ds γ)
    (hall : ∀ g : Pw A k z, PT (SD S) b₁ (toD g)) : (fun d => γ (toD d)) ∈ Real S := by
  obtain ⟨hS, hnd, hmem, hcnt⟩ := h
  have hall' : ∀ g, g ∈ verts 1 ds := fun g => (hmem g).2 (hall g)
  have hlen : (verts 1 ds).length = Fintype.card (Dih A) := by
    rw [← card_pw (k := k) (z := z), ← List.toFinset_card_of_nodup hnd]
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

lemma lR_specP (L : List (Dih A)) (hL : L.toFinset = SD S) :
    ∀ x ∈ lR L, x ∈ SD S ∧ x.s = false := lR_spec (SD S) L hL
lemma lF_specP (L : List (Dih A)) (hL : L.toFinset = SD S) :
    ∀ x ∈ lF L, x ∈ SD S ∧ x.s = true := lF_spec (SD S) L hL

include hinv in
/-- **Family 1** in Γ (rotations first) -/
theorem real1P (L : List (Dih A)) (hL : L.toFinset = SD S) (hF : ∃ x ∈ SD S, x.s = true)
    (hall : ∀ b₁, ref b₁ ∈ SD S → ∀ g : Pw A k z, PT (SD S) b₁ (toD g)) :
    (fun d => FTAbelian.greedy vD ∅ (lR L ++ lF L) (toD d)) ∈ Real S := by
  obtain ⟨b₁, L', hLF⟩ := lF_cons (SD S) L hL hF
  have hb₁S : ref b₁ ∈ SD S := (lF_specP S L hL (ref b₁) (by rw [hLF]; simp)).1
  have hb₁S' : pref b₁ ∈ S := by rw [mem_SD, toD_symm_ref] at hb₁S; exact hb₁S
  obtain ⟨ds1, h1, he1⟩ := phaseR1P S b₁ (lR L) (lR_specP S L hL) ∅ [] 0 (inv_initP S b₁)
    (by simp)
  obtain ⟨ds2, h2, he2⟩ := stepS1P S _ b₁ ds1 _ h1 (hasRef_lR L) he1 hb₁S'
  obtain ⟨ds3, h3, -⟩ := phaseFP S hinv b₁ L'
    (fun x hx => lF_specP S L hL x (by rw [hLF]; simp [hx])) _ ds2 _ h2
    (Finset.mem_insert_self _ _) he2
  have hT : insert (ref b₁) (∅ ∪ (lR L).toFinset) ∪ L'.toFinset = SD S := by
    rw [← hL]; ext x
    simp only [Finset.mem_union, Finset.mem_insert, Finset.empty_union, List.mem_toFinset,
      Finset.notMem_empty, false_or]
    rw [mem_lRF L x, hLF]; simp; tauto
  rw [hT] at h3
  have hγ : FTAbelian.greedy vD ∅ (lR L ++ lF L) =
      0 + FTAbelian.greedy vD ∅ (lR L) +
        Pi.single (ref b₁) (vD (insert (ref b₁) (∅ ∪ (lR L).toFinset)) -
          vD (∅ ∪ (lR L).toFinset)) +
        FTAbelian.greedy vD (insert (ref b₁) (∅ ∪ (lR L).toFinset)) L' := by
    rw [FTAbelian.greedy_append, hLF, FTAbelian.greedy_cons, zero_add, add_assoc]
  rw [hγ]
  exact real_of_invP S b₁ ds3 _ h3 (hall b₁ hb₁S)

include hinv in
/-- **Family 2** in Γ (reflections first) -/
theorem real2P (hH : ∀ (K : AddSubgroup A) (r : A), Hq k (addOrderOf ((r : A ⧸ K))))
    (L : List (Dih A)) (hL : L.toFinset = SD S) (hF : ∃ x ∈ SD S, x.s = true)
    (hall : ∀ b₁, ref b₁ ∈ SD S → ∀ g : Pw A k z, PT (SD S) b₁ (toD g)) :
    (fun d => FTAbelian.greedy vD ∅ (lF L ++ lR L) (toD d)) ∈ Real S := by
  obtain ⟨b₁, L', hLF⟩ := lF_cons (SD S) L hL hF
  have hb₁S : ref b₁ ∈ SD S := (lF_specP S L hL (ref b₁) (by rw [hLF]; simp)).1
  have hb₁S' : pref b₁ ∈ S := by rw [mem_SD, toD_symm_ref] at hb₁S; exact hb₁S
  obtain ⟨ds1, h1, he1⟩ := stepS1P S ∅ b₁ [] 0 (inv_initP S b₁) (by simp [hasRef]) (by simp)
    hb₁S'
  obtain ⟨ds2, h2, -⟩ := phaseFP S hinv b₁ L'
    (fun x hx => lF_specP S L hL x (by rw [hLF]; simp [hx])) _ ds1 _ h1
    (Finset.mem_insert_self _ _) he1
  obtain ⟨ds3, h3⟩ := phaseR2P S hinv hH b₁ (lR L) (lR_specP S L hL) _ ds2 _ h2
  have hT : insert (ref b₁) (∅ : Finset (Dih A)) ∪ L'.toFinset ∪ (lR L).toFinset = SD S := by
    rw [← hL]; ext x
    simp only [Finset.mem_union, Finset.mem_insert, List.mem_toFinset,
      Finset.notMem_empty, or_false]
    rw [mem_lRF L x, hLF]; simp; tauto
  rw [hT] at h3
  have hγ : FTAbelian.greedy vD ∅ (lF L ++ lR L) =
      0 + Pi.single (ref b₁) (vD (insert (ref b₁) (∅ : Finset (Dih A))) -
          vD (∅ : Finset (Dih A))) +
        FTAbelian.greedy vD (insert (ref b₁) ∅) L' +
        FTAbelian.greedy vD (insert (ref b₁) ∅ ∪ L'.toFinset) (lR L) := by
    rw [FTAbelian.greedy_append, hLF, FTAbelian.greedy_cons, zero_add,
      show (∅ : Finset (Dih A)) ∪ (ref b₁ :: L').toFinset = insert (ref b₁) ∅ ∪ L'.toFinset by
        ext; simp]
  rw [hγ]
  exact real_of_invP S b₁ ds3 _ h3 (hall b₁ hb₁S)

end Phases

section HO
variable {A : Type} [AddCommGroup A] [Fintype A] {k : ℤ}

/-- (O) gives the hypothesis of Lemma A for every block count -/
lemma hH_of_O (hk : ∀ a : A, k • k • a = a)
    (hO : ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ ∀ a : A, Odd (addOrderOf a) → k • a = ε • a)
    (K : AddSubgroup A) (r : A) : Hq k (addOrderOf ((r : A ⧸ K))) := by
  set q := addOrderOf ((r : A ⧸ K)) with hq
  have hqr : q • (r : A ⧸ K) = 0 := addOrderOf_nsmul_eq_zero _
  by_cases hq2 : Even q
  · right
    refine ⟨hq2, ?_⟩
    apply (addOrderOf_dvd_iff_zsmul_eq_zero).2
    rw [← QuotientAddGroup.mk_zsmul, sub_smul, one_smul, ← smul_smul, hk, sub_self,
      QuotientAddGroup.mk_zero]
  · left
    obtain ⟨ε, hε, hOε⟩ := hO
    refine ⟨ε, hε, ?_⟩
    have hqodd : Odd q := Nat.not_even_iff_odd.1 hq2
    obtain ⟨s, m', hm', hM⟩ := Nat.exists_eq_two_pow_mul_odd (addOrderOf_pos r).ne'
    have hodd : Odd (addOrderOf ((2 ^ s) • r)) := by
      apply Odd.of_dvd_nat hm'
      apply addOrderOf_dvd_of_nsmul_eq_zero
      rw [smul_smul, mul_comm, ← hM, addOrderOf_nsmul_eq_zero]
    have h1 := hOε _ hodd
    -- y = (k - ε) • r̄ has order dividing 2^s and q
    set y : A ⧸ K := (k - ε) • (r : A ⧸ K) with hy
    have hy1 : (2 ^ s) • y = 0 := by
      rw [hy, smul_comm, ← QuotientAddGroup.mk_nsmul, ← QuotientAddGroup.mk_zsmul, sub_smul, h1,
        sub_self, QuotientAddGroup.mk_zero]
    have hy2 : q • y = 0 := by rw [hy, smul_comm, hqr, smul_zero]
    have hd1 := addOrderOf_dvd_of_nsmul_eq_zero hy1
    have hd2 := addOrderOf_dvd_of_nsmul_eq_zero hy2
    have hcop : Nat.Coprime (2 ^ s) q := (Nat.coprime_two_left.2 hqodd).pow_left s
    have h3 : addOrderOf y ∣ 1 := by
      rw [← hcop.gcd_eq_one]; exact Nat.dvd_gcd hd1 hd2
    have hy0 : y = 0 := AddMonoid.addOrderOf_eq_one_iff.1 (Nat.dvd_one.1 h3)
    exact (addOrderOf_dvd_iff_zsmul_eq_zero).2 hy0

/-- (O) holds for 2-groups (with `ε = 1`) -/
lemma O_of_two_group (n : ℕ) (hA : Fintype.card A = 2 ^ n) :
    ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ ∀ a : A, Odd (addOrderOf a) → k • a = ε • a := by
  refine ⟨1, Or.inl rfl, fun a ha => ?_⟩
  have h1 : addOrderOf a ∣ 2 ^ n := hA ▸ addOrderOf_dvd_card
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h1
  have hi0 : i = 0 := by
    by_contra h0
    rw [hi] at ha
    exact (Nat.not_even_iff_odd.2 ha) ((Nat.even_pow' h0).2 even_two)
  rw [hi0, pow_zero] at hi
  rw [AddMonoid.addOrderOf_eq_one_iff.1 hi, smul_zero, smul_zero]

end HO

section Main
variable {A : Type} [AddCommGroup A] [Fintype A] [DecidableEq A] {k : ℤ} {z : A}
  [Fact (∀ a : A, k • k • a = a)] [Fact (k • z = z)]

lemma pt_closedP (S : Finset (Pw A k z)) (hinv : ∀ s ∈ S, s⁻¹ ∈ S) (b₁ : A)
    (hb₁ : ref b₁ ∈ SD S) (x s : Pw A k z) (hx : PT (SD S) b₁ (toD x)) (hs : s ∈ S) :
    PT (SD S) b₁ (toD (x * s)) := by
  have hR : hasRef (SD S) = true := hasRef_of_mem _ b₁ hb₁
  have hrot : ∀ c, prot c ∈ S → c ∈ KT (SD S) := fun c hc =>
    AddSubgroup.subset_closure (Or.inl (show rot c ∈ SD S by rw [mem_SD]; exact hc))
  have href : ∀ c, pref c ∈ S → c - b₁ ∈ KT (SD S) := fun c hc =>
    AddSubgroup.subset_closure (Or.inr ⟨c, (show ref c ∈ SD S by rw [mem_SD]; exact hc), b₁,
      hb₁, rfl⟩)
  rcases peq_rot_or_ref x with hx' | hx' <;> rcases peq_rot_or_ref s with hs' | hs' <;>
    rw [hx'] at hx <;> rw [hs'] at hs <;> rw [hx', hs']
  · rw [prot_mul_prot, toD_prot, pt_rot]; rw [toD_prot, pt_rot] at hx
    exact add_mem hx (hrot _ hs)
  · rw [prot_mul_pref, toD_pref, pt_ref]; rw [toD_prot, pt_rot] at hx
    exact ⟨hR, by rw [add_sub_assoc]; exact add_mem hx (href _ hs)⟩
  · rw [pref_mul_prot, toD_pref, pt_ref]; rw [toD_pref, pt_ref] at hx
    exact ⟨hR, by
      rw [show x.r + k • s.r - b₁ = (x.r - b₁) + k • s.r by abel]
      exact add_mem hx.2 (k_mem _ _ (hrot _ hs))⟩
  · rw [pref_mul_pref, toD_prot, pt_rot]; rw [toD_pref, pt_ref] at hx
    have hi := href _ (by have := hinv _ hs; rwa [pref_inv] at this)
    rw [show x.r + k • s.r + z = (x.r - b₁) - ((-(k • s.r) - z) - b₁) by abel]
    exact sub_mem hx.2 hi

/-- **Theorem 8.** Fair Traversal for every connected Cayley graph of `Γ(A, k, z)` under (O). -/
theorem ft_pow (hO : ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ ∀ a : A, Odd (addOrderOf a) → k • a = ε • a)
    (S : Finset (Pw A k z)) (G : SimpleGraph (Pw A k z))
    (hG : ∀ x y, G.Adj x y ↔ x⁻¹ * y ∈ S) (hc : G.Connected) :
    ∃ (r k' : ℕ), 0 < r ∧ 0 < k' ∧
      ∃ (a b : Fin r → Pw A k z) (P : ∀ i, G.Walk (a i) (b i)),
        (∀ i, (P i).IsHamiltonian) ∧
        ∀ e ∈ G.edgeSet, (Finset.univ.filter fun i => e ∈ (P i).edges).card = k' := by
  classical
  have hinv := inv_mem_of S G hG
  have hS1 := one_not_mem_of S G hG
  have hH : ∀ (K : AddSubgroup A) (r : A), Hq k (addOrderOf ((r : A ⧸ K))) :=
    hH_of_O (fun a => kk a) hO
  -- the Dih image
  have hS1D : (1 : Dih A) ∉ SD S := by
    rw [mem_SD]; exact hS1
  have hinvD : ∀ s ∈ SD S, s⁻¹ ∈ SD S := by
    intro s hs
    rcases eq_rot_or_ref s with h | h <;> rw [h] at hs ⊢
    · rw [rot_inv, mem_SD, toD_symm_rot]
      rw [mem_SD, toD_symm_rot] at hs
      have := hinv _ hs; rwa [prot_inv] at this
    · rw [ref_inv]; exact hs
  have hF : ∃ x ∈ SD S, x.s = true := by
    by_contra hno
    push_neg at hno
    have := all_of_connected S G hG hc (fun g => g.s = false) rfl (fun x s hx hs => by
      have := hno (toD s) (by rw [mem_SD]; simpa using hs)
      simp only [Bool.not_eq_true, toD_s] at this
      show (x * s).s = false
      rcases peq_rot_or_ref x with h1 | h1 <;> rcases peq_rot_or_ref s with h2 | h2
      · rw [h1, h2, prot_mul_prot]; rfl
      · rw [h2] at this; simp at this
      · rw [h1] at hx; simp at hx
      · rw [h2] at this; simp at this) (pref 0)
    simp at this
  obtain ⟨x0, hx0S, hx0s⟩ := hF
  have hx0 : x0 = ref x0.r := by
    rcases eq_rot_or_ref x0 with h | h
    · rw [h] at hx0s; exact absurd hx0s (by simp)
    · exact h
  set b₁ := x0.r
  have hb₁ : ref b₁ ∈ SD S := hx0 ▸ hx0S
  have hall : ∀ b, ref b ∈ SD S → ∀ g : Pw A k z, PT (SD S) b (toD g) := fun b hb =>
    all_of_connected S G hG hc (fun g => PT (SD S) b (toD g))
      (by show PT (SD S) b (rot 0); rw [pt_rot]; exact zero_mem _)
      (fun x s hx hs => pt_closedP S hinv b hb x s hx hs)
  have hKS : KT (SD S) = ⊤ := by
    rw [eq_top_iff]
    intro a _
    have := hall b₁ hb₁ (prot a)
    rwa [toD_prot, pt_rot] at this
  have hFne : (Fs (SD S)).Nonempty := ⟨x0, Finset.mem_filter.2 ⟨hx0S, hx0s⟩⟩
  have Fa := facts (SD S) hS1D hFne
  set SS := SD S with hSS
  -- the blending weight
  set t := lam SS with ht
  have ht01 : 0 ≤ t ∧ t ≤ 1 := by
    by_cases hr : (Rs SS).card = 0
    · rw [ht, lam, if_pos hr]; norm_num
    · have hr1 : (1 : ℚ) ≤ pr SS := by rw [pr]; exact_mod_cast Nat.one_le_iff_ne_zero.2 hr
      have hNl := Nl_pos (pm (A := A)) (pr SS) (pf SS) (pa SS) (pb SS) (cl (Fs SS)) hr1 Fa.hf1
        Fa.hb Fa.hF1 Fa.hbhF Fa.hfF
      have hNb := Nb_nonneg (pm (A := A)) (pr SS) (pf SS) (pa SS) (cl (Rs SS)) (by linarith)
        (by linarith [Fa.hrR]) Fa.hf1 Fa.ha Fa.hahR
      have hD : 0 < pNl SS + pNb SS := by rw [pNl, pNb]; linarith
      rw [ht, lam, if_neg hr]
      refine ⟨div_nonneg (by rw [pNl]; linarith) hD.le, ?_⟩
      rw [div_le_one hD]; rw [pNl, pNb] at *; linarith
  -- the target and the blended game (Dih model)
  set x : Dih A → ℚ := fun s => if s ∈ SS then tgt SS else 0 with hxdef
  set vl : Finset (Dih A) → ℚ := fun X => t * v1 SS X + (1 - t) * v2 SS X with hvl
  have hv0 : vD (∅ : Finset (Dih A)) = 0 := by rw [vD_rot ∅ (by simp), cl_empty]; simp
  have hvl0 : vl ∅ = 0 := by simp [hvl, v1, v2, hv0]
  have hSR : SS.filter (fun x => x.s = false) = Rs SS := rfl
  have hSF : SS.filter (fun x => ¬ x.s = false) = Fs SS := by
    apply Finset.filter_congr; intro x _; cases x.s <;> simp
  have hvS : vD SS = 2 * pm (A := A) - 1 := vD_S SS hKS ⟨x0, hx0S, hx0s⟩
  have hadm : FTAbelian.Adm vl ∅ SS x := by
    refine ⟨fun j hj => by simp [hxdef, hj], fun U hU => ?_, ?_⟩
    · rw [Finset.empty_union, hvl0, sub_zero,
        Finset.sum_congr rfl (fun j hj => if_pos (hU hj)), Finset.sum_const, nsmul_eq_mul]
      have hUR : U.filter (fun x => x.s = false) ⊆ Rs SS := by
        intro y hy; rw [Finset.mem_filter] at hy; exact Finset.mem_filter.2 ⟨hU hy.1, hy.2⟩
      have hUF : U.filter (fun x => ¬ x.s = false) ⊆ Fs SS := by
        intro y hy; rw [Finset.mem_filter] at hy
        exact Finset.mem_filter.2 ⟨hU hy.1, by simpa using hy.2⟩
      have h1 := ineqR SS hS1D hinvD hKS hFne _ hUR
      have h2 := ineqF SS hS1D hKS hFne _ hUF
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
      rw [Finset.union_comm (Rs SS) (Fs SS), Fs_union_Rs, hvS, tgt]
      have : (SS.card : ℚ) ≠ 0 := by rw [Fa.hcard]; linarith [Fa.hf1, pr_nonneg SS]
      field_simp
      ring
  have hx := FTAbelian.weber vl SS.card SS rfl ∅ x hadm
  -- pull back along toD
  let Φ : (Dih A → ℚ) →ₗ[ℚ] (Pw A k z → ℚ) := LinearMap.funLeft ℚ ℚ (toD : Pw A k z → Dih A)
  have hsub : FTAbelian.Gset vl ∅ SS ⊆ Φ ⁻¹' convexHull ℚ (Real S) := by
    rintro y ⟨L, -, hLS, rfl⟩
    show Φ (FTAbelian.greedy vl ∅ L) ∈ convexHull ℚ (Real S)
    rw [hvl, greedy_lin, greedy_v1 SS L hLS, greedy_v2 SS L hLS, map_add, map_smul, map_smul]
    exact convex_convexHull ℚ _
      (subset_convexHull ℚ _ (real1P S hinv L hLS ⟨x0, hx0S, hx0s⟩ hall))
      (subset_convexHull ℚ _ (real2P S hinv hH L hLS ⟨x0, hx0S, hx0s⟩ hall))
      ht01.1 (by linarith [ht01.2]) (by ring)
  have hx' : Φ x ∈ convexHull ℚ (Real S) :=
    convexHull_min hsub ((convex_convexHull ℚ _).linear_preimage Φ) hx
  have htgt : 0 < tgt SS := by
    rw [tgt]
    apply div_pos
    · linarith [Fa.hm, show (1 : ℚ) ≤ pm (A := A) by rw [pm]; exact_mod_cast Fintype.card_pos]
    · rw [Fa.hcard]; linarith [Fa.hf1, pr_nonneg SS]
  refine assemble S G hG (Φ x) hx' (2 * tgt SS) (by linarith) (fun s hs => ?_) (pref b₁)
    (by rw [mem_SD, toD_symm_ref] at hb₁; exact hb₁)
  have h1 : toD s ∈ SS := by rw [hSS, mem_SD]; simpa using hs
  have h2 : toD s⁻¹ ∈ SS := by rw [hSS, mem_SD]; simpa using hinv s hs
  show x (toD s) + x (toD s⁻¹) = 2 * tgt SS
  simp only [hxdef, if_pos h1, if_pos h2]
  ring

end Main

/-- **Theorem 8, #339 form**: every connected graph with a labelling by some `Γ(A, k, z)`
satisfying the hypotheses (`k • k • a = a`, `k • z = z`, (O)) satisfies the #339 conclusion. -/
theorem main_pow_cayley :
    ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V),
      G.Connected →
      (∃ (A : Type) (_ : AddCommGroup A) (_ : Fintype A) (_ : DecidableEq A) (k : ℤ) (z : A),
        (∀ a : A, k • k • a = a) ∧ k • z = z ∧
        (∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ ∀ a : A, Odd (addOrderOf a) → k • a = ε • a) ∧
        ∃ (e : V ≃ Pw A k z) (S : Finset (Pw A k z)), ∀ u v, G.Adj u v ↔ (e u)⁻¹ * e v ∈ S) →
      2 ≤ Fintype.card V →
      ∃ (r k : ℕ), 0 < r ∧ 0 < k ∧
        ∃ (a b : Fin r → V) (P : ∀ i, G.Walk (a i) (b i)),
          (∀ i, (P i).IsHamiltonian) ∧
          ∀ e ∈ G.edgeSet, (Finset.univ.filter fun i => e ∈ (P i).edges).card = k := by
  intro V _ _ G hc hcay _
  obtain ⟨A, _, _, _, k, z, hk, hz, hO, e, S, hG⟩ := hcay
  haveI : Fact (∀ a : A, k • k • a = a) := ⟨hk⟩
  haveI : Fact (k • z = z) := ⟨hz⟩
  exact transfer G e S hG (fun G' hG' hc' => ft_pow hO S G' hG' hc') hc

/-- the class of `main_pow_cayley` is vertex-transitive -/
lemma isVertexTransitive_of_pow_labelling {V : Type} (G : SimpleGraph V) (A : Type)
    [AddCommGroup A] (k : ℤ) (z : A) (hk : ∀ a : A, k • k • a = a) (hz : k • z = z)
    (e : V ≃ Pw A k z) (S : Set (Pw A k z)) (hG : ∀ u v, G.Adj u v ↔ (e u)⁻¹ * e v ∈ S) :
    IsVertexTransitive G := by
  haveI : Fact (∀ a : A, k • k • a = a) := ⟨hk⟩
  haveI : Fact (k • z = z) := ⟨hz⟩
  exact isVertexTransitive_of_group_labelling G (Pw A k z) e S hG

end FTDih

#print axioms FTDih.main_pow_cayley
#print axioms FTDih.isVertexTransitive_of_pow_labelling

-- ===== FTPowerExtra.lean =====

/-!
# Corollaries of Theorem 8: the semidihedral and modular models

For `n ≥ 1`, `SD_{2^(n+3)} = Γ(Z_{2^(n+2)}, 2^(n+1) - 1, 0)` and `M_{2^(n+3)} = Γ(Z_{2^(n+2)}, 2^(n+1) + 1, 0)`
(for `n = 0` these models are `C₄ × C₂` and `D₈`)
(ρ = `prot 1`, τ = `pref 0`: `ρ^(2^(n+2)) = 1`, `τ² = 1`, `τρτ⁻¹ = ρ^k`). (O) is automatic for
2-groups (`O_of_two_group`). E.g. `n = 1`: SD₁₆ (k = 3) and M₁₆ (k = 5).
-/

namespace FTDih

instance neZero_two_pow (n : ℕ) : NeZero (2 ^ (n + 2)) := ⟨by positivity⟩

/-- `k` for the semidihedral group of order `2^(n+3)` (`n ≥ 1`) -/
def kSD (n : ℕ) : ℤ := 2 ^ (n + 1) - 1
/-- `k` for the modular group of order `2^(n+3)` (`n ≥ 1`) -/
def kM (n : ℕ) : ℤ := 2 ^ (n + 1) + 1

lemma kk_zmod (n : ℕ) (k : ℤ) (hk : ∃ c : ℤ, k * k = 1 + ((2 ^ (n + 2) : ℕ) : ℤ) * c)
    (a : ZMod (2 ^ (n + 2))) : k • k • a = a := by
  obtain ⟨c, hc⟩ := hk
  rw [smul_smul, zsmul_eq_mul, hc]
  simp only [Int.cast_add, Int.cast_one, Int.cast_mul, Int.cast_natCast, ZMod.natCast_self,
    zero_mul, add_zero, one_mul]

lemma kk_SD (n : ℕ) (a : ZMod (2 ^ (n + 2))) : kSD n • kSD n • a = a :=
  kk_zmod n _ ⟨2 ^ n - 1, by rw [kSD]; push_cast; ring⟩ a

lemma kk_M (n : ℕ) (a : ZMod (2 ^ (n + 2))) : kM n • kM n • a = a :=
  kk_zmod n _ ⟨2 ^ n + 1, by rw [kM]; push_cast; ring⟩ a

/-- the defining relations `ρ^(2^(n+2)) = 1`, `τ² = 1`, `τ ρ τ⁻¹ = ρ^k` hold in `Γ(Z_{2^(n+2)}, k, 0)` -/
lemma pw_relations (n : ℕ) (k : ℤ) [Fact (∀ a : ZMod (2 ^ (n + 2)), k • k • a = a)]
    [Fact (k • (0 : ZMod (2 ^ (n + 2))) = 0)] :
    (prot 1 : Pw (ZMod (2 ^ (n + 2))) k 0) ^ (2 ^ (n + 2)) = 1 ∧
    (pref 0 : Pw (ZMod (2 ^ (n + 2))) k 0) ^ 2 = 1 ∧
    (pref 0 : Pw (ZMod (2 ^ (n + 2))) k 0) * prot 1 * (pref 0)⁻¹ = prot (k • 1) := by
  refine ⟨?_, ?_, pref_conj 0 1⟩
  · rw [prot_pow]
    have : ((2 ^ (n + 2) : ℕ) • (1 : ZMod (2 ^ (n + 2)))) = 0 := by
      rw [nsmul_eq_mul, mul_one, ZMod.natCast_self]
    rw [this]; rfl
  · rw [sq, pref_mul_pref]; simp; rfl

/-- **Fair Traversal for every connected Cayley graph of the model `Γ(Z_{2^(n+2)}, 2^(n+1) - 1, 0)`**, the semidihedral
group of order `2^(n+3)` for `n ≥ 1` (`C₄ × C₂` for `n = 0`); stated for all `n`. Order
`2^(n+3)`** (`n = 1`: SD₁₆). -/
theorem main_semidihedral_cayley (n : ℕ) :
    ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V),
      G.Connected →
      (∃ (e : V ≃ Pw (ZMod (2 ^ (n + 2))) (kSD n) 0) (S : Finset (Pw (ZMod (2 ^ (n + 2))) (kSD n) 0)),
        ∀ u v, G.Adj u v ↔ (e u)⁻¹ * e v ∈ S) →
      2 ≤ Fintype.card V →
      ∃ (r k : ℕ), 0 < r ∧ 0 < k ∧
        ∃ (a b : Fin r → V) (P : ∀ i, G.Walk (a i) (b i)),
          (∀ i, (P i).IsHamiltonian) ∧
          ∀ e ∈ G.edgeSet, (Finset.univ.filter fun i => e ∈ (P i).edges).card = k := by
  intro V _ _ G hc hcay hn
  obtain ⟨e, S, hG⟩ := hcay
  exact main_pow_cayley G hc ⟨ZMod (2 ^ (n + 2)), inferInstance, inferInstance, inferInstance,
    kSD n, 0, kk_SD n, smul_zero _, O_of_two_group (n + 2) (ZMod.card _), e, S, hG⟩ hn

/-- **Fair Traversal for every connected Cayley graph of the model `Γ(Z_{2^(n+2)}, 2^(n+1) + 1, 0)`**, the modular
group of order `2^(n+3)` for `n ≥ 1` (`D₈` for `n = 0`); stated for all `n`.
(`n = 1`: M₁₆). -/
theorem main_modular_cayley (n : ℕ) :
    ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V),
      G.Connected →
      (∃ (e : V ≃ Pw (ZMod (2 ^ (n + 2))) (kM n) 0) (S : Finset (Pw (ZMod (2 ^ (n + 2))) (kM n) 0)),
        ∀ u v, G.Adj u v ↔ (e u)⁻¹ * e v ∈ S) →
      2 ≤ Fintype.card V →
      ∃ (r k : ℕ), 0 < r ∧ 0 < k ∧
        ∃ (a b : Fin r → V) (P : ∀ i, G.Walk (a i) (b i)),
          (∀ i, (P i).IsHamiltonian) ∧
          ∀ e ∈ G.edgeSet, (Finset.univ.filter fun i => e ∈ (P i).edges).card = k := by
  intro V _ _ G hc hcay hn
  obtain ⟨e, S, hG⟩ := hcay
  exact main_pow_cayley G hc ⟨ZMod (2 ^ (n + 2)), inferInstance, inferInstance, inferInstance,
    kM n, 0, kk_M n, smul_zero _, O_of_two_group (n + 2) (ZMod.card _), e, S, hG⟩ hn

end FTDih

#print axioms FTDih.main_semidihedral_cayley
#print axioms FTDih.main_modular_cayley
#print axioms FTDih.pw_relations
