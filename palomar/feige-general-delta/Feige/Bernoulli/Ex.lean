module

public import Mathlib

/- Port (Palomar entry): `module` header, `public import`s and a public section added for the module system; otherwise unchanged from github.com/koolkao/feige-lean at commit 7da24abf1619706bf4f705bb24aa4d00bc63b49f. -/

@[expose] public section

/-!
# Finite Bernoulli product expectations

For a finite index set `s` and success probabilities `p`, a subset `S ⊆ s` (the set of
coordinates with `Bᵢ = 1`) has product weight `wt p s S`, and `Ex p s F` is the expectation of
`F : Finset ι → ℝ`.  Everything in Ling's §3 is a finite sum of this form, so no measure
theory is needed for Theorem 2.1.
-/

open Finset

namespace Samuels

variable {ι : Type*} [DecidableEq ι]

/-- Product weight of the high set `S ⊆ s`. -/
noncomputable def wt (p : ι → ℝ) (s S : Finset ι) : ℝ :=
  (∏ i ∈ S, p i) * ∏ i ∈ s \ S, (1 - p i)

/-- Expectation of `F` under independent `Bernoulli (p i)`, `i ∈ s`. -/
noncomputable def Ex (p : ι → ℝ) (s : Finset ι) (F : Finset ι → ℝ) : ℝ :=
  ∑ S ∈ s.powerset, wt p s S * F S

variable {p : ι → ℝ}

@[simp] lemma Ex_empty (F : Finset ι → ℝ) : Ex p ∅ F = F ∅ := by
  simp [Ex, wt]

lemma wt_insert_of_subset {i : ι} {s S : Finset ι} (hi : i ∉ s) (hS : S ⊆ s) :
    wt p (insert i s) S = (1 - p i) * wt p s S := by
  unfold wt
  have hiS : i ∉ S := fun h => hi (hS h)
  rw [Finset.insert_sdiff_of_notMem _ hiS, Finset.prod_insert (by simp [hi])]
  ring

lemma wt_insert_insert {i : ι} {s S : Finset ι} (hi : i ∉ s) (hS : S ⊆ s) :
    wt p (insert i s) (insert i S) = p i * wt p s S := by
  unfold wt
  have hiS : i ∉ S := fun h => hi (hS h)
  have hsd : insert i s \ insert i S = s \ S := by
    ext j
    simp only [mem_sdiff, mem_insert]
    constructor
    · rintro ⟨h1 | h1, h2⟩
      · exact absurd (Or.inl h1) h2
      · exact ⟨h1, fun h => h2 (Or.inr h)⟩
    · rintro ⟨h1, h2⟩
      refine ⟨Or.inr h1, ?_⟩
      rintro (h | h)
      · exact hi (h ▸ h1)
      · exact h2 h
  rw [hsd, Finset.prod_insert hiS]
  ring

/-- Conditioning on the coordinate `i`. -/
lemma Ex_insert {i : ι} {s : Finset ι} (hi : i ∉ s) (F : Finset ι → ℝ) :
    Ex p (insert i s) F = (1 - p i) * Ex p s F + p i * Ex p s (fun S => F (insert i S)) := by
  unfold Ex
  rw [Finset.sum_powerset_insert hi, Finset.mul_sum, Finset.mul_sum]
  congr 1
  · apply Finset.sum_congr rfl
    intro S hS
    rw [wt_insert_of_subset hi (mem_powerset.mp hS)]
    ring
  · apply Finset.sum_congr rfl
    intro S hS
    rw [wt_insert_insert hi (mem_powerset.mp hS)]
    ring

lemma Ex_congr {s : Finset ι} {F G : Finset ι → ℝ} (h : ∀ S ⊆ s, F S = G S) :
    Ex p s F = Ex p s G := by
  unfold Ex
  apply Finset.sum_congr rfl
  intro S hS
  rw [h S (mem_powerset.mp hS)]

lemma Ex_add (s : Finset ι) (F G : Finset ι → ℝ) :
    Ex p s (fun S => F S + G S) = Ex p s F + Ex p s G := by
  simp [Ex, mul_add, Finset.sum_add_distrib]

lemma Ex_sub (s : Finset ι) (F G : Finset ι → ℝ) :
    Ex p s (fun S => F S - G S) = Ex p s F - Ex p s G := by
  simp [Ex, mul_sub, Finset.sum_sub_distrib]

lemma Ex_mul_left (s : Finset ι) (c : ℝ) (F : Finset ι → ℝ) :
    Ex p s (fun S => c * F S) = c * Ex p s F := by
  simp only [Ex, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro S _
  ring

lemma Ex_zero (s : Finset ι) : Ex p s (fun _ => 0) = 0 := by
  simp [Ex]

lemma Ex_finsum {κ : Type*} (s : Finset ι) (t : Finset κ) (F : κ → Finset ι → ℝ) :
    Ex p s (fun S => ∑ j ∈ t, F j S) = ∑ j ∈ t, Ex p s (F j) := by
  simp only [Ex, Finset.mul_sum]
  rw [Finset.sum_comm]

lemma wt_nonneg {s S : Finset ι} (hp0 : ∀ i ∈ s, 0 ≤ p i) (hp1 : ∀ i ∈ s, p i ≤ 1)
    (hS : S ⊆ s) : 0 ≤ wt p s S := by
  unfold wt
  apply mul_nonneg
  · exact Finset.prod_nonneg fun i hi => hp0 i (hS hi)
  · exact Finset.prod_nonneg fun i hi => sub_nonneg.mpr (hp1 i (mem_sdiff.mp hi).1)

lemma Ex_mono {s : Finset ι} (hp0 : ∀ i ∈ s, 0 ≤ p i) (hp1 : ∀ i ∈ s, p i ≤ 1)
    {F G : Finset ι → ℝ} (h : ∀ S ⊆ s, F S ≤ G S) : Ex p s F ≤ Ex p s G := by
  unfold Ex
  apply Finset.sum_le_sum
  intro S hS
  exact mul_le_mul_of_nonneg_left (h S (mem_powerset.mp hS))
    (wt_nonneg hp0 hp1 (mem_powerset.mp hS))

lemma Ex_nonneg {s : Finset ι} (hp0 : ∀ i ∈ s, 0 ≤ p i) (hp1 : ∀ i ∈ s, p i ≤ 1)
    {F : Finset ι → ℝ} (h : ∀ S ⊆ s, 0 ≤ F S) : 0 ≤ Ex p s F := by
  have := Ex_mono hp0 hp1 (F := fun _ => 0) h
  rwa [Ex_zero] at this

lemma Ex_const (s : Finset ι) (c : ℝ) : Ex p s (fun _ => c) = c := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Ex_insert hi]
    simp only [ih]
    ring

/-- The mean of `T = ∑_{i ∈ S} wᵢ`. -/
lemma Ex_sum_mem (s : Finset ι) (w : ι → ℝ) :
    Ex p s (fun S => ∑ i ∈ S, w i) = ∑ i ∈ s, w i * p i := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Ex_insert hi, Finset.sum_insert hi, ih]
    have : Ex p s (fun S => ∑ j ∈ insert i S, w j) = Ex p s (fun S => w i + ∑ j ∈ S, w j) := by
      apply Ex_congr
      intro S hS
      rw [Finset.sum_insert (fun h => hi (hS h))]
    rw [this, Ex_add, Ex_const, ih]
    ring

end Samuels

end
