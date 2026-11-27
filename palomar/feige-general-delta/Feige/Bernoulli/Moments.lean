module

public import Feige.Bernoulli.ZM

/- Port (Palomar entry): `module` header, `public import`s and a public section added for the module system; otherwise unchanged from github.com/koolkao/feige-lean at commit 7da24abf1619706bf4f705bb24aa4d00bc63b49f. -/

@[expose] public section

/-!
# Moments restricted to `Bᵢ = 1`

`E[Bᵢ 1{T<c}] = pᵢ P(T₋ᵢ < c - wᵢ)` and `E[Bᵢ T 1{T<c}] = pᵢ (E[T₋ᵢ 1{T₋ᵢ<c-wᵢ}] + wᵢ P(T₋ᵢ<c-wᵢ))`,
and the decompositions `T 1{T<c} = ∑ᵢ wᵢ Bᵢ 1{T<c}`, `T² 1{T<c} = ∑ᵢ wᵢ Bᵢ T 1{T<c}`.
-/

open Finset

namespace Samuels

variable {ι : Type*} [DecidableEq ι] {p w : ι → ℝ}

/-- `E[Bᵢ 1{T<c}]` on `insert i s`. -/
lemma Ex_mem_ind {i : ι} {s : Finset ι} (hi : i ∉ s) (c : ℝ) :
    Ex p (insert i s) (fun S => if i ∈ S then (if T w S < c then 1 else 0) else 0) =
      p i * Z p w s (c - w i) := by
  rw [Ex_insert hi]
  have h1 : Ex p s (fun S => if i ∈ S then (if T w S < c then (1 : ℝ) else 0) else 0) = 0 := by
    refine (Ex_congr (G := fun _ => 0) fun S hS => ?_).trans (Ex_zero s)
    rw [if_neg (fun h => hi (hS h))]
  rw [h1, mul_zero, zero_add]
  congr 1
  unfold Z
  apply Ex_congr
  intro S hS
  rw [if_pos (mem_insert_self i S), T_insert (fun h => hi (hS h))]
  by_cases h : T w S < c - w i
  · rw [if_pos (by linarith), if_pos h]
  · rw [if_neg (by linarith), if_neg h]

/-- `E[Bᵢ T 1{T<c}]` on `insert i s`. -/
lemma Ex_mem_T {i : ι} {s : Finset ι} (hi : i ∉ s) (c : ℝ) :
    Ex p (insert i s) (fun S => if i ∈ S then (if T w S < c then T w S else 0) else 0) =
      p i * (M p w s (c - w i) + w i * Z p w s (c - w i)) := by
  rw [Ex_insert hi]
  have h1 : Ex p s (fun S => if i ∈ S then (if T w S < c then T w S else 0) else 0) = 0 := by
    refine (Ex_congr (G := fun _ => 0) fun S hS => ?_).trans (Ex_zero s)
    rw [if_neg (fun h => hi (hS h))]
  rw [h1, mul_zero, zero_add]
  congr 1
  unfold M Z
  rw [← Ex_mul_left, ← Ex_add]
  apply Ex_congr
  intro S hS
  rw [if_pos (mem_insert_self i S), T_insert (fun h => hi (hS h))]
  by_cases h : T w S < c - w i
  · rw [if_pos (by linarith), if_pos h, if_pos h]; ring
  · rw [if_neg (by linarith), if_neg h, if_neg h]; ring

lemma sum_mem_ite {s S : Finset ι} (hS : S ⊆ s) (f : ι → ℝ) :
    ∑ i ∈ s, (if i ∈ S then f i else 0) = ∑ i ∈ S, f i := by
  rw [Finset.sum_ite_mem, Finset.inter_eq_right.mpr hS]

/-- `M = ∑ᵢ wᵢ E[Bᵢ 1{T<c}]`. -/
lemma M_eq_sum (s : Finset ι) (c : ℝ) :
    M p w s c = ∑ i ∈ s, w i *
      Ex p s (fun S => if i ∈ S then (if T w S < c then 1 else 0) else 0) := by
  simp_rw [← Ex_mul_left]
  rw [← Ex_finsum]
  unfold M
  apply Ex_congr
  intro S hS
  have : ∑ i ∈ s, w i * (if i ∈ S then (if T w S < c then (1 : ℝ) else 0) else 0) =
      ∑ i ∈ s, (if i ∈ S then w i * (if T w S < c then 1 else 0) else 0) := by
    apply Finset.sum_congr rfl; intro i _; split_ifs <;> simp
  rw [this, sum_mem_ite hS, ← Finset.sum_mul]
  unfold T
  split_ifs <;> simp

/-- `Q = ∑ᵢ wᵢ E[Bᵢ T 1{T<c}]`. -/
lemma Q_eq_sum (s : Finset ι) (c : ℝ) :
    Q p w s c = ∑ i ∈ s, w i *
      Ex p s (fun S => if i ∈ S then (if T w S < c then T w S else 0) else 0) := by
  simp_rw [← Ex_mul_left]
  rw [← Ex_finsum]
  unfold Q
  apply Ex_congr
  intro S hS
  have : ∑ i ∈ s, w i * (if i ∈ S then (if T w S < c then T w S else 0) else 0) =
      ∑ i ∈ s, (if i ∈ S then w i * (if T w S < c then T w S else 0) else 0) := by
    apply Finset.sum_congr rfl; intro i _; split_ifs <;> simp
  rw [this, sum_mem_ite hS, ← Finset.sum_mul]
  change _ = T w S * _
  split_ifs <;> ring

end Samuels

end
