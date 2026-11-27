module

public import Feige.Bernoulli.Ex

/- Port (Palomar entry): `module` header, `public import`s and a public section added for the module system; otherwise unchanged from github.com/koolkao/feige-lean at commit 7da24abf1619706bf4f705bb24aa4d00bc63b49f. -/

@[expose] public section

/-!
# Truncated moments of a weighted Bernoulli sum

`T S = ∑_{i ∈ S} wᵢ`. For a threshold `c`,
* `Z s c = P(T < c)`,
* `M s c = E[T · 1{T < c}]`,
* `Q s c = E[T² · 1{T < c}]`,
and their recursions when one coordinate is added.
-/

open Finset

namespace Samuels

variable {ι : Type*} [DecidableEq ι] (p w : ι → ℝ)

/-- The weighted sum `T(S) = ∑_{i ∈ S} wᵢ`. -/
def T (S : Finset ι) : ℝ := ∑ i ∈ S, w i

/-- `P(T < c)`. -/
noncomputable def Z (s : Finset ι) (c : ℝ) : ℝ :=
  Ex p s (fun S => if T w S < c then 1 else 0)

/-- `E[T 1{T < c}]`. -/
noncomputable def M (s : Finset ι) (c : ℝ) : ℝ :=
  Ex p s (fun S => if T w S < c then T w S else 0)

/-- `E[T² 1{T < c}]`. -/
noncomputable def Q (s : Finset ι) (c : ℝ) : ℝ :=
  Ex p s (fun S => if T w S < c then T w S ^ 2 else 0)

/-- `E[T] = ∑ wᵢ pᵢ`. -/
def E (s : Finset ι) : ℝ := ∑ i ∈ s, w i * p i

variable {p w}

lemma T_insert {i : ι} {S : Finset ι} (hi : i ∉ S) : T w (insert i S) = w i + T w S := by
  simp [T, Finset.sum_insert hi]

lemma Z_insert {i : ι} {s : Finset ι} (hi : i ∉ s) (c : ℝ) :
    Z p w (insert i s) c = (1 - p i) * Z p w s c + p i * Z p w s (c - w i) := by
  unfold Z
  rw [Ex_insert hi]
  congr 2
  apply Ex_congr
  intro S hS
  rw [T_insert (fun h => hi (hS h))]
  by_cases h : T w S < c - w i
  · rw [if_pos (by linarith), if_pos h]
  · rw [if_neg (by linarith), if_neg h]

lemma M_insert {i : ι} {s : Finset ι} (hi : i ∉ s) (c : ℝ) :
    M p w (insert i s) c =
      (1 - p i) * M p w s c + p i * (M p w s (c - w i) + w i * Z p w s (c - w i)) := by
  unfold M Z
  rw [Ex_insert hi]
  congr 2
  rw [← Ex_mul_left, ← Ex_add]
  apply Ex_congr
  intro S hS
  rw [T_insert (fun h => hi (hS h))]
  by_cases h : T w S < c - w i
  · rw [if_pos (by linarith), if_pos h, if_pos h]; ring
  · rw [if_neg (by linarith), if_neg h, if_neg h]; ring

lemma Z_nonneg {s : Finset ι} (hp0 : ∀ i ∈ s, 0 ≤ p i) (hp1 : ∀ i ∈ s, p i ≤ 1) (c : ℝ) :
    0 ≤ Z p w s c := by
  apply Ex_nonneg hp0 hp1
  intro S _
  split_ifs <;> norm_num

lemma Z_pos {s : Finset ι} (hp0 : ∀ i ∈ s, 0 ≤ p i) (hp1 : ∀ i ∈ s, p i < 1)
    (hw : ∀ i ∈ s, 0 ≤ w i) {c : ℝ} (hc : 0 < c) : 0 < Z p w s c := by
  induction s using Finset.induction_on with
  | empty => simp [Z, T, hc]
  | insert i s hi ih =>
    rw [Z_insert hi]
    have h1 := ih (fun j hj => hp0 j (mem_insert_of_mem hj)) (fun j hj => hp1 j (mem_insert_of_mem hj))
      (fun j hj => hw j (mem_insert_of_mem hj))
    have h2 := Z_nonneg (w := w) (fun j hj => hp0 j (mem_insert_of_mem hj))
      (fun j hj => (hp1 j (mem_insert_of_mem hj)).le) (c - w i)
    have h3 : 0 < 1 - p i := sub_pos.mpr (hp1 i (mem_insert_self i s))
    have h4 := hp0 i (mem_insert_self i s)
    nlinarith

lemma Z_le_one {s : Finset ι} (hp0 : ∀ i ∈ s, 0 ≤ p i) (hp1 : ∀ i ∈ s, p i ≤ 1) (c : ℝ) :
    Z p w s c ≤ 1 := by
  have := Ex_mono (F := fun S => if T w S < c then (1 : ℝ) else 0) (G := fun _ => 1) hp0 hp1
    (fun S _ => by split_ifs <;> norm_num)
  rwa [Ex_const] at this

lemma Z_mono {s : Finset ι} (hp0 : ∀ i ∈ s, 0 ≤ p i) (hp1 : ∀ i ∈ s, p i ≤ 1) {c' c : ℝ}
    (hc : c' ≤ c) : Z p w s c' ≤ Z p w s c := by
  apply Ex_mono hp0 hp1
  intro S _
  by_cases h : T w S < c'
  · rw [if_pos h, if_pos (lt_of_lt_of_le h hc)]
  · rw [if_neg h]; split_ifs <;> norm_num

/-- On `{c' ≤ T < c}` we have `T ≥ c'`, so `E[T 1{c' ≤ T < c}] ≥ c' P(c' ≤ T < c)`. -/
lemma M_sub_ge {s : Finset ι} (hp0 : ∀ i ∈ s, 0 ≤ p i) (hp1 : ∀ i ∈ s, p i ≤ 1) {c' c : ℝ}
    (hc : c' ≤ c) : c' * (Z p w s c - Z p w s c') ≤ M p w s c - M p w s c' := by
  unfold M Z
  rw [← Ex_sub, ← Ex_sub, ← Ex_mul_left]
  apply Ex_mono hp0 hp1
  intro S _
  rcases lt_or_ge (T w S) c' with h | h
  · have h' : T w S < c := lt_of_lt_of_le h hc
    simp [h, h']
  · rcases lt_or_ge (T w S) c with h' | h'
    · simp [h', not_lt.mpr h]; nlinarith
    · simp [not_lt.mpr h, not_lt.mpr h']

/-- Claim 3.1, last part: `E[T] ≥ M + (1 - Z)`, i.e. `Z - M ≥ 1 - E[T]`. -/
lemma one_sub_E_le {s : Finset ι} (hp0 : ∀ i ∈ s, 0 ≤ p i) (hp1 : ∀ i ∈ s, p i ≤ 1) :
    1 - E p w s ≤ Z p w s 1 - M p w s 1 := by
  have hE : E p w s = Ex p s (fun S => T w S) := by
    rw [E]; exact (Ex_sum_mem s w).symm
  have : Ex p s (fun S => (if T w S < 1 then T w S else 0) + (1 - (if T w S < 1 then 1 else 0)))
      ≤ Ex p s (fun S => T w S) := by
    apply Ex_mono hp0 hp1
    intro S _
    split_ifs with h
    · simp
    · push Not at h; linarith
  rw [Ex_add, Ex_sub, Ex_const] at this
  unfold M Z
  rw [hE]
  linarith

/-- Cauchy–Schwarz: `M² ≤ Z Q`. -/
lemma M_sq_le {s : Finset ι} (hp0 : ∀ i ∈ s, 0 ≤ p i) (hp1 : ∀ i ∈ s, p i ≤ 1) (c : ℝ)
    (hZ : 0 < Z p w s c) : M p w s c ^ 2 / Z p w s c ≤ Q p w s c := by
  set m := M p w s c / Z p w s c
  have h0 : 0 ≤ Ex p s (fun S => if T w S < c then (T w S - m) ^ 2 else 0) := by
    apply Ex_nonneg hp0 hp1
    intro S _
    split_ifs <;> positivity
  have hexp : Ex p s (fun S => if T w S < c then (T w S - m) ^ 2 else 0) =
      Q p w s c - 2 * m * M p w s c + m ^ 2 * Z p w s c := by
    unfold Q M Z
    rw [← Ex_mul_left, ← Ex_mul_left, ← Ex_sub, ← Ex_add]
    apply Ex_congr
    intro S _
    split_ifs <;> ring
  rw [hexp] at h0
  have : m * Z p w s c = M p w s c := by
    simp only [m]; field_simp
  rw [div_le_iff₀ hZ]
  have : M p w s c ^ 2 = m ^ 2 * Z p w s c ^ 2 := by
    rw [← this]; ring
  nlinarith

end Samuels

end
