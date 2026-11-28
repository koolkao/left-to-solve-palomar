/-
Copyright 2026 Ming-Chih Kao. Licensed under the Apache License, Version 2.0;
see the LICENSE file at the root of this repository.
-/
module

public import Mathlib

/-! Port: copied from `MO451543.lean` of github.com/koolkao/mo451543-jensen-slack (commit
8be6d3435985e8b331e45e9e666a0c61c8cbf172, v1.1.0, Lean v4.36.0, same Mathlib) and put into the module system:
the `module` header, `public import Mathlib`, a public section, and the namespace `MO451543` renamed
`JensenSlack` so that `Solution.lean` can state the compared theorems under their original names
`MO451543.*`. The mathematics and the proofs are
unchanged. -/

@[expose] public section

/-!
# MathOverflow 451543: comparing the two Jensen slacks

For a finitely supported coupling `(X, Y)` with `E[Y | X] = X` and `μ(Y) = E[X | Y]`, the question asks for
which convex `f` one has `E[f X - f (μ Y)] ≤ E[f Y - f X]`.  The asker conjectures `f''` convex suffices.

* `not_comparison_pow_four`: the inequality FAILS for `f x = x ^ 4` (convex, `f'' = 12 x²` convex;
  see `pow_four_in_class`).
* `comparison_iff`: for differentiable `f`, the inequality holds for all finite couplings iff
  `f x = α x² + β x + γ` with `α ≥ 0`. `comparison_iff_of_continuous` and `comparison_iff_of_convex`
  extend this to continuous and to convex `f`.
* `indepComparison_iff_of_continuous`, `indepComparison_iff_of_convex`: the same characterisation for
  the smaller class of couplings `Y = X + Z` with `Z` independent of `X` and `E Z = 0`.

A coupling is given by `n` atoms `(x i, y i)` with weights `w i ≥ 0`, `∑ w = 1` (atoms may repeat).
-/

open Finset

noncomputable section

namespace JensenSlack

variable {ι : Type*} [Fintype ι]

/-- `E[X | Y = y₀]` for the finite coupling `(x, y, w)`. -/
def mu (x y w : ι → ℝ) (y₀ : ℝ) : ℝ :=
  (∑ i ∈ univ.filter (fun i => y i = y₀), w i * x i) / (∑ i ∈ univ.filter (fun i => y i = y₀), w i)

/-- `w` is a probability vector. -/
def IsLaw (w : ι → ℝ) : Prop := (∀ i, 0 ≤ w i) ∧ ∑ i, w i = 1

/-- `E[Y | X] = X`: on every fibre `{X = x₀}`, `∑ w y = x₀ ∑ w`. -/
def IsMart (x y w : ι → ℝ) : Prop :=
  ∀ x₀ : ℝ, ∑ i ∈ univ.filter (fun i => x i = x₀), w i * y i =
    x₀ * ∑ i ∈ univ.filter (fun i => x i = x₀), w i

/-- `E[f X - f (μ Y)]`. -/
def lhs (f : ℝ → ℝ) (x y w : ι → ℝ) : ℝ := ∑ i, w i * (f (x i) - f (mu x y w (y i)))

/-- `E[f Y - f X]`. -/
def rhs (f : ℝ → ℝ) (x y w : ι → ℝ) : ℝ := ∑ i, w i * (f (y i) - f (x i))

/-- The inequality of MO 451543 holds for every finite coupling. -/
def Comparison (f : ℝ → ℝ) : Prop :=
  ∀ (n : ℕ) (x y w : Fin n → ℝ), IsLaw w → IsMart x y w → lhs f x y w ≤ rhs f x y w

/-! ## The counterexample for `x ^ 4` -/

/-- The three-atom coupling `(0,-1/2)` w.p. `1/3`, `(0,1)` w.p. `1/6`, `(1,1)` w.p. `1/2`. -/
def cx : Fin 3 → ℝ := ![0, 0, 1]
def cy : Fin 3 → ℝ := ![-1/2, 1, 1]
def cw : Fin 3 → ℝ := ![1/3, 1/6, 1/2]

lemma sum_filter_three (p : Fin 3 → Prop) [DecidablePred p] (g : Fin 3 → ℝ) :
    ∑ i ∈ univ.filter p, g i =
      (if p 0 then g 0 else 0) + (if p 1 then g 1 else 0) + (if p 2 then g 2 else 0) := by
  rw [Finset.sum_filter, Fin.sum_univ_three]

lemma cw_law : IsLaw cw := by
  refine ⟨fun i => ?_, ?_⟩
  · fin_cases i <;> simp [cw]
  · simp [cw, Fin.sum_univ_three]; norm_num

lemma c_mart : IsMart cx cy cw := by
  intro x₀
  rw [sum_filter_three, sum_filter_three]
  simp only [cx, cy, cw, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  by_cases h0 : (0 : ℝ) = x₀ <;> by_cases h1 : (1 : ℝ) = x₀
  · subst h0; norm_num at h1
  · subst h0; simp only [ite_true, h1, ite_false]; norm_num
  · subst h1; simp only [h0, ite_true, ite_false]; norm_num
  · simp only [h0, h1, ite_false]; norm_num

lemma c_mu_neg : mu cx cy cw (-1/2) = 0 := by
  rw [mu, sum_filter_three, sum_filter_three]
  simp only [cx, cy, cw, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  norm_num

lemma c_mu_one : mu cx cy cw 1 = 3/4 := by
  rw [mu, sum_filter_three, sum_filter_three]
  simp only [cx, cy, cw, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  norm_num

theorem lhs_c : lhs (fun t => t ^ 4) cx cy cw = 37/128 := by
  have h0 : mu cx cy cw (cy 0) = 0 := by simpa [cy] using c_mu_neg
  have h1 : mu cx cy cw (cy 1) = 3/4 := by simpa [cy] using c_mu_one
  have h2 : mu cx cy cw (cy 2) = 3/4 := by simpa [cy] using c_mu_one
  simp only [lhs, Fin.sum_univ_three, h0, h1, h2]
  simp [cx, cw]; norm_num

theorem rhs_c : rhs (fun t => t ^ 4) cx cy cw = 3/16 := by
  simp only [rhs, Fin.sum_univ_three]
  simp [cx, cy, cw]; norm_num

/-- **MO 451543 is false**: `f x = x ^ 4` violates the inequality. -/
theorem not_comparison_pow_four : ¬ Comparison (fun t => t ^ 4) := by
  intro h
  have := h 3 cx cy cw cw_law c_mart
  rw [lhs_c, rhs_c] at this
  norm_num at this

/-- `x ^ 4` is convex and so is its second derivative `12 x ^ 2`: it lies in the asker's class. -/
theorem pow_four_in_class :
    ConvexOn ℝ Set.univ (fun t : ℝ => t ^ 4) ∧ ConvexOn ℝ Set.univ (fun t : ℝ => 12 * t ^ 2) ∧
    deriv (deriv (fun t : ℝ => t ^ 4)) = fun t => 12 * t ^ 2 := by
  refine ⟨(Even.convexOn_pow (by decide)), ?_, ?_⟩
  · exact (Even.convexOn_pow (n := 2) (by decide)).smul (by norm_num : (0:ℝ) ≤ 12)
  · have h1 : deriv (fun t : ℝ => t ^ 4) = fun t => 4 * t ^ 3 := by
      funext t; simp
    rw [h1]; funext t; simp; ring

/-! ## Fibre identities -/

/-- `E[g(Y) μ(Y)] = E[g(Y) X]`. -/
lemma sum_mul_mu (x y w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (g : ℝ → ℝ) :
    ∑ i, w i * g (y i) * mu x y w (y i) = ∑ i, w i * g (y i) * x i := by
  have hmap : ∀ i ∈ (univ : Finset ι), y i ∈ univ.image y :=
    fun i _ => mem_image_of_mem y (mem_univ i)
  rw [← Finset.sum_fiberwise_of_maps_to hmap, ← Finset.sum_fiberwise_of_maps_to hmap]
  refine Finset.sum_congr rfl (fun y₀ _ => ?_)
  have e1 : ∑ i ∈ univ.filter (fun i => y i = y₀), w i * g (y i) * mu x y w (y i) =
      g y₀ * mu x y w y₀ * ∑ i ∈ univ.filter (fun i => y i = y₀), w i := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i hi => ?_)
    rw [(Finset.mem_filter.1 hi).2]; ring
  have e2 : ∑ i ∈ univ.filter (fun i => y i = y₀), w i * g (y i) * x i =
      g y₀ * ∑ i ∈ univ.filter (fun i => y i = y₀), w i * x i := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i hi => ?_)
    rw [(Finset.mem_filter.1 hi).2]; ring
  rw [e1, e2]
  by_cases hS : ∑ i ∈ univ.filter (fun i => y i = y₀), w i = 0
  · have hz : ∀ i ∈ univ.filter (fun i => y i = y₀), w i = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hw i)).1 hS
    have hT : ∑ i ∈ univ.filter (fun i => y i = y₀), w i * x i = 0 :=
      Finset.sum_eq_zero (fun i hi => by rw [hz i hi, zero_mul])
    rw [hS, hT]; ring
  · rw [mu, mul_assoc, div_mul_cancel₀ _ hS]

/-- `E[g(X) Y] = E[g(X) X]` when `E[Y | X] = X`. -/
lemma sum_mul_y (x y w : ι → ℝ) (hm : IsMart x y w) (g : ℝ → ℝ) :
    ∑ i, w i * g (x i) * y i = ∑ i, w i * g (x i) * x i := by
  have hmap : ∀ i ∈ (univ : Finset ι), x i ∈ univ.image x :=
    fun i _ => mem_image_of_mem x (mem_univ i)
  rw [← Finset.sum_fiberwise_of_maps_to hmap, ← Finset.sum_fiberwise_of_maps_to hmap]
  refine Finset.sum_congr rfl (fun x₀ _ => ?_)
  have e1 : ∑ i ∈ univ.filter (fun i => x i = x₀), w i * g (x i) * y i =
      g x₀ * ∑ i ∈ univ.filter (fun i => x i = x₀), w i * y i := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i hi => ?_)
    rw [(Finset.mem_filter.1 hi).2]; ring
  have e2 : ∑ i ∈ univ.filter (fun i => x i = x₀), w i * g (x i) * x i =
      g x₀ * (x₀ * ∑ i ∈ univ.filter (fun i => x i = x₀), w i) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i hi => ?_)
    rw [(Finset.mem_filter.1 hi).2]; ring
  rw [e1, e2, hm x₀]

/-! ## Sufficiency: convex quadratics -/

/-- For a quadratic `f`, `rhs - lhs = α E[(Y - μ(Y))²]`. -/
theorem rhs_sub_lhs_quadratic (α β γ : ℝ) (x y w : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hm : IsMart x y w) :
    rhs (fun t => α * t ^ 2 + β * t + γ) x y w - lhs (fun t => α * t ^ 2 + β * t + γ) x y w =
      α * ∑ i, w i * (y i - mu x y w (y i)) ^ 2 := by
  set m := fun i => mu x y w (y i) with hmdef
  have hA := sum_mul_mu x y w hw id
  have hB := sum_mul_mu x y w hw (fun _ => 1)
  have hC := sum_mul_y x y w hm id
  have hD := sum_mul_y x y w hm (fun _ => 1)
  simp only [id, mul_one] at hA hB hC hD
  have key : rhs (fun t => α * t ^ 2 + β * t + γ) x y w - lhs (fun t => α * t ^ 2 + β * t + γ) x y w
      - α * ∑ i, w i * (y i - mu x y w (y i)) ^ 2 =
      2 * α * (∑ i, w i * y i * mu x y w (y i) - ∑ i, w i * x i * y i)
      + 2 * α * (∑ i, w i * x i * y i - ∑ i, w i * x i * x i)
      + β * (∑ i, w i * y i - ∑ i, w i * x i) + β * (∑ i, w i * mu x y w (y i) - ∑ i, w i * x i) := by
    simp only [rhs, lhs, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    ring
  have h1 : ∑ i, w i * y i * mu x y w (y i) = ∑ i, w i * x i * y i := by
    rw [hA]; exact Finset.sum_congr rfl (fun i _ => by ring)
  rw [h1, hC, hD, hB] at key
  linarith

theorem comparison_of_quadratic (α β γ : ℝ) (hα : 0 ≤ α) :
    Comparison (fun t => α * t ^ 2 + β * t + γ) := by
  intro n x y w hw hm
  have := rhs_sub_lhs_quadratic α β γ x y w hw.1 hm
  have hnn : 0 ≤ α * ∑ i, w i * (y i - mu x y w (y i)) ^ 2 :=
    mul_nonneg hα (Finset.sum_nonneg (fun i _ => mul_nonneg (hw.1 i) (sq_nonneg _)))
  linarith

/-! ## Necessity: the two-point family -/

/-- The family `C(a, b, ε)`. -/
def fx (a b : ℝ) : Fin 3 → ℝ := ![a, a, b]
def fy (a b ε : ℝ) : Fin 3 → ℝ := ![a - ε * (b - a) / (1 - ε), b, b]
def fw (ε : ℝ) : Fin 3 → ℝ := ![(1 - ε) / 2, ε / 2, 1 / 2]

/-- `Δ(ε) = rhs - lhs` for `C(a, b, ε)`. -/
def phi (f : ℝ → ℝ) (a b ε : ℝ) : ℝ :=
  (1 - ε) / 2 * (f (a - ε * (b - a) / (1 - ε)) - f a) - ε * f a + ε * f b
    + (1 + ε) / 2 * (f (b - ε * (b - a) / (1 + ε)) - f b)

section family
variable {a b ε : ℝ}

lemma fam_law (h0 : 0 < ε) (h1 : ε < 1) : IsLaw (fw ε) := by
  refine ⟨fun i => ?_, ?_⟩
  · fin_cases i <;> simp [fw] <;> linarith
  · simp [fw, Fin.sum_univ_three]; ring

lemma fam_ne (hab : a ≠ b) (h1 : ε < 1) : a - ε * (b - a) / (1 - ε) ≠ b := by
  intro h
  have h1' : (1 - ε) ≠ 0 := by linarith
  have : a - ε * (b - a) / (1 - ε) - b = -(b - a) / (1 - ε) := by field_simp; ring
  rw [h, sub_self] at this
  have hba : b - a ≠ 0 := sub_ne_zero.2 (Ne.symm hab)
  have : -(b - a) / (1 - ε) ≠ 0 := div_ne_zero (neg_ne_zero.2 hba) h1'
  exact this (by linarith)

lemma fam_mart (hab : a ≠ b) (h1 : ε < 1) : IsMart (fx a b) (fy a b ε) (fw ε) := by
  intro x₀
  have h1' : (1 - ε) ≠ 0 := by linarith
  rw [sum_filter_three, sum_filter_three]
  simp only [fx, fy, fw, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  by_cases ha : a = x₀ <;> by_cases hb : b = x₀
  · exact absurd (ha.trans hb.symm) hab
  · subst ha; simp only [ite_true, hb, ite_false]; field_simp; ring
  · subst hb; simp only [ha, ite_true, ite_false]; ring
  · simp only [ha, hb, ite_false]; ring

lemma fam_mu1 (hab : a ≠ b) (_h0 : 0 < ε) (h1 : ε < 1) :
    mu (fx a b) (fy a b ε) (fw ε) (a - ε * (b - a) / (1 - ε)) = a := by
  have hne := fam_ne hab h1
  rw [mu, sum_filter_three, sum_filter_three]
  simp only [fx, fy, fw, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, ite_true, Ne.symm hne, ite_false]
  have : (1 - ε) / 2 ≠ 0 := by linarith
  field_simp
  ring

lemma fam_mu2 (hab : a ≠ b) (h0 : 0 < ε) (h1 : ε < 1) :
    mu (fx a b) (fy a b ε) (fw ε) b = b - ε * (b - a) / (1 + ε) := by
  have hne := fam_ne hab h1
  rw [mu, sum_filter_three, sum_filter_three]
  simp only [fx, fy, fw, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, ite_true, hne, ite_false]
  have : (1 + ε) ≠ 0 := by linarith
  field_simp; ring

lemma fam_phi (f : ℝ → ℝ) (hab : a ≠ b) (h0 : 0 < ε) (h1 : ε < 1) :
    rhs f (fx a b) (fy a b ε) (fw ε) - lhs f (fx a b) (fy a b ε) (fw ε) = phi f a b ε := by
  have m0 : mu (fx a b) (fy a b ε) (fw ε) (fy a b ε 0) = a := by
    simpa [fy] using fam_mu1 hab h0 h1
  have m1 : mu (fx a b) (fy a b ε) (fw ε) (fy a b ε 1) = b - ε * (b - a) / (1 + ε) := by
    simpa [fy] using fam_mu2 hab h0 h1
  have m2 : mu (fx a b) (fy a b ε) (fw ε) (fy a b ε 2) = b - ε * (b - a) / (1 + ε) := by
    simpa [fy] using fam_mu2 hab h0 h1
  simp only [rhs, lhs, Fin.sum_univ_three, m0, m1, m2]
  simp only [fx, fy, fw, phi, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  ring

end family

/-- The derivative of `Δ` at `ε = 0`: `f b - f a - (b - a)/2 (f' a + f' b)`. -/
lemma phi_hasDerivAt (f : ℝ → ℝ) (hf : Differentiable ℝ f) (a b : ℝ) :
    HasDerivAt (phi f a b) (f b - f a - (b - a) / 2 * (deriv f a + deriv f b)) 0 := by
  have hu : HasDerivAt (fun e : ℝ => a - e * (b - a) / (1 - e)) (-(b - a)) 0 := by
    have := (((hasDerivAt_id' (0:ℝ)).mul_const (b - a)).div
      ((hasDerivAt_id' (0:ℝ)).const_sub 1) (by norm_num)).const_sub a
    convert this using 1
    norm_num
  have hv : HasDerivAt (fun e : ℝ => b - e * (b - a) / (1 + e)) (-(b - a)) 0 := by
    have := (((hasDerivAt_id' (0:ℝ)).mul_const (b - a)).div
      ((hasDerivAt_id' (0:ℝ)).const_add 1) (by norm_num)).const_sub b
    convert this using 1
    norm_num
  have hfu : HasDerivAt (fun e : ℝ => f (a - e * (b - a) / (1 - e))) (deriv f a * (-(b - a))) 0 :=
    HasDerivAt.comp_of_eq (0:ℝ) (hf a).hasDerivAt hu (by simp)
  have hfv : HasDerivAt (fun e : ℝ => f (b - e * (b - a) / (1 + e))) (deriv f b * (-(b - a))) 0 :=
    HasDerivAt.comp_of_eq (0:ℝ) (hf b).hasDerivAt hv (by simp)
  have hl1 : HasDerivAt (fun e : ℝ => (1 - e) / 2) (-1 / 2) 0 :=
    ((hasDerivAt_id' (0:ℝ)).const_sub 1).div_const 2
  have hl2 : HasDerivAt (fun e : ℝ => (1 + e) / 2) (1 / 2) 0 :=
    ((hasDerivAt_id' (0:ℝ)).const_add 1).div_const 2
  have T1 := hl1.mul (hfu.sub_const (f a))
  have T2 := (hasDerivAt_id' (0:ℝ)).mul_const (f a)
  have T3 := (hasDerivAt_id' (0:ℝ)).mul_const (f b)
  have T4 := hl2.mul (hfv.sub_const (f b))
  have := ((T1.sub T2).add T3).add T4
  convert this using 1
  · funext e
    simp only [phi, Pi.add_apply, Pi.sub_apply, Pi.mul_apply]
  · norm_num
    ring

/-- If `Comparison f` then the trapezoid defect `f b - f a - (b-a)/2 (f' a + f' b)` is `≥ 0`. -/
lemma trap_nonneg (f : ℝ → ℝ) (hf : Differentiable ℝ f) (hC : Comparison f) {a b : ℝ}
    (hab : a ≠ b) : 0 ≤ f b - f a - (b - a) / 2 * (deriv f a + deriv f b) := by
  have hd := (phi_hasDerivAt f hf a b).tendsto_slope_zero_right
  have h0 : phi f a b 0 = 0 := by simp [phi]
  refine ge_of_tendsto hd ?_
  filter_upwards [Ioo_mem_nhdsGT (show (0:ℝ) < 1 by norm_num)] with t ht
  have hle := hC 3 (fx a b) (fy a b t) (fw t) (fam_law ht.1 ht.2) (fam_mart hab ht.2)
  have hp : 0 ≤ phi f a b t := by
    have := fam_phi f hab ht.1 ht.2
    linarith
  simp only [zero_add, h0, sub_zero, smul_eq_mul]
  exact mul_nonneg (inv_nonneg.2 ht.1.le) hp

/-- Trapezoid identity: `f d - f c = (d - c)/2 (f' c + f' d)` for all `c, d`. -/
lemma trap_eq (f : ℝ → ℝ) (hf : Differentiable ℝ f) (hC : Comparison f) (c d : ℝ) :
    f d - f c = (d - c) / 2 * (deriv f c + deriv f d) := by
  by_cases hcd : c = d
  · subst hcd; ring
  · have h1 := trap_nonneg f hf hC hcd
    have h2 := trap_nonneg f hf hC (Ne.symm hcd)
    linarith

/-- **Necessity**: a differentiable `f` satisfying the comparison is a quadratic. -/
theorem quadratic_of_comparison (f : ℝ → ℝ) (hf : Differentiable ℝ f) (hC : Comparison f) :
    ∃ α β γ : ℝ, 0 ≤ α ∧ ∀ t, f t = α * t ^ 2 + β * t + γ := by
  have hg : ∀ t, deriv f t = (1 - t) * deriv f 0 + t * deriv f 1 := by
    intro t
    have e1 := trap_eq f hf hC 0 t
    have e2 := trap_eq f hf hC t 1
    have e3 := trap_eq f hf hC 0 1
    linear_combination (-2) * e1 + (-2) * e2 + 2 * e3
  have hq : ∀ t, f t = (deriv f 1 - deriv f 0) / 2 * t ^ 2 + deriv f 0 * t + f 0 := by
    intro t
    have e1 := trap_eq f hf hC 0 t
    linear_combination e1 + (t / 2) * hg t
  refine ⟨(deriv f 1 - deriv f 0) / 2, deriv f 0, f 0, ?_, hq⟩
  -- α ≥ 0: test on the explicit coupling, where `rhs - lhs = α / 8`
  have hfeq : f = fun t => (deriv f 1 - deriv f 0) / 2 * t ^ 2 + deriv f 0 * t + f 0 := funext hq
  have hle := hC 3 cx cy cw cw_law c_mart
  have := rhs_sub_lhs_quadratic ((deriv f 1 - deriv f 0) / 2) (deriv f 0) (f 0) cx cy cw
    cw_law.1 c_mart
  rw [← hfeq] at this
  have hv : ∑ i, cw i * (cy i - mu cx cy cw (cy i)) ^ 2 = 1 / 8 := by
    have h0 : mu cx cy cw (cy 0) = 0 := by simpa [cy] using c_mu_neg
    have h1 : mu cx cy cw (cy 1) = 3/4 := by simpa [cy] using c_mu_one
    have h2 : mu cx cy cw (cy 2) = 3/4 := by simpa [cy] using c_mu_one
    simp only [Fin.sum_univ_three, h0, h1, h2]
    simp [cy, cw]; norm_num
  rw [hv] at this
  linarith

/-- **Main theorem (MO 451543).** For differentiable `f : ℝ → ℝ`, the Jensen-slack comparison
`E[f X - f (μ Y)] ≤ E[f Y - f X]` holds for every finite coupling with `E[Y|X] = X` iff
`f t = α t² + β t + γ` with `α ≥ 0`. -/
theorem comparison_iff (f : ℝ → ℝ) (hf : Differentiable ℝ f) :
    Comparison f ↔ ∃ α β γ : ℝ, 0 ≤ α ∧ ∀ t, f t = α * t ^ 2 + β * t + γ := by
  constructor
  · exact quadratic_of_comparison f hf
  · rintro ⟨α, β, γ, hα, hfq⟩
    have : f = fun t => α * t ^ 2 + β * t + γ := funext hfq
    rw [this]; exact comparison_of_quadratic α β γ hα

/-! ## From differentiable to continuous `f` (hence every convex `f`)

`Comparison` is invariant under translation and averaging, so the averages
`F_δ t = δ⁻¹ ∫₀^δ f (t + s) ds` of a continuous `f` satisfy it and are differentiable; hence each `F_δ`
is quadratic, and `F_δ → f` pointwise as `δ → 0⁺`. -/

lemma mu_shift (x y w : ι → ℝ) (s y₀ : ℝ)
    (hS : ∑ i ∈ univ.filter (fun i => y i = y₀), w i ≠ 0) :
    mu (fun i => x i + s) (fun i => y i + s) w (y₀ + s) = mu x y w y₀ + s := by
  have hf : univ.filter (fun i => y i + s = y₀ + s) = univ.filter (fun i => y i = y₀) :=
    Finset.filter_congr (fun i _ => add_right_cancel_iff)
  rw [mu, mu, hf]
  have : ∑ i ∈ univ.filter (fun i => y i = y₀), w i * (x i + s) =
      ∑ i ∈ univ.filter (fun i => y i = y₀), w i * x i +
        s * ∑ i ∈ univ.filter (fun i => y i = y₀), w i := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  rw [this]
  field_simp

lemma mart_shift (x y w : ι → ℝ) (hm : IsMart x y w) (s : ℝ) :
    IsMart (fun i => x i + s) (fun i => y i + s) w := by
  intro x₀
  have hf : univ.filter (fun i => x i + s = x₀) = univ.filter (fun i => x i = x₀ - s) :=
    Finset.filter_congr (fun i _ => by constructor <;> intro h <;> linarith)
  rw [hf]
  have := hm (x₀ - s)
  have e : ∑ i ∈ univ.filter (fun i => x i = x₀ - s), w i * (y i + s) =
      ∑ i ∈ univ.filter (fun i => x i = x₀ - s), w i * y i +
        s * ∑ i ∈ univ.filter (fun i => x i = x₀ - s), w i := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  rw [e, this]; ring

/-- `rhs - lhs` as a linear functional of `f` (the `μ`-values do not depend on `f`). -/
lemma rhs_sub_lhs_eq (f : ℝ → ℝ) (x y w : ι → ℝ) :
    rhs f x y w - lhs f x y w = ∑ i, w i * (f (y i) + f (mu x y w (y i)) - 2 * f (x i)) := by
  simp only [rhs, lhs, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl (fun i _ => by ring)

lemma K_nonneg (f : ℝ → ℝ) (x y w : ι → ℝ) (hw : IsLaw w)
    (hsh : ∀ s, lhs f (fun i => x i + s) (fun i => y i + s) w ≤ rhs f (fun i => x i + s) (fun i => y i + s) w)
    (s : ℝ) :
    0 ≤ ∑ i, w i * (f (y i + s) + f (mu x y w (y i) + s) - 2 * f (x i + s)) := by
  have hle := hsh s
  have e := rhs_sub_lhs_eq f (fun i => x i + s) (fun i => y i + s) w
  have e2 : ∑ i, w i * (f (y i + s) + f (mu (fun i => x i + s) (fun i => y i + s) w (y i + s))
      - 2 * f (x i + s)) = ∑ i, w i * (f (y i + s) + f (mu x y w (y i) + s) - 2 * f (x i + s)) := by
    refine Finset.sum_congr rfl (fun i _ => ?_)
    by_cases hwi : w i = 0
    · rw [hwi, zero_mul, zero_mul]
    · have hS : ∑ j ∈ univ.filter (fun j => y j = y i), w j ≠ 0 := by
        have hpos : 0 < w i := lt_of_le_of_ne (hw.1 i) (Ne.symm hwi)
        have : w i ≤ ∑ j ∈ univ.filter (fun j => y j = y i), w j :=
          Finset.single_le_sum (f := w) (fun j _ => hw.1 j) (by simp)
        linarith
      rw [mu_shift x y w s (y i) hS]
  linarith

/-- The averages `F_δ`. -/
def avg (f : ℝ → ℝ) (δ t : ℝ) : ℝ := δ⁻¹ * ∫ s in (0:ℝ)..δ, f (t + s)

lemma avg_le (f : ℝ → ℝ) (hf : Continuous f) (x y w : ι → ℝ) (hw : IsLaw w)
    (hsh : ∀ s, lhs f (fun i => x i + s) (fun i => y i + s) w ≤ rhs f (fun i => x i + s) (fun i => y i + s) w)
    {δ : ℝ} (hδ : 0 < δ) : lhs (avg f δ) x y w ≤ rhs (avg f δ) x y w := by
  have hI : ∀ c : ℝ, IntervalIntegrable (fun s => f (c + s)) MeasureTheory.volume 0 δ :=
    fun c => (hf.comp (continuous_const.add continuous_id)).intervalIntegrable _ _
  have key : ∫ s in (0:ℝ)..δ, ∑ i, w i * (f (y i + s) + f (mu x y w (y i) + s) - 2 * f (x i + s)) =
      ∑ i, w i * ((∫ s in (0:ℝ)..δ, f (y i + s)) + (∫ s in (0:ℝ)..δ, f (mu x y w (y i) + s))
        - 2 * ∫ s in (0:ℝ)..δ, f (x i + s)) := by
    rw [intervalIntegral.integral_finsetSum]
    · refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_sub,
        intervalIntegral.integral_add, intervalIntegral.integral_const_mul]
      · exact hI _
      · exact hI _
      · exact (hI _).add (hI _)
      · exact (hI _).const_mul 2
    · intro i _
      exact (((hI _).add (hI _)).sub ((hI _).const_mul 2)).const_mul (w i)
  have hnn : 0 ≤ ∫ s in (0:ℝ)..δ,
      ∑ i, w i * (f (y i + s) + f (mu x y w (y i) + s) - 2 * f (x i + s)) :=
    intervalIntegral.integral_nonneg hδ.le (fun s _ => K_nonneg f x y w hw hsh s)
  have e := rhs_sub_lhs_eq (avg f δ) x y w
  have e2 : ∑ i, w i * (avg f δ (y i) + avg f δ (mu x y w (y i)) - 2 * avg f δ (x i)) =
      δ⁻¹ * ∑ i, w i * ((∫ s in (0:ℝ)..δ, f (y i + s)) + (∫ s in (0:ℝ)..δ, f (mu x y w (y i) + s))
        - 2 * ∫ s in (0:ℝ)..δ, f (x i + s)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    simp only [avg]; ring
  rw [e2, ← key] at e
  have : 0 ≤ rhs (avg f δ) x y w - lhs (avg f δ) x y w := by
    rw [e]; exact mul_nonneg (inv_nonneg.2 hδ.le) hnn
  linarith

lemma comparison_avg (f : ℝ → ℝ) (hf : Continuous f) (hC : Comparison f) {δ : ℝ} (hδ : 0 < δ) :
    Comparison (avg f δ) :=
  fun m x y w hw hm => avg_le f hf x y w hw (fun s => hC m _ _ w hw (mart_shift x y w hm s)) hδ

/-- `F_δ t = δ⁻¹ (G (t + δ) - G t)` with `G u = ∫₀^u f`. -/
lemma avg_eq (f : ℝ → ℝ) (hf : Continuous f) (δ t : ℝ) :
    avg f δ t = δ⁻¹ * ((∫ u in (0:ℝ)..(t + δ), f u) - ∫ u in (0:ℝ)..t, f u) := by
  rw [avg, intervalIntegral.integral_comp_add_left, add_zero,
    intervalIntegral.integral_interval_sub_left (hf.intervalIntegrable _ _)
      (hf.intervalIntegrable _ _)]

lemma avg_differentiable (f : ℝ → ℝ) (hf : Continuous f) (δ : ℝ) :
    Differentiable ℝ (avg f δ) := by
  have hG : Differentiable ℝ (fun u => ∫ x in (0:ℝ)..u, f x) :=
    fun u => (hf.integral_hasStrictDerivAt 0 u).hasDerivAt.differentiableAt
  have : avg f δ = fun t => δ⁻¹ * ((∫ u in (0:ℝ)..(t + δ), f u) - ∫ u in (0:ℝ)..t, f u) :=
    funext (avg_eq f hf δ)
  rw [this]
  exact ((hG.comp (differentiable_id.add_const δ)).sub hG).const_mul _

lemma avg_tendsto (f : ℝ → ℝ) (hf : Continuous f) (t : ℝ) :
    Filter.Tendsto (fun δ => avg f δ t) (nhdsWithin 0 (Set.Ioi 0)) (nhds (f t)) := by
  have hG := (hf.integral_hasStrictDerivAt 0 t).hasDerivAt.tendsto_slope_zero_right
  refine hG.congr (fun δ => ?_)
  rw [avg_eq f hf, smul_eq_mul, add_comm t δ]

/-- Quadratic interpolation through `-1, 0, 1`. -/
lemma quad_interp {α β γ : ℝ} {F : ℝ → ℝ} (hF : ∀ t, F t = α * t ^ 2 + β * t + γ) (t : ℝ) :
    F t = F 0 + t * (F 1 - F (-1)) / 2 + t ^ 2 * (F 1 - 2 * F 0 + F (-1)) / 2 := by
  rw [hF t, hF 0, hF 1, hF (-1)]; ring

/-- `α ≥ 0` is forced by the explicit coupling. -/
lemma alpha_nonneg (f : ℝ → ℝ) (hC : Comparison f) {α β γ : ℝ}
    (hq : ∀ t, f t = α * t ^ 2 + β * t + γ) : 0 ≤ α := by
  have hfeq : f = fun t => α * t ^ 2 + β * t + γ := funext hq
  have hle := hC 3 cx cy cw cw_law c_mart
  have := rhs_sub_lhs_quadratic α β γ cx cy cw cw_law.1 c_mart
  rw [← hfeq] at this
  have hv : ∑ i, cw i * (cy i - mu cx cy cw (cy i)) ^ 2 = 1 / 8 := by
    have h0 : mu cx cy cw (cy 0) = 0 := by simpa [cy] using c_mu_neg
    have h1 : mu cx cy cw (cy 1) = 3/4 := by simpa [cy] using c_mu_one
    have h2 : mu cx cy cw (cy 2) = 3/4 := by simpa [cy] using c_mu_one
    simp only [Fin.sum_univ_three, h0, h1, h2]
    simp [cy, cw]; norm_num
  rw [hv] at this
  linarith

/-- **Main theorem, continuous version.** For continuous `f : ℝ → ℝ` (in particular every convex
`f : ℝ → ℝ`), the comparison holds for all finite couplings iff `f` is a quadratic with `α ≥ 0`. -/
theorem comparison_iff_of_continuous (f : ℝ → ℝ) (hf : Continuous f) :
    Comparison f ↔ ∃ α β γ : ℝ, 0 ≤ α ∧ ∀ t, f t = α * t ^ 2 + β * t + γ := by
  constructor
  · intro hC
    have hq : ∀ t, f t = f 0 + t * (f 1 - f (-1)) / 2 + t ^ 2 * (f 1 - 2 * f 0 + f (-1)) / 2 := by
      intro t
      have hev : ∀ᶠ δ in nhdsWithin (0:ℝ) (Set.Ioi 0), avg f δ t = avg f δ 0
          + t * (avg f δ 1 - avg f δ (-1)) / 2 + t ^ 2 * (avg f δ 1 - 2 * avg f δ 0 + avg f δ (-1)) / 2 := by
        filter_upwards [self_mem_nhdsWithin] with δ hδ
        obtain ⟨α, β, γ, -, hq⟩ := quadratic_of_comparison (avg f δ) (avg_differentiable f hf δ)
          (comparison_avg f hf hC hδ)
        exact quad_interp hq t
      have hR : Filter.Tendsto (fun δ => avg f δ 0
          + t * (avg f δ 1 - avg f δ (-1)) / 2 + t ^ 2 * (avg f δ 1 - 2 * avg f δ 0 + avg f δ (-1)) / 2)
          (nhdsWithin (0:ℝ) (Set.Ioi 0))
          (nhds (f 0 + t * (f 1 - f (-1)) / 2 + t ^ 2 * (f 1 - 2 * f 0 + f (-1)) / 2)) := by
        have h0 := avg_tendsto f hf 0
        have h1 := avg_tendsto f hf 1
        have hm := avg_tendsto f hf (-1)
        exact (h0.add (((h1.sub hm).const_mul t).div_const 2)).add
          ((((h1.sub (h0.const_mul 2)).add hm).const_mul (t ^ 2)).div_const 2)
      exact tendsto_nhds_unique ((avg_tendsto f hf t).congr' (Filter.EventuallyEq.symm
        (by filter_upwards [hev] with δ h; exact h.symm))) hR
    have hq' : ∀ t, f t = (f 1 - 2 * f 0 + f (-1)) / 2 * t ^ 2 + (f 1 - f (-1)) / 2 * t + f 0 := by
      intro t; rw [hq t]; ring
    exact ⟨_, _, _, alpha_nonneg f hC hq', hq'⟩
  · rintro ⟨α, β, γ, hα, hfq⟩
    have : f = fun t => α * t ^ 2 + β * t + γ := funext hfq
    rw [this]; exact comparison_of_quadratic α β γ hα

/-- **Answer to MO 451543 for convex `f`.** A convex `f : ℝ → ℝ` satisfies the comparison for all finite
couplings iff it is a quadratic `α t² + β t + γ` (necessarily `α ≥ 0`). -/
theorem comparison_iff_of_convex (f : ℝ → ℝ) (hcvx : ConvexOn ℝ Set.univ f) :
    Comparison f ↔ ∃ α β γ : ℝ, 0 ≤ α ∧ ∀ t, f t = α * t ^ 2 + β * t + γ :=
  comparison_iff_of_continuous f
    (continuousOn_univ.1 (hcvx.continuousOn isOpen_univ))

/-! ## Independent additive noise: `Y = X + Z`, `Z` independent of `X`, `E Z = 0`

Even inside this smaller class (the asker's own `|x|` example is of this form), only quadratics work. -/

/-- The comparison for every independent-noise coupling: `X = a i` w.p. `p i`, `Z = z j` w.p. `r j`
independent of `X` with `E Z = 0`, and `Y = X + Z` (indexed by `Fin n × Fin m`). -/
def IndepComparison (f : ℝ → ℝ) : Prop :=
  ∀ (n m : ℕ) (a p : Fin n → ℝ) (z r : Fin m → ℝ), IsLaw p → IsLaw r → ∑ j, r j * z j = 0 →
    lhs f (fun k : Fin n × Fin m => a k.1) (fun k => a k.1 + z k.2) (fun k => p k.1 * r k.2) ≤
    rhs f (fun k : Fin n × Fin m => a k.1) (fun k => a k.1 + z k.2) (fun k => p k.1 * r k.2)

section indep
variable {n m : ℕ}

lemma prod_law {p : Fin n → ℝ} {r : Fin m → ℝ} (hp : IsLaw p) (hr : IsLaw r) :
    IsLaw (fun k : Fin n × Fin m => p k.1 * r k.2) := by
  refine ⟨fun k => mul_nonneg (hp.1 _) (hr.1 _), ?_⟩
  rw [Fintype.sum_prod_type]
  simp_rw [← Finset.mul_sum, hr.2, mul_one, hp.2]

lemma prod_mart (a p : Fin n → ℝ) (z r : Fin m → ℝ) (hr : IsLaw r) (hz : ∑ j, r j * z j = 0) :
    IsMart (fun k : Fin n × Fin m => a k.1) (fun k => a k.1 + z k.2) (fun k => p k.1 * r k.2) := by
  intro x₀
  rw [Finset.sum_filter, Finset.sum_filter, Fintype.sum_prod_type, Fintype.sum_prod_type,
    Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  by_cases h : a i = x₀
  · simp only [h, ite_true]
    calc ∑ j, p i * r j * (x₀ + z j) = p i * x₀ * ∑ j, r j + p i * ∑ j, r j * z j := by
          rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl (fun j _ => by ring)
      _ = x₀ * ∑ j, p i * r j := by
          rw [hz, hr.2, ← Finset.mul_sum, hr.2]; ring
  · simp [h]

/-- Convex quadratics satisfy the independent-noise comparison. -/
theorem indepComparison_of_quadratic (α β γ : ℝ) (hα : 0 ≤ α) :
    IndepComparison (fun t => α * t ^ 2 + β * t + γ) := by
  intro n m a p z r hp hr hz
  have hw := prod_law hp hr
  have := rhs_sub_lhs_quadratic α β γ _ _ _ hw.1 (prod_mart a p z r hr hz)
  have hnn : 0 ≤ α * ∑ k, (fun k : Fin n × Fin m => p k.1 * r k.2) k *
      ((fun k : Fin n × Fin m => a k.1 + z k.2) k - mu (fun k : Fin n × Fin m => a k.1)
        (fun k => a k.1 + z k.2) (fun k => p k.1 * r k.2) ((fun k : Fin n × Fin m => a k.1 + z k.2) k)) ^ 2 :=
    mul_nonneg hα (Finset.sum_nonneg (fun k _ => mul_nonneg (hw.1 k) (sq_nonneg _)))
  linarith

end indep

/-- `Δ` for the independent family: `X = a` (prob `1-q`) or `b` (prob `q`);
`Z = -ε h` (prob `1-ε`) or `(1-ε) h` (prob `ε`), `h = b - a`. -/
def psi (f : ℝ → ℝ) (a b q ε : ℝ) : ℝ :=
  (1 - q) * (1 - ε) * (f (a - ε * (b - a)) - f a)
  + (1 - q) * ε * (f (b - ε * (b - a)) + f (b - (1 - q) * ε * (b - a) / ((1 - q) * ε + q * (1 - ε))) - 2 * f a)
  + q * (1 - ε) * (f (b - ε * (b - a)) + f (b - (1 - q) * ε * (b - a) / ((1 - q) * ε + q * (1 - ε))) - 2 * f b)
  + q * ε * (f (2 * b - a - ε * (b - a)) - f b)

section ifam
variable {a b q ε : ℝ}

def ia (a b : ℝ) : Fin 2 → ℝ := ![a, b]
def ip (q : ℝ) : Fin 2 → ℝ := ![1 - q, q]
def iz (a b ε : ℝ) : Fin 2 → ℝ := ![-(ε * (b - a)), (1 - ε) * (b - a)]
def ir (ε : ℝ) : Fin 2 → ℝ := ![1 - ε, ε]

lemma mu_prod_two (X Y W : Fin 2 × Fin 2 → ℝ) (v : ℝ) : mu X Y W v =
    (((if Y (0, 0) = v then W (0, 0) * X (0, 0) else 0) + (if Y (0, 1) = v then W (0, 1) * X (0, 1) else 0)) +
      ((if Y (1, 0) = v then W (1, 0) * X (1, 0) else 0) + (if Y (1, 1) = v then W (1, 1) * X (1, 1) else 0))) /
    (((if Y (0, 0) = v then W (0, 0) else 0) + (if Y (0, 1) = v then W (0, 1) else 0)) +
      ((if Y (1, 0) = v then W (1, 0) else 0) + (if Y (1, 1) = v then W (1, 1) else 0))) := by
  rw [mu, Finset.sum_filter, Finset.sum_filter, Fintype.sum_prod_type, Fintype.sum_prod_type,
    Fin.sum_univ_two, Fin.sum_univ_two, Fin.sum_univ_two, Fin.sum_univ_two, Fin.sum_univ_two,
    Fin.sum_univ_two]

lemma ifam_psi (f : ℝ → ℝ) (hab : a ≠ b) (hq0 : 0 < q) (hq1 : q < 1) (he0 : 0 < ε) (he1 : ε < 1) :
    rhs f (fun k : Fin 2 × Fin 2 => ia a b k.1) (fun k => ia a b k.1 + iz a b ε k.2)
        (fun k => ip q k.1 * ir ε k.2) -
      lhs f (fun k : Fin 2 × Fin 2 => ia a b k.1) (fun k => ia a b k.1 + iz a b ε k.2)
        (fun k => ip q k.1 * ir ε k.2) = psi f a b q ε := by
  have hh : b - a ≠ 0 := sub_ne_zero.2 (Ne.symm hab)
  -- the three distinct values of Y
  have d1 : a + -(ε * (b - a)) ≠ a + (1 - ε) * (b - a) := by
    intro h; apply hh; linarith
  have d2 : a + -(ε * (b - a)) ≠ b + -(ε * (b - a)) := by
    intro h; apply hh; linarith
  have d3 : a + -(ε * (b - a)) ≠ b + (1 - ε) * (b - a) := by
    intro h; apply hh; linarith
  have d4 : a + (1 - ε) * (b - a) = b + -(ε * (b - a)) := by ring
  have d5 : a + (1 - ε) * (b - a) ≠ b + (1 - ε) * (b - a) := by
    intro h; apply hh; linarith
  have d6 : b + -(ε * (b - a)) ≠ b + (1 - ε) * (b - a) := by
    intro h; apply hh; linarith
  have hm : (1 - q) * ε + q * (1 - ε) ≠ 0 := by nlinarith
  have hm1 : (1 - q) * (1 - ε) ≠ 0 := by
    apply mul_ne_zero <;> linarith
  have hm2 : q * ε ≠ 0 := by positivity
  rw [rhs_sub_lhs_eq, Fintype.sum_prod_type, Fin.sum_univ_two, Fin.sum_univ_two, Fin.sum_univ_two]
  simp only [mu_prod_two]
  simp only [ia, ip, iz, ir, Matrix.cons_val_zero, Matrix.cons_val_one,
    ite_true, d2, d3, d4, d6, Ne.symm d2, Ne.symm d3,
    Ne.symm d6, ite_false, zero_add, add_zero]
  have M1 : (1 - q) * (1 - ε) * a / ((1 - q) * (1 - ε)) = a := by field_simp
  have M2 : ((1 - q) * ε * a + q * (1 - ε) * b) / ((1 - q) * ε + q * (1 - ε)) =
      b - (1 - q) * ε * (b - a) / ((1 - q) * ε + q * (1 - ε)) := by
    field_simp; ring
  have M3 : q * ε * b / (q * ε) = b := by field_simp
  rw [M1, M2, M3, psi]
  have e1 : a + -(ε * (b - a)) = a - ε * (b - a) := by ring
  have e2 : b + -(ε * (b - a)) = b - ε * (b - a) := by ring
  have e3 : b + (1 - ε) * (b - a) = 2 * b - a - ε * (b - a) := by ring
  rw [e1, e2, e3]
  ring

end ifam

lemma psi_hasDerivAt (f : ℝ → ℝ) (hf : Differentiable ℝ f) (a b q : ℝ) (hq : q ≠ 0) :
    HasDerivAt (psi f a b q)
      ((1 - q) * (2 * (f b - f a) - (b - a) * (deriv f a + deriv f b))
        + q * (f (2 * b - a) - f b - (b - a) * deriv f b)) 0 := by
  have hid := hasDerivAt_id' (0:ℝ)
  have hu1 : HasDerivAt (fun e : ℝ => a - e * (b - a)) (-(b - a)) 0 := by
    simpa using (hid.mul_const (b - a)).const_sub a
  have hu2 : HasDerivAt (fun e : ℝ => b - e * (b - a)) (-(b - a)) 0 := by
    simpa using (hid.mul_const (b - a)).const_sub b
  have hu3 : HasDerivAt (fun e : ℝ => 2 * b - a - e * (b - a)) (-(b - a)) 0 := by
    simpa using (hid.mul_const (b - a)).const_sub (2 * b - a)
  have hden : HasDerivAt (fun e : ℝ => (1 - q) * e + q * (1 - e)) ((1 - q) - q) 0 := by
    have := (hid.const_mul (1 - q)).add ((hid.const_sub 1).const_mul q)
    convert this using 1; ring_nf
  have hnum : HasDerivAt (fun e : ℝ => (1 - q) * e * (b - a)) ((1 - q) * (b - a)) 0 := by
    simpa using (hid.const_mul (1 - q)).mul_const (b - a)
  have hM : HasDerivAt (fun e : ℝ => b - (1 - q) * e * (b - a) / ((1 - q) * e + q * (1 - e)))
      (-((1 - q) * (b - a) / q)) 0 := by
    have := (hnum.div hden (by simpa using hq)).const_sub b
    convert this using 1
    have hq2 : ((1 - q) * 0 + q * (1 - 0)) = q := by ring
    rw [hq2]
    field_simp
    ring
  have F1 := HasDerivAt.comp_of_eq (0:ℝ) (hf a).hasDerivAt hu1 (by simp)
  have F2 := HasDerivAt.comp_of_eq (0:ℝ) (hf b).hasDerivAt hu2 (by simp)
  have F3 := HasDerivAt.comp_of_eq (0:ℝ) (hf (2 * b - a)).hasDerivAt hu3 (by simp)
  have F4 := HasDerivAt.comp_of_eq (0:ℝ) (hf b).hasDerivAt hM (by simp)
  have c1 : HasDerivAt (fun e : ℝ => (1 - q) * (1 - e)) (-(1 - q)) 0 := by
    simpa using (hid.const_sub 1).const_mul (1 - q)
  have c2 : HasDerivAt (fun e : ℝ => (1 - q) * e) (1 - q) 0 := by
    simpa using hid.const_mul (1 - q)
  have c3 : HasDerivAt (fun e : ℝ => q * (1 - e)) (-q) 0 := by
    simpa using (hid.const_sub 1).const_mul q
  have c4 : HasDerivAt (fun e : ℝ => q * e) q 0 := by
    simpa using hid.const_mul q
  have T1 := c1.mul (F1.sub_const (f a))
  have T2 := c2.mul ((F2.add F4).sub_const (2 * f a))
  have T3 := c3.mul ((F2.add F4).sub_const (2 * f b))
  have T4 := c4.mul (F3.sub_const (f b))
  have := ((T1.add T2).add T3).add T4
  convert this using 1
  · funext e
    simp only [psi, Pi.add_apply, Pi.mul_apply, Function.comp_apply]
  · simp only [Function.comp_apply]
    norm_num
    field_simp
    ring

lemma psi_zero (f : ℝ → ℝ) (a b q : ℝ) (_hq : q ≠ 0) : psi f a b q 0 = 0 := by
  simp only [psi]
  have : (1 - q) * 0 + q * (1 - 0) = q := by ring
  rw [this]
  simp only [mul_zero, zero_mul, sub_zero, zero_div, add_zero, mul_one]
  ring

/-- Independent-noise comparison forces the trapezoid defect to be `≥ 0`. -/
lemma itrap_nonneg (f : ℝ → ℝ) (hf : Differentiable ℝ f) (hC : IndepComparison f) {a b : ℝ}
    (hab : a ≠ b) : 0 ≤ f b - f a - (b - a) / 2 * (deriv f a + deriv f b) := by
  -- step 1: for each q ∈ (0,1), the ε-derivative at 0 is ≥ 0
  have step : ∀ q : ℝ, 0 < q → q < 1 →
      0 ≤ (1 - q) * (2 * (f b - f a) - (b - a) * (deriv f a + deriv f b))
        + q * (f (2 * b - a) - f b - (b - a) * deriv f b) := by
    intro q hq0 hq1
    have hd := (psi_hasDerivAt f hf a b q hq0.ne').tendsto_slope_zero_right
    refine ge_of_tendsto hd ?_
    filter_upwards [Ioo_mem_nhdsGT (show (0:ℝ) < 1 by norm_num)] with t ht
    have hle := hC 2 2 (ia a b) (ip q) (iz a b t) (ir t)
      ⟨fun i => by fin_cases i <;> simp [ip] <;> linarith, by simp [ip, Fin.sum_univ_two]⟩
      ⟨fun i => by fin_cases i <;> simp [ir] <;> linarith [ht.1, ht.2], by simp [ir, Fin.sum_univ_two]⟩
      (by simp [ir, iz, Fin.sum_univ_two]; ring)
    have hp : 0 ≤ psi f a b q t := by
      have := ifam_psi f hab hq0 hq1 ht.1 ht.2
      linarith
    simp only [zero_add, psi_zero f a b q hq0.ne', sub_zero, smul_eq_mul]
    exact mul_nonneg (inv_nonneg.2 ht.1.le) hp
  -- step 2: let q → 0⁺
  have hlim : Filter.Tendsto (fun q : ℝ => (1 - q) * (2 * (f b - f a) - (b - a) * (deriv f a + deriv f b))
        + q * (f (2 * b - a) - f b - (b - a) * deriv f b)) (nhdsWithin 0 (Set.Ioi 0))
      (nhds (2 * (f b - f a) - (b - a) * (deriv f a + deriv f b))) := by
    have hc : Continuous (fun q : ℝ => (1 - q) * (2 * (f b - f a) - (b - a) * (deriv f a + deriv f b))
        + q * (f (2 * b - a) - f b - (b - a) * deriv f b)) := by fun_prop
    have := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
    simpa using this
  have h2 : 0 ≤ 2 * (f b - f a) - (b - a) * (deriv f a + deriv f b) := by
    refine ge_of_tendsto hlim ?_
    filter_upwards [Ioo_mem_nhdsGT (show (0:ℝ) < 1 by norm_num)] with q hq
    exact step q hq.1 hq.2
  linarith

/-- `α ≥ 0` from the independent coupling `X ≡ 0`, `Z = ±1`. -/
lemma alpha_nonneg_indep (f : ℝ → ℝ) (hC : IndepComparison f) {α β γ : ℝ}
    (hq : ∀ t, f t = α * t ^ 2 + β * t + γ) : 0 ≤ α := by
  have hfeq : f = fun t => α * t ^ 2 + β * t + γ := funext hq
  have hp : IsLaw (![1] : Fin 1 → ℝ) := ⟨fun i => by fin_cases i; simp, by simp⟩
  have hr : IsLaw (![1/2, 1/2] : Fin 2 → ℝ) :=
    ⟨fun i => by fin_cases i <;> simp, by simp [Fin.sum_univ_two]; norm_num⟩
  have hz : ∑ j, (![1/2, 1/2] : Fin 2 → ℝ) j * (![-1, 1] : Fin 2 → ℝ) j = 0 := by
    simp [Fin.sum_univ_two]
  have hle := hC 1 2 ![0] ![1] ![-1, 1] ![1/2, 1/2] hp hr hz
  have := rhs_sub_lhs_quadratic α β γ (fun k : Fin 1 × Fin 2 => (![0] : Fin 1 → ℝ) k.1)
    (fun k => (![0] : Fin 1 → ℝ) k.1 + (![-1, 1] : Fin 2 → ℝ) k.2)
    (fun k => (![1] : Fin 1 → ℝ) k.1 * (![1/2, 1/2] : Fin 2 → ℝ) k.2) (prod_law hp hr).1
    (prod_mart _ _ _ _ hr hz)
  rw [← hfeq] at this
  have hv : ∑ k : Fin 1 × Fin 2, (fun k : Fin 1 × Fin 2 => (![1] : Fin 1 → ℝ) k.1 *
      (![1/2, 1/2] : Fin 2 → ℝ) k.2) k * ((fun k : Fin 1 × Fin 2 => (![0] : Fin 1 → ℝ) k.1 +
      (![-1, 1] : Fin 2 → ℝ) k.2) k - mu (fun k : Fin 1 × Fin 2 => (![0] : Fin 1 → ℝ) k.1)
      (fun k => (![0] : Fin 1 → ℝ) k.1 + (![-1, 1] : Fin 2 → ℝ) k.2)
      (fun k => (![1] : Fin 1 → ℝ) k.1 * (![1/2, 1/2] : Fin 2 → ℝ) k.2)
      ((fun k : Fin 1 × Fin 2 => (![0] : Fin 1 → ℝ) k.1 + (![-1, 1] : Fin 2 → ℝ) k.2) k)) ^ 2 = 1 := by
    simp only [mu, Fintype.sum_prod_type, Fin.sum_univ_one, Fin.sum_univ_two, Finset.sum_filter,
      Matrix.cons_val_zero, Matrix.cons_val_one]
    norm_num
  rw [hv] at this
  linarith

/-- **Independent-noise theorem.** For continuous `f` (in particular convex `f`), the comparison holds
for every independent-noise coupling `Y = X + Z` iff `f` is a quadratic with `α ≥ 0`. -/
theorem indepComparison_iff_of_continuous (f : ℝ → ℝ) (hf : Continuous f) :
    IndepComparison f ↔ ∃ α β γ : ℝ, 0 ≤ α ∧ ∀ t, f t = α * t ^ 2 + β * t + γ := by
  constructor
  · intro hC
    -- the averages inherit the independent comparison (the class is translation invariant)
    have havg : ∀ δ : ℝ, 0 < δ → IndepComparison (avg f δ) := by
      intro δ hδ n m a p z r hp hr hz
      refine avg_le f hf _ _ _ (prod_law hp hr) (fun s => ?_) hδ
      have := hC n m (fun i => a i + s) p z r hp hr hz
      convert this using 2 <;> funext k <;> ring
    -- differentiable + independent comparison ⇒ quadratic
    have hquad : ∀ g : ℝ → ℝ, Differentiable ℝ g → IndepComparison g →
        ∀ t, g t = (deriv g 1 - deriv g 0) / 2 * t ^ 2 + deriv g 0 * t + g 0 := by
      intro g hg hCg
      have trap : ∀ c d, g d - g c = (d - c) / 2 * (deriv g c + deriv g d) := by
        intro c d
        by_cases hcd : c = d
        · subst hcd; ring
        · have h1 := itrap_nonneg g hg hCg hcd
          have h2 := itrap_nonneg g hg hCg (Ne.symm hcd)
          linarith
      have hg' : ∀ t, deriv g t = (1 - t) * deriv g 0 + t * deriv g 1 := by
        intro t
        linear_combination (-2) * trap 0 t + (-2) * trap t 1 + 2 * trap 0 1
      intro t
      linear_combination trap 0 t + (t / 2) * hg' t
    have hq : ∀ t, f t = f 0 + t * (f 1 - f (-1)) / 2 + t ^ 2 * (f 1 - 2 * f 0 + f (-1)) / 2 := by
      intro t
      have hev : ∀ᶠ δ in nhdsWithin (0:ℝ) (Set.Ioi 0), avg f δ t = avg f δ 0
          + t * (avg f δ 1 - avg f δ (-1)) / 2 + t ^ 2 * (avg f δ 1 - 2 * avg f δ 0 + avg f δ (-1)) / 2 := by
        filter_upwards [self_mem_nhdsWithin] with δ hδ
        exact quad_interp (hquad _ (avg_differentiable f hf δ) (havg δ hδ)) t
      have hR : Filter.Tendsto (fun δ => avg f δ 0
          + t * (avg f δ 1 - avg f δ (-1)) / 2 + t ^ 2 * (avg f δ 1 - 2 * avg f δ 0 + avg f δ (-1)) / 2)
          (nhdsWithin (0:ℝ) (Set.Ioi 0))
          (nhds (f 0 + t * (f 1 - f (-1)) / 2 + t ^ 2 * (f 1 - 2 * f 0 + f (-1)) / 2)) := by
        have h0 := avg_tendsto f hf 0
        have h1 := avg_tendsto f hf 1
        have hm := avg_tendsto f hf (-1)
        exact (h0.add (((h1.sub hm).const_mul t).div_const 2)).add
          ((((h1.sub (h0.const_mul 2)).add hm).const_mul (t ^ 2)).div_const 2)
      exact tendsto_nhds_unique ((avg_tendsto f hf t).congr' (Filter.EventuallyEq.symm
        (by filter_upwards [hev] with δ h; exact h.symm))) hR
    have hq' : ∀ t, f t = (f 1 - 2 * f 0 + f (-1)) / 2 * t ^ 2 + (f 1 - f (-1)) / 2 * t + f 0 := by
      intro t; rw [hq t]; ring
    exact ⟨_, _, _, alpha_nonneg_indep f hC hq', hq'⟩
  · rintro ⟨α, β, γ, hα, hfq⟩
    have : f = fun t => α * t ^ 2 + β * t + γ := funext hfq
    rw [this]; exact indepComparison_of_quadratic α β γ hα

theorem indepComparison_iff_of_convex (f : ℝ → ℝ) (hcvx : ConvexOn ℝ Set.univ f) :
    IndepComparison f ↔ ∃ α β γ : ℝ, 0 ≤ α ∧ ∀ t, f t = α * t ^ 2 + β * t + γ :=
  indepComparison_iff_of_continuous f (continuousOn_univ.1 (hcvx.continuousOn isOpen_univ))

end JensenSlack
