module

public import Feige.Bernoulli.Ex

/- Port (Palomar entry): `module` header, `public import`s and a public section added for the module system; otherwise unchanged from github.com/koolkao/feige-lean at commit 7da24abf1619706bf4f705bb24aa4d00bc63b49f. -/

@[expose] public section

/-!
# Finite products of two-point laws

`twoPt p x y = (1-p) δₓ + p δ_y`.  A finite product of such laws is the finite sum of Dirac
masses at the vectors `v_S = (if i ∈ S then yᵢ else xᵢ)` with weights `wt p univ S`
(the strategy `Measure.pi_eq` + `Finset.prod_add` was suggested by Gemini 4 Neon).
Consequently the product measure of any measurable set `A` is the finite Bernoulli
expectation `Ex p univ (1{v_S ∈ A})`.
-/

open MeasureTheory Finset ENNReal

namespace Samuels

noncomputable section

open scoped Classical

/-- The two-point law `(1-p) δₓ + p δ_y`. -/
def twoPt (p x y : ℝ) : Measure ℝ :=
  ENNReal.ofReal (1 - p) • Measure.dirac x + ENNReal.ofReal p • Measure.dirac y

lemma twoPt_isProbability {p x y : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    IsProbabilityMeasure (twoPt p x y) := by
  constructor
  simp [twoPt, ← ENNReal.ofReal_add (sub_nonneg.mpr hp1) hp0]

lemma twoPt_apply (p x y : ℝ) {B : Set ℝ} (hB : MeasurableSet B) :
    twoPt p x y B = (if y ∈ B then ENNReal.ofReal p else 0) +
      (if x ∈ B then ENNReal.ofReal (1 - p) else 0) := by
  simp only [twoPt, Measure.add_apply, Measure.smul_apply, Measure.dirac_apply' _ hB,
    smul_eq_mul]
  simp only [Set.indicator_apply]
  split_ifs <;> simp [add_comm]

variable {n : ℕ}

/-- The vector encoded by a high set. -/
def vecOf (x y : Fin n → ℝ) (S : Finset (Fin n)) : Fin n → ℝ :=
  fun i => if i ∈ S then y i else x i

theorem pi_twoPt_eq (p x y : Fin n → ℝ) (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1) :
    haveI := fun i => twoPt_isProbability (x := x i) (y := y i) (hp0 i) (hp1 i)
    Measure.pi (fun i => twoPt (p i) (x i) (y i)) =
      ∑ S ∈ (univ : Finset (Fin n)).powerset,
        ENNReal.ofReal (wt p univ S) • Measure.dirac (vecOf x y S) := by
  haveI := fun i => twoPt_isProbability (x := x i) (y := y i) (hp0 i) (hp1 i)
  apply Measure.pi_eq
  intro s hs
  have hbox : MeasurableSet (Set.univ.pi s) := MeasurableSet.univ_pi hs
  simp only [Measure.finsetSum_apply, Measure.smul_apply, Measure.dirac_apply' _ hbox,
    smul_eq_mul]
  simp_rw [twoPt_apply _ _ _ (hs _)]
  rw [Finset.prod_add (fun i => if y i ∈ s i then ENNReal.ofReal (p i) else 0)
    (fun i => if x i ∈ s i then ENNReal.ofReal (1 - p i) else 0)]
  apply Finset.sum_congr rfl
  intro S _
  have hwt : ENNReal.ofReal (wt p univ S) =
      (∏ i ∈ S, ENNReal.ofReal (p i)) * ∏ i ∈ univ \ S, ENNReal.ofReal (1 - p i) := by
    unfold wt
    rw [ENNReal.ofReal_mul (Finset.prod_nonneg fun i _ => hp0 i),
      ENNReal.ofReal_prod_of_nonneg (fun i _ => hp0 i),
      ENNReal.ofReal_prod_of_nonneg (fun i _ => sub_nonneg.mpr (hp1 i))]
  rw [hwt, Set.indicator_apply]
  by_cases hmem : vecOf x y S ∈ Set.univ.pi s
  · rw [if_pos hmem, Pi.one_apply, mul_one]
    have hm : ∀ i, vecOf x y S i ∈ s i := fun i => hmem i (Set.mem_univ i)
    congr 1
    · apply Finset.prod_congr rfl
      intro i hi
      have := hm i
      simp only [vecOf, if_pos hi] at this
      rw [if_pos this]
    · apply Finset.prod_congr rfl
      intro i hi
      have := hm i
      have hiS : i ∉ S := (mem_sdiff.mp hi).2
      simp only [vecOf, if_neg hiS] at this
      rw [if_pos this]
  · rw [if_neg hmem, mul_zero]
    simp only [Set.mem_pi, Set.mem_univ, true_implies, not_forall] at hmem
    obtain ⟨i, hi⟩ := hmem
    by_cases hiS : i ∈ S
    · simp only [vecOf, if_pos hiS] at hi
      rw [Finset.prod_eq_zero hiS (if_neg hi), zero_mul]
    · simp only [vecOf, if_neg hiS] at hi
      rw [Finset.prod_eq_zero (mem_sdiff.mpr ⟨mem_univ i, hiS⟩) (if_neg hi), mul_zero]

/-- The product measure of a measurable set, as a finite Bernoulli expectation. -/
theorem pi_twoPt_apply (p x y : Fin n → ℝ) (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1)
    {A : Set (Fin n → ℝ)} (hA : MeasurableSet A) :
    haveI := fun i => twoPt_isProbability (x := x i) (y := y i) (hp0 i) (hp1 i)
    (Measure.pi (fun i => twoPt (p i) (x i) (y i)) A).toReal =
      Ex p univ (fun S => if vecOf x y S ∈ A then 1 else 0) := by
  haveI := fun i => twoPt_isProbability (x := x i) (y := y i) (hp0 i) (hp1 i)
  rw [pi_twoPt_eq p x y hp0 hp1]
  simp only [Measure.finsetSum_apply, Measure.smul_apply, Measure.dirac_apply' _ hA,
    smul_eq_mul]
  rw [ENNReal.toReal_sum (fun S _ => by
    rw [Set.indicator_apply]; split_ifs <;> simp)]
  unfold Ex
  apply Finset.sum_congr rfl
  intro S hS
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal
    (wt_nonneg (fun i _ => hp0 i) (fun i _ => hp1 i) (mem_powerset.mp hS))]
  by_cases h : vecOf x y S ∈ A
  · rw [Set.indicator_of_mem h]; simp [h]
  · rw [Set.indicator_of_notMem h]; simp [h]

end

end Samuels

end
