/-
Copyright 2026 Ming-Chih Kao. Licensed under the Apache License, Version 2.0;
see the LICENSE file at the root of this repository.
-/
module

public import TanhDominance.Proof

/-! Port: copied from `Check.lean` of github.com/koolkao/mo505921-tanh-dominance (commit
25c3c9124f47df41a312f283451699a36b73a2df) and put into the module system (`module` header, public
section, references to `MO505921.*` renamed `TanhDominance.*`). Its statements are not compared by
Comparator; it is kept as the source repository's independent restatement of the question. -/

@[expose] public section

/-!
# Independent check: MathOverflow 505921 restated from the question text

This file restates the question without the vocabulary of `TanhDominance.lean` (no `HasLaw`, no
`gaussianReal`, no `cdf`, no consistency) and derives the answer from `TanhDominance.mo505921`.

Question (MathOverflow 505921, user tituf, 14 Dec 2025, CC BY-SA 4.0): let `X, Y, Z` be independent
Gaussian random variables with mean = variance, with parameters `g_X, g_Y, g_Z > 0`; put
`U := tanh X`, `V := tanh Y tanh Z`. Given `g_Y, g_Z > 0`, is there `g_X > 0` with
`tanh Y tanh Z ⪰_st tanh X`, i.e. `F_U(t) ≥ F_V(t)` for every `t ∈ (-1, 1)`, where
`F_T(t) := P(T ≤ t)`?

Here everything is written out by hand:
* `density g x = (2πg)^{-1/2} exp(-(x - g)² / (2g))`, the `N(g, g)` density;
* `IsGaussMV P W g`: `W` is measurable and `P(W ∈ s) = ∫_s density g` for every Borel `s`;
* `Indep3 P X Y Z`: `P(X ∈ A, Y ∈ B, Z ∈ C) = P(X ∈ A) P(Y ∈ B) P(Z ∈ C)` for all Borel `A, B, C`;
* `F P T t := P(T ≤ t)` (as a real number);
* `Dominates P A B` (`A ⪰_st B`): `F_B(t) ≥ F_A(t)` for every `t ∈ (-1, 1)`.
-/

open MeasureTheory ProbabilityTheory Set Real
open scoped ENNReal NNReal

namespace MO505921Check

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The density of the Gaussian with mean `g` and variance `g`. -/
noncomputable def density (g x : ℝ) : ℝ := (√(2 * π * g))⁻¹ * rexp (-(x - g) ^ 2 / (2 * g))

/-- `W` is Gaussian with mean = variance = `g`. -/
def IsGaussMV (P : Measure Ω) (W : Ω → ℝ) (g : ℝ) : Prop :=
  Measurable W ∧ ∀ s : Set ℝ, MeasurableSet s →
    P (W ⁻¹' s) = ∫⁻ x in s, ENNReal.ofReal (density g x)

/-- `X, Y, Z` are (mutually) independent. -/
def Indep3 (P : Measure Ω) (X Y Z : Ω → ℝ) : Prop :=
  ∀ A B C : Set ℝ, MeasurableSet A → MeasurableSet B → MeasurableSet C →
    P (X ⁻¹' A ∩ Y ⁻¹' B ∩ Z ⁻¹' C) = P (X ⁻¹' A) * P (Y ⁻¹' B) * P (Z ⁻¹' C)

/-- The c.d.f. `F_T(t) = P(T ≤ t)`. -/
noncomputable def F (P : Measure Ω) (T : Ω → ℝ) (t : ℝ) : ℝ := (P {ω | T ω ≤ t}).toReal

/-- `A ⪰_st B` in the sense of the question: `F_B(t) ≥ F_A(t)` for every `t ∈ (-1, 1)`. -/
def Dominates (P : Measure Ω) (A B : Ω → ℝ) : Prop := ∀ t ∈ Ioo (-1 : ℝ) 1, F P A t ≤ F P B t

/-! ## Translation to the vocabulary of `TanhDominance.lean` -/

lemma density_eq {g : ℝ} (hg : 0 ≤ g) (x : ℝ) :
    density g x = gaussianPDFReal (g.toNNReal : ℝ) g.toNNReal x := by
  simp [density, gaussianPDFReal, Real.coe_toNNReal g hg]

lemma hasLaw_of {P : Measure Ω} {W : Ω → ℝ} {g : ℝ} (hg : 0 < g) (hW : IsGaussMV P W g) :
    HasLaw W (gaussianReal (g.toNNReal : ℝ) g.toNNReal) P where
  aemeasurable := hW.1.aemeasurable
  map_eq := by
    ext s hs
    rw [Measure.map_apply hW.1 hs, hW.2 s hs,
      gaussianReal_apply _ (by simpa using hg) s]
    simp_rw [gaussianPDF, density_eq hg.le]

lemma F_eq_cdf {P : Measure Ω} [IsProbabilityMeasure P] {T : Ω → ℝ} (hT : Measurable T) (t : ℝ) :
    F P T t = cdf (P.map T) t := by
  rw [cdf_eq_real, measureReal_def, Measure.map_apply hT measurableSet_Iic]
  rfl

/-- For variables with values in `(-1, 1)`, comparing the c.d.f.s on `(-1, 1)` is the same as
comparing them on all of `ℝ`. -/
lemma all_of_Ioo {P : Measure Ω} [IsProbabilityMeasure P] {A B : Ω → ℝ}
    (hA : ∀ ω, A ω ∈ Ioo (-1 : ℝ) 1) (hB : ∀ ω, B ω ∈ Ioo (-1 : ℝ) 1)
    (h : Dominates P A B) (t : ℝ) : F P A t ≤ F P B t := by
  by_cases h1 : t ≤ -1
  · have : {ω | A ω ≤ t} = ∅ := by
      ext ω; simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_le]
      linarith [(hA ω).1]
    simp only [F, this, measure_empty, ENNReal.toReal_zero]
    exact ENNReal.toReal_nonneg
  by_cases h2 : 1 ≤ t
  · have : {ω | B ω ≤ t} = univ := by
      ext ω; simp only [mem_ofPred_eq, mem_univ, iff_true]
      linarith [(hB ω).2]
    simp only [F, this, measure_univ, ENNReal.toReal_one]
    simpa using ENNReal.toReal_mono ENNReal.one_ne_top (prob_le_one (μ := P) (s := {ω | A ω ≤ t}))
  exact h t ⟨by linarith, by linarith⟩

/-! ## The answer -/

/-- **MO 505921.** For independent `X, Y, Z` Gaussian with mean = variance = `gX, gY, gZ > 0`,
`V = tanh Y tanh Z` does not stochastically dominate `U = tanh X`, and `U` does not dominate `V`. -/
theorem answer {P : Measure Ω} [IsProbabilityMeasure P] {gX gY gZ : ℝ}
    (hgX : 0 < gX) (hgY : 0 < gY) (hgZ : 0 < gZ) {X Y Z : Ω → ℝ}
    (hX : IsGaussMV P X gX) (hY : IsGaussMV P Y gY) (hZ : IsGaussMV P Z gZ)
    (hind : Indep3 P X Y Z) :
    ¬ Dominates P (fun ω => tanh (Y ω) * tanh (Z ω)) (fun ω => tanh (X ω)) ∧
      ¬ Dominates P (fun ω => tanh (X ω)) (fun ω => tanh (Y ω) * tanh (Z ω)) := by
  have hYZ : IndepFun Y Z P := by
    rw [indepFun_iff_measure_inter_preimage_eq_mul]
    intro B C hB hC
    have := hind univ B C MeasurableSet.univ hB hC
    simpa only [preimage_univ, univ_inter, measure_univ, one_mul] using this
  have main := TanhDominance.mo505921 (gX := gX.toNNReal) (gY := gY.toNNReal) (gZ := gZ.toNNReal)
    (by simpa using hgX) (by simpa using hgY) (by simpa using hgZ)
    (hasLaw_of hgX hX) (hasLaw_of hgY hY) (hasLaw_of hgZ hZ) hYZ
  have mU : Measurable fun ω => tanh (X ω) := TanhDominance.measurable_tanh.comp hX.1
  have mV : Measurable fun ω => tanh (Y ω) * tanh (Z ω) :=
    (TanhDominance.measurable_tanh.comp hY.1).mul (TanhDominance.measurable_tanh.comp hZ.1)
  have rU : ∀ ω, tanh (X ω) ∈ Ioo (-1 : ℝ) 1 := fun ω => TanhDominance.tanh_mem _
  have rV : ∀ ω, tanh (Y ω) * tanh (Z ω) ∈ Ioo (-1 : ℝ) 1 := fun ω => TanhDominance.mul_tanh_mem _ _
  constructor
  · intro h
    refine main.1 fun t => ?_
    rw [← F_eq_cdf mV, ← F_eq_cdf mU]
    exact all_of_Ioo rV rU h t
  · intro h
    refine main.2 fun t => ?_
    rw [← F_eq_cdf mV, ← F_eq_cdf mU]
    exact all_of_Ioo rU rV h t

/-! ## The question exactly as asked: "given `g_Y, g_Z > 0`, is there `g_X > 0` ...?"

`answer` says that dominance fails in *every* realization. That would be vacuous if no realization
existed, so we exhibit one (the product space). The same realization is what `question_answer_no` needs:
without it, the inner "for every realization, dominance holds" would be vacuously true, and the
negated existential would be unprovable. `question_answer_no'` states the other reading: no `gX > 0`
gives dominance in *any* realization. -/

/-- A realization: `Ω = ℝ × ℝ × ℝ` with the product of the three Gaussian laws. -/
noncomputable def realization (gX gY gZ : ℝ) : Measure (ℝ × ℝ × ℝ) :=
  (gaussianReal (gX.toNNReal : ℝ) gX.toNNReal).prod
    ((gaussianReal (gY.toNNReal : ℝ) gY.toNNReal).prod (gaussianReal (gZ.toNNReal : ℝ) gZ.toNNReal))

instance (gX gY gZ : ℝ) : IsProbabilityMeasure (realization gX gY gZ) := by
  unfold realization; infer_instance

lemma gauss_density {g : ℝ} (hg : 0 < g) (s : Set ℝ) :
    gaussianReal (g.toNNReal : ℝ) g.toNNReal s = ∫⁻ x in s, ENNReal.ofReal (density g x) := by
  rw [gaussianReal_apply _ (by simpa using hg) s]
  simp_rw [gaussianPDF, density_eq hg.le]

lemma realization_spec {gX gY gZ : ℝ} (hgX : 0 < gX) (hgY : 0 < gY) (hgZ : 0 < gZ) :
    IsGaussMV (realization gX gY gZ) (fun p => p.1) gX ∧
      IsGaussMV (realization gX gY gZ) (fun p => p.2.1) gY ∧
      IsGaussMV (realization gX gY gZ) (fun p => p.2.2) gZ ∧
      Indep3 (realization gX gY gZ) (fun p => p.1) (fun p => p.2.1) (fun p => p.2.2) := by
  have e1 : ∀ s : Set ℝ, (fun p : ℝ × ℝ × ℝ => p.1) ⁻¹' s = s ×ˢ (univ ×ˢ univ) := by
    intro s; ext p; simp
  have e2 : ∀ s : Set ℝ, (fun p : ℝ × ℝ × ℝ => p.2.1) ⁻¹' s = univ ×ˢ (s ×ˢ univ) := by
    intro s; ext p; simp
  have e3 : ∀ s : Set ℝ, (fun p : ℝ × ℝ × ℝ => p.2.2) ⁻¹' s = univ ×ˢ (univ ×ˢ s) := by
    intro s; ext p; simp
  refine ⟨⟨measurable_fst, fun s _ => ?_⟩, ⟨measurable_snd.fst, fun s _ => ?_⟩,
    ⟨measurable_snd.snd, fun s _ => ?_⟩, fun A B C _ _ _ => ?_⟩
  · rw [e1, realization, Measure.prod_prod, Measure.prod_prod, measure_univ, measure_univ,
      mul_one, mul_one, gauss_density hgX]
  · rw [e2, realization, Measure.prod_prod, Measure.prod_prod, measure_univ, measure_univ,
      mul_one, one_mul, gauss_density hgY]
  · rw [e3, realization, Measure.prod_prod, Measure.prod_prod, measure_univ, measure_univ,
      one_mul, one_mul, gauss_density hgZ]
  · have e : (fun p : ℝ × ℝ × ℝ => p.1) ⁻¹' A ∩ (fun p : ℝ × ℝ × ℝ => p.2.1) ⁻¹' B ∩
        (fun p : ℝ × ℝ × ℝ => p.2.2) ⁻¹' C = A ×ˢ (B ×ˢ C) := by
      ext p; simp [and_assoc]
    rw [e, e1, e2, e3]
    simp only [realization, Measure.prod_prod, measure_univ, mul_one, one_mul]
    ring

/-- **The question as asked has a negative answer:** given `gY, gZ > 0`, there is no `gX > 0`
such that `tanh Y tanh Z ⪰_st tanh X` for independent `X, Y, Z` with mean = variance
`gX, gY, gZ`. (The same holds with the dominance reversed.) -/
theorem question_answer_no (gY gZ : ℝ) (hgY : 0 < gY) (hgZ : 0 < gZ) :
    ¬ ∃ gX : ℝ, 0 < gX ∧
      ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (X Y Z : Ω → ℝ),
        IsGaussMV P X gX → IsGaussMV P Y gY → IsGaussMV P Z gZ → Indep3 P X Y Z →
        Dominates P (fun ω => tanh (Y ω) * tanh (Z ω)) (fun ω => tanh (X ω)) := by
  rintro ⟨gX, hgX, h⟩
  obtain ⟨hX, hY, hZ, hind⟩ := realization_spec hgX hgY hgZ
  exact (answer hgX hgY hgZ hX hY hZ hind).1
    (h (ℝ × ℝ × ℝ) (realization gX gY gZ) _ _ _ hX hY hZ hind)

/-- The question with "some realization" in place of "every realization": no `gX > 0` gives
`tanh Y tanh Z ⪰_st tanh X` for any independent `X, Y, Z` with mean = variance `gX, gY, gZ`. -/
theorem question_answer_no' (gY gZ : ℝ) (hgY : 0 < gY) (hgZ : 0 < gZ) :
    ¬ ∃ gX : ℝ, 0 < gX ∧
      ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
        (X Y Z : Ω → ℝ),
        IsGaussMV P X gX ∧ IsGaussMV P Y gY ∧ IsGaussMV P Z gZ ∧ Indep3 P X Y Z ∧
        Dominates P (fun ω => tanh (Y ω) * tanh (Z ω)) (fun ω => tanh (X ω)) := by
  rintro ⟨gX, hgX, Ω, _, P, _, X, Y, Z, hX, hY, hZ, hind, hdom⟩
  exact (answer hgX hgY hgZ hX hY hZ hind).1 hdom

end MO505921Check

end
