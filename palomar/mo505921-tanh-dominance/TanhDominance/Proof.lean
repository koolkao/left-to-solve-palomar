/-
Copyright 2026 Ming-Chih Kao. Licensed under the Apache License, Version 2.0;
see the LICENSE file at the root of this repository.
-/
module

public import Mathlib

/-! Port: copied from `MO505921.lean` of github.com/koolkao/mo505921-tanh-dominance (commit
25c3c9124f47df41a312f283451699a36b73a2df, Lean v4.36.0, same Mathlib) and put into the module system:
the `module` header, `public import Mathlib`, a public section, and the namespace `MO505921` renamed
`TanhDominance` so that `Solution.lean` can state the compared theorems under their original names
`MO505921.*`. The mathematics and the proofs are unchanged. -/

@[expose] public section

/-!
# MathOverflow 505921: `tanh Y * tanh Z` and `tanh X` are never stochastically ordered

`X ~ N(gX, gX)`, `Y ~ N(gY, gY)`, `Z ~ N(gZ, gZ)` (mean = variance > 0), `Y, Z` independent.
Neither `F_{tanh X} ≥ F_{tanh Y tanh Z}` nor the reverse holds pointwise, for any parameters.

We work in the "half-LLR" domain: a measure `μ` on `ℝ` is *consistent* if
`∫⁻ f(-x) dμ = ∫⁻ e^{-2x} f(x) dμ` for every measurable `f ≥ 0`.

* `consistent_gaussianReal`: `N(g, g)` is consistent (Lemma 2).
* `consistent_checkNode`: `(μ₁ ⊗ μ₂).map (artanh (tanh y * tanh z))` is consistent (Lemma 3).
* `eq_of_consistent_of_cdf_le`: consistent laws ordered by their CDFs are equal (Lemma 4).
* `lawU_ne_lawV`: the two laws differ near `0` (small-ball, Lemma 5).
* `mo505921`, `mo505921_iIndep`, `no_gX`: the answer, stated with `HasLaw`, `IndepFun`, `cdf`.
-/
open MeasureTheory ProbabilityTheory Set Real
open scoped ENNReal NNReal

namespace TanhDominance

/-- Consistency (symmetry) of a law on the half-LLR line. -/
def Consistent (μ : Measure ℝ) : Prop :=
  ∀ f : ℝ → ℝ≥0∞, Measurable f →
    ∫⁻ x, f (-x) ∂μ = ∫⁻ x, ENNReal.ofReal (rexp (-2 * x)) * f x ∂μ

lemma gaussianPDFReal_neg (g : ℝ≥0) (hg : g ≠ 0) (x : ℝ) :
    gaussianPDFReal g g (-x) = rexp (-2 * x) * gaussianPDFReal g g x := by
  have hg' : (g : ℝ) ≠ 0 := by exact_mod_cast hg
  simp only [gaussianPDFReal]
  rw [mul_left_comm, ← Real.exp_add]
  congr 2
  field_simp
  ring

/-- `N(g, g)` is consistent. -/
theorem consistent_gaussianReal (g : ℝ≥0) (hg : g ≠ 0) : Consistent (gaussianReal g g) := by
  intro f hf
  have hm1 := lintegral_withDensity_eq_lintegral_mul volume (measurable_gaussianPDF (g : ℝ) g)
    (hf.comp measurable_neg)
  have hmeas2 : Measurable fun x : ℝ => ENNReal.ofReal (rexp (-2 * x)) * f x := by fun_prop
  have hm2 := lintegral_withDensity_eq_lintegral_mul volume (measurable_gaussianPDF (g : ℝ) g) hmeas2
  simp only [Function.comp_def] at hm1 hm2
  rw [gaussianReal_of_var_ne_zero _ hg, hm1, hm2]
  -- change variables x ↦ -x on Lebesgue measure
  have hneg : ∫⁻ x, (gaussianPDF g g * fun x => f (-x)) x =
      ∫⁻ x, (gaussianPDF g g * fun x => f (-x)) (-x) := by
    conv_lhs => rw [← Measure.map_neg_eq_self (volume : Measure ℝ)]
    exact lintegral_map_equiv _ (MeasurableEquiv.neg ℝ)
  rw [hneg]
  congr 1
  funext x
  simp only [Pi.mul_apply, neg_neg, gaussianPDF, gaussianPDFReal_neg g hg x]
  rw [ENNReal.ofReal_mul (Real.exp_pos _).le]
  ring

/-- Left-open lower tails are ordered too. -/
lemma Iio_le_of_Iic_le {μ ν : Measure ℝ} (h : ∀ x, ν (Iic x) ≤ μ (Iic x)) (a : ℝ) :
    ν (Iio a) ≤ μ (Iio a) := by
  have hU : Iio a = ⋃ n : ℕ, Iic (a - 1 / ((n : ℝ) + 1)) := by
    ext x
    simp only [mem_Iio, mem_iUnion, mem_Iic]
    constructor
    · intro hx
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.2 hx)
      exact ⟨n, by linarith⟩
    · rintro ⟨n, hn⟩
      have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      linarith
  have hmono : Monotone fun n : ℕ => Iic (a - 1 / ((n : ℝ) + 1)) := by
    intro m n hmn
    apply Iic_subset_Iic.2
    have : (m : ℝ) + 1 ≤ (n : ℝ) + 1 := by exact_mod_cast Nat.succ_le_succ hmn
    have h1 : 1 / ((n : ℝ) + 1) ≤ 1 / ((m : ℝ) + 1) :=
      one_div_le_one_div_of_le (by positivity) this
    linarith
  rw [hU, hmono.measure_iUnion]
  refine iSup_le fun n => (h _).trans (measure_mono ?_)
  exact subset_iUnion (fun n : ℕ => Iic (a - 1 / ((n : ℝ) + 1))) n

/-- The tail `P(X ≥ a)` of a consistent law as an integral of a nonincreasing function. -/
lemma Ici_eq_lintegral {μ : Measure ℝ} (hμ : Consistent μ) (a : ℝ) :
    μ (Ici a) = ∫⁻ x, ENNReal.ofReal ((Iic (-a)).indicator (fun x => rexp (-2 * x)) x) ∂μ := by
  have h1 := hμ ((Iic (-a)).indicator 1) (measurable_one.indicator measurableSet_Iic)
  have h2 : (fun x => (Iic (-a)).indicator (1 : ℝ → ℝ≥0∞) (-x)) = (Ici a).indicator 1 := by
    funext x
    by_cases hx : a ≤ x <;> simp [indicator, hx]
  rw [h2, lintegral_indicator_one measurableSet_Ici] at h1
  rw [h1]
  congr 1
  funext x
  by_cases hx : x ≤ -a <;> simp [indicator, hx]

lemma superlevel (a t : ℝ) (ht : 0 < t) :
    {x : ℝ | t ≤ (Iic (-a)).indicator (fun x => rexp (-2 * x)) x} = Iic (min (-a) (-(log t) / 2)) := by
  ext x
  simp only [mem_ofPred_eq, mem_Iic, le_min_iff, indicator]
  by_cases hx : x ≤ -a
  · simp only [hx, ite_true, true_and]
    rw [← Real.log_le_iff_le_exp ht]
    constructor <;> intro h <;> linarith
  · simp only [hx, ite_false, false_and, iff_false, not_le]
    exact ht

/-- **Rigidity.** Two consistent probability laws that are ordered in the usual stochastic order
(`F_ν ≤ F_μ` pointwise) are equal. -/
theorem eq_of_consistent_of_cdf_le {μ ν : Measure ℝ} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (hμ : Consistent μ) (hν : Consistent ν)
    (h : ∀ x, ν (Iic x) ≤ μ (Iic x)) : μ = ν := by
  refine Measure.ext_of_Ici μ ν fun a => le_antisymm ?_ ?_
  · -- `μ (Ici a) ≤ ν (Ici a)` from the order of the lower tails
    rw [← compl_Iio, prob_compl_eq_one_sub measurableSet_Iio,
      prob_compl_eq_one_sub measurableSet_Iio]
    exact tsub_le_tsub_left (Iio_le_of_Iic_le h a) 1
  · -- `ν (Ici a) ≤ μ (Ici a)` through the consistency identity and the layer-cake formula
    have hmeas : Measurable fun x : ℝ => (Iic (-a)).indicator (fun x => rexp (-2 * x)) x :=
      ((measurable_const.mul measurable_id).exp).indicator measurableSet_Iic
    have hnn : ∀ x : ℝ, 0 ≤ (Iic (-a)).indicator (fun x => rexp (-2 * x)) x :=
      fun x => indicator_nonneg (fun _ _ => (Real.exp_pos _).le) x
    rw [Ici_eq_lintegral hν, Ici_eq_lintegral hμ,
      lintegral_eq_lintegral_meas_le ν (ae_of_all _ hnn) hmeas.aemeasurable,
      lintegral_eq_lintegral_meas_le μ (ae_of_all _ hnn) hmeas.aemeasurable]
    refine setLIntegral_mono' measurableSet_Ioi fun t ht => ?_
    rw [superlevel a t ht]
    exact h _

/-! ## Facts about `tanh` and `artanh` -/

@[fun_prop] lemma measurable_tanh : Measurable tanh := by
  have : tanh = fun x => sinh x / cosh x := funext tanh_eq_sinh_div_cosh
  rw [this]; exact measurable_sinh.div measurable_cosh

@[fun_prop] lemma measurable_artanh : Measurable artanh :=
  Real.measurable_log.comp (Real.continuous_sqrt.measurable.comp
    ((measurable_const.add measurable_id).div (measurable_const.sub measurable_id)))

lemma mul_tanh_mem (x y : ℝ) : tanh x * tanh y ∈ Ioo (-1 : ℝ) 1 := by
  rw [mem_Ioo, ← abs_lt, abs_mul]
  calc |tanh x| * |tanh y| ≤ |tanh x| * 1 :=
        mul_le_mul_of_nonneg_left (abs_tanh_lt_one y).le (abs_nonneg _)
    _ < 1 := by rw [mul_one]; exact abs_tanh_lt_one x

lemma exp_neg_two_mul_one_add_tanh (x : ℝ) : rexp (-2 * x) * (1 + tanh x) = 1 - tanh x := by
  have hab : rexp x * rexp (-x) = 1 := by rw [← exp_add]; simp
  have hb2 : rexp (-2 * x) = rexp (-x) * rexp (-x) := by rw [← exp_add]; ring_nf
  have hpos : 0 < rexp x + rexp (-x) := by positivity
  rw [tanh_eq, hb2]
  field_simp
  linear_combination (2 * rexp (-x)) * hab

lemma artanh_neg' (t : ℝ) : artanh (-t) = -artanh t := by
  rw [artanh, artanh, ← Real.log_inv, ← Real.sqrt_inv, inv_div, sub_neg_eq_add, ← sub_eq_add_neg]

lemma exp_neg_two_artanh {t : ℝ} (ht : t ∈ Ioo (-1 : ℝ) 1) :
    rexp (-2 * artanh t) = (1 - t) / (1 + t) := by
  have h1 : 0 < 1 + t := by linarith [ht.1]
  have h2 : 0 < 1 - t := by linarith [ht.2]
  rw [show -2 * artanh t = -(artanh t + artanh t) by ring, exp_neg, exp_add, exp_artanh ht,
    Real.mul_self_sqrt (div_pos h1 h2).le, inv_div]

/-! ## The check-node (product) lemma -/

lemma Consistent.flip {μ : Measure ℝ} (hμ : Consistent μ) (h : ℝ → ℝ≥0∞) (hh : Measurable h) :
    ∫⁻ x, ENNReal.ofReal (1 - tanh x) * h (-x) ∂μ = ∫⁻ x, ENNReal.ofReal (1 - tanh x) * h x ∂μ := by
  have key := hμ (fun x => ENNReal.ofReal (1 + tanh x) * h x) (by fun_prop)
  simp only [tanh_neg, ← sub_eq_add_neg] at key
  rw [key]
  refine lintegral_congr fun x => ?_
  rw [← mul_assoc, ← ENNReal.ofReal_mul (exp_pos _).le, exp_neg_two_mul_one_add_tanh]

lemma split_weight (a b : ℝ) (c : ℝ≥0∞) :
    ENNReal.ofReal (2 * (1 - tanh a * tanh b)) * c =
      ENNReal.ofReal (1 - tanh a) * (ENNReal.ofReal (1 + tanh b) * c) +
      ENNReal.ofReal (1 - tanh b) * (ENNReal.ofReal (1 + tanh a) * c) := by
  have ha1 : 0 ≤ 1 - tanh a := by linarith [tanh_lt_one a]
  have hb1 : 0 ≤ 1 - tanh b := by linarith [tanh_lt_one b]
  have ha2 : 0 ≤ 1 + tanh a := by linarith [neg_one_lt_tanh a]
  have hb2 : 0 ≤ 1 + tanh b := by linarith [neg_one_lt_tanh b]
  rw [← mul_assoc, ← mul_assoc, ← ENNReal.ofReal_mul ha1, ← ENNReal.ofReal_mul hb1, ← add_mul,
    ← ENNReal.ofReal_add (mul_nonneg ha1 hb2) (mul_nonneg hb1 ha2)]
  congr 2
  ring

theorem prod_identity {μ₁ μ₂ : Measure ℝ} [SFinite μ₁] [SFinite μ₂] (h₁ : Consistent μ₁)
    (h₂ : Consistent μ₂) (f : ℝ → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ p, ENNReal.ofReal (2 * (1 - tanh p.1 * tanh p.2)) * f (-(tanh p.1 * tanh p.2))
        ∂(μ₁.prod μ₂) =
      ∫⁻ p, ENNReal.ofReal (2 * (1 - tanh p.1 * tanh p.2)) * f (tanh p.1 * tanh p.2)
        ∂(μ₁.prod μ₂) := by
  simp only [split_weight]
  rw [lintegral_add_left (by fun_prop), lintegral_add_left (by fun_prop)]
  congr 1
  · rw [lintegral_prod_symm' _ (by fun_prop), lintegral_prod_symm' _ (by fun_prop)]
    refine lintegral_congr fun b => ?_
    have := h₁.flip (fun a => ENNReal.ofReal (1 + tanh b) * f (tanh a * tanh b)) (by fun_prop)
    simp only [tanh_neg, neg_mul] at this
    exact this
  · rw [lintegral_prod _ (by fun_prop), lintegral_prod _ (by fun_prop)]
    refine lintegral_congr fun a => ?_
    have := h₂.flip (fun b => ENNReal.ofReal (1 + tanh a) * f (tanh a * tanh b)) (by fun_prop)
    simp only [tanh_neg, mul_neg] at this
    exact this

/-- The check-node map on the half-LLR line: `artanh (tanh y * tanh z)`. -/
noncomputable def checkNode (p : ℝ × ℝ) : ℝ := artanh (tanh p.1 * tanh p.2)

@[fun_prop] lemma measurable_checkNode : Measurable checkNode := by
  unfold checkNode; fun_prop

/-- **Product lemma.** The check-node combination of two independent consistent laws is
consistent. -/
theorem consistent_checkNode {μ₁ μ₂ : Measure ℝ} [SFinite μ₁] [SFinite μ₂] (h₁ : Consistent μ₁)
    (h₂ : Consistent μ₂) : Consistent ((μ₁.prod μ₂).map checkNode) := by
  intro g hg
  rw [lintegral_map (by fun_prop : Measurable fun x => g (-x)) measurable_checkNode,
    lintegral_map (by fun_prop) measurable_checkNode]
  have key := prod_identity h₁ h₂ (fun t => ENNReal.ofReal ((2 * (1 + t))⁻¹) * g (artanh t))
    (by fun_prop)
  calc ∫⁻ p, g (-checkNode p) ∂(μ₁.prod μ₂)
      = ∫⁻ p, ENNReal.ofReal (2 * (1 - tanh p.1 * tanh p.2)) *
          (ENNReal.ofReal ((2 * (1 + -(tanh p.1 * tanh p.2)))⁻¹) *
            g (artanh (-(tanh p.1 * tanh p.2)))) ∂(μ₁.prod μ₂) := by
        refine lintegral_congr fun p => ?_
        have ht := mul_tanh_mem p.1 p.2
        have h2 : 0 < 2 * (1 - tanh p.1 * tanh p.2) := by linarith [ht.2]
        rw [← sub_eq_add_neg, ← mul_assoc, ← ENNReal.ofReal_mul h2.le, mul_inv_cancel₀ h2.ne',
          ENNReal.ofReal_one, one_mul, artanh_neg', checkNode]
    _ = ∫⁻ p, ENNReal.ofReal (2 * (1 - tanh p.1 * tanh p.2)) *
          (ENNReal.ofReal ((2 * (1 + tanh p.1 * tanh p.2))⁻¹) *
            g (artanh (tanh p.1 * tanh p.2))) ∂(μ₁.prod μ₂) := key
    _ = ∫⁻ p, ENNReal.ofReal (rexp (-2 * checkNode p)) * g (checkNode p) ∂(μ₁.prod μ₂) := by
        refine lintegral_congr fun p => ?_
        have ht := mul_tanh_mem p.1 p.2
        have h1 : 0 < 1 + tanh p.1 * tanh p.2 := by linarith [ht.1]
        have h2 : 0 < 2 * (1 - tanh p.1 * tanh p.2) := by linarith [ht.2]
        rw [← mul_assoc, ← ENNReal.ofReal_mul h2.le, checkNode, exp_neg_two_artanh ht]
        congr 2
        field_simp

/-! ## Monotonicity of `tanh`; rigidity in the `tanh` coordinate -/

lemma tanh_mem (x : ℝ) : tanh x ∈ Ioo (-1 : ℝ) 1 := ⟨neg_one_lt_tanh x, tanh_lt_one x⟩

lemma tanh_le_tanh_iff' {a b : ℝ} : tanh a ≤ tanh b ↔ a ≤ b := by
  rw [← artanh_le_artanh_iff (tanh_mem a) (tanh_mem b), artanh_tanh, artanh_tanh]

lemma map_tanh_Iic (ρ : Measure ℝ) (x : ℝ) : ρ.map tanh (Iic (tanh x)) = ρ (Iic x) := by
  rw [Measure.map_apply measurable_tanh measurableSet_Iic]
  congr 1
  ext y
  simp [tanh_le_tanh_iff']

/-- Rigidity, transported to the `tanh` coordinate. -/
theorem map_tanh_eq_of_le {μ ν : Measure ℝ} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : Consistent μ) (hν : Consistent ν)
    (h : ∀ t, ν.map tanh (Iic t) ≤ μ.map tanh (Iic t)) : μ.map tanh = ν.map tanh := by
  have := eq_of_consistent_of_cdf_le hμ hν fun x => by
    simpa only [map_tanh_Iic] using h (tanh x)
  rw [this]

/-! ## The two laws -/

/-- Law of `U = tanh X` for `X ~ N(g, g)`. -/
noncomputable def lawU (g : ℝ≥0) : Measure ℝ := (gaussianReal g g).map tanh

/-- Law of `V = tanh Y * tanh Z` for independent `Y ~ N(g₁, g₁)`, `Z ~ N(g₂, g₂)`
(multiplicative convolution of the two `tanh`-laws). -/
noncomputable def lawV (g₁ g₂ : ℝ≥0) : Measure ℝ :=
  (gaussianReal g₁ g₁).map tanh ∗ₘ (gaussianReal g₂ g₂).map tanh

lemma lawV_eq (g₁ g₂ : ℝ≥0) : lawV g₁ g₂ =
    ((gaussianReal g₁ g₁).prod (gaussianReal g₂ g₂)).map (fun p => tanh p.1 * tanh p.2) := by
  rw [lawV, Measure.mconv, Measure.map_prod_map _ _ measurable_tanh measurable_tanh,
    Measure.map_map (by fun_prop) (by fun_prop)]
  rfl

lemma lawV_eq_map_checkNode (g₁ g₂ : ℝ≥0) : lawV g₁ g₂ =
    (((gaussianReal g₁ g₁).prod (gaussianReal g₂ g₂)).map checkNode).map tanh := by
  rw [lawV_eq, Measure.map_map measurable_tanh measurable_checkNode]
  congr 1
  funext p
  exact (tanh_artanh (mul_tanh_mem p.1 p.2)).symm

instance (g : ℝ≥0) : IsProbabilityMeasure (lawU g) := by
  unfold lawU; infer_instance

instance (g₁ g₂ : ℝ≥0) : IsProbabilityMeasure (lawV g₁ g₂) := by
  rw [lawV_eq]; infer_instance

/-- Either stochastic ordering forces the two laws to agree (Lemmas 2–4). -/
theorem lawU_eq_lawV_of_le {gX gY gZ : ℝ≥0} (hX : gX ≠ 0) (hY : gY ≠ 0) (hZ : gZ ≠ 0)
    (h : (∀ t, lawV gY gZ (Iic t) ≤ lawU gX (Iic t)) ∨
      (∀ t, lawU gX (Iic t) ≤ lawV gY gZ (Iic t))) :
    lawU gX = lawV gY gZ := by
  have hc := consistent_checkNode (consistent_gaussianReal gY hY) (consistent_gaussianReal gZ hZ)
  have hg := consistent_gaussianReal gX hX
  rw [lawV_eq_map_checkNode, lawU] at h ⊢
  rcases h with h | h
  · exact map_tanh_eq_of_le hg hc h
  · exact (map_tanh_eq_of_le hc hg h).symm

/-! ## Small balls: the two laws differ near `0` (Lemma 5) -/

lemma artanh_le_two_mul {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 1 / 2) : artanh ε ≤ 2 * ε := by
  have hpos : 0 < 1 - ε := by linarith
  rw [artanh_eq_half_log ⟨by linarith, by linarith⟩]
  have hq : 0 < (1 + ε) / (1 - ε) := div_pos (by linarith) hpos
  have hl := Real.log_le_sub_one_of_pos hq
  have : (1 + ε) / (1 - ε) - 1 ≤ 4 * ε := by
    rw [div_sub_one hpos.ne', div_le_iff₀ hpos]; nlinarith
  linarith

lemma abs_le_of_abs_tanh_le {x ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 1 / 2) (h : |tanh x| ≤ ε) :
    |x| ≤ 2 * ε := by
  have hε : ε ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith, by linarith⟩
  have hup : x ≤ artanh ε := by
    rw [← tanh_le_tanh_iff', tanh_artanh hε]; exact (le_abs_self _).trans h
  have hlo : -artanh ε ≤ x := by
    rw [← artanh_neg', ← tanh_le_tanh_iff', tanh_artanh ⟨by linarith, by linarith⟩]
    exact neg_le_of_abs_le h
  have := artanh_le_two_mul h0 h1
  rw [abs_le]; constructor <;> linarith

lemma self_le_artanh {y : ℝ} (h0 : 0 ≤ y) (h1 : y < 1) : y ≤ artanh y := by
  have habs : |y| < 1 := by rw [abs_of_nonneg h0]; exact h1
  have hs := hasSum_log_sub_log_of_abs_lt_one habs
  have h2 : 2 * y ≤ log (1 + y) - log (1 - y) := by
    have := le_hasSum hs 0 (fun j _ => mul_nonneg (by positivity) (pow_nonneg h0 _))
    simpa using this
  rw [artanh_eq_half_log ⟨by linarith, h1.le⟩, log_div (by linarith) (by linarith)]
  linarith

lemma tanh_le_self' {y : ℝ} (h0 : 0 ≤ y) : tanh y ≤ y := by
  rcases lt_or_ge y 1 with h1 | h1
  · have := self_le_artanh h0 h1
    rw [← tanh_le_tanh_iff', tanh_artanh ⟨by linarith, h1⟩] at this
    exact this
  · exact (tanh_lt_one y).le.trans h1

lemma tanh_nonneg' {y : ℝ} (h0 : 0 ≤ y) : 0 ≤ tanh y := by
  rw [← tanh_zero]; exact tanh_le_tanh_iff'.2 h0

lemma gaussian_le (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0) (s : Set ℝ) :
    gaussianReal m v s ≤ ENNReal.ofReal (√(2 * π * v))⁻¹ * volume s := by
  rw [gaussianReal_apply m hv s, ← setLIntegral_const]
  refine setLIntegral_mono measurable_const fun x _ => ?_
  rw [gaussianPDF]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [gaussianPDFReal]
  refine mul_le_of_le_one_right (by positivity) ?_
  rw [Real.exp_le_one_iff]
  exact div_nonpos_of_nonpos_of_nonneg (by linarith [sq_nonneg (x - m)]) (by positivity)

/-- Lower bound for the Gaussian density on `[-1, 1]`. -/
noncomputable def cLow (m : ℝ) (v : ℝ≥0) : ℝ := (√(2 * π * v))⁻¹ * rexp (-(1 + |m|) ^ 2 / (2 * v))

lemma cLow_pos (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0) : 0 < cLow m v := by
  have : (0 : ℝ) < v := NNReal.coe_pos.2 (pos_iff_ne_zero.2 hv)
  unfold cLow; positivity

lemma le_gaussian (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0) {s : Set ℝ} (hs : s ⊆ Icc (-1) 1) :
    ENNReal.ofReal (cLow m v) * volume s ≤ gaussianReal m v s := by
  rw [gaussianReal_apply m hv s, ← setLIntegral_const]
  refine setLIntegral_mono (measurable_gaussianPDF m v) fun x hx => ?_
  rw [gaussianPDF]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [gaussianPDFReal, cLow]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine Real.exp_le_exp.2 ?_
  have hx' := hs hx
  have h1 : |x - m| ≤ 1 + |m| := by
    calc |x - m| ≤ |x| + |m| := abs_sub _ _
      _ ≤ 1 + |m| := by gcongr; exact abs_le.2 ⟨hx'.1, hx'.2⟩
  have h2 : (x - m) ^ 2 ≤ (1 + |m|) ^ 2 := by
    rw [← sq_abs (x - m)]; exact pow_le_pow_left₀ (abs_nonneg _) h1 2
  have hv' : (0 : ℝ) < 2 * v := by
    have : (0 : ℝ) < v := NNReal.coe_pos.2 (pos_iff_ne_zero.2 hv)
    positivity
  rw [div_le_div_iff_of_pos_right hv']
  linarith

lemma lawU_Icc_le (g : ℝ≥0) (hg : g ≠ 0) {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 1 / 2) :
    lawU g (Icc (-ε) ε) ≤ ENNReal.ofReal ((√(2 * π * g))⁻¹ * (4 * ε)) := by
  rw [lawU, Measure.map_apply measurable_tanh measurableSet_Icc]
  calc gaussianReal g g (tanh ⁻¹' Icc (-ε) ε)
      ≤ gaussianReal g g (Icc (-(2 * ε)) (2 * ε)) := by
        refine measure_mono fun x hx => ?_
        exact abs_le.1 (abs_le_of_abs_tanh_le h0 h1 (abs_le.2 hx))
    _ ≤ ENNReal.ofReal (√(2 * π * g))⁻¹ * volume (Icc (-(2 * ε)) (2 * ε)) := gaussian_le _ hg _
    _ = _ := by
        rw [Real.volume_Icc, ← ENNReal.ofReal_mul (inv_nonneg.2 (Real.sqrt_nonneg _))]
        congr 1; ring

lemma lawV_Icc_ge (g₁ g₂ : ℝ≥0) (h₁ : g₁ ≠ 0) (h₂ : g₂ ≠ 0) (n : ℕ) :
    ENNReal.ofReal (n * (cLow g₁ g₁ * cLow g₂ g₂ * (1 / 2) ^ (n + 1))) ≤
      lawV g₁ g₂ (Icc (-(1 / 2) ^ n) ((1 / 2) ^ n)) := by
  rw [lawV_eq, Measure.map_apply (by fun_prop) measurableSet_Icc]
  set π₂ := (gaussianReal g₁ g₁).prod (gaussianReal g₂ g₂)
  let B : ℕ → Set ℝ := fun k => Ioc ((1 / 2 : ℝ) ^ (k + 1)) ((1 / 2) ^ k)
  let C : ℕ → Set ℝ := fun k => Icc 0 ((1 / 2 : ℝ) ^ (n - k))
  have hc₁ := cLow_pos (g₁ : ℝ) h₁
  have hc₂ := cLow_pos (g₂ : ℝ) h₂
  have hsub : (⋃ k ∈ Finset.range n, B k ×ˢ C k) ⊆
      (fun p : ℝ × ℝ => tanh p.1 * tanh p.2) ⁻¹' Icc (-(1 / 2) ^ n) ((1 / 2) ^ n) := by
    intro p hp
    simp only [mem_iUnion, Finset.mem_range] at hp
    obtain ⟨k, hk, hpk⟩ := hp
    obtain ⟨⟨hy1, hy2⟩, ⟨hz1, hz2⟩⟩ := hpk
    have hy0 : 0 ≤ p.1 := le_trans (by positivity) hy1.le
    have ha0 := tanh_nonneg' hy0
    have hb0 := tanh_nonneg' hz1
    have ha := (tanh_le_self' hy0).trans hy2
    have hb := (tanh_le_self' hz1).trans hz2
    have hprod : tanh p.1 * tanh p.2 ≤ (1 / 2 : ℝ) ^ k * (1 / 2) ^ (n - k) :=
      mul_le_mul ha hb hb0 (by positivity)
    rw [← pow_add, Nat.add_sub_cancel' hk.le] at hprod
    refine ⟨?_, hprod⟩
    have : (0 : ℝ) ≤ (1 / 2) ^ n := by positivity
    have := mul_nonneg ha0 hb0
    linarith
  have hdisj : PairwiseDisjoint (↑(Finset.range n)) (fun k => B k ×ˢ C k) := by
    intro i _ j _ hij
    refine Set.disjoint_prod.2 (Or.inl ?_)
    rw [Set.disjoint_left]
    intro y hyi hyj
    rcases lt_or_gt_of_ne hij with h | h
    · have := pow_le_pow_of_le_one (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num) (Nat.succ_le_of_lt h)
      exact absurd (hyj.2.trans this) (not_le.2 hyi.1)
    · have := pow_le_pow_of_le_one (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num) (Nat.succ_le_of_lt h)
      exact absurd (hyi.2.trans this) (not_le.2 hyj.1)
  have hterm : ∀ k ∈ Finset.range n,
      ENNReal.ofReal (cLow g₁ g₁ * cLow g₂ g₂ * (1 / 2) ^ (n + 1)) ≤ π₂ (B k ×ˢ C k) := by
    intro k hk
    rw [Finset.mem_range] at hk
    have e1 : (1 / 2 : ℝ) ^ k - (1 / 2) ^ (k + 1) = (1 / 2) ^ (k + 1) := by
      rw [pow_succ]; ring
    have hk' : k + 1 + (n - k) = n + 1 := by omega
    have e : cLow g₁ g₁ * cLow g₂ g₂ * (1 / 2) ^ (n + 1) =
        (cLow g₁ g₁ * ((1 / 2) ^ k - (1 / 2) ^ (k + 1))) * (cLow g₂ g₂ * ((1 / 2) ^ (n - k) - 0)) := by
      rw [e1, sub_zero, ← hk', pow_add]; ring
    have hB : B k ⊆ Icc (-1) 1 := fun y hy => ⟨by
        have : (0 : ℝ) < (1 / 2) ^ (k + 1) := by positivity
        linarith [hy.1], hy.2.trans (pow_le_one₀ (by norm_num) (by norm_num))⟩
    have hC : C k ⊆ Icc (-1) 1 := fun z hz => ⟨by linarith [hz.1],
      hz.2.trans (pow_le_one₀ (by norm_num) (by norm_num))⟩
    rw [e, ENNReal.ofReal_mul (mul_nonneg hc₁.le (by rw [e1]; positivity)),
      ENNReal.ofReal_mul hc₁.le, ENNReal.ofReal_mul hc₂.le, Measure.prod_prod,
      ← Real.volume_Ioc, ← Real.volume_Icc]
    exact mul_le_mul' (le_gaussian _ h₁ hB) (le_gaussian _ h₂ hC)
  calc ENNReal.ofReal (n * (cLow g₁ g₁ * cLow g₂ g₂ * (1 / 2) ^ (n + 1)))
      = ∑ k ∈ Finset.range n, ENNReal.ofReal (cLow g₁ g₁ * cLow g₂ g₂ * (1 / 2) ^ (n + 1)) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul,
          ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
    _ ≤ ∑ k ∈ Finset.range n, π₂ (B k ×ˢ C k) := Finset.sum_le_sum hterm
    _ = π₂ (⋃ k ∈ Finset.range n, B k ×ˢ C k) :=
        (measure_biUnion_finset hdisj fun k _ => measurableSet_Ioc.prod measurableSet_Icc).symm
    _ ≤ _ := measure_mono hsub

/-- **Lemma 5.** `tanh X` and `tanh Y * tanh Z` never have the same law. -/
theorem lawU_ne_lawV {gX gY gZ : ℝ≥0} (hX : gX ≠ 0) (hY : gY ≠ 0) (hZ : gZ ≠ 0) :
    lawU gX ≠ lawV gY gZ := by
  intro heq
  set M := (√(2 * π * gX))⁻¹
  set c := cLow gY gY * cLow gZ gZ
  have hc : 0 < c := mul_pos (cLow_pos _ hY) (cLow_pos _ hZ)
  have hM0 : 0 ≤ M := inv_nonneg.2 (Real.sqrt_nonneg _)
  obtain ⟨n, hn⟩ := exists_nat_gt (8 * M / c)
  have hn1 : 1 ≤ n := by
    have : 0 ≤ 8 * M / c := by positivity
    have : (0 : ℝ) < n := by linarith
    exact_mod_cast this
  have hε0 : (0 : ℝ) ≤ (1 / 2) ^ n := by positivity
  have hε1 : (1 / 2 : ℝ) ^ n ≤ 1 / 2 := by
    calc (1 / 2 : ℝ) ^ n ≤ (1 / 2) ^ 1 := pow_le_pow_of_le_one (by norm_num) (by norm_num) hn1
      _ = 1 / 2 := pow_one _
  have hlow := lawV_Icc_ge gY gZ hY hZ n
  have hup := lawU_Icc_le gX hX hε0 hε1
  rw [heq] at hup
  have key := hlow.trans hup
  rw [ENNReal.ofReal_le_ofReal_iff (by positivity)] at key
  have hpow : (0 : ℝ) < (1 / 2) ^ n := by positivity
  have e : (1 / 2 : ℝ) ^ (n + 1) = (1 / 2) ^ n / 2 := by rw [pow_succ]; ring
  rw [e] at key
  have h8 : (n : ℝ) * c ≤ 8 * M := by nlinarith
  rw [div_lt_iff₀ hc] at hn
  linarith

/-! ## Main theorems -/

/-- **MO 505921, measure form.** For all `gX, gY, gZ > 0`, neither `tanh Y * tanh Z ⪰_st tanh X`
(`F_U ≥ F_V`) nor `tanh X ⪰_st tanh Y * tanh Z` (`F_V ≥ F_U`). -/
theorem not_stochastic_order {gX gY gZ : ℝ≥0} (hX : gX ≠ 0) (hY : gY ≠ 0) (hZ : gZ ≠ 0) :
    (¬ ∀ t, cdf (lawV gY gZ) t ≤ cdf (lawU gX) t) ∧
      (¬ ∀ t, cdf (lawU gX) t ≤ cdf (lawV gY gZ) t) := by
  refine ⟨fun h => lawU_ne_lawV hX hY hZ (lawU_eq_lawV_of_le hX hY hZ (Or.inl fun t => ?_)),
    fun h => lawU_ne_lawV hX hY hZ (lawU_eq_lawV_of_le hX hY hZ (Or.inr fun t => ?_))⟩ <;>
  · rw [← ofReal_cdf, ← ofReal_cdf]; exact ENNReal.ofReal_le_ofReal (h t)

/-- **MO 505921, random-variable form.** Let `X, Y, Z` be real random variables with
`X ~ N(gX, gX)`, `Y ~ N(gY, gY)`, `Z ~ N(gZ, gZ)` (mean = variance > 0), `Y` and `Z` independent.
Then `V = tanh Y * tanh Z` does not stochastically dominate `U = tanh X` (i.e. `F_U ≥ F_V` fails at
some point), and `U` does not dominate `V` either. Hence no `gX` answers the question. -/
theorem mo505921 {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {gX gY gZ : ℝ≥0} (hgX : gX ≠ 0) (hgY : gY ≠ 0) (hgZ : gZ ≠ 0) {X Y Z : Ω → ℝ}
    (hX : HasLaw X (gaussianReal gX gX) P) (hY : HasLaw Y (gaussianReal gY gY) P)
    (hZ : HasLaw Z (gaussianReal gZ gZ) P) (hYZ : IndepFun Y Z P) :
    (¬ ∀ t, cdf (P.map fun ω => tanh (Y ω) * tanh (Z ω)) t ≤ cdf (P.map fun ω => tanh (X ω)) t) ∧
      (¬ ∀ t, cdf (P.map fun ω => tanh (X ω)) t ≤
        cdf (P.map fun ω => tanh (Y ω) * tanh (Z ω)) t) := by
  have hU : P.map (fun ω => tanh (X ω)) = lawU gX := ((hasLaw_map measurable_tanh.aemeasurable).comp hX).map_eq
  have hY' : HasLaw (fun ω => tanh (Y ω)) ((gaussianReal gY gY).map tanh) P :=
    (hasLaw_map measurable_tanh.aemeasurable).comp hY
  have hZ' : HasLaw (fun ω => tanh (Z ω)) ((gaussianReal gZ gZ).map tanh) P :=
    (hasLaw_map measurable_tanh.aemeasurable).comp hZ
  have hind : IndepFun (fun ω => tanh (Y ω)) (fun ω => tanh (Z ω)) P :=
    hYZ.comp measurable_tanh measurable_tanh
  have hV : P.map (fun ω => tanh (Y ω) * tanh (Z ω)) = lawV gY gZ :=
    (hind.hasLaw_fun_mul hY' hZ').map_eq
  rw [hU, hV]
  exact not_stochastic_order hgX hgY hgZ

/-- The same with the three variables jointly independent, as in the question. -/
theorem mo505921_iIndep {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {gX gY gZ : ℝ≥0} (hgX : gX ≠ 0) (hgY : gY ≠ 0) (hgZ : gZ ≠ 0) {X Y Z : Ω → ℝ}
    (hX : HasLaw X (gaussianReal gX gX) P) (hY : HasLaw Y (gaussianReal gY gY) P)
    (hZ : HasLaw Z (gaussianReal gZ gZ) P) (hXYZ : iIndepFun ![X, Y, Z] P) :
    (¬ ∀ t, cdf (P.map fun ω => tanh (Y ω) * tanh (Z ω)) t ≤ cdf (P.map fun ω => tanh (X ω)) t) ∧
      (¬ ∀ t, cdf (P.map fun ω => tanh (X ω)) t ≤
        cdf (P.map fun ω => tanh (Y ω) * tanh (Z ω)) t) :=
  mo505921 hgX hgY hgZ hX hY hZ (hXYZ.indepFun (i := 1) (j := 2) (by decide))

/-- The question as asked: given `gY, gZ > 0`, there is no `gX > 0` with `F_U ≥ F_V`. -/
theorem no_gX (gY gZ : ℝ≥0) (hY : gY ≠ 0) (hZ : gZ ≠ 0) :
    ¬ ∃ gX : ℝ≥0, gX ≠ 0 ∧ ∀ t, cdf (lawV gY gZ) t ≤ cdf (lawU gX) t :=
  fun ⟨_, hX, h⟩ => (not_stochastic_order hX hY hZ).1 h

end TanhDominance

end
