/-
Copyright (c) 2026 Ming-Chih Kao. Released under the Apache 2.0 license.
-/
module

public import KimberlingCopula.Defs
public import KimberlingCopula.TauCeti

/-!
# Kimberling's copula inequality (MathOverflow 195959): proof

Port: the proof part of `prepared/mo-195959.proof.lean` (the Left to Solve version of
github.com/koolkao/kimberling-copula-inequality, which uses only Bernstein's theorem on `[0, ∞)`
applied to the shifts `f (· + ε)`), put into the module system for Lean v4.36.0 / Mathlib fc4f59e.
Lines up to `isCompletelyMonotone_shift` are `Kimberling/Basic.lean` of that repository
(commit 18d5fd4ab3dedd0645b425f96ddac6d21d18a599), lines 40–318, unchanged; the rest is the shift
and limit argument. By Bernstein's theorem each shift `f (· + ε)` is the Laplace transform of a
finite measure; normalizing it gives a probability measure `ν`, under which `C(u, v) - uv` is a
covariance and `C(a, a) - a²` a variance of exponentials, and a single-crossing argument compares
them. Letting `ε → 0` gives the inequality. Comments marked `Port` explain any change.
-/

@[expose] public section

open MeasureTheory Filter Topology Set
open scoped NNReal

namespace Kimberling


/-- The exponential kernel `x ↦ exp (-(c x))` on `ℝ≥0`. -/
noncomputable def E (c : ℝ) (x : ℝ≥0) : ℝ := Real.exp (-(c * (x : ℝ)))

lemma E_pos (c : ℝ) (x : ℝ≥0) : 0 < E c x := Real.exp_pos _

lemma E_le_one {c : ℝ} (hc : 0 ≤ c) (x : ℝ≥0) : E c x ≤ 1 := by
  unfold E
  rw [Real.exp_le_one_iff]
  have : 0 ≤ c * (x : ℝ) := mul_nonneg hc x.2
  linarith

lemma continuous_E (c : ℝ) : Continuous (E c) := by
  unfold E; fun_prop

lemma E_mul (b c : ℝ) (x : ℝ≥0) : E b x * E c x = E (b + c) x := by
  unfold E; rw [← Real.exp_add]; congr 1; ring

lemma E_zero_right (c : ℝ) : E c 0 = 1 := by simp [E]

lemma E_zero_left (x : ℝ≥0) : E 0 x = 1 := by simp [E]

section Measure

variable {μ : Measure ℝ≥0} [IsProbabilityMeasure μ]

lemma integrable_of_continuous_bdd {φ : ℝ≥0 → ℝ} (hφ : Continuous φ) {C : ℝ}
    (hb : ∀ x, |φ x| ≤ C) : Integrable φ μ :=
  Integrable.mono' (integrable_const C) hφ.aestronglyMeasurable
    (ae_of_all _ fun x => by simpa [Real.norm_eq_abs] using hb x)

lemma integrable_E {c : ℝ} (hc : 0 ≤ c) : Integrable (E c) μ :=
  integrable_of_continuous_bdd (continuous_E c) fun x => by
    rw [abs_of_pos (E_pos c x)]; exact E_le_one hc x

/-- `(∫ φ)² ≤ ∫ φ²` for a bounded continuous `φ` on a probability space. -/
lemma sq_integral_le {φ : ℝ≥0 → ℝ} (hφ : Continuous φ) {C : ℝ} (hb : ∀ x, |φ x| ≤ C) :
    (∫ x, φ x ∂μ) ^ 2 ≤ ∫ x, φ x ^ 2 ∂μ := by
  set m := ∫ x, φ x ∂μ
  have hi : Integrable φ μ := integrable_of_continuous_bdd hφ hb
  have hC : 0 ≤ C := le_trans (abs_nonneg _) (hb 0)
  have hi2 : Integrable (fun x => φ x ^ 2) μ :=
    integrable_of_continuous_bdd (hφ.pow 2) (C := C ^ 2) fun x => by
      rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hb x) 2
  have h0 : 0 ≤ ∫ x, (φ x - m) ^ 2 ∂μ := integral_nonneg fun x => sq_nonneg _
  have hexp : (fun x => (φ x - m) ^ 2) = fun x => (φ x ^ 2 - (2 * m) * φ x) + m ^ 2 := by
    funext x; ring
  rw [hexp] at h0
  have e1 : ∫ x, (φ x ^ 2 - 2 * m * φ x + m ^ 2) ∂μ =
      ∫ x, (φ x ^ 2 - 2 * m * φ x) ∂μ + ∫ _x, m ^ 2 ∂μ :=
    integral_add (hi2.sub (hi.const_mul _)) (integrable_const _)
  have e2 : ∫ x, (φ x ^ 2 - 2 * m * φ x) ∂μ = ∫ x, φ x ^ 2 ∂μ - ∫ x, 2 * m * φ x ∂μ :=
    integral_sub hi2 (hi.const_mul _)
  have e3 : ∫ x, 2 * m * φ x ∂μ = 2 * m * m := by rw [integral_const_mul]
  have e4 : ∫ _x, m ^ 2 ∂μ = m ^ 2 := by simp
  rw [e1, e2, e3, e4] at h0
  nlinarith

end Measure

/-! ## The single-crossing inequality -/

section Crossing

/-- The ratio function `S(x) = exp((r - p) x) + exp(-(s - r) x)`. On `x ≥ 0` the sign of
`h = E r - (E p + E s)/2` is the sign of `2 - S`. -/
lemma h_nonneg_iff {p r s : ℝ} (x : ℝ≥0) :
    0 ≤ E r x - (E p x + E s x) / 2 ↔
      Real.exp ((r - p) * x) + Real.exp (-((s - r) * x)) ≤ 2 := by
  have hp : E p x = E r x * Real.exp ((r - p) * x) := by
    unfold E; rw [← Real.exp_add]; congr 1; ring
  have hs : E s x = E r x * Real.exp (-((s - r) * x)) := by
    unfold E; rw [← Real.exp_add]; congr 1; ring
  rw [hp, hs]
  have hr := E_pos r x
  constructor
  · intro h
    by_contra hc
    rw [not_le] at hc
    nlinarith
  · intro h
    nlinarith

/-- Convexity step: if `S(x) ≤ 2` and `0 ≤ y ≤ x` then `S(y) ≤ 2`, since `S` is convex with
`S(0) = 2`. -/
lemma S_le_two_of_le {a b : ℝ} {x y : ℝ} (hy : 0 ≤ y) (hyx : y ≤ x)
    (hx : Real.exp (a * x) + Real.exp (-(b * x)) ≤ 2) :
    Real.exp (a * y) + Real.exp (-(b * y)) ≤ 2 := by
  rcases eq_or_lt_of_le (hy.trans hyx) with h0 | hxpos
  · have : y = 0 := le_antisymm (h0 ▸ hyx) hy
    subst this; norm_num
  set t := y / x with ht
  have ht0 : 0 ≤ t := div_nonneg hy hxpos.le
  have ht1 : t ≤ 1 := (div_le_one hxpos).2 hyx
  have hyt : y = t * x := by rw [ht]; field_simp
  have key : ∀ c : ℝ, Real.exp (c * y) ≤ t * Real.exp (c * x) + (1 - t) := by
    intro c
    have := convexOn_exp.2 (mem_univ (c * x)) (mem_univ 0) ht0 (by linarith : 0 ≤ 1 - t)
      (by ring : t + (1 - t) = 1)
    simp only [smul_eq_mul, mul_zero, add_zero, Real.exp_zero, mul_one] at this
    calc Real.exp (c * y) = Real.exp (t * (c * x)) := by rw [hyt]; ring_nf
      _ ≤ t * Real.exp (c * x) + (1 - t) := this
  have h1 := key a
  have h2 := key (-b)
  have e1 : -(b * y) = -b * y := by ring
  have e2 : -(b * x) = -b * x := by ring
  rw [e1]; rw [e2] at hx
  nlinarith

variable {μ : Measure ℝ≥0} [IsProbabilityMeasure μ]

/-- **Single crossing.** For exponents `p, r, s ≥ 0` with
`∫ E r = (∫ E p + ∫ E s) / 2`, we get `∫ ((E p + E s)/2)² ≤ ∫ (E r)²`. -/
lemma crossing {p r s : ℝ} (hp : 0 ≤ p) (hr : 0 ≤ r) (hs : 0 ≤ s)
    (hmean : ∫ x, E r x ∂μ = ((∫ x, E p x ∂μ) + ∫ x, E s x ∂μ) / 2) :
    ∫ x, ((E p x + E s x) / 2) ^ 2 ∂μ ≤ ∫ x, (E r x) ^ 2 ∂μ := by
  set h : ℝ≥0 → ℝ := fun x => E r x - (E p x + E s x) / 2 with hh
  set w : ℝ≥0 → ℝ := fun x => E r x + (E p x + E s x) / 2 with hw
  set P : Set ℝ≥0 := {x | 0 ≤ h x} with hP
  -- `P` is a lower set
  have hlow : ∀ x y : ℝ≥0, y ≤ x → x ∈ P → y ∈ P := by
    intro x y hyx hx
    have hx' : 0 ≤ h x := hx
    show 0 ≤ h y
    simp only [hh] at hx' ⊢
    rw [h_nonneg_iff] at hx' ⊢
    exact S_le_two_of_le y.2 (by exact_mod_cast hyx) hx'
  have h0P : (0 : ℝ≥0) ∈ P := by
    simp [hP, hh, E_zero_right]
  -- `w` is antitone
  have hEanti : ∀ {c : ℝ}, 0 ≤ c → ∀ x y : ℝ≥0, y ≤ x → E c x ≤ E c y := by
    intro c hc x y hyx
    unfold E
    apply Real.exp_le_exp.2
    have : c * (y : ℝ) ≤ c * x := mul_le_mul_of_nonneg_left (by exact_mod_cast hyx) hc
    linarith
  have hwanti : ∀ x y : ℝ≥0, y ≤ x → w x ≤ w y := by
    intro x y hyx
    simp only [hw]
    have := hEanti hr x y hyx
    have := hEanti hp x y hyx
    have := hEanti hs x y hyx
    linarith
  have hw0 : ∀ x, 0 ≤ w x := fun x => by
    simp only [hw]
    have := E_pos r x; have := E_pos p x; have := E_pos s x
    positivity
  set κ := sInf (w '' P) with hκ
  have hbdd : BddBelow (w '' P) := ⟨0, by rintro _ ⟨x, -, rfl⟩; exact hw0 x⟩
  have hne : (w '' P).Nonempty := ⟨w 0, 0, h0P, rfl⟩
  have hpt : ∀ x, 0 ≤ h x * (w x - κ) := by
    intro x
    by_cases hx : x ∈ P
    · have : κ ≤ w x := csInf_le hbdd ⟨x, hx, rfl⟩
      exact mul_nonneg hx (by linarith)
    · have hneg : h x < 0 := lt_of_not_ge hx
      have : w x ≤ κ := by
        apply le_csInf hne
        rintro _ ⟨y, hy, rfl⟩
        apply hwanti
        by_contra hxy
        exact hx (hlow y x (le_of_lt (lt_of_not_ge hxy)) hy)
      exact mul_nonneg_of_nonpos_of_nonpos hneg.le (by linarith)
  -- integrability
  have bE : ∀ {c : ℝ}, 0 ≤ c → ∀ x, 0 < E c x ∧ E c x ≤ 1 := fun hc x => ⟨E_pos _ x, E_le_one hc x⟩
  have hκ0 : 0 ≤ κ := le_csInf hne (by rintro _ ⟨x, -, rfl⟩; exact hw0 x)
  have hκ2 : κ ≤ 2 := by
    have := csInf_le hbdd ⟨0, h0P, rfl⟩
    simp only [hw, E_zero_right] at this
    linarith
  have hcont_h : Continuous h := by
    simp only [hh]; have := continuous_E r; have := continuous_E p; have := continuous_E s
    fun_prop
  have hcont_w : Continuous w := by
    simp only [hw]; have := continuous_E r; have := continuous_E p; have := continuous_E s
    fun_prop
  have hih : Integrable h μ :=
    integrable_of_continuous_bdd hcont_h (C := 2) fun x => by
      obtain ⟨a1, a2⟩ := bE hr x; obtain ⟨b1, b2⟩ := bE hp x; obtain ⟨c1, c2⟩ := bE hs x
      simp only [hh]; rw [abs_le]; constructor <;> linarith
  have hihw : Integrable (fun x => h x * (w x - κ)) μ :=
    integrable_of_continuous_bdd (hcont_h.mul (hcont_w.sub continuous_const)) (C := 4)
      fun x => by
        obtain ⟨a1, a2⟩ := bE hr x; obtain ⟨b1, b2⟩ := bE hp x; obtain ⟨c1, c2⟩ := bE hs x
        have hhx : |h x| ≤ 1 := by simp only [hh]; rw [abs_le]; constructor <;> linarith
        have hwx : |w x - κ| ≤ 4 := by simp only [hw]; rw [abs_le]; constructor <;> linarith
        calc |h x * (w x - κ)| = |h x| * |w x - κ| := abs_mul _ _
          _ ≤ 1 * 4 := mul_le_mul hhx hwx (abs_nonneg _) zero_le_one
          _ = 4 := by ring
  have hint_h : ∫ x, h x ∂μ = 0 := by
    have e1 : ∫ x, h x ∂μ = ∫ x, E r x ∂μ - ∫ x, (E p x + E s x) / 2 ∂μ :=
      integral_sub (integrable_E hr) (((integrable_E hp).add (integrable_E hs)).div_const 2)
    have e2 : ∫ x, (E p x + E s x) / 2 ∂μ = ((∫ x, E p x ∂μ) + ∫ x, E s x ∂μ) / 2 := by
      rw [integral_div, integral_add (integrable_E hp) (integrable_E hs)]
    rw [e1, e2, hmean]; ring
  have hmain : 0 ≤ ∫ x, h x * (w x - κ) ∂μ := integral_nonneg hpt
  have hsplit : (fun x => (E r x) ^ 2 - ((E p x + E s x) / 2) ^ 2) =
      fun x => h x * (w x - κ) + κ * h x := by
    funext x; simp only [hh, hw]; ring
  have hsq1 : Integrable (fun x => (E r x) ^ 2) μ :=
    integrable_of_continuous_bdd ((continuous_E r).pow 2) (C := 1) fun x => by
      obtain ⟨a1, a2⟩ := bE hr x
      rw [abs_of_nonneg (by positivity)]; nlinarith
  have hsq2 : Integrable (fun x => ((E p x + E s x) / 2) ^ 2) μ :=
    integrable_of_continuous_bdd
      ((((continuous_E p).add (continuous_E s)).div_const 2).pow 2) (C := 1) fun x => by
      obtain ⟨b1, b2⟩ := bE hp x; obtain ⟨c1, c2⟩ := bE hs x
      rw [abs_of_nonneg (by positivity)]; nlinarith
  have := integral_sub hsq1 hsq2
  rw [hsplit, integral_add hihw (hih.const_mul κ), integral_const_mul, hint_h] at this
  linarith

/-- **Core inequality.** For exponents `p, r, s ≥ 0` with
`∫ E r = (∫ E p + ∫ E s) / 2`:
`∫ E (p + s) - (∫ E p)(∫ E s) ≤ ∫ E (2 r) - (∫ E r)²`. -/
lemma core {p r s : ℝ} (hp : 0 ≤ p) (hr : 0 ≤ r) (hs : 0 ≤ s)
    (hmean : ∫ x, E r x ∂μ = ((∫ x, E p x ∂μ) + ∫ x, E s x ∂μ) / 2) :
    (∫ x, E (p + s) x ∂μ) - (∫ x, E p x ∂μ) * (∫ x, E s x ∂μ) ≤
      (∫ x, E (r + r) x ∂μ) - (∫ x, E r x ∂μ) ^ 2 := by
  have hc := crossing hp hr hs hmean (μ := μ)
  set A := ∫ x, E p x ∂μ
  set B := ∫ x, E s x ∂μ
  -- variance of the difference
  have hd : (∫ x, (E p x - E s x) / 2 ∂μ) ^ 2 ≤ ∫ x, ((E p x - E s x) / 2) ^ 2 ∂μ :=
    sq_integral_le (((continuous_E p).sub (continuous_E s)).div_const 2) (C := 1) fun x => by
      have := E_pos p x; have := E_le_one hp x; have := E_pos s x; have := E_le_one hs x
      rw [abs_le]; constructor <;> linarith
  have hdint : ∫ x, (E p x - E s x) / 2 ∂μ = (A - B) / 2 := by
    rw [integral_div, integral_sub (integrable_E hp) (integrable_E hs)]
  rw [hdint] at hd
  -- pointwise identities
  have hps : (fun x => E (p + s) x) =
      fun x => ((E p x + E s x) / 2) ^ 2 - ((E p x - E s x) / 2) ^ 2 := by
    funext x; rw [← E_mul]; ring
  have hrr : (fun x => E (r + r) x) = fun x => (E r x) ^ 2 := by
    funext x; rw [← E_mul]; ring
  have bE : ∀ {c : ℝ}, 0 ≤ c → ∀ x, 0 < E c x ∧ E c x ≤ 1 := fun hc x => ⟨E_pos _ x, E_le_one hc x⟩
  have hi1 : Integrable (fun x => ((E p x + E s x) / 2) ^ 2) μ :=
    integrable_of_continuous_bdd
      ((((continuous_E p).add (continuous_E s)).div_const 2).pow 2) (C := 1) fun x => by
      obtain ⟨b1, b2⟩ := bE hp x; obtain ⟨c1, c2⟩ := bE hs x
      rw [abs_of_nonneg (by positivity)]; nlinarith
  have hi2 : Integrable (fun x => ((E p x - E s x) / 2) ^ 2) μ :=
    integrable_of_continuous_bdd
      ((((continuous_E p).sub (continuous_E s)).div_const 2).pow 2) (C := 1) fun x => by
      obtain ⟨b1, b2⟩ := bE hp x; obtain ⟨c1, c2⟩ := bE hs x
      rw [abs_of_nonneg (by positivity)]; nlinarith
  rw [hps, hrr, integral_sub hi1 hi2, hmean]
  nlinarith

/-- The variance case: `(∫ E r)² ≤ ∫ E (r + r)`. -/
lemma var_nonneg {r : ℝ} (hr : 0 ≤ r) :
    (∫ x, E r x ∂μ) ^ 2 ≤ ∫ x, E (r + r) x ∂μ := by
  have hrr : (fun x => E (r + r) x) = fun x => (E r x) ^ 2 := by
    funext x; rw [← E_mul]; ring
  rw [hrr]
  exact sq_integral_le (continuous_E r) (C := 1) fun x => by
    rw [abs_of_pos (E_pos r x)]; exact E_le_one hr x

end Crossing

/-! ## Properties of the generator -/

section Generator

variable {f : ℝ → ℝ} {μ : Measure ℝ≥0} [IsProbabilityMeasure μ]

lemma exists_preimage (hcont : ContinuousOn f (Ici 0)) (hf0 : f 0 = 1)
    (hlim : Tendsto f atTop (𝓝 0)) {u : ℝ} (hu0 : 0 < u) (hu1 : u ≤ 1) :
    ∃ x ∈ Ici (0 : ℝ), f x = u := by
  obtain ⟨T, hT⟩ := (eventually_atTop.1 ((hlim.eventually (gt_mem_nhds hu0))))
  set T' := max T 0
  have hT' : f T' < u := hT T' (le_max_left _ _)
  have hIVT := intermediate_value_Icc' (le_max_right T 0 : (0 : ℝ) ≤ T')
    (hcont.mono (Icc_subset_Ici_self))
  obtain ⟨x, hx, hfx⟩ := hIVT ⟨hT'.le, hf0 ▸ hu1⟩
  exact ⟨x, hx.1, hfx⟩

end Generator

/-! ## Bernstein representation of the shifted generator -/

section Shift

open MO195959

variable {f : ℝ → ℝ}

/-- A positive shift of a function completely monotone on `(0, ∞)` is completely monotone on the
closed half-line (adapted from TauCeti's `IsCompletelyMonotoneOnIoi.isCompletelyMonotone_comp_add_const`). -/
lemma isCompletelyMonotone_shift (hcm : CompletelyMonotoneOn f (Ioi 0)) {a : ℝ} (ha : 0 < a) :
    TauCeti.IsCompletelyMonotone (fun t : ℝ => f (t + a)) := by
  refine ⟨?_, fun n t ht => ?_⟩
  · have hmaps : MapsTo (fun t : ℝ => t + a) (Ici 0) (Ioi 0) := fun t ht =>
      mem_Ioi.mpr (by linarith [mem_Ici.mp ht])
    exact hcm.1.comp ((contDiff_id.add contDiff_const).contDiffOn) hmaps
  · have htpa : 0 < t + a := by linarith
    have hc : ContDiffAt ℝ (n : WithTop ℕ∞) f (t + a) :=
      (hcm.1.contDiffAt (isOpen_Ioi.mem_nhds htpa)).of_le (by exact_mod_cast le_top)
    have hcont : ContDiffAt ℝ (n : WithTop ℕ∞) (fun t : ℝ => f (t + a)) t :=
      hc.comp t (contDiff_id.add contDiff_const).contDiffAt
    rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Ici 0) hcont (mem_Ici.mpr ht),
      iteratedDeriv_comp_add_const]
    have := hcm.2 n (t + a) htpa
    rwa [iteratedDerivWithin_of_isOpen isOpen_Ioi (show t + a ∈ Ioi (0 : ℝ) from htpa)] at this

/-- For `ε > 0` with `f ε > 0`, the normalized shift `t ↦ f (t + ε) / f ε` is the Laplace transform
of a probability measure on `ℝ≥0`. -/
lemma shifted_prob (hcm : CompletelyMonotoneOn f (Ioi 0)) {ε : ℝ} (hε : 0 < ε) (hfε : 0 < f ε) :
    ∃ ν : Measure ℝ≥0, IsProbabilityMeasure ν ∧ ∀ t, 0 ≤ t → ∫ x, E t x ∂ν = f (t + ε) / f ε := by
  obtain ⟨μ, hfin, hrep⟩ :=
    TauCeti.exists_representsLaplace_of_isCompletelyMonotone (isCompletelyMonotone_shift hcm hε)
  have hrep' : ∀ t, 0 ≤ t → f (t + ε) = ∫ x, E t x ∂μ := fun t ht => by
    rw [show f (t + ε) = TauCeti.laplaceTransform μ t from hrep t ht,
      TauCeti.laplaceTransform_apply]; rfl
  have hmass : μ univ = ENNReal.ofReal (f ε) := by
    have h0 := hrep' 0 le_rfl
    simp only [E_zero_left, integral_const, smul_eq_mul, mul_one, zero_add] at h0
    rw [h0, measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)]
  refine ⟨(ENNReal.ofReal (f ε))⁻¹ • μ, ⟨?_⟩, fun t ht => ?_⟩
  · rw [Measure.smul_apply, hmass, smul_eq_mul]
    exact ENNReal.inv_mul_cancel (ENNReal.ofReal_pos.2 hfε).ne' ENNReal.ofReal_ne_top
  · rw [integral_smul_measure, ← hrep' t ht, ENNReal.toReal_inv, ENNReal.toReal_ofReal hfε.le,
      smul_eq_mul, div_eq_inv_mul]

lemma tendsto_zero (hcont : ContinuousOn f (Ici 0)) :
    Tendsto f (𝓝[>] (0 : ℝ)) (𝓝 (f 0)) :=
  (hcont 0 (mem_Ici.2 le_rfl)).mono Ioi_subset_Ici_self

lemma eventually_pos (hcont : ContinuousOn f (Ici 0)) (hf0 : f 0 = 1) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < f ε := by
  have h := tendsto_zero hcont
  rw [hf0] at h
  exact h.eventually (lt_mem_nhds one_pos)

lemma tendsto_sub (hcont : ContinuousOn f (Ici 0)) {b : ℝ} (hb : 0 < b) :
    Tendsto (fun ε => f (b - ε) * f ε) (𝓝[>] (0 : ℝ)) (𝓝 (f b * f 0)) := by
  have hcA : ContinuousAt f b := hcont.continuousAt (Ici_mem_nhds hb)
  have hlin : Tendsto (fun ε : ℝ => b - ε) (𝓝[>] (0 : ℝ)) (𝓝 b) := by
    have : Tendsto (fun ε : ℝ => b - ε) (𝓝 (0 : ℝ)) (𝓝 (b - 0)) :=
      tendsto_const_nhds.sub tendsto_id
    rw [sub_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  exact (hcA.tendsto.comp hlin).mul (tendsto_zero hcont)

/-- Clearing the normalization. -/
lemma scale_ineq {c A B D G F : ℝ} (hc : 0 < c)
    (h : A / c - B / c * (D / c) ≤ G / c - (F / c) ^ 2) : A * c - B * D ≤ G * c - F ^ 2 := by
  have hk : c * c⁻¹ = 1 := mul_inv_cancel₀ hc.ne'
  have h2 := mul_le_mul_of_nonneg_right h (sq_nonneg c)
  have e1 : (A / c - B / c * (D / c)) * c ^ 2 = A * c - B * D := by
    simp only [div_eq_mul_inv]
    calc _ = A * c * (c * c⁻¹) - B * D * (c * c⁻¹) ^ 2 := by ring
      _ = _ := by rw [hk]; ring
  have e2 : (G / c - (F / c) ^ 2) * c ^ 2 = G * c - F ^ 2 := by
    simp only [div_eq_mul_inv]
    calc _ = G * c * (c * c⁻¹) - F ^ 2 * (c * c⁻¹) ^ 2 := by ring
      _ = _ := by rw [hk]; ring
  rw [e1, e2] at h2
  exact h2

/-- `f(a)² ≤ f(2a)` for `a > 0`. -/
lemma var_pos (hcont : ContinuousOn f (Ici 0)) (hf0 : f 0 = 1)
    (hcm : CompletelyMonotoneOn f (Ioi 0)) {a : ℝ} (ha : 0 < a) : f a ^ 2 ≤ f (a + a) := by
  have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), f a ^ 2 ≤ f (a + a - ε) * f ε := by
    filter_upwards [eventually_pos hcont hf0, Ioo_mem_nhdsGT ha] with ε hpos hε
    obtain ⟨ν, hν, hint⟩ := shifted_prob hcm hε.1 hpos
    have hr : 0 ≤ a - ε := by linarith [hε.2]
    have h := var_nonneg (μ := ν) hr
    rw [hint _ hr, hint _ (add_nonneg hr hr)] at h
    simp only [sub_add_cancel] at h
    rw [show a - ε + (a - ε) + ε = a + a - ε by ring] at h
    have h' := scale_ineq (A := 0) (B := 0) (D := 0) hpos (by simpa using h)
    linarith
  have := le_of_tendsto_of_tendsto tendsto_const_nhds (tendsto_sub hcont (by linarith)) hev
  rwa [hf0, mul_one] at this

/-- The key inequality for positive exponents. -/
lemma key_pos (hcont : ContinuousOn f (Ici 0)) (hf0 : f 0 = 1)
    (hcm : CompletelyMonotoneOn f (Ioi 0)) {x y a : ℝ} (hx : 0 < x) (hy : 0 < y) (ha : 0 < a)
    (hmean : f a = (f x + f y) / 2) :
    f (x + y) - f x * f y ≤ f (a + a) - f a ^ 2 := by
  have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      f (x + y - ε) * f ε - f x * f y ≤ f (a + a - ε) * f ε - f a ^ 2 := by
    filter_upwards [eventually_pos hcont hf0, Ioo_mem_nhdsGT (lt_min hx (lt_min hy ha))]
      with ε hpos hε
    have hεx : ε < x := lt_of_lt_of_le hε.2 (min_le_left _ _)
    have hεy : ε < y := lt_of_lt_of_le hε.2 ((min_le_right _ _).trans (min_le_left _ _))
    have hεa : ε < a := lt_of_lt_of_le hε.2 ((min_le_right _ _).trans (min_le_right _ _))
    obtain ⟨ν, hν, hint⟩ := shifted_prob hcm hε.1 hpos
    have hp : 0 ≤ x - ε := by linarith
    have hs : 0 ≤ y - ε := by linarith
    have hr : 0 ≤ a - ε := by linarith
    have hm : ∫ t, E (a - ε) t ∂ν = ((∫ t, E (x - ε) t ∂ν) + ∫ t, E (y - ε) t ∂ν) / 2 := by
      rw [hint _ hr, hint _ hp, hint _ hs]
      simp only [sub_add_cancel]
      rw [hmean]
      ring
    have h := core (μ := ν) hp hr hs hm
    rw [hint _ (add_nonneg hp hs), hint _ hp, hint _ hs, hint _ (add_nonneg hr hr), hint _ hr] at h
    simp only [sub_add_cancel] at h
    rw [show x - ε + (y - ε) + ε = x + y - ε by ring,
      show a - ε + (a - ε) + ε = a + a - ε by ring] at h
    exact scale_ineq hpos h
  have := le_of_tendsto_of_tendsto ((tendsto_sub hcont (add_pos hx hy)).sub tendsto_const_nhds)
    ((tendsto_sub hcont (add_pos ha ha)).sub tendsto_const_nhds) hev
  rwa [hf0, mul_one, mul_one] at this

/-- The key inequality for nonnegative exponents `x, y` and a positive exponent `a`. -/
lemma key (hcont : ContinuousOn f (Ici 0)) (hf0 : f 0 = 1)
    (hcm : CompletelyMonotoneOn f (Ioi 0)) {x y a : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (ha : 0 < a)
    (hmean : f a = (f x + f y) / 2) :
    f (x + y) - f x * f y ≤ f (a + a) - f a ^ 2 := by
  have hv := var_pos hcont hf0 hcm ha
  rcases eq_or_lt_of_le hx with hx0 | hx0
  · subst hx0; rw [zero_add, hf0]; linarith
  rcases eq_or_lt_of_le hy with hy0 | hy0
  · subst hy0; rw [add_zero, hf0]; linarith
  exact key_pos hcont hf0 hcm hx0 hy0 ha hmean

end Shift

/-! ## Main theorem -/

open MO195959 in
theorem main_proof :
    ∀ f : ℝ → ℝ, ContinuousOn f (Set.Ici 0) → f 0 = 1 → Tendsto f atTop (𝓝 0) →
      CompletelyMonotoneOn f (Set.Ioi 0) →
      ∀ u ∈ Set.Icc (0 : ℝ) 1, ∀ v ∈ Set.Icc (0 : ℝ) 1,
        archC f u v - u * v ≤ archC f ((u + v) / 2) ((u + v) / 2) - ((u + v) / 2) ^ 2 := by
  intro f hcont hf0 hlim hcm
  set g := Function.invFunOn f (Set.Ici 0) with hg
  have hgspec : ∀ {u : ℝ}, 0 < u → u ≤ 1 → g u ∈ Ici (0 : ℝ) ∧ f (g u) = u := fun hu0 hu1 =>
    Function.invFunOn_pos (exists_preimage hcont hf0 hlim hu0 hu1)
  -- the claim for positive, distinct arguments
  have hcase : ∀ u v : ℝ, 0 < u → 0 < v → u ≤ 1 → v ≤ 1 → u ≠ v →
      archC f u v - u * v ≤ archC f ((u + v) / 2) ((u + v) / 2) - ((u + v) / 2) ^ 2 := by
    intro u v hu0 hv0 hu1 hv1 huv
    set a := (u + v) / 2 with ha
    have ha0 : 0 < a := by linarith
    have ha1 : a < 1 := by
      rcases lt_or_gt_of_ne huv with h | h <;> linarith
    obtain ⟨gu0, fgu⟩ := hgspec hu0 hu1
    obtain ⟨gv0, fgv⟩ := hgspec hv0 hv1
    obtain ⟨ga0, fga⟩ := hgspec ha0 ha1.le
    have hAC : archC f u v = f (g u + g v) := by
      simp [archC, hu0.ne', hv0.ne', hg]
    have hAA : archC f a a = f (g a + g a) := by
      simp [archC, ha0.ne', hg]
    rw [hAC, hAA]
    have ga0' : 0 < g a := by
      rcases eq_or_lt_of_le (show (0 : ℝ) ≤ g a from ga0) with h | h
      · rw [← h, hf0] at fga; linarith
      · exact h
    have hmean : f (g a) = (f (g u) + f (g v)) / 2 := by rw [fga, fgu, fgv]
    have := key hcont hf0 hcm (show (0 : ℝ) ≤ g u from gu0) (show (0 : ℝ) ≤ g v from gv0) ga0' hmean
    rw [fgu, fgv, fga] at this
    exact this
  intro u ⟨hu0, hu1⟩ v ⟨hv0, hv1⟩
  rcases lt_trichotomy u v with huv | huv | huv
  · rcases eq_or_lt_of_le hu0 with hu | hu
    · -- u = 0
      subst hu
      set a := (0 + v) / 2 with ha
      have ha0 : 0 < a := by linarith
      obtain ⟨ga0, fga⟩ := hgspec ha0 (by linarith)
      have hAA : archC f a a = f (g a + g a) := by simp [archC, ha0.ne', hg]
      have hA0 : archC f 0 v = 0 := by simp [archC]
      rw [hAA, hA0]
      have : 0 < g a := by
        rcases eq_or_lt_of_le (show (0 : ℝ) ≤ g a from ga0) with h | h
        · rw [← h, hf0] at fga; linarith
        · exact h
      have := var_pos hcont hf0 hcm this
      rw [fga] at this
      linarith
    · exact hcase u v hu (by linarith) hu1 hv1 huv.ne
  · subst huv
    have : (u + u) / 2 = u := by ring
    rw [this]; nlinarith
  · rcases eq_or_lt_of_le hv0 with hv | hv
    · subst hv
      set a := (u + 0) / 2 with ha
      have ha0 : 0 < a := by linarith
      obtain ⟨ga0, fga⟩ := hgspec ha0 (by linarith)
      have hAA : archC f a a = f (g a + g a) := by simp [archC, ha0.ne', hg]
      have hA0 : archC f u 0 = 0 := by simp [archC]
      rw [hAA, hA0]
      have : 0 < g a := by
        rcases eq_or_lt_of_le (show (0 : ℝ) ≤ g a from ga0) with h | h
        · rw [← h, hf0] at fga; linarith
        · exact h
      have := var_pos hcont hf0 hcm this
      rw [fga] at this
      linarith
    · have hsym : archC f u v = archC f v u := by
        simp only [archC, or_comm, add_comm]
      have := hcase v u hv (by linarith) hv1 hu1 huv.ne
      rw [hsym, add_comm u v, mul_comm u v]
      exact this

end Kimberling


end
