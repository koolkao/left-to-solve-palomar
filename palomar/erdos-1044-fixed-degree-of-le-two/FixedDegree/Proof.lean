/-
Copyright 2026 Ming-Chih Kao. Licensed under the Apache License, Version 2.0;
see the LICENSE file at the root of this repository.
-/
module

public import FixedDegree.Defs

/-! Ported from the archived Left to Solve file `Erdos1044.erdos_1044.variants.fixed_degree_of_le_two.lean` (Lean v4.33.1) to Lean
v4.36.0 and the module system; the mathematics and the proof are unchanged unless a comment
says otherwise. -/

@[expose] public section

-- Problem: Erdős Problem 1044 — fixed degree of le two
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/1044.lean:100 (declaration Erdos1044.erdos_1044.variants.fixed_degree_of_le_two)
-- Credit: @koolkao (the owner of the agent is credited as the solver)

/-!
# Erdős 1044, fixed degree `n ≤ 2`

For admissible `f` of degree `n ∈ {1, 2}` we show `Λ(X ^ n - 1) ≤ Λ(f)`.

* `Λ` is invariant under rigid motions `w ↦ c + u w`, `‖u‖ = 1` (`maxBoundaryLength_congr`).
* Degree 1: `f = X - a` is a translate of `X - 1`.
* Degree 2: `f = (X - a)(X - b) = (X - c)² - d²` with `c` the midpoint and `d = (a - b)/2`, `‖d‖ ≤ 1`.
  - If `‖d‖ = 1`, `f(c + d v) = d² (v² - 1)`, so `f` is a rigid image of `X ^ 2 - 1`.
  - If `‖d‖ < 1`, the component of `c` contains a segment of length `2`; above and below each
    of its points there is a frontier point, and the orthogonal projection is `1`-Lipschitz,
    so the frontier has `𝓗¹ ≥ 4` (`four_le_frontier_of_segment'`).
  - Each component of `{|w² - 1| < 1}` is a lobe of the lemniscate. Its frontier is covered by
    two images of `[0, 1]` under the `2`-Lipschitz rational parametrisation
    `t ↦ ± √2 (1 - i) t / (t² - i)` and its conjugate, so it has `𝓗¹ ≤ 4` (`lobe_le_four`).
-/

namespace OMA_E1044

open Polynomial Set MeasureTheory Complex

/-- The rigid motion `w ↦ c + u * w` for `‖u‖ = 1`. -/
noncomputable def rig (u c : ℂ) (hu : ‖u‖ = 1) : ℂ ≃ᵢ ℂ where
  toFun w := c + u * w
  invFun w := (w - c) / u
  left_inv w := by
    have : u ≠ 0 := by rintro rfl; simp at hu
    simp only; field_simp; ring
  right_inv w := by
    have : u ≠ 0 := by rintro rfl; simp at hu
    simp only; field_simp; ring
  isometry_toFun := by
    refine Isometry.of_dist_eq fun x y => ?_
    simp only [dist_eq_norm]
    rw [show c + u * x - (c + u * y) = u * (x - y) by ring, norm_mul, hu, one_mul]

@[simp] lemma rig_apply (u c : ℂ) (hu : ‖u‖ = 1) (w : ℂ) : rig u c hu w = c + u * w := rfl

/-- `Λ` is invariant under rigid motions. -/
lemma maxBoundaryLength_congr (e : ℂ ≃ᵢ ℂ) (f g : ℂ[X])
    (h : ∀ v, ‖f.eval (e v)‖ = ‖g.eval v‖) :
    Erdos1044.maxBoundaryLength f = Erdos1044.maxBoundaryLength g := by
  set Uf := {w : ℂ | ‖f.eval w‖ < 1}
  set Ug := {w : ℂ | ‖g.eval w‖ < 1}
  have hpre : e ⁻¹' Uf = Ug := by ext v; simp [Uf, Ug, h]
  have himg : e '' Ug = Uf := by rw [← hpre]; exact Set.image_preimage_eq Uf e.surjective
  have key : ∀ v ∈ Ug, Erdos1041.length (frontier (connectedComponentIn Uf (e v))) =
      Erdos1041.length (frontier (connectedComponentIn Ug v)) := by
    intro v hv
    have h1 := e.toHomeomorph.image_connectedComponentIn hv
    simp only [IsometryEquiv.coe_toHomeomorph] at h1
    rw [himg] at h1
    rw [← h1]
    have h2 := e.toHomeomorph.image_frontier (connectedComponentIn Ug v)
    simp only [IsometryEquiv.coe_toHomeomorph] at h2
    rw [← h2]
    exact e.hausdorffMeasure_image 1 _
  unfold Erdos1044.maxBoundaryLength
  apply le_antisymm
  · refine iSup₂_le fun z hz => ?_
    have hz' : e.symm z ∈ Ug := by
      rw [← hpre]; change e (e.symm z) ∈ Uf
      rw [e.apply_symm_apply]; exact hz
    have := key _ hz'
    rw [e.apply_symm_apply] at this
    rw [this]
    exact le_iSup₂ (f := fun w (_ : w ∈ Ug) =>
      Erdos1041.length (frontier (connectedComponentIn Ug w))) _ hz'
  · refine iSup₂_le fun v hv => ?_
    rw [← key v hv]
    have hv' : e v ∈ Uf := by change v ∈ Ug at hv; rw [← hpre] at hv; exact hv
    exact le_iSup₂ (f := fun w (_ : w ∈ Uf) =>
      Erdos1041.length (frontier (connectedComponentIn Uf w))) _ hv'

end OMA_E1044

namespace OMA_E1044

open Polynomial Set MeasureTheory Complex

/-- On the vertical line through a real point `t` of a bounded open set `C`, going up (`σ = 1`)
or down (`σ = -1`) from `t`, one meets the frontier of `C` at a point off the real axis. -/
lemma exists_frontier_vertical {C : Set ℂ} (hC : IsOpen C) {R : ℝ} (hR : ∀ w ∈ C, ‖w‖ ≤ R)
    {t : ℝ} (ht : (t : ℂ) ∈ C) {σ : ℝ} (hσ : |σ| = 1) :
    ∃ s : ℝ, 0 < s ∧ (t : ℂ) + (σ * s : ℝ) * I ∈ frontier C := by
  set g : ℝ → ℂ := fun s => (t : ℂ) + (σ * s : ℝ) * I with hg
  have gc : Continuous g := by fun_prop
  set T := g ⁻¹' C with hT
  have hTo : IsOpen T := hC.preimage gc
  have h0 : (0 : ℝ) ∈ T := by simpa [hT, hg] using ht
  have hbdd : BddAbove T := by
    refine ⟨R, fun s hs => ?_⟩
    have h1 := hR _ hs
    have h2 : |(g s).im| ≤ ‖g s‖ := abs_im_le_norm _
    have h3 : (g s).im = σ * s := by simp [hg]
    rw [h3, abs_mul, hσ, one_mul] at h2
    exact (le_abs_self s).trans (h2.trans h1)
  set s₀ := sSup T
  have hs₀cl : s₀ ∈ closure T := csSup_mem_closure ⟨0, h0⟩ hbdd
  have hgcl : g s₀ ∈ closure C := by
    have : g '' closure T ⊆ closure (g '' T) := image_closure_subset_closure_image gc
    exact closure_mono (image_preimage_subset g C) (this ⟨s₀, hs₀cl, rfl⟩)
  have hnot : s₀ ∉ T := by
    intro hs
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hTo s₀ hs
    have hmem : s₀ + ε / 2 ∈ T := hball (by
      rw [Metric.mem_ball, Real.dist_eq]
      rw [show s₀ + ε / 2 - s₀ = ε / 2 by ring, abs_of_pos (by linarith)]
      linarith)
    have := le_csSup hbdd hmem
    linarith
  have hpos : 0 < s₀ := by
    have h1 : 0 ≤ s₀ := le_csSup hbdd h0
    rcases h1.lt_or_eq with h | h
    · exact h
    · exact absurd (h ▸ h0) hnot
  refine ⟨s₀, hpos, ?_⟩
  rw [hC.frontier_eq]
  exact ⟨hgcl, hnot⟩

/-- A bounded open set containing the real segment `(-1, 1)` has frontier of length at least `4`:
above and below each point of the segment there is a frontier point, and the real-part
projection is `1`-Lipschitz. -/
lemma four_le_frontier_of_segment {C : Set ℂ} (hC : IsOpen C) {R : ℝ}
    (hR : ∀ w ∈ C, ‖w‖ ≤ R) (hseg : ∀ t ∈ Ioo (-1 : ℝ) 1, (t : ℂ) ∈ C) :
    4 ≤ μH[1] (frontier C) := by
  have hre : LipschitzWith 1 Complex.re := by
    refine LipschitzWith.of_dist_le_mul fun x y => ?_
    rw [Real.dist_eq, dist_eq_norm, NNReal.coe_one, one_mul, ← Complex.sub_re]
    exact abs_re_le_norm _
  have side : ∀ σ : ℝ, |σ| = 1 →
      2 ≤ μH[1] (frontier C ∩ {w : ℂ | 0 < σ * w.im}) := by
    intro σ hσ
    have hsub : Ioo (-1 : ℝ) 1 ⊆ Complex.re '' (frontier C ∩ {w : ℂ | 0 < σ * w.im}) := by
      intro t ht
      obtain ⟨s, hs, hfr⟩ := exists_frontier_vertical hC hR (hseg t ht) hσ
      refine ⟨_, ⟨hfr, ?_⟩, by simp⟩
      have hσσ : σ * σ = 1 := by
        have := sq_abs σ; rw [hσ] at this; nlinarith
      simp only [mem_ofPred_eq, add_im, ofReal_im, mul_im, ofReal_re, I_re, mul_zero, I_im,
        mul_one, zero_add]
      rw [add_zero, ← mul_assoc, hσσ, one_mul]; exact hs
    have h1 := hre.hausdorffMeasure_image_le (d := 1) zero_le_one
      (frontier C ∩ {w : ℂ | 0 < σ * w.im})
    rw [ENNReal.coe_one, ENNReal.one_rpow, one_mul] at h1
    have h2 := measure_mono (μ := (μH[1] : Measure ℝ)) hsub
    rw [hausdorffMeasure_real, Real.volume_Ioo] at h2
    have h3 : ENNReal.ofReal (1 - -1) = 2 := by norm_num
    rw [h3] at h2
    rw [hausdorffMeasure_real] at h1
    calc (2 : ENNReal) ≤ _ := h2
      _ ≤ _ := h1
  have hA := side 1 (by norm_num)
  have hB := side (-1) (by norm_num)
  have hmeas : MeasurableSet (frontier C ∩ {w : ℂ | 0 < (-1) * w.im}) :=
    isClosed_frontier.measurableSet.inter
      (measurableSet_lt measurable_const (measurable_const.mul Complex.measurable_im))
  have hdisj : Disjoint (frontier C ∩ {w : ℂ | 0 < 1 * w.im})
      (frontier C ∩ {w : ℂ | 0 < (-1) * w.im}) := by
    rw [Set.disjoint_left]
    rintro w ⟨_, h1⟩ ⟨_, h2⟩
    simp only [mem_ofPred_eq] at h1 h2
    linarith
  calc (4 : ENNReal) = 2 + 2 := by norm_num
    _ ≤ _ := add_le_add hA hB
    _ = μH[1] ((frontier C ∩ {w : ℂ | 0 < 1 * w.im}) ∪
          (frontier C ∩ {w : ℂ | 0 < (-1) * w.im})) := (measure_union hdisj hmeas).symm
    _ ≤ _ := measure_mono (union_subset inter_subset_left inter_subset_left)

end OMA_E1044

namespace OMA_E1044

open Polynomial Set MeasureTheory Complex ComplexConjugate

/-- A rational parametrisation of the right lobe of the lemniscate `|w² - 1| = 1`:
`gam t = √2 (1 - i) t / (t² - i)`; `t ∈ [0, 1]` traces the upper half of the lobe. -/
noncomputable def gam (t : ℝ) : ℂ := ((Real.sqrt 2 : ℂ) * (1 - I) * t) / ((t : ℂ) ^ 2 - I)

lemma sq_sub_I_ne_zero (t : ℝ) : (t : ℂ) ^ 2 - I ≠ 0 := by
  intro h
  have := congrArg Complex.im h
  simp [sq] at this

lemma norm_sq_sub_I_sq (t : ℝ) : ‖(t : ℂ) ^ 2 - I‖ ^ 2 = t ^ 4 + 1 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp [sq]; ring

lemma gam_lipschitz : LipschitzWith 2 gam := by
  refine LipschitzWith.of_dist_le_mul fun t s => ?_
  rw [dist_eq_norm, Real.dist_eq]
  have hA := sq_sub_I_ne_zero t
  have hB := sq_sub_I_ne_zero s
  have key : gam t - gam s = ((Real.sqrt 2 : ℂ) * (1 - I)) *
      (((s : ℂ) - t) * ((t : ℂ) * s + I)) / (((t : ℂ) ^ 2 - I) * ((s : ℂ) ^ 2 - I)) := by
    unfold gam
    field_simp
    ring_nf
  have hc : ‖(Real.sqrt 2 : ℂ) * (1 - I)‖ = 2 := by
    have h2 : ‖(Real.sqrt 2 : ℂ) * (1 - I)‖ ^ 2 = 2 ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      simp
      norm_num
    exact (pow_left_inj₀ (norm_nonneg _) (by norm_num) two_ne_zero).1 h2
  have hst : ‖((s : ℂ) - t)‖ = |t - s| := by
    rw [← ofReal_sub, norm_real, Real.norm_eq_abs, abs_sub_comm]
  have hts : ‖(t : ℂ) * s + I‖ ≤ ‖(t : ℂ) ^ 2 - I‖ * ‖(s : ℂ) ^ 2 - I‖ := by
    rw [← pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero, mul_pow,
      norm_sq_sub_I_sq, norm_sq_sub_I_sq, Complex.sq_norm, Complex.normSq_apply]
    simp
    nlinarith [sq_nonneg (t ^ 2 - s ^ 2), sq_nonneg (t * s), sq_nonneg t, sq_nonneg s,
      mul_nonneg (sq_nonneg t) (sq_nonneg s)]
  have hApos : 0 < ‖(t : ℂ) ^ 2 - I‖ := norm_pos_iff.2 hA
  have hBpos : 0 < ‖(s : ℂ) ^ 2 - I‖ := norm_pos_iff.2 hB
  rw [key, norm_div, norm_mul, hc, norm_mul, hst, norm_mul, div_le_iff₀ (by positivity)]
  simp only [NNReal.coe_ofNat]
  calc 2 * (|t - s| * ‖(t : ℂ) * s + I‖)
      ≤ 2 * (|t - s| * (‖(t : ℂ) ^ 2 - I‖ * ‖(s : ℂ) ^ 2 - I‖)) := by gcongr
    _ = _ := by ring

/-- Every point of the closed first quadrant on the lemniscate is `gam t` with `t ∈ [0, 1]`. -/
lemma gam_cover (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (h : (x ^ 2 + y ^ 2) ^ 2 = 2 * (x ^ 2 - y ^ 2)) :
    ∃ t ∈ Icc (0 : ℝ) 1, gam t = ⟨x, y⟩ := by
  rcases (add_nonneg hx hy).lt_or_eq with hp | hp
  · have hxy : y ≤ x := by nlinarith [sq_nonneg (x ^ 2 + y ^ 2)]
    set t := Real.sqrt ((x - y) / (x + y)) with ht
    have ht0 : 0 ≤ t := Real.sqrt_nonneg _
    have ht2 : t ^ 2 = (x - y) / (x + y) := Real.sq_sqrt (div_nonneg (by linarith) hp.le)
    have ht1 : t ≤ 1 := by
      rw [ht, Real.sqrt_le_one]
      rw [div_le_one hp]; linarith
    have hkey : Real.sqrt 2 * t = (x ^ 2 + y ^ 2) / (x + y) := by
      rw [← pow_left_inj₀ (by positivity) (by positivity) two_ne_zero, mul_pow,
        Real.sq_sqrt (by norm_num), ht2, div_pow, h]
      field_simp
      ring
    refine ⟨t, ⟨ht0, ht1⟩, ?_⟩
    unfold gam
    rw [div_eq_iff (sq_sub_I_ne_zero t)]
    apply Complex.ext
    · simp [sq]
      have : x * (t * t) + y = (x ^ 2 + y ^ 2) / (x + y) := by
        rw [← sq, ht2]; field_simp; ring
      linarith
    · simp [sq]
      have : y * (t * t) - x = -((x ^ 2 + y ^ 2) / (x + y)) := by
        rw [← sq, ht2]; field_simp; ring
      linarith
  · have hx0 : x = 0 := by linarith
    have hy0 : y = 0 := by linarith
    refine ⟨0, ⟨le_rfl, zero_le_one⟩, ?_⟩
    subst hx0 hy0
    simp [gam]
    rfl

lemma lemniscate_eq {w : ℂ} (h : ‖w ^ 2 - 1‖ = 1) :
    (w.re ^ 2 + w.im ^ 2) ^ 2 = 2 * (w.re ^ 2 - w.im ^ 2) := by
  have h2 : ‖w ^ 2 - 1‖ ^ 2 = 1 := by rw [h]; norm_num
  rw [Complex.sq_norm, Complex.normSq_apply] at h2
  simp [sq] at h2
  nlinarith [h2]

/-- Each component of `{|w² - 1| < 1}` has frontier of length at most `4`. -/
lemma lobe_le_four (z : ℂ) (hz : z ∈ {w : ℂ | ‖w ^ 2 - 1‖ < 1}) :
    μH[1] (frontier (connectedComponentIn {w : ℂ | ‖w ^ 2 - 1‖ < 1} z)) ≤ 4 := by
  set U := {w : ℂ | ‖w ^ 2 - 1‖ < 1} with hUdef
  have hU : IsOpen U := isOpen_lt (by fun_prop) continuous_const
  have hre0 : ∀ w ∈ U, w.re ≠ 0 := by
    intro w hw h0
    have h1 : (w ^ 2 - 1).re = -(w.im ^ 2) - 1 := by simp [sq, h0]
    have h2 := abs_re_le_norm (w ^ 2 - 1)
    rw [h1] at h2
    have : (1 : ℝ) ≤ |-(w.im ^ 2) - 1| := by
      rw [abs_of_neg (by nlinarith [sq_nonneg w.im])]; nlinarith [sq_nonneg w.im]
    exact absurd hw (not_lt.2 (this.trans h2))
  set ε : ℝ := if 0 < z.re then 1 else -1 with hεdef
  have hεε : ε * ε = 1 := by rw [hεdef]; split_ifs <;> norm_num
  have hεz : 0 < ε * z.re := by
    rw [hεdef]; split_ifs with h
    · simpa using h
    · have := hre0 z hz
      have : z.re < 0 := lt_of_le_of_ne (not_lt.1 h) this
      linarith
  set C := connectedComponentIn U z with hC
  have hCU : C ⊆ U := connectedComponentIn_subset U z
  have hCo : IsOpen C := hU.connectedComponentIn
  have hChalf : C ⊆ {w : ℂ | 0 < ε * w.re} := by
    refine isPreconnected_connectedComponentIn.subset_left_of_subset_union
      (u := {w : ℂ | 0 < ε * w.re}) (v := {w : ℂ | ε * w.re < 0})
      (isOpen_lt continuous_const (continuous_const.mul Complex.continuous_re))
      (isOpen_lt (continuous_const.mul Complex.continuous_re) continuous_const)
      ?_ ?_ ⟨z, mem_connectedComponentIn hz, hεz⟩
    · rw [Set.disjoint_left]; intro w h1 h2
      simp only [mem_ofPred_eq] at h1 h2; linarith
    · intro w hw
      have h1 := hre0 w (hCU hw)
      have hε0 : ε ≠ 0 := by intro h; rw [h] at hεε; norm_num at hεε
      rcases lt_or_gt_of_ne (mul_ne_zero hε0 h1) with h | h
      · exact Or.inr h
      · exact Or.inl h
  have hfr : ∀ w ∈ frontier C, ‖w ^ 2 - 1‖ = 1 ∧ 0 ≤ ε * w.re := by
    intro w hw
    rw [hCo.frontier_eq] at hw
    obtain ⟨hcl, hnot⟩ := hw
    have hcl' : closure C ⊆ {w : ℂ | ‖w ^ 2 - 1‖ ≤ 1 ∧ 0 ≤ ε * w.re} := by
      refine closure_minimal (fun v hv => ⟨(hCU hv).le, (hChalf hv).le⟩) ?_
      exact (isClosed_le (f := fun w : ℂ => ‖w ^ 2 - 1‖) (by fun_prop) continuous_const).inter
        (isClosed_le (g := fun w : ℂ => ε * w.re) continuous_const
          (continuous_const.mul Complex.continuous_re))
    obtain ⟨h1, h2⟩ := hcl' hcl
    refine ⟨le_antisymm h1 (not_lt.1 fun hlt => hnot ?_), h2⟩
    have hwU : w ∈ U := hlt
    obtain ⟨y, hy1, hy2⟩ := mem_closure_iff.1 hcl _ (hU.connectedComponentIn (x := w))
      (mem_connectedComponentIn hwU)
    rw [hC, connectedComponentIn_eq hy2, ← connectedComponentIn_eq hy1]
    exact mem_connectedComponentIn hwU
  have hcover : frontier C ⊆ (fun t => (ε : ℂ) * gam t) '' Icc 0 1 ∪
      (fun t => (ε : ℂ) * conj (gam t)) '' Icc 0 1 := by
    intro w hw
    obtain ⟨h1, h2⟩ := hfr w hw
    set v := (ε : ℂ) * w with hv
    have hεc : (ε : ℂ) * ε = 1 := by rw [← ofReal_mul, hεε, ofReal_one]
    have hwv : w = (ε : ℂ) * v := by rw [hv, ← mul_assoc, hεc, one_mul]
    have hvre : v.re = ε * w.re := by simp [hv]
    have hvim : v.im = ε * w.im := by simp [hv]
    have hv2 : ‖v ^ 2 - 1‖ = 1 := by
      rw [hv, mul_pow, sq (ε : ℂ), hεc, one_mul]; exact h1
    have hle := lemniscate_eq hv2
    rcases le_or_gt 0 v.im with him | him
    · obtain ⟨t, ht, hgt⟩ := gam_cover v.re v.im (hvre ▸ h2) him hle
      refine Or.inl ⟨t, ht, ?_⟩
      simp only
      rw [hgt, hwv]
    · obtain ⟨t, ht, hgt⟩ := gam_cover v.re (-v.im) (hvre ▸ h2) (by linarith)
        (by rw [neg_sq]; exact hle)
      refine Or.inr ⟨t, ht, ?_⟩
      simp only
      rw [hgt, hwv]
      congr 1
      apply Complex.ext <;> simp
  have hεn : ‖(ε : ℂ)‖ = 1 := by
    rw [norm_real, Real.norm_eq_abs]
    rw [hεdef]; split_ifs <;> norm_num
  have hmulε : LipschitzWith 1 (fun v : ℂ => (ε : ℂ) * v) := by
    refine LipschitzWith.of_dist_le_mul fun a b => ?_
    rw [dist_eq_norm, dist_eq_norm, ← mul_sub, norm_mul, hεn]; simp
  have hL1 : LipschitzWith 2 (fun t => (ε : ℂ) * gam t) := by
    have h := hmulε.comp gam_lipschitz
    rw [one_mul] at h; exact h
  have hL2 : LipschitzWith 2 (fun t => (ε : ℂ) * conj (gam t)) := by
    have h := (hmulε.comp Complex.isometry_conj.lipschitz).comp gam_lipschitz
    rw [one_mul, one_mul] at h; exact h
  have hpiece : ∀ g : ℝ → ℂ, LipschitzWith 2 g → μH[1] (g '' Icc 0 1) ≤ 2 := by
    intro g hg
    have := hg.hausdorffMeasure_image_le (d := 1) zero_le_one (Icc 0 1)
    rw [hausdorffMeasure_real, Real.volume_Icc, ENNReal.rpow_one] at this
    simpa using this
  calc μH[1] (frontier C) ≤ μH[1] ((fun t => (ε : ℂ) * gam t) '' Icc 0 1 ∪
        (fun t => (ε : ℂ) * conj (gam t)) '' Icc 0 1) := measure_mono hcover
    _ ≤ μH[1] ((fun t => (ε : ℂ) * gam t) '' Icc 0 1) +
        μH[1] ((fun t => (ε : ℂ) * conj (gam t)) '' Icc 0 1) := measure_union_le _ _
    _ ≤ 2 + 2 := add_le_add (hpiece _ hL1) (hpiece _ hL2)
    _ = 4 := by norm_num

end OMA_E1044

namespace OMA_E1044

open Polynomial Set MeasureTheory Complex

/-- The segment lemma for a segment `c + s u`, `s ∈ (-1, 1)`, `‖u‖ = 1`, in any direction. -/
lemma four_le_frontier_of_segment' {C : Set ℂ} (hC : IsOpen C) {R : ℝ}
    (hR : ∀ w ∈ C, ‖w‖ ≤ R) (u c : ℂ) (hu : ‖u‖ = 1)
    (hseg : ∀ s ∈ Ioo (-1 : ℝ) 1, c + (s : ℂ) * u ∈ C) :
    4 ≤ μH[1] (frontier C) := by
  set e := rig u c hu
  have h := four_le_frontier_of_segment (C := e ⁻¹' C) (hC.preimage e.continuous)
    (R := R + ‖c‖) ?_ ?_
  · have hpf := e.toHomeomorph.preimage_frontier C
    simp only [IsometryEquiv.coe_toHomeomorph] at hpf
    rw [← hpf] at h
    rwa [e.hausdorffMeasure_preimage] at h
  · intro w hw
    have h1 := hR _ hw
    simp only [e, rig_apply] at h1
    have h2 : ‖w‖ = ‖(c + u * w) - c‖ := by
      rw [add_sub_cancel_left, norm_mul, hu, one_mul]
    rw [h2]
    exact (norm_sub_le _ _).trans (by linarith)
  · intro t ht
    show e t ∈ C
    simp only [e, rig_apply]
    rw [mul_comm]; exact hseg t ht

lemma eq_prod_of_admissible {f : ℂ[X]} {n : ℕ} (hf : Erdos1044.IsAdmissible f)
    (hdeg : f.natDegree = n) :
    ∃ z : Fin n → ℂ, (∀ i, ‖z i‖ ≤ 1) ∧ f = ∏ i, (X - C (z i)) := by
  obtain ⟨m, -, z, hz, rfl⟩ := hf
  have : m = n := by rw [← hdeg, natDegree_finsetProd_X_sub_C_eq_card]; simp
  subst this
  exact ⟨z, hz, rfl⟩

lemma lam_sq_le_four : Erdos1044.maxBoundaryLength (X ^ 2 - 1) ≤ 4 := by
  unfold Erdos1044.maxBoundaryLength
  have hset : {w : ℂ | ‖(X ^ 2 - 1 : ℂ[X]).eval w‖ < 1} = {w : ℂ | ‖w ^ 2 - 1‖ < 1} := by
    ext w; simp
  rw [hset]
  exact iSup₂_le fun z hz => lobe_le_four z hz

lemma degree_one {f : ℂ[X]} (hf : Erdos1044.IsAdmissible f) (hdeg : f.natDegree = 1) :
    Erdos1044.maxBoundaryLength f = Erdos1044.maxBoundaryLength (X ^ 1 - 1) := by
  obtain ⟨z, -, rfl⟩ := eq_prod_of_admissible hf hdeg
  refine maxBoundaryLength_congr (rig 1 (z 0 - 1) norm_one) _ _ fun v => ?_
  simp only [rig_apply, Fin.prod_univ_one, eval_sub, eval_X, eval_C, one_mul, pow_one, eval_one]
  congr 1; ring

lemma degree_two {f : ℂ[X]} (hf : Erdos1044.IsAdmissible f) (hdeg : f.natDegree = 2) :
    Erdos1044.maxBoundaryLength (X ^ 2 - 1) ≤ Erdos1044.maxBoundaryLength f := by
  obtain ⟨z, hz, rfl⟩ := eq_prod_of_admissible hf hdeg
  set a := z 0
  set b := z 1
  set c := (a + b) / 2 with hc
  set d := (a - b) / 2 with hd
  have hev : ∀ w, (∏ i, (X - C (z i))).eval w = (w - c) ^ 2 - d ^ 2 := by
    intro w; simp [Fin.prod_univ_two, a, b, hc, hd]; ring
  have hev' : ∀ w, (∏ i, (X - C (z i))).eval w = (w - a) * (w - b) := by
    intro w; simp [Fin.prod_univ_two, a, b]
  have hdle : ‖d‖ ≤ 1 := by
    rw [hd, norm_div, Complex.norm_two, div_le_one two_pos]
    exact (norm_sub_le a b).trans (by linarith [hz 0, hz 1])
  rcases hdle.lt_or_eq with hlt | heq
  · -- the component of the midpoint contains a segment of length 2
    refine lam_sq_le_four.trans ?_
    set U := {w : ℂ | ‖(∏ i, (X - C (z i))).eval w‖ < 1} with hU
    have hUo : IsOpen U := isOpen_lt (by fun_prop) continuous_const
    set u : ℂ := if d = 0 then 1 else d / (‖d‖ : ℂ) with hudef
    have hun : ‖u‖ = 1 := by
      rw [hudef]; split_ifs with h
      · simp
      · rw [norm_div, norm_real, Real.norm_eq_abs, abs_norm, div_self (norm_ne_zero_iff.2 h)]
    have hdu : d = (‖d‖ : ℂ) * u := by
      rw [hudef]; split_ifs with h
      · simp [h]
      · rw [mul_div_cancel₀ _ (by exact_mod_cast norm_ne_zero_iff.2 h)]
    have hseg : ∀ s ∈ Ioo (-1 : ℝ) 1, c + (s : ℂ) * u ∈ U := by
      intro s hs
      show ‖(∏ i, (X - C (z i))).eval (c + (s : ℂ) * u)‖ < 1
      have h1 : (∏ i, (X - C (z i))).eval (c + (s : ℂ) * u) =
          u ^ 2 * (((s ^ 2 - ‖d‖ ^ 2 : ℝ)) : ℂ) := by
        rw [hev, show d ^ 2 = ((‖d‖ : ℂ) * u) ^ 2 by rw [← hdu]]; push_cast; ring
      rw [h1, norm_mul, norm_pow, hun, one_pow, one_mul, norm_real, Real.norm_eq_abs,
        abs_sub_lt_iff]
      have hs2 : s ^ 2 < 1 := by nlinarith [hs.1, hs.2]
      constructor <;> nlinarith [norm_nonneg d, sq_nonneg s]
    have hcU : c ∈ U := by simpa using hseg 0 (by norm_num)
    have hsub : (fun s : ℝ => c + (s : ℂ) * u) '' Ioo (-1 : ℝ) 1 ⊆ connectedComponentIn U c := by
      refine IsPreconnected.subset_connectedComponentIn
        (isPreconnected_Ioo.image _ (by fun_prop : Continuous fun s : ℝ => c + (s : ℂ) * u).continuousOn)
        ⟨0, by norm_num, by simp⟩ ?_
      rintro _ ⟨s, hs, rfl⟩; exact hseg s hs
    have hbound : ∀ w ∈ connectedComponentIn U c, ‖w‖ ≤ 2 := by
      intro w hw
      have hwU : ‖(w - a) * (w - b)‖ < 1 := by
        have := connectedComponentIn_subset U c hw
        rw [hU, mem_ofPred_eq, hev'] at this; exact this
      rw [norm_mul] at hwU
      by_cases ha : ‖w - a‖ < 1
      · have : ‖w‖ ≤ ‖w - a‖ + ‖a‖ := by
          calc ‖w‖ = ‖(w - a) + a‖ := by ring_nf
            _ ≤ _ := norm_add_le _ _
        linarith [hz 0]
      · have hb : ‖w - b‖ < 1 := by
          by_contra hb
          have := mul_le_mul (not_lt.1 ha) (not_lt.1 hb) zero_le_one (norm_nonneg _)
          linarith
        have : ‖w‖ ≤ ‖w - b‖ + ‖b‖ := by
          calc ‖w‖ = ‖(w - b) + b‖ := by ring_nf
            _ ≤ _ := norm_add_le _ _
        linarith [hz 1]
    have h4 := four_le_frontier_of_segment' (hUo.connectedComponentIn) hbound u c hun
      (fun s hs => hsub ⟨s, hs, rfl⟩)
    unfold Erdos1044.maxBoundaryLength
    exact h4.trans (le_iSup₂ (f := fun w (_ : w ∈ U) =>
      Erdos1041.length (frontier (connectedComponentIn U w))) c hcU)
  · -- the roots are antipodal: a rigid image of `X ^ 2 - 1`
    refine le_of_eq (maxBoundaryLength_congr (rig d c heq) _ _ fun v => ?_).symm
    rw [rig_apply, hev]
    have : (c + d * v - c) ^ 2 - d ^ 2 = d ^ 2 * (v ^ 2 - 1) := by ring
    rw [this, norm_mul, norm_pow, heq, one_pow, one_mul]
    simp

end OMA_E1044

open Polynomial in
theorem OMA.solution :
    ∀ (n : ℕ) (hn : n = 1 ∨ n = 2),
    IsLeast {L : ENNReal | ∃ f : Polynomial ℂ, Erdos1044.IsAdmissible f ∧ f.natDegree = n ∧
      Erdos1044.maxBoundaryLength f = L}
      (Erdos1044.maxBoundaryLength (Polynomial.X ^ n - 1)) := by
  intro n hn
  refine ⟨⟨X ^ n - 1, ?_, ?_, rfl⟩, ?_⟩
  · rcases hn with rfl | rfl
    · exact ⟨1, one_pos, fun _ => 1, fun _ => by simp, by simp⟩
    · refine ⟨2, two_pos, ![1, -1], fun i => by fin_cases i <;> simp, ?_⟩
      simp [Fin.prod_univ_two]
      ring
  · -- Port (v4.36): `natDegree_X_pow_sub_C` now takes the constant explicitly.
    rw [← map_one C]; exact natDegree_X_pow_sub_C 1
  · rintro L ⟨f, hf, hdeg, rfl⟩
    rcases hn with rfl | rfl
    · exact (OMA_E1044.degree_one hf hdeg).symm.le
    · exact OMA_E1044.degree_two hf hdeg
