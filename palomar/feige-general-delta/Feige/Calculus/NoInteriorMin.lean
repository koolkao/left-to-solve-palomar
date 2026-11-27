module

public import Mathlib

/- Port (Palomar entry): `module` header, `public import`s and a public section added for the module system; otherwise unchanged from github.com/koolkao/feige-lean at commit 7da24abf1619706bf4f705bb24aa4d00bc63b49f. -/

@[expose] public section

/-!
# One-variable calculus helpers

* `le_of_hasDerivAt_nonneg`, `lt_of_hasDerivAt_neg`: monotonicity from the sign of the
  derivative (mean value theorem).
* `min_endpoints_le_of_stationary`: if at every interior stationary point of `g` on `[a, b]`
  the second derivative is negative, then `g` has no interior minimum, so
  `min (g a) (g b) ≤ g x` for all `x ∈ [a, b]`.  This is the argument used for Ling's
  Claim 3.4 and for the minimization over `m` in Ling's Corollary 1.3.
-/

open Set Filter Topology

namespace Samuels

lemma le_of_hasDerivAt_nonneg {f f' : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hc : ContinuousOn f (Icc a b)) (hd : ∀ x ∈ Ioo a b, HasDerivAt f (f' x) x)
    (hpos : ∀ x ∈ Ioo a b, 0 ≤ f' x) : f a ≤ f b := by
  rcases hab.eq_or_lt with rfl | hlt
  · exact le_rfl
  obtain ⟨c, hc', hceq⟩ := exists_hasDerivAt_eq_slope f f' hlt hc hd
  have h0 := hpos c hc'
  rw [hceq, le_div_iff₀ (sub_pos.mpr hlt), zero_mul] at h0
  linarith

lemma lt_of_hasDerivAt_neg {f f' : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hc : ContinuousOn f (Icc a b)) (hd : ∀ x ∈ Ioo a b, HasDerivAt f (f' x) x)
    (hneg : ∀ x ∈ Ioo a b, f' x < 0) : f b < f a := by
  obtain ⟨c, hc', hceq⟩ := exists_hasDerivAt_eq_slope f f' hab hc hd
  have h0 := hneg c hc'
  rw [hceq, div_lt_iff₀ (sub_pos.mpr hab), zero_mul] at h0
  linarith

/-- No interior minimum: if at every interior stationary point the second derivative is
negative, the minimum of `g` over `[a, b]` is attained at an endpoint. -/
theorem min_endpoints_le_of_stationary {g g' g'' : ℝ → ℝ} {a b : ℝ}
    (hcont : ContinuousOn g (Icc a b))
    (hd : ∀ x ∈ Ioo a b, HasDerivAt g (g' x) x)
    (hd2 : ∀ x ∈ Ioo a b, HasDerivAt g' (g'' x) x)
    (hstat : ∀ x ∈ Ioo a b, g' x = 0 → g'' x < 0) :
    ∀ x ∈ Icc a b, min (g a) (g b) ≤ g x := by
  intro x hx
  by_contra hlt
  push Not at hlt
  obtain ⟨c, hcI, hcmin⟩ := isCompact_Icc.exists_isMinOn ⟨x, hx⟩ hcont
  have hcx : g c ≤ g x := hcmin hx
  have hca : c ≠ a := by
    rintro rfl
    have := min_le_left (g c) (g b)
    linarith
  have hcb : c ≠ b := by
    rintro rfl
    have := min_le_right (g a) (g c)
    linarith
  have hcIoo : c ∈ Ioo a b :=
    ⟨lt_of_le_of_ne hcI.1 (Ne.symm hca), lt_of_le_of_ne hcI.2 hcb⟩
  have hloc : IsLocalMin g c := hcmin.isLocalMin (Icc_mem_nhds hcIoo.1 hcIoo.2)
  have hg'c : g' c = 0 := hloc.hasDerivAt_eq_zero (hd c hcIoo)
  have hg''c : g'' c < 0 := hstat c hcIoo hg'c
  have hslope := hasDerivAt_iff_tendsto_slope.mp (hd2 c hcIoo)
  have hev : ∀ᶠ y in 𝓝[≠] c, slope g' c y < 0 :=
    hslope.eventually (gt_mem_nhds hg''c)
  have hev' : ∀ᶠ y in 𝓝[>] c, g' y < 0 := by
    filter_upwards [nhdsGT_le_nhdsNE c hev, self_mem_nhdsWithin] with y hy hyc
    rw [slope_def_field, hg'c, sub_zero] at hy
    have hpos : 0 < y - c := sub_pos.mpr hyc
    by_contra hge
    push Not at hge
    have := div_nonneg hge hpos.le
    linarith
  obtain ⟨u, hu, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hev'
  have hu' : c < u := hu
  set y := (c + min u b) / 2 with hy
  have hcm : c < min u b := lt_min hu' hcIoo.2
  have hcy : c < y := by rw [hy]; linarith
  have hyb : y < min u b := by rw [hy]; linarith
  have hyu : y < u := lt_of_lt_of_le hyb (min_le_left _ _)
  have hyb' : y < b := lt_of_lt_of_le hyb (min_le_right _ _)
  have hlt' : g y < g c := by
    apply lt_of_hasDerivAt_neg hcy
    · exact hcont.mono (Icc_subset_Icc hcI.1 hyb'.le)
    · intro z hz
      exact hd z ⟨lt_of_le_of_lt hcI.1 hz.1, lt_trans hz.2 hyb'⟩
    · intro z hz
      exact hsub ⟨hz.1, lt_trans hz.2 hyu⟩
  have := hcmin (show y ∈ Icc a b from ⟨(lt_of_le_of_lt hcI.1 hcy).le, hyb'.le⟩)
  exact absurd this (not_le.mpr hlt')

end Samuels

end
