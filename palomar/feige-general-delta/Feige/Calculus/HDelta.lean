module

public import Feige.Calculus.NoInteriorMin

/- Port (Palomar entry): `module` header, `public import`s and a public section added for the module system; otherwise unchanged from github.com/koolkao/feige-lean at commit 7da24abf1619706bf4f705bb24aa4d00bc63b49f. -/

@[expose] public section

/-!
# M-Calc-A: the minimization over `m` (manuscript Prop. 5.2, Ling Cor. 1.3)

For `D > 0` and real `x ≥ 1`,
`(1 - 1/(x + D))^x ≥ min (D/(1+D)) (exp (-1))`.

We work with `f(x) = x * (log (x + D - 1) - log (x + D)) = x * log (1 - 1/(x+D))` and show
`f x ≥ min (f 1) (-1)`.

* If `D ≤ 1/2`, then `f' ≥ 0` on `[1, ∞)` (using `log y ≤ (y - 1/y)/2` for `y ≥ 1`), so
  `f x ≥ f 1`.
* If `D > 1/2`, then at every point with `f'' ≥ 0` we have `f' < 0` (using the four-term
  Taylor upper bound for `log (1 - t)`), so every stationary point is a strict local maximum.
  Moreover `f N ≥ -1` for `N` large (explicitly `N (2D - 1) ≥ 2D(1-D)`), so on `[1, N]` the
  minimum is at an endpoint and `f x ≥ min (f 1) (f N) ≥ min (f 1) (-1)`.

This route avoids limits entirely.
-/

open Set Filter Topology Real

namespace Samuels

/-! ### Two elementary logarithm inequalities -/

/-- `log y ≤ (y - y⁻¹)/2` for `y ≥ 1`. -/
lemma log_le_half_sub_inv {y : ℝ} (hy : 1 ≤ y) : log y ≤ (y - y⁻¹) / 2 := by
  let φ : ℝ → ℝ := fun z => (z - z⁻¹) / 2 - log z
  have hφ : ∀ z, 0 < z → HasDerivAt φ ((1 + (z ^ 2)⁻¹) / 2 - z⁻¹) z := by
    intro z hz
    have h1 : HasDerivAt (fun z : ℝ => z⁻¹) (-(z ^ 2)⁻¹) z := hasDerivAt_inv hz.ne'
    have h3 := (((hasDerivAt_id' z).sub h1).div_const 2).sub (hasDerivAt_log hz.ne')
    exact h3.congr_deriv (by ring)
  have key : φ 1 ≤ φ y := by
    apply le_of_hasDerivAt_nonneg hy
    · intro z hz
      exact (hφ z (by linarith [hz.1])).continuousAt.continuousWithinAt
    · intro z hz
      exact hφ z (by linarith [hz.1])
    · intro z hz
      have hz0 : 0 < z := by linarith [hz.1]
      have : (1 + (z ^ 2)⁻¹) / 2 - z⁻¹ = (z - 1) ^ 2 / (2 * z ^ 2) := by
        field_simp
        ring
      rw [this]
      positivity
  have h1 : φ 1 = 0 := by simp [φ]
  simp only [φ, h1] at key
  linarith

/-- Lower bound: for `u > 1`, `log (u-1) - log u ≥ -(2u-1)/(2u(u-1))`. -/
lemma log_sub_log_ge {u : ℝ} (hu : 1 < u) :
    -(2 * u - 1) / (2 * u * (u - 1)) ≤ log (u - 1) - log u := by
  have hu0 : 0 < u := by linarith
  have hu1 : 0 < u - 1 := by linarith
  have hy : 1 ≤ u / (u - 1) := by
    rw [le_div_iff₀ hu1]; linarith
  have h := log_le_half_sub_inv hy
  rw [log_div hu0.ne' hu1.ne'] at h
  have : (u / (u - 1) - (u / (u - 1))⁻¹) / 2 = (2 * u - 1) / (2 * u * (u - 1)) := by
    field_simp
    ring
  rw [this] at h
  rw [neg_div]
  linarith

/-- Upper bound: for `u > 1`,
`log (u-1) - log u ≤ -(1/u + 1/(2u²) + 1/(3u³) + 1/(4u⁴))`. -/
lemma log_sub_log_le {u : ℝ} (hu : 1 < u) :
    log (u - 1) - log u ≤ -(1 / u + 1 / (2 * u ^ 2) + 1 / (3 * u ^ 3) + 1 / (4 * u ^ 4)) := by
  have hu0 : 0 < u := by linarith
  have hu1 : 0 < u - 1 := by linarith
  set t := 1 / u with ht
  have ht0 : 0 < t := by positivity
  have ht1 : t < 1 := by rw [ht, div_lt_one hu0]; exact hu
  have habs : |t| < 1 := by rw [abs_of_pos ht0]; exact ht1
  have hs := hasSum_pow_div_log_of_abs_lt_one habs
  have hle := sum_le_hasSum (Finset.range 4) (fun i _ => by positivity) hs
  have hlog : log (1 - t) = log (u - 1) - log u := by
    rw [← log_div hu1.ne' hu0.ne']
    congr 1
    rw [ht]
    field_simp
  rw [← hlog]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hle
  have : 1 / u + 1 / (2 * u ^ 2) + 1 / (3 * u ^ 3) + 1 / (4 * u ^ 4) =
      0 + t ^ (0 + 1) / ((0 : ℕ) + 1 : ℝ) + t ^ (1 + 1) / ((1 : ℕ) + 1 : ℝ) +
        t ^ (2 + 1) / ((2 : ℕ) + 1 : ℝ) + t ^ (3 + 1) / ((3 : ℕ) + 1 : ℝ) := by
    rw [ht]
    push_cast
    field_simp
    ring
  rw [this]
  linarith

/-! ### The function `f_D` and its derivatives -/

/-- `f_D(x) = x * log (1 - 1/(x + D))`, written as `x * (log (x+D-1) - log (x+D))`. -/
noncomputable def fD (D x : ℝ) : ℝ := x * (log (x + D - 1) - log (x + D))

/-- The first derivative of `fD`. -/
noncomputable def fD' (D x : ℝ) : ℝ :=
  (log (x + D - 1) - log (x + D)) + x / ((x + D - 1) * (x + D))

/-- The second derivative of `fD`. -/
noncomputable def fD'' (D x : ℝ) : ℝ :=
  ((2 * D - 1) * (x + D) - D) / ((x + D - 1) ^ 2 * (x + D) ^ 2)

lemma hasDerivAt_fD {D x : ℝ} (hx : 1 < x + D) : HasDerivAt (fD D) (fD' D x) x := by
  have h1 : x + D - 1 ≠ 0 := by linarith
  have h2 : x + D ≠ 0 := by linarith
  have hA : HasDerivAt (fun y => log (y + D - 1)) (1 / (x + D - 1)) x := by
    have := (((hasDerivAt_id x).add_const D).sub_const 1).log (by simpa using h1)
    simpa using this
  have hB : HasDerivAt (fun y => log (y + D)) (1 / (x + D)) x := by
    have := ((hasDerivAt_id x).add_const D).log (by simpa using h2)
    simpa using this
  have := (hasDerivAt_id' x).mul (hA.sub hB)
  show HasDerivAt (fun y => y * (log (y + D - 1) - log (y + D))) _ x
  refine this.congr_deriv ?_
  simp only [Pi.sub_apply]
  unfold fD'
  field_simp
  ring

lemma hasDerivAt_fD' {D x : ℝ} (hx : 1 < x + D) : HasDerivAt (fD' D) (fD'' D x) x := by
  have h1 : x + D - 1 ≠ 0 := by linarith
  have h2 : x + D ≠ 0 := by linarith
  have hA : HasDerivAt (fun y => log (y + D - 1)) (1 / (x + D - 1)) x := by
    have := (((hasDerivAt_id x).add_const D).sub_const 1).log (by simpa using h1)
    simpa using this
  have hB : HasDerivAt (fun y => log (y + D)) (1 / (x + D)) x := by
    have := ((hasDerivAt_id x).add_const D).log (by simpa using h2)
    simpa using this
  have hP : HasDerivAt (fun y => (y + D - 1) * (y + D)) ((x + D - 1) + (x + D)) x := by
    have := (((hasDerivAt_id' x).add_const D).sub_const 1).mul ((hasDerivAt_id' x).add_const D)
    exact this.congr_deriv (by ring)
  have hQ := (hasDerivAt_id' x).div hP (mul_ne_zero h1 h2)
  have := (hA.sub hB).add hQ
  show HasDerivAt (fun y => (log (y + D - 1) - log (y + D)) + y / ((y + D - 1) * (y + D))) _ x
  refine this.congr_deriv ?_
  unfold fD''
  field_simp
  ring

lemma continuousOn_fD {D a b : ℝ} (ha : 1 < a + D) : ContinuousOn (fD D) (Icc a b) := by
  intro x hx
  exact (hasDerivAt_fD (by linarith [hx.1])).continuousAt.continuousWithinAt

/-! ### Sign facts -/

/-- For `D ≤ 1/2`, `f_D' ≥ 0` wherever `x + D > 1` and `x ≥ 0`. -/
lemma fD'_nonneg {D x : ℝ} (hD : D ≤ 1 / 2) (_hx0 : 0 ≤ x) (hx : 1 < x + D) :
    0 ≤ fD' D x := by
  unfold fD'
  set u := x + D with hu
  have hu1 : 0 < u - 1 := by linarith
  have hu0 : 0 < u := by linarith
  have hlb := log_sub_log_ge hx
  have hxu : x = u - D := by rw [hu]; ring
  have : -(2 * u - 1) / (2 * u * (u - 1)) + x / ((u - 1) * u) =
      (1 - 2 * D) / (2 * u * (u - 1)) := by
    rw [hxu]
    field_simp
    ring
  have hpos : 0 ≤ (1 - 2 * D) / (2 * u * (u - 1)) := by
    apply div_nonneg (by linarith); positivity
  linarith

/-- For `D > 1/2`, wherever `f_D'' ≥ 0` (i.e. `(2D-1)(x+D) ≥ D`) and `x ≥ 1`, we have
`f_D' < 0`. -/
lemma fD'_neg {D x : ℝ} (hD : 1 / 2 < D) (hx : 1 ≤ x) (hsec : D ≤ (2 * D - 1) * (x + D)) :
    fD' D x < 0 := by
  unfold fD'
  set u := x + D with hu
  have hu1' : 1 < u := by linarith
  have hu1 : 0 < u - 1 := by linarith
  have hu0 : 0 < u := by linarith
  have hub := log_sub_log_le hu1'
  have hxu : x = u - D := by rw [hu]; ring
  have heq : -(1 / u + 1 / (2 * u ^ 2) + 1 / (3 * u ^ 3) + 1 / (4 * u ^ 4)) +
      x / ((u - 1) * u) =
      ((6 - 12 * D) * u ^ 3 + 2 * u ^ 2 + u + 3) / (12 * u ^ 4 * (u - 1)) := by
    rw [hxu]
    field_simp
    ring
  -- the polynomial is negative
  have hpoly : (6 - 12 * D) * u ^ 3 + 2 * u ^ 2 + u + 3 < 0 := by
    have hu_ge : 1 + D ≤ u := by linarith
    have h1 : 6 * D * u ^ 2 ≤ (12 * D - 6) * u ^ 3 := by
      have : (12 * D - 6) * u ^ 3 = 6 * ((2 * D - 1) * u) * u ^ 2 := by ring
      rw [this]
      have hu2 : 0 ≤ u ^ 2 := by positivity
      nlinarith
    have h2 : 3 * D * u ≤ 3 * (2 * D - 1) * u ^ 2 := by
      have : 3 * (2 * D - 1) * u ^ 2 = 3 * ((2 * D - 1) * u) * u := by ring
      rw [this]
      nlinarith
    have h3 : (1 + D) ^ 2 + (3 * D - 1) * (1 + D) ≤ u ^ 2 + (3 * D - 1) * u := by
      have h3a : (1 + D) ^ 2 ≤ u ^ 2 := by nlinarith
      have h3b : (3 * D - 1) * (1 + D) ≤ (3 * D - 1) * u :=
        mul_le_mul_of_nonneg_left hu_ge (by linarith)
      linarith
    have h4 : 0 < (2 * D - 1) * (2 * D + 3) := by
      apply mul_pos <;> linarith
    nlinarith
  have hden : 0 < 12 * u ^ 4 * (u - 1) := by positivity
  have := div_neg_of_neg_of_pos hpoly hden
  linarith

/-- For `D > 1/2`, every stationary point of `f_D` in `x ≥ 1` has negative second derivative. -/
lemma fD''_neg_of_stationary {D x : ℝ} (hD : 1 / 2 < D) (hx : 1 ≤ x) (hst : fD' D x = 0) :
    fD'' D x < 0 := by
  by_contra h
  push Not at h
  have hu1 : 0 < x + D - 1 := by linarith
  have hu0 : 0 < x + D := by linarith
  have hden : 0 < (x + D - 1) ^ 2 * (x + D) ^ 2 := by positivity
  unfold fD'' at h
  have hnum : 0 ≤ (2 * D - 1) * (x + D) - D := by
    by_contra hn
    push Not at hn
    have := div_neg_of_neg_of_pos hn hden
    linarith
  have := fD'_neg hD hx (by linarith)
  linarith

/-- For `D > 1/2` and `N ≥ 1` with `N (2D-1) ≥ 2D(1-D)`, we have `f_D N ≥ -1`. -/
lemma fD_ge_neg_one {D N : ℝ} (hD : 1 / 2 < D) (hN : 1 ≤ N)
    (hbig : 2 * D * (1 - D) ≤ N * (2 * D - 1)) : -1 ≤ fD D N := by
  unfold fD
  set u := N + D with hu
  have hu1' : 1 < u := by linarith
  have hu1 : 0 < u - 1 := by linarith
  have hu0 : 0 < u := by linarith
  have hlb := log_sub_log_ge hu1'
  have hN0 : 0 ≤ N := by linarith
  have h1 : N * (-(2 * u - 1) / (2 * u * (u - 1))) ≤ N * (log (u - 1) - log u) :=
    mul_le_mul_of_nonneg_left hlb hN0
  have h2 : -1 ≤ N * (-(2 * u - 1) / (2 * u * (u - 1))) := by
    have hden : 0 < 2 * u * (u - 1) := by positivity
    rw [mul_div_assoc', le_div_iff₀ hden]
    have hNu : N = u - D := by rw [hu]; ring
    rw [hNu] at hbig ⊢
    nlinarith
  linarith

/-! ### The main real inequality -/

/-- `f_D x ≥ min (f_D 1) (-1)` for all `x ≥ 1`. -/
theorem fD_ge_min {D x : ℝ} (hD : 0 < D) (hx : 1 ≤ x) : min (fD D 1) (-1) ≤ fD D x := by
  rcases le_or_gt D (1 / 2) with hD2 | hD2
  · -- monotone case
    have : fD D 1 ≤ fD D x := by
      apply le_of_hasDerivAt_nonneg hx (continuousOn_fD (by linarith))
      · intro z hz; exact hasDerivAt_fD (by linarith [hz.1])
      · intro z hz; exact fD'_nonneg hD2 (by linarith [hz.1]) (by linarith [hz.1])
    exact (min_le_left _ _).trans this
  · -- no interior minimum on `[1, N]`
    set N := max x (2 * D * (1 - D) / (2 * D - 1)) with hNdef
    have hxN : x ≤ N := le_max_left _ _
    have hN1 : 1 ≤ N := hx.trans hxN
    have hbig : 2 * D * (1 - D) ≤ N * (2 * D - 1) := by
      have h2 : 0 < 2 * D - 1 := by linarith
      have : 2 * D * (1 - D) / (2 * D - 1) ≤ N := le_max_right _ _
      rwa [div_le_iff₀ h2] at this
    have hNf := fD_ge_neg_one hD2 hN1 hbig
    have hmin := min_endpoints_le_of_stationary (g := fD D) (g' := fD' D) (g'' := fD'' D)
      (a := 1) (b := N) (continuousOn_fD (by linarith))
      (fun z hz => hasDerivAt_fD (by linarith [hz.1]))
      (fun z hz => hasDerivAt_fD' (by linarith [hz.1]))
      (fun z hz hst => fD''_neg_of_stationary hD2 hz.1.le hst) x ⟨hx, hxN⟩
    calc min (fD D 1) (-1) ≤ min (fD D 1) (fD D N) := min_le_min le_rfl hNf
      _ ≤ fD D x := hmin

/-- `(1 - 1/(x+D))^x = exp (f_D x)` for `x + D > 1`. -/
lemma rpow_eq_exp_fD {D x : ℝ} (hx : 1 < x + D) :
    (1 - 1 / (x + D)) ^ x = exp (fD D x) := by
  have h0 : 0 < x + D := by linarith
  have h1 : 0 < x + D - 1 := by linarith
  have hpos : 0 < 1 - 1 / (x + D) := by
    rw [sub_pos, div_lt_one h0]; exact hx
  rw [rpow_def_of_pos hpos, fD]
  congr 1
  have : 1 - 1 / (x + D) = (x + D - 1) / (x + D) := by field_simp
  rw [this, log_div h1.ne' h0.ne']
  ring

/-- **Prop. 5.2 (real form).** For `D > 0` and real `x ≥ 1`,
`min (D/(1+D)) (exp (-1)) ≤ (1 - 1/(x + D))^x`. -/
theorem min_le_rpow {D x : ℝ} (hD : 0 < D) (hx : 1 ≤ x) :
    min (D / (1 + D)) (exp (-1)) ≤ (1 - 1 / (x + D)) ^ x := by
  rw [rpow_eq_exp_fD (by linarith)]
  have h1 : exp (fD D 1) = D / (1 + D) := by
    have := rpow_eq_exp_fD (D := D) (x := 1) (by linarith)
    rw [← this, rpow_one]
    field_simp
    ring
  have hmono : exp (min (fD D 1) (-1)) ≤ exp (fD D x) := exp_le_exp.mpr (fD_ge_min hD hx)
  have hexpmin : exp (min (fD D 1) (-1)) = min (exp (fD D 1)) (exp (-1)) :=
    Monotone.map_min exp_monotone
  rw [hexpmin, h1] at hmono
  exact hmono

/-- **Prop. 5.2 (integer form, M-Calc-A).** For `δ > 0` and integers `m ≥ 1`,
`min (δ/(1+δ)) (exp (-1)) ≤ (1 - 1/(m + δ))^m`. -/
theorem min_le_pow {δ : ℝ} (hδ : 0 < δ) {m : ℕ} (hm : 1 ≤ m) :
    min (δ / (1 + δ)) (exp (-1)) ≤ (1 - 1 / (m + δ)) ^ m := by
  have := min_le_rpow (x := (m : ℝ)) hδ (by exact_mod_cast hm)
  rwa [rpow_natCast] at this

end Samuels

end
