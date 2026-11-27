/-
Copyright (c) 2026 The Tau Ceti contributors. Released under the Apache 2.0 license.
Vendored by Ming-Chih Kao (2026) from TauCeti (https://github.com/TauCetiProject/TauCeti, commit
ac8801f612041ee3dcb3fa3f950f01318206737c); see the module documentation below for what was taken
and what was changed.
-/
module

public import Mathlib

/-!
# Vendored from TauCeti: Bernstein's theorem on `[0, ∞)`

A small set of declarations from **TauCeti** (https://github.com/TauCetiProject/TauCeti, commit
ac8801f612041ee3dcb3fa3f950f01318206737c), Copyright (c) 2026 The Tau Ceti contributors, Apache 2.0:
Bernstein's theorem for functions completely monotone on `[0, ∞)`
(`TauCeti.exists_representsLaplace_of_isCompletelyMonotone`, Chafaï's approximating measures and the
Prokhorov extraction) and the definitions it needs. Only the declarations in the dependency closure
of that theorem are kept. Source files: `TauCeti/Analysis/CompletelyMonotone/` (`Basic`, `Closure`,
`Integral/Basic`, `Laplace/Kernel`, `Laplace/Representation`, `Bernstein/Measures`,
`Bernstein/Tightness`, `Bernstein/Theorem`), `TauCeti/MeasureTheory/Measure/Prokhorov`,
`TauCeti/Topology/Compactness/Compact`, `TauCeti/Topology/Order/Monotone/Convergence`,
`TauCeti/Analysis/Calculus/IteratedDeriv/Within`.

Changes: `grind`/`expose` attributes removed, a duplicate private helper dropped, five renames for
Mathlib 0df444a (`ite_eq_left`/`ite_eq_right` to `if_pos`/`if_neg`, `continuous_subtype_val` to
`continuous_subtype_val`, `Real.exp_nat_mul` to `Real.exp_nat_mul`, `propext` for a set
`EventuallyEq`) made for the Left to Solve version of this proof, and, for this Palomar entry, the
module header and a public section (Lean v4.36.0, Mathlib fc4f59e); comments marked `Port` explain
any further change.
-/

@[expose] public section

/-! ### From `TauCeti.Analysis.Calculus.IteratedDeriv.Within` -/
section
section
open Set
open scoped ContDiff Topology
section Interior
variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {g : 𝕜 → E} {s : Set 𝕜} {x : 𝕜} {n : ℕ∞ω} {k : ℕ}
/-- If `g` is `C^n` within `s` at a point `x` with `s ∈ 𝓝 x`, then for `k < n` the `k`-th
iterated derivative within `s` has derivative at `x` equal to the `(k+1)`-th iterated derivative
within `s`. -/
theorem ContDiffWithinAt.hasDerivAt_iteratedDerivWithin (hg : ContDiffWithinAt 𝕜 n g s x)
    (hk : k < n) (hx : s ∈ 𝓝 x) :
    HasDerivAt (iteratedDerivWithin k g s) (iteratedDerivWithin (k + 1) g s x) x := by
  -- Near `x` the set `s` agrees with its interior, which is open and so uniquely differentiable.
  have hu : interior s ∈ 𝓝 x := interior_mem_nhds.2 hx
  have hev (j : ℕ) : iteratedDerivWithin j g s =ᶠ[𝓝 x] iteratedDerivWithin j g (interior s) := by
    have hset : s =ᶠ[𝓝 x] interior s := by
      filter_upwards [hu] with y hy
      exact ⟨fun _ => hy, fun _ => interior_subset hy⟩
    filter_upwards [iteratedFDerivWithin_eventually_congr_set (𝕜 := 𝕜) (f := g) hset j] with y hy
    simp only [iteratedDerivWithin_eq_iteratedFDerivWithin, hy]
  have h : HasDerivAt (iteratedDerivWithin k g (interior s))
      (iteratedDerivWithin (k + 1) g (interior s) x) x := by
    rw [iteratedDerivWithin_succ]
    exact ((hg.mono interior_subset).differentiableWithinAt_iteratedDerivWithin hk
      (by
        rw [insert_eq_of_mem (mem_of_mem_nhds hu)]
        exact isOpen_interior.uniqueDiffOn)
      ).hasDerivWithinAt.hasDerivAt hu
  rw [(hev (k + 1)).eq_of_nhds]
  exact h.congr_of_eventuallyEq (hev k)

/-- If `g` is `C^n` on `s` and `s ∈ 𝓝 x`, then for `k < n` the `k`-th iterated derivative within
`s` has derivative at `x` equal to the `(k+1)`-th iterated derivative within `s`. -/
theorem ContDiffOn.hasDerivAt_iteratedDerivWithin (hg : ContDiffOn 𝕜 n g s) (hk : k < n)
    (hx : s ∈ 𝓝 x) :
    HasDerivAt (iteratedDerivWithin k g s) (iteratedDerivWithin (k + 1) g s x) x :=
  (hg x (mem_of_mem_nhds hx)).hasDerivAt_iteratedDerivWithin hk hx

end Interior
section NormedAlgebra
variable {𝕜 𝕜' E F : Type*} [NontriviallyNormedField 𝕜] [NontriviallyNormedField 𝕜']
  [NormedAlgebra 𝕜 𝕜'] [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedSpace 𝕜' E]
  [IsScalarTower 𝕜 𝕜' E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
end NormedAlgebra
end
end

/-! ### From `TauCeti.Topology.Order.Monotone.Convergence` -/
section
section
open Filter Set Topology
namespace TauCeti
variable {ι α : Type*} [Preorder ι] [TopologicalSpace α] {f : ι → α} {a : ι}
/-- **Antitone convergence on a half-line.** A function antitone and bounded below on `[a, ∞)`
tends at infinity to its infimum over `[a, ∞)`. -/
theorem tendsto_atTop_ciInf_of_antitoneOn_Ici [ConditionallyCompletePartialOrderInf α]
    [InfConvergenceClass α] (hf : AntitoneOn f (Ici a)) (hbdd : BddBelow (f '' Ici a)) :
    Tendsto f atTop (𝓝 (⨅ t : Ici a, f t)) := by
  by_cases h : (atTop : Filter ι).NeBot
  · have := (atTop_neBot_iff.1 h).2
    exact tendsto_comp_val_Ici_atTop.mp <|
      tendsto_atTop_ciInf (fun s t hst ↦ hf s.property t.property hst) (by rwa [← image_eq_range])
  · rw [not_neBot.1 h]
    exact tendsto_bot

end TauCeti
end
end

/-! ### From `TauCeti.Analysis.CompletelyMonotone.Basic` -/
section
section
open Set Filter
open scoped ContDiff Topology
open scoped Pointwise
namespace TauCeti
namespace CompletelyMonotoneOn
variable {f : ℝ → ℝ} {s : Set ℝ}
end CompletelyMonotoneOn
/-- A function `f : ℝ → ℝ` is **completely monotone** if it is `C^∞` on the closed half-line
`[0, ∞)` and its iterated derivatives within `[0, ∞)` alternate in sign:
`0 ≤ (-1)ⁿ f⁽ⁿ⁾(t)` for every `n` and every `t ≥ 0`. The smoothness clause prevents the sign
condition from being satisfied vacuously by a junk iterated derivative. -/
def IsCompletelyMonotone (f : ℝ → ℝ) : Prop :=
  ContDiffOn ℝ ∞ f (Ici 0) ∧
    ∀ n : ℕ, ∀ t : ℝ, 0 ≤ t → 0 ≤ (-1) ^ n * iteratedDerivWithin n f (Ici 0) t

namespace IsCompletelyMonotone
variable {f g : ℝ → ℝ}
/-- A completely monotone function is `C^∞` on `[0, ∞)`. -/
lemma contDiffOn (hf : IsCompletelyMonotone f) : ContDiffOn ℝ ∞ f (Ici 0) := hf.1

/-- The sign-alternation property of the iterated derivatives of a completely monotone
function: `0 ≤ (-1)ⁿ f⁽ⁿ⁾(t)` for every `n` and every `t ≥ 0`. -/
lemma neg_one_pow_mul_iteratedDerivWithin_nonneg (hf : IsCompletelyMonotone f) (n : ℕ) {t : ℝ}
    (ht : 0 ≤ t) : 0 ≤ (-1) ^ n * iteratedDerivWithin n f (Ici 0) t := hf.2 n t ht

/-- On the open half-line, the completely monotone sign condition can be read using ordinary
iterated derivatives instead of derivatives within `[0, ∞)`. -/
lemma neg_one_pow_mul_iteratedDeriv_nonneg (hf : IsCompletelyMonotone f) (n : ℕ) {t : ℝ}
    (ht : 0 < t) : 0 ≤ (-1) ^ n * iteratedDeriv n f t := by
  have hnhds : Ici (0 : ℝ) ∈ 𝓝 t :=
    mem_of_superset (isOpen_Ioi.mem_nhds ht) Ioi_subset_Ici_self
  have hcont : ContDiffAt ℝ (n : WithTop ℕ∞) f t :=
    (hf.contDiffOn.contDiffAt hnhds).of_le (by exact_mod_cast le_top)
  rw [← iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Ici 0) hcont
    (mem_Ici.mpr ht.le)]
  exact hf.neg_one_pow_mul_iteratedDerivWithin_nonneg n ht.le

/-- The derivative within `[0, ∞)` of a completely monotone function is nonpositive: it is
nonincreasing. -/
lemma derivWithin_nonpos (hf : IsCompletelyMonotone f) {t : ℝ} (ht : 0 ≤ t) :
    derivWithin f (Ici 0) t ≤ 0 := by
  have h := hf.neg_one_pow_mul_iteratedDerivWithin_nonneg 1 ht
  rw [pow_one, iteratedDerivWithin_one] at h
  linarith

end IsCompletelyMonotone
namespace IsCompletelyMonotone
variable {f g : ℝ → ℝ}
/-- For a completely monotone `f`, the `k`-th iterated derivative within `[0, ∞)` is
differentiable at any `t > 0`, with derivative the `(k+1)`-th iterated derivative. -/
lemma hasDerivAt_iteratedDerivWithin_succ
    (hcm : IsCompletelyMonotone f) (k : ℕ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (iteratedDerivWithin k f (Ici 0))
      (iteratedDerivWithin (k + 1) f (Ici 0) t) t :=
  hcm.contDiffOn.hasDerivAt_iteratedDerivWithin (mod_cast ENat.natCast_lt_top k)
    (Ici_mem_nhds ht)

end IsCompletelyMonotone
/-- Complete monotonicity on the open half-line `(0, ∞)`: the function is `C^∞` there and its
ordinary iterated derivatives alternate in sign. This is the version used for derivatives of
Bernstein functions, whose right derivatives need not be finite at `0`. -/
def IsCompletelyMonotoneOnIoi (f : ℝ → ℝ) : Prop :=
  ContDiffOn ℝ ∞ f (Ioi 0) ∧
    ∀ n : ℕ, ∀ t : ℝ, 0 < t → 0 ≤ (-1) ^ n * iteratedDeriv n f t

namespace IsCompletelyMonotoneOnIoi
variable {f g : ℝ → ℝ}
/-- A completely monotone function on `(0, ∞)` is smooth there. -/
lemma contDiffOn (hf : IsCompletelyMonotoneOnIoi f) : ContDiffOn ℝ ∞ f (Ioi 0) := hf.1

/-- The sign-alternation property on `(0, ∞)`. -/
lemma neg_one_pow_mul_iteratedDeriv_nonneg (hf : IsCompletelyMonotoneOnIoi f) (n : ℕ) {t : ℝ}
    (ht : 0 < t) : 0 ≤ (-1) ^ n * iteratedDeriv n f t := hf.2 n t ht

/-- A completely monotone function on `(0, ∞)` is nonnegative there. -/
lemma nonneg (hf : IsCompletelyMonotoneOnIoi f) {t : ℝ} (ht : 0 < t) : 0 ≤ f t := by
  simpa [iteratedDeriv_zero] using hf.neg_one_pow_mul_iteratedDeriv_nonneg 0 ht

/-- A function completely monotone on `(0, ∞)` that is continuous within `[0, ∞)` at the origin
is nonnegative on all of `[0, ∞)`: nonnegativity on `(0, ∞)` passes to the boundary point `0` in
the limit. -/
lemma nonneg_of_continuousWithinAt (hf : IsCompletelyMonotoneOnIoi f)
    (hcont : ContinuousWithinAt f (Ici 0) 0) {t : ℝ} (ht : 0 ≤ t) : 0 ≤ f t := by
  rcases ht.lt_or_eq with h | h
  · exact hf.nonneg h
  · subst h
    have htends : Filter.Tendsto f (𝓝[>] (0 : ℝ)) (nhds (f 0)) :=
      hcont.tendsto.mono_left (nhdsWithin_mono _ Ioi_subset_Ici_self)
    exact ge_of_tendsto htends (eventually_mem_nhdsWithin.mono fun x hx => hf.nonneg hx)

/-- The derivative of a completely monotone function on `(0, ∞)` is nonpositive there. -/
lemma deriv_nonpos (hf : IsCompletelyMonotoneOnIoi f) {t : ℝ} (ht : 0 < t) :
    deriv f t ≤ 0 := by
  have h := hf.neg_one_pow_mul_iteratedDeriv_nonneg 1 ht
  rw [pow_one, iteratedDeriv_one] at h
  linarith

/-- The closed-half-line Tau Ceti predicate restricts to complete monotonicity on `(0, ∞)`. -/
lemma _root_.TauCeti.IsCompletelyMonotone.isCompletelyMonotoneOnIoi
    (hf : IsCompletelyMonotone f) : IsCompletelyMonotoneOnIoi f :=
  ⟨hf.contDiffOn.mono Ioi_subset_Ici_self,
    fun n _ ht => hf.neg_one_pow_mul_iteratedDeriv_nonneg n ht⟩

end IsCompletelyMonotoneOnIoi
/-- Complete monotonicity on the closed half-line.

This is the classical finite-measure hypothesis: the function is continuous on `[0, ∞)` and
completely monotone on the open half-line `(0, ∞)`. It is weaker at the endpoint than
`IsCompletelyMonotone`, which requires all derivatives within `[0, ∞)` to exist at `0`. -/
def IsContinuousCompletelyMonotoneOnIoi (f : ℝ → ℝ) : Prop :=
  ContinuousOn f (Ici 0) ∧ IsCompletelyMonotoneOnIoi f

namespace IsContinuousCompletelyMonotoneOnIoi
variable {f g : ℝ → ℝ}
/-- A closed-half-line completely monotone function is continuous on `[0, ∞)`. -/
lemma continuousOn (hf : IsContinuousCompletelyMonotoneOnIoi f) : ContinuousOn f (Ici 0) := hf.1

/-- A closed-half-line completely monotone function is completely monotone on `(0, ∞)`. -/
lemma isCompletelyMonotoneOnIoi (hf : IsContinuousCompletelyMonotoneOnIoi f) :
    IsCompletelyMonotoneOnIoi f := hf.2

/-- The stronger predicate `IsCompletelyMonotone` implies the closed-half-line predicate. -/
lemma of_isCompletelyMonotone (hf : IsCompletelyMonotone f) :
    IsContinuousCompletelyMonotoneOnIoi f :=
  ⟨hf.contDiffOn.continuousOn, hf.isCompletelyMonotoneOnIoi⟩

/-- A closed-half-line completely monotone function is nonincreasing on `[0, ∞)`: the
derivative is nonpositive on the interior and continuity extends the monotonicity to the
endpoint. -/
lemma antitoneOn (hf : IsContinuousCompletelyMonotoneOnIoi f) : AntitoneOn f (Ici 0) := by
  refine antitoneOn_of_deriv_nonpos (convex_Ici 0) hf.continuousOn
    (by
      simpa [interior_Ici] using
        hf.isCompletelyMonotoneOnIoi.contDiffOn.differentiableOn (by simp))
    fun x hx => ?_
  rw [interior_Ici] at hx
  exact hf.isCompletelyMonotoneOnIoi.deriv_nonpos hx

/-- A closed-half-line completely monotone function is nonnegative on `[0, ∞)`:
nonnegativity on the open half-line passes to `0` by continuity. -/
lemma nonneg (hf : IsContinuousCompletelyMonotoneOnIoi f) {t : ℝ} (ht : 0 ≤ t) : 0 ≤ f t :=
  hf.isCompletelyMonotoneOnIoi.nonneg_of_continuousWithinAt
    (hf.continuousOn.continuousWithinAt (by simp)) ht

end IsContinuousCompletelyMonotoneOnIoi
/-- The `max`-truncation of a function antitone on a closed half-line is antitone everywhere:
the totalization step of the half-line limit lemma below. -/
private lemma antitone_comp_max {f : ℝ → ℝ} {a : ℝ} (hf : AntitoneOn f (Ici a)) :
    Antitone fun t : ℝ => f (max t a) := fun _ _ hab =>
  hf (mem_Ici.mpr (le_max_right _ _)) (mem_Ici.mpr (le_max_right _ _)) (max_le_max_right a hab)

/-- A function antitone on a closed half-line lies above its limit at infinity there. -/
private lemma le_of_tendsto_atTop_of_antitoneOn_Ici {f : ℝ → ℝ} {a : ℝ} (hf : AntitoneOn f (Ici a))
    {L : ℝ} (hL : Tendsto f atTop (𝓝 L)) {T : ℝ} (hT : a ≤ T) : L ≤ f T := by
  set g₀ := fun t : ℝ => f (max t a) with hg₀
  have hg_anti : Antitone g₀ := antitone_comp_max hf
  have := hg_anti.le_of_tendsto
    (hL.congr' (eventually_atTop.mpr ⟨a, fun t ht => by simp [hg₀, max_eq_left ht]⟩)) T
  simpa [hg₀, max_eq_left hT] using this

namespace IsContinuousCompletelyMonotoneOnIoi
variable {f : ℝ → ℝ}
/-- A closed-half-line completely monotone function has a limit `L ≥ 0` at infinity: it is
antitone on `[0, ∞)` and bounded below by `0`. -/
lemma exists_nonneg_tendsto_atTop (hf : IsContinuousCompletelyMonotoneOnIoi f) :
    ∃ L, Tendsto f atTop (𝓝 L) ∧ 0 ≤ L := by
  have hL := tendsto_atTop_ciInf_of_antitoneOn_Ici hf.antitoneOn
    ⟨0, by rintro y ⟨x, hx, rfl⟩; exact hf.nonneg hx⟩
  exact ⟨_, hL, ge_of_tendsto hL (eventually_atTop.mpr ⟨0, fun t ht => hf.nonneg ht⟩)⟩

/-- A closed-half-line completely monotone function lies above its limit at infinity on
`[0, ∞)`. -/
lemma le_of_tendsto_atTop (hcm : IsContinuousCompletelyMonotoneOnIoi f) {L : ℝ}
    (hL : Tendsto f atTop (𝓝 L)) {T : ℝ} (hT : 0 ≤ T) : L ≤ f T :=
  le_of_tendsto_atTop_of_antitoneOn_Ici hcm.antitoneOn hL hT

end IsContinuousCompletelyMonotoneOnIoi
namespace IsCompletelyMonotone
variable {f : ℝ → ℝ}
end IsCompletelyMonotone
end TauCeti
end
end

/-! ### From `TauCeti.Analysis.CompletelyMonotone.Closure` -/
section
section
open Set
open scoped ContDiff
namespace TauCeti
namespace IsCompletelyMonotone
variable {f g : ℝ → ℝ}
/-- Every alternating iterated derivative of a completely monotone function is completely
monotone. -/
theorem neg_one_pow_mul_iteratedDerivWithin (hf : IsCompletelyMonotone f) (k : ℕ) :
    IsCompletelyMonotone (fun t => (-1 : ℝ) ^ k * iteratedDerivWithin k f (Ici 0) t) := by
  have hu : UniqueDiffOn ℝ (Ici (0 : ℝ)) := uniqueDiffOn_Ici 0
  have hcont : ContDiffOn ℝ ∞ (iteratedDerivWithin k f (Ici 0)) (Ici 0) := by
    induction k with
    | zero => simpa [iteratedDerivWithin_zero] using hf.contDiffOn
    | succ k ih =>
        simpa [iteratedDerivWithin_succ] using ih.derivWithin (m := ∞) hu (by simp)
  refine ⟨?_, fun n t ht => ?_⟩
  · simpa [smul_eq_mul] using hcont.const_smul ((-1 : ℝ) ^ k)
  have hshift :
      iteratedDerivWithin n (iteratedDerivWithin k f (Ici 0)) (Ici 0) =
        iteratedDerivWithin (n + k) f (Ici 0) := by
    induction n with
    | zero => simp [iteratedDerivWithin_zero]
    | succ n ih =>
        rw [iteratedDerivWithin_succ, ih, ← iteratedDerivWithin_succ]
        congr 1
        omega
  have hsign := hf.neg_one_pow_mul_iteratedDerivWithin_nonneg (n + k) ht
  have hiter :
      iteratedDerivWithin n
          (fun t => (-1 : ℝ) ^ k * iteratedDerivWithin k f (Ici 0) t) (Ici 0) t =
        (-1 : ℝ) ^ k * iteratedDerivWithin (n + k) f (Ici 0) t := by
    rw [iteratedDerivWithin_const_mul_field, hshift]
  rw [hiter]
  have key :
      (-1 : ℝ) ^ n * ((-1 : ℝ) ^ k * iteratedDerivWithin (n + k) f (Ici 0) t) =
        (-1 : ℝ) ^ (n + k) * iteratedDerivWithin (n + k) f (Ici 0) t := by
    rw [pow_add]
    ring
  rwa [key]

/-- The negated derivative within `[0, ∞)` of a completely monotone function is completely
monotone. -/
theorem neg_derivWithin (hf : IsCompletelyMonotone f) :
    IsCompletelyMonotone (fun t => -derivWithin f (Ici 0) t) := by
  simpa [pow_one, iteratedDerivWithin_one] using hf.neg_one_pow_mul_iteratedDerivWithin 1

end IsCompletelyMonotone
end TauCeti
end
end

/-! ### From `TauCeti.Analysis.CompletelyMonotone.Integral.Basic` -/
section
section
open MeasureTheory Set intervalIntegral Filter
open scoped ContDiff Topology
namespace TauCeti
variable {f : ℝ → ℝ}
private lemma nat_le_top (n : ℕ) : (n : WithTop ℕ∞) ≤ ∞ := by exact_mod_cast le_top

/-- For a completely monotone function the `n`-th iterated derivative within a compact interval
`[x, T]` agrees with the one taken within the half-line `[0, ∞)` at any strictly positive interior
point. Complete monotonicity supplies the local `ContDiffAt` hypothesis, and both sides reduce to
the unrestricted iterated derivative at `t`. -/
private lemma IsCompletelyMonotone.iteratedDerivWithin_Icc_eq_Ici (hf : IsCompletelyMonotone f)
    {x T t : ℝ} {n : ℕ} (ht_pos : 0 < t) (ht : t ∈ Ioo x T) :
    iteratedDerivWithin n f (Icc x T) t = iteratedDerivWithin n f (Ici 0) t := by
  have hcont : ContDiffAt ℝ (n : WithTop ℕ∞) f t :=
    (hf.contDiffOn.contDiffAt (Ici_mem_nhds ht_pos)).of_le (nat_le_top _)
  have hxT : x < T := lt_trans ht.1 ht.2
  rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc hxT) hcont
        (Ioo_subset_Icc_self ht),
      ← iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Ici 0) hcont
        (mem_Ici.mpr ht_pos.le)]

namespace IsCompletelyMonotone
end IsCompletelyMonotone
/-- The first iterated derivative within `[0, ∞)` of a completely monotone function is
nonpositive (the `derivWithin` sign condition restated for `iteratedDerivWithin 1`). -/
private lemma IsCompletelyMonotone.iteratedDerivWithin_one_nonpos
    (hf : IsCompletelyMonotone f) {t : ℝ} (ht : 0 ≤ t) :
    iteratedDerivWithin 1 f (Ici 0) t ≤ 0 := by
  rw [iteratedDerivWithin_one]; exact hf.derivWithin_nonpos ht

/-- Every iterated derivative within `[0, ∞)` of a completely monotone function is continuous on
the interval spanned by any two nonnegative endpoints. The endpoints need no ordering: `uIcc` is
the unordered interval, and `[0, ∞)` is order-connected. -/
lemma IsCompletelyMonotone.continuousOn_iteratedDerivWithin_uIcc (hcm : IsCompletelyMonotone f)
    (m : ℕ) {x T : ℝ} (hx : 0 ≤ x) (hT : 0 ≤ T) :
    ContinuousOn (iteratedDerivWithin m f (Ici 0)) (uIcc x T) :=
  (hcm.contDiffOn.continuousOn_iteratedDerivWithin (nat_le_top m)
    (uniqueDiffOn_Ici 0)).mono (ordConnected_Ici.uIcc_subset hx hT)

/-- On a compact interval in `[0, ∞)`, the integral of `-f'` for a completely monotone
function is the endpoint drop, with the derivative taken within `[0, ∞)`. -/
lemma IsCompletelyMonotone.integral_neg_iteratedDerivWithin_one_Ici_eq_sub
    (hcm : IsCompletelyMonotone f) {x T : ℝ} (hx : 0 ≤ x) (hxT : x ≤ T) :
    ∫ t in x..T, -iteratedDerivWithin 1 f (Ici 0) t = f x - f T := by
  by_cases h_eq : x = T
  · subst T
    simp
  have htransfer :
      ∫ t in x..T, -iteratedDerivWithin 1 f (Icc x T) t =
      ∫ t in x..T, -iteratedDerivWithin 1 f (Ici 0) t := by
    apply intervalIntegral.integral_congr_uIoo
    intro t ht
    rw [uIoo_of_le hxT] at ht
    have ht_pos : 0 < t := lt_of_le_of_lt hx ht.1
    exact congrArg Neg.neg (hcm.iteratedDerivWithin_Icc_eq_Ici ht_pos ht)
  rw [← htransfer]
  simpa [iteratedDerivWithin_one, intervalIntegral.integral_neg, neg_sub] using
    congrArg Neg.neg (intervalIntegral.integral_derivWithin_Icc_of_contDiffOn_Icc
      ((hcm.contDiffOn.mono
        (Icc_subset_Ici_self.trans (Ici_subset_Ici.mpr hx))).of_le (nat_le_top _)) hxT)

/-- The improper integral `∫ₓ^∞ (-f') dt = f x - L` from an arbitrary nonnegative endpoint `x`,
for a completely monotone function with limit `L` at infinity. -/
lemma IsCompletelyMonotone.integral_Ioi_neg_iteratedDerivWithin_one_of_nonneg
    (hcm : IsCompletelyMonotone f) {x : ℝ} (hx : 0 ≤ x) {L : ℝ} (hL : Tendsto f atTop (nhds L)) :
    ∫ t in Ioi x, -iteratedDerivWithin 1 f (Ici 0) t = f x - L := by
  have hcont : ContinuousWithinAt f (Ici x) x :=
    (hcm.contDiffOn.continuousOn.continuousWithinAt hx).mono (Ici_subset_Ici.mpr hx)
  have hderiv : ∀ t ∈ Ioi x, HasDerivAt f (iteratedDerivWithin 1 f (Ici 0) t) t :=
    fun t ht => hcm.hasDerivAt_iteratedDerivWithin_succ 0 (hx.trans_lt ht)
  have hneg : ∀ t ∈ Ioi x, iteratedDerivWithin 1 f (Ici 0) t ≤ 0 :=
    fun t ht => hcm.iteratedDerivWithin_one_nonpos (hx.trans ht.le)
  have hFTC : ∫ t in Ioi x, iteratedDerivWithin 1 f (Ici 0) t = L - f x :=
    integral_Ioi_of_hasDerivAt_of_nonpos hcont hderiv hneg hL
  rw [MeasureTheory.integral_neg, hFTC]
  ring

end TauCeti
end
end

/-! ### From `TauCeti.Analysis.CompletelyMonotone.Laplace.Kernel` -/
section
section
open Filter MeasureTheory ProbabilityTheory
open scoped BoundedContinuousFunction ENNReal NNReal Topology
namespace NNReal
end NNReal
namespace TauCeti
/-- The Laplace kernel `p ↦ e^{-tp}` is continuous in the coordinate variable. -/
lemma continuous_exp_neg_mul (t : ℝ) :
    Continuous fun x : ℝ≥0 => Real.exp (-(t * (x : ℝ))) := by
  fun_prop

/-- For `0 ≤ x` the Laplace kernel is bounded by `1` on `ℝ≥0`. -/
lemma exp_neg_mul_le_one {x : ℝ} (hx : 0 ≤ x) (p : ℝ≥0) :
    Real.exp (-(x * (p : ℝ))) ≤ 1 :=
  Real.exp_le_one_iff.mpr <| neg_nonpos.mpr <| by positivity

/-- The Laplace kernel as a bundled bounded continuous test function of the nonnegative
variable `p`, for fixed nonnegative `x`. -/
noncomputable def laplaceKernelBoundedContinuous {x : ℝ} (hx : 0 ≤ x) : ℝ≥0 →ᵇ ℝ :=
  .ofNormedAddCommGroup (fun p => Real.exp (-(x * (p : ℝ)))) (continuous_exp_neg_mul x) 1
    fun p => by simpa [Real.norm_eq_abs] using exp_neg_mul_le_one hx p

/-- The bundled Laplace kernel evaluates to the usual exponential kernel on `ℝ≥0`. -/
@[simp]
lemma laplaceKernelBoundedContinuous_apply {x : ℝ} (hx : 0 ≤ x) (p : ℝ≥0) :
    laplaceKernelBoundedContinuous hx p = Real.exp (-(x * (p : ℝ))) :=
  (rfl)

/-- **The Laplace kernel is integrable against a finite measure.** For `0 ≤ x` the kernel
`p ↦ e^{-xp}` is bounded and continuous on `ℝ≥0`, hence integrable against any finite measure. -/
lemma integrable_exp_neg_mul (μ : Measure ℝ≥0) [IsFiniteMeasure μ] {x : ℝ} (hx : 0 ≤ x) :
    Integrable (fun p : ℝ≥0 => Real.exp (-(x * (p : ℝ)))) μ := by
  have h := (laplaceKernelBoundedContinuous hx).integrable μ
  rwa [funext (laplaceKernelBoundedContinuous_apply hx)] at h

section Transform
end Transform
end TauCeti
namespace ProbabilityTheory.Kernel
variable {V : Type*} [MeasurableSpace V]
end ProbabilityTheory.Kernel
end
end

/-! ### From `TauCeti.Analysis.CompletelyMonotone.Bernstein.Measures` -/
section
section
open MeasureTheory Set intervalIntegral Filter
open scoped BoundedContinuousFunction ContDiff NNReal Topology
namespace TauCeti
variable {f : ℝ → ℝ}

/-- The density `ρ_n(t) = (-1)ⁿ/(n-1)! · tⁿ⁻¹ · f⁽ⁿ⁾(t)` for nonzero `n`, used for the `n`-th
approximating measure in the Bernstein proof (Chafaï 2013). By convention the `n = 0` branch
returns `0`. -/
noncomputable def chafaiDensity (f : ℝ → ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  if n = 0 then 0
  else (-1 : ℝ) ^ n / (Nat.factorial (n - 1) : ℝ) *
    t ^ (n - 1) * iteratedDerivWithin n f (Ici 0) t

/-- `chafaiDensity f 0 = 0`. -/
@[simp] lemma chafaiDensity_zero (f : ℝ → ℝ) (t : ℝ) : chafaiDensity f 0 t = 0 := by
  rw [chafaiDensity, ite_eq_left rfl]

/-- The defining formula for `chafaiDensity` at a nonzero order. -/
@[simp]
lemma chafaiDensity_of_ne_zero {n : ℕ} (hn : n ≠ 0) (f : ℝ → ℝ) (t : ℝ) :
    chafaiDensity f n t = (-1 : ℝ) ^ n / (Nat.factorial (n - 1) : ℝ) *
      t ^ (n - 1) * iteratedDerivWithin n f (Ici 0) t := by
  rw [chafaiDensity, ite_eq_right hn]

/-- `chafaiDensity f n` is continuous on `[0, ∞)` when `f` has `n` continuous derivatives
there. -/
lemma continuousOn_chafaiDensity {n : ℕ} (hf : ContDiffOn ℝ (n : WithTop ℕ∞) f (Ici 0)) :
    ContinuousOn (chafaiDensity f n) (Ici 0) := by
  by_cases hn : n = 0
  · subst n
    have hzero : chafaiDensity f 0 = fun _ : ℝ => 0 := funext (chafaiDensity_zero f)
    rw [hzero]
    exact continuousOn_const
  have heq : chafaiDensity f n = fun t => (-1 : ℝ) ^ n / (Nat.factorial (n - 1) : ℝ) *
      t ^ (n - 1) * iteratedDerivWithin n f (Ici 0) t :=
    funext (chafaiDensity_of_ne_zero hn f)
  rw [heq]
  exact (continuousOn_const.mul (continuous_pow _).continuousOn).mul
    (hf.continuousOn_iteratedDerivWithin le_rfl (uniqueDiffOn_Ici 0))

/-- The `n`-th Chafaï approximating measure `σ_n` for the Bernstein representation, with density
`ρ_n` on
`(0, ∞)`. -/
noncomputable def chafaiMeasure (f : ℝ → ℝ) (n : ℕ) : Measure ℝ :=
  (volume.restrict (Ioi 0)).withDensity (fun t => ENNReal.ofReal (chafaiDensity f n t))

/-- `chafaiMeasure` as a `withDensity`, exposed as a lemma rather than an unfoldable body. -/
lemma chafaiMeasure_eq_withDensity (f : ℝ → ℝ) (n : ℕ) :
    chafaiMeasure f n =
      (volume.restrict (Ioi 0)).withDensity (fun t => ENNReal.ofReal (chafaiDensity f n t)) := by
  rw [chafaiMeasure]

/-- The mass `chafaiMeasure f n` assigns to a measurable set, as a set lintegral of the density. -/
@[simp]
lemma chafaiMeasure_apply (f : ℝ → ℝ) (n : ℕ) {s : Set ℝ} (hs : MeasurableSet s) :
    chafaiMeasure f n s =
      ∫⁻ t in s, ENNReal.ofReal (chafaiDensity f n t) ∂(volume.restrict (Ioi 0)) := by
  rw [chafaiMeasure, withDensity_apply _ hs]

/-- The density `ρ_n(t)` is nonnegative when `t ≥ 0` and the `n`-th derivative has the
alternating sign at `t`. -/
lemma chafaiDensity_nonneg {n : ℕ} {t : ℝ} (ht : 0 ≤ t)
    (hsign : 0 ≤ (-1 : ℝ) ^ n * iteratedDerivWithin n f (Ici 0) t) :
    0 ≤ chafaiDensity f n t := by
  simp only [chafaiDensity]
  split_ifs with hn
  · exact le_refl 0
  · have hfact_pos : (0 : ℝ) < ↑(Nat.factorial (n - 1)) :=
      Nat.cast_pos.mpr (Nat.factorial_pos _)
    calc (-1 : ℝ) ^ n / ↑(Nat.factorial (n - 1)) * t ^ (n - 1) *
          iteratedDerivWithin n f (Ici 0) t
        = t ^ (n - 1) / ↑(Nat.factorial (n - 1)) *
          ((-1 : ℝ) ^ n * iteratedDerivWithin n f (Ici 0) t) := by field_simp
      _ ≥ 0 := mul_nonneg (div_nonneg (pow_nonneg ht _) hfact_pos.le) hsign

/-- For `n = 1`, the density simplifies to `-f'(t)`. -/
lemma chafaiDensity_one (t : ℝ) :
    chafaiDensity f 1 t = -iteratedDerivWithin 1 f (Ici 0) t := by
  simp [chafaiDensity]

/-- Difference of two successive Chafaï densities, in the algebraic form used by integration by
parts. -/
private lemma chafaiDensity_succ_succ_sub_succ (f : ℝ → ℝ) (m : ℕ) (t : ℝ) :
    chafaiDensity f (m + 2) t - chafaiDensity f (m + 1) t =
      ↑(m + 1) * t ^ m *
          (((-1 : ℝ) ^ (m + 2) / ↑(m + 1).factorial) *
            iteratedDerivWithin (m + 1) f (Ici 0) t) +
        t ^ (m + 1) *
          (((-1 : ℝ) ^ (m + 2) / ↑(m + 1).factorial) *
            iteratedDerivWithin (m + 2) f (Ici 0) t) := by
  -- Put both densities into their nonzero defining branches.
  have hm2 : m + 2 ≠ 0 := by omega
  have hm1 : m + 1 ≠ 0 := by omega
  have hdens_m2 :
      chafaiDensity f (m + 2) t =
        (-1 : ℝ) ^ (m + 2) / ((m + 1).factorial : ℝ) *
          t ^ (m + 1) * iteratedDerivWithin (m + 2) f (Ici 0) t := by
    rw [chafaiDensity_of_ne_zero hm2]
    norm_num
  have hdens_m1 :
      chafaiDensity f (m + 1) t =
        (-1 : ℝ) ^ (m + 1) / (m.factorial : ℝ) *
          t ^ m * iteratedDerivWithin (m + 1) f (Ici 0) t := by
    rw [chafaiDensity_of_ne_zero hm1]
    norm_num
  rw [hdens_m2, hdens_m1]
  -- Move the two factorial denominators to the same `(m + 1)!` denominator and normalize the
  -- alternating sign.
  have hfact : ((m + 1).factorial : ℝ) = ((m + 1 : ℕ) : ℝ) * ↑m.factorial := by
    rw [Nat.factorial_succ]
    push_cast
    ring
  rw [hfact]
  have hfact_ne : (m.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have _ : ((m : ℝ) + 1) ≠ 0 := by positivity
  have hneg : (-1 : ℝ) ^ (m + 2) = (-1) ^ (m + 1) * (-1) := pow_succ (-1) (m + 1)
  rw [hneg]
  field_simp
  ring

/-- The Bernstein kernel `φ_n(x,p) = max(1 - xp/(n-1), 0)ⁿ⁻¹` for `n ≥ 2`. After the change of
variable `p = (n-1)/t`, the Taylor integral kernel on `[0, T]` becomes `φ_n(x, p)`, which
converges pointwise to `e^{-xp}` as `n → ∞` (the classical `(1-x/n)ⁿ → e^{-x}` limit). -/
noncomputable def bernsteinKernel (n : ℕ) (x p : ℝ) : ℝ :=
  if n ≤ 1 then 0 else (max (1 - x * p / (↑(n - 1) : ℝ)) 0) ^ (n - 1)

/-- The defining formula for the Bernstein kernel at `2 ≤ n`. -/
@[simp]
lemma bernsteinKernel_of_two_le {n : ℕ} (hn : 2 ≤ n) (x p : ℝ) :
    bernsteinKernel n x p = (max (1 - x * p / (↑(n - 1) : ℝ)) 0) ^ (n - 1) := by
  have hnle : ¬ n ≤ 1 := by omega
  rw [bernsteinKernel, ite_eq_right hnle]

/-- The Bernstein kernel is continuous in `p` for fixed `n` and `x`. -/
lemma continuous_bernsteinKernel (n : ℕ) (x : ℝ) : Continuous (bernsteinKernel n x) := by
  unfold bernsteinKernel
  split_ifs <;> fun_prop

/-- The Bernstein kernel is nonnegative. -/
@[simp] lemma bernsteinKernel_nonneg (n : ℕ) (x p : ℝ) : 0 ≤ bernsteinKernel n x p := by
  rw [bernsteinKernel]; split_ifs <;> positivity

/-- On the nonnegative half-plane, the Bernstein kernel is bounded above by `1`. -/
lemma bernsteinKernel_le_one {n : ℕ} {x p : ℝ} (hx : 0 ≤ x) (hp : 0 ≤ p) :
    bernsteinKernel n x p ≤ 1 := by
  rw [bernsteinKernel]
  split_ifs with hn
  · norm_num
  · have hn_pos : (0 : ℝ) < (↑(n - 1) : ℝ) := Nat.cast_pos.mpr (by omega)
    have hratio_nonneg : 0 ≤ x * p / (↑(n - 1) : ℝ) :=
      div_nonneg (mul_nonneg hx hp) hn_pos.le
    have hbase_nonneg : 0 ≤ max (1 - x * p / (↑(n - 1) : ℝ)) 0 := le_max_right _ _
    have hbase_le_one : max (1 - x * p / (↑(n - 1) : ℝ)) 0 ≤ 1 := by
      exact max_le (by linarith) zero_le_one
    exact pow_le_one₀ hbase_nonneg hbase_le_one

/-- The Bernstein kernel as a bundled bounded continuous test function of the nonnegative
variable `p`, for fixed `n` and nonnegative `x`. -/
noncomputable def bernsteinKernelBoundedContinuous (n : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    ℝ≥0 →ᵇ ℝ where
  toFun := fun p => bernsteinKernel n x (p : ℝ)
  continuous_toFun := (continuous_bernsteinKernel n x).comp continuous_subtype_val
  map_bounded' :=
    ⟨1, fun p q => by
      rw [Real.dist_eq]
      have hp0 : 0 ≤ bernsteinKernel n x (p : ℝ) := bernsteinKernel_nonneg n x (p : ℝ)
      have hp1 : bernsteinKernel n x (p : ℝ) ≤ 1 := bernsteinKernel_le_one hx p.property
      have hq0 : 0 ≤ bernsteinKernel n x (q : ℝ) := bernsteinKernel_nonneg n x (q : ℝ)
      have hq1 : bernsteinKernel n x (q : ℝ) ≤ 1 := bernsteinKernel_le_one hx q.property
      exact abs_sub_le_iff.mpr ⟨by linarith, by linarith⟩⟩

/-- The bundled Bernstein kernel evaluates to the unbundled kernel on `ℝ≥0`. -/
@[simp]
lemma bernsteinKernelBoundedContinuous_apply (n : ℕ) {x : ℝ} (hx : 0 ≤ x) (p : ℝ≥0) :
    bernsteinKernelBoundedContinuous n hx p = bernsteinKernel n x (p : ℝ) := by
  rw [bernsteinKernelBoundedContinuous]; rfl

/-- **The Bernstein kernel at a nonnegative point is integrable against a finite measure.** For
`0 ≤ x`, the map `p ↦ bernsteinKernel n x p` is integrable against any finite measure on `ℝ≥0`.
The companion of `TauCeti.integrable_exp_neg_mul`, which says the same of the Laplace kernel. -/
lemma integrable_bernsteinKernel (μ : Measure ℝ≥0) [IsFiniteMeasure μ] (n : ℕ) {x : ℝ}
    (hx : 0 ≤ x) : Integrable (fun p : ℝ≥0 => bernsteinKernel n x (p : ℝ)) μ := by
  have h := (bernsteinKernelBoundedContinuous n hx).integrable μ
  rwa [funext (bernsteinKernelBoundedContinuous_apply n hx)] at h

/-- **An atom at `0` shifts the Laplace transform by its mass.** The kernel takes the value `1` at
`p = 0`, so adjoining `c • δ₀` to a finite measure adds exactly `c`. -/
@[simp]
lemma integral_exp_neg_mul_add_smul_dirac_zero (μ : Measure ℝ≥0) [IsFiniteMeasure μ] (c : ℝ≥0)
    {x : ℝ} (hx : 0 ≤ x) :
    ∫ p : ℝ≥0, Real.exp (-(x * (p : ℝ))) ∂(μ + c • Measure.dirac (0 : ℝ≥0))
      = (∫ p : ℝ≥0, Real.exp (-(x * (p : ℝ))) ∂μ) + c := by
  rw [integral_add_measure (integrable_exp_neg_mul μ hx)
      (integrable_exp_neg_mul (c • Measure.dirac (0 : ℝ≥0)) hx),
    integral_smul_nnreal_measure, integral_dirac]
  simp [NNReal.smul_def]

/-- The Bernstein kernel is measurable in `p` for fixed `n` and `x`. -/
lemma measurable_bernsteinKernel (n : ℕ) (x : ℝ) : Measurable (bernsteinKernel n x) := by
  unfold bernsteinKernel; split_ifs
  · exact measurable_const
  · fun_prop

/-- The rescaling map `t ↦ max ((n-1)/t) 0`, valued in `ℝ≥0`. -/
noncomputable def chafaiRescaling (n : ℕ) (t : ℝ) : ℝ≥0 :=
  Real.toNNReal (((n : ℝ) - 1) / t)

/-- The rescaling map `t ↦ max ((n-1)/t) 0`, valued in `ℝ≥0`, is measurable. -/
lemma measurable_chafaiRescaling (n : ℕ) :
    Measurable (chafaiRescaling n) :=
  continuous_real_toNNReal.measurable.comp (measurable_const.div measurable_id)

/-- On the nonnegative part of the source, the `ℝ≥0` rescaling coerces back to `(n-1)/t`. -/
@[simp]
lemma chafaiRescaling_coe_of_nonneg {n : ℕ} (hn : 1 ≤ n) {t : ℝ} (ht : 0 ≤ t) :
    (chafaiRescaling n t : ℝ) = ((n : ℝ) - 1) / t := by
  have hnum : 0 ≤ (n : ℝ) - 1 := by
    exact sub_nonneg.mpr (by exact_mod_cast hn)
  have hnonneg : 0 ≤ ((n : ℝ) - 1) / t := div_nonneg hnum ht
  simp [chafaiRescaling, Real.coe_toNNReal', max_eq_left hnonneg]

/-- The rescaled measure `σ̃_n`: pushforward of `chafaiMeasure f n` under the `ℝ≥0` rescaling. -/
noncomputable def chafaiRescaled (f : ℝ → ℝ) (n : ℕ) : Measure ℝ≥0 :=
  Measure.map (chafaiRescaling n) (chafaiMeasure f n)

/-- `chafaiRescaled` as a pushforward, exposed as a lemma rather than an unfoldable body. -/
lemma chafaiRescaled_eq_map (f : ℝ → ℝ) (n : ℕ) :
    chafaiRescaled f n = Measure.map (chafaiRescaling n) (chafaiMeasure f n) := by
  rw [chafaiRescaled]

/-- Integrating against `chafaiRescaled f n` is integrating the pullback along the Chafaï
rescaling against `chafaiMeasure f n`. -/
lemma chafaiRescaled_integral (f : ℝ → ℝ) (n : ℕ) {g : ℝ≥0 → ℝ}
    (hg : AEStronglyMeasurable g (chafaiRescaled f n)) :
    ∫ x, g x ∂(chafaiRescaled f n) =
      ∫ t, g (chafaiRescaling n t) ∂(chafaiMeasure f n) := by
  rw [chafaiRescaled_eq_map] at hg ⊢
  exact MeasureTheory.integral_map (measurable_chafaiRescaling n).aemeasurable hg

/-- On positive source points, pulling the Bernstein kernel back along the Chafaï rescaling
gives the classical finite-order kernel `(max (1 - x / t) 0) ^ (n - 1)`. -/
lemma bernsteinKernel_chafaiRescaling_of_pos {n : ℕ} (hn : 2 ≤ n) (x : ℝ) {t : ℝ} (ht : 0 < t) :
    bernsteinKernel n x (chafaiRescaling n t : ℝ) = (max (1 - x / t) 0) ^ (n - 1) := by
  rw [bernsteinKernel_of_two_le hn]
  rw [chafaiRescaling_coe_of_nonneg (by omega : 1 ≤ n) ht.le]
  congr 2
  have hcast : ((n : ℝ) - 1) = (↑(n - 1) : ℝ) := by
    norm_num [Nat.cast_sub (by omega : 1 ≤ n)]
  have hn1 : (↑(n - 1) : ℝ) ≠ 0 := by
    exact_mod_cast (by omega : n - 1 ≠ 0)
  rw [hcast]
  field_simp [hn1, ht.ne']

/-- Pushforward preserves total mass. -/
lemma chafaiRescaled_mass_eq (f : ℝ → ℝ) (n : ℕ) :
    (chafaiRescaled f n) univ = (chafaiMeasure f n) univ := by
  unfold chafaiRescaled
  rw [Measure.map_apply (measurable_chafaiRescaling n) MeasurableSet.univ, Set.preimage_univ]

private lemma aemeasurable_chafaiDensity_ofReal (f : ℝ → ℝ) (hcm : IsCompletelyMonotone f) (n : ℕ) :
    AEMeasurable (fun t => ENNReal.ofReal (chafaiDensity f n t))
      (volume.restrict (Ioi 0)) := by
  have hcont : ContinuousOn (chafaiDensity f n) (Ici 0) :=
    continuousOn_chafaiDensity (n := n) (hcm.contDiffOn.of_le (nat_le_top n))
  exact ((hcont.mono Ioi_subset_Ici_self).aemeasurable measurableSet_Ioi).ennreal_ofReal

private lemma chafaiDensity_neg_derivWithin_pred (f : ℝ → ℝ)
    {n : ℕ} (hn : 2 ≤ n) {t : ℝ} (ht : 0 < t) :
    chafaiDensity (fun t => -derivWithin f (Ici 0) t) (n - 1) t =
      ((n : ℝ) - 1) / t * chafaiDensity f n t := by
  have hn0 : n ≠ 0 := by omega
  have hn10 : n - 1 ≠ 0 := by omega
  rw [chafaiDensity_of_ne_zero hn10, chafaiDensity_of_ne_zero hn0]
  have hiter : iteratedDerivWithin (n - 1)
        (fun t => -derivWithin f (Ici 0) t) (Ici 0) t =
      -iteratedDerivWithin n f (Ici 0) t := by
    -- The negated function elaborates as negation of `derivWithin`; expose that defeq.
    change iteratedDerivWithin (n - 1) (-(derivWithin f (Ici 0))) (Ici 0) t =
      -iteratedDerivWithin n f (Ici 0) t
    rw [iteratedDerivWithin_neg]
    congr 1
    rw [← iteratedDerivWithin_succ']
    congr 1
    omega
  rw [hiter]
  have hfact : ((n - 1).factorial : ℝ) =
      ((n - 1 : ℕ) : ℝ) * ((n - 2).factorial : ℝ) := by
    rw [show n - 1 = (n - 2) + 1 by omega, Nat.factorial_succ]
    norm_num
  rw [hfact]
  have hnp : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    norm_num [Nat.cast_sub (by omega : 1 ≤ n)]
  have hsub : n - 1 - 1 = n - 2 := by omega
  have hpow' : t ^ (n - 2) * t = t ^ (n - 1) := by
    rw [show n - 1 = (n - 2) + 1 by omega, pow_succ]
  have hsign : -((-1 : ℝ) ^ (n - 1)) = (-1 : ℝ) ^ n := by
    have hpow : ((-1 : ℝ) ^ n) = (-1 : ℝ) ^ ((n - 1) + 1) := by
      congr
      omega
    rw [hpow, pow_succ]
    ring
  have hden : (n : ℝ) - 1 ≠ 0 := by
    have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
    nlinarith
  rw [hnp, hsub]
  field_simp [ht.ne', hden]
  rw [← hsign, ← hpow']
  ring

private lemma chafaiRescaled_lintegral_coe_eq_chafaiMeasure_neg_derivWithin
    (f : ℝ → ℝ) (hcm : IsCompletelyMonotone f) {n : ℕ} (hn : 2 ≤ n) :
    ∫⁻ p : ℝ≥0, ENNReal.ofReal (p : ℝ) ∂(chafaiRescaled f n) =
      (chafaiMeasure (fun t => -derivWithin f (Ici 0) t) (n - 1)) univ := by
  rw [chafaiRescaled_eq_map]
  rw [lintegral_map]
  swap
  · exact ENNReal.measurable_ofReal.comp (by fun_prop : Measurable fun p : ℝ≥0 => (p : ℝ))
  swap
  · exact measurable_chafaiRescaling n
  rw [chafaiMeasure_eq_withDensity]
  rw [lintegral_withDensity_eq_lintegral_mul₀]
  swap
  · exact aemeasurable_chafaiDensity_ofReal f hcm n
  swap
  · exact ((NNReal.continuous_coe.measurable.comp (measurable_chafaiRescaling n)).aemeasurable)
      |>.ennreal_ofReal
  rw [chafaiMeasure_eq_withDensity, withDensity_apply _ MeasurableSet.univ]
  simp only [Measure.restrict_univ]
  refine lintegral_congr_ae ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have htpos : 0 < t := ht
  have hscale : (chafaiRescaling n t : ℝ) = ((n : ℝ) - 1) / t :=
    chafaiRescaling_coe_of_nonneg (by omega : 1 ≤ n) htpos.le
  have hdens_nonneg : 0 ≤ chafaiDensity f n t :=
    chafaiDensity_nonneg htpos.le (hcm.neg_one_pow_mul_iteratedDerivWithin_nonneg n htpos.le)
  have hdens_eq := chafaiDensity_neg_derivWithin_pred f hn htpos
  simp only [Pi.mul_apply]
  rw [hscale, ← ENNReal.ofReal_mul hdens_nonneg, mul_comm, ← hdens_eq]

/-- The Chafaï density of order `n` is interval-integrable on `[0, T]`: it is continuous on
`Ici 0` given `n`-fold differentiability there, and `[0, T]` sits inside that ray. -/
private lemma intervalIntegrable_chafaiDensity {f : ℝ → ℝ} {n : ℕ}
    (hf : ContDiffOn ℝ ((n : ℕ) : WithTop ℕ∞) f (Ici 0)) {T : ℝ} (hT : 0 ≤ T) :
    IntervalIntegrable (fun t => chafaiDensity f n t) volume 0 T :=
  ((continuousOn_chafaiDensity hf).mono Icc_subset_Ici_self).intervalIntegrable_of_Icc hT

/-- **IBP identity** for the CM density:
`∫₀ᵀ ρ_{m+2}(t) dt = B_{m+2}(T) + ∫₀ᵀ ρ_{m+1}(t) dt`. -/
private lemma chafaiDensity_ibp_identity (f : ℝ → ℝ) {m : ℕ}
    (hf : ContDiffOn ℝ ((m + 2 : ℕ) : WithTop ℕ∞) f (Ici 0)) (T : ℝ) (hT : 0 < T) :
    ∫ t in (0 : ℝ)..T, chafaiDensity f (m + 2) t =
    (-1 : ℝ) ^ (m + 2) * T ^ (m + 1) / ↑(m + 1).factorial *
      iteratedDerivWithin (m + 1) f (Ici 0) T +
    ∫ t in (0 : ℝ)..T, chafaiDensity f (m + 1) t := by
  set c : ℝ := (-1) ^ (m + 2) / ↑(m + 1).factorial
  set g := iteratedDerivWithin (m + 1) f (Ici 0)
  set F := fun t : ℝ => t ^ (m + 1) * (c * g t)
  have hf_m1 : ContDiffOn ℝ ((m + 1 : ℕ) : WithTop ℕ∞) f (Ici 0) :=
    hf.of_le (by exact_mod_cast (by omega : m + 1 ≤ m + 2))
  -- The primitive is continuous up to the endpoints, and differentiates to the density difference.
  have hF_cont : ContinuousOn F (Icc 0 T) :=
    ((continuous_pow _).continuousOn).mul (continuousOn_const.mul
      ((hf_m1.continuousOn_iteratedDerivWithin le_rfl (uniqueDiffOn_Ici 0)).mono
        Icc_subset_Ici_self))
  -- The product rule gives two summands; `chafaiDensity_succ_succ_sub_succ` identifies them with
  -- the density difference, which is the form the integrability and FTC steps below want.
  have hF_deriv : ∀ t ∈ Ioo 0 T, HasDerivAt F
      (chafaiDensity f (m + 2) t - chafaiDensity f (m + 1) t) t := fun t ht => by
    have hg : HasDerivAt g (iteratedDerivWithin (m + 2) f (Ici 0) t) t :=
      hf.hasDerivAt_iteratedDerivWithin (mod_cast (m + 1).lt_succ_self)
        (Ici_mem_nhds ht.1)
    exact (chafaiDensity_succ_succ_sub_succ f m t).symm ▸
      (hasDerivAt_pow (m + 1) t).mul (hg.const_mul _)
  -- Both density branches are interval-integrable, so the difference is too.
  have h_int_m2 : IntervalIntegrable (fun t => chafaiDensity f (m + 2) t) volume 0 T :=
    intervalIntegrable_chafaiDensity hf hT.le
  have h_int_m1 : IntervalIntegrable (fun t => chafaiDensity f (m + 1) t) volume 0 T :=
    intervalIntegrable_chafaiDensity hf_m1 hT.le
  -- FTC now reads off the difference of the two integrals directly.
  have hstep1 := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hT.le hF_cont hF_deriv
    (h_int_m2.sub h_int_m1)
  have hF0 : F 0 = 0 := by simp [F, zero_pow (by omega : m + 1 ≠ 0)]
  rw [hF0, sub_zero, intervalIntegral.integral_sub h_int_m2 h_int_m1] at hstep1
  -- The lower endpoint vanishes; the upper endpoint is the boundary term in the statement.
  suffices hgoal : (-1 : ℝ) ^ (m + 2) * T ^ (m + 1) / ↑(m + 1).factorial * g T = F T by linarith
  simp only [F, c]; ring

/-- Monotonicity of the finite-interval Chafaï-density integrals in the order:
for `2 ≤ k` and `0 ≤ T`, the integral of the `k`-th density on `[0,T]` is bounded above by the
integral of the preceding density, assuming the endpoint has the required alternating sign. -/
lemma integral_chafaiDensity_le_pred (f : ℝ → ℝ) {k : ℕ} (hk : 2 ≤ k)
    (hf : ContDiffOn ℝ (k : WithTop ℕ∞) f (Ici 0)) (T : ℝ) (hT : 0 ≤ T)
    (hsign : 0 ≤ (-1 : ℝ) ^ (k - 1) * iteratedDerivWithin (k - 1) f (Ici 0) T) :
    ∫ t in (0 : ℝ)..T, chafaiDensity f k t ≤ ∫ t in (0 : ℝ)..T, chafaiDensity f (k - 1) t := by
  -- The degenerate interval is immediate; otherwise reindex `k` as `m + 2` for the IBP lemma.
  rcases hT.eq_or_lt with rfl | hT_pos
  · simp
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 2 := ⟨k - 2, by omega⟩
  have hsub : m + 2 - 1 = m + 1 := by omega
  simp only [hsub]
  have hibp := chafaiDensity_ibp_identity (m := m) f hf T hT_pos
  set B := (-1 : ℝ) ^ (m + 2) * T ^ (m + 1) / ↑(m + 1).factorial *
    iteratedDerivWithin (m + 1) f (Ici 0) T
  -- The boundary term in the IBP identity is nonpositive by complete-monotone sign alternation.
  have hB : B ≤ 0 := by
    have hsign_m : 0 ≤ (-1 : ℝ) ^ (m + 1) * iteratedDerivWithin (m + 1) f (Ici 0) T := by
      simpa [hsub] using hsign
    have h_neg : (-1 : ℝ) ^ (m + 2) * iteratedDerivWithin (m + 1) f (Ici 0) T ≤ 0 := by
      have : (-1 : ℝ) ^ (m + 2) = (-1) ^ (m + 1) * (-1) := pow_succ (-1) (m + 1)
      rw [this]; nlinarith [hsign_m]
    suffices B = T ^ (m + 1) / ↑(m + 1).factorial *
        ((-1 : ℝ) ^ (m + 2) * iteratedDerivWithin (m + 1) f (Ici 0) T) by
      rw [this]
      exact mul_nonpos_of_nonneg_of_nonpos
        (div_nonneg (pow_nonneg hT_pos.le _) (Nat.cast_nonneg _)) h_neg
    simp only [B]; ring
  linarith

/-- The public `n = 0` convention for Chafaï measures: the zeroth approximating measure is
zero. -/
@[simp]
lemma chafaiMeasure_zero (f : ℝ → ℝ) : chafaiMeasure f 0 = 0 := by
  rw [chafaiMeasure_eq_withDensity]
  ext s hs
  rw [withDensity_apply _ hs]
  simp

/-- The rescaled Chafaï measure on the target type `ℝ≥0` shares the `n = 0` zero convention:
`chafaiRescaled f 0 = 0`, as the pushforward of the zero measure. -/
@[simp]
lemma chafaiRescaled_zero (f : ℝ → ℝ) : chafaiRescaled f 0 = 0 := by
  rw [chafaiRescaled_eq_map, chafaiMeasure_zero, Measure.map_zero]

private lemma integral_chafaiDensity_one_eq (f : ℝ → ℝ) (hcm : IsCompletelyMonotone f)
    (T : ℝ) (hT : 0 ≤ T) :
    ∫ t in (0 : ℝ)..T, chafaiDensity f 1 t = f 0 - f T := by
  have h1 : ∫ t in (0 : ℝ)..T, chafaiDensity f 1 t =
      ∫ t in (0 : ℝ)..T, -iteratedDerivWithin 1 f (Ici 0) t :=
    intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall fun t _ => chafaiDensity_one t)
  rw [h1]
  exact IsCompletelyMonotone.integral_neg_iteratedDerivWithin_one_Ici_eq_sub hcm le_rfl hT

private lemma integral_chafaiDensity_le_sub (f : ℝ → ℝ) (hcm : IsCompletelyMonotone f)
    (j : ℕ) (hj : 1 ≤ j) (T : ℝ) (hT : 0 < T) :
    ∫ t in (0 : ℝ)..T, chafaiDensity f j t ≤ f 0 - f T := by
  induction j with
  | zero => omega
  | succ p ih =>
    by_cases hp : p = 0
    · subst hp
      exact le_of_eq (integral_chafaiDensity_one_eq f hcm T hT.le)
    · calc ∫ t in (0 : ℝ)..T, chafaiDensity f (p + 1) t
          ≤ ∫ t in (0 : ℝ)..T, chafaiDensity f p t := by
            exact integral_chafaiDensity_le_pred f (k := p + 1) (by omega)
              (hcm.contDiffOn.of_le (nat_le_top (p + 1)))
              T hT.le (by
                simpa using hcm.neg_one_pow_mul_iteratedDerivWithin_nonneg p hT.le)
        _ ≤ f 0 - f T := ih (Nat.one_le_iff_ne_zero.mpr hp)

private lemma integral_chafaiDensity_le_tendsto_sub (f : ℝ → ℝ)
    (hcm : IsCompletelyMonotone f) (n : ℕ) (hn : 1 ≤ n) (L : ℝ)
    (hL : Tendsto f atTop (nhds L)) (T : ℝ) (hT : 0 < T) :
    ∫ t in (0 : ℝ)..T, chafaiDensity f n t ≤ f 0 - L := by
  linarith [integral_chafaiDensity_le_sub f hcm n hn T hT,
    (IsContinuousCompletelyMonotoneOnIoi.of_isCompletelyMonotone hcm).le_of_tendsto_atTop hL hT.le]

private lemma chafaiDensity_integrableOn_Ioi_of_tendsto (f : ℝ → ℝ)
    (hcm : IsCompletelyMonotone f) (n : ℕ) (hn : 1 ≤ n) (L : ℝ) (hL : Tendsto f atTop (nhds L)) :
    IntegrableOn (chafaiDensity f n) (Ioi 0) := by
  have hcont : ContinuousOn (chafaiDensity f n) (Ici 0) :=
    continuousOn_chafaiDensity (n := n) ((hcm.contDiffOn).of_le (nat_le_top n))
  -- The improper-integrability criterion reduces the proof to compact integrability on each
  -- interval and a uniform bound for interval integrals of `|ρ_n|`.
  apply integrableOn_Ioi_of_intervalIntegral_norm_bounded (f 0 - L) 0
    (l := atTop) (b := id)
  -- Compact integrability comes from continuity of the density on `[0, ∞)`.
  · intro T
    exact (hcont.mono Icc_subset_Ici_self).integrableOn_compact isCompact_Icc
      |>.mono_set Ioc_subset_Icc_self
  · exact tendsto_id
  -- On positive intervals the density is nonnegative, so the norm integral is the density
  -- integral, bounded by the finite-interval Chafaï estimate.
  · filter_upwards [eventually_gt_atTop 0] with T hT
    simp only [id]
    calc ∫ t in (0 : ℝ)..T, ‖chafaiDensity f n t‖
        = ∫ t in (0 : ℝ)..T, chafaiDensity f n t := by
          apply intervalIntegral.integral_congr_ae
          apply ae_of_all
          intro t ht
          rw [uIoc_of_le hT.le] at ht
          rw [Real.norm_eq_abs,
            abs_of_nonneg (chafaiDensity_nonneg ht.1.le
              (hcm.neg_one_pow_mul_iteratedDerivWithin_nonneg n ht.1.le))]
      _ ≤ f 0 - L := integral_chafaiDensity_le_tendsto_sub f hcm n hn L hL T hT

private lemma chafaiMeasure_mass_le_of_tendsto (f : ℝ → ℝ)
    (hcm : IsCompletelyMonotone f) (n : ℕ) (hn : 1 ≤ n) (L : ℝ) (hL : Tendsto f atTop (nhds L))
    (hint : IntegrableOn (chafaiDensity f n) (Ioi 0)) :
    (chafaiMeasure f n) univ ≤ ENNReal.ofReal (f 0 - L) := by
  rw [chafaiMeasure_eq_withDensity]
  rw [withDensity_apply _ MeasurableSet.univ]
  simp only [Measure.restrict_univ]
  rw [← ofReal_integral_eq_lintegral_ofReal hint
    ((ae_restrict_mem measurableSet_Ioi).mono fun t (ht : 0 < t) =>
      chafaiDensity_nonneg ht.le (hcm.neg_one_pow_mul_iteratedDerivWithin_nonneg n ht.le))]
  exact ENNReal.ofReal_le_ofReal
    (le_of_tendsto (intervalIntegral_tendsto_integral_Ioi 0 hint tendsto_id)
      (eventually_atTop.mpr ⟨1, fun T hT =>
        integral_chafaiDensity_le_tendsto_sub f hcm n hn L hL T (by linarith)⟩))

/-- **Total mass bound with a chosen limit**: `chafaiMeasure f n` is finite with total mass
`≤ f(0) - L` whenever `f(t) → L` at infinity. -/
lemma chafaiMeasure_finite_mass_of_tendsto (f : ℝ → ℝ) (hcm : IsCompletelyMonotone f)
    (n : ℕ) (L : ℝ) (hL : Tendsto f atTop (nhds L)) :
    IsFiniteMeasure (chafaiMeasure f n) ∧
    (chafaiMeasure f n) univ ≤ ENNReal.ofReal (f 0 - L) := by
  by_cases hn0 : n = 0
  · subst n
    rw [chafaiMeasure_zero]
    exact ⟨inferInstance, by simp⟩
  have hn : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn0
  have hint : IntegrableOn (chafaiDensity f n) (Ioi 0) :=
    chafaiDensity_integrableOn_Ioi_of_tendsto f hcm n hn L hL
  have hfin : IsFiniteMeasure (chafaiMeasure f n) := by
    unfold chafaiMeasure
    exact isFiniteMeasure_withDensity_ofReal hint.hasFiniteIntegral
  have hmass : (chafaiMeasure f n) univ ≤ ENNReal.ofReal (f 0 - L) :=
    chafaiMeasure_mass_le_of_tendsto f hcm n hn L hL hint
  exact ⟨hfin, hmass⟩

/-- **Natural total mass bound**: for a completely monotone `f`, the Chafaï measures are finite
and uniformly bounded by `f(0) - L`, where `L` is the automatically obtained limit of `f` at
infinity. -/
lemma chafaiMeasure_finite_mass (f : ℝ → ℝ) (hcm : IsCompletelyMonotone f) :
    ∃ L : ℝ, Tendsto f atTop (nhds L) ∧ 0 ≤ L ∧
      ∀ n,
        IsFiniteMeasure (chafaiMeasure f n) ∧
        (chafaiMeasure f n) univ ≤ ENNReal.ofReal (f 0 - L) := by
  obtain ⟨L, hL, hL_nn⟩ :=
    (IsContinuousCompletelyMonotoneOnIoi.of_isCompletelyMonotone hcm).exists_nonneg_tendsto_atTop
  exact ⟨L, hL, hL_nn, fun n => chafaiMeasure_finite_mass_of_tendsto f hcm n L hL⟩

/-- **Natural rescaled total mass bound**: for a completely monotone `f`, the rescaled
Chafaï measures on `ℝ≥0` are finite and uniformly bounded by `f(0) - L`, where `L` is the
automatically obtained limit of `f` at infinity. -/
lemma chafaiRescaled_finite_mass (f : ℝ → ℝ) (hcm : IsCompletelyMonotone f) :
    ∃ L : ℝ, Tendsto f atTop (nhds L) ∧ 0 ≤ L ∧
      ∀ n,
        IsFiniteMeasure (chafaiRescaled f n) ∧
        (chafaiRescaled f n) univ ≤ ENNReal.ofReal (f 0 - L) := by
  obtain ⟨L, hL, hL_nn, hfinite⟩ := chafaiMeasure_finite_mass f hcm
  refine ⟨L, hL, hL_nn, fun n => ?_⟩
  have hmass := chafaiRescaled_mass_eq f n
  refine ⟨?_, ?_⟩
  · exact ⟨by rw [hmass]; exact (hfinite n).1.measure_univ_lt_top⟩
  · rw [hmass]
    exact (hfinite n).2

/-- Uniform first-moment bound for the rescaled Chafaï measures. -/
lemma chafaiRescaled_lintegral_coe_le (f : ℝ → ℝ) (hcm : IsCompletelyMonotone f) :
    ∀ n,
      ∫⁻ p : ℝ≥0, ENNReal.ofReal (p : ℝ) ∂(chafaiRescaled f n) ≤
        ENNReal.ofReal (-derivWithin f (Ici 0) 0) := by
  intro n
  have _ : 0 ≤ -derivWithin f (Ici 0) 0 := by
    linarith [hcm.derivWithin_nonpos le_rfl]
  rcases lt_or_ge n 2 with hn | hn
  · interval_cases n
    · rw [chafaiRescaled_zero]
      simp
    · rw [chafaiRescaled_eq_map, lintegral_map]
      swap
      · exact ENNReal.measurable_ofReal.comp
          (by fun_prop : Measurable fun p : ℝ≥0 => (p : ℝ))
      swap
      · exact measurable_chafaiRescaling 1
      simp [chafaiRescaling]
  · obtain ⟨L, _hL, hL_nonneg, hfinite⟩ :=
      chafaiMeasure_finite_mass (fun t => -derivWithin f (Ici 0) t) hcm.neg_derivWithin
    calc
      ∫⁻ p : ℝ≥0, ENNReal.ofReal (p : ℝ) ∂(chafaiRescaled f n)
          = (chafaiMeasure (fun t => -derivWithin f (Ici 0) t) (n - 1)) univ :=
              chafaiRescaled_lintegral_coe_eq_chafaiMeasure_neg_derivWithin f hcm hn
      _ ≤ ENNReal.ofReal (-derivWithin f (Ici 0) 0 - L) := (hfinite (n - 1)).2
      _ ≤ ENNReal.ofReal (-derivWithin f (Ici 0) 0) :=
          ENNReal.ofReal_le_ofReal (by linarith)

/-- Prokhorov-ready mass bound for the rescaled Chafaï measures: a completely monotone function
supplies a nonnegative real mass constant `C = f(0) - L`, where `L` is the limit of `f` at
infinity, such that every `chafaiRescaled f n` is finite and has total mass at most `C`. -/
lemma chafaiRescaled_prokhorov_mass_bound (f : ℝ → ℝ) (hcm : IsCompletelyMonotone f) :
    ∃ L : ℝ, ∃ C : ℝ≥0, Tendsto f atTop (nhds L) ∧ 0 ≤ L ∧ (C : ℝ) = f 0 - L ∧
      ∀ n,
        IsFiniteMeasure (chafaiRescaled f n) ∧
        (chafaiRescaled f n) univ ≤ (C : ENNReal) := by
  obtain ⟨L, hL, hL_nn, hfinite⟩ := chafaiRescaled_finite_mass f hcm
  have hL_le : L ≤ f 0 :=
    (IsContinuousCompletelyMonotoneOnIoi.of_isCompletelyMonotone hcm).le_of_tendsto_atTop hL le_rfl
  let C : ℝ≥0 := ⟨f 0 - L, sub_nonneg.mpr hL_le⟩
  refine ⟨L, C, hL, hL_nn, rfl, fun n => ?_⟩
  refine ⟨(hfinite n).1, ?_⟩
  have hC : (C : ENNReal) = ENNReal.ofReal (f 0 - L) := by
    rw [← ENNReal.ofReal_coe_nnreal (p := C)]
    rfl
  rw [hC]
  exact (hfinite n).2

private lemma chafai_kernel_density_eq (f : ℝ → ℝ) (n : ℕ) (hn : 2 ≤ n) (x : ℝ) (hx : 0 ≤ x) :
    ∫ t in Ioi 0, bernsteinKernel n x (((n : ℝ) - 1) / t) *
      chafaiDensity f n t =
    ∫ t in Ioi x, (-1 : ℝ) ^ n / ↑(n - 1).factorial *
      (t - x) ^ (n - 1) * iteratedDerivWithin n f (Ici 0) t := by
  have hn0 : n ≠ 0 := by omega
  have _ : ¬ n ≤ 1 := by omega
  have hsubset : Ioi x ⊆ Ioi 0 := Ioi_subset_Ioi hx
  have hvanish : ∀ t ∈ Ioi 0 \ Ioi x,
      bernsteinKernel n x (((n : ℝ) - 1) / t) * chafaiDensity f n t = 0 := by
    intro t ht
    simp only [Set.mem_sdiff, mem_Ioi, not_lt] at ht
    rw [← chafaiRescaling_coe_of_nonneg (by omega : 1 ≤ n) ht.1.le,
      bernsteinKernel_chafaiRescaling_of_pos hn x ht.1,
      max_eq_right (by rw [sub_nonpos, le_div_iff₀ ht.1]; linarith)]
    rw [zero_pow (by omega : n - 1 ≠ 0), zero_mul]
  rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi hsubset hvanish]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  simp only [mem_Ioi] at ht
  have ht_pos : 0 < t := lt_of_le_of_lt hx ht
  dsimp only
  rw [← chafaiRescaling_coe_of_nonneg (by omega : 1 ≤ n) ht_pos.le,
    bernsteinKernel_chafaiRescaling_of_pos hn x ht_pos,
    max_eq_left (by rw [sub_nonneg, div_le_one₀ ht_pos]; linarith)]
  rw [chafaiDensity_of_ne_zero hn0]
  have key : (1 - x / t) ^ (n - 1) * t ^ (n - 1) = (t - x) ^ (n - 1) := by
    rw [← mul_pow]
    congr 1
    field_simp [ne_of_gt ht_pos]
  calc
    (1 - x / t) ^ (n - 1) *
        (((-1 : ℝ) ^ n / ↑(n - 1).factorial * t ^ (n - 1)) *
          iteratedDerivWithin n f (Ici 0) t)
        = (-1 : ℝ) ^ n / ↑(n - 1).factorial *
          ((1 - x / t) ^ (n - 1) * t ^ (n - 1)) *
          iteratedDerivWithin n f (Ici 0) t := by ring
    _ = _ := by rw [key]

/-- For `k ≠ 0`, dividing by `k!` and multiplying by `k` is dividing by `(k - 1)!`. This is the
coefficient bookkeeping produced by differentiating the order-`k` kernel. -/
private lemma div_factorial_mul_natCast {k : ℕ} (hk : k ≠ 0) (c z : ℝ) :
    c / ↑k.factorial * ((k : ℝ) * z) = c / ↑(k - 1).factorial * z := by
  have hfact : k.factorial = k * (k - 1).factorial := (Nat.mul_factorial_pred hk).symm
  rw [hfact]
  push_cast
  field_simp

private lemma ibp_finite_interval (f : ℝ → ℝ) (hcm : IsCompletelyMonotone f)
    (k : ℕ) (hk : k ≠ 0) (x T : ℝ) (hx : 0 ≤ x) (hxT : x < T) :
    ∫ t in x..T, (-1 : ℝ) ^ (k + 1) / ↑k.factorial * (t - x) ^ k *
      iteratedDerivWithin (k + 1) f (Ici 0) t =
    (-1 : ℝ) ^ (k + 1) / ↑k.factorial * (T - x) ^ k *
      iteratedDerivWithin k f (Ici 0) T -
    ∫ t in x..T, (-1 : ℝ) ^ (k + 1) / ↑(k - 1).factorial * (t - x) ^ (k - 1) *
      iteratedDerivWithin k f (Ici 0) t := by
  set c := (-1 : ℝ) ^ (k + 1) / ↑k.factorial
  set g := iteratedDerivWithin k f (Ici 0)
  set g' := iteratedDerivWithin (k + 1) f (Ici 0)
  set u := fun t : ℝ => c * (t - x) ^ k
  set u' := fun t : ℝ => c * (↑k * (t - x) ^ (k - 1))
  have hu'_eq : ∀ t, u' t =
      (-1 : ℝ) ^ (k + 1) / ↑(k - 1).factorial * (t - x) ^ (k - 1) := fun t => by
    simp only [u', c]
    exact div_factorial_mul_natCast hk _ _
  have hu_cont : ContinuousOn u (uIcc x T) :=
    continuousOn_const.mul ((continuousOn_id.sub continuousOn_const).pow _)
  have hg_cont : ContinuousOn g (uIcc x T) :=
    hcm.continuousOn_iteratedDerivWithin_uIcc k hx (hx.trans hxT.le)
  have hu_deriv : ∀ t ∈ Ioo (min x T) (max x T),
      HasDerivWithinAt u (u' t) (Ioi t) t := by
    intro t _ht
    apply HasDerivAt.hasDerivWithinAt
    simpa [u, u', mul_assoc] using
      (((hasDerivAt_pow k (t - x)).comp t
        ((hasDerivAt_id t).sub_const x)).const_mul c)
  have hg_deriv : ∀ t ∈ Ioo (min x T) (max x T),
      HasDerivWithinAt g (g' t) (Ioi t) t := by
    intro t ht
    rw [min_eq_left hxT.le, max_eq_right hxT.le] at ht
    exact (hcm.hasDerivAt_iteratedDerivWithin_succ k (lt_of_le_of_lt hx ht.1)).hasDerivWithinAt
  have hu'_int : IntervalIntegrable u' volume x T :=
    (continuousOn_const.mul (continuousOn_const.mul
      ((continuousOn_id.sub continuousOn_const).pow _))).intervalIntegrable
  have hg'_int : IntervalIntegrable g' volume x T :=
    (hcm.continuousOn_iteratedDerivWithin_uIcc (k + 1) hx (hx.trans hxT.le)).intervalIntegrable
  have hibp := integral_mul_deriv_eq_deriv_mul_of_hasDeriv_right
    hu_cont hg_cont hu_deriv hg_deriv hu'_int hg'_int
  have hu0 : u x = 0 := by simp [u, sub_self, zero_pow hk]
  rw [hu0, zero_mul, sub_zero] at hibp
  have _ : ∫ t in x..T, (-1 : ℝ) ^ (k + 1) / ↑k.factorial * (t - x) ^ k *
        iteratedDerivWithin (k + 1) f (Ici 0) t =
      ∫ t in x..T, u t * g' t :=
    intervalIntegral.integral_congr_ae (ae_of_all _ fun t _ => by ring)
  have h2 : ∫ t in x..T, u' t * g t =
      ∫ t in x..T, (-1 : ℝ) ^ (k + 1) / ↑(k - 1).factorial * (t - x) ^ (k - 1) *
        iteratedDerivWithin k f (Ici 0) t :=
    intervalIntegral.integral_congr_ae (ae_of_all _ fun t _ => by rw [hu'_eq])
  linarith

private lemma normalized_iteratedDerivWithin_nonneg_antitone (f : ℝ → ℝ)
    (hcm : IsCompletelyMonotone f) (k : ℕ) :
    (∀ T, 0 ≤ T → 0 ≤ (-1 : ℝ) ^ k * iteratedDerivWithin k f (Ici 0) T) ∧
      AntitoneOn (fun T => (-1 : ℝ) ^ k * iteratedDerivWithin k f (Ici 0) T) (Ici 0) := by
  constructor
  · intro T hT
    exact hcm.neg_one_pow_mul_iteratedDerivWithin_nonneg k hT
  · apply antitoneOn_of_deriv_nonpos (convex_Ici 0)
    · exact (hcm.contDiffOn.continuousOn_iteratedDerivWithin (nat_le_top k)
        (uniqueDiffOn_Ici 0)).const_mul ((-1 : ℝ) ^ k)
    · rw [interior_Ici]
      intro T hT
      exact ((hcm.hasDerivAt_iteratedDerivWithin_succ k hT).const_mul
        ((-1 : ℝ) ^ k)).differentiableAt.differentiableWithinAt
    · rw [interior_Ici]
      intro T hT
      have hderiv : deriv (fun T => (-1 : ℝ) ^ k *
            iteratedDerivWithin k f (Ici 0) T) T =
          (-1 : ℝ) ^ k * iteratedDerivWithin (k + 1) f (Ici 0) T := by
        simpa using
          ((hcm.hasDerivAt_iteratedDerivWithin_succ k hT).const_mul
            ((-1 : ℝ) ^ k)).deriv
      rw [hderiv]
      have hsign : 0 ≤ (-1 : ℝ) ^ (k + 1) *
          iteratedDerivWithin (k + 1) f (Ici 0) T :=
        hcm.neg_one_pow_mul_iteratedDerivWithin_nonneg (k + 1) hT.le
      have hneg : 0 ≤ -(((-1 : ℝ) ^ k) *
          iteratedDerivWithin (k + 1) f (Ici 0) T) := by
        simpa [pow_succ, mul_assoc] using hsign
      linarith

/-- Pointwise lower bound for the density on `Icc (T/2) T`: at each such point `t`,
`chafaiDensity f k` is at least the constant `(1/(k-1)!)·(T/2)^(k-1)·h T`. -/
private lemma chafaiDensity_ge_const_on_Icc (f : ℝ → ℝ) (k : ℕ) (h : ℝ → ℝ)
    (T : ℝ) (hhT_nonneg : 0 ≤ h T) {t : ℝ} (ht : t ∈ Icc (T / 2) T) (hT_le_ht : h T ≤ h t)
    (h_density_eq_t :
      chafaiDensity f k t = (1 / ↑((k - 1).factorial)) * t ^ (k - 1) * h t) :
    (1 / ↑((k - 1).factorial)) * (T / 2) ^ (k - 1) * h T ≤ chafaiDensity f k t := by
  -- `0 ≤ T/2` follows from the membership hypothesis `T/2 ≤ t ≤ T`.
  have hT_nonneg : 0 ≤ T := by have := ht.1.trans ht.2; linarith
  -- Combine the power monotonicity `(T/2)^(k-1) ≤ t^(k-1)` with the pointwise bound `h T ≤ h t`.
  have hhalf_nonneg : 0 ≤ T / 2 := by linarith
  have ht_nonneg : 0 ≤ t := le_trans hhalf_nonneg ht.1
  have hpow : (T / 2) ^ (k - 1) ≤ t ^ (k - 1) := pow_le_pow_left₀ hhalf_nonneg ht.1 _
  have hcoeff_nonneg : (0 : ℝ) ≤ 1 / ↑((k - 1).factorial) := by positivity
  have hright_nonneg : 0 ≤ (1 / ↑((k - 1).factorial)) * t ^ (k - 1) :=
    mul_nonneg hcoeff_nonneg (pow_nonneg ht_nonneg _)
  rw [h_density_eq_t]
  calc
    (1 / ↑((k - 1).factorial)) * (T / 2) ^ (k - 1) * h T
        ≤ ((1 / ↑((k - 1).factorial)) * t ^ (k - 1)) * h T := by
          simpa [mul_assoc] using
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow hcoeff_nonneg) hhT_nonneg
    _ ≤ ((1 / ↑((k - 1).factorial)) * t ^ (k - 1)) * h t :=
          mul_le_mul_of_nonneg_left hT_le_ht hright_nonneg

/-- Interval-integral form of the tail lower bound: integrating the pointwise bound
`chafaiDensity_ge_const_on_Icc` over `[T/2, T]` gives
`(1/(k-1)!)·(T/2)^k·h T ≤ ∫ t in T/2..T, chafaiDensity f k t`. -/
private lemma const_le_intervalIntegral_chafaiDensity (f : ℝ → ℝ) (k : ℕ) (hk : k ≠ 0)
    (h : ℝ → ℝ) (h_antitone : AntitoneOn h (Ici 0)) (T : ℝ) (hT_nonneg : 0 ≤ T) (h_density_eq :
      ∀ t ∈ Icc (T / 2) T,
        chafaiDensity f k t = (1 / ↑((k - 1).factorial)) * t ^ (k - 1) * h t)
    (hdens_int : IntervalIntegrable (chafaiDensity f k) volume (T / 2) T)
    (hhT_nonneg : 0 ≤ h T) :
    (1 / ↑((k - 1).factorial)) * (T / 2) ^ k * h T ≤
      ∫ t in T / 2..T, chafaiDensity f k t := by
  have hconst_int :
      IntervalIntegrable (fun _ : ℝ =>
        (1 / ↑((k - 1).factorial)) * (T / 2) ^ (k - 1) * h T) volume (T / 2) T :=
    intervalIntegrable_const
  -- Integrate the pointwise bound `chafaiDensity_ge_const_on_Icc` directly over `[T/2, T]`.
  have hmono_int :=
    intervalIntegral.integral_mono_on (by linarith) hconst_int hdens_int
      (fun t ht => chafaiDensity_ge_const_on_Icc f k h T hhT_nonneg ht
        (h_antitone (le_trans (by linarith : (0 : ℝ) ≤ T / 2) ht.1) hT_nonneg ht.2)
        (h_density_eq t ht))
  have hlen : T - T / 2 = T / 2 := by ring
  rw [intervalIntegral.integral_const, smul_eq_mul, hlen] at hmono_int
  -- Recombine `(T/2)·(T/2)^(k-1) = (T/2)^k` (uses `k ≠ 0`), as a named algebraic equality.
  have hpow : (T / 2) ^ (k - 1) * (T / 2) = (T / 2) ^ k := by
    rw [← pow_succ, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hk)]
  have hconst_eq :
      T / 2 * ((1 / ↑((k - 1).factorial)) * (T / 2) ^ (k - 1) * h T) =
        (1 / ↑((k - 1).factorial)) * (T / 2) ^ k * h T := by
    rw [← hpow]; ring
  rwa [hconst_eq] at hmono_int

/-- Boundary-term tail estimate, the engine of
`tendsto_sub_pow_mul_normalized_iteratedDerivWithin`: `(T-x)^k · h T` is
eventually squeezed by a multiple of the vanishing density tail `∫_{Ioi (T/2)}`. -/
private lemma density_tail_lower_bound_eventually (f : ℝ → ℝ)
    (hcm : IsCompletelyMonotone f) (k : ℕ) (hk : k ≠ 0) (x : ℝ)
    (h : ℝ → ℝ) (h_nonneg : ∀ T, 0 ≤ T → 0 ≤ h T) (h_antitone : AntitoneOn h (Ici 0))
    (h_density_eq : ∀ t, chafaiDensity f k t = (1 / ↑((k - 1).factorial)) * t ^ (k - 1) * h t)
    (hint_density : IntegrableOn (chafaiDensity f k) (Ioi 0)) :
    ∀ᶠ T in atTop,
      (T - x) ^ k * h T ≤
        ((4 : ℝ) ^ k * ↑((k - 1).factorial)) *
          ∫ t in Ioi (T / 2), chafaiDensity f k t := by
  have hcont_density : ContinuousOn (chafaiDensity f k) (Ici 0) :=
    continuousOn_chafaiDensity (n := k) (hcm.contDiffOn.of_le (nat_le_top k))
  filter_upwards [eventually_gt_atTop (max (2 * |x|) 2)] with T hT
  have hT2 : (2 : ℝ) < T := lt_of_le_of_lt (le_max_right (2 * |x|) 2) hT
  have hTpos : 0 < T := by linarith
  have hTabs : 2 * |x| < T := lt_of_le_of_lt (le_max_left (2 * |x|) 2) hT
  -- the shift is dominated by `T` in both directions, so `T - x` sits between `0` and `2 * T`
  have hTx_nonneg : 0 ≤ T - x := by linarith [le_abs_self x, abs_nonneg x]
  have hTx_le : T - x ≤ 2 * T := by linarith [neg_abs_le x, abs_nonneg x]
  have hhalf_nonneg : 0 ≤ T / 2 := by linarith
  have hhT_nonneg : 0 ≤ h T := h_nonneg T hTpos.le
  have h_interval_le :
      ∫ t in T / 2..T, chafaiDensity f k t ≤ ∫ t in Ioi (T / 2), chafaiDensity f k t := by
    rw [intervalIntegral.integral_of_le (by linarith)]
    exact setIntegral_mono_set (hint_density.mono_set (Ioi_subset_Ioi hhalf_nonneg))
      ((ae_restrict_mem measurableSet_Ioi).mono fun t ht =>
        chafaiDensity_nonneg (lt_of_le_of_lt hhalf_nonneg ht).le
          (hcm.neg_one_pow_mul_iteratedDerivWithin_nonneg k (lt_of_le_of_lt hhalf_nonneg ht).le))
      (ae_of_all _ fun _ ht => Ioc_subset_Ioi_self ht)
  have hhalf_le :
      (T / 2) ^ k * h T ≤ ↑((k - 1).factorial) * ∫ t in Ioi (T / 2), chafaiDensity f k t := by
    have hfact_pos : (0 : ℝ) < ↑((k - 1).factorial) := Nat.cast_pos.mpr (Nat.factorial_pos _)
    have hIcc_subset : Icc (T / 2) T ⊆ Ici 0 := fun t ht => le_trans hhalf_nonneg ht.1
    have hmul := mul_le_mul_of_nonneg_left
      ((const_le_intervalIntegral_chafaiDensity f k hk h h_antitone T hTpos.le
        (fun t _ => h_density_eq t)
        ((hcont_density.mono hIcc_subset).intervalIntegrable_of_Icc (by linarith))
        hhT_nonneg).trans h_interval_le) hfact_pos.le
    have hfact_cancel :
        ↑((k - 1).factorial) * ((1 / ↑((k - 1).factorial)) * (T / 2) ^ k * h T) =
          (T / 2) ^ k * h T := by field_simp
    rwa [hfact_cancel] at hmul
  calc
    (T - x) ^ k * h T ≤ (2 * T) ^ k * h T := by gcongr
    _ = (4 : ℝ) ^ k * ((T / 2) ^ k * h T) := by
      -- doubling the bound and halving the argument each cost a factor `2 ^ k`
      have h4 : (4 : ℝ) ^ k = 2 ^ k * 2 ^ k := by rw [← mul_pow]; norm_num
      rw [mul_pow, div_pow, h4]
      field_simp
    _ ≤ (4 : ℝ) ^ k * (↑((k - 1).factorial) * ∫ t in Ioi (T / 2), chafaiDensity f k t) := by gcongr
    _ = ((4 : ℝ) ^ k * ↑((k - 1).factorial)) *
          ∫ t in Ioi (T / 2), chafaiDensity f k t := by ring

/-- **The weighted normalized derivative vanishes at infinity.** Let `f` be completely monotone,
let `k` be a nonzero order and let `x` be any real shift. Writing `h T` for the normalized
derivative
`(-1) ^ k * iteratedDerivWithin k f (Ici 0) T`, the products `(T - x) ^ k * h T` tend to `0` as
`T → ∞`. -/
private lemma tendsto_sub_pow_mul_normalized_iteratedDerivWithin (f : ℝ → ℝ)
    (hcm : IsCompletelyMonotone f) (k : ℕ) (hk : k ≠ 0) (x : ℝ) :
    Tendsto (fun T => (T - x) ^ k * ((-1 : ℝ) ^ k * iteratedDerivWithin k f (Ici 0) T))
      atTop (nhds 0) := by
  -- complete monotonicity already supplies the limit at infinity that integrability needs
  obtain ⟨L, hL, -⟩ :=
    (IsContinuousCompletelyMonotoneOnIoi.of_isCompletelyMonotone hcm).exists_nonneg_tendsto_atTop
  set h := fun T => (-1 : ℝ) ^ k * iteratedDerivWithin k f (Ici 0) T
  have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk
  obtain ⟨h_nonneg₀, h_antitone₀⟩ :=
    normalized_iteratedDerivWithin_nonneg_antitone f hcm k
  have h_nonneg : ∀ T, 0 ≤ T → 0 ≤ h T := by simpa [h] using h_nonneg₀
  have h_antitone : AntitoneOn h (Ici 0) := by simpa [h] using h_antitone₀
  have hint_density : IntegrableOn (chafaiDensity f k) (Ioi 0) :=
    chafaiDensity_integrableOn_Ioi_of_tendsto f hcm k hk1 L hL
  -- `tendsto_integral_Ioi_zero` takes the cut point along any map to `atTop`, so `T / 2` needs
  -- no separate composition argument.
  have htail_half : Tendsto (fun T : ℝ => ∫ t in Ioi (T / 2), chafaiDensity f k t)
      atTop (nhds 0) :=
    tendsto_integral_Ioi_zero (b := fun T : ℝ => T / 2)
      (tendsto_id.atTop_div_const (by norm_num))
  have hupper := density_tail_lower_bound_eventually f hcm k hk x h h_nonneg h_antitone
    (by
      intro t
      rw [chafaiDensity_of_ne_zero hk]
      simp only [h]
      field_simp)
    hint_density
  have hnonneg_event : ∀ᶠ T in atTop, 0 ≤ (T - x) ^ k * h T := by
    filter_upwards [eventually_gt_atTop (max x 0)] with T hT
    have hT0 : 0 < T := lt_of_le_of_lt (le_max_right x 0) hT
    have hxT : x < T := lt_of_le_of_lt (le_max_left x 0) hT
    exact mul_nonneg (pow_nonneg (sub_nonneg.mpr hxT.le) _) (h_nonneg T hT0.le)
  have hupper_tendsto :
      Tendsto (fun T : ℝ =>
        ((4 : ℝ) ^ k * ↑((k - 1).factorial)) *
          ∫ t in Ioi (T / 2), chafaiDensity f k t) atTop (nhds 0) := by
    simpa [mul_zero] using htail_half.const_mul (((4 : ℝ) ^ k) * ↑((k - 1).factorial))
  -- squeeze between nonnegativity and the vanishing tail bound
  exact squeeze_zero' hnonneg_event hupper hupper_tendsto

/-- **The shifted order-`k` kernel is dominated by the Chafaï density.** For `0 ≤ x ≤ t` the
kernel built from `(t - x) ^ (k - 1)` is nonnegative and bounded by the density built from
`t ^ (k - 1)`. -/
private lemma norm_ibp_kernel_le_chafaiDensity (f : ℝ → ℝ)
    {k : ℕ} (hk0 : k ≠ 0) {x t : ℝ} (hx : 0 ≤ x) (ht : x ≤ t)
    (hcm_sign : 0 ≤ (-1 : ℝ) ^ k * iteratedDerivWithin k f (Ici 0) t) :
    ‖(-1 : ℝ) ^ k / ↑(k - 1).factorial * (t - x) ^ (k - 1) *
      iteratedDerivWithin k f (Ici 0) t‖ ≤ chafaiDensity f k t := by
  have htx : 0 ≤ t - x := by linarith
  have htx_le : t - x ≤ t := by linarith
  rw [chafaiDensity_of_ne_zero hk0]
  have hfact : (0 : ℝ) < ↑(k - 1).factorial := Nat.cast_pos.mpr (Nat.factorial_pos _)
  have hval_nn : 0 ≤ (-1 : ℝ) ^ k / ↑(k - 1).factorial * (t - x) ^ (k - 1) *
      iteratedDerivWithin k f (Ici 0) t := by
    calc
      (-1 : ℝ) ^ k / ↑(k - 1).factorial * (t - x) ^ (k - 1) *
          iteratedDerivWithin k f (Ici 0) t
          = (t - x) ^ (k - 1) / ↑(k - 1).factorial *
            ((-1 : ℝ) ^ k * iteratedDerivWithin k f (Ici 0) t) := by field_simp
      _ ≥ 0 := mul_nonneg (div_nonneg (pow_nonneg htx _) hfact.le) hcm_sign
  rw [Real.norm_eq_abs, abs_of_nonneg hval_nn]
  calc
    (-1 : ℝ) ^ k / ↑(k - 1).factorial * (t - x) ^ (k - 1) *
        iteratedDerivWithin k f (Ici 0) t
        = (1 / ↑(k - 1).factorial) * (t - x) ^ (k - 1) *
          ((-1 : ℝ) ^ k * iteratedDerivWithin k f (Ici 0) t) := by field_simp
    _ ≤ (1 / ↑(k - 1).factorial) * t ^ (k - 1) *
        ((-1 : ℝ) ^ k * iteratedDerivWithin k f (Ici 0) t) := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ htx htx_le _) (by positivity))
            hcm_sign
    _ = (-1 : ℝ) ^ k / ↑(k - 1).factorial * t ^ (k - 1) *
        iteratedDerivWithin k f (Ici 0) t := by field_simp

private lemma ibp_kernel_integrableOn (f : ℝ → ℝ) (hcm : IsCompletelyMonotone f)
    (k : ℕ) (hk : 1 ≤ k) (x : ℝ) (hx : 0 ≤ x) (L : ℝ) (hL : Tendsto f atTop (nhds L)) :
    IntegrableOn (fun t => (-1 : ℝ) ^ k / ↑(k - 1).factorial * (t - x) ^ (k - 1) *
      iteratedDerivWithin k f (Ici 0) t) (Ioi x) := by
  have hk0 : k ≠ 0 := by omega
  have hint_density : IntegrableOn (chafaiDensity f k) (Ioi 0) :=
    chafaiDensity_integrableOn_Ioi_of_tendsto f hcm k hk L hL
  apply Integrable.mono' (hint_density.mono_set (Ioi_subset_Ioi hx))
  · apply (ContinuousOn.aestronglyMeasurable _ measurableSet_Ioi)
    exact ((continuousOn_const.mul
      ((continuousOn_id.sub continuousOn_const).pow _)).mul
      ((hcm.contDiffOn.continuousOn_iteratedDerivWithin (nat_le_top k)
        (uniqueDiffOn_Ici 0)).mono
        (fun t ht => mem_Ici.mpr (lt_of_le_of_lt hx ht).le)))
  · rw [ae_restrict_iff' measurableSet_Ioi]
    exact ae_of_all _ fun t ht => norm_ibp_kernel_le_chafaiDensity f hk0 hx (le_of_lt ht)
      (hcm.neg_one_pow_mul_iteratedDerivWithin_nonneg k (le_trans hx (le_of_lt ht)))

/-- Raising the sign exponent of the order-`k` kernel by one negates its integral. -/
private lemma intervalIntegral_neg_one_pow_succ_kernel (f : ℝ → ℝ) (k : ℕ) (x T : ℝ) :
    ∫ t in x..T, (-1 : ℝ) ^ (k + 1) / ↑(k - 1).factorial * (t - x) ^ (k - 1) *
        iteratedDerivWithin k f (Ici 0) t =
      -(∫ t in x..T, (-1 : ℝ) ^ k / ↑(k - 1).factorial * (t - x) ^ (k - 1) *
        iteratedDerivWithin k f (Ici 0) t) := by
  rw [← intervalIntegral.integral_neg]
  refine intervalIntegral.integral_congr_ae (ae_of_all _ fun t _ => ?_)
  rw [pow_succ (-1 : ℝ) k]
  ring

/-- For a completely monotone `f` with limit `L` at infinity, `0 ≤ x` and `k ≠ 0`, the order-`k`
kernel identity implies the order-`k + 1` one: if the order-`k` kernel integrates against the
`k`-th derivative to `f x - L` on `(x, ∞)`, then so does the order-`k + 1` kernel against the
`(k + 1)`-st derivative. -/
private lemma chafai_repeated_ibp_succ (f : ℝ → ℝ) (hcm : IsCompletelyMonotone f)
    (k : ℕ) (hk : k ≠ 0) (x : ℝ) (hx : 0 ≤ x) (L : ℝ) (hL : Tendsto f atTop (nhds L))
    (ih : ∫ t in Ioi x, (-1 : ℝ) ^ k / ↑(k - 1).factorial * (t - x) ^ (k - 1) *
      iteratedDerivWithin k f (Ici 0) t = f x - L) :
    ∫ t in Ioi x, (-1 : ℝ) ^ (k + 1) / ↑k.factorial * (t - x) ^ k *
      iteratedDerivWithin (k + 1) f (Ici 0) t = f x - L := by
  -- Integrate by parts on `[x, T]`; the boundary term decays, so `T → ∞` transfers `ih`.
  have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk
  have hintk := ibp_kernel_integrableOn f hcm k hk1 x hx L hL
  have hintkp1 := ibp_kernel_integrableOn f hcm (k + 1) (by omega) x hx L hL
  simp only [show k + 1 - 1 = k by omega] at hintkp1
  have htend_k : Tendsto (fun T => ∫ t in x..T,
      (-1 : ℝ) ^ k / ↑(k - 1).factorial * (t - x) ^ (k - 1) *
      iteratedDerivWithin k f (Ici 0) t) atTop (nhds (f x - L)) := by
    rw [← ih]
    exact intervalIntegral_tendsto_integral_Ioi x hintk tendsto_id
  have htend_sum : Tendsto (fun T =>
      (-1 : ℝ) ^ (k + 1) / ↑k.factorial * (T - x) ^ k *
        iteratedDerivWithin k f (Ici 0) T +
      ∫ t in x..T, (-1 : ℝ) ^ k / ↑(k - 1).factorial * (t - x) ^ (k - 1) *
        iteratedDerivWithin k f (Ici 0) t) atTop (nhds (f x - L)) := by
    have hbdry : Tendsto (fun T => (-1 : ℝ) ^ (k + 1) / ↑k.factorial * (T - x) ^ k *
        iteratedDerivWithin k f (Ici 0) T) atTop (nhds 0) := by
      have heq : ∀ T, -(1 / (k.factorial : ℝ)) *
          ((T - x) ^ k * ((-1 : ℝ) ^ k * iteratedDerivWithin k f (Ici 0) T)) =
          (-1 : ℝ) ^ (k + 1) / ↑k.factorial * (T - x) ^ k *
            iteratedDerivWithin k f (Ici 0) T := fun T => by
        simp only [pow_succ]
        ring
      simpa using
        (((tendsto_sub_pow_mul_normalized_iteratedDerivWithin f hcm k hk x).const_mul
          (-(1 / (k.factorial : ℝ)))).congr heq)
    simpa [zero_add] using hbdry.add htend_k
  have htend_via_ibp : Tendsto (fun T => ∫ t in x..T,
      (-1 : ℝ) ^ (k + 1) / ↑k.factorial * (t - x) ^ k *
      iteratedDerivWithin (k + 1) f (Ici 0) t) atTop (nhds (f x - L)) :=
    Tendsto.congr' ((eventually_gt_atTop x).mono fun T hxT => by
      have := ibp_finite_interval f hcm k hk x T hx hxT
      linarith [intervalIntegral_neg_one_pow_succ_kernel f k x T]) htend_sum
  exact tendsto_nhds_unique
    ((intervalIntegral_tendsto_integral_Ioi x hintkp1 tendsto_id).congr
      (fun T => by simp [id])) htend_via_ibp

/-- **Repeated integration by parts for a completely monotone function.** For `n ≥ 1`, `0 ≤ x`
and `f` tending to `L` at infinity, integrating the order-`n` kernel
`(-1) ^ n / (n - 1)! * (t - x) ^ (n - 1)` against the `n`-th derivative of `f` over `(x, ∞)`
recovers `f x - L`. This is the analytic identity behind the Chafaï reconstruction of `f` from
its derivatives. -/
private lemma chafai_repeated_ibp (f : ℝ → ℝ) (hcm : IsCompletelyMonotone f)
    (n : ℕ) (hn : 1 ≤ n) (x : ℝ) (hx : 0 ≤ x) (L : ℝ) (hL : Tendsto f atTop (nhds L)) :
    ∫ t in Ioi x, (-1 : ℝ) ^ n / ↑(n - 1).factorial *
      (t - x) ^ (n - 1) *
      iteratedDerivWithin n f (Ici 0) t = f x - L := by
  induction n with
  | zero => omega
  | succ k ih =>
    by_cases hk : k = 0
    · subst hk
      simpa using hcm.integral_Ioi_neg_iteratedDerivWithin_one_of_nonneg hx hL
    · have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk
      simp only [show k + 1 - 1 = k by omega]
      exact chafai_repeated_ibp_succ f hcm k hk x hx L hL (ih hk1)

/-- **Chafaï reconstruction identity** for the nonconstant part. -/
lemma chafaiRescaled_integral_bernsteinKernel_eq_sub_tendsto_atTop
    (f : ℝ → ℝ) (hcm : IsCompletelyMonotone f) (n : ℕ) (hn : 2 ≤ n) (x : ℝ) (hx : 0 ≤ x)
    (L : ℝ) (hL : Tendsto f atTop (nhds L)) :
    ∫ p, bernsteinKernel n x (p : ℝ) ∂(chafaiRescaled f n) = f x - L := by
  have h_integral_pullback :
      ∫ p : ℝ≥0, bernsteinKernel n x (p : ℝ) ∂(chafaiRescaled f n) =
        ∫ t, bernsteinKernel n x (chafaiRescaling n t : ℝ) ∂(chafaiMeasure f n) := by
    exact chafaiRescaled_integral f n
      ((measurable_bernsteinKernel n x).comp (by fun_prop : Measurable fun p : ℝ≥0 => (p : ℝ))
        |>.aestronglyMeasurable)
  have h_integral_density :
      ∫ t, bernsteinKernel n x (chafaiRescaling n t : ℝ) ∂(chafaiMeasure f n) =
        ∫ t in Ioi 0,
          bernsteinKernel n x (((n : ℝ) - 1) / t) * chafaiDensity f n t := by
    rw [chafaiMeasure_eq_withDensity]
    have hcont_density : ContinuousOn (chafaiDensity f n) (Ici 0) :=
      continuousOn_chafaiDensity (n := n) (hcm.contDiffOn.of_le (nat_le_top n))
    rw [integral_withDensity_eq_integral_toReal_smul₀
      (AEMeasurable.ennreal_ofReal
        ((hcont_density.mono Ioi_subset_Ici_self).aestronglyMeasurable
          measurableSet_Ioi |>.aemeasurable))
      (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
    exact setIntegral_congr_ae measurableSet_Ioi
      (ae_of_all _ fun t ht => by
        simp only [smul_eq_mul, mem_Ioi] at ht ⊢
        rw [chafaiRescaling_coe_of_nonneg (by omega : 1 ≤ n) ht.le]
        rw [ENNReal.toReal_ofReal
          (chafaiDensity_nonneg ht.le
            (hcm.neg_one_pow_mul_iteratedDerivWithin_nonneg n ht.le))]
        ring)
  have hkernel := chafai_kernel_density_eq f n hn x hx
  have hibp := chafai_repeated_ibp f hcm n (by omega) x hx L hL
  rw [h_integral_pullback, h_integral_density, hkernel]
  exact hibp

private lemma bernsteinKernel_le_exp {n : ℕ} (hn : 2 ≤ n) {x p : ℝ} (_hx : 0 ≤ x) (_hp : 0 ≤ p) :
    bernsteinKernel n x p ≤ Real.exp (-(x * p)) := by
  rw [bernsteinKernel_of_two_le hn]
  by_cases h : 1 - x * p / ↑(n - 1) ≤ 0
  · rw [max_eq_right h]
    rw [zero_pow (by omega : n - 1 ≠ 0)]
    exact le_of_lt (Real.exp_pos _)
  · push Not at h
    rw [max_eq_left h.le]
    have hden_pos : (0 : ℝ) < ↑(n - 1) := Nat.cast_pos.mpr (by omega)
    have hle : 1 - x * p / ↑(n - 1) ≤ Real.exp (-(x * p / ↑(n - 1))) := by
      linarith [Real.add_one_le_exp (-(x * p / ↑(n - 1)))]
    calc
      (1 - x * p / ↑(n - 1)) ^ (n - 1)
          ≤ (Real.exp (-(x * p / ↑(n - 1)))) ^ (n - 1) :=
            pow_le_pow_left₀ h.le hle _
      _ = Real.exp (↑(n - 1) * -(x * p / ↑(n - 1))) := by
            rw [← Real.exp_nat_mul]
      _ = Real.exp (-(x * p)) := by
            congr 1
            field_simp [hden_pos.ne']

/-- **Local error bound for the Bernstein truncation.** For `0 ≤ u < 1` and `m : ℕ`, the
difference `exp (-(m·u)) - (1 - u) ^ m` is bounded above by the second-order term
`m·u² / (1 - u)`. This is the pointwise estimate driving the uniform convergence of the
Bernstein kernel to the Laplace kernel. -/
private lemma exp_neg_mul_sub_one_sub_pow_le (u : ℝ) (hu_nn : 0 ≤ u) (hu_lt_1 : u < 1) (m : ℕ) :
    Real.exp (-(↑m * u)) - (1 - u) ^ m ≤ ↑m * u ^ 2 / (1 - u) := by
  have h1u : 0 < 1 - u := by linarith
  -- The logarithmic lower bound converts the power into an exponential with a Taylor-tail term.
  have hpow_ge : (1 - u) ^ m ≥ Real.exp (-(↑m * u) - ↑m * u ^ 2 / (1 - u)) := by
    have heq : (1 - u) ^ m = Real.exp (↑m * Real.log (1 - u)) := by
      rw [← Real.rpow_natCast (1 - u) m, Real.rpow_def_of_pos h1u, mul_comm]
    rw [heq]
    gcongr
    have hfactor : -(↑m * u) - ↑m * u ^ 2 / (1 - u) = ↑m * (-u - u ^ 2 / (1 - u)) := by ring
    rw [hfactor]
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg m)
    have habs : |u| < 1 := by rwa [abs_of_nonneg hu_nn]
    have hlog := Real.abs_log_sub_add_sum_range_le habs 1
    simp only [Finset.sum_range_one, Nat.cast_zero, zero_add, div_one, pow_one] at hlog
    have hu_sq : u ^ (1 + 1) = u ^ 2 := by ring
    rw [abs_of_nonneg hu_nn, hu_sq] at hlog
    linarith [(abs_le.mp hlog).1]
  set b := ↑m * u ^ 2 / (1 - u) with _hb_def
  have hb_nn : 0 ≤ b := div_nonneg (mul_nonneg (Nat.cast_nonneg m) (sq_nonneg u)) h1u.le
  have hmu_nn : 0 ≤ ↑m * u := mul_nonneg (Nat.cast_nonneg m) hu_nn
  -- `exp` sits above its tangent line at `0`, so the exponential gap is at most `b`.
  suffices h : Real.exp (-(↑m * u)) - Real.exp (-(↑m * u) - b) ≤ b by linarith
  have hsplit : Real.exp (-(↑m * u) - b) = Real.exp (-(↑m * u)) * Real.exp (-b) := by
    rw [← Real.exp_add]
    ring_nf
  rw [hsplit]
  nlinarith [Real.exp_pos (-(↑m * u)), Real.exp_pos (-b),
    Real.exp_le_one_iff.mpr (neg_nonpos.mpr hmu_nn), Real.add_one_le_exp (-b)]

/-- **Compact-support tail estimate.** Once `M` exceeds `C + 2C²/ε`, the error parameter
`xp² / (M - xp)` stays below `ε / 2` for every `0 ≤ xp ≤ C`. Positivity of `M - C` follows
from the size hypothesis, so the only inputs are the pointwise bounds on `xp`. -/
private lemma sq_div_sub_lt_div_two (xp C ε M : ℝ) (hxp_nn : 0 ≤ xp) (hxp_le_C : xp ≤ C)
    (hε : 0 < ε) (hM : 2 * C ^ 2 / ε < M - C) :
    xp ^ 2 / (M - xp) < ε / 2 := by
  have haux : 0 ≤ 2 * C ^ 2 / ε := div_nonneg (by positivity) hε.le
  have hMC_pos : 0 < M - C := by linarith
  -- Monotone in the numerator and the denominator: `xp²/(M-xp) ≤ C²/(M-C)`.
  have hmono : xp ^ 2 / (M - xp) ≤ C ^ 2 / (M - C) :=
    div_le_div₀ (sq_nonneg C) (sq_le_sq' (by linarith) hxp_le_C) hMC_pos (by linarith)
  -- The size hypothesis on `M` forces `C²/(M-C) < ε/2`.
  have hsmall : C ^ 2 / (M - C) < ε / 2 := by
    rw [div_lt_div_iff₀ hMC_pos (by positivity : (0 : ℝ) < 2)]
    have h2 : ε * (M - C) > ε * (2 * C ^ 2 / ε) := mul_lt_mul_of_pos_left hM hε
    rw [mul_div_cancel₀ _ (ne_of_gt hε)] at h2
    linarith
  linarith

private lemma kernel_uniform_conv_compact (x R ε : ℝ) (hx : 0 < x) (hR : 0 < R) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n, N ≤ n → ∀ p, 0 ≤ p → p ≤ R →
      |bernsteinKernel n x p - Real.exp (-(x * p))| < ε := by
  set C := x * R
  have hC_pos : 0 < C := mul_pos hx hR
  obtain ⟨N₀, hN₀⟩ := exists_nat_gt (C + 2 + 2 * C ^ 2 / ε)
  refine ⟨N₀, fun n hn p hp hpR => ?_⟩
  have hn_gt : (↑n : ℝ) > C + 2 + 2 * C ^ 2 / ε := lt_of_lt_of_le hN₀ (Nat.cast_le.mpr hn)
  have haux : 0 ≤ 2 * C ^ 2 / ε := div_nonneg (by positivity) hε.le
  have hn_ge2 : 2 ≤ n := by exact_mod_cast (show (2 : ℝ) < ↑n by linarith [hC_pos]).le
  have hle := bernsteinKernel_le_exp hn_ge2 hx.le hp
  rw [abs_of_nonpos (by linarith), neg_sub]
  set m := n - 1
  have hm_pos : (0 : ℝ) < ↑m := Nat.cast_pos.mpr (by omega)
  have hm_eq : (↑m : ℝ) = ↑n - 1 := by rw [Nat.cast_sub (show 1 ≤ n by omega)]; simp
  have hxp_nn : 0 ≤ x * p := mul_nonneg hx.le hp
  have hxp_le_C : x * p ≤ C := mul_le_mul_of_nonneg_left hpR hx.le
  set u := x * p / ↑m with hu_def
  have hu_nn : 0 ≤ u := div_nonneg hxp_nn hm_pos.le
  have hu_lt_1 : u < 1 := by rw [div_lt_one hm_pos]; linarith [hm_eq]
  have hkernel_eq : bernsteinKernel n x p = (1 - u) ^ m := by
    rw [bernsteinKernel_of_two_le hn_ge2]
    congr 1
    exact max_eq_left (by
      -- `max_eq_left` needs the truncated factor `1 - x*p/m` nonneg; expose it as the defeq goal.
      change 0 ≤ 1 - x * p / (↑m : ℝ)
      rw [← hu_def]; linarith)
  rw [hkernel_eq]
  set b := ↑m * u ^ 2 / (1 - u) with hb_def
  have hmu : ↑m * u = x * p := by simp only [hu_def]; field_simp [hm_pos.ne']
  -- Assemble the two phase estimates: the local error is `≤ b`, and `b < ε/2` on `p ≤ R`.
  have hstep : Real.exp (-(x * p)) - (1 - u) ^ m ≤ b := by
    rw [hb_def, ← hmu]
    exact exp_neg_mul_sub_one_sub_pow_le u hu_nn hu_lt_1 m
  have hb_eq : b = (x * p) ^ 2 / (↑m - x * p) := by
    simp only [hb_def, hu_def]
    field_simp [hm_pos.ne']
  have hb_small : b < ε / 2 := by
    rw [hb_eq]
    exact sq_div_sub_lt_div_two (x * p) C ε ↑m hxp_nn hxp_le_C hε (by linarith [hm_eq])
  linarith

private lemma kernel_uniform_conv (x : ℝ) (hx : 0 < x) (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n, N ≤ n → ∀ p, 0 ≤ p →
      |bernsteinKernel n x p - Real.exp (-(x * p))| < ε := by
  have htail : Tendsto (fun R => Real.exp (-(x * R))) atTop (nhds 0) := by
    apply Tendsto.comp Real.tendsto_exp_neg_atTop_nhds_zero
    exact tendsto_id.const_mul_atTop hx
  obtain ⟨R₀, hR₀⟩ := Metric.tendsto_atTop.mp htail (ε / 2) (half_pos hε)
  set R := max R₀ 1
  have hR_pos : 0 < R := lt_of_lt_of_le one_pos (le_max_right R₀ 1)
  have hR_tail : Real.exp (-(x * R)) < ε / 2 := by
    have h1 := hR₀ R (le_max_left _ _)
    rwa [dist_zero_right, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] at h1
  obtain ⟨N₁, hN₁⟩ := kernel_uniform_conv_compact x R (ε / 2) hx hR_pos (half_pos hε)
  refine ⟨max N₁ 2, fun n hn p hp => ?_⟩
  have hn2 : 2 ≤ n := le_trans (le_max_right N₁ 2) hn
  by_cases hpR : p ≤ R
  · linarith [hN₁ n (le_trans (le_max_left _ _) hn) p hp hpR]
  · push Not at hpR
    have h1 := bernsteinKernel_le_exp hn2 hx.le hp
    rw [abs_of_nonpos (by linarith)]
    have h2 : Real.exp (-(x * p)) ≤ Real.exp (-(x * R)) := by
      apply Real.exp_le_exp_of_le
      linarith [mul_le_mul_of_nonneg_left (le_of_lt hpR) hx.le]
    linarith [bernsteinKernel_nonneg n x p]

/-- Bernstein-to-Laplace replacement against a uniformly finite sequence of measures. -/
lemma integral_bernsteinKernel_sub_laplaceKernel_tendsto_zero_of_mass_bound
    {C : ℝ} (σ : ℕ → Measure ℝ≥0)
    (hmass : ∀ᶠ n in atTop, (σ n) univ ≤ ENNReal.ofReal C) (x : ℝ) (hx : 0 ≤ x) :
    Tendsto (fun n => ∫ p : ℝ≥0,
        (bernsteinKernel n x (p : ℝ) - Real.exp (-(x * (p : ℝ)))) ∂(σ n))
      atTop (nhds 0) := by
  by_cases hx0 : x = 0
  · subst hx0
    suffices h : ∀ᶠ n in atTop, ∫ p : ℝ≥0,
        (bernsteinKernel n 0 (p : ℝ) - Real.exp (-(0 * (p : ℝ)))) ∂(σ n) = 0 by
      exact Tendsto.congr' (EventuallyEq.symm h) tendsto_const_nhds
    filter_upwards [eventually_ge_atTop 2] with n hn
    apply integral_eq_zero_of_ae
    apply ae_of_all
    intro p
    -- At `x = 0` the integrand is defeq to this explicit difference; expose it before rewriting.
    change bernsteinKernel n 0 (p : ℝ) - Real.exp (-(0 * (p : ℝ))) = 0
    rw [bernsteinKernel_of_two_le hn]
    simp
  · have hx_pos : 0 < x := lt_of_le_of_ne hx (Ne.symm hx0)
    rw [Metric.tendsto_atTop]
    intro ε hε
    have hmax_pos : 0 < max C 1 := lt_max_of_lt_right one_pos
    obtain ⟨N, hN⟩ := kernel_uniform_conv x hx_pos
      (ε / (2 * max C 1)) (div_pos hε (by positivity))
    refine eventually_atTop.1 <| ((eventually_ge_atTop N).and hmass).mono fun n hn => ?_
    rcases hn with ⟨hn, hmass_n⟩
    rw [dist_zero_right]
    have : IsFiniteMeasure (σ n) := ⟨hmass_n.trans_lt ENNReal.ofReal_lt_top⟩
    calc
      ‖∫ p : ℝ≥0, (bernsteinKernel n x (p : ℝ) - Real.exp (-(x * (p : ℝ)))) ∂(σ n)‖
          ≤ ∫ p : ℝ≥0,
              ‖bernsteinKernel n x (p : ℝ) - Real.exp (-(x * (p : ℝ)))‖ ∂(σ n) :=
            norm_integral_le_integral_norm _
      _ ≤ ∫ _ : ℝ≥0, (ε / (2 * max C 1)) ∂(σ n) := by
          apply integral_mono_of_nonneg
            (ae_of_all _ fun _ => norm_nonneg _) (integrable_const _)
          exact ae_of_all _ fun p => by
            simpa [Real.norm_eq_abs] using le_of_lt (hN n hn (p : ℝ) p.property)
      _ = ε / (2 * max C 1) * ((σ n) univ).toReal := by
          simp [MeasureTheory.integral_const, smul_eq_mul, Measure.real, mul_comm]
      _ ≤ ε / (2 * max C 1) * max C 1 := by
          apply mul_le_mul_of_nonneg_left _ (le_of_lt (div_pos hε (by positivity)))
          exact ENNReal.toReal_le_of_le_ofReal (le_of_lt hmax_pos)
            (le_trans hmass_n (ENNReal.ofReal_le_ofReal (le_max_left C 1)))
      _ = ε / 2 := by field_simp
      _ < ε := half_lt_self hε

/-- Weak convergence of the rescaled Chafaï measures specializes to the Laplace kernel:
if all bounded-continuous test integrals for `chafaiRescaled f n` converge to those for `μ₀`,
then the integrals of `p ↦ exp (-x * p)` converge for every `x ≥ 0`. -/
lemma chafaiRescaled_tendsto_laplace_integral_of_weak {μ₀ : Measure ℝ≥0} {l : Filter ℕ}
    (hweak : ∀ g : BoundedContinuousFunction ℝ≥0 ℝ,
        Tendsto (fun n => ∫ p, g p ∂(chafaiRescaled f n)) l
          (nhds (∫ p, g p ∂μ₀)))
    {x : ℝ} (hx : 0 ≤ x) :
    Tendsto (fun n => ∫ p, Real.exp (-(x * (p : ℝ))) ∂(chafaiRescaled f n)) l
      (nhds (∫ p, Real.exp (-(x * (p : ℝ))) ∂μ₀)) := by
  simpa using hweak (laplaceKernelBoundedContinuous hx)

end TauCeti
end
end

/-! ### From `TauCeti.Analysis.CompletelyMonotone.Laplace.Representation` -/
section
section
open MeasureTheory ProbabilityTheory Set Filter
open scoped BoundedContinuousFunction ContDiff ENNReal NNReal Pointwise Topology
namespace TauCeti
/-- The Laplace transform of a measure on `ℝ≥0`, evaluated at a real parameter `t`.

The theorem statements in this file use the transform only for `0 ≤ t`; for negative `t`, the
Bochner integral is still a total Lean term, but may be the default value when the integrand is not
integrable. -/
noncomputable def laplaceTransform (μ : Measure ℝ≥0) (t : ℝ) : ℝ :=
  ∫ x, Real.exp (-(t * (x : ℝ))) ∂μ

/-- The defining formula for `laplaceTransform`. Not `@[simp]`: simp should not unfold the
abstraction into a raw integral; the evaluation lemmas below are the simp normal forms. -/
lemma laplaceTransform_apply (μ : Measure ℝ≥0) (t : ℝ) :
    laplaceTransform μ t = ∫ x, Real.exp (-(t * (x : ℝ))) ∂μ := by
  rw [laplaceTransform]

/-- A finite measure represents a function by its Laplace transform on the nonnegative
half-line. -/
def RepresentsLaplace (μ : Measure ℝ≥0) (f : ℝ → ℝ) : Prop :=
  IsFiniteMeasure μ ∧ ∀ t : ℝ, 0 ≤ t → f t = laplaceTransform μ t

/-- `RepresentsLaplace μ f` unfolds to finiteness of `μ` and equality with the Laplace transform
on the nonnegative half-line. -/
lemma representsLaplace_iff {f : ℝ → ℝ} {μ : Measure ℝ≥0} :
    RepresentsLaplace μ f ↔
      IsFiniteMeasure μ ∧ ∀ t : ℝ, 0 ≤ t → f t = laplaceTransform μ t :=
  Iff.rfl

namespace RepresentsLaplace
variable {f : ℝ → ℝ} {μ : Measure ℝ≥0}
end RepresentsLaplace
namespace RepresentsLaplace
end RepresentsLaplace
variable {f : ℝ → ℝ} {μ : Measure ℝ≥0}
namespace RepresentsLaplaceOnIoi
end RepresentsLaplaceOnIoi
end TauCeti
end
end

/-! ### From `TauCeti.Analysis.CompletelyMonotone.Bernstein.Tightness` -/
section
section
open MeasureTheory Set
open scoped ENNReal NNReal Topology
namespace TauCeti
variable {f : ℝ → ℝ}
/-- The rescaled Chafaï measures satisfy the uniform Markov tail estimate

`chafaiRescaled f n (R, ∞) ≤ ofReal (-f'(0)) / R`

for every positive `R`. The derivative is taken within `[0, ∞)`, as in the definition of
complete monotonicity. -/
lemma chafaiRescaled_measure_Ioi_le (hcm : IsCompletelyMonotone f) (n : ℕ) {R : ℝ≥0} (hR : R ≠ 0) :
    chafaiRescaled f n (Ioi R) ≤
      ENNReal.ofReal (-derivWithin f (Ici 0) 0) / (R : ℝ≥0∞) := by
  let μ := chafaiRescaled f n
  let moment : ℝ≥0 → ℝ≥0∞ := fun p => ENNReal.ofReal (p : ℝ)
  have hmoment_meas : AEMeasurable moment μ :=
    (ENNReal.measurable_ofReal.comp (by fun_prop : Measurable fun p : ℝ≥0 => (p : ℝ)))
      |>.aemeasurable
  have hsubset : Ioi R ⊆ {p | (R : ℝ≥0∞) ≤ moment p} := by
    intro p hp
    simpa [moment, ENNReal.ofReal_coe_nnreal] using hp.le
  calc
    μ (Ioi R) ≤ μ {p | (R : ℝ≥0∞) ≤ moment p} := measure_mono hsubset
    _ ≤ (∫⁻ p, moment p ∂μ) / (R : ℝ≥0∞) :=
      meas_ge_le_lintegral_div hmoment_meas (by simpa using hR) (by simp)
    _ ≤ ENNReal.ofReal (-derivWithin f (Ici 0) 0) / (R : ℝ≥0∞) :=
      ENNReal.div_le_div_right (chafaiRescaled_lintegral_coe_le f hcm n) _

/-- The family of all rescaled Chafaï approximating measures of a completely monotone function
is tight. Equivalently, for every positive error tolerance there is a compact interval
`[0, R] ⊆ ℝ≥0` whose complement has at most that much mass for every approximation order. -/
theorem isTightMeasureSet_range_chafaiRescaled (hcm : IsCompletelyMonotone f) :
    IsTightMeasureSet (range (chafaiRescaled f)) := by
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
  intro ε hε
  by_cases hε_top : ε = ∞
  · refine ⟨∅, isCompact_empty, fun μ _ => ?_⟩
    simp [hε_top]
  let D : ℝ≥0 := ⟨-derivWithin f (Ici 0) 0,
    neg_nonneg.mpr (hcm.derivWithin_nonpos le_rfl)⟩
  let R : ℝ≥0 := D / ε.toNNReal + 1
  have hR : R ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one (le_add_self))
  have hcompact : IsCompact (Iic R) := by
    have hset : Iic R = Icc (0 : ℝ≥0) R := by
      ext p
      simp
    rw [hset]
    exact isCompact_Icc
  refine ⟨Iic R, hcompact, ?_⟩
  intro μ hμ
  obtain ⟨n, rfl⟩ := hμ
  rw [compl_Iic]
  refine (chafaiRescaled_measure_Ioi_le hcm n hR).trans ?_
  have hD : ENNReal.ofReal (-derivWithin f (Ici 0) 0) = (D : ℝ≥0∞) := by
    exact (ENNReal.coe_nnreal_eq D).symm
  rw [hD]
  have hR_gt : D / ε.toNNReal < R := lt_add_one _
  have hε_toNNReal : ε.toNNReal ≠ 0 :=
    ENNReal.toNNReal_ne_zero.mpr ⟨hε.ne', hε_top⟩
  have hR_gt' : (D : ℝ≥0∞) / (ε.toNNReal : ℝ≥0∞) < (R : ℝ≥0∞) := by
    rw [← ENNReal.coe_div hε_toNNReal]
    exact_mod_cast hR_gt
  rw [ENNReal.coe_toNNReal hε_top] at hR_gt'
  exact (ENNReal.div_le_iff (by simpa using hR) (by simp)).2
    ((ENNReal.div_le_iff' hε.ne' hε_top).1 hR_gt'.le)

end TauCeti
end
end

/-! ### From `TauCeti.Topology.Compactness.Compact` -/
section
section
namespace TauCeti
open Filter Set Topology
variable {X : Type*} [TopologicalSpace X]
/-- A family that eventually lies in a compact set `s` along an ultrafilter converges along it to
a point of `s`. -/
theorem _root_.IsCompact.exists_tendsto_of_eventually_mem {ι : Type*} {s : Set X}
    (hs : IsCompact s) {U : Ultrafilter ι} {u : ι → X} (hu : ∀ᶠ i in U, u i ∈ s) :
    ∃ x ∈ s, Tendsto u U (𝓝 x) := by
  obtain ⟨x, hx, h⟩ := hs.ultrafilter_le_nhds' (U.map u) (Ultrafilter.mem_map.2 hu)
  exact ⟨x, hx, by rwa [Ultrafilter.coe_map] at h⟩

section TubeLemma
variable {α E P : Type*} [TopologicalSpace α] [CompactSpace α] [TopologicalSpace E]
  [TopologicalSpace P] {ι : α → P} {W : Set (E × P)}
end TubeLemma
end TauCeti
end
end

/-! ### From `TauCeti.MeasureTheory.Measure.Prokhorov` -/
section
section
open MeasureTheory Set Filter Topology TopologicalSpace
open scoped ENNReal NNReal Topology
namespace TauCeti
variable {α : Type*} [MeasurableSpace α] [TopologicalSpace α]
  [T2Space α] [BorelSpace α]
/-- **Prokhorov's theorem for finite measures.** A tight set of finite measures with uniformly
bounded total mass has compact closure in the topology of weak convergence.

This is the finite-measure counterpart of Mathlib's `isCompact_closure_of_isTightMeasureSet`
for probability measures. -/
theorem isCompact_closure_of_isTightMeasureSet_of_mass_le {S : Set (FiniteMeasure α)} {C : ℝ≥0}
    (hTight : IsTightMeasureSet {(μ : Measure α) | μ ∈ S}) (hmass : ∀ μ ∈ S, μ.mass ≤ C) :
    IsCompact (closure S) := by
  -- Choose a positive sequence decreasing to zero; these values are the tail tolerances in
  -- Prokhorov's compact set criterion.
  obtain ⟨u, -, hu_pos, hu_lim⟩ :
      ∃ u : ℕ → ℝ≥0, StrictAnti u ∧ (∀ n, 0 < u n) ∧ Tendsto u atTop (𝓝 0) :=
    exists_seq_strictAnti_tendsto 0
  have hchoose : ∀ j, ∃ K : Set α, IsCompact K ∧ ∀ μ ∈ S, (μ : Measure α) Kᶜ ≤ u j := fun j => by
    obtain ⟨K, hK, htail⟩ := isTightMeasureSet_iff_exists_isCompact_measure_compl_le.mp hTight
      (u j : ENNReal) (by exact_mod_cast hu_pos j)
    exact ⟨K, hK, fun μ hμ => htail μ ⟨μ, hμ, rfl⟩⟩
  choose K hK_comp hK_tail using hchoose
  -- Accumulating the compact sets supplied by tightness gives the monotone exhaustion that
  -- Mathlib's Prokhorov criterion expects.
  refine (isCompact_setOfPred_finiteMeasure_mass_le_compl_isCompact_le (E := α) C hu_lim
    (isCompact_accumulate hK_comp) (Or.inr Set.monotone_accumulate)).closure_of_subset
    fun μ hμ => ⟨hmass μ hμ, fun j => ENNReal.coe_le_coe.mp ?_⟩
  simpa using (measure_mono (compl_subset_compl.mpr
    (Set.subset_accumulate (s := K) (x := j)))).trans (hK_tail j μ hμ)

/-- **Prokhorov's theorem along an ultrafilter.** A family of Borel measures on a Hausdorff space
that frequently lies, along a filter `l`, in a tight set `S` with uniformly bounded mass has a weak
cluster limit along an ultrafilter `U ≤ l`, along which the family eventually lies in `S`.

The limit is a finite measure with the same mass bound, and the integrals of every bounded
continuous function converge along `U`; no first-countability assumption on `FiniteMeasure α` is
needed. The members of the family outside `S` are unconstrained and may have infinite mass. -/
lemma exists_ultrafilter_tendsto_integral_of_isTightMeasureSet {ι : Type*} (σ : ι → Measure α)
    (l : Filter ι) {S : Set (Measure α)} (C : ℝ≥0) (hmass : ∀ μ ∈ S, μ univ ≤ C)
    (hTight : IsTightMeasureSet S) (hσ : ∃ᶠ i in l, σ i ∈ S) :
    ∃ (μ₀ : Measure α) (U : Ultrafilter ι), ↑U ≤ l ∧ (∀ᶠ i in U, σ i ∈ S) ∧
      IsFiniteMeasure μ₀ ∧ μ₀ univ ≤ C ∧ ∀ g : BoundedContinuousFunction α ℝ,
        Tendsto (fun i => ∫ x, g x ∂σ i) U (𝓝 (∫ x, g x ∂μ₀)) := by
  -- The members of `S` are finite measures, and their closure in `FiniteMeasure α` is compact.
  let Sf : Set (FiniteMeasure α) := {μ | (μ : Measure α) ∈ S}
  have hSf_mass : Sf ⊆ {μ | μ.mass ≤ C} := fun μ hμ => by
    rw [mem_ofPred_eq, ← ENNReal.coe_le_coe, FiniteMeasure.ennreal_mass]
    exact hmass _ hμ
  have hcompact : IsCompact (closure Sf) := isCompact_closure_of_isTightMeasureSet_of_mass_le
    (hTight.subset (by rintro - ⟨μ, hμ, rfl⟩; exact hμ)) hSf_mass
  -- Index by the subtype of the `i` with `σ i ∈ S`; the filter `l` restricts to it because these
  -- indices are frequent in `l`.
  let s : Set ι := {i | σ i ∈ S}
  have : (comap ((↑) : s → ι) l).NeBot :=
    comap_neBot_iff_frequently.2 (by rwa [Subtype.range_coe])
  let σf : s → FiniteMeasure α := fun i => ⟨σ i, ⟨(hmass _ i.property).trans_lt ENNReal.coe_lt_top⟩⟩
  -- Along an ultrafilter below the restricted filter, `σf` converges weakly in the compact set.
  obtain ⟨U, hUle⟩ := Ultrafilter.exists_le (comap ((↑) : s → ι) l)
  obtain ⟨μf, hμf, hUtend⟩ := hcompact.exists_tendsto_of_eventually_mem (U := U) (u := σf)
    (.of_forall fun i => subset_closure i.property)
  refine ⟨μf, U.map (↑), map_le_iff_le_comap.2 hUle, ?_, inferInstance, ?_, fun g => ?_⟩
  · rw [Ultrafilter.coe_map]
    exact eventually_map.2 (.of_forall fun i => i.property)
  · rw [← FiniteMeasure.ennreal_mass, ENNReal.coe_le_coe]
    exact closure_minimal hSf_mass (isClosed_le FiniteMeasure.continuous_mass continuous_const) hμf
  · rw [Ultrafilter.coe_map, tendsto_map'_iff]
    simpa only [σf, Function.comp_def, FiniteMeasure.toMeasure_mk] using
      FiniteMeasure.tendsto_iff_forall_integral_tendsto.mp hUtend g

section ProbabilityMeasure
variable [PolishSpace α] {μs : ℕ → ProbabilityMeasure α} {μ : ProbabilityMeasure α}
end ProbabilityMeasure
end TauCeti
end
end

/-! ### From `TauCeti.Analysis.CompletelyMonotone.Bernstein.Theorem` -/
section
section
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal Topology
namespace TauCeti
variable {f : ℝ → ℝ}
/-- **The weak limit represents the non-constant part.** Along the ultrafilter `U`, the Chafaï
measures converge weakly to `μ₀`; passing the reconstruction identity to that limit replaces the
Bernstein kernel by `e^{-tp}` and exhibits `μ₀` as a representing measure for `f - L`, where `L` is
the limit of `f` at infinity. The atom carrying `L` itself is added by the caller.

Stated pointwise in `t`, which is how the caller consumes it. -/
private theorem sub_eq_integral_exp_neg_mul_of_weak_limit {L : ℝ} {C : ℝ≥0} {μ₀ : Measure ℝ≥0}
    {U : Ultrafilter ℕ} (hcm : IsCompletelyMonotone f) (hL : Tendsto f atTop (nhds L))
    (hmass' : ∀ᶠ n in atTop, (chafaiRescaled f n) univ ≤ (C : ℝ≥0∞)) (hU : (U : Filter ℕ) ≤ atTop)
    (hweak : ∀ g : BoundedContinuousFunction ℝ≥0 ℝ,
      Tendsto (fun n => ∫ x, g x ∂(chafaiRescaled f n)) (U : Filter ℕ) (nhds (∫ x, g x ∂μ₀)))
    {t : ℝ} (ht : 0 ≤ t) :
    f t - L = ∫ p : ℝ≥0, Real.exp (-(t * (p : ℝ))) ∂μ₀ := by
  have : (U : Filter ℕ).NeBot := U.neBot'
  have hlap : Tendsto (fun n => ∫ p, Real.exp (-(t * (p : ℝ))) ∂(chafaiRescaled f n))
      (U : Filter ℕ) (nhds (∫ p, Real.exp (-(t * (p : ℝ))) ∂μ₀)) :=
    chafaiRescaled_tendsto_laplace_integral_of_weak hweak ht
  have herr : Tendsto (fun n => ∫ p : ℝ≥0,
      (bernsteinKernel n t (p : ℝ) - Real.exp (-(t * (p : ℝ))))
        ∂(chafaiRescaled f n)) (U : Filter ℕ) (nhds 0) :=
    (integral_bernsteinKernel_sub_laplaceKernel_tendsto_zero_of_mass_bound
      (C := (C : ℝ)) (chafaiRescaled f)
      (hmass'.mono fun n hn => hn.trans
        (by simp [ENNReal.ofReal_coe_nnreal])) t ht).mono_left hU
  -- the mass bound makes the Chafaï measures eventually finite along `U`
  have hfin : ∀ᶠ n in (U : Filter ℕ), IsFiniteMeasure (chafaiRescaled f n) :=
    Filter.Eventually.mono (hU hmass') fun n hn => ⟨hn.trans_lt ENNReal.coe_lt_top⟩
  have hsplit : ∀ᶠ n in (U : Filter ℕ), ∫ p : ℝ≥0,
      (bernsteinKernel n t (p : ℝ) - Real.exp (-(t * (p : ℝ)))) ∂(chafaiRescaled f n)
        = (∫ p, bernsteinKernel n t (p : ℝ) ∂(chafaiRescaled f n))
          - ∫ p, Real.exp (-(t * (p : ℝ))) ∂(chafaiRescaled f n) := by
    filter_upwards [hfin] with n hn
    exact integral_sub (integrable_bernsteinKernel (chafaiRescaled f n) n ht)
      (integrable_exp_neg_mul (chafaiRescaled f n) ht)
  -- The Bernstein integral is constantly `f t - L` once `n ≥ 2`.
  have hconst : ∀ᶠ n in (U : Filter ℕ),
      ∫ p, bernsteinKernel n t (p : ℝ) ∂(chafaiRescaled f n) = f t - L := by
    have h2 : ∀ᶠ n in (U : Filter ℕ), 2 ≤ n := hU (eventually_ge_atTop 2)
    filter_upwards [h2] with n hn
    exact chafaiRescaled_integral_bernsteinKernel_eq_sub_tendsto_atTop f hcm n hn t ht L hL
  -- Pass to the limit: `(f t - L) - ∫ laplace → 0`.
  have hdiff : Tendsto (fun n => (f t - L)
      - ∫ p, Real.exp (-(t * (p : ℝ))) ∂(chafaiRescaled f n)) (U : Filter ℕ) (nhds 0) := by
    refine herr.congr' ?_
    filter_upwards [hconst, hsplit] with n hn hs
    rw [hs, hn]
  have hlim := hdiff.add hlap
  simp only [sub_add_cancel, zero_add] at hlim
  exact tendsto_nhds_unique tendsto_const_nhds hlim

/-- **Bernstein's theorem, existence half.** A completely monotone function on `[0, ∞)` is the
Laplace transform of a finite positive measure on `ℝ≥0`.

Uniqueness of that measure is not asserted here; it is `TauCeti.RepresentsLaplace.unique`, and
the two combine in the Hausdorff--Bernstein--Widder theorem. -/
theorem exists_representsLaplace_of_isCompletelyMonotone
    (hcm : IsCompletelyMonotone f) :
    ∃ μ : Measure ℝ≥0, RepresentsLaplace μ f := by
  obtain ⟨L, C, hL, hL_nn, -, hmass⟩ := chafaiRescaled_prokhorov_mass_bound f hcm
  have hmass' : ∀ n, (chafaiRescaled f n) univ ≤ (C : ℝ≥0∞) := fun n => (hmass n).2
  obtain ⟨μ₀, U, hU, -, hμ₀fin, -, hweak⟩ :=
    exists_ultrafilter_tendsto_integral_of_isTightMeasureSet (chafaiRescaled f) atTop C
      (forall_mem_range.2 hmass') (isTightMeasureSet_range_chafaiRescaled hcm)
      (.of_forall mem_range_self)
  -- The limit represents the non-constant part `f - L`.
  have key : ∀ t : ℝ, 0 ≤ t → f t - L = ∫ p, Real.exp (-(t * (p : ℝ))) ∂μ₀ :=
    fun t ht => sub_eq_integral_exp_neg_mul_of_weak_limit hcm hL (.of_forall hmass') hU hweak ht
  -- Add the atom `L · δ₀` to recover `f` itself.
  have := hμ₀fin
  refine ⟨μ₀ + L.toNNReal • Measure.dirac 0,
    representsLaplace_iff.mpr ⟨inferInstance, fun t ht => ?_⟩⟩
  rw [laplaceTransform_apply,
    integral_exp_neg_mul_add_smul_dirac_zero μ₀ _ ht, Real.coe_toNNReal L hL_nn]
  linarith [key t ht]

end TauCeti
end
end

end
