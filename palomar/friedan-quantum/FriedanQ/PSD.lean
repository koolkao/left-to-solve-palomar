/-
Copyright 2026 Ming-Chih Kao. Licensed under the Apache License, Version 2.0;
see the LICENSE file at the root of this repository.
-/
module

public import FriedanQ.Corollaries

/-! Port: copied from `quantum-lean/FriedanQ/PSD.lean` of github.com/koolkao/friedan-entropy-inequality (commit 0f4ba65dc126f59e7158fbcbc01548baa78cf21d, Lean v4.36.0, Mathlib fc4f59e, physlib edc607c) and put into the module system (`module` header, `public import`, public section). The proofs are unchanged unless a comment marked `Port` says otherwise. -/

@[expose] public section

/-!
# Non-faithful states: the α-z version for positive semidefinite `ρ, σ`

Perturb `ρ_t = (ρ + t I)/(1 + n t)`, apply `friedan_alphaZ`, and let `t → 0⁺`, using the
continuity of the functional calculus in the matrix (Mathlib `Continuous.cfc_of_mem_nhdsSet`,
`x ↦ x^r` with `r ≥ 0` being continuous on `ℝ`). If `K = 0` the left side is `0`.
-/

open Real Finset Matrix Filter Topology
open scoped ComplexOrder Matrix.Norms.L2Operator

namespace FriedanQ

variable {d : Type*} [Fintype d] [DecidableEq d]

/-- `vN ≥ 0` for density matrices. -/
lemma vN_nonneg {ρ : Matrix d d ℂ} (hρ : ρ.PosSemidef) (hρ1 : ρ.trace = 1) : 0 ≤ vN ρ := by
  rw [vN, trace_cfc_re hρ.1]
  have hs : ∑ i, hρ.1.eigenvalues i = 1 := by
    have h := congrArg Complex.re (hρ.1.trace_eq_sum_eigenvalues.symm.trans hρ1)
    simpa [Complex.re_sum] using h
  refine sum_nonneg fun i _ => negMulLog_nonneg (hρ.eigenvalues_nonneg i) ?_
  rw [← hs]
  exact single_le_sum (fun j _ => hρ.eigenvalues_nonneg j) (mem_univ i)

/-- the perturbation, written with `|t|` so that it is continuous on all of `ℝ` -/
noncomputable def pert (A : Matrix d d ℂ) (t : ℝ) : Matrix d d ℂ :=
  (1 + (Fintype.card d : ℝ) * |t|)⁻¹ • (A + |t| • (1 : Matrix d d ℂ))

lemma pert_den_pos (t : ℝ) : (0 : ℝ) < 1 + (Fintype.card d : ℝ) * |t| := by
  have : (0 : ℝ) ≤ (Fintype.card d : ℝ) * |t| := mul_nonneg (Nat.cast_nonneg _) (abs_nonneg _)
  linarith

lemma pert_zero (A : Matrix d d ℂ) : pert A 0 = A := by simp [pert]

lemma pert_herm {A : Matrix d d ℂ} (hA : A.IsHermitian) (t : ℝ) : (pert A t).IsHermitian :=
  (hA.add (isHermitian_one.smul_real _)).smul_real _

lemma pert_cont (A : Matrix d d ℂ) : Continuous (pert A) := by
  unfold pert
  have h1 : Continuous fun t : ℝ => (1 + (Fintype.card d : ℝ) * |t|)⁻¹ :=
    (continuous_const.add (continuous_const.mul continuous_abs)).inv₀
      (fun t => (pert_den_pos (d := d) t).ne')
  exact h1.smul (continuous_const.add (continuous_abs.smul continuous_const))

lemma pert_posDef {A : Matrix d d ℂ} (hA : A.PosSemidef) {t : ℝ} (ht : 0 < t) :
    (pert A t).PosDef := by
  unfold pert
  have h1 : (|t| • (1 : Matrix d d ℂ)).PosDef := PosDef.one.smul (abs_pos.2 ht.ne')
  exact (PosDef.posSemidef_add hA h1).smul (inv_pos.2 (pert_den_pos (d := d) t))

lemma pert_trace {A : Matrix d d ℂ} (hA : A.trace = 1) (t : ℝ) : (pert A t).trace = 1 := by
  unfold pert
  rw [trace_smul, trace_add, trace_smul, trace_one, hA]
  have hpos : (0 : ℝ) < 1 + (Fintype.card d : ℝ) * |t| := by positivity
  rw [Complex.real_smul, Complex.real_smul]
  push_cast
  field_simp

lemma cfc_cont (f : ℝ → ℝ) (hf : Continuous f) {B : ℝ → Matrix d d ℂ} (hB : Continuous B)
    (hBh : ∀ t, (B t).IsHermitian) : Continuous (fun t => cfc f (B t)) :=
  Continuous.cfc_of_mem_nhdsSet f (s := Set.univ) Filter.univ_mem hB (fun t => hBh t)
    hf.continuousOn

/-- the α-z mean as a function of the pair -/
noncomputable def azM (a z : ℝ) (ρ σ : Matrix d d ℂ) : Matrix d d ℂ :=
  cfc (fun x : ℝ => x ^ z)
    (cfc (fun x : ℝ => x ^ (a / (2 * z))) ρ * cfc (fun x : ℝ => x ^ ((1 - a) / z)) σ *
      cfc (fun x : ℝ => x ^ (a / (2 * z))) ρ)

lemma inner_herm (a z : ℝ) (ρ σ : Matrix d d ℂ) :
    (cfc (fun x : ℝ => x ^ (a / (2 * z))) ρ * cfc (fun x : ℝ => x ^ ((1 - a) / z)) σ *
      cfc (fun x : ℝ => x ^ (a / (2 * z))) ρ).IsHermitian := by
  have := isHermitian_conjTranspose_mul_mul (cfc (fun x : ℝ => x ^ (a / (2 * z))) ρ)
    (cfc_predicate (fun x : ℝ => x ^ ((1 - a) / z)) σ :
      (cfc (fun x : ℝ => x ^ ((1 - a) / z)) σ).IsHermitian)
  rwa [conjT_cfc] at this

/-- **α-z version for positive semidefinite density matrices** (`z > 0`, `0 ≤ a ≤ 1`). -/
theorem friedan_alphaZ_psd (ρ σ : Matrix d d ℂ) (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef)
    (hρ1 : ρ.trace = 1) (hσ1 : σ.trace = 1) {a z : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hz : 0 < z) :
    (trace (azM a z ρ σ)).re ^ 2 * vN ((trace (azM a z ρ σ)).re⁻¹ • azM a z ρ σ) ≤
      a * vN ρ + (1 - a) * vN σ := by
  set ρt := pert ρ
  set σt := pert σ
  -- continuity of the mean along the perturbation
  have hr1 : Continuous fun x : ℝ => x ^ (a / (2 * z)) :=
    continuous_rpow_const (div_nonneg ha0 (by positivity))
  have hr2 : Continuous fun x : ℝ => x ^ ((1 - a) / z) :=
    continuous_rpow_const (div_nonneg (by linarith) hz.le)
  have hr3 : Continuous fun x : ℝ => x ^ z := continuous_rpow_const hz.le
  have hR := cfc_cont _ hr1 (pert_cont ρ) (pert_herm hρ.1)
  have hT := cfc_cont _ hr2 (pert_cont σ) (pert_herm hσ.1)
  have hN : Continuous fun t => cfc (fun x : ℝ => x ^ (a / (2 * z))) (ρt t) *
      cfc (fun x : ℝ => x ^ ((1 - a) / z)) (σt t) * cfc (fun x : ℝ => x ^ (a / (2 * z))) (ρt t) :=
    (hR.mul hT).mul hR
  have hM : Continuous fun t => azM a z (ρt t) (σt t) :=
    cfc_cont _ hr3 hN (fun t => inner_herm a z _ _)
  have hMh : ∀ t, (azM a z (ρt t) (σt t)).IsHermitian := fun t => cfc_predicate _ _
  have hK : Continuous fun t => (trace (azM a z (ρt t) (σt t))).re :=
    Complex.continuous_re.comp hM.matrix_trace
  -- right side
  have hvN : ∀ {A : Matrix d d ℂ}, A.IsHermitian → Continuous fun t => vN (pert A t) := by
    intro A hA
    exact Complex.continuous_re.comp
      (cfc_cont _ continuous_negMulLog (pert_cont A) (pert_herm hA)).matrix_trace
  have hG : Tendsto (fun t => a * vN (ρt t) + (1 - a) * vN (σt t)) (𝓝[>] 0)
      (𝓝 (a * vN ρ + (1 - a) * vN σ)) := by
    have hc : Continuous fun t => a * vN (pert ρ t) + (1 - a) * vN (pert σ t) :=
      (continuous_const.mul (hvN hρ.1)).add (continuous_const.mul (hvN hσ.1))
    have h := hc.tendsto 0
    simp only [ρt, σt, pert_zero] at h
    exact h.mono_left nhdsWithin_le_nhds
  set K0 := (trace (azM a z ρ σ)).re
  have hK0 : K0 = (trace (azM a z (ρt 0) (σt 0))).re := by simp [ρt, σt, pert_zero, K0]
  rcases eq_or_ne K0 0 with h0 | h0
  · rw [h0]
    have := vN_nonneg hρ hρ1
    have := vN_nonneg hσ hσ1
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul]
    nlinarith
  -- K0 > 0 (limit of positive values)
  have hKpos : ∀ t, 0 < t → 0 ≤ (trace (azM a z (ρt t) (σt t))).re := by
    intro t ht
    rw [azM, trace_cfc_re (inner_herm a z _ _)]
    have hN' := inner_herm a z (ρt t) (σt t)
    exact sum_nonneg fun i _ => by
      have hpd : (cfc (fun x : ℝ => x ^ (a / (2 * z))) (ρt t) *
          cfc (fun x : ℝ => x ^ ((1 - a) / z)) (σt t) *
            cfc (fun x : ℝ => x ^ (a / (2 * z))) (ρt t)).PosSemidef := by
        have := (cfc_posDef (pert_posDef hσ ht) (f := fun x : ℝ => x ^ ((1 - a) / z))
          (fun s hs => rpow_pos_of_pos hs _)).posSemidef.conjTranspose_mul_mul_same
          (cfc (fun x : ℝ => x ^ (a / (2 * z))) (ρt t))
        rwa [conjT_cfc] at this
      exact rpow_nonneg (hpd.eigenvalues_nonneg i) _
  have hK0nn : 0 ≤ K0 := by
    rw [hK0]
    exact ge_of_tendsto ((hK.tendsto 0).mono_left nhdsWithin_le_nhds)
      (eventually_nhdsWithin_of_forall fun t (ht : t ∈ Set.Ioi 0) => hKpos t ht)
  have hK0pos : 0 < K0 := lt_of_le_of_ne hK0nn (Ne.symm h0)
  -- left side, with `K` replaced by `max K (K0/2)` (continuous, positive)
  set h := fun t => max ((trace (azM a z (ρt t) (σt t))).re) (K0 / 2)
  have hhc : Continuous h := hK.max continuous_const
  have hhpos : ∀ t, 0 < h t := fun t => lt_of_lt_of_le (by linarith) (le_max_right _ _)
  set F := fun t => (h t) ^ 2 * vN ((h t)⁻¹ • azM a z (ρt t) (σt t))
  have hFc : Continuous F := by
    refine (hhc.pow 2).mul (Complex.continuous_re.comp (Continuous.matrix_trace ?_))
    exact cfc_cont _ continuous_negMulLog
      ((hhc.inv₀ fun t => (hhpos t).ne').smul hM) (fun t => (hMh t).smul_real _)
  have hF0 : F 0 = K0 ^ 2 * vN (K0⁻¹ • azM a z ρ σ) := by
    have : h 0 = K0 := by
      simp only [h, ρt, σt, pert_zero]; exact max_eq_left (by linarith)
    simp only [F, this, ρt, σt, pert_zero]
  have hFt : Tendsto F (𝓝[>] 0) (𝓝 (K0 ^ 2 * vN (K0⁻¹ • azM a z ρ σ))) :=
    hF0 ▸ (hFc.tendsto 0).mono_left nhdsWithin_le_nhds
  -- eventually `h t = K t`, and there the faithful theorem applies
  have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), F t ≤ a * vN (ρt t) + (1 - a) * vN (σt t) := by
    have hnear : ∀ᶠ t in 𝓝 (0 : ℝ), K0 / 2 < (trace (azM a z (ρt t) (σt t))).re := by
      have := (hK.tendsto 0)
      rw [← hK0] at this
      exact this.eventually (lt_mem_nhds (by linarith))
    filter_upwards [hnear.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with t ht htpos
    have hht : h t = (trace (azM a z (ρt t) (σt t))).re := max_eq_left ht.le
    simp only [F, hht]
    exact friedan_alphaZ (ρt t) (σt t) (pert_posDef hρ htpos) (pert_posDef hσ htpos)
      (pert_trace hρ1 t) (pert_trace hσ1 t) ha0 ha1 hz
  exact le_of_tendsto_of_tendsto hFt hG hev

end FriedanQ

end
