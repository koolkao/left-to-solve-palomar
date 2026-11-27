/-
Copyright 2026 Ming-Chih Kao. Licensed under the Apache License, Version 2.0;
see the LICENSE file at the root of this repository.
-/
module

public import FriedanQ.MatrixAZ

/-! Port: copied from `quantum-lean/FriedanQ/Corollaries.lean` of github.com/koolkao/friedan-entropy-inequality (commit 0f4ba65dc126f59e7158fbcbc01548baa78cf21d, Lean v4.36.0, Mathlib fc4f59e, physlib edc607c) and put into the module system (`module` header, `public import`, public section). The proofs are unchanged unless a comment marked `Port` says otherwise. -/

@[expose] public section

/-!
# Petz and sandwiched versions (corollaries of `friedan_alphaZ`)
-/

open Real Finset Matrix
open scoped ComplexOrder

namespace FriedanQ

variable {d : Type*} [Fintype d] [DecidableEq d]

/-- **Petz version**: `M = ρ^{a/2} σ^{1-a} ρ^{a/2}` (`K = tr ρ^a σ^{1-a}`). -/
theorem friedan_petz (ρ σ : Matrix d d ℂ) (hρ : ρ.PosDef) (hσ : σ.PosDef)
    (hρ1 : ρ.trace = 1) (hσ1 : σ.trace = 1) {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    let M := cfc (fun x : ℝ => x ^ (a / 2)) ρ * cfc (fun x : ℝ => x ^ (1 - a)) σ *
      cfc (fun x : ℝ => x ^ (a / 2)) ρ
    (trace M).re ^ 2 * vN ((trace M).re⁻¹ • M) ≤ a * vN ρ + (1 - a) * vN σ := by
  intro M
  have h := friedan_alphaZ ρ σ hρ hσ hρ1 hσ1 ha0 ha1 one_pos
  simp only [mul_one, div_one, rpow_one] at h
  have hMh : M.IsHermitian := by
    have := isHermitian_conjTranspose_mul_mul (cfc (fun x : ℝ => x ^ (a / 2)) ρ)
      (cfc_predicate (fun x : ℝ => x ^ (1 - a)) σ : (cfc (fun x : ℝ => x ^ (1 - a)) σ).IsHermitian)
    rwa [conjT_cfc] at this
  have hc : cfc (fun x : ℝ => x) (cfc (fun x : ℝ => x ^ (a / 2)) ρ *
      cfc (fun x : ℝ => x ^ (1 - a)) σ * cfc (fun x : ℝ => x ^ (a / 2)) ρ) =
      cfc (fun x : ℝ => x ^ (a / 2)) ρ * cfc (fun x : ℝ => x ^ (1 - a)) σ *
        cfc (fun x : ℝ => x ^ (a / 2)) ρ := cfc_id' ℝ _ hMh
  simp only [hc] at h
  exact h

/-- **Sandwiched version** (`0 < a ≤ 1`): `M = (σ^{(1-a)/2a} ρ σ^{(1-a)/2a})^a`. -/
theorem friedan_sandwiched (ρ σ : Matrix d d ℂ) (hρ : ρ.PosDef) (hσ : σ.PosDef)
    (hρ1 : ρ.trace = 1) (hσ1 : σ.trace = 1) {a : ℝ} (ha0 : 0 < a) (ha1 : a ≤ 1) :
    let M := cfc (fun x : ℝ => x ^ a)
      (cfc (fun x : ℝ => x ^ ((1 - a) / (2 * a))) σ * ρ * cfc (fun x : ℝ => x ^ ((1 - a) / (2 * a))) σ)
    (trace M).re ^ 2 * vN ((trace M).re⁻¹ • M) ≤ a * vN ρ + (1 - a) * vN σ := by
  intro M
  have h := friedan_alphaZ σ ρ hσ hρ hσ1 hρ1 (a := 1 - a) (z := a) (by linarith) (by linarith) ha0
  have e1 : 1 - (1 - a) = a := by ring
  have e2 : a / a = 1 := div_self ha0.ne'
  simp only [e1, e2, rpow_one] at h
  have hc : cfc (fun x : ℝ => x) ρ = ρ := cfc_id' ℝ ρ hρ.1
  simp only [hc] at h
  linarith
end FriedanQ

end
