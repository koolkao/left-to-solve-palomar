/-
Copyright 2026 Ming-Chih Kao. Licensed under the Apache License, Version 2.0;
see the LICENSE file at the root of this repository.
-/
module

public import E521.Defs
public import E521.Part7

/-!
# Erdős 521 in formal-conjectures vocabulary

`E521.erdos521_false_le` (in `E521/Part7.lean`) says: for any root count `Rc n ω` at most the number
of real roots of `fR n ω` with multiplicity, it is not true that `Rc n ω / log n` tends to `2/π`
almost surely under `μS`. Here `littlewoodPolynomial ω n = fR n ω` and `rademacherMeasure = μS`, and both the
distinct count `realRootCount` and the count with multiplicity are at most `(fR n ω).roots.card`.
-/

@[expose] public section

open MeasureTheory Filter Polynomial
open scoped Topology

namespace Erdos521

lemma rademacherMeasure_eq : rademacherMeasure = E521.μS := rfl

lemma littlewoodPolynomial_eq (ω : ℕ → Bool) (n : ℕ) : littlewoodPolynomial ω n = E521.fR n ω := by
  unfold littlewoodPolynomial E521.fR E521D.T
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← Polynomial.C_mul_X_pow_eq_monomial]
  rfl

lemma realRootCount_le (ω : ℕ → Bool) (n : ℕ) :
    realRootCount ω n ≤ (E521.fR n ω).roots.card := by
  classical
  unfold realRootCount
  rw [littlewoodPolynomial_eq, Polynomial.rootSet_def, Set.ncard_coe_finset, aroots_def,
    Algebra.algebraMap_self, Polynomial.map_id]
  exact Multiset.toFinset_card_le _

theorem erdos_521_proof : ¬ Claim := by
  unfold Claim
  rw [rademacherMeasure_eq]
  exact E521.erdos521_false_le (fun n ω => realRootCount ω n) (fun n ω => realRootCount_le ω n)

theorem erdos_521_with_multiplicity_proof :
    ¬ ∀ᵐ ω ∂rademacherMeasure,
      Tendsto (fun n : ℕ ↦ ((littlewoodPolynomial ω n).roots.card : ℝ) / Real.log (n : ℝ))
        atTop (𝓝 ((2 : ℝ) / Real.pi)) := by
  rw [rademacherMeasure_eq]
  exact E521.erdos521_false_le (fun n ω => (littlewoodPolynomial ω n).roots.card)
    (fun n ω => by rw [littlewoodPolynomial_eq])

end Erdos521
