/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.

Adapted by Ming-Chih Kao (2026) from google-deepmind/formal-conjectures, commit
9097e2f90e66d2f6244209cb1c07f7120d17ec53, file `FormalConjectures/ErdosProblems/521.lean`:
the definitions used by the statement are collected in one module that imports only Mathlib. The changes are listed in
the module documentation of `Challenge.lean`.
-/
module

public import Mathlib

/-!
# Definitions used by the statement

A verbatim copy of the definitions in `Challenge.lean` (themselves copied from formal-conjectures),
so that the proof development and `Solution.lean` use the same declarations. Comparator checks that
they agree with the Challenge.
-/

@[expose] public section

namespace Erdos521

open MeasureTheory Filter Polynomial
open scoped Topology

/-- `true` encodes the sign `+1`, `false` the sign `-1`. -/
def sign (b : Bool) : ℝ := if b then 1 else -1

/-- One fair coin: the uniform probability measure on `Bool`. -/
noncomputable def fairCoin : Measure Bool :=
  (2 : ENNReal)⁻¹ • (Measure.dirac true + Measure.dirac false)

/-- The law of an infinite sequence of independent fair coins `(ε_k)_{k ≥ 0}`,
each uniform on `{-1, +1}`. -/
noncomputable def rademacherMeasure : Measure (ℕ → Bool) :=
  Measure.infinitePi (fun _ : ℕ ↦ fairCoin)

/-- The degree-`n` Littlewood polynomial `f_n(z) = ∑_{0 ≤ k ≤ n} ε_k z^k`. -/
noncomputable def littlewoodPolynomial (ω : ℕ → Bool) (n : ℕ) : ℝ[X] :=
  ∑ k ∈ Finset.range (n + 1), Polynomial.monomial k (sign (ω k))

/-- `R_n`: the number of distinct real roots of `f_n`. -/
noncomputable def realRootCount (ω : ℕ → Bool) (n : ℕ) : ℕ :=
  Set.ncard ((littlewoodPolynomial ω n).rootSet ℝ)

/-- The assertion asked about in Problem 521: almost surely `R_n / log n → 2/π`. -/
def Claim : Prop :=
  ∀ᵐ ω ∂rademacherMeasure,
    Tendsto (fun n : ℕ ↦ (realRootCount ω n : ℝ) / Real.log (n : ℝ))
      atTop (𝓝 ((2 : ℝ) / Real.pi))

end Erdos521

