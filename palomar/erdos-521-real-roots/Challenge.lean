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
the statement and the definitions it uses are collected in one module that imports only Mathlib, and one
variant (counting roots with multiplicity) is added. The changes are listed in the module documentation below.
-/
module

public import Mathlib

/-!
# Erdős Problem 521: the almost-sure limit `R_n / log n → 2/π` fails

This is the statement `Erdos521.erdos_521` of
[formal-conjectures](https://github.com/google-deepmind/formal-conjectures) at commit
`9097e2f90e66d2f6244209cb1c07f7120d17ec53` (`FormalConjectures/ErdosProblems/521.lean`), with the
definitions it uses (`sign`, `fairCoin`, `rademacherMeasure`, `littlewoodPolynomial`, `realRootCount`,
`Claim`) copied in so that this file imports only Mathlib.

The text of each definition and of `erdos_521` is unchanged; the formal-conjectures attributes
(`@[category …]`, `@[AMS …]`, `formal_proof …`, the `set_option` for its linter) are omitted, and so are the
API lemmas `fairCoin_apply` and `fairCoin_isProbabilityMeasure`, which the statement does not use. The
docstring of `erdos_521` is kept as written.

Added here (not in formal-conjectures): `Erdos521.erdos_521_with_multiplicity`, the same conclusion when
`R_n` counts the real roots of `f_n` *with multiplicity* (`(littlewoodPolynomial ω n).roots.card`; the
real polynomial's `roots` are its real roots). This is the reading of the Left to Solve statement
`statements/erdos-521.lean` that the original proof was written for. Neither form implies the other
formally; the proof gives both, since both counts are at most the count with multiplicity.

*Reference:* [erdosproblems.com/521](https://www.erdosproblems.com/521); P. Erdős and A. C. Offord, *On the
number of real roots of a random algebraic equation*, Proc. London Math. Soc. (3) 6 (1956), 139–160.
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

namespace Erdos521

open MeasureTheory Filter Polynomial
open scoped Topology

/--
Let $(\epsilon_k)_{k\geq 0}$ be independently uniformly chosen at random from
$\{-1,1\}$. If $R_n$ counts the number of real roots of
$f_n(z)=\sum_{0\leq k\leq n}\epsilon_k z^k$ then is it true that, almost surely,
$$\lim_{n\to \infty}\frac{R_n}{\log n}=\frac{2}{\pi}?$$

The answer is no: this almost-sure limit fails. This result was obtained first by others, who
deserve the credit for the problem; the link is to an independent machine-checked proof by
Star Fleet Math.
-/
theorem erdos_521 : ¬ Claim := by
  sorry

/-- The same failure when $R_n$ counts the real roots of $f_n$ with multiplicity: it is not true that,
almost surely, `(number of real roots of f_n, with multiplicity) / log n` tends to $2/\pi$ (almost-sure
convergence fails; this does not claim divergence almost surely). -/
theorem erdos_521_with_multiplicity :
    ¬ ∀ᵐ ω ∂rademacherMeasure,
      Tendsto (fun n : ℕ ↦ ((littlewoodPolynomial ω n).roots.card : ℝ) / Real.log (n : ℝ))
        atTop (𝓝 ((2 : ℝ) / Real.pi)) := by
  sorry

end Erdos521
