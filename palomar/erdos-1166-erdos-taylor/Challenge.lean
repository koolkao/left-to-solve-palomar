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
9097e2f90e66d2f6244209cb1c07f7120d17ec53, files `FormalConjectures/ErdosProblems/1165.lean`, `FormalConjectures/ErdosProblems/1166.lean`:
the statement and the definitions it uses are collected in one module that imports only Mathlib. The changes are listed in
the module documentation of `Challenge.lean`.
-/
module

public import Mathlib

/-!
# Erdős Problem 1166: the Erdős–Taylor theorem on the maximal local time of the planar walk

This is the statement `Erdos1166.erdos_1166.variants.erdos_taylor` of
[formal-conjectures](https://github.com/google-deepmind/formal-conjectures) at commit
`9097e2f90e66d2f6244209cb1c07f7120d17ec53` (`FormalConjectures/ErdosProblems/1166.lean`), with the definitions it uses copied in so
that this file imports only Mathlib. The walk and its local times come from
`FormalConjectures/ErdosProblems/1165.lean`.

The text of each definition and of the theorem is unchanged. One dependency changed meaning
between the Mathlib versions: `MeasureTheory.pdf.IsUniform X s P μ` was `Measure.map X P = μ[|s]` at
Mathlib `0df444a` (used by formal-conjectures) and is `HasLaw X μ[|s] P`, that is
`AEMeasurable X P ∧ Measure.map X P = μ[|s]`, at Mathlib `fc4f59e` (used here). Since
`IsSimpleRandomWalkSteps` also requires every step to be measurable, the hypothesis
`IsSimpleRandomWalkSteps X` is equivalent under both readings. The formal-conjectures attributes
(`@[category …]`, `@[AMS …]`) are omitted, and so are the declarations of those files that this
statement does not use. Docstrings are kept as written, so some of them mention declarations
of the formal-conjectures files (such as other variants or API lemmas) that are not copied here.

*References:*
- [erdosproblems.com/1166](https://www.erdosproblems.com/1166)
- [ErTa60] Erdős, P. and Taylor, S. J., *Some problems concerning the structure of random walk
  paths*. Acta Math. Acad. Sci. Hungar. 11 (1960), 137--162.
-/

@[expose] public section

open MeasureTheory Filter
open scoped ProbabilityTheory Topology Real ENNReal

namespace Erdos1165

/-- The four unit steps $(\pm 1, 0)$ and $(0, \pm 1)$ of the simple random walk on
$\mathbb{Z}^2$. -/
def steps : Set (ℤ × ℤ) := {(1, 0), (-1, 0), (0, 1), (0, -1)}

/-- `X k` is the $k$-th step of a simple random walk on $\mathbb{Z}^2$, on the probability space
`Ω`: the steps are random variables, they are independent, and each is uniformly distributed on
`steps`. -/
structure IsSimpleRandomWalkSteps {Ω : Type*} [MeasureSpace Ω] (X : ℕ → Ω → ℤ × ℤ) : Prop where
  /-- Each step is a random variable. -/
  measurable (k : ℕ) : Measurable (X k)
  /-- The steps are independent. -/
  indep : ProbabilityTheory.iIndepFun X ℙ
  /-- Each step is uniform on `steps`. -/
  isUniform (k : ℕ) : MeasureTheory.pdf.IsUniform (X k) steps ℙ Measure.count

/-- The position $s_n = \sum_{k<n} X_k$ of the walk after $n$ steps, so that $s_0 = 0$. -/
def position {Ω : Type*} (X : ℕ → Ω → ℤ × ℤ) (n : ℕ) (ω : Ω) : ℤ × ℤ :=
  ∑ k ∈ Finset.range n, X k ω

/-- The local time $f_n(x)=\#\{0\le k\le n : s_k=x\}$ of the site `x` at time `n`. -/
def localTime {Ω : Type*} (X : ℕ → Ω → ℤ × ℤ) (n : ℕ) (ω : Ω) (x : ℤ × ℤ) : ℕ :=
  ((Finset.range (n + 1)).filter fun k ↦ position X k ω = x).card

end Erdos1165

namespace Erdos1166

open Erdos1165

/-- The maximal local time $\max_y f_n(y)$ at time `n`. It is the largest of the local times of
the sites $s_0,\ldots,s_n$ visited so far, because every other site has local time $0$. -/
def maxLocalTime {Ω : Type*} (X : ℕ → Ω → ℤ × ℤ) (n : ℕ) (ω : Ω) : ℕ :=
  (Finset.range (n + 1)).sup fun k ↦ localTime X n ω (position X k ω)

end Erdos1166

namespace Erdos1166

open Erdos1165

/--
Erdős and Taylor [ErTa60, p. 162] proved that, for the simple random walk on $\mathbb{Z}^2$, if
$T_n$ is the maximal number of visits to a point in the first $n$ steps, then almost surely
$$\frac{1}{4\pi}\leq\liminf_{n\to\infty}\frac{T_n}{(\log n)^2}
  \leq\limsup_{n\to\infty}\frac{T_n}{(\log n)^2}\leq\frac{1}{\pi}.$$
They conjectured that the limit exists and equals $1/\pi$, see
`erdos_1166.variants.dembo_peres_rosen_zeitouni`.

We use `maxLocalTime`, which also counts the visit at time $0$. This changes $T_n$ by at most one.
The bounds are stated with $\varepsilon$ to avoid the junk values of `liminf` and `limsup`.
-/
theorem erdos_1166.variants.erdos_taylor {Ω : Type*} [MeasureSpace Ω]
    [IsProbabilityMeasure (ℙ : Measure Ω)] {X : ℕ → Ω → ℤ × ℤ}
    (hX : IsSimpleRandomWalkSteps X) :
    ∀ᵐ ω, ∀ ε : ℝ, 0 < ε →
      (∀ᶠ n : ℕ in atTop, 1 / (4 * π) - ε ≤ (maxLocalTime X n ω : ℝ) / Real.log n ^ 2) ∧
      (∀ᶠ n : ℕ in atTop, (maxLocalTime X n ω : ℝ) / Real.log n ^ 2 ≤ 1 / π + ε) := by
  sorry

end Erdos1166
