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

