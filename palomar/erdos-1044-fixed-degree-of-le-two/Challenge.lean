/-
Copyright 2025 The Formal Conjectures Authors.
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
9097e2f90e66d2f6244209cb1c07f7120d17ec53, files `FormalConjectures/ErdosProblems/1041.lean`, `FormalConjectures/ErdosProblems/1044.lean`:
the statement and the definitions it uses are collected in one module that imports only Mathlib. The changes are listed in
the module documentation of `Challenge.lean`.
-/
module

public import Mathlib

/-!
# Erdős Problem 1044 for degrees 1 and 2: $z^n - 1$ minimises the boundary length

This is the statement `Erdos1044.erdos_1044.variants.fixed_degree_of_le_two` of
[formal-conjectures](https://github.com/google-deepmind/formal-conjectures) at commit
`9097e2f90e66d2f6244209cb1c07f7120d17ec53` (`FormalConjectures/ErdosProblems/1044.lean`), with the definitions it uses copied in so
that this file imports only Mathlib. `Erdos1041.length` comes from
`FormalConjectures/ErdosProblems/1041.lean`.

The text of each definition and of the theorem is unchanged; the formal-conjectures attributes
(`@[category …]`, `@[AMS …]`) are omitted, and so are the declarations of those files that this
statement does not use. Docstrings are kept as written, so some of them mention declarations
of the formal-conjectures files (such as other variants or API lemmas) that are not copied here.

*References:*
- [erdosproblems.com/1044](https://www.erdosproblems.com/1044)
- [EHP58] Erdős, P., Herzog, F. and Piranian, G., *Metric properties of polynomials*.
  J. Analyse Math. 6 (1958), 125-148.
-/

@[expose] public section

open Polynomial ENNReal

namespace Erdos1041

open MeasureTheory

/--
The length of a subset $s$ of $\mathbb{C}$ is defined to be its 1-dimensional
Hausdorff measure $\mathcal{H}^1(s)$.
-/
noncomputable def length (s : Set ℂ) : ℝ≥0∞ := μH[1] s

end Erdos1041

namespace Erdos1044

/--
The polynomials under consideration: those of the form $f(z)=\prod_{i=1}^n(z-z_i)$, for some
$n\geq 1$, where $\lvert z_i\rvert\leq 1$ for all $i$.
-/
def IsAdmissible (f : ℂ[X]) : Prop :=
  ∃ n : ℕ, 0 < n ∧ ∃ z : Fin n → ℂ, (∀ i, ‖z i‖ ≤ 1) ∧ f = ∏ i, (X - C (z i))

/--
$\Lambda(f)$, the maximum of the lengths of the boundaries of the connected components of
$\{ z: \lvert f(z)\rvert<1\}$, where the length of a subset of $\mathbb{C}$ is its
$1$-dimensional Hausdorff measure.
-/
noncomputable def maxBoundaryLength (f : ℂ[X]) : ℝ≥0∞ :=
  ⨆ z ∈ {w : ℂ | ‖f.eval w‖ < 1},
    Erdos1041.length (frontier (connectedComponentIn {w : ℂ | ‖f.eval w‖ < 1} z))

end Erdos1044

namespace Erdos1044

/--
Tang also suggests that, if the degree $n$ is fixed, then the infimum over all such $f$ of
degree $n$ is attained by $f_n(z)=z^n-1$ (and proves this for $n=1$ and $n=2$).
-/
theorem erdos_1044.variants.fixed_degree_of_le_two (n : ℕ) (hn : n = 1 ∨ n = 2) :
    IsLeast {L : ℝ≥0∞ | ∃ f : ℂ[X], IsAdmissible f ∧ f.natDegree = n ∧ maxBoundaryLength f = L}
      (maxBoundaryLength (X ^ n - 1)) := by
  sorry

end Erdos1044
