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

