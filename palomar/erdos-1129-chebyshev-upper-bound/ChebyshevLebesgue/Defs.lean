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
9097e2f90e66d2f6244209cb1c07f7120d17ec53, files `FormalConjectures/ErdosProblems/1129.lean`:
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

namespace Erdos1129

/-- A node set: $n$ points $-1\le x_1<\dots<x_n\le 1$, written as a strictly increasing map
`Fin n → ℝ` with values in $[-1,1]$. Distinct nodes are needed for the fundamental functions
$l_k$ to be defined (otherwise a division by zero gives a junk value). Ordering the nodes is no
restriction, because everything below is symmetric in the nodes. -/
def IsNodeSet {n : ℕ} (x : Fin n → ℝ) : Prop :=
  StrictMono x ∧ ∀ i, x i ∈ Set.Icc (-1 : ℝ) 1

/-- The Lebesgue function $L_x(t)=\sum_k\lvert l_k(t)\rvert$ of the nodes `x`, where
$l_k(t)=\prod_{i\ne k}\frac{t-x_i}{x_k-x_i}$ is the Lagrange basis polynomial `Lagrange.basis`
(see `lebesgueFunction_eq` for the explicit product). -/
noncomputable def lebesgueFunction {n : ℕ} (x : Fin n → ℝ) (t : ℝ) : ℝ :=
  ∑ k, |(Lagrange.basis Finset.univ x k).eval t|

/-- The Lebesgue constant $\Lambda(x)=\max_{t\in[-1,1]}L_x(t)$ of the nodes `x`. For a node set,
$L_x$ is continuous, so the supremum is attained. -/
noncomputable def lebesgueConstant {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  sSup (lebesgueFunction x '' Set.Icc (-1 : ℝ) 1)

/-- `x` is the node set of the zeros of the Chebyshev polynomial $T_n$, in increasing order.
$T_n$ has $n$ simple zeros in $(-1,1)$, so there is exactly one such `x`. -/
def IsChebyshevNodes {n : ℕ} (x : Fin n → ℝ) : Prop :=
  IsNodeSet x ∧ ∀ j, (Polynomial.Chebyshev.T ℝ (n : ℤ)).eval (x j) = 0

end Erdos1129

