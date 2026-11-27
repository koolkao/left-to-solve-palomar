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
the statement and the definitions it uses are collected in one module that imports only Mathlib. The changes are listed in
the module documentation of `Challenge.lean`.
-/
module

public import Mathlib

/-!
# Erdős Problem 1129: the Lebesgue constant of the Chebyshev nodes is $\frac{2}{\pi}\log n + O(1)$

This is the statement `Erdos1129.erdos_1129.variants.chebyshev_upper_bound` of
[formal-conjectures](https://github.com/google-deepmind/formal-conjectures) at commit
`9097e2f90e66d2f6244209cb1c07f7120d17ec53` (`FormalConjectures/ErdosProblems/1129.lean`), with the
definitions it uses (`IsNodeSet`, `lebesgueFunction`, `lebesgueConstant`, `IsChebyshevNodes`)
copied in so that this file imports only Mathlib.

The text of each definition and of the theorem is unchanged; the formal-conjectures attributes
(`@[category …]`, `@[AMS …]`) are omitted, and so are the declarations of those files that this
statement does not use. Docstrings are kept as written, so some of them mention declarations
of the formal-conjectures files (such as other variants or API lemmas) that are not copied here.

*References:*
- [erdosproblems.com/1129](https://www.erdosproblems.com/1129)
- [Er61c] Erdős, P., *Problems and results on the theory of interpolation. II*. Acta Math.
  Acad. Sci. Hungar. 12 (1961), 235-244.
- [Er67] Erdős, P., *Problems and results on the convergence and divergence properties of the
  Lagrange interpolation polynomials and some extremal problems*. Mathematica (Cluj) (1967), 65-73.
- [Ib16] Ibrahimoglu, B. A., *Lebesgue functions and Lebesgue constants in polynomial
  interpolation*. J. Inequal. Appl. (2016), Paper No. 93.
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

namespace Erdos1129

/--
This is best possible: for the zeros of the Chebyshev polynomial $T_n$ there is an absolute
constant $c_2$ with $\max_{x\in[-1,1]}\sum_k\lvert l_k(x)\rvert<\frac{2}{\pi}\log n+c_2$
([Er61c, p. 236], [Er67, p. 66]). [Ib16, Section 3.2] gives the precise asymptotics.
-/
theorem erdos_1129.variants.chebyshev_upper_bound :
    ∃ C : ℝ, ∀ (n : ℕ) (x : Fin n → ℝ), 1 ≤ n → IsChebyshevNodes x →
      lebesgueConstant x < 2 / Real.pi * Real.log n + C := by
  sorry

end Erdos1129
