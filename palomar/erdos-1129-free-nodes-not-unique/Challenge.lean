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
# Erdős Problem 1129: for  \ge 3$ the optimal interpolation nodes are not unique

This is the statement `Erdos1129.erdos_1129.variants.free_nodes_not_unique` of
[formal-conjectures](https://github.com/google-deepmind/formal-conjectures) at commit
`9097e2f90e66d2f6244209cb1c07f7120d17ec53` (`FormalConjectures/ErdosProblems/1129.lean`), with the
definitions it uses (`IsNodeSet`, `lebesgueFunction`, `lebesgueConstant`, `IsMinimiser`) copied
in so that this file imports only Mathlib.

The text of each definition and of the theorem is unchanged; the formal-conjectures attributes
(`@[category …]`, `@[AMS …]`) are omitted, and so are the declarations of those files that this
statement does not use. Docstrings are kept as written, so some of them mention declarations
of the formal-conjectures files (such as other variants or API lemmas) that are not copied here.

*References:*
- [erdosproblems.com/1129](https://www.erdosproblems.com/1129)
- [Ib16] Ibrahimoglu, B. A., *Lebesgue functions and Lebesgue constants in polynomial
  interpolation*. J. Inequal. Appl. (2016), Paper No. 93.
- [RaVa15] Rack, H.-J. and Vajda, R., *Optimal cubic Lagrange interpolation: Extremal node
  systems with minimal Lebesgue constant*. Stud. Univ. Babeş-Bolyai Math. 60 (2015), 151-171.
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

/-- `x` is a minimiser: a node set whose Lebesgue constant is at most that of every node set in
$[-1,1]$ with $n$ nodes. -/
def IsMinimiser {n : ℕ} (x : Fin n → ℝ) : Prop :=
  IsNodeSet x ∧ ∀ y : Fin n → ℝ, IsNodeSet y → lebesgueConstant x ≤ lebesgueConstant y

end Erdos1129

namespace Erdos1129

/--
Without the canonical hypothesis the minimiser of $\Lambda$ is not unique. For every $n\ge 3$
there are uncountably many node sets $x_1<\dots<x_n$ in $[-1,1]$ with the minimal Lebesgue
constant [RaVa15, Theorem 2.5]. The reason is affine invariance. Rescaling a node set to a
canonical one keeps its local maxima between consecutive nodes and does not increase $\Lambda$
([Ib16, Section 2.1 (e)]), so the minimal Lebesgue constant $\Lambda^*$ is attained by the
canonical minimiser $x^*$. The shrunk node set $x^*/\tau$ with $\tau\ge 1$ has
$\Lambda(x^*/\tau)=\max_{\lvert u\rvert\le\tau}L_{x^*}(u)$. Since $L_{x^*}(\pm 1)=1<\Lambda^*$ for
$n\ge 3$, this is still $\Lambda^*$ for all $\tau\ge 1$ close to $1$ (see the proof of
[RaVa15, Theorem 2.5]). For $n=4$ the node sets
$\pm 1/\tau,\pm t/\tau$ with $1\le\tau\le b$ for a constant $b\approx 1.0433$, where $t$ is as
in `erdos_1129.variants.four_nodes`, are all optimal [RaVa15, Theorem 4.2].
-/
theorem erdos_1129.variants.free_nodes_not_unique (n : ℕ) (hn : 3 ≤ n) :
    ¬ {x : Fin n → ℝ | IsMinimiser x}.Countable := by
  sorry

end Erdos1129
