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
9097e2f90e66d2f6244209cb1c07f7120d17ec53, files `FormalConjectures/ErdosProblems/1129.lean`, `FormalConjectures/ErdosProblems/1130.lean`:
the statement and the definitions it uses are collected in one module that imports only Mathlib. The changes are listed in
the module documentation of `Challenge.lean`.
-/
module

public import Mathlib

/-!
# Erdős Problem 1130, Erdős's bound $\Upsilon(x_1,\ldots,x_n) < \sqrt n$

This is the statement `Erdos1130.erdos_1130.variants.erdos_sqrt` of
[formal-conjectures](https://github.com/google-deepmind/formal-conjectures) at commit
`9097e2f90e66d2f6244209cb1c07f7120d17ec53` (`FormalConjectures/ErdosProblems/1130.lean`), with the
definitions it uses copied in from `FormalConjectures/ErdosProblems/1129.lean` (`IsNodeSet`,
`lebesgueFunction`, `extendedNodes`, `gapMax`) and `1130.lean` (`upsilon`), so that this file
imports only Mathlib.

The text of each definition and of the theorem is unchanged, with one exception: in
`extendedNodes` the index bound `by omega` is replaced by the term `Nat.sub_one_lt_of_le h.1 h.2`,
which proves the same bound. (With `by omega`, Comparator reported that
`Erdos1129.extendedNodes._proof_2` differs between `Challenge` and the proof development: the
abstracted proof refers to a private auxiliary declaration whose name contains the module name. By
proof irrelevance the function is the same.) The formal-conjectures attributes
(`@[category …]`, `@[AMS …]`) are omitted, and so are the declarations of those files that this
statement does not use. Docstrings are kept as written, so some of them mention declarations
of the formal-conjectures files (such as other variants or API lemmas) that are not copied here.

*References:*
- [erdosproblems.com/1130](https://www.erdosproblems.com/1130)
- [Er47] Erdős, P., *Some remarks on polynomials*. Bull. Amer. Math. Soc. 53 (1947), 1169-1176.
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

/-- The nodes together with the endpoints: `extendedNodes x 0` is $x_0=-1$, `extendedNodes x i` is
the node $x_i$ for $1\le i\le n$, and `extendedNodes x i` is $x_{n+1}=1$ for $i>n$. -/
noncomputable def extendedNodes {n : ℕ} (x : Fin n → ℝ) (i : ℕ) : ℝ :=
  if h : 1 ≤ i ∧ i ≤ n then x ⟨i - 1, Nat.sub_one_lt_of_le h.1 h.2⟩ else if i = 0 then -1 else 1

/-- `gapMax x i` is $\lambda_i(x)=\max_{t\in[x_i,x_{i+1}]}L_x(t)$ with $x_0=-1$ and $x_{n+1}=1$, for
$0\le i\le n$ (for larger `i` the value is not meaningful). For $1\le i\le n-1$ it is the local
maximum of the Lebesgue function between the consecutive nodes $x_i$ and $x_{i+1}$. If
$x_1=-1$ (respectively $x_n=1$) the gap $i=0$ (respectively $i=n$) is a single point, where
$L_x=1$. -/
noncomputable def gapMax {n : ℕ} (x : Fin n → ℝ) (i : ℕ) : ℝ :=
  sSup (lebesgueFunction x '' Set.Icc (extendedNodes x i) (extendedNodes x (i + 1)))

end Erdos1129

namespace Erdos1130

open Erdos1129

/-- $\Upsilon(x)=\min_{0\le i\le n}\max_{t\in[x_i,x_{i+1}]}L_x(t)$ with $x_0=-1$ and $x_{n+1}=1$:
the smallest of the $n+1$ local maxima `gapMax x i`, $0\le i\le n$. If $x_1=-1$ or $x_n=1$ then an
outer gap is a single point, where the Lebesgue function is $1$, and $\Upsilon(x)=1$. -/
noncomputable def upsilon {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  ⨅ i : Fin (n + 1), gapMax x (i : ℕ)

end Erdos1130

namespace Erdos1130

open Erdos1129

/--
Erdős [Er47, Theorem 2, pp. 1171-1172] proved that for nodes $x_1\le\cdots\le x_n$ in $[-1,1]$
there is an $i$ with $\max_{x\in[x_i,x_{i+1}]}\sum_k\lvert l_k(x)\rvert<\sqrt n$, that is,
$\Upsilon(x_1,\ldots,x_n)<\sqrt n$. The paper allows coinciding nodes (then it calls the claim
obvious); here the nodes are distinct. We take $n\ge 2$: for $n=1$ the sum is identically $1$.
-/
theorem erdos_1130.variants.erdos_sqrt (n : ℕ) (hn : 2 ≤ n) (x : Fin n → ℝ)
    (hx : IsNodeSet x) :
    upsilon x < Real.sqrt n := by
  sorry

end Erdos1130
