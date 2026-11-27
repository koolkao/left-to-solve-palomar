/-
Copyright 2025 The Formal Conjectures Authors.

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
9097e2f90e66d2f6244209cb1c07f7120d17ec53, files `FormalConjectures/Wikipedia/Hadamard.lean`:
the statement and the definitions it uses are collected in one module that imports only Mathlib. The changes are listed in
the module documentation of `Challenge.lean`.
-/
module

public import Mathlib

/-!
# Hadamard matrices exist in every order $4k \le 664$

This is the statement `Hadamard.HadamardConjecture.variants.first_cases` of
[formal-conjectures](https://github.com/google-deepmind/formal-conjectures) at commit
`9097e2f90e66d2f6244209cb1c07f7120d17ec53` (`FormalConjectures/Wikipedia/Hadamard.lean`), with the definitions it uses copied in so
that this file imports only Mathlib.

The text of each definition and of the theorem is unchanged; the formal-conjectures attributes
(`@[category …]`, `@[AMS …]`) are omitted, and so are the declarations of those files that this
statement does not use. Docstrings are kept as written, so some of them mention declarations
of the formal-conjectures files (such as other variants or API lemmas) that are not copied here.

*References:*
- [Wikipedia](https://en.wikipedia.org/wiki/Hadamard_matrix#Hadamard_conjecture)
- [Tao's optimization constant 23a](https://teorth.github.io/optimizationproblems/constants/23a.html)
- Kharaghani, H. and Tayfeh-Rezaie, B., *A Hadamard matrix of order 428*. J. Combin. Des. 13
  (2005), 435-440 (after which 668 is the smallest order $4k$ with no known Hadamard matrix).
-/

@[expose] public section

namespace Hadamard

/--
A square matrix $M$ with $±1$-entries that satisfies the equality $|M| ≤ n^\frac{n}{2}$ is called a *Hadamard matrix*.
-/
def IsHadamard {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) : Prop :=
    (∀ (i j : Fin n), M i j ∈ ({1, -1} : Finset ℝ)) ∧
    |M.det| = n ^ ((n : ℝ) / 2)

/--
The **smallest unsolved order** of the Hadamard conjecture: the smallest $n = 4k$ such that there
is no Hadamard matrix of order $n$, or $\infty$ if there is none.
-/
noncomputable def hadamardConstant : ℕ∞ :=
  ⨅ (k : ℕ) (_ : ¬ ∃ M, IsHadamard (n := 4 * k) M), (4 * k : ℕ∞)

end Hadamard

namespace Hadamard

/--
For all $k ≤ 166$, it is known there that there is a Hadamard matrix of size $4 * k$.
So `hadamardConstant` is at least $668$.
-/
theorem HadamardConjecture.variants.first_cases : 668 ≤ hadamardConstant := by
  sorry

end Hadamard
