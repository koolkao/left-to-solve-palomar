/-
Copyright 2026 The Formal Conjectures Authors.
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
9097e2f90e66d2f6244209cb1c07f7120d17ec53, files `FormalConjectures/ErdosProblems/70.lean` and
`FormalConjecturesForMathlib/Data/Set/Triplewise.lean`: the statement and the definitions it uses
are collected in one module that imports only Mathlib. The changes are listed in the module
documentation of `Challenge.lean`.
-/
module

public import Mathlib

/-!
# Erdős Problem 70: the Erdős–Rado relation $\mathfrak{c} \to (\omega + n, 4)^3_2$

This is the statement `Erdos70.erdos_70.variants.erdos_rado` of
[formal-conjectures](https://github.com/google-deepmind/formal-conjectures) at commit
`9097e2f90e66d2f6244209cb1c07f7120d17ec53` (`FormalConjectures/ErdosProblems/70.lean`), with the
definitions it uses copied in so that this file imports only Mathlib:

* `Set.Triplewise` (from `FormalConjecturesForMathlib/Data/Set/Triplewise.lean`);
* `Erdos70.RealCardinalRamsey3` (from `FormalConjectures/ErdosProblems/70.lean`).

The text of both definitions is unchanged, except that the docstring of `RealCardinalRamsey3` no
longer refers to `OrdinalCardinalRamsey3`, which is not needed here. The formal-conjectures
attributes (`@[category …]`, `@[AMS …]`) are omitted.

*References:*
- [erdosproblems.com/70](https://www.erdosproblems.com/70)
- [ErRa56] Erdős, P. and Rado, R., *A partition calculus in set theory*,
  Bull. Amer. Math. Soc. **62** (1956), 427–489, Theorem 31.
-/

@[expose] public section

open Cardinal Ordinal
open scoped Cardinal

namespace Set

/--
The ternary relation `r` holds triplewise on the set `s`
if `r x y z` for all *distinct* `x y z ∈ s`.
-/
protected def Triplewise {α : Type*} (s : Set α) (r : α → α → α → Prop) : Prop :=
  ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, y ∈ s → ∀ ⦃z⦄, z ∈ s → x ≠ y → y ≠ z → x ≠ z → r x y z

end Set

namespace Erdos70

/--
`RealCardinalRamsey3 β c` asserts the 3-uniform partition relation
$\mathfrak{c} \to (\beta, c)^3_2$, where $\mathfrak{c}$ is the order type of the real
numbers with their usual order.

It states that for any 2-coloring of all 3-element subsets of $\mathbb{R}$,
one of the following must hold:
* There is a red-monochromatic subset of order type $\beta$: the range of an order embedding
  `β.ToType ↪o ℝ` such that any three distinct elements of the range are colored red.
* There is a blue-monochromatic subset of cardinality $c$: a set $s \subseteq \mathbb{R}$ with
  $\#s = c$ such that every three distinct elements of $s$ are colored blue.

The coloring is encoded as a predicate on ordered triples of
distinct reals that is invariant under permutation of its three arguments.
-/
def RealCardinalRamsey3 (β : Ordinal.{0}) (c : Cardinal.{0}) : Prop :=
  -- For any partition of 3-element subsets of `ℝ` into red and blue:
  ∀ (isRed : ℝ → ℝ → ℝ → Prop),
    -- The colouring is well-defined on *unordered* triples of distinct elements:
    (∀ x y z, x ≠ y → y ≠ z → x ≠ z →
      (isRed x y z ↔ isRed y x z) ∧ (isRed x y z ↔ isRed x z y)) →
    -- either there is a red-monochromatic subset of order type β
    (∃ e : β.ToType ↪o ℝ, (Set.range e).Triplewise isRed) ∨
    -- or there is a blue-monochromatic subset of cardinality c
    (∃ s : Set ℝ, #s = c ∧ s.Triplewise (fun x y z ↦ ¬ isRed x y z))

end Erdos70

namespace Erdos70

/--
**Erdős–Rado partial result**: $\mathfrak{c} \to (\omega + n, 4)^3_2$ for any
$2 \le n < \omega$, where $\mathfrak{c}$ is the order type of the real numbers.
Positive partial answer to Problem 70 with $\beta = \omega + n$ and the blue side
fixed at $4$ [ErRa56, Theorem 31].
-/
theorem erdos_70.variants.erdos_rado (n : ℕ) (hn : 2 ≤ n) :
    RealCardinalRamsey3 (ω + n) 4 := by
  sorry

end Erdos70
