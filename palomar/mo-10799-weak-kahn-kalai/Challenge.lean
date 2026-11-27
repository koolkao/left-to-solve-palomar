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
9097e2f90e66d2f6244209cb1c07f7120d17ec53, files `FormalConjectures/Mathoverflow/10799.lean`:
the statement and the definitions it uses are collected in one module that imports only Mathlib. The changes are listed in
the module documentation of `Challenge.lean`.
-/
module

public import Mathlib

/-!
# MathOverflow 10799: the weak Kahn–Kalai theorem on optimal monotone families

This is the statement `Mathoverflow10799.mathoverflow_10799.variants.weak_kahn_kalai` of
[formal-conjectures](https://github.com/google-deepmind/formal-conjectures) at commit
`9097e2f90e66d2f6244209cb1c07f7120d17ec53` (`FormalConjectures/Mathoverflow/10799.lean`), with the definitions it uses copied in so
that this file imports only Mathlib.

The text of each definition and of the theorem is unchanged; the formal-conjectures attributes
(`@[category …]`, `@[AMS …]`) are omitted, and so are the declarations of those files that this
statement does not use. Docstrings are kept as written, so some of them mention declarations
of the formal-conjectures files (such as other variants or API lemmas) that are not copied here.

*References:*
- [mathoverflow/10799](https://mathoverflow.net/questions/10799), asked by Gil Kalai
- [Thresholds and expectation thresholds](https://arxiv.org/abs/math/0603218) by Jeff Kahn and
  Gil Kalai, Combin. Probab. Comput. 16 (2007), 495-502. (formal-conjectures lists this arXiv
  number under the title "An Isoperimetric Inequality for the Hamming Cube and Integrality Gaps in
  Bounded-Degree Graphs"; arXiv gives the title used here.)
-/

@[expose] public section

namespace Mathoverflow10799

open Finset Real

/--
Start with a set $X=\{1,2,...,n\}$ of $n$ elements and the family $2^X$ of all subsets of $X$.
For a real number $p$ between zero and one, we consider a probability distribution $\mu_p$ on
$2^X$ where the probability that $i \in S$ is $p$, independently for different $i$'s.
Thus for $p=1/2$ we get the uniform probability distribution.

For $S \subseteq \{0, \ldots, n-1\}$, its probability is $p^{|S|} (1-p)^{n - |S|}$.
-/
noncomputable def μ {n : ℕ} (p : ℝ) (S : Finset (Fin n)) : ℝ :=
  p ^ #S * (1 - p) ^ (n - #S)

/--
The $p$-biased measure of a family $\mathcal F \subseteq 2^{[n]}$,
i.e. $\mu_p(\mathcal F) = \sum_{S \in \mathcal F} \mu_p(S)$.
-/
noncomputable def μFamily {n : ℕ} (p : ℝ) (F : Finset (Finset (Fin n))) : ℝ :=
  ∑ S ∈ F, μ p S

/--
Given a family $F$, for a subset $S$ of $X$, we write $h(S)$ as the number of subsets $T$ in $X$
such that
(1) $T$ differs from $S$ in exactly one element
(2) Exactly one set among $S$ and $T$ belongs to $F$.
-/
def boundaryCount (n : ℕ) (F : Finset (Finset (Fin n))) (S : Finset (Fin n)) : ℕ :=
  (Finset.univ.filter fun i : Fin n ↦ Xor (S ∈ F) (symmDiff S {i} ∈ F)).card

/--
The edge-boundary of $F$ is the expectation of $h(S)$ (according to $\mu_p$) over all
subsets $S$ of $X$. It is denoted by $I^p(F)$.
-/
noncomputable def edgeBoundary (n : ℕ) (p : ℝ) (F : Finset (Finset (Fin n))) : ℝ :=
  ∑ S : Finset (Fin n), μ p S * boundaryCount n F S

/--
A family $F$ of subsets of $2^X$ is monotone increasing if when $S$ belongs to $F$ and $T$
contains $S$ then $T$ also belongs to $F$. (Monotone increasing families also also called "filtes"
and "up-families".) From now on we will restrict our attention to the case of monotone increasing
families.

This is Mathlib's `IsUpperSet` applied to the coercion of $\mathcal F$ to a set,
using the fact that `≤` on `Finset` is `⊆`.
-/
abbrev IsMonotoneIncreasing {n : ℕ} (F : Finset (Finset (Fin n))) : Prop :=
  IsUpperSet (↑F : Set (Finset (Fin n)))

/--
Following Kahn–Kalai, a family is $(C \log(1/p), p)$-optimal if the isoperimetric inequality
(IR) is sharp up to the multiplicative constant $C \log(1/p)$, i.e.
$$I^p(\mathcal F) \le \frac{C}{p} \cdot \mu_p(\mathcal F) \cdot \log \frac{1}{\mu_p(\mathcal F)}.$$
`IsOptimal` is the special case $C = 1000$.
-/
noncomputable def IsOptimalWith {n : ℕ} (C p : ℝ) (F : Finset (Finset (Fin n))) : Prop :=
  let m := μFamily p F
  edgeBoundary n p F ≤ C * Real.log (1 / p) * (m * Real.logb p m / p)

end Mathoverflow10799

namespace Mathoverflow10799

open Finset Real

/--
Weaker version proven by Kahn–Kalai (2006): for every fixed $\varepsilon > 0$ there is a constant
$C = C_\varepsilon$ such that for every monotone increasing family $F$ with critical probability
$t$, i.e. $\mu_t(F) = 1/2$, there is some $p \in [n^{-\varepsilon} t, t]$ for which $F$ is
$(C \log(1/p), p)$-optimal.
-/
theorem mathoverflow_10799.variants.weak_kahn_kalai :
    ∀ ε > (0 : ℝ), ∃ C > (0 : ℝ), ∀ (n : ℕ) (_ : 2 ≤ n)
    (F : Finset (Finset (Fin n))) (_ : IsMonotoneIncreasing F)
    (t : ℝ) (_ : 0 < t) (_ : t < 1) (_ : μFamily t F = 1 / 2),
    ∃ p, (n : ℝ) ^ (-ε) * t ≤ p ∧ p ≤ t ∧ IsOptimalWith C p F := by
  sorry

end Mathoverflow10799
