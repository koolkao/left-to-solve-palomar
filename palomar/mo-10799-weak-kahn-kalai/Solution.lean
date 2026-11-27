/-
Copyright 2026 Ming-Chih Kao. Licensed under the Apache License, Version 2.0;
see the LICENSE file at the root of this repository.
-/
module

public import WeakKahnKalai

/-!
# Solution

Proves `Mathoverflow10799.mathoverflow_10799.variants.weak_kahn_kalai`, the declaration stated in `Challenge.lean`, from
`OMA.solution` in `WeakKahnKalai/Proof.lean`.
-/

public section

namespace Mathoverflow10799

open Finset Real

theorem mathoverflow_10799.variants.weak_kahn_kalai :
    ∀ ε > (0 : ℝ), ∃ C > (0 : ℝ), ∀ (n : ℕ) (_ : 2 ≤ n)
    (F : Finset (Finset (Fin n))) (_ : IsMonotoneIncreasing F)
    (t : ℝ) (_ : 0 < t) (_ : t < 1) (_ : μFamily t F = 1 / 2),
    ∃ p, (n : ℝ) ^ (-ε) * t ≤ p ∧ p ≤ t ∧ IsOptimalWith C p F :=
  OMA.solution

end Mathoverflow10799
