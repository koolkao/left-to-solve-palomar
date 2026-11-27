/-
Copyright 2026 Ming-Chih Kao. Licensed under the Apache License, Version 2.0;
see the LICENSE file at the root of this repository.
-/
module

public import FixedDegree

/-!
# Solution

Proves `Erdos1044.erdos_1044.variants.fixed_degree_of_le_two`, the declaration stated in `Challenge.lean`, from
`OMA.solution` in `FixedDegree/Proof.lean`.
-/

public section

open Polynomial ENNReal

namespace Erdos1044

theorem erdos_1044.variants.fixed_degree_of_le_two (n : ℕ) (hn : n = 1 ∨ n = 2) :
    IsLeast {L : ℝ≥0∞ | ∃ f : ℂ[X], IsAdmissible f ∧ f.natDegree = n ∧ maxBoundaryLength f = L}
      (maxBoundaryLength (X ^ n - 1)) :=
  OMA.solution n hn

end Erdos1044
