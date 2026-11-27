/-
Copyright 2026 Ming-Chih Kao. Licensed under the Apache License, Version 2.0;
see the LICENSE file at the root of this repository.
-/
module

public import ChebyshevLebesgue

/-!
# Solution

Proves `Erdos1129.erdos_1129.variants.chebyshev_upper_bound`, the declaration stated in `Challenge.lean`, from
`OMA.solution` in `ChebyshevLebesgue/Proof.lean`.
-/

public section

namespace Erdos1129

theorem erdos_1129.variants.chebyshev_upper_bound :
    ∃ C : ℝ, ∀ (n : ℕ) (x : Fin n → ℝ), 1 ≤ n → IsChebyshevNodes x →
      lebesgueConstant x < 2 / Real.pi * Real.log n + C :=
  OMA.solution

end Erdos1129
