/-
Copyright 2026 Ming-Chih Kao. Licensed under the Apache License, Version 2.0;
see the LICENSE file at the root of this repository.
-/
module

public import HadamardFirstCases

/-!
# Solution

Proves `Hadamard.HadamardConjecture.variants.first_cases`, the declaration stated in `Challenge.lean`, from
`OMA.solution` in `HadamardFirstCases/Proof.lean`.
-/

public section

namespace Hadamard

theorem HadamardConjecture.variants.first_cases : 668 ≤ hadamardConstant :=
  OMA.solution

end Hadamard
