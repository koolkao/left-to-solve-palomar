/-
Copyright 2026 Ming-Chih Kao. Licensed under the Apache License, Version 2.0;
see the LICENSE file at the root of this repository.
-/
module

public import E521

/-!
# Solution

Proves `Erdos521.erdos_521` and `Erdos521.erdos_521_with_multiplicity`, the declarations stated in
`Challenge.lean`, from `E521/Main.lean` (the merged Left to Solve proof, ported to Lean v4.36 and the module
system in `E521/Part1.lean` … `E521/Part7.lean`).
-/

@[expose] public section

open MeasureTheory Filter Polynomial
open scoped Topology

namespace Erdos521

theorem erdos_521 : ¬ Claim :=
  erdos_521_proof

theorem erdos_521_with_multiplicity :
    ¬ ∀ᵐ ω ∂rademacherMeasure,
      Tendsto (fun n : ℕ ↦ ((littlewoodPolynomial ω n).roots.card : ℝ) / Real.log (n : ℝ))
        atTop (𝓝 ((2 : ℝ) / Real.pi)) :=
  erdos_521_with_multiplicity_proof

end Erdos521
