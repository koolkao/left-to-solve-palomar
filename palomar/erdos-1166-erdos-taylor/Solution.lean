/-
Copyright 2026 Ming-Chih Kao. Licensed under the Apache License, Version 2.0;
see the LICENSE file at the root of this repository.
-/
module

public import ErdosTaylor

/-!
# Solution

Proves `Erdos1166.erdos_1166.variants.erdos_taylor`, the declaration stated in `Challenge.lean`:
the reduction `main` (Left to Solve PR #750) applied to the proofs of its three hypotheses
`H1` (PR #1067), `H2` (PR #909) and `H3` (PR #1157).
-/

public section

open MeasureTheory Filter
open scoped ProbabilityTheory Topology Real ENNReal

namespace Erdos1166

open Erdos1165

theorem erdos_1166.variants.erdos_taylor {Ω : Type*} [MeasureSpace Ω]
    [IsProbabilityMeasure (ℙ : Measure Ω)] {X : ℕ → Ω → ℤ × ℤ}
    (hX : IsSimpleRandomWalkSteps X) :
    ∀ᵐ ω, ∀ ε : ℝ, 0 < ε →
      (∀ᶠ n : ℕ in atTop, 1 / (4 * π) - ε ≤ (maxLocalTime X n ω : ℝ) / Real.log n ^ 2) ∧
      (∀ᶠ n : ℕ in atTop, (maxLocalTime X n ω : ℝ) / Real.log n ^ 2 ≤ 1 / π + ε) :=
  OMA.R_Erdos1166_erdos_1166_variants_erdos_taylor_R1.main OMA.H1Proof.h1 OMA.H2Proof.h2
    OMA.H3Proof.h3 hX

end Erdos1166
