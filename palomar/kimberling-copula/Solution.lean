/-
Copyright 2026 Ming-Chih Kao. Licensed under the Apache License, Version 2.0;
see the LICENSE file at the root of this repository.
-/
module

public import KimberlingCopula

/-!
# Solution

Proves `MO195959.kimberling_inequality`, the declaration stated in `Challenge.lean`, from
`Kimberling.main_proof` in `KimberlingCopula/Proof.lean`. The definitions `MO195959.CompletelyMonotoneOn`
and `MO195959.archC` are in `KimberlingCopula/Defs.lean`, with the same text as in `Challenge.lean`.
-/

@[expose] public section

namespace MO195959

open Filter Topology

theorem kimberling_inequality :
    ∀ f : ℝ → ℝ, ContinuousOn f (Set.Ici 0) → f 0 = 1 → Tendsto f atTop (𝓝 0) →
      CompletelyMonotoneOn f (Set.Ioi 0) →
      ∀ u ∈ Set.Icc (0 : ℝ) 1, ∀ v ∈ Set.Icc (0 : ℝ) 1,
        archC f u v - u * v ≤ archC f ((u + v) / 2) ((u + v) / 2) - ((u + v) / 2) ^ 2 :=
  Kimberling.main_proof

end MO195959
