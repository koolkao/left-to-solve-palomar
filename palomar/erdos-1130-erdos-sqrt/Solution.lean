/-
Copyright 2026 Ming-Chih Kao. Licensed under the Apache License, Version 2.0;
see the LICENSE file at the root of this repository.
-/
module

public import ErdosSqrt

/-!
# Solution

Proves `Erdos1130.erdos_1130.variants.erdos_sqrt`, the declaration stated in `Challenge.lean`, from
`OMA.solution` in `ErdosSqrt/Proof.lean`.
-/

public section

namespace Erdos1130

open Erdos1129

theorem erdos_1130.variants.erdos_sqrt (n : ℕ) (hn : 2 ≤ n) (x : Fin n → ℝ)
    (hx : IsNodeSet x) :
    upsilon x < Real.sqrt n :=
  OMA.solution n hn x hx

end Erdos1130
