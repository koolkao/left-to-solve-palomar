/-
Copyright 2026 Ming-Chih Kao. Licensed under the Apache License, Version 2.0;
see the LICENSE file at the root of this repository.
-/
module

public import FreeNodes

/-!
# Solution

Proves `Erdos1129.erdos_1129.variants.free_nodes_not_unique`, the declaration stated in `Challenge.lean`, from
`OMA.solution` in `FreeNodes/Proof.lean`.
-/

public section

namespace Erdos1129

theorem erdos_1129.variants.free_nodes_not_unique (n : ℕ) (hn : 3 ≤ n) :
    ¬ {x : Fin n → ℝ | IsMinimiser x}.Countable :=
  OMA.solution n hn

end Erdos1129
