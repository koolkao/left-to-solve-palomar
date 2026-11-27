/-
Copyright 2026 Ming-Chih Kao. Licensed under the Apache License, Version 2.0;
see the LICENSE file at the root of this repository.
-/
module

public import ErdosRado

/-!
# Solution

Proves `Erdos70.erdos_70.variants.erdos_rado`, the declaration stated in `Challenge.lean`,
from `E70.erdos_rado_real` in `ErdosRado/Proof.lean`.
-/

public section

open Cardinal Ordinal
open scoped Cardinal

namespace Erdos70

theorem erdos_70.variants.erdos_rado (n : ℕ) (hn : 2 ≤ n) :
    RealCardinalRamsey3 (ω + n) 4 := by
  intro isRed hSym
  exact E70.erdos_rado_real n isRed hSym

end Erdos70
