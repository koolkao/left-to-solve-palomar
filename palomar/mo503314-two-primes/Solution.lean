/-
Copyright 2026 Ming-Chih Kao. Licensed under the Apache License, Version 2.0;
see the LICENSE file at the root of this repository.
-/
module

public import TwoPrimes

/-!
# Solution

Proves the declaration stated in `Challenge.lean` from `TwoPrimes/Proof.lean` (the source repository's proof,
ported to Lean v4.36 and the module system).
-/

@[expose] public section

open Complex Real

namespace MO503314

/-- **MathOverflow 503314, odd `d`.** -/
theorem mo503314 (m d : ℕ) (hm : 0 < m) (hd : Odd d) (hmd : Nat.Coprime m d) (r₁ r₂ : ℤ)
    (ho₁ : orderOf (r₁ : ZMod m) = d) (ho₂ : orderOf (r₂ : ZMod m) = d)
    (hg₁ : Int.gcd (r₁ - 1) m = 1) (hg₂ : Int.gcd (r₂ - 1) m = 1)
    (hstar : ∀ k : ℤ,
      (∏ u ∈ Finset.Icc 1 (d - 1),
        (cexp (2 * π * I * k / m) - cexp (2 * π * I * (k * r₁ ^ u) / m)) *
        (cexp (2 * π * I * k / m) - cexp (2 * π * I * (-(k * r₁ ^ u)) / m))) =
      ∏ u ∈ Finset.Icc 1 (d - 1),
        (cexp (2 * π * I * k / m) - cexp (2 * π * I * (k * r₂ ^ u) / m)) *
        (cexp (2 * π * I * k / m) - cexp (2 * π * I * (-(k * r₂ ^ u)) / m))) :
    ∃ c : ℕ, (r₁ : ZMod m) ^ c = (r₂ : ZMod m) :=
  TwoPrimes.mo503314 m d hm hd hmd r₁ r₂ ho₁ ho₂ hg₁ hg₂ hstar

end MO503314
