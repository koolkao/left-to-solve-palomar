/-
Copyright 2026 Ming-Chih Kao. Licensed under the Apache License, Version 2.0;
see the LICENSE file at the root of this repository.
-/
module

public import FriedanEntropy
public import FriedanMulti

/-!
# Solution

Proves the three declarations stated in `Challenge.lean` from the proof development:
`OMA.S_mo_138395.main` (`FriedanEntropy/Proof.lean`), `FriedanMulti.theoremM`
(`FriedanMulti/Main.lean`) and `FriedanR2.theoremR2` (`FriedanMulti/R2Main.lean`). The statements
there use the abbreviations `entropy` and `renyi`, which unfold to the sums written out here.
-/

@[expose] public section

namespace Friedan138395

theorem friedan_two (n : ℕ) (X Y : Fin n → ℝ) (hX0 : ∀ i, 0 ≤ X i) (hX1 : ∑ i, X i = 1)
    (hY0 : ∀ i, 0 ≤ Y i) (hY1 : ∑ i, Y i = 1) (α : ℝ) (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    (hK : 0 < ∑ i, X i ^ α * Y i ^ (1 - α)) :
    (∑ i, X i ^ α * Y i ^ (1 - α)) ^ 2 *
        ∑ i, Real.negMulLog (X i ^ α * Y i ^ (1 - α) / ∑ j, X j ^ α * Y j ^ (1 - α)) ≤
      α * ∑ i, Real.negMulLog (X i) + (1 - α) * ∑ i, Real.negMulLog (Y i) :=
  OMA.S_mo_138395.main n X Y hX0 hX1 hY0 hY1 α hα0 hα1 hK

theorem friedan_multi (n m : ℕ) (X : Fin m → Fin n → ℝ) (hX0 : ∀ j i, 0 ≤ X j i)
    (hX1 : ∀ j, ∑ i, X j i = 1) (a : Fin m → ℝ) (ha0 : ∀ j, 0 ≤ a j) (ha1 : ∑ j, a j = 1)
    (hK : 0 < ∑ i, ∏ j, X j i ^ a j) :
    (∑ i, ∏ j, X j i ^ a j) ^ 2 *
        ∑ i, Real.negMulLog ((∏ j, X j i ^ a j) / ∑ k, ∏ j, X j k ^ a j) ≤
      ∑ j, a j * ∑ i, Real.negMulLog (X j i) :=
  FriedanMulti.theoremM n m X hX0 hX1 a ha0 ha1 hK

theorem friedan_renyi_two_point (m : ℕ) (X : Fin m → Fin 2 → ℝ) (hX0 : ∀ j i, 0 ≤ X j i)
    (hX1 : ∀ j, ∑ i, X j i = 1) (a : Fin m → ℝ) (ha0 : ∀ j, 0 ≤ a j) (ha1 : ∑ j, a j = 1)
    (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ ≠ 1) (hγ2 : γ ≤ 2 * Real.log 2)
    (hK : 0 < ∑ i, ∏ j, X j i ^ a j) :
    (∑ i, ∏ j, X j i ^ a j) ^ 2 *
        (Real.log (∑ i, ((∏ j, X j i ^ a j) / ∑ k, ∏ j, X j k ^ a j) ^ γ) / (1 - γ)) ≤
      ∑ j, a j * (Real.log (∑ i, X j i ^ γ) / (1 - γ)) :=
  FriedanR2.theoremR2 m X hX0 hX1 a ha0 ha1 γ hγ0 hγ1 hγ2 hK

end Friedan138395
