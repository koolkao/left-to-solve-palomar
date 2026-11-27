/-
Copyright 2026 Ming-Chih Kao. Licensed under the Apache License, Version 2.0;
see the LICENSE file at the root of this repository.
-/
module

public import Mathlib

/-! Port: copied from `FriedanMulti/Statement.lean` of github.com/koolkao/friedan-entropy-inequality (commit 0f4ba65dc126f59e7158fbcbc01548baa78cf21d, Lean v4.33.1, Mathlib 0df444a) and put into the module system (`module` header, `public import`, public section). No other change was needed for Lean v4.36.0 / Mathlib fc4f59e. -/

@[expose] public section

/-!
# Friedan's entropy inequality for `m` distributions (Theorem M): statement

Let `X₁, …, X_m` be probability vectors on `Fin n` and `a₁, …, a_m ≥ 0` weights with `∑ aⱼ = 1`.
Put `zᵢ = ∏ⱼ Xⱼ(i)^{aⱼ}` (real power, `0^0 = 1`), `K = ∑ᵢ zᵢ` and, when `K > 0`, `Z = z / K`.
Then `∑ⱼ aⱼ H(Xⱼ) ≥ K² H(Z)`, where `H(P) = -∑ᵢ P(i) log P(i)` (natural log, `0 log 0 = 0`).

For `m = 2` this is the statement `mo-138395` of Left to Solve (Friedan, MathOverflow 138395).
Conventions as there: probability vectors are written out (nonnegative, summing to `1`), entropy
uses `Real.negMulLog`, and `K > 0` is assumed (if `K = 0`, Lean's `0 / 0 = 0` makes the left side
`0` and the inequality is trivial).
-/

namespace FriedanMulti

/-- Shannon entropy `H(P) = -∑ᵢ P(i) log P(i)` (natural logarithm, `0 log 0 = 0`). -/
noncomputable def entropy {n : ℕ} (P : Fin n → ℝ) : ℝ :=
  ∑ i, Real.negMulLog (P i)

/-- Theorem M (Friedan's inequality for `m` distributions), as a proposition. -/
def TheoremM : Prop :=
  ∀ (n m : ℕ) (X : Fin m → Fin n → ℝ), (∀ j i, 0 ≤ X j i) → (∀ j, ∑ i, X j i = 1) →
    ∀ a : Fin m → ℝ, (∀ j, 0 ≤ a j) → ∑ j, a j = 1 →
      0 < ∑ i, ∏ j, X j i ^ a j →
      (∑ i, ∏ j, X j i ^ a j) ^ 2 *
          entropy (fun i => (∏ j, X j i ^ a j) / ∑ k, ∏ j, X j k ^ a j) ≤
        ∑ j, a j * entropy (X j)

end FriedanMulti

end
