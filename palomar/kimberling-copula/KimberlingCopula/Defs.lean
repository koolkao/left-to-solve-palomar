/-
Copyright 2026 Ming-Chih Kao. Licensed under the Apache License, Version 2.0;
see the LICENSE file at the root of this repository.
-/
module

public import Mathlib

/-! The two definitions of the statement (Left to Solve statement mo-195959, PR #1260, by Ming-Chih
Kao), in namespace `MO195959`; `Challenge.lean` contains the same text. -/

@[expose] public section

namespace MO195959

open Filter Topology

/-- `f` is completely monotonic on the open set `s`: it is infinitely differentiable on `s` and
`(-1)ᵏ f⁽ᵏ⁾(x) ≥ 0` for every `k` and every `x ∈ s` (Widder 1946). -/
def CompletelyMonotoneOn (f : ℝ → ℝ) (s : Set ℝ) : Prop :=
  ContDiffOn ℝ (⊤ : ℕ∞) f s ∧ ∀ k : ℕ, ∀ x ∈ s, 0 ≤ (-1 : ℝ) ^ k * iteratedDerivWithin k f s x

/-- The Archimedean copula `C(u, v) = f(g(u) + g(v))`, with `g` the inverse of `f` on `[0, ∞)`,
and with the value `0 = f(∞)` when `u = 0` or `v = 0` (as `g(0) = ∞`). -/
noncomputable def archC (f : ℝ → ℝ) (u v : ℝ) : ℝ :=
  if u = 0 ∨ v = 0 then 0
  else f (Function.invFunOn f (Set.Ici 0) u + Function.invFunOn f (Set.Ici 0) v)

end MO195959

end
