/-
Copyright 2026 Ming-Chih Kao. Licensed under the Apache License, Version 2.0;
see the LICENSE file at the root of this repository.
-/
module

public import Mathlib

/-!
# MathOverflow 503314: the odd-`d` conjecture on products over powers of a root of unity

MathOverflow question 503314 ("Identity involving primitive roots of unity", emiliocba, 31 October 2025,
<https://mathoverflow.net/questions/503314>, CC BY-SA 4.0) considers `m, d` with `gcd(m, d) = 1`,
`ξ = e^{2πi/m}`, and integers `r₁, r₂` of multiplicative order exactly `d` modulo `m` with `gcd(rᵢ - 1, m) = 1`,
satisfying for all `k ∈ ℤ`

  `∏_{u=1}^{d-1} (ξ^k - ξ^{k r₁^u})(ξ^k - ξ^{-k r₁^u}) = ∏_{u=1}^{d-1} (ξ^k - ξ^{k r₂^u})(ξ^k - ξ^{-k r₂^u})`  (*)

and conjectures: if `d` is odd, then `r₁^c ≡ r₂ (mod m)` for some `c`, i.e. `⟨r₁⟩ = ⟨r₂⟩` in `(ℤ/m)^×`.

The theorem below, proved in `Solution.lean` (Ming-Chih Kao, 2026, <https://github.com/koolkao/mo503314-two-primes>),
is the conjecture for every odd `d` and every `m ≥ 1`. Known before: `d` an odd prime (A. Ikeda, Osaka J. Math. 17
(1980), Theorem 3.7) and `(ℤ/m)^×` cyclic (M. Colantonio and E. A. Lauret, arXiv:2602.12939, Remark 2.6 and
Corollary 1.8).

Vocabulary: `ξ^a` is written `cexp (2 * π * I * a / m)` with `π` the real constant (`open Real`), so `ξ^{k r^u}` is
`cexp (2 * π * I * (k * r ^ u) / m)`; the order condition is Mathlib's `orderOf` in `ZMod m`; `Int.gcd` is the gcd
of integers; the conclusion `∃ c, r₁^c = r₂` in `ZMod m` is `r₁^c ≡ r₂ (mod m)`.
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
  sorry

end MO503314
