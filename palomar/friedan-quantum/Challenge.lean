/-
Copyright 2026 Ming-Chih Kao. Licensed under the Apache License, Version 2.0;
see the LICENSE file at the root of this repository.
-/
module

public import Mathlib

/-!
# Friedan's entropy inequality for non-commuting Hamiltonians and density matrices
(MathOverflow 138395, the quantum question)

At the end of MathOverflow question 138395 (Daniel Friedan, 2013, <https://mathoverflow.net/q/138395>,
CC BY-SA 3.0), Friedan restates his entropy inequality for two commuting Hamiltonians `H₀, H₁`
(Hermitian `n × n` matrices), with `Z(H) = tr e^{-H}`, `ρ_H = e^{-H}/Z(H)`,
`S(H) = -tr ρ_H log ρ_H`, `H_α = (1 - α) H₀ + α H₁` and `K = Z(H_α) / (Z(H₀)^{1-α} Z(H₁)^α)`:
`(1 - α) S(H₀) + α S(H₁) ≥ K² S(H_α)`, and asks:

> Does the inequality hold without the assumption that `H₀` and `H₁` commute, i.e. in quantum
> statistical mechanics?

The answer is yes (`friedan_question`). Ming-Chih Kao (2026,
<https://github.com/koolkao/friedan-entropy-inequality>, QUANTUM.md) gives proofs of this and of the
other inequalities below; as far as the authors searched, they are new.

Vocabulary (all from Mathlib): matrices are `Matrix (Fin n) (Fin n) ℂ`; `cfc f A` is the continuous
functional calculus, which for a Hermitian matrix `A` applies `f : ℝ → ℝ` to its eigenvalues (any
`f` is continuous on the finite spectrum); every `cfc` argument below is Hermitian (on a
non-Hermitian argument `cfc` would return `0`). So `cfc Real.exp` is the matrix exponential, and on
positive definite matrices `cfc Real.log` and `cfc (· ^ p)` are the matrix logarithm and real powers;
on a singular positive semidefinite matrix they act as `Real.log 0 = 0` and `0 ^ p` (with
`0 ^ (0 : ℝ) = 1`) on the kernel. `trace` is the matrix trace and `.re` its real part; `PosDef` /
`PosSemidef` (with `ComplexOrder`) are positive definite / positive semidefinite; `Xᴴ` is the
conjugate transpose. Entropy is `S(A) = -re tr(A log A)`, which with `Real.log 0 = 0` is
`-∑ λᵢ log λᵢ` with the convention `0 log 0 = 0`. `K⁻¹ • M` is `M / K` (and `0` if `K = 0`).

* `friedan_question`: Friedan's question exactly as posed (two Hamiltonians, `0 ≤ a ≤ 1`).
* `hamiltonians_multi`: the same for `m` Hamiltonians and weights summing to `1`.
* `logEuclidean_multi`: the density-matrix form with the log-Euclidean mean `exp(∑ aⱼ log ρⱼ)` of
  `m` faithful states (for `m = 2` and Gibbs states it is `friedan_question`).
* `alphaZ_psd`, `kuboAndo`, `product_multi`: the same inequality for other weighted geometric means
  (α-z means for positive semidefinite states; Kubo–Ando; multivariate product means).

Scope: the compared statements are these six inequalities. They do not assert `K > 0` (it holds
for the means of faithful states, but is not part of the claim). Not stated here, and proved on
paper only or only in the source repository: the spectral forms (Proposition A, Theorem QM, for an
arbitrary `M` with weakly log-majorized eigenvalues), the log-Euclidean and Kubo–Ando means of
non-faithful states (Corollary B), and the weighted Karcher mean (Corollary QM-K).
-/

@[expose] public section

open Matrix
open scoped ComplexOrder

namespace FriedanQuantum

/-- **Friedan's quantum question (MathOverflow 138395), answered yes.** For Hermitian `H₀, H₁` on
`ℂⁿ` (`n ≥ 1`, not necessarily commuting) and `0 ≤ a ≤ 1`, with `Z(H) = tr e^{-H}`,
`ρ_H = e^{-H} / Z(H)`, `S(H) = -tr(ρ_H log ρ_H)`, `H_a = (1 - a) H₀ + a H₁` and
`K = Z(H_a) / (Z(H₀)^{1-a} Z(H₁)^a)`: `K² S(H_a) ≤ (1 - a) S(H₀) + a S(H₁)`. -/
theorem friedan_question (n : ℕ) [NeZero n] (H₀ H₁ : Matrix (Fin n) (Fin n) ℂ)
    (h₀ : H₀.IsHermitian) (h₁ : H₁.IsHermitian) (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    let Z : Matrix (Fin n) (Fin n) ℂ → ℝ := fun H => (trace (cfc Real.exp (-H))).re
    let ρ : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ :=
      fun H => (Z H)⁻¹ • cfc Real.exp (-H)
    let S : Matrix (Fin n) (Fin n) ℂ → ℝ := fun H => -(trace (ρ H * cfc Real.log (ρ H))).re
    let Ha := (1 - a) • H₀ + a • H₁
    let K := Z Ha / (Z H₀ ^ (1 - a) * Z H₁ ^ a)
    K ^ 2 * S Ha ≤ (1 - a) * S H₀ + a * S H₁ := by
  sorry

/-- **The α-z means, positive semidefinite states.** For density matrices `ρ, σ` (positive
semidefinite, trace one, not necessarily faithful), `0 ≤ a ≤ 1` and `z > 0`, with
`M = (ρ^{a/2z} σ^{(1-a)/z} ρ^{a/2z})^z`, `K = tr M` and `S(A) = -tr(A log A)`:
`K² S(M / K) ≤ a S(ρ) + (1 - a) S(σ)`. Here `M` is the formula itself: at `a = 0` and `a = 1` the
zeroth power is the identity (`0 ^ (0 : ℝ) = 1`), so `M = σ`, respectively `M = ρ`; if `K = 0`
(possible for `0 < a < 1` when the supports are orthogonal) the left side is `0`. `z = 1` is the
Petz mean; with `ρ, σ, a` replaced by `σ, ρ, 1 - a` and `z = a` (for `0 < a ≤ 1`), the sandwiched
mean `(σ^{(1-a)/2a} ρ σ^{(1-a)/2a})^a`. -/
theorem alphaZ_psd {n : ℕ} (ρ σ : Matrix (Fin n) (Fin n) ℂ) (hρ : ρ.PosSemidef)
    (hσ : σ.PosSemidef) (hρ1 : ρ.trace = 1) (hσ1 : σ.trace = 1) (a z : ℝ) (ha0 : 0 ≤ a)
    (ha1 : a ≤ 1) (hz : 0 < z) :
    let M := cfc (fun x : ℝ => x ^ z)
      (cfc (fun x : ℝ => x ^ (a / (2 * z))) ρ * cfc (fun x : ℝ => x ^ ((1 - a) / z)) σ *
        cfc (fun x : ℝ => x ^ (a / (2 * z))) ρ)
    let S : Matrix (Fin n) (Fin n) ℂ → ℝ := fun A => -(trace (A * cfc Real.log A)).re
    let K := (trace M).re
    K ^ 2 * S (K⁻¹ • M) ≤ a * S ρ + (1 - a) * S σ := by
  sorry

/-- **The Kubo–Ando mean.** For faithful density matrices `ρ, σ` and `0 ≤ a ≤ 1`, with
`M = σ #_a ρ = σ^{1/2} (σ^{-1/2} ρ σ^{-1/2})^a σ^{1/2}`, `K = tr M` and `S(A) = -tr(A log A)`:
`K² S(M / K) ≤ a S(ρ) + (1 - a) S(σ)`. -/
theorem kuboAndo {n : ℕ} (ρ σ : Matrix (Fin n) (Fin n) ℂ) (hρ : ρ.PosDef)
    (hσ : σ.PosDef) (hρ1 : ρ.trace = 1) (hσ1 : σ.trace = 1) (a : ℝ) (ha0 : 0 ≤ a)
    (ha1 : a ≤ 1) :
    let sq := cfc (fun x : ℝ => x ^ (1 / 2 : ℝ)) σ
    let isq := cfc (fun x : ℝ => x ^ (-(1 / 2) : ℝ)) σ
    let M := sq * cfc (fun x : ℝ => x ^ a) (isq * ρ * isq) * sq
    let S : Matrix (Fin n) (Fin n) ℂ → ℝ := fun A => -(trace (A * cfc Real.log A)).re
    let K := (trace M).re
    K ^ 2 * S (K⁻¹ • M) ≤ a * S ρ + (1 - a) * S σ := by
  sorry

/-- **Friedan's form for `m` Hamiltonians.** For Hermitian `H j` on `ℂⁿ` (`n ≥ 1`, `j : Fin m`) and
weights `a j ≥ 0` with `∑ⱼ a j = 1`, with `Z`, `ρ_H`, `S` as in `friedan_question`,
`H_a = ∑ⱼ a j H j` and `K = Z(H_a) / ∏ⱼ Z(H j)^{a j}`: `K² S(H_a) ≤ ∑ⱼ a j S(H j)`. -/
theorem hamiltonians_multi (n m : ℕ) [NeZero n] (H : Fin m → Matrix (Fin n) (Fin n) ℂ)
    (hH : ∀ j, (H j).IsHermitian) (a : Fin m → ℝ) (ha0 : ∀ j, 0 ≤ a j) (has : ∑ j, a j = 1) :
    let Z : Matrix (Fin n) (Fin n) ℂ → ℝ := fun H => (trace (cfc Real.exp (-H))).re
    let ρ : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ :=
      fun H => (Z H)⁻¹ • cfc Real.exp (-H)
    let S : Matrix (Fin n) (Fin n) ℂ → ℝ := fun H => -(trace (ρ H * cfc Real.log (ρ H))).re
    let Ha := ∑ j, a j • H j
    let K := Z Ha / ∏ j, Z (H j) ^ a j
    K ^ 2 * S Ha ≤ ∑ j, a j * S (H j) := by
  sorry

/-- **The log-Euclidean mean of `m` faithful states.** For faithful density matrices `ρ j`
(`j : Fin m`) and weights `a j ≥ 0` with `∑ⱼ a j = 1`, with `M = exp(∑ⱼ a j log ρ j)`, `K = tr M`
and `S(A) = -tr(A log A)`: `K² S(M / K) ≤ ∑ⱼ a j S(ρ j)`. -/
theorem logEuclidean_multi (n m : ℕ) (ρ : Fin m → Matrix (Fin n) (Fin n) ℂ)
    (hρ : ∀ j, (ρ j).PosDef) (hρ1 : ∀ j, (ρ j).trace = 1) (a : Fin m → ℝ) (ha0 : ∀ j, 0 ≤ a j)
    (has : ∑ j, a j = 1) :
    let M := cfc Real.exp (∑ j, a j • cfc Real.log (ρ j))
    let S : Matrix (Fin n) (Fin n) ℂ → ℝ := fun A => -(trace (A * cfc Real.log A)).re
    let K := (trace M).re
    K ^ 2 * S (K⁻¹ • M) ≤ ∑ j, a j * S (ρ j) := by
  sorry

/-- **The multivariate product means of `m + 1` faithful states.** For faithful density matrices
`ρ j` (`j : Fin (m + 1)`), weights `a j ≥ 0` with `∑ⱼ a j = 1` and `z > 0`, with
`X = ρ₀^{a₀/2z} ρ₁^{a₁/2z} ⋯ ρ_m^{a_m/2z}` (list product in the order of the index),
`M = (Xᴴ X)^z`, `K = tr M` and `S(A) = -tr(A log A)`: `K² S(M / K) ≤ ∑ⱼ a j S(ρ j)`. Any other
order of the factors is the same statement for a re-indexed family. -/
theorem product_multi (n m : ℕ) (ρ : Fin (m + 1) → Matrix (Fin n) (Fin n) ℂ)
    (hρ : ∀ j, (ρ j).PosDef) (hρ1 : ∀ j, (ρ j).trace = 1) (a : Fin (m + 1) → ℝ)
    (ha0 : ∀ j, 0 ≤ a j) (has : ∑ j, a j = 1) (z : ℝ) (hz : 0 < z) :
    let X := (List.ofFn fun j => cfc (fun x : ℝ => x ^ (a j / (2 * z))) (ρ j)).prod
    let M := cfc (fun x : ℝ => x ^ z) (Xᴴ * X)
    let S : Matrix (Fin n) (Fin n) ℂ → ℝ := fun A => -(trace (A * cfc Real.log A)).re
    let K := (trace M).re
    K ^ 2 * S (K⁻¹ • M) ≤ ∑ j, a j * S (ρ j) := by
  sorry

end FriedanQuantum
