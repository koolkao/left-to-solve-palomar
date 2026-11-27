/-
Copyright 2026 Ming-Chih Kao. Licensed under the Apache License, Version 2.0;
see the LICENSE file at the root of this repository.
-/
module

public import HadamardFirstCases.Defs

/-! Ported from the archived Left to Solve file `Hadamard.HadamardConjecture.variants.first_cases.lean` (Lean v4.33.1) to Lean
v4.36.0 and the module system; the mathematics and the proof are unchanged unless a comment
says otherwise. -/

@[expose] public section

-- Problem: Hadamard's conjecture — first cases
-- Upstream: formal-conjectures FormalConjectures/Wikipedia/Hadamard.lean:142 (declaration Hadamard.HadamardConjecture.variants.first_cases)
-- Credit: @koolkao (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

/-!
# Hadamard matrices of every order `4k`, `k ≤ 166`

We build an integer `±1` matrix `H` with `H * Hᵀ = n • 1` for every order `n = 4k`, `k ≤ 166`, and
then pass to a real matrix with `|det| = n ^ (n / 2)`.

* `k` even: Sylvester doubling (`hexI_double`).
* `4k - 1` prime: Paley I (`paleyI_isHad`, `paleyI_hex`), via the quadratic character of `ZMod p`
  and Mathlib's Jacobi sum `jacobiSum_nontrivial_inv`.
* `2k - 1` prime: Paley II (`paleyII_isHad`, `paleyII_hex`).
* otherwise: the Goethals–Seidel array over a finite abelian group (`gs_isHad`), fed with four
  `±1` sequences whose periodic autocorrelations sum to zero, checked by the kernel
  (`decide +kernel`) from bit-packed data: Williamson quadruples (Hall 1983, London 2013),
  Djoković's skew supplementary difference sets (1992–2023), T-sequences from base/Turyn(-type)
  sequences (Cohen et al. 1989, Kharaghani–Tayfeh-Rezaie 2005, Best–Djoković–Kharaghani–Ramp 2013,
  Sawade 1985, Schneider), Cooper–Wallis products; for `k = 81` the group is `ZMod 9 × ZMod 9`.
* `k = 101, 149`: Spence's bordered array (Spence 1975) with four sequences of length `k - 1`
  from relative difference sets (`spence_isHad`).

The sequence data were taken from the tables compiled in SageMath and checked here by the kernel.
All Lean code is original.
-/

open Matrix Finset
open scoped Kronecker

namespace OMAHad


/-- An integer `±1` matrix `H` with `H * Hᵀ = n • 1`, `n` the number of rows. -/
def IsHad {ι : Type*} [Fintype ι] [DecidableEq ι] (H : Matrix ι ι ℤ) : Prop :=
  (∀ i j, H i j = 1 ∨ H i j = -1) ∧ H * Hᵀ = (Fintype.card ι : ℤ) • (1 : Matrix ι ι ℤ)

/-- There is an integer Hadamard matrix of order `n`. -/
def HexI (n : ℕ) : Prop := ∃ H : Matrix (Fin n) (Fin n) ℤ, IsHad H

lemma hexI_of_isHad {ι : Type*} [Fintype ι] [DecidableEq ι] {H : Matrix ι ι ℤ} (h : IsHad H) :
    HexI (Fintype.card ι) := by
  let e := Fintype.equivFin ι
  refine ⟨Matrix.reindex e e H, fun i j => by simpa using h.1 (e.symm i) (e.symm j), ?_⟩
  rw [Fintype.card_fin]
  ext i j
  simp only [Matrix.mul_apply, Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.transpose_apply]
  rw [← Equiv.sum_comp e]
  simp only [Equiv.symm_apply_apply]
  have := congrFun (congrFun h.2 (e.symm i)) (e.symm j)
  simp only [Matrix.mul_apply, Matrix.transpose_apply] at this
  rw [this]
  simp [Matrix.smul_apply, Matrix.one_apply]

lemma hexI_congr {m n : ℕ} (h : m = n) (hm : HexI m) : HexI n := h ▸ hm

lemma abs_det_eq {n : ℕ} {x : ℝ} (hx : x ^ 2 = (n : ℝ) ^ n) : |x| = (n : ℝ) ^ ((n : ℝ) / 2) := by
  have h0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  rw [← Real.sqrt_sq_eq_abs, hx, Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul h0]
  congr 1
  ring

theorem isHadamard_of_hexI {n : ℕ} (h : HexI n) :
    ∃ M : Matrix (Fin n) (Fin n) ℝ, Hadamard.IsHadamard M := by
  obtain ⟨H, hpm, hg⟩ := h
  refine ⟨(Int.castRingHom ℝ).mapMatrix H, ?_, ?_⟩
  · intro i j
    rcases hpm i j with h | h <;> simp [h]
  · rw [← RingHom.map_det]
    apply abs_det_eq
    have := congrArg Matrix.det hg
    rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_smul, Matrix.det_one, Fintype.card_fin,
      mul_one] at this
    have h2 : ((H.det : ℤ) : ℝ) ^ 2 = ((n : ℤ) : ℝ) ^ n := by
      rw [← Int.cast_pow, ← Int.cast_pow, sq, this]
    simpa using h2

/-- Sylvester's doubling. -/
def P2 : Matrix (Fin 2) (Fin 2) ℤ := !![1, 1; 1, -1]

lemma P2_mul : P2 * P2ᵀ = (2 : ℤ) • (1 : Matrix (Fin 2) (Fin 2) ℤ) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [P2, Matrix.mul_apply, Fin.sum_univ_two]

theorem hexI_double {n : ℕ} (h : HexI n) : HexI (2 * n) := by
  obtain ⟨H, hpm, hg⟩ := h
  have : IsHad (H ⊗ₖ P2) := by
    refine ⟨?_, ?_⟩
    · rintro ⟨i, a⟩ ⟨j, b⟩
      simp only [Matrix.kronecker_apply]
      rcases hpm i j with h | h <;> fin_cases a <;> fin_cases b <;> simp [h, P2]
    · rw [show (H ⊗ₖ P2)ᵀ = Hᵀ ⊗ₖ P2ᵀ from (Matrix.kroneckerMap_transpose _ _ _).symm, ← Matrix.mul_kronecker_mul, hg, P2_mul,
        Matrix.smul_kronecker, Matrix.kronecker_smul, Matrix.one_kronecker_one, smul_smul]
      simp [Fintype.card_prod, mul_comm]
  have h2 := hexI_of_isHad this
  simpa [Fintype.card_prod, mul_comm] using h2



section Paley

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

/-- Abstract hypotheses on a character-like function `χ` used in Paley's constructions. -/
structure PaleyChar (χ : G → ℤ) : Prop where
  zero : χ 0 = 0
  pm : ∀ x, x ≠ 0 → χ x = 1 ∨ χ x = -1
  sum : ∑ x, χ x = 0
  corr : ∀ c, c ≠ 0 → ∑ x, χ x * χ (x + c) = -1

lemma PaleyChar.sum_sq {χ : G → ℤ} (h : PaleyChar χ) :
    ∑ x, χ x * χ (x + 0) = (Fintype.card G : ℤ) - 1 := by
  have : ∀ x, χ x * χ (x + 0) = if x = 0 then 0 else 1 := by
    intro x
    rw [add_zero]
    split_ifs with hx
    · simp [hx, h.zero]
    · rcases h.pm x hx with h1 | h1 <;> simp [h1]
  rw [Finset.sum_congr rfl (fun x _ => this x), Finset.sum_ite, Finset.sum_const_zero, zero_add,
    Finset.sum_const, Finset.filter_ne' Finset.univ (0 : G), Finset.card_erase_of_mem (mem_univ _),
    Finset.card_univ, nsmul_eq_mul, mul_one, Nat.cast_sub Fintype.card_pos]
  simp

lemma PaleyChar.corr' {χ : G → ℤ} (h : PaleyChar χ) (c : G) :
    ∑ x, χ x * χ (x + c) = if c = 0 then (Fintype.card G : ℤ) - 1 else -1 := by
  split_ifs with hc
  · subst hc; exact h.sum_sq
  · exact h.corr c hc

lemma PaleyChar.sum_shift {χ : G → ℤ} (h : PaleyChar χ) (u : G) : ∑ z, χ (z + u) = 0 := by
  rw [← h.sum]
  exact Fintype.sum_equiv (Equiv.addRight u) _ _ (fun _ => rfl)

lemma sum_mul_shift (f : G → ℤ) (x y : G) :
    ∑ z, f (z + -x) * f (z + -y) = ∑ w, f w * f (w + (x - y)) := by
  refine Fintype.sum_equiv (Equiv.addRight (-x)) _ _ (fun z => ?_)
  simp only [Equiv.coe_addRight]
  congr 2
  abel

/-- The Paley I core: `Q x y = χ (y - x)` on the diagonal-free part, bordered. -/
def paleyI (χ : G → ℤ) : Matrix (Option G) (Option G) ℤ
  | none, _ => 1
  | some _, none => -1
  | some x, some y => (if x = y then 1 else 0) + χ (y + -x)

theorem paleyI_isHad {χ : G → ℤ} (h : PaleyChar χ) (hneg : ∀ x, χ (-x) = -χ x) :
    IsHad (paleyI χ) := by
  refine ⟨?_, ?_⟩
  · rintro (_ | x) (_ | y) <;> simp only [paleyI, reduceCtorEq, true_or, or_true]
    by_cases hxy : x = y
    · simp [hxy, h.zero]
    · have : y + -x ≠ 0 := by
        intro h0; apply hxy; rw [← sub_eq_add_neg, sub_eq_zero] at h0; exact h0.symm
      rcases h.pm _ this with h1 | h1 <;> simp [hxy, h1]
  · ext (_ | x) (_ | y)
    · simp [Matrix.mul_apply, Fintype.sum_option, paleyI, Fintype.card_option]
    · simp only [Matrix.mul_apply, Fintype.sum_option, paleyI, Matrix.transpose_apply, one_mul,
        Fintype.card_option, Matrix.smul_apply, Matrix.one_apply, reduceCtorEq, if_false,
        smul_zero, Finset.sum_add_distrib]
      rw [h.sum_shift]
      simp [Finset.sum_ite_eq]
    · simp only [Matrix.mul_apply, Fintype.sum_option, paleyI, Matrix.transpose_apply, mul_one,
        Fintype.card_option, Matrix.smul_apply, Matrix.one_apply, reduceCtorEq, if_false,
        smul_zero, Finset.sum_add_distrib]
      rw [h.sum_shift]
      simp [Finset.sum_ite_eq]
    · simp only [Matrix.mul_apply, Fintype.sum_option, paleyI, Matrix.transpose_apply,
        Fintype.card_option, Matrix.smul_apply, Matrix.one_apply, Option.some.injEq]
      have e1 : ∀ z, ((if x = z then (1 : ℤ) else 0) + χ (z + -x)) *
          ((if y = z then 1 else 0) + χ (z + -y)) =
          ((if x = z then 1 else 0) * (if y = z then 1 else 0)) +
          ((if x = z then χ (z + -y) else 0) + (if y = z then χ (z + -x) else 0)) +
          χ (z + -x) * χ (z + -y) := by
        intro z; split_ifs <;> ring
      rw [Finset.sum_congr rfl (fun z _ => e1 z), Finset.sum_add_distrib, Finset.sum_add_distrib,
        Finset.sum_add_distrib, sum_mul_shift, h.corr']
      simp only [Finset.sum_ite_eq, mem_univ, if_true]
      by_cases hxy : x = y
      · subst hxy; simp [h.zero]; ring
      · have hne : x - y ≠ 0 := sub_ne_zero.mpr hxy
        have h2 : χ (y + -x) + χ (x + -y) = 0 := by
          rw [show y + -x = -(x + -y) by abel, hneg]; ring
        simp only [hxy, hne, if_false, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', mem_univ,
          smul_zero]
        simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, mem_univ, if_true, hxy, if_false]
        linarith

/-- The Paley II conference matrix, for symmetric `χ`. -/
def conf (χ : G → ℤ) : Matrix (Option G) (Option G) ℤ
  | none, none => 0
  | none, some _ => 1
  | some _, none => 1
  | some x, some y => χ (y + -x)

lemma conf_transpose {χ : G → ℤ} (hneg : ∀ x, χ (-x) = χ x) : (conf χ)ᵀ = conf χ := by
  ext (_ | x) (_ | y) <;> simp [conf]
  rw [← hneg]; congr 1; abel

lemma conf_mul {χ : G → ℤ} (h : PaleyChar χ) :
    conf χ * (conf χ)ᵀ = (Fintype.card G : ℤ) • (1 : Matrix (Option G) (Option G) ℤ) := by
  ext (_ | x) (_ | y)
  · simp [Matrix.mul_apply, Fintype.sum_option, conf]
  · simp only [Matrix.mul_apply, Fintype.sum_option, conf, Matrix.transpose_apply, one_mul,
      zero_mul, zero_add, Matrix.smul_apply, Matrix.one_apply, reduceCtorEq, if_false, smul_zero]
    exact h.sum_shift _
  · simp only [Matrix.mul_apply, Fintype.sum_option, conf, Matrix.transpose_apply, mul_one,
      mul_zero, zero_add, Matrix.smul_apply, Matrix.one_apply, reduceCtorEq, if_false, smul_zero]
    exact h.sum_shift _
  · simp only [Matrix.mul_apply, Fintype.sum_option, conf, Matrix.transpose_apply, mul_one,
      Matrix.smul_apply, Matrix.one_apply, Option.some.injEq]
    rw [sum_mul_shift, h.corr']
    by_cases hxy : x = y
    · subst hxy; simp
    · simp [hxy, sub_ne_zero.mpr hxy]

def N2 : Matrix (Fin 2) (Fin 2) ℤ := !![1, -1; -1, -1]

theorem paleyII_isHad {χ : G → ℤ} (h : PaleyChar χ) (hneg : ∀ x, χ (-x) = χ x) :
    IsHad (conf χ ⊗ₖ P2 + (1 : Matrix (Option G) (Option G) ℤ) ⊗ₖ N2) := by
  have hdiag : ∀ x, conf χ x x = 0 := by
    rintro (_ | x) <;> simp [conf, h.zero]
  have hoff : ∀ x y, x ≠ y → conf χ x y = 1 ∨ conf χ x y = -1 := by
    rintro (_ | x) (_ | y) hxy
    · exact absurd rfl hxy
    · simp [conf]
    · simp [conf]
    · simp only [conf]
      apply h.pm
      intro h0; apply hxy; rw [← sub_eq_add_neg, sub_eq_zero] at h0; rw [h0]
  refine ⟨?_, ?_⟩
  · rintro ⟨x, a⟩ ⟨y, b⟩
    simp only [Matrix.add_apply, Matrix.kronecker_apply, Matrix.one_apply]
    by_cases hxy : x = y
    · subst hxy; rw [hdiag]; fin_cases a <;> fin_cases b <;> simp [N2]
    · rcases hoff x y hxy with h1 | h1 <;> rw [h1] <;> fin_cases a <;> fin_cases b <;>
        simp [P2, hxy]
  · have hPN : P2 * N2ᵀ + N2 * P2ᵀ = 0 := by
      ext i j; fin_cases i <;> fin_cases j <;>
        simp only [Matrix.add_apply, Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply] <;>
        simp [P2, N2]
    have hNN : N2 * N2ᵀ = (2 : ℤ) • (1 : Matrix (Fin 2) (Fin 2) ℤ) := by
      ext i j; fin_cases i <;> fin_cases j <;> simp [N2, Matrix.mul_apply, Fin.sum_univ_two]
    have tk : ∀ {m n : Type _} (A : Matrix m m ℤ) (B : Matrix n n ℤ), (A ⊗ₖ B)ᵀ = Aᵀ ⊗ₖ Bᵀ :=
      fun A B => (Matrix.kroneckerMap_transpose _ _ _).symm
    rw [Matrix.transpose_add, tk, tk, Matrix.transpose_one, conf_transpose hneg, Matrix.add_mul,
      Matrix.mul_add, Matrix.mul_add, ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
      ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, Matrix.mul_one, Matrix.one_mul,
      Matrix.one_mul]
    rw [show conf χ * conf χ = conf χ * (conf χ)ᵀ by rw [conf_transpose hneg], conf_mul h, P2_mul,
      hNN, add_assoc, ← add_assoc (conf χ ⊗ₖ (P2 * N2ᵀ)), ← Matrix.kronecker_add, hPN,
      Matrix.kronecker_zero, zero_add, Matrix.smul_kronecker, Matrix.kronecker_smul,
      Matrix.one_kronecker_one, smul_smul, ← add_smul]
    simp only [Fintype.card_prod, Fintype.card_option, Fintype.card_fin]
    congr 1
    push_cast; ring

end Paley


section GS

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

/-- Periodic cross-correlation. -/
def corr (f g : G → ℤ) (s : G) : ℤ := ∑ w, f w * g (w + s)

/-- Convolution. -/
def conv (f g : G → ℤ) (t : G) : ℤ := ∑ w, f w * g (t - w)

lemma sumS1 (f g : G → ℤ) (u v : G) : ∑ z, f (z + u) * g (z + v) = corr f g (v - u) := by
  refine Fintype.sum_equiv (Equiv.addRight u) _ _ (fun z => ?_)
  simp only [Equiv.coe_addRight]; congr 2; abel

lemma sumS2 (f g : G → ℤ) (u v : G) : ∑ z, f (-z + u) * g (-z + v) = corr f g (v - u) := by
  refine Fintype.sum_equiv ((Equiv.neg G).trans (Equiv.addRight u)) _ _ (fun z => ?_)
  simp only [Equiv.trans_apply, Equiv.neg_apply, Equiv.coe_addRight]; congr 2; abel

lemma sumS3 (f g : G → ℤ) (u v : G) : ∑ z, f (z + u) * g (-z + v) = conv f g (u + v) := by
  refine Fintype.sum_equiv (Equiv.addRight u) _ _ (fun z => ?_)
  simp only [Equiv.coe_addRight]; congr 2; abel

lemma sumS4 (f g : G → ℤ) (u v : G) : ∑ z, f (-z + u) * g (z + v) = conv f g (u + v) := by
  refine Fintype.sum_equiv ((Equiv.neg G).trans (Equiv.addRight u)) _ _ (fun z => ?_)
  simp only [Equiv.trans_apply, Equiv.neg_apply, Equiv.coe_addRight]; congr 2; abel

lemma corr_swap (f g : G → ℤ) (s : G) : corr g f s = corr f g (-s) := by
  unfold corr
  refine Fintype.sum_equiv (Equiv.addRight s) _ _ (fun w => ?_)
  simp only [Equiv.coe_addRight, add_neg_cancel_right]; ring

lemma conv_comm (f g : G → ℤ) (t : G) : conv g f t = conv f g t := by
  unfold conv
  refine Fintype.sum_equiv ((Equiv.neg G).trans (Equiv.addRight t)) _ _ (fun w => ?_)
  simp only [Equiv.trans_apply, Equiv.neg_apply, Equiv.coe_addRight]
  rw [show t - (-w + t) = w by abel, show -w + t = t - w by abel]; ring

/-- The Goethals–Seidel array, entrywise, for group-developed blocks. -/
def gsE (a b c d : G → ℤ) : Fin 4 → Fin 4 → G → G → ℤ :=
  ![![fun x z => a (z + -x), fun x z => b (-z + -x), fun x z => c (-z + -x), fun x z => d (-z + -x)],
    ![fun x z => -b (-z + -x), fun x z => a (z + -x), fun x z => d (z + x), fun x z => -c (z + x)],
    ![fun x z => -c (-z + -x), fun x z => -d (z + x), fun x z => a (z + -x), fun x z => b (z + x)],
    ![fun x z => -d (-z + -x), fun x z => c (z + x), fun x z => -b (z + x), fun x z => a (z + -x)]]

def gs (a b c d : G → ℤ) : Matrix (Fin 4 × G) (Fin 4 × G) ℤ := fun p q => gsE a b c d p.1 q.1 p.2 q.2

/-- Hypotheses on four `±1` sequences: total periodic autocorrelation vanishes off zero. -/
structure GSQuad (a b c d : G → ℤ) : Prop where
  pm : ∀ x, (a x = 1 ∨ a x = -1) ∧ (b x = 1 ∨ b x = -1) ∧ (c x = 1 ∨ c x = -1) ∧ (d x = 1 ∨ d x = -1)
  paf : ∀ s, s ≠ 0 → corr a a s + corr b b s + corr c c s + corr d d s = 0

lemma corr_self_zero {f : G → ℤ} (h : ∀ x, f x = 1 ∨ f x = -1) : corr f f 0 = Fintype.card G := by
  have : ∀ w, f w * f w = 1 := by
    intro w; rcases h w with h1 | h1 <;> simp [h1]
  simp only [corr, add_zero, this]
  simp

lemma corr_self_neg (f : G → ℤ) (s : G) : corr f f (-s) = corr f f s := by
  rw [← corr_swap]

theorem gs_isHad {a b c d : G → ℤ} (h : GSQuad a b c d) : IsHad (gs a b c d) := by
  refine ⟨?_, ?_⟩
  · rintro ⟨i, x⟩ ⟨k, z⟩
    obtain ⟨ha, hb, hc, hd⟩ := h.pm (z + -x)
    obtain ⟨ha', hb', hc', hd'⟩ := h.pm (-z + -x)
    obtain ⟨_, hb'', hc'', hd''⟩ := h.pm (z + x)
    simp only [gs]
    fin_cases i <;> fin_cases k <;> simp [gsE] <;> omega
  · have tot : ∀ s, corr a a s + corr b b s + corr c c s + corr d d s =
        if s = 0 then 4 * (Fintype.card G : ℤ) else 0 := by
      intro s
      split_ifs with hs
      · subst hs
        rw [corr_self_zero (fun x => (h.pm x).1), corr_self_zero (fun x => (h.pm x).2.1),
          corr_self_zero (fun x => (h.pm x).2.2.1), corr_self_zero (fun x => (h.pm x).2.2.2)]
        ring
      · exact h.paf s hs
    ext ⟨i, x⟩ ⟨j, y⟩
    have key : ∀ f : G → ℤ, corr f f (y + -1 • x) = corr f f (-1 • y + x) := fun f => by
      rw [← corr_self_neg]; congr 1; abel
    have ht := tot (-1 • y + x)
    have hiff : (-1 • y + x = 0) ↔ x = y := by
      constructor
      · intro h0; rw [neg_one_zsmul, neg_add_eq_sub, sub_eq_zero] at h0; exact h0
      · rintro rfl; abel
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Fintype.sum_prod_type, Fin.sum_univ_four,
      gs, Matrix.smul_apply, Matrix.one_apply, Prod.mk.injEq, Fintype.card_prod, Fintype.card_fin]
    fin_cases i <;> fin_cases j <;>
      simp only [gsE, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val, neg_mul, mul_neg,
        Finset.sum_neg_distrib, neg_neg, sumS1, sumS2, sumS3, sumS4] <;>
      (try simp only [corr_swap b a, corr_swap c a, corr_swap d a, corr_swap c b, corr_swap d b,
        corr_swap d c, conv_comm b a, conv_comm c a, conv_comm d a, conv_comm c b, conv_comm d b,
        conv_comm d c]) <;> abel_nf
    all_goals first
      | (simp only [false_and, if_false, smul_zero, Fin.isValue]; done)
      | (simp only [key, true_and, Fin.isValue]
         by_cases hxy : x = y
         · simp only [hxy, if_true] at ht ⊢
           rw [if_pos (by abel)] at ht
           simp only [smul_eq_mul, mul_one, Nat.cast_mul, Nat.cast_ofNat]
           linarith
         · simp only [hxy, if_false, smul_zero] at ht ⊢
           rw [if_neg (fun h0 => hxy (hiff.mp h0))] at ht
           linarith)

end GS

section Quad

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

lemma quad_corr (hF : ringChar F ≠ 2) (c : F) (hc : c ≠ 0) :
    ∑ x, quadraticChar F x * quadraticChar F (x + c) = -1 := by
  set χ := quadraticChar F
  have hχ1 : χ ≠ 1 := quadraticChar_ne_one hF
  have hJ : ∑ t, χ t * χ (1 - t) = -χ (-1) := by
    have := jacobiSum_nontrivial_inv hχ1
    rw [(quadraticChar_isQuadratic F).inv] at this
    rw [jacobiSum] at this; exact this
  have hm : (-c) ≠ 0 := neg_ne_zero.mpr hc
  have e : ∑ x, χ x * χ (x + c) = ∑ t, χ (-c * t) * χ (-c * t + c) :=
    (Fintype.sum_bijective (fun t => -c * t) (mulLeft_bijective₀ _ hm) _ _ (fun _ => rfl)).symm
  rw [e]
  have e2 : ∀ t, χ (-c * t) * χ (-c * t + c) = (χ (-c) * χ c) * (χ t * χ (1 - t)) := by
    intro t
    rw [show -c * t + c = c * (1 - t) by ring, map_mul, map_mul]; ring
  rw [Finset.sum_congr rfl (fun t _ => e2 t), ← Finset.mul_sum, hJ,
    show -c = -1 * c by ring, map_mul]
  have h1 : χ c * χ c = 1 := by rw [← sq]; exact quadraticChar_sq_one hc
  have h2 : χ (-1) * χ (-1) = 1 := by rw [← sq]; exact quadraticChar_sq_one (by simp)
  linear_combination (-(χ (-1)) * χ (-1)) * h1 - h2

lemma quad_paleyChar (hF : ringChar F ≠ 2) : PaleyChar (fun x : F => quadraticChar F x) where
  zero := quadraticChar_zero
  pm := fun _ hx => quadraticChar_dichotomy hx
  sum := quadraticChar_sum_zero hF
  corr := quad_corr hF

end Quad

lemma ringChar_zmod_ne_two {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) : ringChar (ZMod p) ≠ 2 := by
  rw [ZMod.ringChar_zmod_n]; exact hp

theorem paleyI_hex (p : ℕ) [Fact p.Prime] (hp : p % 4 = 3) : HexI (p + 1) := by
  have h2 : p ≠ 2 := by rintro rfl; norm_num at hp
  have hF := ringChar_zmod_ne_two h2
  have hneg : ∀ x : ZMod p, quadraticChar (ZMod p) (-x) = -quadraticChar (ZMod p) x := by
    intro x
    rw [show -x = -1 * x by ring, map_mul, quadraticChar_neg_one hF, ZMod.card,
      ZMod.χ₄_nat_three_mod_four hp]; ring
  have := hexI_of_isHad (paleyI_isHad (quad_paleyChar hF) hneg)
  simpa [Fintype.card_option, ZMod.card] using this

theorem paleyII_hex (p : ℕ) [Fact p.Prime] (hp : p % 4 = 1) : HexI (2 * (p + 1)) := by
  have h2 : p ≠ 2 := by rintro rfl; norm_num at hp
  have hF := ringChar_zmod_ne_two h2
  have hneg : ∀ x : ZMod p, quadraticChar (ZMod p) (-x) = quadraticChar (ZMod p) x := by
    intro x
    rw [show -x = -1 * x by ring, map_mul, quadraticChar_neg_one hF, ZMod.card,
      ZMod.χ₄_nat_one_mod_four hp]; ring
  have := hexI_of_isHad (paleyII_isHad (quad_paleyChar hF) hneg)
  simpa [Fintype.card_option, Fintype.card_prod, ZMod.card, mul_comm] using this

/- ### Kernel-checkable data for group-developed quadruples on `ZMod m` -/

/-- The sign encoded by bit `i` of `N` (`1` bit means `-1`). -/
def sg (N i : ℕ) : ℤ := if N.testBit i then -1 else 1

lemma sg_pm (N i : ℕ) : sg N i = 1 ∨ sg N i = -1 := by
  unfold sg; split_ifs <;> simp

/-- Partial periodic autocorrelation sums. -/
def pafR (N m s : ℕ) : ℕ → ℤ
  | 0 => 0
  | i + 1 => pafR N m s i + sg N i * sg N ((i + s) % m)

lemma pafR_eq (N m s k : ℕ) :
    pafR N m s k = ∑ i ∈ Finset.range k, sg N i * sg N ((i + s) % m) := by
  induction k with
  | zero => rfl
  | succ k ih => rw [pafR, ih, Finset.sum_range_succ]

def tot4 (A B C D m s : ℕ) : ℤ := pafR A m s m + pafR B m s m + pafR C m s m + pafR D m s m

def allZ (A B C D m : ℕ) : ℕ → Bool
  | 0 => true
  | k + 1 => (tot4 A B C D m (k + 1) == 0) && allZ A B C D m k

lemma allZ_spec {A B C D m K : ℕ} (h : allZ A B C D m K = true) :
    ∀ s, 1 ≤ s → s ≤ K → tot4 A B C D m s = 0 := by
  induction K with
  | zero => intro s h1 h2; omega
  | succ K ih =>
    intro s h1 h2
    simp only [allZ, Bool.and_eq_true, beq_iff_eq] at h
    rcases Nat.lt_or_ge s (K + 1) with hs | hs
    · exact ih h.2 s h1 (by omega)
    · rw [show s = K + 1 by omega]; exact h.1

lemma corr_zmod (N n : ℕ) (s : ZMod (n + 1)) :
    corr (fun x : ZMod (n + 1) => sg N x.val) (fun x => sg N x.val) s = pafR N (n + 1) s.val (n + 1) := by
  rw [pafR_eq, corr]
  rw [← Fin.sum_univ_eq_sum_range (fun i => sg N i * sg N ((i + s.val) % (n + 1)))]
  rfl

theorem gs_hex (n A B C D : ℕ) (h : allZ A B C D (n + 1) n = true) : HexI (4 * (n + 1)) := by
  have hq : GSQuad (G := ZMod (n + 1)) (fun x => sg A x.val) (fun x => sg B x.val)
      (fun x => sg C x.val) (fun x => sg D x.val) := by
    refine ⟨fun x => ⟨sg_pm _ _, sg_pm _ _, sg_pm _ _, sg_pm _ _⟩, fun s hs => ?_⟩
    rw [corr_zmod, corr_zmod, corr_zmod, corr_zmod]
    have h1 : 1 ≤ s.val := Nat.one_le_iff_ne_zero.mpr ((ZMod.val_ne_zero s).mpr hs)
    have h2 : s.val ≤ n := Nat.lt_succ_iff.mp (ZMod.val_lt s)
    exact allZ_spec h s.val h1 h2
  have := hexI_of_isHad (gs_isHad hq)
  simpa [Fintype.card_prod, ZMod.card] using this

/- ### Data on `ZMod (a+1) × ZMod (b+1)` (used once, for order `4 · 81`) -/

def pafI (N q s1 s2 i : ℕ) (p : ℕ) : ℕ → ℤ
  | 0 => 0
  | j + 1 => pafI N q s1 s2 i p j + sg N (q * i + j) * sg N (q * ((i + s1) % p) + (j + s2) % q)

def paf2 (N p q s1 s2 : ℕ) : ℕ → ℤ
  | 0 => 0
  | i + 1 => paf2 N p q s1 s2 i + pafI N q s1 s2 i p q

lemma pafI_eq (N q s1 s2 i p k : ℕ) : pafI N q s1 s2 i p k =
    ∑ j ∈ Finset.range k, sg N (q * i + j) * sg N (q * ((i + s1) % p) + (j + s2) % q) := by
  induction k with
  | zero => rfl
  | succ k ih => rw [pafI, ih, Finset.sum_range_succ]

lemma paf2_eq (N p q s1 s2 k : ℕ) : paf2 N p q s1 s2 k = ∑ i ∈ Finset.range k,
    ∑ j ∈ Finset.range q, sg N (q * i + j) * sg N (q * ((i + s1) % p) + (j + s2) % q) := by
  induction k with
  | zero => rfl
  | succ k ih => rw [paf2, ih, Finset.sum_range_succ, pafI_eq]

def tot2 (A B C D p q s1 s2 : ℕ) : ℤ :=
  paf2 A p q s1 s2 p + paf2 B p q s1 s2 p + paf2 C p q s1 s2 p + paf2 D p q s1 s2 p

def allZ2 (A B C D p q : ℕ) : ℕ → Bool
  | 0 => true
  | k + 1 => (tot2 A B C D p q ((k + 1) / q) ((k + 1) % q) == 0) && allZ2 A B C D p q k

lemma allZ2_spec {A B C D p q K : ℕ} (h : allZ2 A B C D p q K = true) :
    ∀ k, 1 ≤ k → k ≤ K → tot2 A B C D p q (k / q) (k % q) = 0 := by
  induction K with
  | zero => intro s h1 h2; omega
  | succ K ih =>
    intro s h1 h2
    simp only [allZ2, Bool.and_eq_true, beq_iff_eq] at h
    rcases Nat.lt_or_ge s (K + 1) with hs | hs
    · exact ih h.2 s h1 (by omega)
    · rw [show s = K + 1 by omega]; exact h.1

lemma corr_zmod2 (N a b : ℕ) (s : ZMod (a + 1) × ZMod (b + 1)) :
    corr (fun x : ZMod (a + 1) × ZMod (b + 1) => sg N ((b + 1) * x.1.val + x.2.val))
      (fun x => sg N ((b + 1) * x.1.val + x.2.val)) s =
      paf2 N (a + 1) (b + 1) s.1.val s.2.val (a + 1) := by
  rw [paf2_eq, corr, Fintype.sum_prod_type]
  rw [← Fin.sum_univ_eq_sum_range]
  refine Fintype.sum_congr _ _ (fun i => ?_)
  rw [← Fin.sum_univ_eq_sum_range]
  rfl

theorem gs2_hex (a b A B C D : ℕ)
    (h : allZ2 A B C D (a + 1) (b + 1) ((a + 1) * (b + 1) - 1) = true) :
    HexI (4 * ((a + 1) * (b + 1))) := by
  have hq : GSQuad (G := ZMod (a + 1) × ZMod (b + 1))
      (fun x => sg A ((b + 1) * x.1.val + x.2.val)) (fun x => sg B ((b + 1) * x.1.val + x.2.val))
      (fun x => sg C ((b + 1) * x.1.val + x.2.val)) (fun x => sg D ((b + 1) * x.1.val + x.2.val)) := by
    refine ⟨fun x => ⟨sg_pm _ _, sg_pm _ _, sg_pm _ _, sg_pm _ _⟩, fun s hs => ?_⟩
    rw [corr_zmod2, corr_zmod2, corr_zmod2, corr_zmod2]
    have h1 := ZMod.val_lt s.1
    have h2 := ZMod.val_lt s.2
    set k := (b + 1) * s.1.val + s.2.val with hk
    have hk1 : k / (b + 1) = s.1.val := by
      rw [hk, Nat.mul_add_div (Nat.succ_pos b), Nat.div_eq_of_lt h2, add_zero]
    have hk2 : k % (b + 1) = s.2.val := by
      rw [hk, Nat.mul_add_mod, Nat.mod_eq_of_lt h2]
    have hpos : 1 ≤ k := by
      by_contra hcon
      have h0 : k = 0 := by omega
      have e1 : s.1.val = 0 := by rw [← hk1, h0, Nat.zero_div]
      have e2 : s.2.val = 0 := by rw [← hk2, h0, Nat.zero_mod]
      apply hs
      exact Prod.ext ((ZMod.val_eq_zero _).mp e1) ((ZMod.val_eq_zero _).mp e2)
    have hle : k ≤ (a + 1) * (b + 1) - 1 := by
      have : k < (a + 1) * (b + 1) := by
        calc k = (b + 1) * s.1.val + s.2.val := hk
          _ < (b + 1) * s.1.val + (b + 1) := by omega
          _ = (b + 1) * (s.1.val + 1) := by ring
          _ ≤ (b + 1) * (a + 1) := Nat.mul_le_mul_left _ h1
          _ = (a + 1) * (b + 1) := by ring
      omega
    have := allZ2_spec h k hpos hle
    rw [hk1, hk2] at this
    exact this
  have := hexI_of_isHad (gs_isHad hq)
  simpa [Fintype.card_prod, ZMod.card] using this

/- ### A bordered Goethals–Seidel array (Spence 1975), for orders `4q` with `q = 101, 149` -/

section Spence

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

/-- The inner Goethals–Seidel-type array used in the bordered construction. -/
def gsV (a b c d : G → ℤ) : Fin 4 → Fin 4 → G → G → ℤ :=
  ![![fun x z => a (z + -x), fun x z => b (-z + -x), fun x z => c (-z + -x), fun x z => d (-z + -x)],
    ![fun x z => -b (-z + -x), fun x z => a (z + -x), fun x z => -d (z + x), fun x z => c (z + x)],
    ![fun x z => -c (-z + -x), fun x z => d (z + x), fun x z => a (z + -x), fun x z => -b (z + x)],
    ![fun x z => -d (-z + -x), fun x z => -c (z + x), fun x z => b (z + x), fun x z => a (z + -x)]]

lemma gsV_prod (a b c d : G → ℤ) (i j : Fin 4) (x y : G) :
    ∑ k, ∑ z, gsV a b c d i k x z * gsV a b c d j k y z =
      if i = j then corr a a (-1 • y + x) + corr b b (-1 • y + x) + corr c c (-1 • y + x) +
        corr d d (-1 • y + x) else 0 := by
  have key : ∀ f : G → ℤ, corr f f (y + -1 • x) = corr f f (-1 • y + x) := fun f => by
    rw [← corr_self_neg]; congr 1; abel
  simp only [Fin.sum_univ_four]
  fin_cases i <;> fin_cases j <;>
    simp only [gsV, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val, neg_mul, mul_neg,
      Finset.sum_neg_distrib, neg_neg, sumS1, sumS2, sumS3, sumS4] <;>
    (try simp only [corr_swap b a, corr_swap c a, corr_swap d a, corr_swap c b, corr_swap d b,
      corr_swap d c, conv_comm b a, conv_comm c a, conv_comm d a, conv_comm c b, conv_comm d b,
      conv_comm d c]) <;> abel_nf <;> (try simp only [key]) <;>
    (try simp only [Fin.isValue, if_true, if_false, ite_true, ite_false, ↓reduceIte]) <;> abel

lemma sum_comp_add (f : G → ℤ) (u : G) : ∑ z, f (z + u) = ∑ z, f z :=
  Fintype.sum_equiv (Equiv.addRight u) _ _ (fun _ => rfl)

lemma sum_comp_neg_add (f : G → ℤ) (u : G) : ∑ z, f (-z + u) = ∑ z, f z :=
  Fintype.sum_equiv ((Equiv.neg G).trans (Equiv.addRight u)) _ _ (fun _ => rfl)

def TL : Matrix (Fin 4) (Fin 4) ℤ := !![1, -1, 1, 1; 1, 1, -1, 1; -1, 1, 1, 1; -1, -1, -1, 1]
def TR : Matrix (Fin 4) (Fin 4) ℤ := !![1, 1, 1, 1; -1, 1, -1, 1; -1, 1, 1, -1; -1, -1, 1, 1]
def BL : Matrix (Fin 4) (Fin 4) ℤ := !![-1, 1, 1, -1; -1, -1, 1, 1; -1, -1, -1, -1; 1, -1, 1, -1]

/-- The bordered array. -/
def spenceM (a b c d : G → ℤ) : Matrix (Fin 4 ⊕ (Fin 4 × G)) (Fin 4 ⊕ (Fin 4 × G)) ℤ
  | .inl r, .inl l => TL r l
  | .inl r, .inr kz => TR r kz.1
  | .inr ix, .inl l => BL ix.1 l
  | .inr ix, .inr kz => gsV a b c d ix.1 kz.1 ix.2 kz.2

structure SpenceQuad (a b c d : G → ℤ) : Prop where
  pm : ∀ x, (a x = 1 ∨ a x = -1) ∧ (b x = 1 ∨ b x = -1) ∧ (c x = 1 ∨ c x = -1) ∧ (d x = 1 ∨ d x = -1)
  paf : ∀ s, s ≠ 0 → corr a a s + corr b b s + corr c c s + corr d d s = -4
  sa : ∑ x, a x = 0
  sb : ∑ x, b x = 0
  sc : ∑ x, c x = 0
  sd : ∑ x, d x = 2

theorem spence_isHad {a b c d : G → ℤ} (h : SpenceQuad a b c d) : IsHad (spenceM a b c d) := by
  refine ⟨?_, ?_⟩
  · rintro (r | ⟨i, x⟩) (l | ⟨k, z⟩)
    · fin_cases r <;> fin_cases l <;> simp [spenceM, TL]
    · fin_cases r <;> fin_cases k <;> simp [spenceM, TR]
    · fin_cases i <;> fin_cases l <;> simp [spenceM, BL]
    · obtain ⟨ha, hb, hc, hd⟩ := h.pm (z + -x)
      obtain ⟨ha', hb', hc', hd'⟩ := h.pm (-z + -x)
      obtain ⟨_, hb'', hc'', hd''⟩ := h.pm (z + x)
      simp only [spenceM]
      fin_cases i <;> fin_cases k <;> simp [gsV] <;> omega
  · have hcard : Fintype.card (Fin 4 ⊕ (Fin 4 × G)) = 4 + 4 * Fintype.card G := by
      simp [Fintype.card_sum, Fintype.card_prod]
    have tot : ∀ s, corr a a s + corr b b s + corr c c s + corr d d s =
        if s = 0 then 4 * (Fintype.card G : ℤ) else -4 := by
      intro s
      split_ifs with hs
      · subst hs
        rw [corr_self_zero (fun x => (h.pm x).1), corr_self_zero (fun x => (h.pm x).2.1),
          corr_self_zero (fun x => (h.pm x).2.2.1), corr_self_zero (fun x => (h.pm x).2.2.2)]
        ring
      · exact h.paf s hs
    have hiff : ∀ x y : G, (-1 • y + x = 0) ↔ x = y := by
      intro x y
      constructor
      · intro h0; rw [neg_one_zsmul, neg_add_eq_sub, sub_eq_zero] at h0; exact h0
      · rintro rfl; abel
    rw [hcard]
    ext (r | ⟨i, x⟩) (l | ⟨j, y⟩)
    · simp only [Matrix.mul_apply, Matrix.transpose_apply, Fintype.sum_sum_type,
        Fintype.sum_prod_type, spenceM, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
        Fin.sum_univ_four, Matrix.smul_apply, Matrix.one_apply, Sum.inl.injEq]
      fin_cases r <;> fin_cases l <;> simp [TL, TR] <;> ring
    · simp only [Matrix.mul_apply, Matrix.transpose_apply, Fintype.sum_sum_type,
        Fintype.sum_prod_type, spenceM, Fin.sum_univ_four, Matrix.smul_apply, Matrix.one_apply,
        reduceCtorEq, if_false, smul_zero, ← Finset.mul_sum]
      fin_cases r <;> fin_cases j <;>
        simp only [gsV, TL, TR, BL, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val,
          Matrix.of_apply, Finset.sum_neg_distrib, sum_comp_add, sum_comp_neg_add, h.sa, h.sb, h.sc,
          h.sd] <;> norm_num
    · simp only [Matrix.mul_apply, Matrix.transpose_apply, Fintype.sum_sum_type,
        Fintype.sum_prod_type, spenceM, Fin.sum_univ_four, Matrix.smul_apply, Matrix.one_apply,
        reduceCtorEq, if_false, smul_zero, ← Finset.sum_mul]
      fin_cases i <;> fin_cases l <;>
        simp only [gsV, TL, TR, BL, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val,
          Matrix.of_apply, Finset.sum_neg_distrib, sum_comp_add, sum_comp_neg_add, h.sa, h.sb, h.sc,
          h.sd, neg_mul, one_mul] <;> norm_num
    · simp only [Matrix.mul_apply, Matrix.transpose_apply, Fintype.sum_sum_type, spenceM,
        Matrix.smul_apply, Matrix.one_apply, Sum.inr.injEq, Prod.mk.injEq]
      rw [Fintype.sum_prod_type, gsV_prod]
      rw [Fin.sum_univ_four]
      by_cases hij : i = j
      · subst hij
        simp only [if_true, true_and]
        rw [tot]
        by_cases hxy : x = y
        · subst hxy
          rw [if_pos ((hiff x x).mpr rfl), if_pos rfl]
          fin_cases i <;> simp [BL]
        · rw [if_neg (fun h0 => hxy ((hiff x y).mp h0)), if_neg hxy]
          fin_cases i <;> simp [BL]
      · simp only [hij, if_false, false_and, smul_zero, add_zero]
        fin_cases i <;> fin_cases j <;> simp [BL] at hij ⊢

end Spence

def allZc (A B C D m : ℕ) (t : ℤ) : ℕ → Bool
  | 0 => true
  | k + 1 => (tot4 A B C D m (k + 1) == t) && allZc A B C D m t k

lemma allZc_spec {A B C D m K : ℕ} {t : ℤ} (h : allZc A B C D m t K = true) :
    ∀ s, 1 ≤ s → s ≤ K → tot4 A B C D m s = t := by
  induction K with
  | zero => intro s h1 h2; omega
  | succ K ih =>
    intro s h1 h2
    simp only [allZc, Bool.and_eq_true, beq_iff_eq] at h
    rcases Nat.lt_or_ge s (K + 1) with hs | hs
    · exact ih h.2 s h1 (by omega)
    · rw [show s = K + 1 by omega]; exact h.1

def sumR (N : ℕ) : ℕ → ℤ
  | 0 => 0
  | i + 1 => sumR N i + sg N i

lemma sumR_eq (N k : ℕ) : sumR N k = ∑ i ∈ Finset.range k, sg N i := by
  induction k with
  | zero => rfl
  | succ k ih => rw [sumR, ih, Finset.sum_range_succ]

lemma sum_zmod (N n : ℕ) : ∑ x : ZMod (n + 1), sg N x.val = sumR N (n + 1) := by
  rw [sumR_eq, ← Fin.sum_univ_eq_sum_range]
  rfl

theorem spence_hex (n A B C D : ℕ) (h : allZc A B C D (n + 1) (-4) n = true)
    (ha : sumR A (n + 1) = 0) (hb : sumR B (n + 1) = 0) (hc : sumR C (n + 1) = 0)
    (hd : sumR D (n + 1) = 2) : HexI (4 + 4 * (n + 1)) := by
  have hq : SpenceQuad (G := ZMod (n + 1)) (fun x => sg A x.val) (fun x => sg B x.val)
      (fun x => sg C x.val) (fun x => sg D x.val) := by
    refine ⟨fun x => ⟨sg_pm _ _, sg_pm _ _, sg_pm _ _, sg_pm _ _⟩, fun s hs => ?_,
      by rw [sum_zmod, ha], by rw [sum_zmod, hb], by rw [sum_zmod, hc], by rw [sum_zmod, hd]⟩
    rw [corr_zmod, corr_zmod, corr_zmod, corr_zmod]
    have h1 : 1 ≤ s.val := Nat.one_le_iff_ne_zero.mpr ((ZMod.val_ne_zero s).mpr hs)
    have h2 : s.val ≤ n := Nat.lt_succ_iff.mp (ZMod.val_lt s)
    exact allZc_spec h s.val h1 h2
  have := hexI_of_isHad (spence_isHad hq)
  simpa [Fintype.card_sum, Fintype.card_prod, ZMod.card] using this

/- ### Orders `4 · 101` and `4 · 149`: Spence's bordered array (data from Spence's relative difference sets) -/

theorem hex4_101 : HexI (4 * 101) := hexI_congr (by norm_num) (spence_hex 99
  410811836209302887598968423125
  24395363851291877618874379350
  24395363851294129418688064596
  55674014173602952415937886624
  (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  (by decide +kernel))

theorem hex4_149 : HexI (4 * 149) := hexI_congr (by norm_num) (spence_hex 147
  353024592154045679079155997483901472280655105
  24758326043423676451150098424897699664054550
  24758326043423676451187877356760656825764116
  60230286346533571983165205272000523227290024
  (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  (by decide +kernel))

/- ### One construction for each odd `k ≤ 165` (except `k = 101, 149`) -/

theorem hex4_1 : HexI (4 * 1) := by
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  exact hexI_congr (by norm_num) (paleyI_hex 3 (by norm_num))

theorem hex4_3 : HexI (4 * 3) := by
  have : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  exact hexI_congr (by norm_num) (paleyI_hex 11 (by norm_num))

theorem hex4_5 : HexI (4 * 5) := by
  have : Fact (Nat.Prime 19) := ⟨by norm_num⟩
  exact hexI_congr (by norm_num) (paleyI_hex 19 (by norm_num))

theorem hex4_7 : HexI (4 * 7) := by
  have : Fact (Nat.Prime 13) := ⟨by norm_num⟩
  exact hexI_congr (by norm_num) (paleyII_hex 13 (by norm_num))

theorem hex4_9 : HexI (4 * 9) := by
  have : Fact (Nat.Prime 17) := ⟨by norm_num⟩
  exact hexI_congr (by norm_num) (paleyII_hex 17 (by norm_num))

theorem hex4_11 : HexI (4 * 11) := by
  have : Fact (Nat.Prime 43) := ⟨by norm_num⟩
  exact hexI_congr (by norm_num) (paleyI_hex 43 (by norm_num))

/-- Goethals–Seidel, data: will. -/
theorem hex4_13 : HexI (4 * 13) := hexI_congr (by norm_num) (gs_hex 12
  720
  7470
  3804
  3804
  (by decide +kernel))

theorem hex4_15 : HexI (4 * 15) := by
  have : Fact (Nat.Prime 59) := ⟨by norm_num⟩
  exact hexI_congr (by norm_num) (paleyI_hex 59 (by norm_num))

theorem hex4_17 : HexI (4 * 17) := by
  have : Fact (Nat.Prime 67) := ⟨by norm_num⟩
  exact hexI_congr (by norm_num) (paleyI_hex 67 (by norm_num))

theorem hex4_19 : HexI (4 * 19) := by
  have : Fact (Nat.Prime 37) := ⟨by norm_num⟩
  exact hexI_congr (by norm_num) (paleyII_hex 37 (by norm_num))

theorem hex4_21 : HexI (4 * 21) := by
  have : Fact (Nat.Prime 83) := ⟨by norm_num⟩
  exact hexI_congr (by norm_num) (paleyI_hex 83 (by norm_num))

/-- Goethals–Seidel, data: will. -/
theorem hex4_23 : HexI (4 * 23) := hexI_congr (by norm_num) (gs_hex 22
  3909084
  4817298
  1877304
  1146504
  (by decide +kernel))

/-- Goethals–Seidel, data: will. -/
theorem hex4_25 : HexI (4 * 25) := hexI_congr (by norm_num) (gs_hex 24
  2805072
  14287212
  7090392
  23266074
  (by decide +kernel))

theorem hex4_27 : HexI (4 * 27) := by
  have : Fact (Nat.Prime 107) := ⟨by norm_num⟩
  exact hexI_congr (by norm_num) (paleyI_hex 107 (by norm_num))

/-- Goethals–Seidel, data: will. -/
theorem hex4_29 : HexI (4 * 29) := hexI_congr (by norm_num) (gs_hex 28
  120974136
  389286714
  39587472
  228725100
  (by decide +kernel))

theorem hex4_31 : HexI (4 * 31) := by
  have : Fact (Nat.Prime 61) := ⟨by norm_num⟩
  exact hexI_congr (by norm_num) (paleyII_hex 61 (by norm_num))

theorem hex4_33 : HexI (4 * 33) := by
  have : Fact (Nat.Prime 131) := ⟨by norm_num⟩
  exact hexI_congr (by norm_num) (paleyI_hex 131 (by norm_num))

theorem hex4_35 : HexI (4 * 35) := by
  have : Fact (Nat.Prime 139) := ⟨by norm_num⟩
  exact hexI_congr (by norm_num) (paleyI_hex 139 (by norm_num))

theorem hex4_37 : HexI (4 * 37) := by
  have : Fact (Nat.Prime 73) := ⟨by norm_num⟩
  exact hexI_congr (by norm_num) (paleyII_hex 73 (by norm_num))

/-- Goethals–Seidel, data: skew. -/
theorem hex4_39 : HexI (4 * 39) := hexI_congr (by norm_num) (gs_hex 38
  499333381584
  344751321154
  473212019336
  468701397222
  (by decide +kernel))

theorem hex4_41 : HexI (4 * 41) := by
  have : Fact (Nat.Prime 163) := ⟨by norm_num⟩
  exact hexI_congr (by norm_num) (paleyI_hex 163 (by norm_num))

/-- Goethals–Seidel, data: skew. -/
theorem hex4_43 : HexI (4 * 43) := hexI_congr (by norm_num) (gs_hex 42
  5117392458156
  5117392458156
  3755977809018
  1395688473793
  (by decide +kernel))

theorem hex4_45 : HexI (4 * 45) := by
  have : Fact (Nat.Prime 179) := ⟨by norm_num⟩
  exact hexI_congr (by norm_num) (paleyI_hex 179 (by norm_num))

/-- Goethals–Seidel, data: tseq. -/
theorem hex4_47 : HexI (4 * 47) := hexI_congr (by norm_num) (gs_hex 46
  65168284714926
  52206268122953
  65168286021713
  88531205687113
  (by decide +kernel))

theorem hex4_49 : HexI (4 * 49) := by
  have : Fact (Nat.Prime 97) := ⟨by norm_num⟩
  exact hexI_congr (by norm_num) (paleyII_hex 97 (by norm_num))

theorem hex4_51 : HexI (4 * 51) := by
  have : Fact (Nat.Prime 101) := ⟨by norm_num⟩
  exact hexI_congr (by norm_num) (paleyII_hex 101 (by norm_num))

theorem hex4_53 : HexI (4 * 53) := by
  have : Fact (Nat.Prime 211) := ⟨by norm_num⟩
  exact hexI_congr (by norm_num) (paleyI_hex 211 (by norm_num))

theorem hex4_55 : HexI (4 * 55) := by
  have : Fact (Nat.Prime 109) := ⟨by norm_num⟩
  exact hexI_congr (by norm_num) (paleyII_hex 109 (by norm_num))

theorem hex4_57 : HexI (4 * 57) := by
  have : Fact (Nat.Prime 227) := ⟨by norm_num⟩
  exact hexI_congr (by norm_num) (paleyI_hex 227 (by norm_num))

/-- Goethals–Seidel, data: tseq. -/
theorem hex4_59 : HexI (4 * 59) := hexI_congr (by norm_num) (gs_hex 58
  437091855667246112
  235746216561030177
  437091855960427487
  340714535449211937
  (by decide +kernel))

/-- Goethals–Seidel, data: will. -/
theorem hex4_61 : HexI (4 * 61) := hexI_congr (by norm_num) (gs_hex 60
  980244285659567724
  980244285659567724
  2108698770711933102
  197144238501760848
  (by decide +kernel))

theorem hex4_63 : HexI (4 * 63) := by
  have : Fact (Nat.Prime 251) := ⟨by norm_num⟩
  exact hexI_congr (by norm_num) (paleyI_hex 251 (by norm_num))

/-- Goethals–Seidel, data: skew. -/
theorem hex4_65 : HexI (4 * 65) := hexI_congr (by norm_num) (gs_hex 64
  32374889200631854576
  12701519162707093890
  784179586197400812
  6709323671786651200
  (by decide +kernel))

/-- Goethals–Seidel, data: skew. -/
theorem hex4_67 : HexI (4 * 67) := hexI_congr (by norm_num) (gs_hex 66
  61808106872519771730
  7860292854920327566
  114717466348671366736
  7339548030373285052
  (by decide +kernel))

theorem hex4_69 : HexI (4 * 69) := by
  have : Fact (Nat.Prime 137) := ⟨by norm_num⟩
  exact hexI_congr (by norm_num) (paleyII_hex 137 (by norm_num))

theorem hex4_71 : HexI (4 * 71) := by
  have : Fact (Nat.Prime 283) := ⟨by norm_num⟩
  exact hexI_congr (by norm_num) (paleyI_hex 283 (by norm_num))

/-- Goethals–Seidel, data: skew. -/
theorem hex4_73 : HexI (4 * 73) := hexI_congr (by norm_num) (gs_hex 72
  9042599403342592790176
  1715294641098217138176
  8094605636775596943008
  23389805723951640927
  (by decide +kernel))

theorem hex4_75 : HexI (4 * 75) := by
  have : Fact (Nat.Prime 149) := ⟨by norm_num⟩
  exact hexI_congr (by norm_num) (paleyII_hex 149 (by norm_num))

theorem hex4_77 : HexI (4 * 77) := by
  have : Fact (Nat.Prime 307) := ⟨by norm_num⟩
  exact hexI_congr (by norm_num) (paleyI_hex 307 (by norm_num))

theorem hex4_79 : HexI (4 * 79) := by
  have : Fact (Nat.Prime 157) := ⟨by norm_num⟩
  exact hexI_congr (by norm_num) (paleyII_hex 157 (by norm_num))

theorem hex4_81 : HexI (4 * 81) := gs2_hex 8 8
  630468148537486398168526
  1226581758506390952120905
  232077170398846333815429
  2068856789973291790370563
  (by decide +kernel)

theorem hex4_83 : HexI (4 * 83) := by
  have : Fact (Nat.Prime 331) := ⟨by norm_num⟩
  exact hexI_congr (by norm_num) (paleyI_hex 331 (by norm_num))

/-- Goethals–Seidel, data: cw5x17. -/
theorem hex4_85 : HexI (4 * 85) := hexI_congr (by norm_num) (gs_hex 84
  10567595096845848461833734
  5650498296529939301492103
  16757381391207689656606205
  2181127822973122937392765
  (by decide +kernel))

theorem hex4_87 : HexI (4 * 87) := by
  have : Fact (Nat.Prime 347) := ⟨by norm_num⟩
  exact hexI_congr (by norm_num) (paleyI_hex 347 (by norm_num))

/-- Goethals–Seidel, data: tseq. -/
theorem hex4_89 : HexI (4 * 89) := hexI_congr (by norm_num) (gs_hex 88
  113974647585430478000108224
  421700132593588082370006335
  113974647201934702312279359
  197269887432597830407146815
  (by decide +kernel))

theorem hex4_91 : HexI (4 * 91) := by
  have : Fact (Nat.Prime 181) := ⟨by norm_num⟩
  exact hexI_congr (by norm_num) (paleyII_hex 181 (by norm_num))

/-- Goethals–Seidel, data: skew. -/
theorem hex4_93 : HexI (4 * 93) := hexI_congr (by norm_num) (gs_hex 92
  2598311555733345003793503866
  3997333041610256279656339788
  9791329286632119855180460524
  5606887207705569911202946152
  (by decide +kernel))

theorem hex4_95 : HexI (4 * 95) := by
  have : Fact (Nat.Prime 379) := ⟨by norm_num⟩
  exact hexI_congr (by norm_num) (paleyI_hex 379 (by norm_num))

theorem hex4_97 : HexI (4 * 97) := by
  have : Fact (Nat.Prime 193) := ⟨by norm_num⟩
  exact hexI_congr (by norm_num) (paleyII_hex 193 (by norm_num))

theorem hex4_99 : HexI (4 * 99) := by
  have : Fact (Nat.Prime 197) := ⟨by norm_num⟩
  exact hexI_congr (by norm_num) (paleyII_hex 197 (by norm_num))

/-- Goethals–Seidel, data: skew. -/
theorem hex4_103 : HexI (4 * 103) := hexI_congr (by norm_num) (gs_hex 102
  7794179692703159759099620882872
  443043060329971472411804821444
  7882672018541227811069763415694
  9021438811519065711278011865630
  (by decide +kernel))

theorem hex4_105 : HexI (4 * 105) := by
  have : Fact (Nat.Prime 419) := ⟨by norm_num⟩
  exact hexI_congr (by norm_num) (paleyI_hex 419 (by norm_num))

/-- Goethals–Seidel, data: tseq. -/
theorem hex4_107 : HexI (4 * 107) := hexI_congr (by norm_num) (gs_hex 106
  119248894060070021979558352815746
  63299323569783054129665832089981
  119248894061210615305632627521917
  98959953258289715935848051472765
  (by decide +kernel))

/-- Goethals–Seidel, data: skew. -/
theorem hex4_109 : HexI (4 * 109) := hexI_congr (by norm_num) (gs_hex 108
  123459675551352000816092535023078
  133430319674679116411051224115224
  441819033027258125526959733944914
  230730465453557616443923388797274
  (by decide +kernel))

theorem hex4_111 : HexI (4 * 111) := by
  have : Fact (Nat.Prime 443) := ⟨by norm_num⟩
  exact hexI_congr (by norm_num) (paleyI_hex 443 (by norm_num))

/-- Goethals–Seidel, data: skew. -/
theorem hex4_113 : HexI (4 * 113) := hexI_congr (by norm_num) (gs_hex 112
  3344197861305871323060357997126506
  7986437295470406459173996972920784
  4990453293018079577299979729491238
  9291803127227728181044594075947476
  (by decide +kernel))

theorem hex4_115 : HexI (4 * 115) := by
  have : Fact (Nat.Prime 229) := ⟨by norm_num⟩
  exact hexI_congr (by norm_num) (paleyII_hex 229 (by norm_num))

theorem hex4_117 : HexI (4 * 117) := by
  have : Fact (Nat.Prime 467) := ⟨by norm_num⟩
  exact hexI_congr (by norm_num) (paleyI_hex 467 (by norm_num))

/-- Goethals–Seidel, data: cw7x17. -/
theorem hex4_119 : HexI (4 * 119) := hexI_congr (by norm_num) (gs_hex 118
  359802979893708438310212668804752794
  404230419027649635635704678547092151
  643261204488558214325666905744822693
  599442256243051743344440642480621193
  (by decide +kernel))

theorem hex4_121 : HexI (4 * 121) := by
  have : Fact (Nat.Prime 241) := ⟨by norm_num⟩
  exact hexI_congr (by norm_num) (paleyII_hex 241 (by norm_num))

theorem hex4_123 : HexI (4 * 123) := by
  have : Fact (Nat.Prime 491) := ⟨by norm_num⟩
  exact hexI_congr (by norm_num) (paleyI_hex 491 (by norm_num))

theorem hex4_125 : HexI (4 * 125) := by
  have : Fact (Nat.Prime 499) := ⟨by norm_num⟩
  exact hexI_congr (by norm_num) (paleyI_hex 499 (by norm_num))

/-- Goethals–Seidel, data: skew. -/
theorem hex4_127 : HexI (4 * 127) := hexI_congr (by norm_num) (gs_hex 126
  30790515292689894969866990722818747158
  164553985446118980021128635465599674774
  170031998885396078193270883716963993398
  144750698989741433121040559526395792544
  (by decide +kernel))

theorem hex4_129 : HexI (4 * 129) := by
  have : Fact (Nat.Prime 257) := ⟨by norm_num⟩
  exact hexI_congr (by norm_num) (paleyII_hex 257 (by norm_num))

theorem hex4_131 : HexI (4 * 131) := by
  have : Fact (Nat.Prime 523) := ⟨by norm_num⟩
  exact hexI_congr (by norm_num) (paleyI_hex 523 (by norm_num))

/-- Goethals–Seidel, data: skew. -/
theorem hex4_133 : HexI (4 * 133) := hexI_congr (by norm_num) (gs_hex 132
  7942647804560016447713734847576855692612
  6380609705683622259289542672990016437768
  1403403954254707772143955877925547868370
  8097323306954330336317689630496586843542
  (by decide +kernel))

theorem hex4_135 : HexI (4 * 135) := by
  have : Fact (Nat.Prime 269) := ⟨by norm_num⟩
  exact hexI_congr (by norm_num) (paleyII_hex 269 (by norm_num))

theorem hex4_137 : HexI (4 * 137) := by
  have : Fact (Nat.Prime 547) := ⟨by norm_num⟩
  exact hexI_congr (by norm_num) (paleyI_hex 547 (by norm_num))

theorem hex4_139 : HexI (4 * 139) := by
  have : Fact (Nat.Prime 277) := ⟨by norm_num⟩
  exact hexI_congr (by norm_num) (paleyII_hex 277 (by norm_num))

theorem hex4_141 : HexI (4 * 141) := by
  have : Fact (Nat.Prime 563) := ⟨by norm_num⟩
  exact hexI_congr (by norm_num) (paleyI_hex 563 (by norm_num))

theorem hex4_143 : HexI (4 * 143) := by
  have : Fact (Nat.Prime 571) := ⟨by norm_num⟩
  exact hexI_congr (by norm_num) (paleyI_hex 571 (by norm_num))

/-- Goethals–Seidel, data: skew. -/
theorem hex4_145 : HexI (4 * 145) := hexI_congr (by norm_num) (gs_hex 144
  23579831101534759513072580534518622313392700
  3823609839665890011129782742117883110984718
  35242117700903372516339130846979766794085200
  17993423883908222951078322874238521148600676
  (by decide +kernel))

theorem hex4_147 : HexI (4 * 147) := by
  have : Fact (Nat.Prime 587) := ⟨by norm_num⟩
  exact hexI_congr (by norm_num) (paleyI_hex 587 (by norm_num))

/-- Goethals–Seidel, data: skew. -/
theorem hex4_151 : HexI (4 * 151) := hexI_congr (by norm_num) (gs_hex 150
  1144267159190969317896070117456432421177003314
  720663383830420833255545847144864618580641812
  2486594102399190239895960764092477504680166398
  1846614654125591630493096650747539574244785736
  (by decide +kernel))

/-- Goethals–Seidel, data: cw9x17. -/
theorem hex4_153 : HexI (4 * 153) := hexI_congr (by norm_num) (gs_hex 152
  4099740666797090884077736836929091454289979290
  5011548844889436015451228469271824981868088395
  605884980572856658443354005787406617452730057
  1700890339459985114906209909947831493758352665
  (by decide +kernel))

theorem hex4_155 : HexI (4 * 155) := by
  have : Fact (Nat.Prime 619) := ⟨by norm_num⟩
  exact hexI_congr (by norm_num) (paleyI_hex 619 (by norm_num))

theorem hex4_157 : HexI (4 * 157) := by
  have : Fact (Nat.Prime 313) := ⟨by norm_num⟩
  exact hexI_congr (by norm_num) (paleyII_hex 313 (by norm_num))

theorem hex4_159 : HexI (4 * 159) := by
  have : Fact (Nat.Prime 317) := ⟨by norm_num⟩
  exact hexI_congr (by norm_num) (paleyII_hex 317 (by norm_num))

theorem hex4_161 : HexI (4 * 161) := by
  have : Fact (Nat.Prime 643) := ⟨by norm_num⟩
  exact hexI_congr (by norm_num) (paleyI_hex 643 (by norm_num))

/-- Goethals–Seidel, data: skew. -/
theorem hex4_163 : HexI (4 * 163) := hexI_congr (by norm_num) (gs_hex 162
  1664259177461776699951958694591402940219036787638
  6216067312173878904540994703258213788490468754946
  10385147151030179519217636758261853422182935052370
  3461422350741554151044530629799274536264528082016
  (by decide +kernel))

theorem hex4_165 : HexI (4 * 165) := by
  have : Fact (Nat.Prime 659) := ⟨by norm_num⟩
  exact hexI_congr (by norm_num) (paleyI_hex 659 (by norm_num))

theorem odd_hex (k : ℕ) (hk : k ≤ 166) (hodd : Odd k) : HexI (4 * k) := by
  interval_cases k <;> first | exact absurd hodd (by decide) | exact hex4_101 | exact hex4_149 | exact hex4_1 | exact hex4_3 | exact hex4_5 | exact hex4_7 | exact hex4_9 | exact hex4_11 | exact hex4_13 | exact hex4_15 | exact hex4_17 | exact hex4_19 | exact hex4_21 | exact hex4_23 | exact hex4_25 | exact hex4_27 | exact hex4_29 | exact hex4_31 | exact hex4_33 | exact hex4_35 | exact hex4_37 | exact hex4_39 | exact hex4_41 | exact hex4_43 | exact hex4_45 | exact hex4_47 | exact hex4_49 | exact hex4_51 | exact hex4_53 | exact hex4_55 | exact hex4_57 | exact hex4_59 | exact hex4_61 | exact hex4_63 | exact hex4_65 | exact hex4_67 | exact hex4_69 | exact hex4_71 | exact hex4_73 | exact hex4_75 | exact hex4_77 | exact hex4_79 | exact hex4_81 | exact hex4_83 | exact hex4_85 | exact hex4_87 | exact hex4_89 | exact hex4_91 | exact hex4_93 | exact hex4_95 | exact hex4_97 | exact hex4_99 | exact hex4_103 | exact hex4_105 | exact hex4_107 | exact hex4_109 | exact hex4_111 | exact hex4_113 | exact hex4_115 | exact hex4_117 | exact hex4_119 | exact hex4_121 | exact hex4_123 | exact hex4_125 | exact hex4_127 | exact hex4_129 | exact hex4_131 | exact hex4_133 | exact hex4_135 | exact hex4_137 | exact hex4_139 | exact hex4_141 | exact hex4_143 | exact hex4_145 | exact hex4_147 | exact hex4_151 | exact hex4_153 | exact hex4_155 | exact hex4_157 | exact hex4_159 | exact hex4_161 | exact hex4_163 | exact hex4_165

theorem hex0 : HexI 0 :=
  ⟨0, fun i => Fin.elim0 i, by ext i; exact Fin.elim0 i⟩

theorem hex_all :
    ∀ k, k ≤ 166 → HexI (4 * k) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    rcases Nat.even_or_odd k with ⟨j, rfl⟩ | hodd
    · rcases Nat.eq_zero_or_pos j with rfl | hj
      · exact hex0
      · exact hexI_congr (by ring) (hexI_double (ih j (by omega) (by omega)))
    · exact odd_hex k hk hodd

theorem first_cases :
    668 ≤ Hadamard.hadamardConstant := by
  unfold Hadamard.hadamardConstant
  refine le_iInf₂ (fun k hk => ?_)
  by_cases hk' : k ≤ 166
  · exact absurd (isHadamard_of_hexI (hex_all k hk')) hk
  · have : (668 : ℕ) ≤ 4 * k := by omega
    exact_mod_cast this

end OMAHad

theorem OMA.solution :
    668 ≤ Hadamard.hadamardConstant :=
  OMAHad.first_cases
