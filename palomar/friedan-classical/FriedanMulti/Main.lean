/-
Copyright 2026 Ming-Chih Kao. Licensed under the Apache License, Version 2.0;
see the LICENSE file at the root of this repository.
-/
module

public import FriedanMulti.Statement
public import FriedanMulti.Induction

/-! Port: copied from `quantum-lean/FriedanMulti/Main.lean` of github.com/koolkao/friedan-entropy-inequality (commit 0f4ba65dc126f59e7158fbcbc01548baa78cf21d), the source repository's own Lean v4.36 port of `FriedanMulti/Main.lean` (it spells out one continuity proof), and put into the module system (`module` header, `public import`, public section; the import `FriedanQ.Classical` is replaced by `FriedanEntropy.Proof`, which has the same proof body). -/

@[expose] public section

/-!
# Theorem M: positive vectors (log coordinates), then zero entries by continuity
-/

open Real Finset Filter Topology

namespace FriedanMulti

variable {n m : ℕ}

theorem pos_case [NeZero n] (X : Fin m → Fin n → ℝ) (hX : ∀ j i, 0 < X j i)
    (hXs : ∀ j, ∑ i, X j i = 1) (a : Fin m → ℝ) (ha0 : ∀ j, 0 ≤ a j) (has : ∑ j, a j = 1) :
    (∑ i, ∏ j, X j i ^ a j) ^ 2 *
        entropy (fun i => (∏ j, X j i ^ a j) / ∑ k, ∏ j, X j k ^ a j) ≤
      ∑ j, a j * entropy (X j) := by
  let x : Fin m → Fin n → ℝ := fun j i => Real.log (X j i)
  have hz : ∀ i, ∏ j, X j i ^ a j = exp (comb x a i) := by
    intro i
    unfold comb
    rw [Real.exp_sum]
    refine Finset.prod_congr rfl (fun j _ => ?_)
    rw [Real.rpow_def_of_pos (hX j i), mul_comm]
  have hexp : ∀ j i, exp (x j i) = X j i := fun j i => Real.exp_log (hX j i)
  have hS : ∀ j, Sx (x j) = 1 := fun j => by
    unfold Sx
    simp only [hexp]
    exact hXs j
  have hH : ∀ j, entropy (X j) = gg (x j) := by
    intro j
    rw [← ent_one (x j) (hS j)]
    unfold entropy
    simp only [hexp]
  have hL : (∑ i, ∏ j, X j i ^ a j) ^ 2 *
      entropy (fun i => (∏ j, X j i ^ a j) / ∑ k, ∏ j, X j k ^ a j) = gg (comb x a) := by
    simp only [hz]
    rw [← ent_exp (comb x a)]
    rfl
  rw [hL]
  simp only [hH]
  exact log_thm x hS a ha0 has

/-- **Theorem M** (Friedan's inequality for `m` distributions). -/
theorem theoremM : TheoremM := by
  intro n m X hX0 hXs a ha0 has hK
  have hn : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h; simp at hK
    · exact h
  have : NeZero n := ⟨hn.ne'⟩
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  let Xe : ℝ → Fin m → Fin n → ℝ := fun e j i => (1 - e) * X j i + e / n
  have hpos : ∀ e ∈ Set.Ioo (0 : ℝ) 1, ∀ j i, 0 < Xe e j i := by
    intro e he j i
    have := mul_nonneg (by linarith [he.2] : (0 : ℝ) ≤ 1 - e) (hX0 j i)
    have := div_pos he.1 hn'
    simp only [Xe]
    linarith
  have hsum : ∀ e : ℝ, ∀ j, ∑ i, Xe e j i = 1 := by
    intro e j
    simp only [Xe]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, hXs j, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    field_simp
    ring
  let L : ℝ → ℝ := fun e => (∑ i, ∏ j, Xe e j i ^ a j) ^ 2 *
    entropy (fun i => (∏ j, Xe e j i ^ a j) / ∑ k, ∏ j, Xe e j k ^ a j)
  let R : ℝ → ℝ := fun e => ∑ j, a j * entropy (Xe e j)
  have hLR : ∀ e ∈ Set.Ioo (0 : ℝ) 1, L e ≤ R e :=
    fun e he => pos_case (Xe e) (hpos e he) (hsum e) a ha0 has
  have h0 : Xe 0 = X := by funext j i; simp [Xe]
  have crp : ∀ q : ℝ, 0 ≤ q → Continuous (fun x : ℝ => x ^ q) :=
    fun q hq => continuous_iff_continuousAt.2 (fun x => Real.continuousAt_rpow_const x q (Or.inr hq))
  have cX : ∀ j i, Continuous (fun e => Xe e j i) := fun j i => by simp only [Xe]; fun_prop
  have cz : ∀ i, Continuous (fun e => ∏ j, Xe e j i ^ a j) :=
    fun i => continuous_finsetProd _ (fun j _ => (crp (a j) (ha0 j)).comp (cX j i))
  have cK : Continuous (fun e => ∑ i, ∏ j, Xe e j i ^ a j) :=
    continuous_finsetSum _ (fun i _ => cz i)
  have hK0 : (∑ i, ∏ j, Xe 0 j i ^ a j) ≠ 0 := by rw [h0]; exact hK.ne'
  have cE : ContinuousAt
      (fun e => entropy (fun i => (∏ j, Xe e j i ^ a j) / ∑ k, ∏ j, Xe e j k ^ a j)) 0 := by
    unfold entropy
    exact tendsto_finsetSum _ (fun i _ =>
      Real.continuous_negMulLog.continuousAt.comp ((cz i).continuousAt.div cK.continuousAt hK0))
  have cL : ContinuousAt L 0 := (cK.pow 2).continuousAt.mul cE
  have cR : Continuous R := by
    show Continuous (fun e => ∑ j, a j * ∑ i, Real.negMulLog (Xe e j i))
    refine continuous_finsetSum univ (f := fun j e => a j * ∑ i, Real.negMulLog (Xe e j i))
      (fun j _ => ?_)
    refine continuous_const.mul (continuous_finsetSum univ
      (f := fun i e => Real.negMulLog (Xe e j i)) (fun i _ => ?_))
    exact Real.continuous_negMulLog.comp (cX j i)
  have hcont : ContinuousAt (fun e => R e - L e) 0 := cR.continuousAt.sub cL
  have hlim := hcont.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
  have := ge_of_tendsto hlim (Filter.mem_of_superset
    (Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)) (fun e he => sub_nonneg.2 (hLR e he)))
  have h' : L 0 ≤ R 0 := sub_nonneg.1 this
  simp only [L, R, h0] at h'
  exact h'

end FriedanMulti

end
