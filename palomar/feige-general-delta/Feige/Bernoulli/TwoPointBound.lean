module

public import Feige.Bernoulli.Thm21

/- Port (Palomar entry): `module` header, `public import`s and a public section added for the module system; otherwise unchanged from github.com/koolkao/feige-lean at commit 7da24abf1619706bf4f705bb24aa4d00bc63b49f. -/

@[expose] public section

/-!
# Bernoullification for mean-one two-point laws (Ling §2.2, equal means)

Coordinate `i` takes value `xᵢ` with probability `1 - pᵢ` and `yᵢ` with probability `pᵢ`, where
`0 ≤ xᵢ ≤ yᵢ`, `pᵢ (yᵢ - xᵢ) = 1 - xᵢ` (mean one) and `0 ≤ pᵢ < 1`.  Atoms at one are
`x = y = 1`, `p = 0`.  With `Λ = δ + ∑ (1 - xᵢ)`, `wᵢ = (yᵢ - xᵢ)/Λ`, `a = 1/Λ`,
the event `∑ Yᵢ < n + δ` is `T < 1`, `wᵢ pᵢ = (1-xᵢ)/Λ ≤ a`, and `d = 1 - E[T] = δ/Λ`,
so `d/(d+a) = δ/(1+δ)`.
-/

open Finset Real

namespace Samuels

theorem twoPoint_bound {n : ℕ} (x y p : Fin n → ℝ) {δ : ℝ} (hδ : 0 < δ)
    (hx0 : ∀ i, 0 ≤ x i) (hxy : ∀ i, x i ≤ y i) (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i < 1)
    (hpxy : ∀ i, p i * (y i - x i) = 1 - x i) :
    min (δ / (1 + δ)) (exp (-1)) ≤
      Ex p univ (fun S => if ∑ i, x i + ∑ i ∈ S, (y i - x i) < n + δ then 1 else 0) := by
  have hx1 : ∀ i, 0 ≤ 1 - x i := fun i => by
    rw [← hpxy i]; exact mul_nonneg (hp0 i) (sub_nonneg.mpr (hxy i))
  set Λ := δ + ∑ i, (1 - x i) with hΛ
  have hΛpos : 0 < Λ := by
    have : 0 ≤ ∑ i, (1 - x i) := Finset.sum_nonneg fun i _ => hx1 i
    linarith
  set w : Fin n → ℝ := fun i => (y i - x i) / Λ with hw
  have hw0 : ∀ i ∈ (univ : Finset (Fin n)), 0 ≤ w i :=
    fun i _ => div_nonneg (sub_nonneg.mpr (hxy i)) hΛpos.le
  have hwp : ∀ i, w i * p i = (1 - x i) / Λ := fun i => by
    simp only [hw]; rw [← hpxy i]; ring
  have hwa : ∀ i ∈ (univ : Finset (Fin n)), w i * p i ≤ 1 / Λ := fun i _ => by
    rw [hwp i]
    exact div_le_div_of_nonneg_right (by linarith [hx0 i]) hΛpos.le
  have hE : E p w univ = (∑ i, (1 - x i)) / Λ := by
    simp only [E, hwp, Finset.sum_div]
  have hd : 1 - E p w univ = δ / Λ := by
    rw [hE]; field_simp; rw [hΛ]; ring
  have hmain := bernoulli_equal_bound p w univ (fun i _ => hp0 i) (fun i _ => hp1 i) hw0
    (one_div_pos.mpr hΛpos) hwa (by rw [hd]; exact div_pos hδ hΛpos)
  have hratio : (1 - E p w univ) / ((1 - E p w univ) + 1 / Λ) = δ / (1 + δ) := by
    rw [hd]; field_simp; ring
  rw [hratio] at hmain
  refine hmain.trans (le_of_eq ?_)
  unfold Z
  apply Ex_congr
  intro S _
  have hsumx : ∑ i, x i = n - ∑ i, (1 - x i) := by
    simp [Finset.sum_sub_distrib]
  have hiff : T w S < 1 ↔ ∑ i, x i + ∑ i ∈ S, (y i - x i) < n + δ := by
    simp only [T, hw, ← Finset.sum_div]
    rw [div_lt_one hΛpos, hsumx, hΛ]
    constructor <;> intro h <;> linarith
  by_cases h : T w S < 1
  · rw [if_pos h, if_pos (hiff.mp h)]
  · rw [if_neg h, if_neg (fun h' => h (hiff.mpr h'))]

end Samuels

end
