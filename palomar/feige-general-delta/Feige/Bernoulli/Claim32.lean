module

public import Feige.Bernoulli.Moments
public import Feige.Bernoulli.Step

/- Port (Palomar entry): `module` header, `public import`s and a public section added for the module system; otherwise unchanged from github.com/koolkao/feige-lean at commit 7da24abf1619706bf4f705bb24aa4d00bc63b49f. -/

@[expose] public section

/-!
# Ling's Claims 3.1 and 3.2 (interior case, `0 ≤ pᵢ < 1`)

`R s = 1 - E[T | T < 1]` and `L s = E[T] - E[T | T < 1]`.

* `exists_index`: some coordinate `i` has `E[T₋ᵢ | T₋ᵢ < 1] ≤ E[T | T < 1]` (this is
  `Cov(T, Bᵢ | T < 1) ≥ 0` in Ling's proof).  Following a suggestion of Fable, we take `i` with
  `wᵢ Dᵢ ≥ 0` where `∑ wᵢ Dᵢ = Var(T | T<1) · P(T<1) ≥ 0`, and treat `wᵢ = 0` directly.
* `claim32`: the Bellman induction.
-/

open Finset Real

namespace Samuels

variable {ι : Type*} [DecidableEq ι] {p w : ι → ℝ}

/-- `R = 1 - E[T | T < 1]`. -/
noncomputable def Rv (p w : ι → ℝ) (s : Finset ι) : ℝ := 1 - M p w s 1 / Z p w s 1

/-- `L = E[T] - E[T | T < 1]`. -/
noncomputable def Lv (p w : ι → ℝ) (s : Finset ι) : ℝ := E p w s - M p w s 1 / Z p w s 1

lemma exists_index {s : Finset ι} (hs : s.Nonempty) (hp0 : ∀ i ∈ s, 0 ≤ p i)
    (hp1 : ∀ i ∈ s, p i < 1) (hw : ∀ i ∈ s, 0 ≤ w i) :
    ∃ i ∈ s, M p w (s.erase i) 1 ≤ M p w s 1 / Z p w s 1 * Z p w (s.erase i) 1 := by
  have hp1' : ∀ i ∈ s, p i ≤ 1 := fun i hi => (hp1 i hi).le
  have hZ : 0 < Z p w s 1 := Z_pos hp0 hp1 hw one_pos
  set m := M p w s 1 / Z p w s 1 with hm
  have hmZ : m * Z p w s 1 = M p w s 1 := by rw [hm]; field_simp
  -- `Dᵢ = E[Bᵢ T 1{T<1}] - m E[Bᵢ 1{T<1}]`
  let D : ι → ℝ := fun i =>
    p i * (M p w (s.erase i) (1 - w i) + w i * Z p w (s.erase i) (1 - w i)) -
      m * (p i * Z p w (s.erase i) (1 - w i))
  have hsum : 0 ≤ ∑ i ∈ s, w i * D i := by
    have hQ := Q_eq_sum (p := p) (w := w) s 1
    have hMs := M_eq_sum (p := p) (w := w) s 1
    have hB : ∀ i ∈ s, Ex p s (fun S => if i ∈ S then (if T w S < 1 then T w S else 0) else 0) =
        p i * (M p w (s.erase i) (1 - w i) + w i * Z p w (s.erase i) (1 - w i)) := by
      intro i hi
      conv_lhs => rw [← insert_erase hi]
      exact Ex_mem_T (notMem_erase i s) 1
    have hA : ∀ i ∈ s, Ex p s (fun S => if i ∈ S then (if T w S < 1 then 1 else 0) else 0) =
        p i * Z p w (s.erase i) (1 - w i) := by
      intro i hi
      conv_lhs => rw [← insert_erase hi]
      exact Ex_mem_ind (notMem_erase i s) 1
    rw [Finset.sum_congr rfl (fun i hi => by rw [hB i hi])] at hQ
    rw [Finset.sum_congr rfl (fun i hi => by rw [hA i hi])] at hMs
    have hcs := M_sq_le hp0 hp1' 1 hZ (w := w)
    have : ∑ i ∈ s, w i * D i = Q p w s 1 - m * M p w s 1 := by
      simp only [D, mul_sub, Finset.sum_sub_distrib]
      rw [hQ, hMs, Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl; intro i _; ring
    rw [this]
    have : m * M p w s 1 = M p w s 1 ^ 2 / Z p w s 1 := by rw [hm]; ring
    linarith
  obtain ⟨i, hi, hDi⟩ : ∃ i ∈ s, 0 ≤ w i * D i := by
    by_contra h
    push Not at h
    have := Finset.sum_lt_sum_of_nonempty hs h
    simp at this
    linarith
  refine ⟨i, hi, ?_⟩
  have his : i ∉ (s.erase i) := notMem_erase i s
  have hss : insert i (s.erase i) = s := insert_erase hi
  have hZr := Z_insert (p := p) (w := w) his 1
  have hMr := M_insert (p := p) (w := w) his 1
  rw [hss] at hZr hMr
  have hpi1 : 0 < 1 - p i := sub_pos.mpr (hp1 i hi)
  -- `Dᵢ = (1 - pᵢ)(m Z₀ - M₀)`
  have hDform : D i = (1 - p i) * (m * Z p w (s.erase i) 1 - M p w (s.erase i) 1) := by
    simp only [D]
    linear_combination -hMr + m * hZr - hmZ
  rcases (hw i hi).lt_or_eq with hwpos | hwzero
  · have : 0 ≤ D i := by
      by_contra h; push Not at h; nlinarith
    rw [hDform] at this
    nlinarith
  · -- `wᵢ = 0`: then `Z₁ = Z₀` and `M₁ = M₀`
    have hD2 : D i = p i * (M p w (s.erase i) 1 - m * Z p w (s.erase i) 1) := by
      simp only [D, ← hwzero, sub_zero]; ring
    have : (m * Z p w (s.erase i) 1 - M p w (s.erase i) 1) = 0 := by
      have h := hDform.symm.trans hD2
      linear_combination h
    linarith

/-- **Claim 3.2** (Bellman induction). -/
theorem claim32 (p w a : ι → ℝ) (s : Finset ι) (hp0 : ∀ i ∈ s, 0 ≤ p i)
    (hp1 : ∀ i ∈ s, p i < 1) (hw : ∀ i ∈ s, 0 ≤ w i) (hwa : ∀ i ∈ s, w i * p i ≤ a i)
    (ha : ∀ i ∈ s, 0 < a i) (hR : ∀ i ∈ s, a i < Rv p w s) :
    ∃ ℓ : ι → ℝ, (∀ i ∈ s, 0 ≤ ℓ i ∧ ℓ i ≤ a i) ∧ ∑ i ∈ s, ℓ i = Lv p w s ∧
      -log (Z p w s 1) ≤ ∑ i ∈ s, ℓ i / a i * log (Rv p w s / (Rv p w s - a i)) := by
  induction s using Finset.strongInduction with
  | H s ih =>
  rcases s.eq_empty_or_nonempty with rfl | hs
  · refine ⟨fun _ => 0, by simp, ?_, ?_⟩
    · simp [Lv, E, M, Z, T]
    · simp [Z, T]
  have hp1' : ∀ i ∈ s, p i ≤ 1 := fun i hi => (hp1 i hi).le
  obtain ⟨i, hi, hchoice⟩ := exists_index hs hp0 hp1 hw
  set s' := s.erase i with hs'
  have his : i ∉ s' := notMem_erase i s
  have hss : insert i s' = s := insert_erase hi
  have hsub : s' ⊆ s := erase_subset i s
  have hp0' : ∀ j ∈ s', 0 ≤ p j := fun j hj => hp0 j (hsub hj)
  have hp1'' : ∀ j ∈ s', p j < 1 := fun j hj => hp1 j (hsub hj)
  have hw' : ∀ j ∈ s', 0 ≤ w j := fun j hj => hw j (hsub hj)
  have hZ : 0 < Z p w s 1 := Z_pos hp0 hp1 hw one_pos
  have hZ0 : 0 < Z p w s' 1 := Z_pos hp0' hp1'' hw' one_pos
  set m := M p w s 1 / Z p w s 1 with hm
  set m0 := M p w s' 1 / Z p w s' 1 with hm0
  have hmm0 : m0 ≤ m := by rw [hm0, div_le_iff₀ hZ0]; exact hchoice
  have hRR : Rv p w s ≤ Rv p w s' := by simp only [Rv]; linarith
  -- induction hypothesis on `s'`
  obtain ⟨ℓ', hℓ'b, hℓ'sum, hℓ'log⟩ := ih s' (erase_ssubset hi) hp0' hp1'' hw'
    (fun j hj => hwa j (hsub hj)) (fun j hj => ha j (hsub hj))
    (fun j hj => lt_of_lt_of_le (hR j (hsub hj)) hRR)
  -- the real step
  have hZr := Z_insert (p := p) (w := w) his 1
  have hMr := M_insert (p := p) (w := w) his 1
  rw [hss] at hZr hMr
  have hZ1 := Z_nonneg (w := w) hp0' (fun j hj => (hp1'' j hj).le) (1 - w i)
  have hZ1le := Z_mono (w := w) hp0' (fun j hj => (hp1'' j hj).le)
    (show 1 - w i ≤ 1 by linarith [hw i hi])
  have hMsub := M_sub_ge (w := w) hp0' (fun j hj => (hp1'' j hj).le)
    (show 1 - w i ≤ 1 by linarith [hw i hi])
  have hmZ : m * ((1 - p i) * Z p w s' 1 + p i * Z p w s' (1 - w i)) =
      (1 - p i) * M p w s' 1 + p i * (M p w s' (1 - w i) + w i * Z p w s' (1 - w i)) := by
    rw [← hZr, ← hMr, hm]; field_simp
  obtain ⟨hΔ0, hΔa, hlog⟩ := claim32_step hZ0 hZ1 hZ1le (hp0 i hi) (hp1 i hi) hMsub hmZ
    hchoice (hwa i hi) (ha i hi) (hR i hi)
  set Δ := w i * p i - (m - m0) with hΔ
  have hRdef : Rv p w s = 1 - m := rfl
  rw [← hZr, ← hRdef] at hlog
  -- assemble
  refine ⟨Function.update ℓ' i Δ, ?_, ?_, ?_⟩
  · intro j hj
    by_cases hji : j = i
    · subst hji; simp [hΔ0, hΔa]
    · rw [Function.update_of_ne hji]
      exact hℓ'b j (mem_erase.mpr ⟨hji, hj⟩)
  · have hE : E p w s = E p w s' + w i * p i := by
      rw [← hss, E, E, Finset.sum_insert his]; ring
    rw [← hss, Finset.sum_insert his, Function.update_self,
      Finset.sum_congr rfl (fun j hj => Function.update_of_ne (ne_of_mem_erase hj) Δ ℓ'),
      hℓ'sum, hss]
    simp only [Lv]
    rw [hE, hΔ, hm, hm0]
    ring
  · rw [← hss, Finset.sum_insert his, Function.update_self,
      Finset.sum_congr rfl (fun j hj => by rw [Function.update_of_ne (ne_of_mem_erase hj) Δ ℓ'])]
    rw [hss]
    have hmono : ∑ j ∈ s', ℓ' j / a j * log (Rv p w s' / (Rv p w s' - a j)) ≤
        ∑ j ∈ s', ℓ' j / a j * log (Rv p w s / (Rv p w s - a j)) := by
      apply Finset.sum_le_sum
      intro j hj
      have haj := ha j (hsub hj)
      have hRj := hR j (hsub hj)
      apply mul_le_mul_of_nonneg_left _ (div_nonneg (hℓ'b j hj).1 haj.le)
      apply log_le_log
      · apply div_pos <;> linarith
      · rw [div_le_div_iff₀ (by linarith) (by linarith)]
        nlinarith
    linarith

end Samuels

end
