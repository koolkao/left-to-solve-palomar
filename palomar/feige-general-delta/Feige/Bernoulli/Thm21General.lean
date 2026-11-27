module

public import Feige.Bernoulli.Claim32
public import Feige.Calculus.Prop51

/- Port (Palomar entry): `module` header, `public import`s and a public section added for the module system; otherwise unchanged from github.com/koolkao/feige-lean at commit 7da24abf1619706bf4f705bb24aa4d00bc63b49f. -/

@[expose] public section

/-!
# Ling's Theorem 2.1 in full generality (sorted, unequal bounds `aᵢ`)

`P(T < 1) ≥ min_{i ∈ s} ∏_{j ∈ s, j ≥ i} (1 - aⱼ/(d + Cᵢ))`, `Cᵢ = ∑_{j ∈ s, j ≥ i} aⱼ`,
stated as `∃ i ∈ s, term i ≤ P(T < 1)`.

* Claim 3.1 handles `L ≤ a_max`.
* Otherwise Claim 3.2, the rearrangement Claim 3.3 (`claim33`, valid for every `i`), and
  Prop. 5.1 (`prop51`) on `[C_{>i}, C_{≥i}]` for the largest `i` with `L ≤ C_{≥i}`.
Everything is done with logarithms; no real powers (suggestion of Fable).
-/

open Finset Real

namespace Samuels

variable {ι : Type*} [LinearOrder ι]

/-- `C_{≥ i} = ∑_{j ∈ s, i ≤ j} aⱼ`. -/
def Cge (s : Finset ι) (a : ι → ℝ) (i : ι) : ℝ := ∑ j ∈ s.filter (i ≤ ·), a j

/-- `C_{> i} = ∑_{j ∈ s, i < j} aⱼ`. -/
def Cgt (s : Finset ι) (a : ι → ℝ) (i : ι) : ℝ := ∑ j ∈ s.filter (i < ·), a j

/-- The candidate bound `∏_{j ≥ i} (1 - aⱼ/(d + C_{≥ i}))`. -/
noncomputable def term (s : Finset ι) (a : ι → ℝ) (d : ℝ) (i : ι) : ℝ :=
  ∏ j ∈ s.filter (i ≤ ·), (1 - a j / (d + Cge s a i))

lemma filter_le_eq_insert {s : Finset ι} {i : ι} (hi : i ∈ s) :
    s.filter (i ≤ ·) = insert i (s.filter (i < ·)) := by
  ext j
  simp only [mem_filter, mem_insert]
  constructor
  · rintro ⟨hj, hij⟩
    rcases hij.eq_or_lt with h | h
    · exact Or.inl h.symm
    · exact Or.inr ⟨hj, h⟩
  · rintro (rfl | ⟨hj, h⟩)
    · exact ⟨hi, le_rfl⟩
    · exact ⟨hj, h.le⟩

lemma Cge_eq {s : Finset ι} {a : ι → ℝ} {i : ι} (hi : i ∈ s) : Cge s a i = a i + Cgt s a i := by
  unfold Cge Cgt
  rw [filter_le_eq_insert hi, sum_insert (by simp)]

lemma le_sum_of_mem {t : Finset ι} {a : ι → ℝ} (ha : ∀ j ∈ t, 0 ≤ a j) {j : ι} (hj : j ∈ t) :
    a j ≤ ∑ k ∈ t, a k :=
  single_le_sum ha hj

/-- `log term = ∑ (log (d + C - aⱼ) - log (d + C))`. -/
lemma log_term {s : Finset ι} {a : ι → ℝ} {d : ℝ} (hd : 0 < d) (ha : ∀ j ∈ s, 0 < a j) (i : ι) :
    0 < term s a d i ∧ log (term s a d i) =
      ∑ j ∈ s.filter (i ≤ ·), (log (d + Cge s a i - a j) - log (d + Cge s a i)) := by
  have hC : ∀ j ∈ s.filter (i ≤ ·), a j ≤ Cge s a i := fun j hj =>
    le_sum_of_mem (fun k hk => (ha k (mem_filter.mp hk).1).le) hj
  have hpos : ∀ j ∈ s.filter (i ≤ ·), 0 < 1 - a j / (d + Cge s a i) := fun j hj => by
    have := hC j hj
    rw [sub_pos, div_lt_one (by linarith [(ha j (mem_filter.mp hj).1)])]
    linarith
  refine ⟨prod_pos hpos, ?_⟩
  unfold term
  rw [log_prod (fun j hj => (hpos j hj).ne')]
  apply sum_congr rfl
  intro j hj
  have h1 := hC j hj
  have h2 := ha j (mem_filter.mp hj).1
  have hR : 0 < d + Cge s a i := by linarith
  rw [← log_div (by linarith) hR.ne']
  congr 1
  field_simp

/-- Monotonicity of `cⱼ = (log R - log (R - aⱼ))/aⱼ` in `aⱼ` (from the chord bound). -/
lemma c_mono {R x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) (hyR : y < R) :
    (log R - log (R - x)) / x ≤ (log R - log (R - y)) / y := by
  have hR : 0 < R := by linarith
  have hy : 0 < y := by linarith
  have hch := neg_log_one_sub_le (div_pos hx hR).le (div_le_div_of_nonneg_right hxy hR.le)
    ((div_lt_one hR).mpr hyR) (div_pos hy hR)
  have e : ∀ z, z < R → -log (1 - z / R) = log R - log (R - z) := fun z hz => by
    have : 1 - z / R = (R - z) / R := by field_simp
    rw [this, log_div (by linarith) hR.ne']; ring
  rw [e x (by linarith), e y hyR] at hch
  have hxy' : x / R / (y / R) = x / y := by field_simp
  rw [hxy'] at hch
  rw [div_le_div_iff₀ hx hy]
  have := mul_le_mul_of_nonneg_left hch hy.le
  calc (log R - log (R - x)) * y = y * (log R - log (R - x)) := by ring
    _ ≤ y * (x / y * (log R - log (R - y))) := this
    _ = (log R - log (R - y)) * x := by field_simp

/-- **Claim 3.3** (rearrangement), for an arbitrary index `i`. -/
lemma claim33 {s : Finset ι} {a ℓ c : ι → ℝ} (i : ι) (hℓ : ∀ j ∈ s, 0 ≤ ℓ j ∧ ℓ j ≤ a j)
    (hc : ∀ j ∈ s, j ≤ i → c j ≤ c i) (hc' : ∀ j ∈ s, i ≤ j → c i ≤ c j) :
    ∑ j ∈ s, ℓ j * c j ≤
      ∑ j ∈ s.filter (i < ·), a j * c j + (∑ j ∈ s, ℓ j - Cgt s a i) * c i := by
  unfold Cgt
  rw [sum_filter, sum_filter, sub_mul, sum_mul, sum_mul]
  have : ∀ j ∈ s, ℓ j * c j - (if i < j then a j * c j else 0) ≤
      ℓ j * c i - (if i < j then a j else 0) * c i := by
    intro j hj
    obtain ⟨h0, h1⟩ := hℓ j hj
    split_ifs with h
    · have := hc' j hj h.le
      nlinarith
    · push Not at h
      have := hc j hj h
      nlinarith
  have := sum_le_sum this
  simp only [sum_sub_distrib] at this
  linarith

/-- **Theorem 2.1** (Ling), interior case `0 ≤ pᵢ < 1`, sorted positive bounds. -/
theorem thm21 (p w a : ι → ℝ) (s : Finset ι) (hs : s.Nonempty)
    (hp0 : ∀ i ∈ s, 0 ≤ p i) (hp1 : ∀ i ∈ s, p i < 1) (hw : ∀ i ∈ s, 0 ≤ w i)
    (hwa : ∀ i ∈ s, w i * p i ≤ a i) (ha : ∀ i ∈ s, 0 < a i)
    (hmono : ∀ i ∈ s, ∀ j ∈ s, i ≤ j → a i ≤ a j) (hd : 0 < 1 - E p w s) :
    ∃ i ∈ s, term s a (1 - E p w s) i ≤ Z p w s 1 := by
  have hp1' : ∀ i ∈ s, p i ≤ 1 := fun i hi => (hp1 i hi).le
  set d := 1 - E p w s with hddef
  have hZ : 0 < Z p w s 1 := Z_pos hp0 hp1 hw one_pos
  have hZM : d ≤ Z p w s 1 - M p w s 1 := one_sub_E_le hp0 hp1'
  set R := Rv p w s with hRdef
  set L := Lv p w s with hLdef
  have hRL : R = d + L := by simp only [hRdef, hLdef, Rv, Lv, hddef]; ring
  have hZR : Z p w s 1 * R = Z p w s 1 - M p w s 1 := by
    simp only [hRdef, Rv]; field_simp
  have hRpos : 0 < R := by
    by_contra h; push Not at h
    have : Z p w s 1 * R ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hZ.le h
    linarith
  set imax := s.max' hs with himax
  have himax_mem : imax ∈ s := max'_mem s hs
  have hamax : ∀ j ∈ s, a j ≤ a imax := fun j hj => hmono j hj imax himax_mem (le_max' s j hj)
  have hfilter_max : s.filter (imax ≤ ·) = {imax} := by
    ext j
    simp only [mem_filter, mem_singleton]
    constructor
    · rintro ⟨hj, h⟩; exact le_antisymm (le_max' s j hj) h
    · rintro rfl; exact ⟨himax_mem, le_rfl⟩
  have hCmax : Cge s a imax = a imax := by simp [Cge, hfilter_max]
  rcases le_or_gt L (a imax) with hLa | hLa
  · -- Claim 3.1
    refine ⟨imax, himax_mem, ?_⟩
    unfold term
    rw [hfilter_max, prod_singleton, hCmax]
    have h1 : 1 - a imax / (d + a imax) = d / (d + a imax) := by
      have : 0 < d + a imax := by linarith [ha imax himax_mem]
      field_simp; ring
    rw [h1, div_le_iff₀ (by linarith [ha imax himax_mem])]
    have h2 : Z p w s 1 * R ≤ Z p w s 1 * (d + a imax) :=
      mul_le_mul_of_nonneg_left (by linarith) hZ.le
    linarith
  · have haR : ∀ j ∈ s, a j < R := fun j hj => by linarith [hamax j hj]
    obtain ⟨ℓ, hℓb, hℓsum, hℓlog⟩ := claim32 p w a s hp0 hp1 hw hwa ha haR
    set c : ι → ℝ := fun j => (log R - log (R - a j)) / a j with hcdef
    have hlogZ : -(∑ j ∈ s, ℓ j * c j) ≤ log (Z p w s 1) := by
      have : ∑ j ∈ s, ℓ j / a j * log (R / (R - a j)) = ∑ j ∈ s, ℓ j * c j := by
        apply sum_congr rfl; intro j hj
        have := haR j hj
        rw [log_div hRpos.ne' (by linarith)]
        simp only [hcdef]; ring
      linarith
    have hcmono : ∀ j ∈ s, ∀ k ∈ s, j ≤ k → c j ≤ c k := fun j hj k hk hjk =>
      c_mono (ha j hj) (hmono j hj k hk hjk) (haR k hk)
    -- `L ≤ C_{≥ min}`
    set imin := s.min' hs
    have hfilter_min : s.filter (imin ≤ ·) = s := by
      ext j; simp only [mem_filter, and_iff_left_iff_imp]; exact fun hj => min'_le s j hj
    have hLtot : L ≤ Cge s a imin := by
      rw [Cge, hfilter_min, hLdef, ← hℓsum]
      exact sum_le_sum fun j hj => (hℓb j hj).2
    -- the index `i`
    set A := s.filter (fun i => L ≤ Cge s a i)
    have hA : A.Nonempty := ⟨imin, mem_filter.mpr ⟨min'_mem s hs, hLtot⟩⟩
    set i := A.max' hA
    have hiA : i ∈ A := max'_mem A hA
    have hi : i ∈ s := (mem_filter.mp hiA).1
    have hLi : L ≤ Cge s a i := (mem_filter.mp hiA).2
    have hine : i < imax := by
      rcases (le_max' s i hi).lt_or_eq with h | h
      · exact h
      · exfalso; rw [h, hCmax] at hLi; linarith
    set B := s.filter (i < ·)
    have hB : B.Nonempty := ⟨imax, mem_filter.mpr ⟨himax_mem, hine⟩⟩
    set j0 := B.min' hB
    have hj0B : j0 ∈ B := min'_mem B hB
    have hj0 : j0 ∈ s := (mem_filter.mp hj0B).1
    have hij0 : i < j0 := (mem_filter.mp hj0B).2
    have hfj0 : s.filter (j0 ≤ ·) = B := by
      ext j
      simp only [B, mem_filter]
      constructor
      · rintro ⟨hj, h⟩; exact ⟨hj, lt_of_lt_of_le hij0 h⟩
      · rintro ⟨hj, h⟩; exact ⟨hj, min'_le B j (mem_filter.mpr ⟨hj, h⟩)⟩
    have hCj0 : Cge s a j0 = Cgt s a i := by rw [Cge, hfj0]; rfl
    have hKL : Cgt s a i ≤ L := by
      by_contra h; push Not at h
      have : j0 ∈ A := mem_filter.mpr ⟨hj0, by rw [hCj0]; exact h.le⟩
      have := le_max' A j0 this
      exact absurd hij0 (not_lt.mpr this)
    -- Claim 3.3 and Prop 5.1
    have h33 := claim33 i hℓb (fun j hj hji => hcmono j hj i hi hji)
      (fun j hj hij => hcmono i hi j hj hij)
    rw [hℓsum] at h33
    have hBpos : ∀ j ∈ B, 0 ≤ a j := fun j hj => (ha j (mem_filter.mp hj).1).le
    have haK : ∀ j ∈ B, a j ≤ Cgt s a i := fun j hj => le_sum_of_mem hBpos hj
    have hbα : ∀ j ∈ B, a i ≤ a j := fun j hj => hmono i hi j (mem_filter.mp hj).1 (mem_filter.mp hj).2.le
    have h51 := prop51 (d := d) (K := Cgt s a i) B a (ha i hi) hbα (fun j hj => by linarith [haK j hj])
      (by linarith [hbα j0 hj0B, haK j0 hj0B]) L ⟨hKL, by have := Cge_eq (s := s) (a := a) hi; linarith⟩
    -- identify `G51` at `L` with the bound on `log Z`
    have hG : G51 B a (a i) d (Cgt s a i) L =
        -(∑ j ∈ B, a j * c j + (L - Cgt s a i) * c i) := by
      unfold G51
      rw [← hRL]
      have hai := ha i hi
      simp only [hcdef]
      rw [neg_add, ← sum_neg_distrib]
      congr 1
      · apply sum_congr rfl; intro j hj
        have := ha j (mem_filter.mp hj).1
        field_simp; ring
      · field_simp; ring
    -- endpoints
    have hEi : G51 B a (a i) d (Cgt s a i) (Cgt s a i + a i) = log (term s a d i) := by
      rw [(log_term hd ha i).2, filter_le_eq_insert hi, sum_insert (by simp), Cge_eq hi]
      unfold G51
      have hai := ha i hi
      rw [show Cgt s a i + a i - Cgt s a i = a i by ring, div_self hai.ne', one_mul,
        show s.filter (i < ·) = B from rfl, add_comm (a i) (Cgt s a i)]
      ring
    have hEj : G51 B a (a i) d (Cgt s a i) (Cgt s a i) = log (term s a d j0) := by
      rw [(log_term hd ha j0).2, hfj0, hCj0]
      unfold G51
      simp
    rw [hEi, hEj, hG] at h51
    have hlog : min (log (term s a d j0)) (log (term s a d i)) ≤ log (Z p w s 1) := by
      linarith
    rcases min_le_iff.mp hlog with h | h
    · refine ⟨j0, hj0, ?_⟩
      rw [← log_le_log_iff (log_term hd ha j0).1 hZ]; linarith
    · refine ⟨i, hi, ?_⟩
      rw [← log_le_log_iff (log_term hd ha i).1 hZ]; linarith

end Samuels

end
