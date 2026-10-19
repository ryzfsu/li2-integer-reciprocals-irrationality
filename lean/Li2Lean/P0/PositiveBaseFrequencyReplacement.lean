/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.PositiveBaseCellShift
import Li2Lean.P0.FrequencyRatio
import Li2Lean.P0.ContourFrequencyFactor

open scoped BigOperators

namespace Li2Lean.P0.PositiveBase

noncomputable section

open Li2Lean.P0
open Li2Lean.P0.FrequencyLeaf

/-- The factor converting a base-2 frequency weight product to base `q`. -/
def qFrequencyScale (q : ℕ) (R : Finset ℕ) : ℝ :=
  ∏ r ∈ R, ((2 : ℝ) / (q : ℝ)) ^ r

/-- The frequency-dependent contour factor with the q-specific weights. -/
def qFrequencyFactor (q m g : ℕ) (S R : Finset ℕ)
    (d : ℕ) (Z : Fin d → ℂ) : ℝ :=
  qFrequencyScale q R * FrequencyLeaf.frequencyFactor m g S R d Z

/-- Each q-weight is the base-2 weight times the exact exponential scale. -/
theorem qFrequencyWeightReal_eq_scale_mul_weight
    (q g r : ℕ) (hq : 0 < q) :
    qFrequencyWeightReal q g r =
      ((2 : ℝ) / (q : ℝ)) ^ r * FrequencyLeaf.weight g r := by
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  unfold qFrequencyWeightReal FrequencyLeaf.weight
  calc
    (Nat.choose (r - 1) g : ℝ) / (q : ℝ) ^ r =
        (Nat.choose (r - 1) g : ℝ) * ((q : ℝ) ^ r)⁻¹ := by ring
    _ = (Nat.choose (r - 1) g : ℝ) *
        (((2 : ℝ) / (q : ℝ)) ^ r * (1 / 2 : ℝ) ^ r) := by
      congr 1
      rw [← mul_pow]
      have hbase : (2 : ℝ) / (q : ℝ) * (1 / 2 : ℝ) = (q : ℝ)⁻¹ := by
        field_simp [hqR]
      rw [hbase, inv_pow]
    _ = ((2 : ℝ) / (q : ℝ)) ^ r *
        ((Nat.choose (r - 1) g : ℝ) * (1 / 2 : ℝ) ^ r) := by ring

/-- The weight product on an increasing tuple becomes the scaled q=2 product
on its image set. -/
theorem qFrequencyWeights_eq_scale_mul
    {m : ℕ} (q g : ℕ) (R : Fin m → ℕ) (hR : StrictMono R)
    (hq : 0 < q) :
    (∏ i : Fin m, qFrequencyWeightReal q g (R i)) =
      qFrequencyScale q ((Finset.univ : Finset (Fin m)).image R) *
        (∏ i : Fin m, FrequencyLeaf.weight g (R i)) := by
  classical
  calc
    (∏ i : Fin m, qFrequencyWeightReal q g (R i)) =
        ∏ i : Fin m,
          (((2 : ℝ) / (q : ℝ)) ^ (R i) * FrequencyLeaf.weight g (R i)) := by
      apply Finset.prod_congr rfl
      intro i hi
      exact qFrequencyWeightReal_eq_scale_mul_weight q g (R i) hq
    _ = (∏ i : Fin m, ((2 : ℝ) / (q : ℝ)) ^ (R i)) *
          (∏ i : Fin m, FrequencyLeaf.weight g (R i)) := Finset.prod_mul_distrib
    _ = qFrequencyScale q ((Finset.univ : Finset (Fin m)).image R) *
          (∏ i : Fin m, FrequencyLeaf.weight g (R i)) := by
      rw [Li2Lean.P0.prod_fin_image R hR.injective]
      rfl

/-- Removing `r` and inserting `s ≤ r` changes the scale by exactly
`(2/q)^(r-s)`. -/
theorem qFrequencyScale_replace_eq
    (q g m : ℕ) (R : Finset ℕ) (s r : ℕ)
    (hr : r ∈ R) (hs : s ∉ R) (hsr : s ≤ r) :
    qFrequencyScale q R =
      ((2 : ℝ) / (q : ℝ)) ^ (r - s) *
        qFrequencyScale q (FrequencyLeaf.replace g m R s r) := by
  classical
  let b : ℝ := (2 : ℝ) / (q : ℝ)
  have herase : r ∉ R.erase r := by simp
  have hsErase : s ∉ R.erase r := by
    intro hs'
    exact hs (Finset.mem_erase.mp hs').2
  have hRscale : qFrequencyScale q R = b ^ r * qFrequencyScale q (R.erase r) := by
    rw [qFrequencyScale, ← Finset.insert_erase hr]
    rw [Finset.prod_insert herase]
    simp [qFrequencyScale, b]
  have hRepScale :
      qFrequencyScale q (FrequencyLeaf.replace g m R s r) =
        b ^ s * qFrequencyScale q (R.erase r) := by
    rw [FrequencyLeaf.replace]
    simp [qFrequencyScale, b, hsErase]
  have hpow : b ^ r = b ^ (r - s) * b ^ s := by
    rw [← pow_add]
    congr 1
    omega
  rw [hRscale, hRepScale, hpow]
  ring

/-- For q ≥ 2, the q-weighted frequency factor obeys the same largest-site
replacement estimate as the q=2 factor. The only extra multiplier is
`(2/q)^(r-s) ≤ 1`, while the residual tail remains weighted by the paper's
base-2 weight. -/
theorem qFrequencyFactor_replacement_le
    {m g r s : ℕ} (q : ℕ) (hq : 2 ≤ q)
    (hm : 0 < m) (hm4 : 4 ∣ m) (hgm : 2 * g = m)
    (S R : Finset ℕ) (hSI : S ⊆ FrequencyLeaf.I_m m)
    (hR : FrequencyLeaf.admissible g m R)
    (hrmem : r ∈ R) (hs : s ∉ R) (hgs : g < s) (hsite : s ≤ g + m)
    (hr : 20 * m < r) (hmax : ∀ u ∈ R, u ≤ r)
    (Z : Fin (m - S.card) → ℂ)
    (hZre : ∀ z, -(m : ℝ) / 6 < (Z z).re)
    (hZnorm : ∀ z, ‖Z z‖ < 5 * (m : ℝ) / 2) :
    qFrequencyFactor q m g S R (m - S.card) Z ≤
      ((12500 : ℝ) ^ m * (m : ℝ) ^ 2 / (4 * (r : ℝ) ^ 2) *
        FrequencyLeaf.weight g r) *
        qFrequencyFactor q m g S (FrequencyLeaf.replace g m R s r)
          (m - S.card) Z := by
  have hb : 0 ≤ (2 : ℝ) / (q : ℝ) := by positivity
  have hb1 : (2 : ℝ) / (q : ℝ) ≤ 1 := by
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < q)]
    have hqR : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
    nlinarith
  have hpow : ((2 : ℝ) / (q : ℝ)) ^ (r - s) ≤ 1 :=
    pow_le_one₀ hb hb1
  have hpow_nonneg : 0 ≤ ((2 : ℝ) / (q : ℝ)) ^ (r - s) :=
    pow_nonneg hb (r - s)
  have hscale := qFrequencyScale_replace_eq q g m R s r hrmem hs (by omega)
  have hbase := FrequencyLeaf.frequencyFactor_replacement_le
    hm hm4 hgm S R hSI hR hrmem hs hgs hsite hr hmax Z hZre hZnorm
  have hscale_nonneg :
      0 ≤ qFrequencyScale q (FrequencyLeaf.replace g m R s r) := by
    unfold qFrequencyScale
    apply Finset.prod_nonneg
    intro t ht
    exact pow_nonneg (div_nonneg (by norm_num) (by positivity)) t
  have hweight_nonneg : 0 ≤ FrequencyLeaf.weight g r := by
    unfold FrequencyLeaf.weight
    positivity
  have hC_nonneg :
      0 ≤ (12500 : ℝ) ^ m * (m : ℝ) ^ 2 /
        (4 * (r : ℝ) ^ 2) * FrequencyLeaf.weight g r := by
    positivity
  have hfreq_nonneg :=
    FrequencyLeaf.frequencyFactor_nonneg m g S
      (FrequencyLeaf.replace g m R s r) (d := m - S.card) Z
  unfold qFrequencyFactor
  rw [hscale]
  calc
    ((2 : ℝ) / (q : ℝ)) ^ (r - s) *
        qFrequencyScale q (FrequencyLeaf.replace g m R s r) *
          FrequencyLeaf.frequencyFactor m g S R (m - S.card) Z =
      (((2 : ℝ) / (q : ℝ)) ^ (r - s) *
        qFrequencyScale q (FrequencyLeaf.replace g m R s r)) *
          FrequencyLeaf.frequencyFactor m g S R (m - S.card) Z := by ring
    _ ≤ (((2 : ℝ) / (q : ℝ)) ^ (r - s) *
          qFrequencyScale q (FrequencyLeaf.replace g m R s r)) *
        (((12500 : ℝ) ^ m * (m : ℝ) ^ 2 /
          (4 * (r : ℝ) ^ 2) * FrequencyLeaf.weight g r) *
          FrequencyLeaf.frequencyFactor m g S
            (FrequencyLeaf.replace g m R s r) (m - S.card) Z) :=
      mul_le_mul_of_nonneg_left hbase
        (mul_nonneg hpow_nonneg hscale_nonneg)
    _ = ((2 : ℝ) / (q : ℝ)) ^ (r - s) *
          (qFrequencyScale q (FrequencyLeaf.replace g m R s r) *
            (((12500 : ℝ) ^ m * (m : ℝ) ^ 2 /
              (4 * (r : ℝ) ^ 2) * FrequencyLeaf.weight g r) *
              FrequencyLeaf.frequencyFactor m g S
                (FrequencyLeaf.replace g m R s r) (m - S.card) Z)) := by ring
    _ ≤ 1 *
          (qFrequencyScale q (FrequencyLeaf.replace g m R s r) *
            (((12500 : ℝ) ^ m * (m : ℝ) ^ 2 /
              (4 * (r : ℝ) ^ 2) * FrequencyLeaf.weight g r) *
              FrequencyLeaf.frequencyFactor m g S
                (FrequencyLeaf.replace g m R s r) (m - S.card) Z)) :=
      mul_le_mul_of_nonneg_right hpow
        (mul_nonneg hscale_nonneg (mul_nonneg hC_nonneg hfreq_nonneg))
    _ = ((12500 : ℝ) ^ m * (m : ℝ) ^ 2 /
          (4 * (r : ℝ) ^ 2) * FrequencyLeaf.weight g r) *
        (qFrequencyScale q (FrequencyLeaf.replace g m R s r) *
          FrequencyLeaf.frequencyFactor m g S
            (FrequencyLeaf.replace g m R s r) (m - S.card) Z) := by ring

end

end Li2Lean.P0.PositiveBase

#print axioms Li2Lean.P0.PositiveBase.qFrequencyWeightReal_eq_scale_mul_weight
#print axioms Li2Lean.P0.PositiveBase.qFrequencyWeights_eq_scale_mul
#print axioms Li2Lean.P0.PositiveBase.qFrequencyScale_replace_eq
#print axioms Li2Lean.P0.PositiveBase.qFrequencyFactor_replacement_le
