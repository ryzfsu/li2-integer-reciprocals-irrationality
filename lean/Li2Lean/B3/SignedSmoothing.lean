/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/

import Li2Lean.V.AllMSmoothing

/-!
Signed V denominator-transfer extensions.

The common smoothing geometry, circle-average identity, transfer budgets, and
`AllMSmoothingCertificate` live in `Li2Lean.V.AllMSmoothing`.  This module
keeps only the denominator perturbation estimates specific to the signed V
route, so importing both interfaces cannot redeclare the canonical names.
-/

namespace Li2Lean

noncomputable section

namespace B3

open MeasureTheory

/-! ### The explicit denominator transfer estimates -/

/-- The product perturbation caused by the two translated circles
(`v-analytic.tex:550-552`). -/
theorem translatedAtom_product_displacement (x y : ℂ) (m : ℕ) (theta phi : ℝ)
    (hm : 0 < m) (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) :
    ‖translatedAtom x m theta * translatedAtom y m phi - x * y‖ ≤
      6 * smoothingEpsilon m + 9 * smoothingEpsilon m ^ 2 := by
  have heps : 0 ≤ smoothingEpsilon m := by
    unfold smoothingEpsilon
    positivity
  let a := translatedAtom x m theta
  let b := translatedAtom y m phi
  have hax : ‖a - x‖ ≤ 3 * smoothingEpsilon m := by
    exact translatedAtom_dist_le_threeEpsilon x m theta hm
  have hby : ‖b - y‖ ≤ 3 * smoothingEpsilon m := by
    exact translatedAtom_dist_le_threeEpsilon y m phi hm
  have hbn : ‖b‖ ≤ 1 + 3 * smoothingEpsilon m := by
    exact translatedAtom_norm_le_one_add_threeEpsilon (u := y) m phi hm hy
  have hab : a * b - x * y = (a - x) * b + x * (b - y) := by ring
  have hterm1 : ‖a - x‖ * ‖b‖ ≤
      (3 * smoothingEpsilon m) * (1 + 3 * smoothingEpsilon m) := by
    exact mul_le_mul hax hbn (norm_nonneg b) (by nlinarith [heps])
  have hterm2 : ‖x‖ * ‖b - y‖ ≤ 1 * (3 * smoothingEpsilon m) := by
    exact mul_le_mul hx hby (norm_nonneg _) (by norm_num)
  rw [show translatedAtom x m theta * translatedAtom y m phi - x * y =
    (a - x) * b + x * (b - y) by exact hab]
  calc
    ‖(a - x) * b + x * (b - y)‖ ≤
        ‖a - x‖ * ‖b‖ + ‖x‖ * ‖b - y‖ := by
      simpa only [norm_mul] using (norm_add_le ((a - x) * b) (x * (b - y)))
    _ ≤ (3 * smoothingEpsilon m) * (1 + 3 * smoothingEpsilon m) +
        1 * (3 * smoothingEpsilon m) := add_le_add hterm1 hterm2
    _ = 6 * smoothingEpsilon m + 9 * smoothingEpsilon m ^ 2 := by ring

/-- The scalar absorption used in the weighted cross-denominator estimate
(`v-analytic.tex:555-558`). -/
theorem denominator_transfer_scalar_absorption {m : ℕ} (hm : 64 ≤ m) :
    (15 / 2 : ℝ) * smoothingEpsilon m +
        (45 / 4 : ℝ) * smoothingEpsilon m ^ 2 ≤
      8 * smoothingEpsilon m := by
  have hε := smoothingEpsilon_le_one_div_4096 hm
  have hεnonneg : 0 ≤ smoothingEpsilon m := by
    unfold smoothingEpsilon
    positivity
  nlinarith

/-- The `8 L_D epsilon` absorption in v13 `v-analytic.tex:555-558`. -/
theorem denominator_transfer_cost_at_epsilon {m : ℕ} (hm : 64 ≤ m)
    {q : ℕ} (hq : 2 ≤ q) :
    ((15 / 2 : ℝ) * smoothingEpsilon m +
        (45 / 4 : ℝ) * smoothingEpsilon m ^ 2) * denominatorLipschitz q ≤
      denominatorTransferCost q * smoothingEpsilon m := by
  have hscalar := denominator_transfer_scalar_absorption hm
  have hL : 0 ≤ denominatorLipschitz q := (denominatorLipschitz_pos hq).le
  unfold denominatorTransferCost
  nlinarith [mul_le_mul_of_nonneg_right hscalar hL]

/-- The uniform tube radius `1+3/4096`, v13 `v-analytic.tex:550-552`. -/
def denominatorTubeRadius : ℝ := 1 + 3 / 4096

/-- A real logarithm is Lipschitz above a common positive lower bound.
This is the scalar form used for the denominator transfer in
`v-analytic.tex:551-557`. -/
theorem abs_log_sub_log_le_common_lower {u v c : ℝ} (hc : 0 < c)
    (hu : c ≤ u) (hv : c ≤ v) :
    |Real.log u - Real.log v| ≤ |u - v| / c := by
  have hu0 : 0 < u := lt_of_lt_of_le hc hu
  have hv0 : 0 < v := lt_of_lt_of_le hc hv
  have h1 : Real.log u - Real.log v ≤ (u - v) / v := by
    rw [← Real.log_div hu0.ne' hv0.ne']
    have h := Real.log_le_sub_one_of_pos (div_pos hu0 hv0)
    calc
      Real.log (u / v) ≤ u / v - 1 := h
      _ = (u - v) / v := by field_simp
  have h2 : Real.log v - Real.log u ≤ (v - u) / u := by
    rw [← Real.log_div hv0.ne' hu0.ne']
    have h := Real.log_le_sub_one_of_pos (div_pos hv0 hu0)
    calc
      Real.log (v / u) ≤ v / u - 1 := h
      _ = (v - u) / u := by field_simp
  have h3 : (u - v) / v ≤ |u - v| / c :=
    (div_le_div_of_nonneg_right (le_abs_self _) hv0.le).trans
      (div_le_div_of_nonneg_left (abs_nonneg _) hc hv)
  have h4 : (v - u) / u ≤ |u - v| / c := by
    have hsub : v - u ≤ |u - v| := by
      rw [abs_sub_comm]
      exact le_abs_self _
    exact (div_le_div_of_nonneg_right hsub hu0.le).trans
      (div_le_div_of_nonneg_left (abs_nonneg _) hc hu)
  rw [abs_le]
  constructor <;> linarith

/-- The denominator stays at least `q-(1+3/4096)^2` from zero, v13
`v-analytic.tex:550-552`. -/
theorem denominator_norm_lower {q : ℕ} {z : ℂ} (hq : 2 ≤ q)
    (hz : ‖z‖ ≤ denominatorTubeRadius ^ 2) :
    (q : ℝ) - denominatorTubeRadius ^ 2 ≤ ‖(q : ℂ) + z‖ := by
  have hqR : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have htriangle : ‖(q : ℂ)‖ ≤ ‖(q : ℂ) + z‖ + ‖z‖ := by
    calc
      ‖(q : ℂ)‖ = ‖((q : ℂ) + z) - z‖ := by congr 1; ring
      _ ≤ ‖(q : ℂ) + z‖ + ‖z‖ := norm_sub_le _ _
  have hqnorm : ‖(q : ℂ)‖ = (q : ℝ) := by norm_cast
  rw [hqnorm] at htriangle
  linarith

/-- The quantitative logarithm transfer on the v13 tube,
`v-analytic.tex:546-557`. -/
theorem denominator_log_lipschitz {q : ℕ} (hq : 2 ≤ q) (u v x y : ℂ)
    (hu : ‖u‖ ≤ denominatorTubeRadius) (hv : ‖v‖ ≤ denominatorTubeRadius)
    (hx : ‖x‖ ≤ denominatorTubeRadius) (hy : ‖y‖ ≤ denominatorTubeRadius) :
    |Real.log ‖(q : ℂ) + u * v‖ - Real.log ‖(q : ℂ) + x * y‖| ≤
      denominatorLipschitz q * ‖u * v - x * y‖ := by
  have hden : 0 < (q : ℝ) - denominatorTubeRadius ^ 2 := by
    norm_num [denominatorTubeRadius]
    have hqR : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
    nlinarith
  have huv : ‖u * v‖ ≤ denominatorTubeRadius ^ 2 := by
    rw [norm_mul]
    have hrad : 0 ≤ denominatorTubeRadius := by
      norm_num [denominatorTubeRadius]
    calc
      ‖u‖ * ‖v‖ ≤ denominatorTubeRadius * denominatorTubeRadius :=
        mul_le_mul hu hv (norm_nonneg _) hrad
      _ = denominatorTubeRadius ^ 2 := by ring
  have hxy : ‖x * y‖ ≤ denominatorTubeRadius ^ 2 := by
    rw [norm_mul]
    have hrad : 0 ≤ denominatorTubeRadius := by
      norm_num [denominatorTubeRadius]
    calc
      ‖x‖ * ‖y‖ ≤ denominatorTubeRadius * denominatorTubeRadius :=
        mul_le_mul hx hy (norm_nonneg _) hrad
      _ = denominatorTubeRadius ^ 2 := by ring
  have hA : (q : ℝ) - denominatorTubeRadius ^ 2 ≤
      ‖(q : ℂ) + u * v‖ := denominator_norm_lower hq huv
  have hB : (q : ℝ) - denominatorTubeRadius ^ 2 ≤
      ‖(q : ℂ) + x * y‖ := denominator_norm_lower hq hxy
  have hnormdiff :
      |‖(q : ℂ) + u * v‖ - ‖(q : ℂ) + x * y‖| ≤ ‖u * v - x * y‖ := by
    calc
      |‖(q : ℂ) + u * v‖ - ‖(q : ℂ) + x * y‖| ≤
          ‖((q : ℂ) + u * v) - ((q : ℂ) + x * y)‖ := abs_norm_sub_norm_le _ _
      _ = ‖u * v - x * y‖ := by congr 1; ring
  have hlog := abs_log_sub_log_le_common_lower hden hA hB
  have hcoeff : (1 : ℝ) / ((q : ℝ) - denominatorTubeRadius ^ 2) ≤
      denominatorTubeRadius / ((q : ℝ) - denominatorTubeRadius ^ 2) := by
    exact div_le_div_of_nonneg_right (by norm_num [denominatorTubeRadius]) hden.le
  calc
    |Real.log ‖(q : ℂ) + u * v‖ - Real.log ‖(q : ℂ) + x * y‖| ≤
        |‖(q : ℂ) + u * v‖ - ‖(q : ℂ) + x * y‖| /
          ((q : ℝ) - denominatorTubeRadius ^ 2) := hlog
    _ ≤ ‖u * v - x * y‖ /
          ((q : ℝ) - denominatorTubeRadius ^ 2) :=
      div_le_div_of_nonneg_right hnormdiff hden.le
    _ = ((1 : ℝ) / ((q : ℝ) - denominatorTubeRadius ^ 2)) *
        ‖u * v - x * y‖ := by ring
    _ ≤ (denominatorTubeRadius /
        ((q : ℝ) - denominatorTubeRadius ^ 2)) * ‖u * v - x * y‖ :=
      mul_le_mul_of_nonneg_right hcoeff (norm_nonneg _)
    _ = denominatorLipschitz q * ‖u * v - x * y‖ := by
      simp [denominatorLipschitz, denominatorTubeRadius]

/-- The pointwise denominator transfer between original and smoothed atoms,
`v-analytic.tex:550-558`. -/
theorem translatedAtom_denominator_log_transfer {q m : ℕ} (hq : 2 ≤ q)
    (hm : 64 ≤ m) (x y : ℂ) (theta phi : ℝ) (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) :
    |Real.log ‖(q : ℂ) + translatedAtom x m theta * translatedAtom y m phi‖ -
      Real.log ‖(q : ℂ) + x * y‖| ≤
      denominatorLipschitz q *
        (6 * smoothingEpsilon m + 9 * smoothingEpsilon m ^ 2) := by
  have hε := smoothingEpsilon_le_one_div_4096 hm
  have hεnonneg : 0 ≤ smoothingEpsilon m := by
    unfold smoothingEpsilon
    positivity
  have hrad : 1 + 3 * smoothingEpsilon m ≤ denominatorTubeRadius := by
    norm_num [denominatorTubeRadius]
    nlinarith
  have hone : (1 : ℝ) ≤ 1 + 3 * smoothingEpsilon m := by nlinarith
  have hxR : ‖x‖ ≤ denominatorTubeRadius := hx.trans (hone.trans hrad)
  have hyR : ‖y‖ ≤ denominatorTubeRadius := hy.trans (hone.trans hrad)
  have huR : ‖translatedAtom x m theta‖ ≤ denominatorTubeRadius :=
    (translatedAtom_norm_le_one_add_threeEpsilon (u := x) m theta
      (by omega) hx).trans hrad
  have hvR : ‖translatedAtom y m phi‖ ≤ denominatorTubeRadius :=
    (translatedAtom_norm_le_one_add_threeEpsilon (u := y) m phi
      (by omega) hy).trans hrad
  have hlog := denominator_log_lipschitz hq (translatedAtom x m theta)
    (translatedAtom y m phi) x y huR hvR hxR hyR
  have hprod := translatedAtom_product_displacement x y m theta phi (by omega) hx hy
  exact hlog.trans (mul_le_mul_of_nonneg_left hprod (denominatorLipschitz_pos hq).le)

theorem weighted_denominator_pair_cost {q m : ℕ} (hq : 2 ≤ q) (hm : 64 ≤ m)
    (x y : ℂ) (theta phi : ℝ) (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) :
    (5 / 4 : ℝ) *
      |Real.log ‖(q : ℂ) + translatedAtom x m theta * translatedAtom y m phi‖ -
        Real.log ‖(q : ℂ) + x * y‖| ≤ denominatorTransferCost q * smoothingEpsilon m := by
  have hpair := translatedAtom_denominator_log_transfer hq hm x y theta phi hx hy
  have hcost := denominator_transfer_cost_at_epsilon hm hq
  calc
    (5 / 4 : ℝ) *
        |Real.log ‖(q : ℂ) + translatedAtom x m theta * translatedAtom y m phi‖ -
          Real.log ‖(q : ℂ) + x * y‖| ≤
      (5 / 4 : ℝ) * (denominatorLipschitz q *
        (6 * smoothingEpsilon m + 9 * smoothingEpsilon m ^ 2)) :=
      mul_le_mul_of_nonneg_left hpair (by norm_num)
    _ = ((15 / 2 : ℝ) * smoothingEpsilon m +
        (45 / 4 : ℝ) * smoothingEpsilon m ^ 2) * denominatorLipschitz q := by ring
    _ ≤ denominatorTransferCost q * smoothingEpsilon m := hcost


end B3

end

end Li2Lean

#print axioms Li2Lean.B3.translatedAtom_circleAverage
#print axioms Li2Lean.B3.all_m_log_bound_of_certificate
