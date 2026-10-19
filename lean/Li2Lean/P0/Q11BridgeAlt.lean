/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.Q11WmuTail
import Li2Lean.P0.Q11EndpointCoarseV2
import Li2Lean.P0.ContourEnergyLowerBound

open MeasureTheory Set
open scoped ENNReal

namespace Li2Lean.P0.Q11Data

noncomputable section

open Li2Lean.P0.ConfigContourTail

theorem q11BaseTail_ge_coarse {t : ℝ} (ht : (81 / 10 : ℝ) ≤ t) :
    3 * Real.log t + t * q11Lambda ≤ q11BaseTail t := by
  have htpos : 0 < t := by linarith
  have hhalf : (1 / 2 : ℝ) ≤ t := by linarith
  have hB := Li2Lean.P0.EnergyLowerBound.B0_ge htpos
  have hpsi := Li2Lean.P0.EnergyLowerBound.psi_le hhalf
  have hlog := Real.log_le_sub_one_of_pos htpos
  have hlog2lo : (2 : ℝ) / 3 ≤ Real.log 2 := by
    have h := Real.le_log_one_add_of_nonneg (x := (1 : ℝ)) (by norm_num)
    norm_num at h
    exact h
  have hlog2hi : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h ⊢
    exact h
  have hlog_mul : t * Real.log t ≤ t * (t - 1) :=
    mul_le_mul_of_nonneg_left hlog htpos.le
  have hlog_half : Real.log t / 2 ≤ (t - 1) / 2 := by linarith
  have hlog2_half : Real.log 2 / 2 ≤ (1 : ℝ) / 2 := by linarith
  have hlog2_mul : t * (2 / 3 : ℝ) ≤ t * Real.log 2 :=
    mul_le_mul_of_nonneg_left hlog2lo htpos.le
  have hupper : Real.log t / 2 + 1 / 2 + Real.log 2 / 2 -
      t * Real.log 2 ≤ (1 : ℝ) / 2 - t / 6 := by
    nlinarith [hlog_half, hlog2_half, hlog2_mul]
  have hpsi0 : Config.psi t ≤ 0 := by
    have hneg : (1 / 2 : ℝ) - t / 6 < 0 := by nlinarith [ht]
    have hlt : Config.psi t < 0 := lt_of_le_of_lt (le_trans hpsi hupper) hneg
    exact hlt.le
  have hbase : q11BaseTail t = Config.B0 t - Config.psi t + t * q11Lambda := by
    simp [q11BaseTail, q11Psi]
    ring
  have hBpsi : 3 * Real.log t ≤ Config.B0 t - Config.psi t := by
    calc
      3 * Real.log t ≤ Config.B0 t := hB
      _ ≤ Config.B0 t - Config.psi t := by
        rw [sub_eq_add_neg]
        exact le_add_of_nonneg_right (neg_nonneg.mpr hpsi0)
  rw [hbase]
  linarith [hBpsi]

end

end Li2Lean.P0.Q11Data
