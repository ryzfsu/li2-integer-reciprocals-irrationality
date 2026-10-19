/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.PositiveBaseContour
import Li2Lean.P0.FrequencyRegularity
import Li2Lean.P0.PositiveBaseFrequencyTail
import Li2Lean.P0.EnvContour
import Li2Lean.P0.Contour

open Finset

namespace Li2Lean.P0.Env

noncomputable section

open Li2Lean.P0.PositiveBase

/-- The coefficient of the unipotent source-row operation at base q. -/
def qSourceRowOperationCoefficient (q : ℤ) : ℝ :=
  Real.log ((q : ℝ) / ((q : ℝ) - 1))

theorem qSourceRowOperationCoefficient_positive (q : ℤ) (hq : 2 ≤ q) :
    0 < qSourceRowOperationCoefficient q := by
  have hqR : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hden : 0 < (q : ℝ) - 1 := by linarith
  have hratio : 1 < (q : ℝ) / ((q : ℝ) - 1) := by
    rw [lt_div_iff₀ hden]
    nlinarith
  exact Real.log_pos hratio

theorem qSourceRowOperationCoefficient_two :
    qSourceRowOperationCoefficient 2 = Real.log 2 := by
  norm_num [qSourceRowOperationCoefficient]

/-- The diagonal contribution to a source row at base q.  The pin constant
is `log q`; the row-operation coefficient above is a different quantity. -/
def qPinPart (q : ℤ) (g a j : ℕ) : ℂ :=
  if a = j then Complex.ofReal (Real.log (q : ℝ)) * p0UComplex q g a else 0

/-- The contour contribution to a source row at base q. -/
def qContPart (q : ℤ) (g a j : ℕ) : ℂ :=
  -p0EllipseIntegral (2 * g) (fun z =>
    p0EntireQ q g z / ((z - (a : ℂ)) * (z - (j : ℂ))))

/-- The q-parametric row split, directly from `ContourIdentity q`. -/
theorem p0C_split_q (q : ℤ) (hq : InRange q) (g a j : ℕ)
    (ha : a < 4 * g) (hj : j < 4 * g) :
    p0CComplex q g a j = qPinPart q g a j + qContPart q g a j := by
  have h := Li2Lean.P0.PositiveBase.contourIdentity_all q hq g a j ha hj
  simpa [qPinPart, qContPart, add_comm] using h

/-- Regression to the existing base-2 contour row decomposition. -/
theorem qPinPart_two (g a j : ℕ) :
    qPinPart 2 g a j =
      if a = j then (Complex.ofReal (Real.log 2)) * p0U g a else 0 := by
  by_cases h : a = j
  · subst j
    simp [qPinPart, p0UComplex_two]
  · simp [qPinPart, h]

end

end Li2Lean.P0.Env

namespace Li2Lean.P0.Env
noncomputable section
open Finset MeasureTheory
open Li2Lean.P0.PositiveBase
open Li2Lean.P0.FrequencyRegularity

private theorem continuous_p0EntireQ_local (q : ℤ) (g : ℕ) :
    Continuous (p0EntireQ q g) := by
  unfold p0EntireQ
  fun_prop

private theorem ellipse_sub_ne_local
    (m : ℕ) (hm : 0 < m) (a : ℕ) (ha : a ≤ 2 * m) (u : ℝ) :
    p0EllipsePoint m u - (a : ℂ) ≠ 0 := by
  apply sub_ne_zero.mpr
  simpa using
    (ellipsePoint_ne_real m hm u (a : ℝ) (by positivity)
      (by exact_mod_cast ha))

def qPhiC (q : ℕ) (m a : ℕ) (u : ℝ) : ℂ :=
  -((Complex.ofReal (2 * Real.pi) * Complex.I)⁻¹ *
    p0EntireQ (q : ℤ) (m / 2) (p0EllipsePoint m u) *
    p0EllipseTangent m u) * (p0EllipsePoint m u - (a : ℂ))⁻¹

def qPsiC (m j : ℕ) (u : ℝ) : ℂ :=
  (p0EllipsePoint m u - (j : ℂ))⁻¹

theorem continuous_qPhiC (q m : ℕ) (hm : 0 < m) (a : ℕ) (ha : a ≤ 2 * m) :
    Continuous (qPhiC q m a) := by
  unfold qPhiC
  apply Continuous.mul
  · exact ((continuous_const.mul ((continuous_p0EntireQ_local (q : ℤ) (m / 2)).comp
      (FrequencyRegularity.continuous_ellipsePoint m))).mul
      (FrequencyRegularity.continuous_ellipseTangent m)).neg
  · exact ((FrequencyRegularity.continuous_ellipsePoint m).sub continuous_const).inv₀
      (ellipse_sub_ne_local m hm a ha)

theorem continuous_qPsiC (m : ℕ) (hm : 0 < m) (j : ℕ) (hj : j ≤ 2 * m) :
    Continuous (qPsiC m j) :=
  ((FrequencyRegularity.continuous_ellipsePoint m).sub continuous_const).inv₀
    (ellipse_sub_ne_local m hm j hj)

theorem integrable_qPhiC_qPsiC (q m : ℕ) (hm : 0 < m) (a j : ℕ) (ha : a ≤ 2 * m)
    (hj : j ≤ 2 * m) :
    Integrable (fun u => qPhiC q m a u * qPsiC m j u) contourParameterMeasure :=
  ((continuous_qPhiC q m hm a ha).mul (continuous_qPsiC m hm j hj)).integrableOn_Icc

theorem qContPart_eq_integral (q m : ℕ) (hm : 0 < m) (a j : ℕ) (ha : a ≤ 2 * m)
    (hj : j ≤ 2 * m) (hEven : 2 ∣ m) :
    qContPart (q : ℤ) (m / 2) a j = ∫ u, qPhiC q m a u * qPsiC m j u ∂contourParameterMeasure := by
  have hgm : 2 * (m / 2) = m := by omega
  unfold qContPart p0EllipseIntegral contourParameterMeasure
  rw [hgm]
  rw [intervalIntegral.integral_of_le (by positivity), ← integral_Icc_eq_integral_Ioc,
    ← integral_const_mul, ← integral_neg]
  apply integral_congr_ae
  filter_upwards [] with u
  have h1 := ellipse_sub_ne_local m hm a ha u
  have h2 := ellipse_sub_ne_local m hm j hj u
  simp only [qPhiC, qPsiC]
  field_simp

end
end Li2Lean.P0.Env
