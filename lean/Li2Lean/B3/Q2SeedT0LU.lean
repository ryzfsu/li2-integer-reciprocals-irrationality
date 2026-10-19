/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.B3.Q2SeedResidueInterface

namespace Li2Lean.B3
noncomputable section
set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

def q2SourceMatrixAtZeroExplicit : Matrix (Fin 9) (Fin 9) ℚ := !![
  -6, 0, 12, -6, 12, -15, (132 : ℚ) / 5, -42, (516 : ℚ) / 7;
  3, 12, 0, -24, 12, -24, 30, (-264 : ℚ) / 5, 84;
  -6, -6, -24, 0, 48, -24, 48, -60, (528 : ℚ) / 5;
  (15 : ℚ) / 2, 12, 12, 48, 0, -96, 48, -96, 120;
  (5 : ℚ) / 2, (-7 : ℚ) / 4, (-29 : ℚ) / 6, (59 : ℚ) / 24, (-218 : ℚ) / 45, (61 : ℚ) / 10, (-3741 : ℚ) / 350, (28633 : ℚ) / 1680, (-263507 : ℚ) / 8820;
  (-7 : ℚ) / 6, (-29 : ℚ) / 6, (65 : ℚ) / 18, (39 : ℚ) / 4, (-97 : ℚ) / 20, (877 : ℚ) / 90, (-1276 : ℚ) / 105, (89959 : ℚ) / 4200, (-257417 : ℚ) / 7560;
  (89 : ℚ) / 36, (59 : ℚ) / 24, (39 : ℚ) / 4, (-1031 : ℚ) / 144, (-389 : ℚ) / 20, (1169 : ℚ) / 120, (-24511 : ℚ) / 1260, (81769 : ℚ) / 3360, (-134851 : ℚ) / 3150;
  (-361 : ℚ) / 120, (-218 : ℚ) / 45, (-97 : ℚ) / 20, (-389 : ℚ) / 20, (25847 : ℚ) / 1800, (584 : ℚ) / 15, (-8171 : ℚ) / 420, (98107 : ℚ) / 2520, (-49039 : ℚ) / 1008;
  (1 : ℚ) / 2, (1 : ℚ) / 3, (1 : ℚ) / 4, (1 : ℚ) / 5, (1 : ℚ) / 6, (1 : ℚ) / 7, (1 : ℚ) / 8, (1 : ℚ) / 9, (1 : ℚ) / 10
]

def q2L0 : Matrix (Fin 9) (Fin 9) ℚ := !![
  1, 0, 0, 0, 0, 0, 0, 0, 0;
  (-1 : ℚ) / 2, 1, 0, 0, 0, 0, 0, 0, 0;
  1, (-1 : ℚ) / 2, 1, 0, 0, 0, 0, 0, 0;
  (-5 : ℚ) / 4, 1, (-7 : ℚ) / 11, 1, 0, 0, 0, 0, 0;
  (-5 : ℚ) / 12, (-7 : ℚ) / 48, (-25 : ℚ) / 792, (-371 : ℚ) / 5520, 1, 0, 0, 0, 0;
  (7 : ℚ) / 36, (-29 : ℚ) / 72, (-133 : ℚ) / 1188, (-79 : ℚ) / 6210, (44966 : ℚ) / 49051, 1, 0, 0, 0;
  (-89 : ℚ) / 216, (59 : ℚ) / 288, (-1939 : ℚ) / 4752, (-3781 : ℚ) / 33120, (51259 : ℚ) / 98102, (-88699913 : ℚ) / 125513908, 1, 0, 0;
  (361 : ℚ) / 720, (-109 : ℚ) / 270, (76 : ℚ) / 297, (-100673 : ℚ) / 248400, (599652 : ℚ) / 245255, (1312231929 : ℚ) / 313784770, (54189067028688 : ℚ) / 21573137363665, 1, 0;
  (-1 : ℚ) / 12, (1 : ℚ) / 36, (-13 : ℚ) / 396, (269 : ℚ) / 82800, (85311 : ℚ) / 245255, (4342784373 : ℚ) / 8785973560, (-17159616397809 : ℚ) / 60404784618262, (-1746814252806146179 : ℚ) / 39274074983074916348, 1
]

def q2U0 : Matrix (Fin 9) (Fin 9) ℚ := !![
  -6, 0, 12, -6, 12, -15, (132 : ℚ) / 5, -42, (516 : ℚ) / 7;
  0, 12, 6, -27, 18, (-63 : ℚ) / 2, (216 : ℚ) / 5, (-369 : ℚ) / 5, (846 : ℚ) / 7;
  0, 0, -33, (-15 : ℚ) / 2, 45, (-99 : ℚ) / 4, (216 : ℚ) / 5, (-549 : ℚ) / 10, (3231 : ℚ) / 35;
  0, 0, 0, (690 : ℚ) / 11, (282 : ℚ) / 11, -99, (3591 : ℚ) / 55, (-1206 : ℚ) / 11, (57762 : ℚ) / 385;
  0, 0, 0, 0, (49051 : ℚ) / 8280, (-22409 : ℚ) / 1840, (159239 : ℚ) / 12880, (-785191 : ℚ) / 38640, (63821351 : ℚ) / 2028600;
  0, 0, 0, 0, 0, (31378477 : ℚ) / 4414590, (-381291923 : ℚ) / 68671400, (1127710667 : ℚ) / 103007100, (-211580422063 : ℚ) / 12978894600;
  0, 0, 0, 0, 0, 0, (-4314627472733 : ℚ) / 1581475240800, (4417245127363 : ℚ) / 790737620400, (-344040071027369 : ℚ) / 33210980056800;
  0, 0, 0, 0, 0, 0, 0, (-1402645535109818441 : ℚ) / 135910765391089500, (5593078613507885891 : ℚ) / 317125119245875500;
  0, 0, 0, 0, 0, 0, 0, 0, (158649262379640306631463 : ℚ) / 412377787322286621654000
]

theorem q2_lu0 : q2SourceMatrixAtZeroExplicit = q2L0 * q2U0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [q2SourceMatrixAtZeroExplicit, q2L0, q2U0, Matrix.mul_apply, Fin.sum_univ_succ]

theorem q2_lu0_det : q2SourceMatrixAtZeroExplicit.det =
    (158649262379640306631463 / 2333772000000000 : ℚ) := by
  rw [q2_lu0, Matrix.det_mul]
  have hL : q2L0.IsLowerTriangular := by decide
  have hU : q2U0.IsUpperTriangular := by decide
  rw [Matrix.det_of_isLowerTriangular q2L0 hL, Matrix.det_of_isUpperTriangular hU]
  norm_num [q2L0, q2U0, Fin.prod_univ_succ]

theorem q2_source_eq_explicit :
    q2SourceMatrixAtZero = q2SourceMatrixAtZeroExplicit := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [q2SourceMatrixAtZero, q2SourceMatrixAtZeroExplicit,
      V.vSourceMatrix, V.vJIndex,
      V.vMatrixSize, V.vM, V.vS, V.vIIndexNat, V.vCEntry, V.vBEntry,
      V.vMomentB, V.vMomentT, V.vVEntry]

theorem q2_constant_eq :
    (V.vPolynomial 1 (-2 : ℤ)).coeff 0 = vSeedConstant 2 := by
  have hdet : q2SourceMatrixAtZero.det =
      (158649262379640306631463 / 2333772000000000 : ℚ) := by
    rw [q2_source_eq_explicit, q2_lu0_det]
  have heval : (V.vPolynomial 1 (-2 : ℤ)).eval 0 =
      (158649262379640306631463 / 2333772000000000 : ℚ) := by
    rw [← q2SourceMatrixAtZero_det_eq_seed_eval]
    exact hdet
  rw [Polynomial.coeff_zero_eq_eval_zero]
  simpa [vSeedConstant] using heval

end
end Li2Lean.B3
