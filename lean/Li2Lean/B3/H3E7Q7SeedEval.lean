/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.B3.ActualFrobeniusProducer

namespace Li2Lean.B3
noncomputable section
set_option maxRecDepth 1000000
set_option maxHeartbeats 30000000

def q7SourceMatrixAtZeroExplicit : Matrix (Fin 9) (Fin 9) ℚ := !![
  -56, 0, 392, -1176, (16856 : ℚ) / 3, -29400, (823592 : ℚ) / 5, -960792, 5764808;
  168, 392, 0, -2744, 8232, (-117992 : ℚ) / 3, 205800, (-5765144 : ℚ) / 5, 6725544;
  (-2408 : ℚ) / 3, -1176, -2744, 0, 19208, -57624, (825944 : ℚ) / 3, -1440600, (40356008 : ℚ) / 5;
  4200, (16856 : ℚ) / 3, 8232, 19208, 0, -134456, 403368, (-5781608 : ℚ) / 3, 10084200;
  (15 : ℚ) / 2, (-27 : ℚ) / 4, (-157 : ℚ) / 3, (3769 : ℚ) / 24, (-135047 : ℚ) / 180, (942199 : ℚ) / 240, (-46189651 : ℚ) / 2100, (92373047 : ℚ) / 720, (-277121821 : ℚ) / 360;
  (-269 : ℚ) / 12, (-157 : ℚ) / 3, (1705 : ℚ) / 36, (4397 : ℚ) / 12, (-43969 : ℚ) / 40, (315113 : ℚ) / 60, (-46167671 : ℚ) / 1680, (30793109 : ℚ) / 200, (-1939833907 : ℚ) / 2160;
  (3859 : ℚ) / 36, (3769 : ℚ) / 24, (4397 : ℚ) / 12, (-47731 : ℚ) / 144, (-38473 : ℚ) / 15, (461677 : ℚ) / 60, (-7720261 : ℚ) / 210, (92335357 : ℚ) / 480, (-1939965817 : ℚ) / 1800;
  (-134597 : ℚ) / 240, (-135047 : ℚ) / 180, (-43969 : ℚ) / 40, (-38473 : ℚ) / 15, (8353069 : ℚ) / 3600, (179541 : ℚ) / 10, (-22622161 : ℚ) / 420, (30881047 : ℚ) / 120, (-387808493 : ℚ) / 288;
  (1 : ℚ) / 2, (1 : ℚ) / 3, (1 : ℚ) / 4, (1 : ℚ) / 5, (1 : ℚ) / 6, (1 : ℚ) / 7, (1 : ℚ) / 8, (1 : ℚ) / 9, (1 : ℚ) / 10
]
def q7L0 : Matrix (Fin 9) (Fin 9) ℚ := !![
  1, 0, 0, 0, 0, 0, 0, 0, 0;
  -3, 1, 0, 0, 0, 0, 0, 0, 0;
  (43 : ℚ) / 3, -3, 1, 0, 0, 0, 0, 0, 0;
  -75, (43 : ℚ) / 3, (-159 : ℚ) / 37, 1, 0, 0, 0, 0, 0;
  (-15 : ℚ) / 112, (-27 : ℚ) / 1568, (-5 : ℚ) / 1184, (-103661 : ℚ) / 11085760, 1, 0, 0, 0, 0;
  (269 : ℚ) / 672, (-157 : ℚ) / 1176, (-61 : ℚ) / 6216, (-4307 : ℚ) / 2771440, (5093665 : ℚ) / 25417107, 1, 0, 0, 0;
  (-3859 : ℚ) / 2016, (3769 : ℚ) / 9408, (-6641 : ℚ) / 49728, (-1766941 : ℚ) / 66514560, (33595745 : ℚ) / 16944738, (-8186791643271 : ℚ) / 16764415569878, 1, 0, 0;
  (134597 : ℚ) / 13440, (-135047 : ℚ) / 70560, (19023 : ℚ) / 33152, (-1387891 : ℚ) / 10392900, (60316828 : ℚ) / 42361845, (1018725739901697 : ℚ) / 41911038924695, (-969925157015979500736 : ℚ) / 142736649474419458295, 1, 0;
  (-1 : ℚ) / 112, (1 : ℚ) / 1176, (-33 : ℚ) / 58016, (-13501 : ℚ) / 27714400, (5830558 : ℚ) / 98844305, (5421484792818 : ℚ) / 293377272472865, (-131036437331657718048 : ℚ) / 9791734153945174839037, (331920547704671290369120226 : ℚ) / 436748497698189933858986300805, 1
]
def q7U0 : Matrix (Fin 9) (Fin 9) ℚ := !![
  -56, 0, 392, -1176, (16856 : ℚ) / 3, -29400, (823592 : ℚ) / 5, -960792, 5764808;
  0, 392, 1176, -6272, 25088, (-382592 : ℚ) / 3, (3499776 : ℚ) / 5, (-20177024 : ℚ) / 5, 24019968;
  0, 0, (-14504 : ℚ) / 3, -1960, (125440 : ℚ) / 9, -18816, (213248 : ℚ) / 15, (1122688 : ℚ) / 5, (-37467136 : ℚ) / 15;
  0, 0, 0, (1385720 : ℚ) / 111, (4502904 : ℚ) / 37, (-197260672 : ℚ) / 333, (515345152 : ℚ) / 185, (-1685079424 : ℚ) / 111, (16173581312 : ℚ) / 185;
  0, 0, 0, 0, (19768861 : ℚ) / 12120, (-569129951 : ℚ) / 72720, (2702605377 : ℚ) / 70700, (-3066958465 : ℚ) / 14544, (1556191630937 : ℚ) / 1272600;
  0, 0, 0, 0, 0, (8382207784939 : ℚ) / 18300317040, (-225091824914539 : ℚ) / 71167899600, (1894016477402519 : ℚ) / 91501585200, (-84978245428259591 : ℚ) / 640511096400;
  0, 0, 0, 0, 0, 0, (-199831309264187241613 : ℚ) / 60351896051560800, (4488687201168545832961 : ℚ) / 181055688154682400, (-6013804633262419466597 : ℚ) / 36211137630936480;
  0, 0, 0, 0, 0, 0, 0, (-594215643126789025658484763 : ℚ) / 17128397936930334995400, (366675806998465454135235167501 : ℚ) / 1027703876215820099724000;
  0, 0, 0, 0, 0, 0, 0, 0, (45201875743684818015679253923350829 : ℚ) / 1123067565509631258494536202070000
]
theorem q7_lu0 : q7SourceMatrixAtZeroExplicit = q7L0 * q7U0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [q7SourceMatrixAtZeroExplicit, q7L0, q7U0, Matrix.mul_apply, Fin.sum_univ_succ]

theorem q7_lu0_det : q7SourceMatrixAtZeroExplicit.det = (1824058729423489878071240450876107476590203 : ℚ) / 398580750000000 := by
  rw [q7_lu0, Matrix.det_mul]
  have hL : q7L0.IsLowerTriangular := by decide
  have hU : q7U0.IsUpperTriangular := by decide
  rw [Matrix.det_of_isLowerTriangular q7L0 hL, Matrix.det_of_isUpperTriangular hU]
  norm_num [q7L0, q7U0, Fin.prod_univ_succ]

def q7SourceMatrixAtZero : Matrix (Fin 9) (Fin 9) ℚ :=
  fun r c => (V.vSourceMatrix 1 (-7 : ℤ) r c).eval 0

theorem q7_source_eq_explicit :
    q7SourceMatrixAtZero = q7SourceMatrixAtZeroExplicit := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [q7SourceMatrixAtZero, q7SourceMatrixAtZeroExplicit,
      V.vSourceMatrix, V.vJIndex,
      V.vMatrixSize, V.vM, V.vS, V.vIIndexNat, V.vCEntry, V.vBEntry,
      V.vMomentB, V.vMomentT, V.vVEntry]

theorem q7SourceMatrixAtZero_det_eq_seed_eval :
    q7SourceMatrixAtZero.det =
      (V.vPolynomial 1 (-7 : ℤ)).eval 0 := by
  unfold q7SourceMatrixAtZero V.vPolynomial
  calc
    Matrix.det (fun r c =>
        (V.vSourceMatrix 1 (-7 : ℤ) r c).eval 0) =
        ((Polynomial.evalRingHom (0 : ℚ)).mapMatrix
          (V.vSourceMatrix 1 (-7 : ℤ))).det := by
      congr 1
    _ = (Polynomial.evalRingHom (0 : ℚ))
        ((V.vSourceMatrix 1 (-7 : ℤ)).det) :=
      (RingHom.map_det (Polynomial.evalRingHom (0 : ℚ))
        (V.vSourceMatrix 1 (-7 : ℤ))).symm

theorem q7_constant_eq :
    (V.vPolynomial 1 (-7 : ℤ)).coeff 0 = vSeedConstant 7 := by
  have hdet : q7SourceMatrixAtZero.det =
      (1824058729423489878071240450876107476590203 : ℚ) / 398580750000000 := by
    rw [q7_source_eq_explicit, q7_lu0_det]
  have heval : (V.vPolynomial 1 (-7 : ℤ)).eval 0 =
      (1824058729423489878071240450876107476590203 : ℚ) / 398580750000000 := by
    rw [← q7SourceMatrixAtZero_det_eq_seed_eval]
    exact hdet
  rw [Polynomial.coeff_zero_eq_eval_zero]
  simpa [vSeedConstant] using heval

end
end Li2Lean.B3
