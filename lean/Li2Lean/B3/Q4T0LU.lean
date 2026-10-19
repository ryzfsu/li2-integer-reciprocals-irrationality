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

def q4SourceMatrixAtZeroExplicit : Matrix (Fin 9) (Fin 9) ℚ := !![
  -20, 0, 80, -120, (1040 : ℚ) / 3, -1020, 3280, -10920, (262160 : ℚ) / 7;
  30, 80, 0, -320, 480, (-4160 : ℚ) / 3, 4080, -13120, 43680;
  (-260 : ℚ) / 3, -120, -320, 0, 1280, -1920, (16640 : ℚ) / 3, -16320, 52480;
  255, (1040 : ℚ) / 3, 480, 1280, 0, -5120, 7680, (-66560 : ℚ) / 3, 65280;
  (9 : ℚ) / 2, (-15 : ℚ) / 4, (-107 : ℚ) / 6, (643 : ℚ) / 24, (-6961 : ℚ) / 90, (13657 : ℚ) / 60, (-768497 : ℚ) / 1050, (12281147 : ℚ) / 5040, (-18427268 : ℚ) / 2205;
  (-20 : ℚ) / 3, (-107 : ℚ) / 6, (136 : ℚ) / 9, (857 : ℚ) / 12, (-1071 : ℚ) / 10, (9283 : ℚ) / 30, (-95594 : ℚ) / 105, (4098709 : ℚ) / 1400, (-36843301 : ℚ) / 3780;
  (697 : ℚ) / 36, (643 : ℚ) / 24, (857 : ℚ) / 12, (-8695 : ℚ) / 144, (-17137 : ℚ) / 60, (51413 : ℚ) / 120, (-519833 : ℚ) / 420, (12236137 : ℚ) / 3360, (-73776587 : ℚ) / 6300;
  (-3413 : ℚ) / 60, (-6961 : ℚ) / 90, (-1071 : ℚ) / 10, (-17137 : ℚ) / 60, (217411 : ℚ) / 900, (2285 : ℚ) / 2, (-71977 : ℚ) / 42, (831737 : ℚ) / 168, (-7341671 : ℚ) / 504;
  (1 : ℚ) / 2, (1 : ℚ) / 3, (1 : ℚ) / 4, (1 : ℚ) / 5, (1 : ℚ) / 6, (1 : ℚ) / 7, (1 : ℚ) / 8, (1 : ℚ) / 9, (1 : ℚ) / 10
]
def q4L0 : Matrix (Fin 9) (Fin 9) ℚ := !![
  1, 0, 0, 0, 0, 0, 0, 0, 0;
  (-3 : ℚ) / 2, 1, 0, 0, 0, 0, 0, 0, 0;
  (13 : ℚ) / 3, (-3 : ℚ) / 2, 1, 0, 0, 0, 0, 0, 0;
  (-51 : ℚ) / 4, (13 : ℚ) / 3, (-147 : ℚ) / 73, 1, 0, 0, 0, 0, 0;
  (-9 : ℚ) / 40, (-3 : ℚ) / 64, (-139 : ℚ) / 11680, (-46223 : ℚ) / 2546560, 1, 0, 0, 0, 0;
  (1 : ℚ) / 3, (-107 : ℚ) / 480, (-547 : ℚ) / 17520, (-6327 : ℚ) / 1273280, (32764934 : ℚ) / 68151861, 1, 0, 0, 0;
  (-697 : ℚ) / 720, (643 : ℚ) / 1920, (-15649 : ℚ) / 70080, (-635557 : ℚ) / 15279360, (318127009 : ℚ) / 318042018, (-144016971663 : ℚ) / 133559873342, 1, 0, 0;
  (3413 : ℚ) / 1200, (-6961 : ℚ) / 7200, (13117 : ℚ) / 29200, (-133207 : ℚ) / 596850, (247616354 : ℚ) / 113586435, (1291984867707 : ℚ) / 95399909530, (-18394796797618835622 : ℚ) / 12649131079350768265, 1, 0;
  (-1 : ℚ) / 40, (1 : ℚ) / 240, (-21 : ℚ) / 5840, (-13523 : ℚ) / 12732800, (5770921 : ℚ) / 53007003, (122005019277 : ℚ) / 1068478986736, (-969363736764596901 : ℚ) / 20238609726961229224, (1350437352013108810702535 : ℚ) / 1476949674357253695827975712, 1
]
def q4U0 : Matrix (Fin 9) (Fin 9) ℚ := !![
  -20, 0, 80, -120, (1040 : ℚ) / 3, -1020, 3280, -10920, (262160 : ℚ) / 7;
  0, 80, 120, -500, 1000, (-8750 : ℚ) / 3, 9000, -29500, (699000 : ℚ) / 7;
  0, 0, (-1460 : ℚ) / 3, -230, (11500 : ℚ) / 9, -1875, (14500 : ℚ) / 3, -13250, (839500 : ℚ) / 21;
  0, 0, 0, (318320 : ℚ) / 219, (194160 : ℚ) / 73, (-6085000 : ℚ) / 657, (1477000 : ℚ) / 73, (-13198000 : ℚ) / 219, (1334000 : ℚ) / 7;
  0, 0, 0, 0, (17669001 : ℚ) / 159160, (-942626149 : ℚ) / 2864880, (9500581557 : ℚ) / 11141200, (-53236522957 : ℚ) / 20054160, (26504714773 : ℚ) / 3051720;
  0, 0, 0, 0, 0, (9539990953 : ℚ) / 180401985, (-827058706717 : ℚ) / 5300700300, (119085715854149 : ℚ) / 214678362150, (-68996761387303 : ℚ) / 35358789060;
  0, 0, 0, 0, 0, 0, (-2529826215870153653 : ℚ) / 14304262434928200, (15833725855751592307 : ℚ) / 21456393652392300, (-50096554991141455249 : ℚ) / 17669971243146600;
  0, 0, 0, 0, 0, 0, 0, (-4395683554634683618535642 : ℚ) / 6640793816659153339125, (474462881026656087073567778 : ℚ) / 139456670149842220121625;
  0, 0, 0, 0, 0, 0, 0, 0, (7832593865226972397808003345441 : ℚ) / 1628337015978872199650343222480
]
theorem q4_lu0 : q4SourceMatrixAtZeroExplicit = q4L0 * q4U0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [q4SourceMatrixAtZeroExplicit, q4L0, q4U0, Matrix.mul_apply, Fin.sum_univ_succ]

theorem q4_lu0_det : q4SourceMatrixAtZeroExplicit.det = (62660750921815779182464026763528 : ℚ) / 16747366663125 := by
  rw [q4_lu0, Matrix.det_mul]
  have hL : q4L0.IsLowerTriangular := by decide
  have hU : q4U0.IsUpperTriangular := by decide
  rw [Matrix.det_of_isLowerTriangular q4L0 hL, Matrix.det_of_isUpperTriangular hU]
  norm_num [q4L0, q4U0, Fin.prod_univ_succ]

def q4SourceMatrixAtZero : Matrix (Fin 9) (Fin 9) ℚ :=
  fun r c => (V.vSourceMatrix 1 (-4 : ℤ) r c).eval 0

theorem q4_source_eq_explicit :
    q4SourceMatrixAtZero = q4SourceMatrixAtZeroExplicit := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [q4SourceMatrixAtZero, q4SourceMatrixAtZeroExplicit,
      V.vSourceMatrix, V.vJIndex,
      V.vMatrixSize, V.vM, V.vS, V.vIIndexNat, V.vCEntry, V.vBEntry,
      V.vMomentB, V.vMomentT, V.vVEntry]

theorem q4SourceMatrixAtZero_det_eq_seed_eval :
    q4SourceMatrixAtZero.det =
      (V.vPolynomial 1 (-4 : ℤ)).eval 0 := by
  unfold q4SourceMatrixAtZero V.vPolynomial
  calc
    Matrix.det (fun r c =>
        (V.vSourceMatrix 1 (-4 : ℤ) r c).eval 0) =
        ((Polynomial.evalRingHom (0 : ℚ)).mapMatrix
          (V.vSourceMatrix 1 (-4 : ℤ))).det := by
      congr 1
    _ = (Polynomial.evalRingHom (0 : ℚ))
        ((V.vSourceMatrix 1 (-4 : ℤ)).det) :=
      (RingHom.map_det (Polynomial.evalRingHom (0 : ℚ))
        (V.vSourceMatrix 1 (-4 : ℤ))).symm

theorem q4_constant_eq :
    (V.vPolynomial 1 (-4 : ℤ)).coeff 0 = vSeedConstant 4 := by
  have hdet : q4SourceMatrixAtZero.det =
      (62660750921815779182464026763528 : ℚ) / 16747366663125 := by
    rw [q4_source_eq_explicit, q4_lu0_det]
  have heval : (V.vPolynomial 1 (-4 : ℤ)).eval 0 =
      (62660750921815779182464026763528 : ℚ) / 16747366663125 := by
    rw [← q4SourceMatrixAtZero_det_eq_seed_eval]
    exact hdet
  rw [Polynomial.coeff_zero_eq_eval_zero]
  simpa [vSeedConstant] using heval

end
end Li2Lean.B3
