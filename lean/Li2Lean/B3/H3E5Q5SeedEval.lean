/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.B3.ActualFrobeniusProducer

/-!
# q = 5 seed constant/evaluation bridge

This file certifies the T = 0 q = 5 source determinant by an
explicit rational LU factorization.  The determinant/evaluation bridge
uses `Polynomial.evalRingHom` and `RingHom.map_det`, without unfolding
Leibniz's formula.
-/

namespace Li2Lean.B3
noncomputable section

set_option maxRecDepth 1000000
set_option maxHeartbeats 30000000

def q5SourceMatrixAtZeroExplicit : Matrix (Fin 9) (Fin 9) ℚ := !![
  -30, 0, 150, -300, 1050, -3900, 15630, -65100, (1953150 : ℚ) / 7;
  60, 150, 0, -750, 1500, -5250, 19500, -78150, 325500;
  -210, -300, -750, 0, 3750, -7500, 26250, -97500, 390750;
  780, 1050, 1500, 3750, 0, -18750, 37500, -131250, 487500;
  (11 : ℚ) / 2, (-19 : ℚ) / 4, (-82 : ℚ) / 3, (1313 : ℚ) / 24, (-34457 : ℚ) / 180, (11377 : ℚ) / 16, (-79791 : ℚ) / 28, (3988031 : ℚ) / 336, (-179475059 : ℚ) / 3528;
  (-131 : ℚ) / 12, (-82 : ℚ) / 3, (859 : ℚ) / 36, (547 : ℚ) / 4, (-10939 : ℚ) / 40, (34459 : ℚ) / 36, (-1194569 : ℚ) / 336, (2393737 : ℚ) / 168, (-179461283 : ℚ) / 3024;
  (1379 : ℚ) / 36, (1313 : ℚ) / 24, (547 : ℚ) / 4, (-17171 : ℚ) / 144, (-6837 : ℚ) / 10, (16409 : ℚ) / 12, (-301514 : ℚ) / 63, (11945711 : ℚ) / 672, (-35906041 : ℚ) / 504;
  (-34127 : ℚ) / 240, (-34457 : ℚ) / 180, (-10939 : ℚ) / 40, (-6837 : ℚ) / 10, (2146519 : ℚ) / 3600, (51278 : ℚ) / 15, (-2871563 : ℚ) / 420, (60302863 : ℚ) / 2520, (-895928101 : ℚ) / 10080;
  (1 : ℚ) / 2, (1 : ℚ) / 3, (1 : ℚ) / 4, (1 : ℚ) / 5, (1 : ℚ) / 6, (1 : ℚ) / 7, (1 : ℚ) / 8, (1 : ℚ) / 9, (1 : ℚ) / 10
]
def q5L0 : Matrix (Fin 9) (Fin 9) ℚ := !![
  1, 0, 0, 0, 0, 0, 0, 0, 0;
  -2, 1, 0, 0, 0, 0, 0, 0, 0;
  7, -2, 1, 0, 0, 0, 0, 0, 0;
  -26, 7, (-11 : ℚ) / 4, 1, 0, 0, 0, 0, 0;
  (-11 : ℚ) / 60, (-19 : ℚ) / 600, (-29 : ℚ) / 3600, (-383 : ℚ) / 30000, 1, 0, 0, 0, 0;
  (131 : ℚ) / 360, (-41 : ℚ) / 225, (-431 : ℚ) / 21600, (-217 : ℚ) / 67500, (39907 : ℚ) / 107018, 1, 0, 0, 0;
  (-1379 : ℚ) / 1080, (1313 : ℚ) / 3600, (-7879 : ℚ) / 43200, (-5729 : ℚ) / 180000, (68852 : ℚ) / 53509, (-338830151 : ℚ) / 365077060, 1, 0, 0;
  (34127 : ℚ) / 7200, (-34457 : ℚ) / 27000, (433151 : ℚ) / 864000, (-984661 : ℚ) / 5400000, (2149227 : ℚ) / 1070180, (8167142991 : ℚ) / 456346325, (-8630565383468187 : ℚ) / 2747073255001265, 1, 0;
  (-1 : ℚ) / 60, (1 : ℚ) / 450, (-1 : ℚ) / 576, (-341 : ℚ) / 450000, (22509 : ℚ) / 267545, (4829509098 : ℚ) / 79860606875, (-13755046593904416 : ℚ) / 480737819625221375, (3852550360910630745368 : ℚ) / 2954051125397150340057125, 1
]
def q5U0 : Matrix (Fin 9) (Fin 9) ℚ := !![
  -30, 0, 150, -300, 1050, -3900, 15630, -65100, (1953150 : ℚ) / 7;
  0, 150, 300, -1350, 3600, -13050, 50760, -208350, (6184800 : ℚ) / 7;
  0, 0, -1200, -600, 3600, -6300, 18360, -58500, (1432800 : ℚ) / 7;
  0, 0, 0, 3750, 12000, -46125, 139050, -526275, (14841000 : ℚ) / 7;
  0, 0, 0, 0, (53509 : ℚ) / 180, (-5284 : ℚ) / 5, (4964857 : ℚ) / 1400, (-29092639 : ℚ) / 2100, (1005077537 : ℚ) / 17640;
  0, 0, 0, 0, 0, (456346325 : ℚ) / 3852648, (-7525763773 : ℚ) / 14982520, (102410891507 : ℚ) / 44947560, (-827178776287 : ℚ) / 80905608;
  0, 0, 0, 0, 0, 0, (-549414651000253 : ℚ) / 919994191200, (2911011547885009 : ℚ) / 919994191200, (-8397819044141873 : ℚ) / 551996514720;
  0, 0, 0, 0, 0, 0, 0, (-3376058429025314674351 : ℚ) / 1107619936416510048, (54000728857561990965575 : ℚ) / 2584446518305190112;
  0, 0, 0, 0, 0, 0, 0, 0, (2580514312373792571606402323 : ℚ) / 231597608231136586660478600
]
theorem q5_lu0 : q5SourceMatrixAtZeroExplicit = q5L0 * q5U0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [q5SourceMatrixAtZeroExplicit, q5L0, q5U0, Matrix.mul_apply, Fin.sum_univ_succ]

theorem q5_lu0_det : q5SourceMatrixAtZeroExplicit.det = (40320536130840508931350036296875 : ℚ) / 2788079616 := by
  rw [q5_lu0, Matrix.det_mul]
  have hL : q5L0.IsLowerTriangular := by decide
  have hU : q5U0.IsUpperTriangular := by decide
  rw [Matrix.det_of_isLowerTriangular q5L0 hL, Matrix.det_of_isUpperTriangular hU]
  norm_num [q5L0, q5U0, Fin.prod_univ_succ]

def q5SourceMatrixAtZero : Matrix (Fin 9) (Fin 9) ℚ :=
  fun r c => (V.vSourceMatrix 1 (-5 : ℤ) r c).eval 0

theorem q5_source_eq_explicit :
    q5SourceMatrixAtZero = q5SourceMatrixAtZeroExplicit := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [q5SourceMatrixAtZero, q5SourceMatrixAtZeroExplicit,
      V.vSourceMatrix, V.vJIndex,
      V.vMatrixSize, V.vM, V.vS, V.vIIndexNat, V.vCEntry, V.vBEntry,
      V.vMomentB, V.vMomentT, V.vVEntry]

theorem q5SourceMatrixAtZero_det_eq_seed_eval :
    q5SourceMatrixAtZero.det =
      (V.vPolynomial 1 (-5 : ℤ)).eval 0 := by
  unfold q5SourceMatrixAtZero V.vPolynomial
  calc
    Matrix.det (fun r c =>
        (V.vSourceMatrix 1 (-5 : ℤ) r c).eval 0) =
        ((Polynomial.evalRingHom (0 : ℚ)).mapMatrix
          (V.vSourceMatrix 1 (-5 : ℤ))).det := by
      congr 1
    _ = (Polynomial.evalRingHom (0 : ℚ))
        ((V.vSourceMatrix 1 (-5 : ℤ)).det) :=
      (RingHom.map_det (Polynomial.evalRingHom (0 : ℚ))
        (V.vSourceMatrix 1 (-5 : ℤ))).symm

theorem q5_constant_eq :
    (V.vPolynomial 1 (-5 : ℤ)).coeff 0 = vSeedConstant 5 := by
  have hdet : q5SourceMatrixAtZero.det =
      (40320536130840508931350036296875 : ℚ) / 2788079616 := by
    rw [q5_source_eq_explicit, q5_lu0_det]
  have heval : (V.vPolynomial 1 (-5 : ℤ)).eval 0 =
      (40320536130840508931350036296875 : ℚ) / 2788079616 := by
    rw [← q5SourceMatrixAtZero_det_eq_seed_eval]
    exact hdet
  rw [Polynomial.coeff_zero_eq_eval_zero]
  simpa [vSeedConstant] using heval

end
end Li2Lean.B3

#print axioms Li2Lean.B3.q5_lu0_det
#print axioms Li2Lean.B3.q5SourceMatrixAtZero_det_eq_seed_eval
#print axioms Li2Lean.B3.q5_constant_eq
