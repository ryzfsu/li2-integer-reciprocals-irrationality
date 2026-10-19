/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Mathlib
import Li2Lean.B3.ActualFrobeniusProducer

/-!
# q = 3 seed constant/evaluation bridge

The explicit matrix below is the actual q = 3, `n = 1`, `T = 0` source
matrix.  Its determinant is certified by a rational LU factorization; no
Leibniz expansion of `Matrix.det` is used.  This is the finite E3 leaf from
v13 `nonvanishing.tex:146-198`.
-/

namespace Li2Lean.B3

noncomputable section

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

open Li2Lean

theorem q3SignedRange : SignedVBaseRange 3 := by
  constructor <;> norm_num [SignedVBaseRange]

def q3SourceMatrixAtZero : Matrix (Fin 9) (Fin 9) ℚ :=
  fun r c => (V.vSourceMatrix 1 (-3 : ℤ) r c).eval 0

def q3SourceMatrixAtZeroExplicit : Matrix (Fin 9) (Fin 9) ℚ := !![
  -12, 0, 36, -36, 84, -180, (2196 : ℚ) / 5, -1092, (19692 : ℚ) / 7;
  12, 36, 0, -108, 108, -252, 540, (-6588 : ℚ) / 5, 3276;
  -28, -36, -108, 0, 324, -324, 756, -1620, (19764 : ℚ) / 5;
  60, 84, 108, 324, 0, -972, 972, -2268, 4860;
  (7 : ℚ) / 2, (-11 : ℚ) / 4, (-31 : ℚ) / 3, (83 : ℚ) / 8, (-483 : ℚ) / 20, (12431 : ℚ) / 240, (-88437 : ℚ) / 700, (175929 : ℚ) / 560, (-14275729 : ℚ) / 17640;
  (-41 : ℚ) / 12, (-31 : ℚ) / 3, (301 : ℚ) / 36, (373 : ℚ) / 12, (-3727 : ℚ) / 120, (13051 : ℚ) / 180, (-260971 : ℚ) / 1680, (1592041 : ℚ) / 4200, (-14249689 : ℚ) / 15120;
  (97 : ℚ) / 12, (83 : ℚ) / 8, (373 : ℚ) / 12, (-1201 : ℚ) / 48, (-466 : ℚ) / 5, (5593 : ℚ) / 60, (-45671 : ℚ) / 210, (521977 : ℚ) / 1120, (-14328019 : ℚ) / 12600;
  (-1379 : ℚ) / 80, (-483 : ℚ) / 20, (-3727 : ℚ) / 120, (-466 : ℚ) / 5, (30041 : ℚ) / 400, (8389 : ℚ) / 30, (-39147 : ℚ) / 140, (182691 : ℚ) / 280, (-2818631 : ℚ) / 2016;
  (1 : ℚ) / 2, (1 : ℚ) / 3, (1 : ℚ) / 4, (1 : ℚ) / 5, (1 : ℚ) / 6, (1 : ℚ) / 7, (1 : ℚ) / 8, (1 : ℚ) / 9, (1 : ℚ) / 10]
def q3L0 : Matrix (Fin 9) (Fin 9) ℚ := !![
  1, 0, 0, 0, 0, 0, 0, 0, 0;
  -1, 1, 0, 0, 0, 0, 0, 0, 0;
  (7 : ℚ) / 3, -1, 1, 0, 0, 0, 0, 0, 0;
  -5, (7 : ℚ) / 3, (-17 : ℚ) / 13, 1, 0, 0, 0, 0, 0;
  (-7 : ℚ) / 24, (-11 : ℚ) / 144, (-35 : ℚ) / 1872, (-3821 : ℚ) / 125280, 1, 0, 0, 0, 0;
  (41 : ℚ) / 144, (-31 : ℚ) / 108, (-19 : ℚ) / 351, (-19 : ℚ) / 2349, (645703 : ℚ) / 1030695, 1, 0, 0, 0;
  (-97 : ℚ) / 144, (83 : ℚ) / 288, (-83 : ℚ) / 288, (-5213 : ℚ) / 83520, (514553 : ℚ) / 687130, (-10887547933 : ℚ) / 10379221358, 1, 0, 0;
  (1379 : ℚ) / 960, (-161 : ℚ) / 240, (14069 : ℚ) / 37440, (-45061 : ℚ) / 156600, (3933052 : ℚ) / 1717825, (225325609893 : ℚ) / 25948053395, (1312869644500584 : ℚ) / 4881666735643585, 1, 0;
  (-1 : ℚ) / 24, (1 : ℚ) / 108, (-17 : ℚ) / 1872, (-133 : ℚ) / 104400, (276258 : ℚ) / 1717825, (41164926834 : ℚ) / 181636373765, (-3248826580796864 : ℚ) / 34171667149505095, (-185910284130622635506 : ℚ) / 44790336632551184683533, 1]
def q3U0 : Matrix (Fin 9) (Fin 9) ℚ := !![
  -12, 0, 36, -36, 84, -180, (2196 : ℚ) / 5, -1092, (19692 : ℚ) / 7;
  0, 36, 36, -144, 192, -432, (4896 : ℚ) / 5, (-12048 : ℚ) / 5, (42624 : ℚ) / 7;
  0, 0, -156, -60, 320, -336, (3552 : ℚ) / 5, (-7408 : ℚ) / 5, (121728 : ℚ) / 35;
  0, 0, 0, (5220 : ℚ) / 13, (5076 : ℚ) / 13, (-16944 : ℚ) / 13, (117792 : ℚ) / 65, (-52560 : ℚ) / 13, (4215936 : ℚ) / 455;
  0, 0, 0, 0, (68713 : ℚ) / 2088, (-1664951 : ℚ) / 20880, (117833 : ℚ) / 812, (-9921959 : ℚ) / 29232, (2107603027 : ℚ) / 2557800;
  0, 0, 0, 0, 0, (5189610679 : ℚ) / 247366800, (-4285163987 : ℚ) / 115437840, (56601903431 : ℚ) / 577189200, (-15065832729551 : ℚ) / 60604866000;
  0, 0, 0, 0, 0, 0, (-976333347128717 : ℚ) / 29061819802400, (8945180069713831 : ℚ) / 87185459407200, (-7181600511573559 : ℚ) / 24411928634016;
  0, 0, 0, 0, 0, 0, 0, (-710957724326209280691 : ℚ) / 6834333429901019000, (13633384869688819223619 : ℚ) / 38272267207445706400;
  0, 0, 0, 0, 0, 0, 0, 0, (115446952178385645197847979 : ℚ) / 69673856983968509507718000]
theorem q3_lu0 : q3SourceMatrixAtZeroExplicit = q3L0 * q3U0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [q3SourceMatrixAtZeroExplicit, q3L0, q3U0, Matrix.mul_apply,
      Fin.sum_univ_succ]

theorem q3_lu0_det : q3SourceMatrixAtZeroExplicit.det =
    ((1039022569605470806780631811 : ℚ) / 9604000000000 : ℚ) := by
  rw [q3_lu0, Matrix.det_mul]
  have hL : q3L0.IsLowerTriangular := by decide
  have hU : q3U0.IsUpperTriangular := by decide
  rw [Matrix.det_of_isLowerTriangular q3L0 hL,
    Matrix.det_of_isUpperTriangular hU]
  norm_num [q3L0, q3U0, Fin.prod_univ_succ]

theorem q3SourceMatrixAtZero_det_eq_seed_eval :
    q3SourceMatrixAtZero.det =
      (V.vPolynomial 1 (-3 : ℤ)).eval 0 := by
  unfold q3SourceMatrixAtZero V.vPolynomial
  calc
    Matrix.det (fun r c =>
        (V.vSourceMatrix 1 (-3 : ℤ) r c).eval 0) =
        ((Polynomial.evalRingHom (0 : ℚ)).mapMatrix
          (V.vSourceMatrix 1 (-3 : ℤ))).det := by
      congr 1
    _ = (Polynomial.evalRingHom (0 : ℚ))
        ((V.vSourceMatrix 1 (-3 : ℤ)).det) :=
      (RingHom.map_det (Polynomial.evalRingHom (0 : ℚ))
        (V.vSourceMatrix 1 (-3 : ℤ))).symm

theorem q3_source_eq_explicit :
    q3SourceMatrixAtZero = q3SourceMatrixAtZeroExplicit := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [q3SourceMatrixAtZero, q3SourceMatrixAtZeroExplicit,
      V.vSourceMatrix, V.vJIndex,
      V.vMatrixSize, V.vM, V.vS, V.vIIndexNat, V.vCEntry, V.vBEntry,
      V.vMomentB, V.vMomentT, V.vVEntry]

theorem q3_constant_eq :
    (V.vPolynomial 1 (-3 : ℤ)).coeff 0 = vSeedConstant 3 := by
  have hdet : q3SourceMatrixAtZero.det =
      ((1039022569605470806780631811 : ℚ) / 9604000000000 : ℚ) := by
    rw [q3_source_eq_explicit, q3_lu0_det]
  have heval : (V.vPolynomial 1 (-3 : ℤ)).eval 0 =
      ((1039022569605470806780631811 : ℚ) / 9604000000000 : ℚ) := by
    rw [← q3SourceMatrixAtZero_det_eq_seed_eval]
    exact hdet
  rw [Polynomial.coeff_zero_eq_eval_zero]
  simpa [vSeedConstant] using heval

end
end Li2Lean.B3

#print axioms Li2Lean.B3.q3_lu0_det
#print axioms Li2Lean.B3.q3SourceMatrixAtZero_det_eq_seed_eval
#print axioms Li2Lean.B3.q3_constant_eq
