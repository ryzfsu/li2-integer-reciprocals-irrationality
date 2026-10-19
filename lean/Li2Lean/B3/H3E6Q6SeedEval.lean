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

def q6SourceMatrixAtZeroExplicit : Matrix (Fin 9) (Fin 9) ℚ := !![
  -42, 0, 252, -630, 2604, -11655, (279972 : ℚ) / 5, -279930, 1439676;
  105, 252, 0, -1512, 3780, -15624, 69930, (-1679832 : ℚ) / 5, 1679580;
  -434, -630, -1512, 0, 9072, -22680, 93744, -419580, (10078992 : ℚ) / 5;
  (3885 : ℚ) / 2, 2604, 3780, 9072, 0, -54432, 136080, -562464, 2517480;
  (13 : ℚ) / 2, (-23 : ℚ) / 4, (-233 : ℚ) / 6, (777 : ℚ) / 8, (-2007 : ℚ) / 5, (53899 : ℚ) / 30, (-3021049 : ℚ) / 350, (24164787 : ℚ) / 560, (-1957396397 : ℚ) / 8820;
  (-97 : ℚ) / 6, (-233 : ℚ) / 6, (623 : ℚ) / 18, (2797 : ℚ) / 12, (-34961 : ℚ) / 60, (216761 : ℚ) / 90, (-1131874 : ℚ) / 105, (217515703 : ℚ) / 4200, (-1957347467 : ℚ) / 7560;
  (803 : ℚ) / 12, (777 : ℚ) / 8, (2797 : ℚ) / 12, (-9965 : ℚ) / 48, (-27969 : ℚ) / 20, (419537 : ℚ) / 120, (-6069293 : ℚ) / 420, (72439971 : ℚ) / 1120, (-489410288 : ℚ) / 1575;
  (-11977 : ℚ) / 40, (-2007 : ℚ) / 5, (-34961 : ℚ) / 60, (-27969 : ℚ) / 20, (249133 : ℚ) / 200, (125861 : ℚ) / 15, (-587351 : ℚ) / 28, (24277179 : ℚ) / 280, (-391175821 : ℚ) / 1008;
  (1 : ℚ) / 2, (1 : ℚ) / 3, (1 : ℚ) / 4, (1 : ℚ) / 5, (1 : ℚ) / 6, (1 : ℚ) / 7, (1 : ℚ) / 8, (1 : ℚ) / 9, (1 : ℚ) / 10
]
def q6L0 : Matrix (Fin 9) (Fin 9) ℚ := !![
  1, 0, 0, 0, 0, 0, 0, 0, 0;
  (-5 : ℚ) / 2, 1, 0, 0, 0, 0, 0, 0, 0;
  (31 : ℚ) / 3, (-5 : ℚ) / 2, 1, 0, 0, 0, 0, 0, 0;
  (-185 : ℚ) / 4, (31 : ℚ) / 3, (-425 : ℚ) / 121, 1, 0, 0, 0, 0, 0;
  (-13 : ℚ) / 84, (-23 : ℚ) / 1008, (-349 : ℚ) / 60984, (-225707 : ℚ) / 22047984, 1, 0, 0, 0, 0;
  (97 : ℚ) / 252, (-233 : ℚ) / 1512, (-1249 : ℚ) / 91476, (-36181 : ℚ) / 16535988, (1573937642 : ℚ) / 5587551993, 1, 0, 0, 0;
  (-803 : ℚ) / 504, (37 : ℚ) / 96, (-18805 : ℚ) / 121968, (-172369 : ℚ) / 6299424, (6010283491 : ℚ) / 3725034662, (-115233812950393 : ℚ) / 162207318531332, 1, 0, 0;
  (1711 : ℚ) / 240, (-223 : ℚ) / 140, (268 : ℚ) / 495, (-16995187 : ℚ) / 110239920, (16364313992 : ℚ) / 9312586655, (8706385409321367 : ℚ) / 405518296328330, (-8566312390317856486668 : ℚ) / 1746491756345626563035, 1, 0;
  (-1 : ℚ) / 84, (1 : ℚ) / 756, (-29 : ℚ) / 30492, (-21127 : ℚ) / 36746640, (128873415 : ℚ) / 1862517331, (75157074641037 : ℚ) / 2270902459438648, (-92433646236789977167 : ℚ) / 4890176917767754376498, (3586183604872895318189534395 : ℚ) / 3443822892010700867968452195372, 1
]
def q6U0 : Matrix (Fin 9) (Fin 9) ℚ := !![
  -42, 0, 252, -630, 2604, -11655, (279972 : ℚ) / 5, -279930, 1439676;
  0, 252, 630, -3087, 10290, (-89523 : ℚ) / 2, 209916, (-5178957 : ℚ) / 5, 5278770;
  0, 0, -2541, (-2415 : ℚ) / 2, 7889, (-56595 : ℚ) / 4, (199626 : ℚ) / 5, (-232897 : ℚ) / 2, (1680357 : ℚ) / 5;
  0, 0, 0, (918666 : ℚ) / 121, (5059530 : ℚ) / 121, (-1986999 : ℚ) / 11, (84327579 : ℚ) / 121, (-1945112526 : ℚ) / 605, (1904010150 : ℚ) / 121;
  0, 0, 0, 0, (1862517331 : ℚ) / 2624760, (-15531330829 : ℚ) / 5249520, (248793418603 : ℚ) / 20414800, (-2108687100377 : ℚ) / 36746640, (1589985084689 : ℚ) / 5591880;
  0, 0, 0, 0, 0, (40551829632833 : ℚ) / 167626559790, (-10543770912293923 : ℚ) / 7822572790200, (9731461698455243 : ℚ) / 1303762131700, (-1336661825053565867 : ℚ) / 32854805718840;
  0, 0, 0, 0, 0, 0, (-49899764467017901801 : ℚ) / 32441463706266400, (3357004784633140465747 : ℚ) / 340635368915797200, (-38687079714650921354741 : ℚ) / 681270737831594400;
  0, 0, 0, 0, 0, 0, 0, (-13665963857185320904636715061 : ℚ) / 1222544229441938594124500, (117116392383256211771961065391 : ℚ) / 1222544229441938594124500;
  0, 0, 0, 0, 0, 0, 0, 0, (41800273111348852260110895358501547 : ℚ) / 1874970241205826028116157306369200
]
theorem q6_lu0 : q6SourceMatrixAtZeroExplicit = q6L0 * q6U0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [q6SourceMatrixAtZeroExplicit, q6L0, q6U0, Matrix.mul_apply, Fin.sum_univ_succ]

theorem q6_lu0_det : q6SourceMatrixAtZeroExplicit.det = (376202458002139670340998058226513923 : ℚ) / 28000000000 := by
  rw [q6_lu0, Matrix.det_mul]
  have hL : q6L0.IsLowerTriangular := by decide
  have hU : q6U0.IsUpperTriangular := by decide
  rw [Matrix.det_of_isLowerTriangular q6L0 hL, Matrix.det_of_isUpperTriangular hU]
  norm_num [q6L0, q6U0, Fin.prod_univ_succ]

def q6SourceMatrixAtZero : Matrix (Fin 9) (Fin 9) ℚ :=
  fun r c => (V.vSourceMatrix 1 (-6 : ℤ) r c).eval 0

theorem q6_source_eq_explicit :
    q6SourceMatrixAtZero = q6SourceMatrixAtZeroExplicit := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [q6SourceMatrixAtZero, q6SourceMatrixAtZeroExplicit,
      V.vSourceMatrix, V.vJIndex,
      V.vMatrixSize, V.vM, V.vS, V.vIIndexNat, V.vCEntry, V.vBEntry,
      V.vMomentB, V.vMomentT, V.vVEntry]

theorem q6SourceMatrixAtZero_det_eq_seed_eval :
    q6SourceMatrixAtZero.det =
      (V.vPolynomial 1 (-6 : ℤ)).eval 0 := by
  unfold q6SourceMatrixAtZero V.vPolynomial
  calc
    Matrix.det (fun r c =>
        (V.vSourceMatrix 1 (-6 : ℤ) r c).eval 0) =
        ((Polynomial.evalRingHom (0 : ℚ)).mapMatrix
          (V.vSourceMatrix 1 (-6 : ℤ))).det := by
      congr 1
    _ = (Polynomial.evalRingHom (0 : ℚ))
        ((V.vSourceMatrix 1 (-6 : ℤ)).det) :=
      (RingHom.map_det (Polynomial.evalRingHom (0 : ℚ))
        (V.vSourceMatrix 1 (-6 : ℤ))).symm

theorem q6_constant_eq :
    (V.vPolynomial 1 (-6 : ℤ)).coeff 0 = vSeedConstant 6 := by
  have hdet : q6SourceMatrixAtZero.det =
      (376202458002139670340998058226513923 : ℚ) / 28000000000 := by
    rw [q6_source_eq_explicit, q6_lu0_det]
  have heval : (V.vPolynomial 1 (-6 : ℤ)).eval 0 =
      (376202458002139670340998058226513923 : ℚ) / 28000000000 := by
    rw [← q6SourceMatrixAtZero_det_eq_seed_eval]
    exact hdet
  rw [Polynomial.coeff_zero_eq_eval_zero]
  simpa [vSeedConstant] using heval

end
end Li2Lean.B3

#print axioms Li2Lean.B3.q6_lu0_det
#print axioms Li2Lean.B3.q6SourceMatrixAtZero_det_eq_seed_eval
#print axioms Li2Lean.B3.q6_constant_eq
