/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/

import Mathlib
import Li2Lean.AllN.P0ActualTowerProducer
import Li2Lean.P0.PositiveTower.SeedTables345

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

/-!
# Positive P0 tower seed checks for q = 3, 4, 5

This module records the finite integer data used by the q-specific tower
stubs.  The tables are kept as `Int`/`Nat` lists, and all finite checks below
are Boolean checks over those lists.  The source-to-table equalities remain
named proof obligations (`tower_q3_seed_residue`, etc.); they are not hidden
inside a data-bearing structure.

The rows are generated from the M = 4 source matrix in
the proof plan and use the v13 auxiliary
primes 17, 53, and 11.  q = 5 and q = 7 both use p = 11; the base-unit
checks below record that 11 divides neither 5 nor 4.
-/

namespace Li2Lean.P0.PositiveTower.SeedChecks345

noncomputable section

open Li2Lean.P0.PositiveBase
open Li2Lean.P0.PositiveTower.SeedTables345

/-! ## Fixed q = 3, 4, 5 data -/

def towerPrime : ℕ → ℕ
  | 3 => 17
  | 4 => 53
  | 5 => 11
  | _ => 0

def numTable : ℕ → List (List Int)
  | 3 => num3
  | 4 => num4
  | 5 => num5
  | _ => []

def denTable : ℕ → List (List Nat)
  | 3 => den3
  | 4 => den4
  | 5 => den5
  | _ => []

def residueTable : ℕ → List (List Nat)
  | 3 => res3
  | 4 => res4
  | 5 => res5
  | _ => []

def inverseTable : ℕ → List (List Nat)
  | 3 => inv3
  | 4 => inv4
  | 5 => inv5
  | _ => []

def getInt (L : List (List Int)) (i j : ℕ) : Int :=
  (L.getD i []).getD j 0

def getNat (L : List (List Nat)) (i j : ℕ) : Nat :=
  (L.getD i []).getD j 0

/-! ## Pure integer Boolean checks -/

/-- Every denominator is a p-unit and every numerator has the listed residue. -/
def residueCheck (q : ℕ) : Bool :=
  let p := towerPrime q
  (List.range 8).all fun i => (List.range 8).all fun j =>
    getNat (denTable q) i j % p != 0 &&
      (getInt (numTable q) i j -
        (getNat (residueTable q) i j : Int) *
          (getNat (denTable q) i j : Int)) % (p : Int) == 0

/-- The listed inverse is a right inverse modulo the listed prime. -/
def inverseCheck (q : ℕ) : Bool :=
  let p := towerPrime q
  (List.range 8).all fun i => (List.range 8).all fun j =>
    ((List.range 8).foldl
      (fun s k => s + getNat (residueTable q) i k *
        getNat (inverseTable q) k j) 0) % p ==
      (if i = j then 1 else 0)

theorem residueCheck_q3 : residueCheck 3 = true := by decide
theorem residueCheck_q4 : residueCheck 4 = true := by decide
theorem residueCheck_q5 : residueCheck 5 = true := by decide

theorem inverseCheck_q3 : inverseCheck 3 = true := by decide
theorem inverseCheck_q4 : inverseCheck 4 = true := by decide
theorem inverseCheck_q5 : inverseCheck 5 = true := by decide

/-! ## Prime and base-unit checks -/

theorem q3_prime : Nat.Prime (towerPrime 3) := by norm_num [towerPrime]
theorem q4_prime : Nat.Prime (towerPrime 4) := by norm_num [towerPrime]
theorem q5_prime : Nat.Prime (towerPrime 5) := by norm_num [towerPrime]

theorem q3_base_conditions :
    10 < towerPrime 3 ∧
      ¬ (towerPrime 3 : ℤ) ∣ (3 : ℤ) ∧
      ¬ (towerPrime 3 : ℤ) ∣ (3 : ℤ) - 1 := by
  norm_num [towerPrime]

theorem q4_base_conditions :
    10 < towerPrime 4 ∧
      ¬ (towerPrime 4 : ℤ) ∣ (4 : ℤ) ∧
      ¬ (towerPrime 4 : ℤ) ∣ (4 : ℤ) - 1 := by
  norm_num [towerPrime]

theorem q5_base_conditions :
    10 < towerPrime 5 ∧
      ¬ (towerPrime 5 : ℤ) ∣ (5 : ℤ) ∧
      ¬ (towerPrime 5 : ℤ) ∣ (5 : ℤ) - 1 := by
  norm_num [towerPrime]

/-! ## Concrete matrix views -/

def listMat (p : ℕ) (L : List (List Nat)) :
    Matrix (Fin 8) (Fin 8) (ZMod p) :=
  fun i j => (getNat L i j : ZMod p)

def residueMatrix (q : ℕ) :
    Matrix (Fin 8) (Fin 8) (ZMod (towerPrime q)) :=
  listMat (towerPrime q) (residueTable q)

def inverseMatrix (q : ℕ) :
    Matrix (Fin 8) (Fin 8) (ZMod (towerPrime q)) :=
  listMat (towerPrime q) (inverseTable q)

/-! A denominator-explicit rational residue.  This is the same expression as
`Rat.cast_def`, but does not require a prime instance merely to state a
finite certificate. -/

def ratResidue (p : ℕ) (x : ℚ) : ZMod p :=
  (x.num : ZMod p) * (x.den : ZMod p)⁻¹

/-! ## Named q-specific source obligations -/

def q3InRange : InRange (3 : ℤ) := by norm_num [InRange]
def q4InRange : InRange (4 : ℤ) := by norm_num [InRange]
def q5InRange : InRange (5 : ℤ) := by norm_num [InRange]

/-- q = 3 source seed residue; the integer table gives the target `12`. -/
theorem tower_q3_seed_residue :
    ratResidue 17 (p0SourceEvalQ (family (3 : ℤ) q3InRange) 4 0) =
      (12 : ZMod 17) := by
  let A : Matrix (Fin 8) (Fin 8) ℚ :=
    fun i j => (getInt num3 i.val j.val : ℚ) /
      (getNat den3 i.val j.val : ℚ)
  let L : Matrix (Fin 8) (Fin 8) ℚ := !![
    1, 0, 0, 0, 0, 0, 0, 0;
    53/16, 1, 0, 0, 0, 0, 0, 0;
    269/24, 1486/645, 1, 0, 0, 0, 0, 0;
    607/16, 1253/215, 7911/314, 1, 0, 0, 0, 0;
    13/32, -211/1290, 4141/3768, 839197/17418456, 1, 0, 0, 0;
    43/32, 523/1290, 17033/15072, 1794475/34836912,
      1335355943/981567658, 1, 0, 0;
    1309/288, 241/258, 575/1413, -552283/104510736,
      1663618622/1472351487, 22663184360692/6260282896629, 1, 0;
    1969/128, 12193/5160, 615943/60288, 56508239/139347648,
      -5164830337/1963135316, 44353603018523/4173521931086,
      252821235298931745/40446539269562588, 1]
  let U : Matrix (Fin 8) (Fin 8) ℚ := !![
    -8, -15/2, -45, -261/2, -402, -2547/2, -20403/5, -26241/2;
    0, -645/32, 1881/16, 6921/32, 6009/8, 81135/32,
      674199/80, 4436169/160;
    0, 0, 3768/215, 181224/215, 393504/215, 258684/43,
      21077352/1075, 68333496/1075;
    0, 0, 0, -2903076/157, -5602380/157, -19141038/157,
      -62467992/157, -1013564364/785;
    0, 0, 0, 0, -490783829/2903076, -6230094287/19353840,
      -6027142637/6048075, -15783138901/5080383;
    0, 0, 0, 0, 0, -6260282896629/78525412640,
      -14910466372041/49078382900, -187526993912969/171774340150;
    0, 0, 0, 0, 0, 0, 10111634817390647/104338048277150,
      2427522019301651389/4382198027640300;
    0, 0, 0, 0, 0, 0, 0,
      -152226465442226939391/4044653926956258800]
  have hEntries :
      (fun i j : Fin 8 =>
        (p0MatrixQ (3 : ℚ) 4 i j).eval (0 : ℚ)) = A := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [A, getInt, getNat, num3, den3,
        p0MatrixQ, p0CQ, p0BQ, p0AQ, p0UQ,
        p0TQ, p0BQQ, p0Q, Nat.choose,
        Finset.sum_range_succ]
  have hEvalDet :
      (Matrix.det (p0MatrixQ (3 : ℚ) 4)).eval (0 : ℚ) =
        Matrix.det (fun i j : Fin 8 =>
          (p0MatrixQ (3 : ℚ) 4 i j).eval (0 : ℚ)) := by
    have h := RingHom.map_det (Polynomial.evalRingHom (0 : ℚ))
      (p0MatrixQ (3 : ℚ) 4)
    change (Matrix.det (p0MatrixQ (3 : ℚ) 4)).eval (0 : ℚ) =
      Matrix.det (fun i j : Fin 8 =>
        (p0MatrixQ (3 : ℚ) 4 i j).eval (0 : ℚ)) at h
    exact h
  have hSource :
      p0SourceEvalQ (family (3 : ℤ) q3InRange) 4 0 =
        A.det := by
    change (p0CanonicalPolynomial (3 : ℤ) 4).eval (0 : ℚ) =
      A.det
    simp only [p0CanonicalPolynomial,
      if_pos (by decide : 4 ∣ (4 : ℕ))]
    norm_num only [Int.cast_ofNat]
    rw [hEvalDet, hEntries]
  have hLU : L * U = A := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [L, U, A, getInt, getNat,
        num3, den3, Matrix.mul_apply, Fin.sum_univ_succ, List.getD]
  have hL : L.IsLowerTriangular := by
    dsimp [L]
    decide
  have hU : U.IsUpperTriangular := by
    dsimp [U]
    decide
  have hDet :
      A.det = (4110114566940127363557 / 1600000 : ℚ) := by
    rw [← hLU, Matrix.det_mul,
      Matrix.det_of_isLowerTriangular L hL,
      Matrix.det_of_isUpperTriangular hU]
    norm_num [L, U, Fin.prod_univ_succ]
  rw [hSource, hDet]
  norm_num [ratResidue]
  change ((4110114566940127363557 : Nat) : ZMod 17) *
    ((1600000 : Nat) : ZMod 17)⁻¹ = 12
  rw [← ZMod.natCast_mod 4110114566940127363557 17,
    ← ZMod.natCast_mod 1600000 17]
  norm_num
  change ((13 : Int) : ZMod 17) * (Nat.gcdA 11 17 : ZMod 17) = 12
  norm_num [Nat.gcdA, Nat.xgcd, Nat.xgcdAux, Nat.strongRec_eq]
  change ((-39 : Int) : ZMod 17) = ((12 : Int) : ZMod 17)
  rw [ZMod.intCast_eq_intCast_iff']
  norm_num

/-- q = 4 source seed residue; the integer table gives the target `51`. -/
theorem tower_q4_seed_residue :
    ratResidue 53 (p0SourceEvalQ (family (4 : ℤ) q4InRange) 4 0) =
      (51 : ZMod 53) := by
  let A : Matrix (Fin 8) (Fin 8) ℚ :=
    fun i j => (getInt num4 i.val j.val : ℚ) /
      (getNat den4 i.val j.val : ℚ)
  let L : Matrix (Fin 8) (Fin 8) ℚ := !![
    1, 0, 0, 0, 0, 0, 0, 0;
    95/22, 1, 0, 0, 0, 0, 0, 0;
    213/11, 1324/449, 1, 0, 0, 0, 0, 0;
    349/4, 8877/898, 30244/2221, 1, 0, 0, 0, 0;
    19/66, -106/1347, 21689/159912, 3526301/267422808, 1, 0, 0, 0;
    41/33, 775/2694, 15391/106608, 26146763/1604536848,
      98728867617/57533454482, 1, 0, 0;
    1103/198, 3428/4041, 414131/1439208, -41045087/7220415816,
      55435808363/28766727241, 2913460562242014/759687672221677, 1, 0;
    13253/528, 10215/3592, 7517479/1918944, 2769629465/9627221088,
      -549664170303/115066908964, 18409139720502957/1519375344443354,
      305519945383442686725/40919349011183253268, 1]
  let U : Matrix (Fin 8) (Fin 8) ℚ := !![
    -11, -10, -84, -314, -1276, -5373, -114676/5, -98302;
    0, -449/11, 3374/11, 8931/11, 3638, 353443/22,
      774294/11, 16859717/55;
    0, 0, 79956/449, 1525722/449, 4840380/449, 20759517/449,
      445694292/2245, 1913345622/2245;
    0, 0, 0, -66855702/2221, -161775324/2221, -749095299/2221,
      -16141833576/11105, -13890857490/2221;
    0, 0, 0, 0, -28766727241/133711404, -124384486487/222852340,
      -617200833974/278565425, -3502515923024/389991595;
    0, 0, 0, 0, 0, -759687672221677/3452007268920,
      -840454541379818/719168181025, -28672266507680597/5034177267175;
    0, 0, 0, 0, 0, 0,
      81838698022366506536/170929726249877325,
      4252672944498885665552/1196508083749141275;
    0, 0, 0, 0, 0, 0, 0,
      -2332265731274392109118484/5370664557717801991425]
  have hEntries :
      (fun i j : Fin 8 =>
        (p0MatrixQ (4 : ℚ) 4 i j).eval (0 : ℚ)) = A := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [A, getInt, getNat, num4, den4,
        p0MatrixQ, p0CQ, p0BQ, p0AQ, p0UQ,
        p0TQ, p0BQQ, p0Q, Nat.choose,
        Finset.sum_range_succ]
  have hEvalDet :
      (Matrix.det (p0MatrixQ (4 : ℚ) 4)).eval (0 : ℚ) =
        Matrix.det (fun i j : Fin 8 =>
          (p0MatrixQ (4 : ℚ) 4 i j).eval (0 : ℚ)) := by
    have h := RingHom.map_det (Polynomial.evalRingHom (0 : ℚ))
      (p0MatrixQ (4 : ℚ) 4)
    change (Matrix.det (p0MatrixQ (4 : ℚ) 4)).eval (0 : ℚ) =
      Matrix.det (fun i j : Fin 8 =>
        (p0MatrixQ (4 : ℚ) 4 i j).eval (0 : ℚ)) at h
    exact h
  have hSource :
      p0SourceEvalQ (family (4 : ℤ) q4InRange) 4 0 =
        A.det := by
    change (p0CanonicalPolynomial (4 : ℤ) 4).eval (0 : ℚ) =
      A.det
    simp only [p0CanonicalPolynomial,
      if_pos (by decide : 4 ∣ (4 : ℕ))]
    norm_num only [Int.cast_ofNat]
    rw [hEvalDet, hEntries]
  have hLU : L * U = A := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [L, U, A, getInt, getNat,
        num4, den4, Matrix.mul_apply, Fin.sum_univ_succ, List.getD]
  have hL : L.IsLowerTriangular := by
    dsimp [L]
    decide
  have hU : U.IsUpperTriangular := by
    dsimp [U]
    decide
  have hDet :
      A.det = (4664531462548784218236968 / 196875 : ℚ) := by
    rw [← hLU, Matrix.det_mul,
      Matrix.det_of_isLowerTriangular L hL,
      Matrix.det_of_isUpperTriangular hU]
    norm_num [L, U, Fin.prod_univ_succ]
  rw [hSource, hDet]
  norm_num [ratResidue]
  change ((4664531462548784218236968 : Nat) : ZMod 53) *
    ((196875 : Nat) : ZMod 53)⁻¹ = 51
  rw [← ZMod.natCast_mod 4664531462548784218236968 53,
    ← ZMod.natCast_mod 196875 53]
  norm_num
  change ((40 : Int) : ZMod 53) * (Nat.gcdA 33 53 : ZMod 53) = 51
  norm_num [Nat.gcdA, Nat.xgcd, Nat.xgcdAux, Nat.strongRec_eq]
  change ((-320 : Int) : ZMod 53) = ((51 : Int) : ZMod 53)
  rw [ZMod.intCast_eq_intCast_iff']
  norm_num

/-- q = 5 source seed residue; the integer table gives the target `4`. -/
theorem tower_q5_seed_residue :
    ratResidue 11 (p0SourceEvalQ (family (5 : ℤ) q5InRange) 4 0) =
      (4 : ZMod 11) := by
  let A : Matrix (Fin 8) (Fin 8) ℚ :=
    fun i j => (getInt num5 i.val j.val : ℚ) /
      (getNat den5 i.val j.val : ℚ)
  let L : Matrix (Fin 8) (Fin 8) ℚ := !![
    1, 0, 0, 0, 0, 0, 0, 0;
    149/28, 1, 0, 0, 0, 0, 0, 0;
    1249/42, 8258/2301, 1, 0, 0, 0, 0, 0;
    4687/28, 11509/767, 490047/37417, 1, 0, 0, 0, 0;
    25/112, -709/15340, 987/22010, 77534569/15254478600, 1, 0, 0, 0;
    19/16, 3423/15340, 291387/5986720, 435103703/61017914400,
      169335309998/80503602521, 1, 0, 0;
    6689/1008, 110563/138060, 1001971/4490040, -355182247/91526871600,
      732854875996/241510807563, 769945250974113/194318922019247, 1, 0;
    8367/224, 308179/92040, 69984749/23946880, 18154414527/81357219200,
      -4828016950783/644028820168, 39701080595429883/3109102752307952,
      1832604033062947457133/214533764774400520360, 1]
  let U : Matrix (Fin 8) (Fin 8) ℚ := !![
    -14, -25/2, -135, -1235/2, -3120, -32805/2, -87497, -937495/2;
    0, -3835/56, 17665/28, 122415/56, 167865/14, 3665745/56,
      9975603/28, 108188435/56;
    0, 0, 1496680/2301, 22907740/2301, 31927120/767, 169249940/767,
      2710494376/2301, 4834683580/767;
    0, 0, 0, -2542413100/37417, -7717674700/37417,
      -44258819100/37417, -237272502760/37417, -1272669931540/37417;
    0, 0, 0, 0, -80503602521/305089572, -1742157550429/2033930480,
      -104742549507/25424131, -54613657028471/2669533755;
    0, 0, 0, 0, 0, -971594610096235/1932086460504,
      -1386471587865236/402518012605, -71671020012856483/3381151305882;
    0, 0, 0, 0, 0, 0, 5363344119360013009/3497740596346446,
      687242243051512553771/48968368348850244;
    0, 0, 0, 0, 0, 0, 0,
      -830977823146495400190403/321800647161600780540]
  have hEntries :
      (fun i j : Fin 8 =>
        (p0MatrixQ (5 : ℚ) 4 i j).eval (0 : ℚ)) = A := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [A, getInt, getNat, num5, den5,
        p0MatrixQ, p0CQ, p0BQ, p0AQ, p0UQ,
        p0TQ, p0BQQ, p0Q, Nat.choose,
        Finset.sum_range_succ]
  have hEvalDet :
      (Matrix.det (p0MatrixQ (5 : ℚ) 4)).eval (0 : ℚ) =
        Matrix.det (fun i j : Fin 8 =>
          (p0MatrixQ (5 : ℚ) 4 i j).eval (0 : ℚ)) := by
    have h := RingHom.map_det (Polynomial.evalRingHom (0 : ℚ))
      (p0MatrixQ (5 : ℚ) 4)
    change (Matrix.det (p0MatrixQ (5 : ℚ) 4)).eval (0 : ℚ) =
      Matrix.det (fun i j : Fin 8 =>
        (p0MatrixQ (5 : ℚ) 4 i j).eval (0 : ℚ)) at h
    exact h
  have hSource :
      p0SourceEvalQ (family (5 : ℤ) q5InRange) 4 0 =
        A.det := by
    change (p0CanonicalPolynomial (5 : ℤ) 4).eval (0 : ℚ) =
      A.det
    simp only [p0CanonicalPolynomial,
      if_pos (by decide : 4 ∣ (4 : ℕ))]
    norm_num only [Int.cast_ofNat]
    rw [hEvalDet, hEntries]
  have hLU : L * U = A := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [L, U, A, getInt, getNat,
        num5, den5, Matrix.mul_apply, Fin.sum_univ_succ, List.getD]
  have hL : L.IsLowerTriangular := by
    dsimp [L]
    decide
  have hU : U.IsUpperTriangular := by
    dsimp [U]
    decide
  have hDet :
      A.det = (519361139466559625119001875 / 23328 : ℚ) := by
    rw [← hLU, Matrix.det_mul,
      Matrix.det_of_isLowerTriangular L hL,
      Matrix.det_of_isUpperTriangular hU]
    norm_num [L, U, Fin.prod_univ_succ]
  rw [hSource, hDet]
  norm_num [ratResidue]
  change ((519361139466559625119001875 : Nat) : ZMod 11) *
    ((23328 : Nat) : ZMod 11)⁻¹ = 4
  rw [← ZMod.natCast_mod 519361139466559625119001875 11,
    ← ZMod.natCast_mod 23328 11]
  norm_num
  change ((10 : Int) : ZMod 11) * (Nat.gcdA 8 11 : ZMod 11) = 4
  norm_num [Nat.gcdA, Nat.xgcd, Nat.xgcdAux, Nat.strongRec_eq]
  change ((-40 : Int) : ZMod 11) = ((4 : Int) : ZMod 11)
  rw [ZMod.intCast_eq_intCast_iff']
  norm_num

/-! The inverse certificates are named separately from the source residue
equalities so the finite matrix work can be filled independently. -/

theorem tower_q3_inverse_mod :
    residueMatrix 3 * inverseMatrix 3 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

theorem tower_q4_inverse_mod :
    residueMatrix 4 * inverseMatrix 4 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

theorem tower_q5_inverse_mod :
    residueMatrix 5 * inverseMatrix 5 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

/-! Nonzero consequences are elementary once the source residue stubs land. -/

theorem tower_q3_seed_nonzero :
    ratResidue 17 (p0SourceEvalQ (family (3 : ℤ) q3InRange) 4 0) ≠ 0 := by
  rw [tower_q3_seed_residue]
  decide

theorem tower_q4_seed_nonzero :
    ratResidue 53 (p0SourceEvalQ (family (4 : ℤ) q4InRange) 4 0) ≠ 0 := by
  rw [tower_q4_seed_residue]
  decide

theorem tower_q5_seed_nonzero :
    ratResidue 11 (p0SourceEvalQ (family (5 : ℤ) q5InRange) 4 0) ≠ 0 := by
  rw [tower_q5_seed_residue]
  decide

end

end Li2Lean.P0.PositiveTower.SeedChecks345

#print axioms Li2Lean.P0.PositiveTower.SeedChecks345.tower_q3_seed_residue
#print axioms Li2Lean.P0.PositiveTower.SeedChecks345.tower_q4_seed_residue
#print axioms Li2Lean.P0.PositiveTower.SeedChecks345.tower_q5_seed_residue
