/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.PositiveTower.EntryGoodness
import Li2Lean.P0.PencilAlgebra

namespace Li2Lean.P0.PositiveTower.EntryGoodness
noncomputable section
open Li2Lean Li2Lean.P0.PositiveTower
variable {p : ℕ} [hp : Fact (Nat.Prime p)] {a : ℤ}
variable (hp10 : 10 < p) (hunit : Nat.Coprime (a - 1).natAbs p)

def towerScaledMatrixQ (k : ℕ) (r : ℚ) :
    Matrix (Fin (2 * (4 * p ^ k))) (Fin (2 * (4 * p ^ k))) ℚ :=
  fun row col =>
    let q := p ^ k
    let m := 4 * q
    let i := 1 * q + (if row.val < m then row.val else row.val - m)
    if row.val < m then
      qRatP p k * p0CQ (a : ℚ) (2 * q) i col.val
    else
      (qRatP p k)^2 * p0BQ (a : ℚ) (2 * q) i col.val -
        ((qRatP p k)^2 * r) * p0AQ (a : ℚ) (2 * q) i col.val

include hp10 hunit in
lemma towerScaledMatrixQ_good (k : ℕ) (r : ℚ)
    (hbound : r.den < p ^ k) :
    ∀ row col, towerScaledMatrixQ (p := p) (a := a) k r row col ∈ (GoodP p) := by
  intro row col
  let q := p ^ k
  let m := 4 * q
  let i := 1 * q + (if row.val < m then row.val else row.val - m)
  have hqpos : 0 < q := by dsimp [q]; exact pow_pos hp.out.pos k
  have h10 : 10 * q < p * q := Nat.mul_lt_mul_of_pos_right hp10 hqpos
  have hqp : q < p * q := by omega
  have hg : 2 * q < p * q := by omega
  have hi : i < p * q := by
    dsimp [i, m]
    split_ifs <;> omega
  have hj : col.val < p * q := by
    have hsize : col.val < 8 * q := by
      have := col.isLt
      omega
    omega
  by_cases hr : row.val < m
  · simp only [towerScaledMatrixQ, q, m, i, hr]
    have hidx : i = 1 * q + row.val := by
      simp [i, m, hr]
    have hcol8 : col.val < 8 * q := by
      have := col.isLt
      omega
    have hrow4 : row.val < 4 * q := by simpa [m] using hr
    have hleft : 1 * q + row.val < 5 * q := by omega
    have hmaxlt : max (1 * q + row.val) col.val < 8 * q :=
      max_lt_iff.mpr ⟨by omega, hcol8⟩
    have hmax : max (1 * q + row.val) col.val + 2 * q < p * q := by omega
    have hmem := q_mul_p0CQ_good (a := a) k (2 * q) (1 * q + row.val) col.val
      (by simpa [q] using hmax)
    simpa [q] using hmem
  · simp only [towerScaledMatrixQ, q, m, i, hr, if_false]
    let i' : ℕ := 1 * q + (row.val - m)
    have hidx : i' = i := by
      dsimp [i', i, m]
      have hr' : ¬ row.val < 4 * q := by simpa [m] using hr
      rw [if_neg hr']
    apply (GoodP p).sub_mem
    · have hi' : i' < p * p ^ k := by rw [hidx]; simpa [q] using hi
      have hj' : col.val < p * p ^ k := by simpa [q] using hj
      have hg' : 2 * q < p * p ^ k := by simpa [q] using hg
      have hmem := q_sq_mul_p0BQ_good hunit k (2 * q) i' col.val hg' hi' hj'
      simpa [q, m, i'] using hmem
    · exact (GoodP p).mul_mem (q_sq_mul_rat_good k r hbound)
        (by
          have hmem := p0AQ_good (p := p) (a := a) (2 * q) i' col.val
          simpa [q, m, i'] using hmem)

include hp10 hunit in
def towerScaledMatrixGood (k : ℕ) (r : ℚ)
  (hbound : r.den < p ^ k) :
    Matrix (Fin (2 * (4 * p ^ k))) (Fin (2 * (4 * p ^ k))) (GoodP p) :=
  fun row col => ⟨towerScaledMatrixQ (p := p) (a := a) k r row col,
    towerScaledMatrixQ_good hp10 hunit k r hbound row col⟩

include hp10 hunit in
theorem towerScaledMatrixGood_coe (k : ℕ) (r : ℚ)
    (hbound : r.den < p ^ k) :
    ((GoodP p).subtype.mapMatrix (towerScaledMatrixGood hp10 hunit k r hbound)) =
      towerScaledMatrixQ (p := p) (a := a) k r := by
  ext row col
  rfl

theorem towerScaledMatrixQ_eq_eval (k : ℕ) (r : ℚ) :
    towerScaledMatrixQ (p := p) (a := a) k r =
      (p0ScaledPencilMatrixQ (a : ℚ) (4 * p ^ k) (p ^ k)).map
        (fun f => Polynomial.eval ((qRatP p k)^2 * r) f) := by
  ext row col
  let q := p ^ k
  let m := 4 * q
  have hq : (q : ℚ) = qRatP p k := by simp [q, qRatP]
  have hm4 : m / 4 = 1 * q := by dsimp [m]; omega
  have hm2 : m / 2 = 2 * q := by dsimp [m]; omega
  by_cases hr : row.val < m
  · simp only [towerScaledMatrixQ, p0ScaledPencilMatrixQ, q, m, hm4, hm2,
      if_pos hr, Matrix.map_apply, Polynomial.eval_C]
    rw [hq]
  · simp only [towerScaledMatrixQ, p0ScaledPencilMatrixQ, q, m, hm4, hm2,
      if_neg hr, if_false, Matrix.map_apply, Polynomial.eval_sub,
      Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_C]
    rw [hq]

include hp10 hunit in
theorem towerScaledMatrixGood_det_value (k : ℕ) (r : ℚ)
    (hbound : r.den < p ^ k) :
    ((Matrix.det (towerScaledMatrixGood hp10 hunit k r hbound) : (GoodP p)) : ℚ) =
      Matrix.det (towerScaledMatrixQ (p := p) (a := a) k r) := by
  change (GoodP p).subtype
      (Matrix.det (towerScaledMatrixGood hp10 hunit k r hbound)) =
    Matrix.det ((GoodP p).subtype.mapMatrix
      (towerScaledMatrixGood hp10 hunit k r hbound))
  calc
    _ = Matrix.det ((GoodP p).subtype.mapMatrix
          (towerScaledMatrixGood hp10 hunit k r hbound)) :=
      RingHom.map_det (GoodP p).subtype (towerScaledMatrixGood hp10 hunit k r hbound)
    _ = Matrix.det (towerScaledMatrixQ (p := p) (a := a) k r) := by
      rw [towerScaledMatrixGood_coe]


end
end Li2Lean.P0.PositiveTower.EntryGoodness
