/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.Pole.DivDiff

namespace Li2Lean.P0.Pole

open Matrix

noncomputable section

/-- The coefficient matrix for all forward differences of orders `0,...,n-1`.
The row indexed by `u` contains the weights of `Δ^u` at the points `0,...,u`.
-/
def forwardDiffMatrix (n : ℕ) : Matrix (Fin n) (Fin n) ℚ := fun u a =>
  if a.val ≤ u.val then fdw u.val a.val else 0

/-- Two independent blocks of row differences, preserving the top/lower split
of the pole matrix.
-/
def poleRowDiffMatrix (m : ℕ) : Matrix (Fin (2 * m)) (Fin (2 * m)) ℚ :=
  fun r c =>
    if r.val < m then
      if c.val < m then
        if c.val ≤ r.val then fdw r.val c.val else 0
      else 0
    else if m ≤ c.val then
      if c.val - m ≤ r.val - m then fdw (r.val - m) (c.val - m) else 0
    else 0

private theorem fdw_self (u : ℕ) : fdw u u = 1 := by
  simp [fdw]

private theorem det_forwardDiffMatrix (n : ℕ) :
    Matrix.det (forwardDiffMatrix n) = 1 := by
  classical
  have htri : Matrix.IsLowerTriangular (forwardDiffMatrix n) := by
    intro u a hua
    change u < a at hua
    have hval : u.val < a.val := Fin.lt_def.mp hua
    simp [forwardDiffMatrix, Nat.not_le_of_gt hval]
  rw [Matrix.det_of_isLowerTriangular (forwardDiffMatrix n) htri]
  simp [forwardDiffMatrix, fdw_self]

private theorem det_poleRowDiffMatrix (m : ℕ) :
    Matrix.det (poleRowDiffMatrix m) = 1 := by
  classical
  have htri : Matrix.IsLowerTriangular (poleRowDiffMatrix m) := by
    intro r c hrc
    change r < c at hrc
    by_cases hr : r.val < m
    · by_cases hc : c.val < m
      · have hval : r.val < c.val := Fin.lt_def.mp hrc
        simp [poleRowDiffMatrix, hr, hc, Nat.not_le_of_gt hval]
      · simp [poleRowDiffMatrix, hr, hc]
    · by_cases hc : c.val < m
      · have hnot : ¬ r < c := by
          intro hlt
          change r < c at hlt
          have hval : r.val < c.val := Fin.lt_def.mp hlt
          have hr' : m ≤ r.val := Nat.le_of_not_gt hr
          omega
        exact (hnot hrc).elim
      · have hval : r.val < c.val := Fin.lt_def.mp hrc
        have hshift : r.val - m < c.val - m := by omega
        simp [poleRowDiffMatrix, hr, Nat.not_le_of_gt hshift]
  have hdiag : ∀ r, poleRowDiffMatrix m r r = 1 := by
    intro r
    by_cases hr : r.val < m
    · simp [poleRowDiffMatrix, hr, fdw_self]
    · have hr' : m ≤ r.val := Nat.le_of_not_gt hr
      simp [poleRowDiffMatrix, hr, hr', fdw_self]
  rw [Matrix.det_of_isLowerTriangular (poleRowDiffMatrix m) htri]
  simp [hdiag]

/-- Applying forward differences independently to the two row blocks and to
all columns preserves the determinant.  The matrices are rational and hence
independent of the polynomial variables in `R`.
-/
theorem det_poleForwardDifferenceTransform
    {R : Type*} [CommRing R] [Algebra ℚ R]
    (m : ℕ) (M : Matrix (Fin (2 * m)) (Fin (2 * m)) R) :
    Matrix.det
        ((algebraMap ℚ R).mapMatrix (poleRowDiffMatrix m) * M *
          (algebraMap ℚ R).mapMatrix (forwardDiffMatrix (2 * m)).transpose) =
      Matrix.det M := by
  have hrow :
      Matrix.det ((algebraMap ℚ R).mapMatrix (poleRowDiffMatrix m)) = 1 := by
    rw [← RingHom.map_det, det_poleRowDiffMatrix]
    simp
  have hcol :
      Matrix.det ((algebraMap ℚ R).mapMatrix (forwardDiffMatrix (2 * m)).transpose) = 1 := by
    rw [← RingHom.map_det, Matrix.det_transpose, det_forwardDiffMatrix]
    simp
  rw [Matrix.det_mul, Matrix.det_mul, hrow, hcol]
  simp

end

end Li2Lean.P0.Pole
