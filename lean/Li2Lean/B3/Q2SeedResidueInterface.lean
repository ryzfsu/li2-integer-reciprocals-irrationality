/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/

import Mathlib
import Li2Lean.B3.ActualFrobeniusProducer
import Li2Lean.Kit.ReducedRational

/-!
# The q = 2 seed finite-place interface

This is the smallest construction-bound boundary for the remaining q = 2
seed/LU bridge.  The rational matrix is the actual v13 `V.vSourceMatrix`, and
the only finite matrix named here is the printed reduction of that same seed.
No arbitrary polynomial, valuation, or replacement determinant is accepted.

Source anchors: v13 `nonvanishing.tex:146-198`, especially the q = 2 row of
the seed table at lines 170-197.  The source matrix formulas are reused from
`V.VFamily` (`v-arithmetic.tex:13-32`) through
`B3.ActualFrobeniusProducer`.
-/

namespace Li2Lean.B3

noncomputable section

open Li2Lean

abbrev Q2SeedRing := ZMod (vSeedPrime 2)

theorem q2SignedRange : SignedVBaseRange 2 := by
  constructor <;> norm_num [SignedVBaseRange]

/-- The actual v13 9 by 9 source matrix at the seed value `T = 0`.
The dimensions reduce definitionally because `vMatrixSize 1 = 9`. -/
def q2SourceMatrixAtZero : Matrix (Fin 9) (Fin 9) ℚ :=
  fun r c => (V.vSourceMatrix 1 (-2 : ℤ) r c).eval 0

/-!
The following matrix is the finite-place target printed by the q = 2
9 by 9 seed reduction.  It is data for the producer boundary; its determinant
is deliberately kept as an explicit certificate field below rather than
being hidden behind a theorem about an arbitrary matrix.
-/
def q2SeedMatrixResidue : Matrix (Fin 9) (Fin 9) Q2SeedRing := !![
  5, 0, 1, 5, 1, 7, 0, 2, 3;
  3, 1, 0, 9, 1, 9, 8, 0, 7;
  5, 5, 9, 0, 4, 9, 4, 6, 0;
  2, 1, 1, 4, 0, 3, 4, 3, 10;
  8, 1, 8, 2, 2, 5, 6, 0, 1;
  8, 8, 3, 7, 10, 4, 0, 5, 9;
  4, 2, 7, 3, 2, 8, 5, 10, 5;
  9, 2, 10, 2, 9, 3, 1, 9, 3;
  6, 4, 3, 9, 2, 8, 7, 5, 10
]

theorem q2SeedPrime_prime : Nat.Prime (vSeedPrime 2) := by
  norm_num [vSeedPrime]

theorem q2SeedPrime_gt_seven : 7 < vSeedPrime 2 := by
  norm_num [vSeedPrime]

/-- The denominator support statement used by the q = 2 seed row.
This is the concrete `2,3,5,7` support assertion of v13
`nonvanishing.tex:193-197`, before it is consumed by a determinant map. -/
theorem q2SeedPrime_coprime_support : Nat.Coprime (vSeedPrime 2) 2520 := by
  norm_num [vSeedPrime]

/-- Definitional bridge from the actual rational source matrix to the actual
v13 determinant value.  This is only evaluation commuting with determinant;
the finite-place reduction is intentionally not proved here. -/
theorem q2SourceMatrixAtZero_det_eq_seed_eval :
    q2SourceMatrixAtZero.det =
      (V.vPolynomial 1 (-2 : ℤ)).eval 0 := by
  unfold q2SourceMatrixAtZero V.vPolynomial
  calc
    Matrix.det (fun r c =>
        (V.vSourceMatrix 1 (-2 : ℤ) r c).eval 0) =
        ((Polynomial.evalRingHom (0 : ℚ)).mapMatrix
          (V.vSourceMatrix 1 (-2 : ℤ))).det := by
      congr 1
    _ = (Polynomial.evalRingHom (0 : ℚ))
        ((V.vSourceMatrix 1 (-2 : ℤ)).det) :=
      (RingHom.map_det (Polynomial.evalRingHom (0 : ℚ))
        (V.vSourceMatrix 1 (-2 : ℤ))).symm

/-!
The fields below are the exact remaining q = 2 obligations:

* `boundary` carries the coefficient denominators, the five printed residue
  coefficients, and the exact seed constant required by
  `VActualFrobeniusTowerProducer` (`nonvanishing.tex:170-198`).
* `source_entry_representative` records an entrywise finite-place lift of the
  actual rational source matrix.
* `determinant_representative` is the determinant-level bridge on which a
  future `RingHom.map_det` proof can close the LU certificate.
* `residue_det_eq_four` is the q = 2 LU output, corresponding to the first
  row of the v13 table (`nonvanishing.tex:179-191`).

Nothing here asserts the existence of these fields. -/
structure Q2ActualSeedResidueInterface : Prop where
  boundary : VActualSeedBoundary 2 q2SignedRange
  source_entry_representative :
    ∀ r c, ∃ z : ContourKit.ReducedRational (vSeedPrime 2),
      z.value = q2SourceMatrixAtZero r c ∧
      z.residue = q2SeedMatrixResidue r c
  determinant_representative :
    ∃ z : ContourKit.ReducedRational (vSeedPrime 2),
      z.value = q2SourceMatrixAtZero.det ∧
      z.residue = q2SeedMatrixResidue.det
  residue_det_eq_four : q2SeedMatrixResidue.det = (4 : Q2SeedRing)

theorem Q2ActualSeedResidueInterface.seed_boundary
    (h : Q2ActualSeedResidueInterface) :
    VActualSeedBoundary 2 q2SignedRange :=
  h.boundary

theorem Q2ActualSeedResidueInterface.seed_eval_ne_zero
    (h : Q2ActualSeedResidueInterface) :
    (V.vPolynomial 1 (-2 : ℤ)).eval 0 ≠ 0 := by
  obtain ⟨z, hzvalue, hzresidue⟩ := h.determinant_representative
  have hz : z.residue ≠ 0 := by
    rw [hzresidue, h.residue_det_eq_four]
    decide
  have hzvalue' : z.value ≠ 0 :=
    ContourKit.ReducedRational.value_ne_zero z hz
  rw [hzvalue, q2SourceMatrixAtZero_det_eq_seed_eval] at hzvalue'
  exact hzvalue'

end
end Li2Lean.B3

#print axioms Li2Lean.B3.q2SourceMatrixAtZero_det_eq_seed_eval
#print axioms Li2Lean.B3.Q2ActualSeedResidueInterface.seed_boundary
#print axioms Li2Lean.B3.Q2ActualSeedResidueInterface.seed_eval_ne_zero

