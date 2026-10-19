/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.V.VLiteralContour

namespace Li2Lean.V

/-! The discrete Vandermonde used in the literal v13 integrand is exactly
the determinant convention used by the existing Cauchy determinant kit.
Source: v13 `v-analytic.tex:118-120,127-153`. -/

theorem vContourVandermonde_eq_det {d : ℕ} (z : Fin d → ℂ) :
    Literal.vContourVandermonde z = (Matrix.vandermonde z).det := by
  have hIoi (i : Fin d) :
      (Finset.univ : Finset (Fin d)).filter (fun j => i < j) = Finset.Ioi i := by
    ext j
    simp [Finset.mem_Ioi]
  calc
    Literal.vContourVandermonde z =
        ∏ i : Fin d, ∏ j : Fin d, if i < j then z j - z i else 1 := rfl
    _ = ∏ i : Fin d, ∏ j ∈ Finset.Ioi i, (z j - z i) := by
      apply Finset.prod_congr rfl
      intro i hi
      symm
      rw [← hIoi i, Finset.prod_filter]
    _ = (Matrix.vandermonde z).det := (Matrix.det_vandermonde z).symm

end Li2Lean.V

#print axioms Li2Lean.V.vContourVandermonde_eq_det
