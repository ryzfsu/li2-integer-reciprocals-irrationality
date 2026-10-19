/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.PositiveBaseEnvelopeCore
import Li2Lean.P0.EnvMatrixQ

namespace Li2Lean.P0.PositiveBase

noncomputable section
open Filter Topology

/-- The literal q-polynomial evaluation is the determinant of the q-pencil
matrix used by the frequency truncation argument. -/
theorem qGmBeta_eq_det_XbetaQ (q m : ℕ) (h4 : 4 ∣ m) :
    qGmBeta q m = (Li2Lean.P0.Env.XbetaQ (q : ℤ) m).det := by
  unfold qGmBeta
  have hpoly : p0CanonicalPolynomial (q : ℤ) m =
      Matrix.det (p0MatrixQ (q : ℚ) m) := by
    simp [p0CanonicalPolynomial, h4]
  rw [hpoly]
  let f := Polynomial.eval₂RingHom (algebraMap ℚ ℂ)
    ((li2InvValue (q : ℤ) : ℝ) : ℂ)
  change f (Matrix.det (p0MatrixQ (q : ℚ) m)) = _
  rw [RingHom.map_det]
  congr 1
  ext r c
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply,
    Li2Lean.p0MatrixQ, Li2Lean.P0.Env.XbetaQ, Li2Lean.P0.Env.lab, f]
  split_ifs with hr
  · simp
  · simp [Polynomial.eval₂_sub, Polynomial.eval₂_mul,
      Polynomial.eval₂_X, Polynomial.eval₂_C]
    ring

/-- Any uniform bound on q-frequency truncations bounds the actual q determinant. -/
theorem norm_qGmBeta_le_of_trunc (q m : ℕ) (hq : 2 ≤ q) (hm : 0 < m)
    (h4 : 4 ∣ m) (C : ℝ)
    (hb : ∀ H, ‖(Li2Lean.P0.Env.truncMatrixQ q m H).det‖ ≤ C) :
    ‖qGmBeta q m‖ ≤ C := by
  rw [qGmBeta_eq_det_XbetaQ q m h4,
    Li2Lean.P0.Env.det_XbetaQ_eq_det_XinfQ q m hm]
  have ht : Tendsto
      (fun H => ‖(Li2Lean.P0.Env.truncMatrixQ q m H).det‖) atTop
      (𝓝 ‖(Li2Lean.P0.Env.XinfQ (q : ℤ) m).det‖) := by
    exact ((continuous_id.matrix_det.tendsto
      (Li2Lean.P0.Env.XinfQ (q : ℤ) m)).comp
      (Li2Lean.P0.Env.tendsto_truncMatrixQ q m hq)).norm
  exact le_of_tendsto' ht hb

end

end Li2Lean.P0.PositiveBase
