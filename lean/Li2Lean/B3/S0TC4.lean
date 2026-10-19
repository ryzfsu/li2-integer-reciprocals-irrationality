/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.V.SignedEnergy

/-!
Algebraic C4 bridge for the signed-V duality argument.  This file keeps the
measure-theoretic Fubini facts explicit and does not package the desired
residual inequality as a certificate field.  The zero-mass/L6 proof of the
last scalar inequality belongs to C1-C3 and is supplied separately.
-/

namespace Li2Lean.V

noncomputable section

/-- The componentwise quadratic remainder after subtracting the reference
triple.  The mixed `v-z` and cross-kernel terms keep their natural product
measure orientations. -/
noncomputable def signedVDualRemainder (μ ν : SignedVMeasures) : ℝ :=
  (vLogInteraction μ.μx μ.μx + vLogInteraction ν.μx ν.μx -
      vLogInteraction μ.μx ν.μx - vLogInteraction ν.μx μ.μx) +
    (vLogInteraction μ.μv μ.μv + vLogInteraction ν.μv ν.μv -
      vLogInteraction μ.μv ν.μv - vLogInteraction ν.μv μ.μv) +
    (vLogInteraction μ.μz μ.μz + vLogInteraction ν.μz ν.μz -
      vLogInteraction μ.μz ν.μz - vLogInteraction ν.μz μ.μz) +
    (vLogInteraction μ.μv μ.μz + vLogInteraction ν.μv ν.μz -
      vLogInteraction ν.μv μ.μz - vLogInteraction ν.μz μ.μv) -
    (vCrossInteraction μ.q μ.μx μ.μv + vCrossInteraction ν.q ν.μx ν.μv -
      vCrossInteraction ν.q μ.μx ν.μv - vCrossInteraction ν.q ν.μx μ.μv)

/-- Expand the signed-V dual residual into the explicit quadratic remainder.
The hypotheses are exactly the three self-kernel symmetries and the three
Fubini field evaluations; no conclusion-shaped residual identity is assumed.
-/
theorem signedVDualResidual_eq_remainder
    (μ ν : SignedVMeasures)
    (hxx : vLogInteraction μ.μx ν.μx = vLogInteraction ν.μx μ.μx)
    (hvv : vLogInteraction μ.μv ν.μv = vLogInteraction ν.μv μ.μv)
    (hzz : vLogInteraction μ.μz ν.μz = vLogInteraction ν.μz μ.μz)
    (hFx : (∫ w : ℂ, signedVFieldX ν w ∂μ.μx) =
      2 * vLogInteraction ν.μx μ.μx -
        vCrossInteraction ν.q μ.μx ν.μv)
    (hFv : (∫ w : ℂ, signedVFieldV ν w ∂μ.μv) =
      2 * vLogInteraction ν.μv μ.μv +
        vLogInteraction ν.μz μ.μv -
        vCrossInteraction ν.q ν.μx μ.μv)
    (hFz : (∫ w : ℂ, signedVFieldZ ν w ∂μ.μz) =
      2 * vLogInteraction ν.μz μ.μz +
        vLogInteraction ν.μv μ.μz) :
    signedVDualResidual μ ν = signedVDualRemainder μ ν := by
  unfold signedVDualResidual signedVDualRemainder signedVQuadratic
  rw [hFx, hFv, hFz, hxx, hvv, hzz]
  ring

/-- The C4 signed-V field comparison follows from the independently proved
nonpositivity of the zero-mass remainder. -/
theorem signedV_duality_comparison_of_remainder
    (μ ν : SignedVMeasures)
    (hxx : vLogInteraction μ.μx ν.μx = vLogInteraction ν.μx μ.μx)
    (hvv : vLogInteraction μ.μv ν.μv = vLogInteraction ν.μv μ.μv)
    (hzz : vLogInteraction μ.μz ν.μz = vLogInteraction ν.μz μ.μz)
    (hFx : (∫ w : ℂ, signedVFieldX ν w ∂μ.μx) =
      2 * vLogInteraction ν.μx μ.μx -
        vCrossInteraction ν.q μ.μx ν.μv)
    (hFv : (∫ w : ℂ, signedVFieldV ν w ∂μ.μv) =
      2 * vLogInteraction ν.μv μ.μv +
        vLogInteraction ν.μz μ.μv -
        vCrossInteraction ν.q ν.μx μ.μv)
    (hFz : (∫ w : ℂ, signedVFieldZ ν w ∂μ.μz) =
      2 * vLogInteraction ν.μz μ.μz +
        vLogInteraction ν.μv μ.μz)
    (hRemainder : signedVDualRemainder μ ν ≤ 0) :
    signedVDualResidual μ ν ≤ 0 := by
  rw [signedVDualResidual_eq_remainder μ ν hxx hvv hzz hFx hFv hFz]
  exact hRemainder

/-- The same result in the displayed v13 inequality form. -/
theorem signedV_duality_field_comparison_of_remainder
    (μ ν : SignedVMeasures)
    (hxx : vLogInteraction μ.μx ν.μx = vLogInteraction ν.μx μ.μx)
    (hvv : vLogInteraction μ.μv ν.μv = vLogInteraction ν.μv μ.μv)
    (hzz : vLogInteraction μ.μz ν.μz = vLogInteraction ν.μz μ.μz)
    (hFx : (∫ w : ℂ, signedVFieldX ν w ∂μ.μx) =
      2 * vLogInteraction ν.μx μ.μx -
        vCrossInteraction ν.q μ.μx ν.μv)
    (hFv : (∫ w : ℂ, signedVFieldV ν w ∂μ.μv) =
      2 * vLogInteraction ν.μv μ.μv +
        vLogInteraction ν.μz μ.μv -
        vCrossInteraction ν.q ν.μx μ.μv)
    (hFz : (∫ w : ℂ, signedVFieldZ ν w ∂μ.μz) =
      2 * vLogInteraction ν.μz μ.μz +
        vLogInteraction ν.μv μ.μz)
    (hRemainder : signedVDualRemainder μ ν ≤ 0) :
    signedVQuadratic μ ≤
      -signedVQuadratic ν +
        (∫ w : ℂ, signedVFieldX ν w ∂μ.μx) +
        (∫ w : ℂ, signedVFieldV ν w ∂μ.μv) +
        (∫ w : ℂ, signedVFieldZ ν w ∂μ.μz) := by
  have hResidual := signedV_duality_comparison_of_remainder μ ν
    hxx hvv hzz hFx hFv hFz hRemainder
  unfold signedVDualResidual at hResidual
  linarith

/-- Connect the C1--C3 square certificate to C4 once its explicit remainder
identity has been proved. The old interface assumed the residual identity
directly; this bridge asks only for the independent square decomposition. -/
theorem signedV_duality_field_comparison_of_square
    (μ ν : SignedVMeasures)
    (c : SignedVSquareCertificate μ ν)
    (hSquare : signedVDualRemainder μ ν = c.remainder)
    (hxx : vLogInteraction μ.μx ν.μx = vLogInteraction ν.μx μ.μx)
    (hvv : vLogInteraction μ.μv ν.μv = vLogInteraction ν.μv μ.μv)
    (hzz : vLogInteraction μ.μz ν.μz = vLogInteraction ν.μz μ.μz)
    (hFx : (∫ w : ℂ, signedVFieldX ν w ∂μ.μx) =
      2 * vLogInteraction ν.μx μ.μx -
        vCrossInteraction ν.q μ.μx ν.μv)
    (hFv : (∫ w : ℂ, signedVFieldV ν w ∂μ.μv) =
      2 * vLogInteraction ν.μv μ.μv +
        vLogInteraction ν.μz μ.μv -
        vCrossInteraction ν.q ν.μx μ.μv)
    (hFz : (∫ w : ℂ, signedVFieldZ ν w ∂μ.μz) =
      2 * vLogInteraction ν.μz μ.μz +
        vLogInteraction ν.μv μ.μz) :
    signedVQuadratic μ ≤
      -signedVQuadratic ν +
        (∫ w : ℂ, signedVFieldX ν w ∂μ.μx) +
        (∫ w : ℂ, signedVFieldV ν w ∂μ.μv) +
        (∫ w : ℂ, signedVFieldZ ν w ∂μ.μz) := by
  have hRemainder : signedVDualRemainder μ ν ≤ 0 := by
    rw [hSquare]
    exact signedV_square_remainder_nonpos μ ν c
  exact signedV_duality_field_comparison_of_remainder μ ν
    hxx hvv hzz hFx hFv hFz hRemainder

end
end Li2Lean.V
