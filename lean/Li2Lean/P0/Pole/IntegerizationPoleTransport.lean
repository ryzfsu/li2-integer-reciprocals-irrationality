/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.IntegerizationS08Lift
import Li2Lean.P0.Pole.MatrixCore

namespace Li2Lean.P0.Pole

open Li2Lean.P0.Integerization
open Li2Lean.P0.Integerization.S08
open Li2Lean.P0.PoleMatrixCore

noncomputable section

/-- Integer-polynomial lift of the pole matrix pencil rescaling. -/
def tScaleZ (g : ℕ) : Polynomial (Polynomial ℤ) →+* Polynomial (Polynomial ℤ) :=
  Polynomial.eval₂RingHom
    (Polynomial.eval₂RingHom (Polynomial.C.comp Polynomial.C)
      ((Polynomial.X - 1) ^ g * Polynomial.C Polynomial.X))
    Polynomial.X

private theorem map_eval₂_inner (g : ℕ) (a : Polynomial ℤ) :
    Polynomial.mapRingHom (Polynomial.mapRingHom (Int.castRingHom ℚ))
      (Polynomial.eval₂ (Polynomial.C.comp Polynomial.C)
        ((Polynomial.X - 1) ^ g * Polynomial.C Polynomial.X) a) =
      Polynomial.eval₂ (Polynomial.C.comp Polynomial.C)
        ((Polynomial.X - 1) ^ g * Polynomial.C Polynomial.X)
        (Polynomial.map (Int.castRingHom ℚ) a) := by
  let f : Polynomial ℤ →+* BivPoly :=
    (Polynomial.mapRingHom (Polynomial.mapRingHom (Int.castRingHom ℚ))).comp
      (Polynomial.eval₂RingHom (Polynomial.C.comp Polynomial.C)
        ((Polynomial.X - 1) ^ g * Polynomial.C Polynomial.X))
  let h : Polynomial ℤ →+* BivPoly :=
    (Polynomial.eval₂RingHom (Polynomial.C.comp Polynomial.C)
      ((Polynomial.X - 1) ^ g * Polynomial.C Polynomial.X)).comp
        (Polynomial.mapRingHom (Int.castRingHom ℚ))
  have hf : f = h := by
    apply Polynomial.ringHom_ext
    · intro z
      simp [f, h]
    · simp [f, h, Polynomial.mapRingHom, Polynomial.map_C, Polynomial.map_X]
  change f a = h a
  rw [hf]

/-- Clearing denominators commutes with the pole pencil rescaling T ↦ (a-1)^g T. -/
theorem psi_tScaleZ (g : ℕ) (Z : Polynomial (Polynomial ℤ)) :
    psi (tScaleZ g Z) = tScale g (psi Z) := by
  let f : Polynomial (Polynomial ℤ) →+* BivPoly := psi.comp (tScaleZ g)
  let h : Polynomial (Polynomial ℤ) →+* BivPoly := (tScale g).comp psi
  have eqfh : f = h := by
    apply Polynomial.ringHom_ext
    · intro a
      simpa [f, h, psi, tScale, tScaleZ] using map_eval₂_inner g a
    · simp [f, h, tScaleZ, tScale, psi]
  change f Z = h Z
  rw [eqfh]

end

end Li2Lean.P0.Pole
