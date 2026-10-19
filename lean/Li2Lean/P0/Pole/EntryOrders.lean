/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.Pole.P0PoleCoefficientsSkeleton

namespace Li2Lean.P0.Pole

open Polynomial Finset Li2Lean.P0.Integerization
open scoped BigOperators

noncomputable section
private def outerCoeffHom (n : ℕ) : BivPoly →+ Polynomial ℚ where
  toFun := fun f => f.coeff n
  map_zero' := by simp
  map_add' f g := by simp

private theorem outerCoeffHom_apply (n : ℕ) (f : BivPoly) : outerCoeffHom n f = f.coeff n := rfl

private theorem outerCoeffHom_sum (n : ℕ) {ι : Type} (s : Finset ι)
    (f : ι → BivPoly) :
    outerCoeffHom n (∑ i ∈ s, f i) = ∑ i ∈ s, outerCoeffHom n (f i) := by
  exact map_sum (outerCoeffHom n) f s

/-! The lower block before the pencil correction.  Exposing this form keeps
the coefficient-order argument reusable by the determinant assembly. -/
noncomputable def fdLowerEntry (g u v : ℕ) (x0 : ℕ) : BivPoly :=
  ∑ a ∈ Finset.range (u + 1), ∑ c ∈ Finset.range (v + 1),
    Polynomial.C (Polynomial.C (fdw u a * fdw v c)) *
      shiftB (formalB g (x0 + a) c)

theorem fdLowerEntry_coeff_eq_zero (g u v x0 k : ℕ) (hk : k < g)
    (hkuv : k ≤ u + v) :
    (fdLowerEntry g u v x0).coeff k = 0 := by
  classical
  have hkg : k ≤ g := Nat.le_of_lt hk
  have ht : 1 ≤ g - k := by omega
  have htg : g - k ≤ g := by omega
  have hsub : g - (g - k) = k := Nat.sub_sub_self hkg
  have hdeg : (piPoly g (g - k)).natDegree ≤ u + v := by
    calc
      (piPoly g (g - k)).natDegree ≤ g - (g - k) :=
        piPoly_natDegree_le g (g - k) ht htg
      _ = k := hsub
      _ ≤ u + v := hkuv
  rw [← hsub]
  unfold fdLowerEntry
  simp only [Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul]
  simp_rw [coeff_shift_formalB g _ _ (g - k) ht htg]
  simp only [cq]
  simp_rw [← Polynomial.C_mul]
  simpa [Nat.cast_add] using
    congrArg (fun z : ℚ => (Polynomial.C z : Polynomial ℚ))
      (fwdDiff2_dd_eq_zero (piPoly g (g - k)) (x0 : ℚ)
        (u := u) (v := v) hdeg)

/-- The `(u,v)` double forward difference of an entry on the shifted matrix,
based at row `x0` and column `0`. -/
def fdwShiftFormalC (g x0 u v : ℕ) : BivPoly :=
  ∑ a ∈ range (u + 1), ∑ c ∈ range (v + 1),
    ratConst (fdw u a * fdw v c) * shiftB (formalC g (x0 + a) c)

def fdwShiftFormalB (g x0 u v : ℕ) : BivPoly :=
  ∑ a ∈ range (u + 1), ∑ c ∈ range (v + 1),
    ratConst (fdw u a * fdw v c) *
      shiftB (formalB g (x0 + a) c -
        Polynomial.C Polynomial.X * (aVar - ratConst 1) ^ g *
          formalA g (x0 + a) c)

private theorem coeff_shiftPoleLower (g i j t : ℕ) (ht : 1 ≤ t) (htg : t ≤ g) :
    (shiftB (formalB g i j -
      Polynomial.C Polynomial.X * (aVar - ratConst 1) ^ g * formalA g i j)).coeff
        (g - t) = cq (dd (piPoly g t) (i : ℚ) (j : ℚ)) := by
  have hk : g - t < g := by omega
  rw [map_sub, Polynomial.coeff_sub, coeff_shift_formalB g i j t ht htg,
    coeff_shift_pencilA g i j (g - t) hk]
  simp

private theorem fdwShiftFormalC_coeff_formula (g x0 u v : ℕ) :
    (fdwShiftFormalC g x0 u v).coeff 0 =
      Polynomial.C (∑ a ∈ range (u + 1), ∑ c ∈ range (v + 1),
        fdw u a * fdw v c * dd (bp g g) (x0 + a : ℚ) c) := by
  change outerCoeffHom 0
    (∑ a ∈ range (u + 1), ∑ c ∈ range (v + 1),
      ratConst (fdw u a * fdw v c) * shiftB (formalC g (x0 + a) c)) = _
  simp_rw [outerCoeffHom_sum]
  simp only [outerCoeffHom_apply, ratConst, Polynomial.coeff_C_mul,
    coeff_zero_shift_formalC, cq]
  simp only [map_sum, map_mul]

  push_cast
  rfl
private theorem fdwShiftFormalB_coeff_formula (g x0 u v t : ℕ)
    (ht : 1 ≤ t) (htg : t ≤ g) :
    (fdwShiftFormalB g x0 u v).coeff (g - t) =
      Polynomial.C (∑ a ∈ range (u + 1), ∑ c ∈ range (v + 1),
        fdw u a * fdw v c * dd (piPoly g t) (x0 + a : ℚ) c) := by
  change outerCoeffHom (g - t)
    (∑ a ∈ range (u + 1), ∑ c ∈ range (v + 1),
      ratConst (fdw u a * fdw v c) *
        shiftB (formalB g (x0 + a) c -
          Polynomial.C Polynomial.X * (aVar - ratConst 1) ^ g * formalA g (x0 + a) c)) = _
  simp_rw [outerCoeffHom_sum]
  simp_rw [outerCoeffHom_apply]
  simp_rw [ratConst, Polynomial.coeff_C_mul]
  simp only [map_sum, map_mul]

  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro c hc
  have hentry :
      (shiftB (formalB g (x0 + a) c -
        Polynomial.C Polynomial.X * (aVar - Polynomial.C (Polynomial.C 1)) ^ g *
          formalA g (x0 + a) c)).coeff (g - t) = Polynomial.C (dd (piPoly g t) (x0 + a : ℚ) c) := by
    simpa [ratConst, cq] using coeff_shiftPoleLower g (x0 + a) c t ht htg
  rw [hentry]
theorem fdwShiftFormalC_coeff_zero (g x0 u v : ℕ)
    (hdeg : (bp g g).natDegree ≤ u + v) :
    (fdwShiftFormalC g x0 u v).coeff 0 = 0 := by
  have hz := fwdDiff2_dd_eq_zero (bp g g) (x0 : ℚ) hdeg
  rw [fdwShiftFormalC_coeff_formula, hz]
  simp

theorem fdwShiftFormalB_coeff (g x0 u v t : ℕ)
    (ht : 1 ≤ t) (htg : t ≤ g)
    (hdeg : (piPoly g t).natDegree ≤ u + v) :
    (fdwShiftFormalB g x0 u v).coeff (g - t) = 0 := by
  have hz := fwdDiff2_dd_eq_zero (piPoly g t) (x0 : ℚ) hdeg
  rw [fdwShiftFormalB_coeff_formula g x0 u v t ht htg, hz]
  simp

theorem fdwShiftFormalC_X_dvd_of_le (g x0 u v : ℕ)
    (hguv : g ≤ u + v) :
    (Polynomial.X : BivPoly) ∣ fdwShiftFormalC g x0 u v := by
  rw [Polynomial.X_dvd_iff]
  have hbp : (bp g g).natDegree ≤ g := bp_natDegree_le g g
  exact fdwShiftFormalC_coeff_zero g x0 u v (hbp.trans hguv)

theorem fdwShiftFormalB_X_pow_dvd (g x0 u v : ℕ) :
    (Polynomial.X : BivPoly) ^ min g (u + v + 1) ∣
      fdwShiftFormalB g x0 u v := by
  rw [Polynomial.X_pow_dvd_iff]
  intro k hk
  have hkg : k < g := Nat.lt_of_lt_of_le hk (Nat.min_le_left _ _)
  have hkuv : k ≤ u + v := by
    have h := Nat.lt_of_lt_of_le hk (Nat.min_le_right _ _)
    omega
  let t : ℕ := g - k
  have ht : 1 ≤ t := by
    dsimp [t]
    omega
  have htg : t ≤ g := by
    dsimp [t]
    omega
  have hgt : g - t = k := by
    dsimp [t]
    omega
  have hdeg : (piPoly g t).natDegree ≤ u + v := by
    calc
      (piPoly g t).natDegree ≤ g - t := piPoly_natDegree_le g t ht htg
      _ = k := hgt
      _ ≤ u + v := hkuv
  simpa [hgt] using fdwShiftFormalB_coeff g x0 u v t ht htg hdeg

end
