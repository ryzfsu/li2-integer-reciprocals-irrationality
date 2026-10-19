/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Typed bridge for the actual v13 literal rows.  The contour moments are proved
in `Li2Lean.V.Literal.VLiteralContourNonzero`; this file only packages those
rows for the existing nested Andreief theorem.
-/

import Li2Lean.V.VLiteralContourNonzero
import Li2Lean.V.NestedAndreief

namespace Li2Lean.V

noncomputable section

open MeasureTheory Set

/-! The explicit four-piece parameterization agrees with the compact VPath
surface already used by the B3 interfaces (`v-analytic.tex:85-104`). -/

theorem literal_piece_zero_eq_vNegativeSegment (q : ℕ) (t : ℝ) :
    Literal.vContourPoint q 0 t = vNegativeSegment q t := by
  simp [Literal.vContourPoint, vNegativeSegment]

theorem literal_piece_one_eq_vPositiveSegment (q : ℕ) (t : ℝ) :
    Literal.vContourPoint q 1 t = vPositiveSegment t := by
  simp [Literal.vContourPoint, vPositiveSegment]

theorem literal_piece_two_eq_vUpperArc (q : ℕ) (t : ℝ) :
    Literal.vContourPoint q 2 t = vUpperArc t := by
  simp [Literal.vContourPoint, vUpperArc, P0.circlePoint]

theorem literal_piece_three_eq_vLowerArc (q : ℕ) (t : ℝ) :
    Literal.vContourPoint q 3 t = vLowerArc t := by
  simp [Literal.vContourPoint, vLowerArc, P0.circlePoint]

theorem literal_laurent_zero (q : ℕ) (hq : 2 ≤ q) :
    Literal.vContourLaurentMoment q 0 = 0 :=
  Literal.vContourLaurentMoment_zero q hq

theorem literal_laurent_nonzero (q : ℕ) (hq : 2 ≤ q) {d : ℤ} (hd : d ≠ 0) :
    Literal.vContourLaurentMoment q d =
      (1 - (-(q : ℂ)) ^ d) / (d : ℂ) :=
  Literal.vContourLaurentMoment_of_ne_zero q hq hd

/-! Unified v13 Laurent moment formula (`v-analytic.tex:96-103`).  The
zero exponent is the separately evaluated branch of the signed Gamma_q
chain; all nonzero exponents use the endpoint primitive. -/
theorem literal_laurent_identity (q : ℕ) (hq : 2 ≤ q) (d : ℤ) :
    Literal.vContourLaurentMoment q d =
      if d = 0 then 0 else (1 - (-(q : ℂ)) ^ d) / (d : ℂ) := by
  by_cases hd : d = 0
  · rw [if_pos hd]
    subst d
    exact Literal.vContourLaurentMoment_zero q hq
  · rw [if_neg hd]
    exact Literal.vContourLaurentMoment_of_ne_zero q hq hd

/-! The first literal matrix row identity.  This is the C block in
`v-arithmetic.tex:24-27`; the Laurent exponent is the integer difference
`j-i`, exactly as in `v-analytic.tex:96-104`. -/

theorem literal_C_entry_eq_laurent_moment (q i j : ℕ) (hq : 2 ≤ q) :
    (-(q : ℂ)) ^ i * Literal.vContourLaurentMoment q ((j : ℤ) - (i : ℤ)) =
      (vCEntry (-(q : ℤ)) i j : ℂ) := by
  by_cases hij : i = j
  · subst j
    rw [show ((i : ℤ) - (i : ℤ)) = 0 by ring]
    rw [literal_laurent_zero q hq]
    simp [vCEntry]
  · have hd : (j : ℤ) - (i : ℤ) ≠ 0 := by
      exact sub_ne_zero.mpr (by exact_mod_cast (Ne.symm hij))
    rw [literal_laurent_nonzero q hq hd]
    have hentry : ((vCEntry (-(q : ℤ)) i j : ℚ) : ℂ) =
        ((-(q : ℂ)) ^ i - (-(q : ℂ)) ^ j) /
          ((j : ℂ) - (i : ℂ)) := by
      simp [vCEntry, hij]
    rw [hentry]
    have hqpos : 0 < q := by omega
    have hq0 : (-(q : ℂ)) ≠ 0 := by
      norm_num [Nat.ne_of_gt hqpos]
    have hpow : (-(q : ℂ)) ^ i * (-(q : ℂ)) ^ ((j : ℤ) - (i : ℤ)) =
        (-(q : ℂ)) ^ j := by
      calc
        (-(q : ℂ)) ^ i * (-(q : ℂ)) ^ ((j : ℤ) - (i : ℤ)) =
            (-(q : ℂ)) ^ i *
              ((-(q : ℂ)) ^ (j : ℤ) / (-(q : ℂ)) ^ (i : ℤ)) := by
                rw [zpow_sub₀ hq0]
        _ = (-(q : ℂ)) ^ i *
              ((-(q : ℂ)) ^ j / (-(q : ℂ)) ^ i) := by
                rw [zpow_natCast, zpow_natCast]
        _ = (-(q : ℂ)) ^ j := by field_simp [hq0]
    have hden : ((j : ℤ) - (i : ℤ) : ℂ) ≠ 0 := by
      exact_mod_cast hd
    have hden' : (j : ℂ) - (i : ℂ) ≠ 0 := by
      exact_mod_cast hd
    field_simp [hden']
    push_cast
    have hnum : (-(q : ℂ)) ^ i *
        (1 - (-(q : ℂ)) ^ ((j : ℤ) - (i : ℤ))) =
        (-(q : ℂ)) ^ i - (-(q : ℂ)) ^ j := by
      rw [mul_sub, mul_one, hpow]
    rw [hnum]
    ring

/- Frozen-base regression (`q=2`, hence `a=-2`) keeps the identical C-block
   statement used by the Li2(1/2) certificate path. -/
theorem literal_C_entry_eq_laurent_moment_q2 (i j : ℕ) :
    (-(2 : ℂ)) ^ i * Literal.vContourLaurentMoment 2
        ((j : ℤ) - (i : ℤ)) =
      (vCEntry (-(2 : ℤ)) i j : ℂ) := by
  exact literal_C_entry_eq_laurent_moment 2 i j (by norm_num)

/-! `V13LiteralAndreiefData` names the remaining literal S0 moment and
alignment obligations. The carriers follow the three domains in
`v-analytic.tex:109-145`: the outer `v` variables lie in `[0,1]`, the middle
variables parameterize the four pieces of `Gamma_q`, and the inner `x`
variables lie in `[0,1]`. The third determinant has `m+n=L` rows, since the
fixed polynomial block has size `n` (`v-arithmetic.tex:13-17`). -/

structure V13LiteralAndreiefData (q n : ℕ) where
  sigma_v : SigmaFinite Literal.vContourUnitIntervalMeasure
  sigma_z : SigmaFinite Literal.vContourParameterMeasure
  M0 : Matrix (Fin (5 * n) ⊕ Fin (4 * n)) (Fin (5 * n) ⊕ Fin (4 * n)) ℂ
  a0 : Fin (5 * n) → ℝ → ℂ
  b0 : ℝ → (Fin (5 * n) ⊕ Fin (4 * n)) → ℂ
  M1 : (Fin (5 * n) → ℝ) →
    Matrix (Fin (4 * n) ⊕ Fin (5 * n)) (Fin (4 * n) ⊕ Fin (5 * n)) ℂ
  a1 : (Fin (5 * n) → ℝ) → Fin (4 * n) → (Fin 4 × ℝ) → ℂ
  b1 : (Fin (5 * n) → ℝ) → (Fin 4 × ℝ) →
    (Fin (4 * n) ⊕ Fin (5 * n)) → ℂ
  M2 : (Fin (5 * n) → ℝ) →
    Matrix (Fin (4 * n) ⊕ Fin n) (Fin (4 * n) ⊕ Fin n) ℂ
  a2 : (Fin (5 * n) → ℝ) → Fin (4 * n) → ℝ → ℂ
  b2 : (Fin (5 * n) → ℝ) → ℝ →
    (Fin (4 * n) ⊕ Fin n) → ℂ
  hint0 : ∀ k c, Integrable (fun t => a0 k t * b0 t c)
    Literal.vContourUnitIntervalMeasure
  hmom0 : ∀ k c, M0 (Sum.inl k) c =
    ∫ t, a0 k t * b0 t c ∂Literal.vContourUnitIntervalMeasure
  hint1 : ∀ v k c, Integrable (fun t => a1 v k t * b1 v t c)
    Literal.vContourParameterMeasure
  hmom1 : ∀ v k c, M1 v (Sum.inl k) c =
    ∫ t, a1 v k t * b1 v t c ∂Literal.vContourParameterMeasure
  hint2 : ∀ v k c, Integrable (fun t => a2 v k t * b2 v t c)
    Literal.vContourUnitIntervalMeasure
  hmom2 : ∀ v k c, M2 v (Sum.inl k) c =
    ∫ t, a2 v k t * b2 v t c ∂Literal.vContourUnitIntervalMeasure
  halign1 : ∀ v, (M1 v).det =
    (P0.Env.rowRepl M0 (fun l => b0 (v l))).det
  halign2 : ∀ v, (M2 v).det =
    (Matrix.of fun k l => a0 k (v l)).det

/-! Applying the existing three nested Andreief identities is now a one-line
consumer theorem. The third matrix uses `m+n=5n` rows, as in the Cauchy--
Vandermonde block of `v-analytic.tex:139-173`. -/
theorem v13_nested_andreief_of_data {q n : ℕ}
    (D : V13LiteralAndreiefData q n) :
    (∫ v : Fin (5 * n) → ℝ,
      (∫ x : Fin (4 * n) → ℝ,
        andreiefProduct (D.M2 v) (D.a2 v) (D.b2 v) x
          ∂(Measure.pi fun _ : Fin (4 * n) => Literal.vContourUnitIntervalMeasure)) *
      (∫ z : Fin (4 * n) → (Fin 4 × ℝ),
        andreiefProduct (D.M1 v) (D.a1 v) (D.b1 v) z
          ∂(Measure.pi fun _ : Fin (4 * n) => Literal.vContourParameterMeasure))
        ∂(Measure.pi fun _ : Fin (5 * n) => Literal.vContourUnitIntervalMeasure)) =
      (((4 * n).factorial : ℂ) ^ 2 * ((5 * n).factorial : ℂ)) * D.M0.det := by
  letI : SigmaFinite Literal.vContourUnitIntervalMeasure := D.sigma_v
  letI : SigmaFinite Literal.vContourParameterMeasure := D.sigma_z
  simpa using
    (nested_andreief (m := 4 * n) (L := 5 * n) (h := n)
      Literal.vContourUnitIntervalMeasure Literal.vContourParameterMeasure
      Literal.vContourUnitIntervalMeasure D.M0 D.a0 D.b0 D.M1 D.a1 D.b1 D.M2 D.a2 D.b2
      D.hint0 D.hmom0 D.hint1 D.hmom1 D.hint2 D.hmom2 D.halign1 D.halign2)

end

end Li2Lean.V

#print axioms Li2Lean.V.literal_laurent_zero
#print axioms Li2Lean.V.literal_laurent_nonzero
#print axioms Li2Lean.V.v13_nested_andreief_of_data
#print axioms Li2Lean.V.literal_C_entry_eq_laurent_moment_q2
