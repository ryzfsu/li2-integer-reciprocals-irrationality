/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.V.VLiteralNestedBridge

namespace Li2Lean.V

noncomputable section

open MeasureTheory Set

/- The combined column coordinate records `J = [n, 10n)` in its two
   summands; this is the column order used by the v13 C block. -/
/-- Column number in the v13 interval `J`, `v-arithmetic.tex:15-16` and
`v-analytic.tex:127-153`. -/
def vLiteralContourColumnIndex (n : ℕ)
    (c : Fin (4 * n) ⊕ Fin (5 * n)) : ℕ :=
  Sum.elim (fun k => n + k.val) (fun l => n + 4 * n + l.val) c

/- The contour rows are the actual `C` rows. The other `L` rows are supplied
   by the preceding v-variable Andreief step, so they remain an input here. -/
/-- The v13 middle matrix with its literal contour C rows,
`v-arithmetic.tex:24-27` and `v-analytic.tex:96-104,127-153`. -/
def vLiteralContourM1 (q n : ℕ)
    (bottom : Fin (5 * n) → (Fin (4 * n) ⊕ Fin (5 * n)) → ℂ) :
    Matrix (Fin (4 * n) ⊕ Fin (5 * n))
      (Fin (4 * n) ⊕ Fin (5 * n)) ℂ :=
  fun r c => Sum.elim
    (fun k => (vCEntry (-(q : ℤ)) (vIIndexNat n k.val)
      (vLiteralContourColumnIndex n c) : ℂ))
    (fun l => bottom l c) r

/- These are the row and column factors of `C_ij=(-q)^i int_Gamma z^(j-i-1) dz`.
   The path weight carries the signed-chain coefficients, as in v13. -/
/-- The row factor for the contour Andreief identity,
`v-analytic.tex:96-104,127-153`. -/
def vLiteralContourA1 (q n : ℕ) (_v : Fin (5 * n) → ℝ)
    (k : Fin (4 * n)) (p : Fin 4 × ℝ) : ℂ :=
  let i := vIIndexNat n k.val
  (-(q : ℂ)) ^ i *
    (Literal.vContourWeight q p *
      Literal.vContourPoint q p.1 p.2 ^ (-(i : ℤ) - 1))

/-- The column factor for the contour Andreief identity,
`v-analytic.tex:96-104,127-153`. -/
def vLiteralContourB1 (q n : ℕ) (_v : Fin (5 * n) → ℝ)
    (p : Fin 4 × ℝ) (c : Fin (4 * n) ⊕ Fin (5 * n)) : ℂ :=
  Literal.vContourPoint q p.1 p.2 ^
    (vLiteralContourColumnIndex n c : ℤ)

/- Nonvanishing on each of the four v13 path pieces, using the existing
   geometric path lemmas. -/
/- v13 `v-analytic.tex:87-94`. -/
private theorem vLiteralContourPoint_ne_zero (q : ℕ) (hq : 2 ≤ q)
    (piece : Fin 4) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    Literal.vContourPoint q piece t ≠ 0 := by
  fin_cases piece
  · change Literal.vContourPoint q 0 t ≠ 0
    rw [literal_piece_zero_eq_vNegativeSegment]
    exact vNegativeSegment_ne_zero hq ht
  · change Literal.vContourPoint q 1 t ≠ 0
    rw [literal_piece_one_eq_vPositiveSegment]
    exact vPositiveSegment_ne_zero ht
  · change Literal.vContourPoint q 2 t ≠ 0
    rw [literal_piece_two_eq_vUpperArc]
    exact vUpperArc_ne_zero
  · change Literal.vContourPoint q 3 t ≠ 0
    rw [literal_piece_three_eq_vLowerArc]
    exact vLowerArc_ne_zero

/- Compactness is used only to establish integrability of each literal
   Laurent kernel on the four-piece positive parameter space. -/
/-- Every integer Laurent kernel on the v13 contour parameter space is
integrable, `v-analytic.tex:87-104`. -/
theorem vLiteralContourPowerIntegrable (q : ℕ) (hq : 2 ≤ q) (d : ℤ) :
    Integrable
      (Literal.vContourIntegrand q (fun z : ℂ => z ^ d))
      Literal.vContourParameterMeasure := by
  let g : Fin 4 × ℝ → ℂ := fun p =>
    Literal.vContourIntegrand q (fun z : ℂ => z ^ d) p
  have hcont : ContinuousOn g
      ((Set.univ : Set (Fin 4)) ×ˢ Set.Icc (0 : ℝ) 1) := by
    apply continuousOn_of_forall_continuousAt
    rintro ⟨piece, t⟩ hp
    have ht : t ∈ Set.Icc (0 : ℝ) 1 := (Set.mem_prod.mp hp).2
    have hpnt : Literal.vContourPoint q piece t ≠ 0 :=
      vLiteralContourPoint_ne_zero q hq piece ht
    have hpoint : ContinuousAt
        (fun s : ℝ => Literal.vContourPoint q piece s) t := by
      fin_cases piece <;> simp [Literal.vContourPoint] <;> fun_prop
    have hzpow : ContinuousAt
        (fun s : ℝ => Literal.vContourPoint q piece s ^ d) t :=
      hpoint.zpow₀ d (Or.inl hpnt)
    have hw : ContinuousAt
        (fun s : ℝ => Literal.vContourWeight q (piece, s)) t := by
      fin_cases piece <;>
        simp [Literal.vContourWeight, Literal.vContourComponentWeight,
          Literal.vContourDerivative, Literal.vContourPoint] <;> fun_prop
    have hs : ({piece} ×ˢ (Set.univ : Set ℝ)) ∈ nhds (piece, t) := by
      apply (isOpen_discrete ({piece} : Set (Fin 4))).prod isOpen_univ |>.mem_nhds
      simp
    have hev : (fun p : Fin 4 × ℝ => g p) =ᶠ[nhds (piece, t)]
        (fun p : Fin 4 × ℝ => Literal.vContourWeight q (piece, p.2) *
          Literal.vContourPoint q piece p.2 ^ d) := by
      filter_upwards [hs] with p hp'
      rcases p with ⟨p1, p2⟩
      have hpiece : p1 = piece := by
        exact Set.mem_singleton_iff.mp (Set.mem_prod.mp hp').1
      subst p1
      rfl
    have hcomp : ContinuousAt
        (fun p : Fin 4 × ℝ => Literal.vContourWeight q (piece, p.2) *
          Literal.vContourPoint q piece p.2 ^ d) (piece, t) := by
      change ContinuousAt
        ((fun s : ℝ => Literal.vContourWeight q (piece, s) *
          Literal.vContourPoint q piece s ^ d) ∘ Prod.snd) (piece, t)
      exact (hw.mul hzpow).comp (x := (piece, t)) (f := Prod.snd)
        (g := fun s : ℝ => Literal.vContourWeight q (piece, s) *
          Literal.vContourPoint q piece s ^ d) continuousAt_snd
    exact hcomp.congr_of_eventuallyEq hev
  have hcompact : IsCompact
      ((Set.univ : Set (Fin 4)) ×ˢ Set.Icc (0 : ℝ) 1) :=
    isCompact_univ.prod isCompact_Icc
  have hIntOn : IntegrableOn g
      ((Set.univ : Set (Fin 4)) ×ˢ Set.Icc (0 : ℝ) 1)
      (Measure.count.prod volume) :=
    ContinuousOn.integrableOn_compact hcompact hcont
  have hIntRestrict : Integrable g
      ((Measure.count.prod volume).restrict
        ((Set.univ : Set (Fin 4)) ×ˢ Set.Icc (0 : ℝ) 1)) := hIntOn.integrable
  have hmeasure :
      (Measure.count.prod volume).restrict
          ((Set.univ : Set (Fin 4)) ×ˢ Set.Icc (0 : ℝ) 1) =
        Measure.count.prod (volume.restrict (Set.Icc (0 : ℝ) 1)) := by
    rw [← Measure.prod_restrict]
    simp
  rw [hmeasure] at hIntRestrict
  exact hIntRestrict

/- The factorization is the Laurent exponent identity in the C block. -/
/-- The two Andreief factors multiply to the v13 Laurent kernel,
`v-analytic.tex:96-104,127-153`. -/
theorem vLiteralContourA1_mul_B1 (q n : ℕ) (hq : 2 ≤ q)
    (v : Fin (5 * n) → ℝ)
    (k : Fin (4 * n)) (c : Fin (4 * n) ⊕ Fin (5 * n))
    (p : Fin 4 × ℝ)
    (hp : p.2 ∈ Set.Icc (0 : ℝ) 1) :
    vLiteralContourA1 q n v k p * vLiteralContourB1 q n v p c =
      (-(q : ℂ)) ^ (vIIndexNat n k.val) *
        (Literal.vContourWeight q p *
          Literal.vContourPoint q p.1 p.2 ^
          ((vLiteralContourColumnIndex n c : ℤ) -
            (vIIndexNat n k.val : ℤ) - 1)) := by
  let i := vIIndexNat n k.val
  let j := vLiteralContourColumnIndex n c
  let z := Literal.vContourPoint q p.1 p.2
  change (-(q : ℂ)) ^ i * (Literal.vContourWeight q p *
      z ^ (-(i : ℤ) - 1)) * z ^ (j : ℤ) =
    (-(q : ℂ)) ^ i * (Literal.vContourWeight q p *
      z ^ ((j : ℤ) - (i : ℤ) - 1))
  have hz : z ≠ 0 := vLiteralContourPoint_ne_zero q hq p.1 hp
  have hexp : (-(i : ℤ) - 1) + (j : ℤ) = (j : ℤ) - (i : ℤ) - 1 := by ring
  calc
    (-(q : ℂ)) ^ i * (Literal.vContourWeight q p *
        z ^ (-(i : ℤ) - 1)) * z ^ (j : ℤ) =
        (-(q : ℂ)) ^ i * (Literal.vContourWeight q p *
          (z ^ (-(i : ℤ) - 1) * z ^ (j : ℤ))) := by
      ring
    _ = (-(q : ℂ)) ^ i * (Literal.vContourWeight q p *
        z ^ ((-(i : ℤ) - 1) + (j : ℤ))) := by
      rw [← zpow_add₀ hz]
    _ = (-(q : ℂ)) ^ i * (Literal.vContourWeight q p *
        z ^ ((j : ℤ) - (i : ℤ) - 1)) := by rw [hexp]

/- The chosen positive parameter space is supported on the four unit
   intervals that parameterize the v13 contour. -/
/- v13 `v-analytic.tex:87-94`. -/
private theorem vLiteralContourParameter_mem_ae :
    ∀ᵐ p : Fin 4 × ℝ ∂Literal.vContourParameterMeasure,
      p ∈ (Set.univ : Set (Fin 4)) ×ˢ Set.Icc (0 : ℝ) 1 := by
  have hmeasure :
      (Measure.count.prod volume).restrict
          ((Set.univ : Set (Fin 4)) ×ˢ Set.Icc (0 : ℝ) 1) =
        Literal.vContourParameterMeasure := by
    rw [← Measure.prod_restrict]
    simp [Literal.vContourParameterMeasure]
  rw [← hmeasure]
  exact ae_restrict_mem (MeasurableSet.univ.prod measurableSet_Icc)

/- The integrability field corresponding to `hmom1` in the nested Andreief
   interface is proved for the actual v13 row and column factors. -/
/-- The literal C-row integrand is integrable, `v-analytic.tex:87-104,127-153`.
-/
theorem vLiteralContourA1B1_integrable (q n : ℕ) (hq : 2 ≤ q)
    (v : Fin (5 * n) → ℝ) (k : Fin (4 * n))
    (c : Fin (4 * n) ⊕ Fin (5 * n)) :
    Integrable
      (fun p : Fin 4 × ℝ => vLiteralContourA1 q n v k p *
        vLiteralContourB1 q n v p c)
      Literal.vContourParameterMeasure := by
  let i := vIIndexNat n k.val
  let d := (vLiteralContourColumnIndex n c : ℤ) - (i : ℤ) - 1
  have hbase := vLiteralContourPowerIntegrable q hq d
  have hmul : Integrable
      (fun p : Fin 4 × ℝ => (-(q : ℂ)) ^ i *
        Literal.vContourIntegrand q (fun z : ℂ => z ^ d) p)
      Literal.vContourParameterMeasure := by
    exact hbase.const_mul _
  have hsupport : ∀ᵐ p : Fin 4 × ℝ ∂Literal.vContourParameterMeasure,
      p ∈ (Set.univ : Set (Fin 4)) ×ˢ Set.Icc (0 : ℝ) 1 := by
    exact vLiteralContourParameter_mem_ae
  apply hmul.congr
  filter_upwards [hsupport] with p hp
  have hp' : p.2 ∈ Set.Icc (0 : ℝ) 1 := (Set.mem_prod.mp hp).2
  have hfac := vLiteralContourA1_mul_B1 q n hq v k c p hp'
  simpa [i, d, Literal.vContourIntegrand] using hfac.symm

/- This theorem is exactly `hmom1` for the top contour block of M1. -/
/-- The actual v13 contour moment entries equal the signed determinant C
entries, `v-arithmetic.tex:24-27` and `v-analytic.tex:96-104,127-153`. -/
theorem vLiteralContourM1_hmom1 (q n : ℕ) (hq : 2 ≤ q)
    (bottom : Fin (5 * n) → (Fin (4 * n) ⊕ Fin (5 * n)) → ℂ)
    (v : Fin (5 * n) → ℝ) (k : Fin (4 * n))
    (c : Fin (4 * n) ⊕ Fin (5 * n)) :
    vLiteralContourM1 q n bottom (Sum.inl k) c =
      ∫ p, vLiteralContourA1 q n v k p * vLiteralContourB1 q n v p c
        ∂Literal.vContourParameterMeasure := by
  let i := vIIndexNat n k.val
  let j := vLiteralContourColumnIndex n c
  calc
    vLiteralContourM1 q n bottom (Sum.inl k) c =
        (-(q : ℂ)) ^ i * Literal.vContourLaurentMoment q
          ((j : ℤ) - (i : ℤ)) := by
      exact (literal_C_entry_eq_laurent_moment q i j hq).symm
    _ = (-(q : ℂ)) ^ i *
        ∫ p, Literal.vContourIntegrand q
          (fun z : ℂ => z ^ ((j : ℤ) - (i : ℤ) - 1)) p
          ∂Literal.vContourParameterMeasure := rfl
    _ = ∫ p, (-(q : ℂ)) ^ i * Literal.vContourIntegrand q
        (fun z : ℂ => z ^ ((j : ℤ) - (i : ℤ) - 1)) p
        ∂Literal.vContourParameterMeasure := by rw [integral_const_mul]
    _ = ∫ p, vLiteralContourA1 q n v k p * vLiteralContourB1 q n v p c
        ∂Literal.vContourParameterMeasure := by
      apply integral_congr_ae
      have hsupport : ∀ᵐ p : Fin 4 × ℝ ∂Literal.vContourParameterMeasure,
          p ∈ (Set.univ : Set (Fin 4)) ×ˢ Set.Icc (0 : ℝ) 1 := by
        exact vLiteralContourParameter_mem_ae
      filter_upwards [hsupport] with p hp
      have hp' : p.2 ∈ Set.Icc (0 : ℝ) 1 := (Set.mem_prod.mp hp).2
      have hfactor := vLiteralContourA1_mul_B1 q n hq v k c p hp'
      simpa [Literal.vContourIntegrand] using hfactor.symm

/- Frozen-base regression: at q=2 this reproduces the existing C-block
   statement from the Li2(1/2) contour code. -/
/-- q=2 instance of the contour-row moment identity,
`v-arithmetic.tex:24-27` and `v-analytic.tex:96-104`. -/
theorem vLiteralContourM1_hmom1_q2 (n : ℕ)
    (bottom : Fin (5 * n) → (Fin (4 * n) ⊕ Fin (5 * n)) → ℂ)
    (v : Fin (5 * n) → ℝ) (k : Fin (4 * n))
    (c : Fin (4 * n) ⊕ Fin (5 * n)) :
    vLiteralContourM1 2 n bottom (Sum.inl k) c =
      ∫ p, vLiteralContourA1 2 n v k p * vLiteralContourB1 2 n v p c
        ∂Literal.vContourParameterMeasure :=
  vLiteralContourM1_hmom1 2 n (by norm_num) bottom v k c

end

end Li2Lean.V

#print axioms Li2Lean.V.vLiteralContourPowerIntegrable
#print axioms Li2Lean.V.vLiteralContourA1_mul_B1
#print axioms Li2Lean.V.vLiteralContourA1B1_integrable
#print axioms Li2Lean.V.vLiteralContourM1_hmom1
#print axioms Li2Lean.V.vLiteralContourM1_hmom1_q2
