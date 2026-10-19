/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.B3.G2Smoothing
import Li2Lean.V.VLiteralNestedBridge

open MeasureTheory

namespace Li2Lean
namespace B3

noncomputable section

/-! A generic Fubini step for the C7 raw-integral-to-S1 bridge.  The pointwise
factorization and the sole product-integrability premise are kept explicit;
this theorem does not claim that the literal v13 kernel factorization has
already been proved. -/
theorem iterated_integral_mul_factorization
    {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace γ]
    (μx : Measure γ) (μv : Measure α) (μz : Measure β)
    [SigmaFinite μx] [SigmaFinite μv]
    (A : γ → α → ℂ) (B : α → β → ℂ)
    (hSwap : Integrable
      (fun y : γ × α => A y.1 y.2 * ∫ z, B y.2 z ∂μz)
      (μx.prod μv)) :
    (∫ x, ∫ v, ∫ z, A x v * B v z ∂μz ∂μv ∂μx) =
      ∫ v, (∫ x, A x v ∂μx) * (∫ z, B v z ∂μz) ∂μv := by
  calc
    (∫ x, ∫ v, ∫ z, A x v * B v z ∂μz ∂μv ∂μx) =
        ∫ x, ∫ v, A x v * (∫ z, B v z ∂μz) ∂μv ∂μx := by
      apply integral_congr_ae
      filter_upwards [] with x
      apply integral_congr_ae
      filter_upwards [] with v
      rw [integral_const_mul]
    _ = ∫ v, ∫ x, A x v * (∫ z, B v z ∂μz) ∂μx ∂μv :=
      integral_integral_swap hSwap
    _ = ∫ v, (∫ x, A x v ∂μx) * (∫ z, B v z ∂μz) ∂μv := by
      apply integral_congr_ae
      filter_upwards [] with v
      rw [integral_mul_const]

/-! The specialized C7 helper exposes precisely the missing canonical-kernel
identity and the integrability needed to exchange x and v.  The actual S1
kernel construction must prove these hypotheses from the literal v13 formulas. -/
theorem vContourTripleIntegral_eq_canonicalS1Andreief_def
    {q n : ℕ} (D : V.V13LiteralAndreiefData q n)
    (hKernel : ∀ (x : Fin (4 * n) → ℝ) (v : Fin (5 * n) → ℝ)
        (p : Fin (4 * n) → Fin 4 × ℝ),
      (∏ i : Fin (4 * n), V.Literal.vContourWeight q (p i)) *
          V.Literal.vContourPhi q n x v
            (fun i => V.Literal.vContourPoint q (p i).1 (p i).2) =
        V.andreiefProduct (D.M2 v) (D.a2 v) (D.b2 v) x *
          V.andreiefProduct (D.M1 v) (D.a1 v) (D.b1 v) p)
    (hSwap : Integrable
      (fun y : (Fin (4 * n) → ℝ) × (Fin (5 * n) → ℝ) =>
        V.andreiefProduct (D.M2 y.2) (D.a2 y.2) (D.b2 y.2) y.1 *
          ∫ p : Fin (4 * n) → Fin 4 × ℝ,
            V.andreiefProduct (D.M1 y.2) (D.a1 y.2) (D.b1 y.2) p
              ∂(Measure.pi fun _ : Fin (4 * n) => V.Literal.vContourParameterMeasure))
      ((Measure.pi fun _ : Fin (4 * n) => V.Literal.vContourUnitIntervalMeasure).prod
        (Measure.pi fun _ : Fin (5 * n) => V.Literal.vContourUnitIntervalMeasure))) :
    V.Literal.vContourTripleIntegral q n =
      ∫ v : Fin (5 * n) → ℝ,
        (∫ x : Fin (4 * n) → ℝ,
          V.andreiefProduct (D.M2 v) (D.a2 v) (D.b2 v) x
            ∂(Measure.pi fun _ : Fin (4 * n) => V.Literal.vContourUnitIntervalMeasure)) *
        (∫ p : Fin (4 * n) → Fin 4 × ℝ,
          V.andreiefProduct (D.M1 v) (D.a1 v) (D.b1 v) p
            ∂(Measure.pi fun _ : Fin (4 * n) => V.Literal.vContourParameterMeasure))
          ∂(Measure.pi fun _ : Fin (5 * n) => V.Literal.vContourUnitIntervalMeasure) := by
  let μx : Measure (Fin (4 * n) → ℝ) :=
    Measure.pi fun _ : Fin (4 * n) => V.Literal.vContourUnitIntervalMeasure
  let μv : Measure (Fin (5 * n) → ℝ) :=
    Measure.pi fun _ : Fin (5 * n) => V.Literal.vContourUnitIntervalMeasure
  let μz : Measure (Fin (4 * n) → Fin 4 × ℝ) :=
    Measure.pi fun _ : Fin (4 * n) => V.Literal.vContourParameterMeasure
  let A : (Fin (4 * n) → ℝ) → (Fin (5 * n) → ℝ) → ℂ :=
    fun x v => V.andreiefProduct (D.M2 v) (D.a2 v) (D.b2 v) x
  let B : (Fin (5 * n) → ℝ) → (Fin (4 * n) → Fin 4 × ℝ) → ℂ :=
    fun v p => V.andreiefProduct (D.M1 v) (D.a1 v) (D.b1 v) p
  letI : SigmaFinite V.Literal.vContourUnitIntervalMeasure := D.sigma_v
  letI : SigmaFinite V.Literal.vContourParameterMeasure := D.sigma_z
  have hSwap' : Integrable (fun y => A y.1 y.2 * ∫ p, B y.2 p ∂μz)
      (μx.prod μv) := by
    simpa [A, B, μx, μv, μz] using hSwap
  have hFactor : ∀ (x : Fin (4 * n) → ℝ) (v : Fin (5 * n) → ℝ)
      (p : Fin (4 * n) → Fin 4 × ℝ),
      (∏ i : Fin (4 * n), V.Literal.vContourWeight q (p i)) *
          V.Literal.vContourPhi q n x v
            (fun i => V.Literal.vContourPoint q (p i).1 (p i).2) = A x v * B v p := by
    simpa [A, B] using hKernel
  calc
    V.Literal.vContourTripleIntegral q n =
        ∫ x, ∫ v, ∫ p, A x v * B v p ∂μz ∂μv ∂μx := by
      unfold V.Literal.vContourTripleIntegral
      apply integral_congr_ae
      filter_upwards [] with x
      apply integral_congr_ae
      filter_upwards [] with v
      apply integral_congr_ae
      filter_upwards [] with p
      exact hFactor x v p
    _ = ∫ v, (∫ x, A x v ∂μx) * (∫ p, B v p ∂μz) ∂μv :=
      iterated_integral_mul_factorization μx μv μz A B hSwap'
    _ = ∫ v : Fin (5 * n) → ℝ,
        (∫ x : Fin (4 * n) → ℝ,
          V.andreiefProduct (D.M2 v) (D.a2 v) (D.b2 v) x
            ∂(Measure.pi fun _ : Fin (4 * n) => V.Literal.vContourUnitIntervalMeasure)) *
        (∫ p : Fin (4 * n) → Fin 4 × ℝ,
          V.andreiefProduct (D.M1 v) (D.a1 v) (D.b1 v) p
            ∂(Measure.pi fun _ : Fin (4 * n) => V.Literal.vContourParameterMeasure))
          ∂(Measure.pi fun _ : Fin (5 * n) => V.Literal.vContourUnitIntervalMeasure) := by
      simp [A, B, μx, μv, μz]

theorem vContourTripleIntegral_eq_canonicalS1Andreief
    {q n : ℕ} (D : V.V13LiteralAndreiefData q n)
    (hKernel : ∀ (x : Fin (4 * n) → ℝ) (v : Fin (5 * n) → ℝ)
        (p : Fin (4 * n) → Fin 4 × ℝ),
      (∏ i : Fin (4 * n), V.Literal.vContourWeight q (p i)) *
          V.Literal.vContourPhi q n x v
            (fun i => V.Literal.vContourPoint q (p i).1 (p i).2) =
        V.andreiefProduct (D.M2 v) (D.a2 v) (D.b2 v) x *
          V.andreiefProduct (D.M1 v) (D.a1 v) (D.b1 v) p)
    (hSwap : Integrable
      (fun y : (Fin (4 * n) → ℝ) × (Fin (5 * n) → ℝ) =>
        V.andreiefProduct (D.M2 y.2) (D.a2 y.2) (D.b2 y.2) y.1 *
          ∫ p : Fin (4 * n) → Fin 4 × ℝ,
            V.andreiefProduct (D.M1 y.2) (D.a1 y.2) (D.b1 y.2) p
              ∂(Measure.pi fun _ : Fin (4 * n) => V.Literal.vContourParameterMeasure))
      ((Measure.pi fun _ : Fin (4 * n) => V.Literal.vContourUnitIntervalMeasure).prod
        (Measure.pi fun _ : Fin (5 * n) => V.Literal.vContourUnitIntervalMeasure))) :
    V.Literal.vContourTripleIntegral q n = V.v13S1AndreiefIntegral D := by
  rw [V.v13S1AndreiefIntegral]
  exact vContourTripleIntegral_eq_canonicalS1Andreief_def D hKernel hSwap

/-! A scalar version of the C7 bridge.  The literal determinant rows carry
the fixed `q`-power produced by the `(-q)^i` contour rows and the
`q/x` Cauchy--Vandermonde substitution.  Keeping that scalar explicit avoids
silently identifying the raw integrand with the determinant product. -/
theorem vContourTripleIntegral_eq_const_mul_canonicalS1Andreief
    {q n : ℕ} (D : V.V13LiteralAndreiefData q n) (c : ℂ)
    (hKernel : ∀ (x : Fin (4 * n) → ℝ) (v : Fin (5 * n) → ℝ)
        (p : Fin (4 * n) → Fin 4 × ℝ),
      (∏ i : Fin (4 * n), V.Literal.vContourWeight q (p i)) *
          V.Literal.vContourPhi q n x v
            (fun i => V.Literal.vContourPoint q (p i).1 (p i).2) =
        c * (V.andreiefProduct (D.M2 v) (D.a2 v) (D.b2 v) x *
          V.andreiefProduct (D.M1 v) (D.a1 v) (D.b1 v) p))
    (hSwap : Integrable
      (fun y : (Fin (4 * n) → ℝ) × (Fin (5 * n) → ℝ) =>
        V.andreiefProduct (D.M2 y.2) (D.a2 y.2) (D.b2 y.2) y.1 *
          ∫ p : Fin (4 * n) → Fin 4 × ℝ,
            V.andreiefProduct (D.M1 y.2) (D.a1 y.2) (D.b1 y.2) p
              ∂(Measure.pi fun _ : Fin (4 * n) => V.Literal.vContourParameterMeasure))
      ((Measure.pi fun _ : Fin (4 * n) => V.Literal.vContourUnitIntervalMeasure).prod
        (Measure.pi fun _ : Fin (5 * n) => V.Literal.vContourUnitIntervalMeasure))) :
    V.Literal.vContourTripleIntegral q n =
      c * V.v13S1AndreiefIntegral D := by
  let μx : Measure (Fin (4 * n) → ℝ) :=
    Measure.pi fun _ : Fin (4 * n) => V.Literal.vContourUnitIntervalMeasure
  let μv : Measure (Fin (5 * n) → ℝ) :=
    Measure.pi fun _ : Fin (5 * n) => V.Literal.vContourUnitIntervalMeasure
  let μz : Measure (Fin (4 * n) → Fin 4 × ℝ) :=
    Measure.pi fun _ : Fin (4 * n) => V.Literal.vContourParameterMeasure
  let A : (Fin (4 * n) → ℝ) → (Fin (5 * n) → ℝ) → ℂ :=
    fun x v => V.andreiefProduct (D.M2 v) (D.a2 v) (D.b2 v) x
  let B : (Fin (5 * n) → ℝ) → (Fin (4 * n) → Fin 4 × ℝ) → ℂ :=
    fun v p => V.andreiefProduct (D.M1 v) (D.a1 v) (D.b1 v) p
  letI : SigmaFinite V.Literal.vContourUnitIntervalMeasure := D.sigma_v
  letI : SigmaFinite V.Literal.vContourParameterMeasure := D.sigma_z
  have hSwap' : Integrable (fun y => A y.1 y.2 * ∫ p, B y.2 p ∂μz)
      (μx.prod μv) := by
    simpa [A, B, μx, μv, μz] using hSwap
  have hFactor : ∀ (x : Fin (4 * n) → ℝ) (v : Fin (5 * n) → ℝ)
      (p : Fin (4 * n) → Fin 4 × ℝ),
      (∏ i : Fin (4 * n), V.Literal.vContourWeight q (p i)) *
          V.Literal.vContourPhi q n x v
            (fun i => V.Literal.vContourPoint q (p i).1 (p i).2) =
        c * (A x v * B v p) := by
    simpa [A, B] using hKernel
  calc
    V.Literal.vContourTripleIntegral q n =
        ∫ x, ∫ v, ∫ p, c * (A x v * B v p) ∂μz ∂μv ∂μx := by
      unfold V.Literal.vContourTripleIntegral
      apply integral_congr_ae
      filter_upwards [] with x
      apply integral_congr_ae
      filter_upwards [] with v
      apply integral_congr_ae
      filter_upwards [] with p
      exact hFactor x v p
    _ = c * (∫ x, ∫ v, ∫ p, A x v * B v p ∂μz ∂μv ∂μx) := by
      simp_rw [integral_const_mul]
    _ = c * (∫ v, (∫ x, A x v ∂μx) * (∫ p, B v p ∂μz) ∂μv) := by
      rw [iterated_integral_mul_factorization μx μv μz A B hSwap']
    _ = c * V.v13S1AndreiefIntegral D := by
      simp [V.v13S1AndreiefIntegral, A, B, μx, μv, μz]

end
end B3
end Li2Lean
