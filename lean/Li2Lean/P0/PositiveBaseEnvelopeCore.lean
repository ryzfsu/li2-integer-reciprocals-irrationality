/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.PositiveBaseParam
import Li2Lean.P0.FrequencyLimit

open MeasureTheory

namespace Li2Lean.P0.PositiveBase

noncomputable section

open scoped BigOperators ENNReal

open Li2Lean.P0
open Li2Lean.P0.Config

/-! ## q-dependent literal source data -/

/-- The literal determinant value at `Li₂(1/q)` for the q-polynomial. -/
noncomputable def qGmBeta (q : ℕ) (m : ℕ) : ℂ :=
  Polynomial.eval₂ (algebraMap ℚ ℂ) (li2InvValue (q : ℤ) : ℂ)
    (p0CanonicalPolynomial (q : ℤ) m)

/-- The q-dependent pinned source factor in the absolute contour integrand. -/
noncomputable def qUReal (q g i : ℕ) : ℝ :=
  (q : ℝ) ^ i * (Nat.choose (i + g) g : ℝ)

/-- The q-dependent frequency weight in the absolute contour integrand. -/
noncomputable def qFrequencyWeightReal (q g r : ℕ) : ℝ :=
  (Nat.choose (r - 1) g : ℝ) / (q : ℝ) ^ r

/-- The q-dependent absolute contour integrand.  The three Cauchy minors are
unchanged; every source factor carrying the base is explicit here. -/
noncomputable def qContourQValue {m : ℕ} (q : ℕ) (S : Finset ℕ)
    (h4 : 4 ∣ m) (hSI : S ⊆ Iset m) (R : Fin m → ℕ)
    (hR : StrictMono R) (Z : Fin (m - S.card) → ℂ) : ℝ :=
  let minors := contourQMinors S h4 hSI R hR Z
  (∏ a ∈ S, Real.log (q : ℝ) * qUReal q (m / 2) a) *
    (∏ i : Fin m, qFrequencyWeightReal q (m / 2) (R i)) *
    (∏ i : Fin (m - S.card), ‖p0EntireQ (q : ℤ) (m / 2) (Z i)‖) *
    ‖minors.1 * minors.2.1 * minors.2.2‖

private theorem qPinned_subset_Iset (C : FiniteConfiguration) :
    C.pinned ⊆ Iset C.m := by
  rw [Iset_eq_paper_interval C.m C.four_dvd_m]
  simpa [pinnedUniverse] using C.pinned_subset

private theorem qContour_count_eq (C : FiniteConfiguration) :
    C.contourCount = C.m - C.pinned.card := by
  have h := C.mass_balance
  omega

private noncomputable def qScaledContourPoint (C : FiniteConfiguration)
    (i : Fin C.contourCount) : ℂ :=
  Complex.ofReal (C.m : ℝ) * C.contour i

/-- The actual q-weight attached to a finite configuration. -/
noncomputable def qLiteralConfigQWeight (q : ℕ)
    (C : FiniteConfiguration) : ℝ :=
  qContourQValue q C.pinned C.four_dvd_m (qPinned_subset_Iset C)
    (fun i : Fin C.m =>
      orderedElem C.frequency (Fin.cast C.frequency_card.symm i))
    (by
      intro i j hij
      exact (Finset.orderIsoOfFin C.frequency C.frequency_card).strictMono hij)
    (fun i : Fin (C.m - C.pinned.card) =>
      qScaledContourPoint C (Fin.cast (qContour_count_eq C).symm i))

/-! q = 2 is a regression for the source definitions only.  No q >= 3
statement below invokes these lemmas. -/

theorem qGmBeta_two (m : ℕ) : qGmBeta 2 m = GmBeta m := by
  rfl

theorem qUReal_two (g i : ℕ) : qUReal 2 g i = UReal g i := by
  simp [qUReal, UReal]

theorem qFrequencyWeightReal_two (g r : ℕ) :
    qFrequencyWeightReal 2 g r = frequencyWeightReal g r := by
  simp [qFrequencyWeightReal, frequencyWeightReal]

theorem qContourQValue_two {m : ℕ} (S : Finset ℕ) (h4 : 4 ∣ m)
    (hSI : S ⊆ Iset m) (R : Fin m → ℕ) (hR : StrictMono R)
    (Z : Fin (m - S.card) → ℂ) :
    qContourQValue 2 S h4 hSI R hR Z = contourQValue S h4 hSI R hR Z := by
  simp only [qContourQValue, contourQValue, qUReal, qFrequencyWeightReal,
    UReal, frequencyWeightReal, p0EntireQ_two, Nat.cast_ofNat, ell]

/-! ## q-dependent coefficient envelope -/

/-- The q-parametric absolute contour integrand.  It uses the q-specific
one-body factors in `qContourQValue`, while retaining the same ellipse
parameter density and increasing-frequency domain as `FrequencyLimit`. -/
def qEnvelopeTerm (q m : ℕ) (h4 : 4 ∣ m) (S : Finset ℕ)
    (hSI : S ⊆ Iset m)
    (r : IncreasingFrequencyTuple (m / 2) m)
    (u : Fin (m - S.card) → ℝ) : ℝ :=
  qContourQValue q S h4 hSI r.val r.property.1
    (fun i => p0EllipsePoint m (u i)) *
      ∏ i : Fin (m - S.card), contourArcDensity m (u i)

/-- Full q-specific contribution of a pinned set to the absolute frequency
envelope, with no finite cutoff or free energy function. -/
def qFullContribution (q m : ℕ) (h4 : 4 ∣ m) (S : Finset ℕ)
    (hSI : S ⊆ Iset m) : ℝ≥0∞ :=
  ENNReal.ofReal ((Nat.factorial (m - S.card) : ℝ)⁻¹) *
    ∫⁻ u : Fin (m - S.card) → ℝ,
      ∑' r : IncreasingFrequencyTuple (m / 2) m,
        ENNReal.ofReal (qEnvelopeTerm q m h4 S hSI r u)
      ∂(ContourKit.productMeasure contourParameterMeasure)

/-- Actual q-specific full contour envelope, parallel to
`FrequencyLimit.fullEnvelope`. -/
def qFullEnvelope (q m : ℕ) (h4 : 4 ∣ m) : ℝ≥0∞ := by
  classical
  exact ∑ S ∈ (Iset m).powerset,
    if hSI : S ⊆ Iset m then qFullContribution q m h4 S hSI else 0

/-- The fixed q-envelope bound is the real value of the actual full contour
integral. This definition leaves its finiteness and coefficient domination
to the named q-parametric analytic producer. -/
noncomputable def qEInfinity (q m : ℕ) (h4 : 4 ∣ m) : ℝ :=
  (qFullEnvelope q m h4).toReal

/-- A signed coefficient envelope at the actual q-polynomial and q-value,
bounded by the actual q-specific full contour integral. -/
def QSignedCoefficientEnvelope (q : ℕ) : Prop :=
  3 ≤ q → q ≤ 11 →
    ∀ m : ℕ, 8 ≤ m → ∀ h4 : 4 ∣ m,
      ‖qGmBeta q m‖ ≤ qEInfinity q m h4

end

end Li2Lean.P0.PositiveBase
