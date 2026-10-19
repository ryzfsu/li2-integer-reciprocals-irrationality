/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.B3.S0TFromP0L6
import Li2Lean.B3.S0TC4
import Li2Lean.B3.S0KernelBridge
import Li2Lean.B3.S0TBudgetAssembly
import Li2Lean.B3.S0ActualInterface
import Li2Lean.B3.SmoothedEnergy
import Li2Lean.V.S0TC5
import Li2Lean.V.OuterMomentPolynomialAdapter
import Li2Lean.V.VZDeterminants
import Li2Lean.V.VXDeterminants
import Mathlib.MeasureTheory.Constructions.Pi

/-!
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

The q-uniform C8 assembly for the signed-V S0 transfer.

The C2--C7 declarations are imported here as the construction boundary:
their concrete measure, reflection, smoothing, kernel, and transfer facts
must be supplied by the reference-measure proof.  This file only performs
the final normalized logarithmic algebra.  In particular, the raw C5--C7
estimate is an explicit hypothesis; it is not replaced by a conclusion-shaped
field or a new sorry.
-/

namespace Li2Lean.B3

open Li2Lean V
open MeasureTheory

/-! ## The determinant-normalization boundary

The three determinant evaluations in the v13 calculation leave a single
scalar.  The contour rows contribute `(-q)^(16*n^2-2*n)` and the
`q/x` Cauchy--Vandermonde block contributes `q^(8*n^2-2*n)`.  Their product
is `q^(24*n^2-4*n)`; the two signs are even for `m=4*n`.  The pointwise
kernel equation below keeps this scalar explicit instead of treating the
unscaled determinant product as the literal integrand.
-/

def vContourQScale (q n : ℕ) : ℂ :=
  (q : ℂ) ^ (24 * n ^ 2 - 4 * n)

structure V13LiteralS0AssemblyData (q n : ℕ) where
  data : V.V13LiteralAndreiefData q n
  /-- The concrete determinant product after the `D_x,D_{xv},D_z,D_{zv}`
      evaluations, including the fixed q-power. -/
  hKernel : ∀ (x : Fin (4 * n) → ℝ) (v : Fin (5 * n) → ℝ)
      (p : Fin (4 * n) → Fin 4 × ℝ),
    (∀ i, x i ∈ Set.Icc (0 : ℝ) 1) →
    (∀ i, v i ∈ Set.Icc (0 : ℝ) 1) →
    (∏ i : Fin (4 * n), V.Literal.vContourWeight q (p i)) *
        V.Literal.vContourPhi q n x v
          (fun i => V.Literal.vContourPoint q (p i).1 (p i).2) =
      (vContourQScale q n)⁻¹ *
        (V.andreiefProduct (data.M2 v) (data.a2 v) (data.b2 v) x *
          V.andreiefProduct (data.M1 v) (data.a1 v) (data.b1 v) p)
  /-- The x/v/contour row construction has the same determinant as the
      outer signed moment matrix.  This is the remaining finite row-alignment
      theorem supplied by the concrete construction. -/
  hM0 : data.M0.det =
    Complex.ofReal ((V.vOuterMomentMatrix q n).det)
  hSwap : Integrable
      (fun y : (Fin (4 * n) → ℝ) × (Fin (5 * n) → ℝ) =>
        V.andreiefProduct (data.M2 y.2) (data.a2 y.2) (data.b2 y.2) y.1 *
          ∫ p : Fin (4 * n) → Fin 4 × ℝ,
            V.andreiefProduct (data.M1 y.2) (data.a1 y.2) (data.b1 y.2) p
              ∂(Measure.pi fun _ : Fin (4 * n) =>
                V.Literal.vContourParameterMeasure))
        ((Measure.pi fun _ : Fin (4 * n) =>
          V.Literal.vContourUnitIntervalMeasure).prod
          (Measure.pi fun _ : Fin (5 * n) =>
          V.Literal.vContourUnitIntervalMeasure))

/-! The literal kernel factorization is needed only on the supports of the
unit-interval product measures.  This version keeps that support condition
explicit and discharges it with the product-measure AE API. -/
theorem vContourTripleIntegral_eq_const_mul_canonicalS1Andreief_restrict
    {q n : ℕ} (D : V.V13LiteralAndreiefData q n) (c : ℂ)
    (hKernel : ∀ (x : Fin (4 * n) → ℝ) (v : Fin (5 * n) → ℝ)
      (p : Fin (4 * n) → Fin 4 × ℝ),
      (∀ i, x i ∈ Set.Icc (0 : ℝ) 1) →
      (∀ i, v i ∈ Set.Icc (0 : ℝ) 1) →
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
    V.Literal.vContourTripleIntegral q n = c * V.v13S1AndreiefIntegral D := by
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
  have hX : (Set.univ.pi (fun _ : Fin (4 * n) => (Set.univ : Set ℝ))) ≤ᵐ[μx]
      Set.univ.pi (fun _ : Fin (4 * n) => Set.Icc (0 : ℝ) 1) := by
    apply Measure.ae_le_set_pi
    intro i hi
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Icc] with t ht
    intro _
    exact ht
  have hV : (Set.univ.pi (fun _ : Fin (5 * n) => (Set.univ : Set ℝ))) ≤ᵐ[μv]
      Set.univ.pi (fun _ : Fin (5 * n) => Set.Icc (0 : ℝ) 1) := by
    apply Measure.ae_le_set_pi
    intro i hi
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Icc] with t ht
    intro _
    exact ht
  calc
    V.Literal.vContourTripleIntegral q n =
        ∫ x, ∫ v, ∫ p, c * (A x v * B v p) ∂μz ∂μv ∂μx := by
      unfold V.Literal.vContourTripleIntegral
      apply integral_congr_ae
      filter_upwards [hX] with x hx
      apply integral_congr_ae
      filter_upwards [hV] with v hv
      apply integral_congr_ae
      filter_upwards [] with p
      apply hKernel x v p
      · intro i
        exact (Set.mem_pi.mp (hx (by simp))) i (by simp)
      · intro i
        exact (Set.mem_pi.mp (hv (by simp))) i (by simp)
    _ = c * (∫ x, ∫ v, ∫ p, A x v * B v p ∂μz ∂μv ∂μx) := by
      simp_rw [integral_const_mul]
    _ = c * (∫ v, (∫ x, A x v ∂μx) * (∫ p, B v p ∂μz) ∂μv) := by
      rw [iterated_integral_mul_factorization μx μv μz A B hSwap']
    _ = c * V.v13S1AndreiefIntegral D := by
      simp [V.v13S1AndreiefIntegral, A, B, μx, μv, μz]

theorem vContourTripleIntegral_eq_qscale_inv_mul_s1
    {q n : ℕ} (D : V13LiteralS0AssemblyData q n) :
    V.Literal.vContourTripleIntegral q n =
      (vContourQScale q n)⁻¹ * V.v13S1AndreiefIntegral D.data := by
  exact vContourTripleIntegral_eq_const_mul_canonicalS1Andreief_restrict
    D.data (vContourQScale q n)⁻¹ D.hKernel D.hSwap

/-! The q-power introduced by the literal kernel factorization cancels the
    inverse scale in the triple integral. This is the algebraic H5 bridge;
    the construction-bound hypotheses remain packaged in `D`. -/
theorem vContourQScale_mul_tripleIntegral_eq_factorial_det
    {q n : ℕ} (hq : 2 ≤ q) (D : V13LiteralS0AssemblyData q n) :
    vContourQScale q n * V.Literal.vContourTripleIntegral q n =
      (((4 * n).factorial : ℂ) ^ 2 * ((5 * n).factorial : ℂ)) *
        Complex.ofReal ((V.vOuterMomentMatrix q n).det) := by
  have hqpos : 0 < q := by omega
  have hqscale : vContourQScale q n ≠ 0 := by
    unfold vContourQScale
    exact pow_ne_zero _ (by exact_mod_cast (Nat.ne_of_gt hqpos))
  rw [vContourTripleIntegral_eq_qscale_inv_mul_s1 D]
  rw [V.v13S1AndreiefIntegral_eq_factorial_det]
  rw [D.hM0]
  field_simp [hqscale]

theorem vContourActualGValue_eq_prefactor_mul_triple_of_assembly
    {q n : ℕ} (hq : 2 ≤ q) (D : V13LiteralS0AssemblyData q n) :
    vContourActualGValue q n =
      V.Literal.vContourPrefactor q n *
        V.Literal.vContourTripleIntegral q n := by
  have hqpos : 0 < q := by omega
  have hqpow : vContourQScale q n ≠ 0 := by
    unfold vContourQScale
    exact pow_ne_zero _ (by exact_mod_cast (Nat.ne_of_gt hqpos))
  have hfac :
      (((Nat.factorial (4 * n) : ℕ) : ℂ) ^ 2 *
        ((Nat.factorial (5 * n) : ℕ) : ℂ)) ≠ 0 := by
    exact mul_ne_zero
      (pow_ne_zero _ (by exact_mod_cast Nat.factorial_ne_zero (4 * n)))
      (by exact_mod_cast Nat.factorial_ne_zero (5 * n))
  have htriple := vContourTripleIntegral_eq_qscale_inv_mul_s1 D
  rw [V.v13S1AndreiefIntegral_eq_factorial_det] at htriple
  have hactual : vContourActualGValue q n = D.data.M0.det := by
    calc
      vContourActualGValue q n = V.Literal.vContourGValue q n :=
        vContourActualGValue_eq_literal q n
      _ = Complex.ofReal ((V.vOuterMomentMatrix q n).det) :=
        (V.vOuterMomentMatrix_det_eq_vContourGValue q n hq).symm
      _ = D.data.M0.det := D.hM0.symm
  rw [hactual, htriple]
  unfold V.Literal.vContourPrefactor
  unfold vContourQScale at hqpow ⊢
  have hfac' :
      (((Nat.factorial (n * 4) : ℕ) : ℂ) *
        ((Nat.factorial (n * 5) : ℕ) : ℂ)) ≠ 0 := by
    exact mul_ne_zero
      (by exact_mod_cast Nat.factorial_ne_zero (n * 4))
      (by exact_mod_cast Nat.factorial_ne_zero (n * 5))
  have hfacExact :
      (((Nat.factorial (4 * n) : ℕ) : ℂ) *
        ((Nat.factorial (5 * n) : ℕ) : ℂ)) ≠ 0 := by
    exact mul_ne_zero
      (by exact_mod_cast Nat.factorial_ne_zero (4 * n))
      (by exact_mod_cast Nat.factorial_ne_zero (5 * n))
  field_simp [hqpow, hfac, hfac', hfacExact]
  symm
  calc
    D.data.M0.det * ↑(4 * n).factorial * ↑(5 * n).factorial /
          (↑(4 * n).factorial * ↑(5 * n).factorial) =
        D.data.M0.det *
          ((↑(4 * n).factorial * ↑(5 * n).factorial) /
            (↑(4 * n).factorial * ↑(5 * n).factorial)) := by ring
    _ = D.data.M0.det := by rw [div_self hfacExact]; ring

/-!
hcore is exactly the C5--C7 unnormalised triple-integral estimate in
v-analytic.tex:522-601.  The C1--C4 algebra and C6 smoothing hypotheses
are upstream inputs used to establish this estimate for the concrete
reference measure; keeping it explicit prevents the assembly theorem from
silently assuming a measure identity that is not yet proved.
-/
theorem s0T_of_reference_facts
    {q : ℕ} (hq : SignedVBaseRange q)
    (P : VReferencePackage q hq)
    (Tq : ℝ) (hTq : 0 < Tq)
    (hcore : ∀ n : ℕ, 64 ≤ 4 * n →
      V.Literal.vContourTripleIntegral q n ≠ 0 →
      Real.log ‖V.Literal.vContourTripleIntegral q n‖ ≤
        -(((vQlow q : ℚ) : ℝ) - (3 / 2 : ℝ) * Real.log (q : ℝ) -
          (vKx q : ℝ) - (5 / 4 : ℝ) * (vKv q : ℝ) - (vKz q : ℝ)) *
          ((4 * n : ℕ) : ℝ) ^ 2 +
        (13 / 2 : ℝ) * ((4 * n : ℕ) : ℝ) *
          Real.log ((4 * n : ℕ) : ℝ) +
        3 * sigmaBudget P.Ax P.Av P.Az *
          (1 + Real.log (((4 * n : ℕ) : ℝ) ^ 2 / 3)) +
        (2 * denominatorTransferCost q + 7 + 130) +
          ((4 * n : ℕ) : ℝ) - Real.log (s0TransferPrefactor q n)) :
    ∀ n : ℕ, V.Literal.vContourTripleIntegral q n ≠ 0 →
      64 ≤ 4 * n →
      Real.log |v13PhiMaxValue q Tq n| ≤
        s0TransferPhiBudget q (vAlpha q) (vSigma q)
          Tq (v13PhiMaxValue q Tq n) n := by
  intro n hI hn
  apply s0T_budget_of_reference_facts P n Tq hTq hn hI
  intro _
  exact hcore n hn hI

end Li2Lean.B3

#print axioms Li2Lean.B3.s0T_of_reference_facts

