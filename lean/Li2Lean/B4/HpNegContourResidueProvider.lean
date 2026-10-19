/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.B4.NegativeContourProducer
import Li2Lean.B4.NegContourResidueProducer
import Li2Lean.B4.P1TailConsumerBridge

/-!
# Construction-bound provider for the exceptional negative contour

This module is the adapter between the P1 rectangle calculation and the
`HpNegContourProducerInput` consumed by the negative tail.  The kernel,
principal parts, and residue coefficients are the fixed v13 construction from
`hp-tail.tex:12-27,256-266`; no arbitrary sequence or contour function is
introduced here.

The fields in `HpTailRectangleDecompositionAssumptions` are exactly the
analytic obligations left by `NegContourResidueProducer`: boundary equality,
holomorphy and integrability of the entire remainder, rectangle geometry,
pole separation, principal-part integrability, and the four-edge
parameterization.  The explicit all-`n` M0 certificate and the residue-sum
identity are filled by this adapter.

The remaining boundary and coefficient-rate obligations are kept as named
fields when constructing `HpNegContourProducerInput`; this file does not
claim the v13 endpoint estimate.
-/

open Complex Set MeasureTheory intervalIntegral Topology
open scoped BigOperators

namespace Li2Lean.B4.NegContourResidueProducer

noncomputable section

open Li2Lean.B4
open Li2Lean.B4.Residues
open Li2Lean.B4.ResidueTailBridge
open Li2Lean.B4.ContourDecomposition
open Li2Lean.B4.RectanglePrincipalParts

/-! These are the non-algebraic fields of
`HpTailRectangleDecomposition`.  They are stated for the concrete v13
kernel, so an unrelated `B` sequence cannot satisfy the provider by type
accident.  The algebraic fields `explicit_residue` and `residue_sum` are
supplied below by `explicitResidueCertificate_all` and
`hpTailResidueSum_eq_branch`. -/
structure HpTailRectangleDecompositionAssumptions
    (q n : ℕ) (height : ℝ) : Prop where
  boundary_decomposition :
    Set.EqOn (hpTailKernelPlus q n)
      (hpTailEntireRemainder q n +
        principalParts (Finset.range (n + 1))
          (hpTailUPrime q n) (hpTailVPrime q n) hpTailNatPole)
      (RectangleBorder
        (Complex.ofReal (-1 / 2) - Complex.ofReal ((n : ℝ) * height) * Complex.I)
        (Complex.ofReal ((n : ℝ) + 1 / 2) +
          Complex.ofReal ((n : ℝ) * height) * Complex.I))
  entire_holomorphic :
    HolomorphicOn (hpTailEntireRemainder q n)
      (Complex.Rectangle
        (Complex.ofReal (-1 / 2) - Complex.ofReal ((n : ℝ) * height) * Complex.I)
        (Complex.ofReal ((n : ℝ) + 1 / 2) +
          Complex.ofReal ((n : ℝ) * height) * Complex.I))
  entire_border_integrable :
    RectangleBorderIntegrable (hpTailEntireRemainder q n)
      (Complex.ofReal (-1 / 2) - Complex.ofReal ((n : ℝ) * height) * Complex.I)
      (Complex.ofReal ((n : ℝ) + 1 / 2) +
        Complex.ofReal ((n : ℝ) * height) * Complex.I)
  real_corner_order :
    (Complex.ofReal (-1 / 2) - Complex.ofReal ((n : ℝ) * height) * Complex.I).re ≤
      (Complex.ofReal ((n : ℝ) + 1 / 2) +
        Complex.ofReal ((n : ℝ) * height) * Complex.I).re
  imag_corner_order :
    (Complex.ofReal (-1 / 2) - Complex.ofReal ((n : ℝ) * height) * Complex.I).im ≤
      (Complex.ofReal ((n : ℝ) + 1 / 2) +
        Complex.ofReal ((n : ℝ) * height) * Complex.I).im
  pole_interior : ∀ j, j ∈ Finset.range (n + 1) →
    Complex.Rectangle
      (Complex.ofReal (-1 / 2) - Complex.ofReal ((n : ℝ) * height) * Complex.I)
      (Complex.ofReal ((n : ℝ) + 1 / 2) +
        Complex.ofReal ((n : ℝ) * height) * Complex.I) ∈ 𝓝 (hpTailNatPole j)
  corner_avoidance : ∀ j, j ∈ Finset.range (n + 1) →
    ((Complex.ofReal (-1 / 2) - Complex.ofReal ((n : ℝ) * height) * Complex.I).re ≠
        (hpTailNatPole j).re) ∧
      ((Complex.ofReal ((n : ℝ) + 1 / 2) +
          Complex.ofReal ((n : ℝ) * height) * Complex.I).re ≠
        (hpTailNatPole j).re) ∧
      ((Complex.ofReal (-1 / 2) - Complex.ofReal ((n : ℝ) * height) * Complex.I).im ≠
        (hpTailNatPole j).im) ∧
      ((Complex.ofReal ((n : ℝ) + 1 / 2) +
          Complex.ofReal ((n : ℝ) * height) * Complex.I).im ≠
        (hpTailNatPole j).im)
  double_border_integrable : ∀ j, j ∈ Finset.range (n + 1) →
    RectangleBorderIntegrable
      (doublePart (hpTailUPrime q n) hpTailNatPole j)
      (Complex.ofReal (-1 / 2) - Complex.ofReal ((n : ℝ) * height) * Complex.I)
      (Complex.ofReal ((n : ℝ) + 1 / 2) +
        Complex.ofReal ((n : ℝ) * height) * Complex.I)
  simple_border_integrable : ∀ j, j ∈ Finset.range (n + 1) →
    RectangleBorderIntegrable
      (simplePart (hpTailVPrime q n) hpTailNatPole j)
      (Complex.ofReal (-1 / 2) - Complex.ofReal ((n : ℝ) * height) * Complex.I)
      (Complex.ofReal ((n : ℝ) + 1 / 2) +
        Complex.ofReal ((n : ℝ) * height) * Complex.I)
  edge_parameterization :
    hpTailRectIntegral (-1 / 2) ((n : ℝ) + 1 / 2)
        (-((n : ℝ) * height)) ((n : ℝ) * height)
        (hpTailKernelPlus q n) =
      RectangleIntegral (hpTailKernelPlus q n)
        (Complex.ofReal (-1 / 2) - Complex.ofReal ((n : ℝ) * height) * Complex.I)
        (Complex.ofReal ((n : ℝ) + 1 / 2) +
          Complex.ofReal ((n : ℝ) * height) * Complex.I)

/-- Fill the two construction-specific fields omitted from the assumption
record.  `explicitResidueCertificate_all` is the all-`n` M0 certificate
(`hp-tail.tex:12-23`), while the residue sum is the concrete
`B_n+lambda C_n` identity (`hp-tail.tex:256-266`). -/
theorem HpTailRectangleDecompositionAssumptions.toDecomposition
    {q n : ℕ} {height : ℝ}
    (hq : 0 < q)
    (h : HpTailRectangleDecompositionAssumptions q n height) :
    HpTailRectangleDecomposition q n height :=
  { explicit_residue := explicitResidueCertificate_all n
    boundary_decomposition := h.boundary_decomposition
    entire_holomorphic := h.entire_holomorphic
    entire_border_integrable := h.entire_border_integrable
    real_corner_order := h.real_corner_order
    imag_corner_order := h.imag_corner_order
    pole_interior := h.pole_interior
    corner_avoidance := h.corner_avoidance
    double_border_integrable := h.double_border_integrable
    simple_border_integrable := h.simple_border_integrable
    residue_sum := hpTailResidueSum_eq_branch q n hq
    edge_parameterization := h.edge_parameterization }

/-! The provider is restricted to the three exceptional v13 bases.  This
restriction supplies positivity for the exponential residue identity and
prevents the adapter from becoming a generic arbitrary-base interface. -/
structure HpNegContourResidueProvider (q : ℕ) : Prop where
  q_spec : q = 8 ∨ q = 9 ∨ q = 10
  decomposition : ∀ n : ℕ, 0 < n →
    HpTailRectangleDecompositionAssumptions q n (1 / 5 : ℝ)

theorem HpNegContourResidueProvider.q_pos
    {q : ℕ} (h : HpNegContourResidueProvider q) : 0 < q := by
  rcases h.q_spec with rfl | rfl | rfl <;> norm_num

/-- The P1 residue field required by `HpNegContourProducerInput`, obtained
from the explicit rectangle decomposition assumptions. -/
theorem HpNegContourResidueProvider.residue
    {q : ℕ} (h : HpNegContourResidueProvider q) :
    ∀ n : ℕ, 0 < n →
      HpTailResidueRectangleCertificate q n (1 / 5 : ℝ) := by
  intro n hn
  exact hpTailResidueRectangleCertificate_of q n (1 / 5 : ℝ)
    (by
      rcases h.q_spec with rfl | rfl | rfl <;> norm_num)
    hn (by norm_num)
    ((h.decomposition n hn).toDecomposition h.q_pos)

/-! The P1 consumer bridge sees the same typed residue producer.  This
projection is useful to later tail consumers and records the exceptional-base
membership separately from the decomposition assumptions. -/
theorem HpNegContourResidueProvider.p1_consumer
    {q : ℕ} (h : HpNegContourResidueProvider q) :
    HpTailP1ConsumerInput q :=
  { q_mem := by
      rw [Li2Lean.B4.NegativeContour.mem_negativeContourBases_iff]
      exact h.q_spec
    p1 := h.residue }

/-! The final producer constructor leaves exactly the two independent
analytic obligations: the four-side boundary bound and the coefficient rate
bound.  The residue field is now fully supplied by the P1 provider above. -/
theorem hpNegContourProducerInput_of_provider
    {q : ℕ} (h : HpNegContourResidueProvider q)
    (boundary : Li2Lean.B4.NegContour.HpNegBorderBound q)
    (branch_bound : ∀ n : ℕ, 30 ≤ n →
      ‖hpTailBranchValuePlus q n‖ ≤
        (1 / (2 * Real.pi)) * (3 * ((n + 1 : ℕ) : ℝ)) *
          (Real.exp 18 * ((n + 1 : ℕ) : ℝ) ^ 18 * (29 : ℝ) ^ n)) :
    Li2Lean.B4.NegativeContour.HpNegContourProducerInput q :=
  { q_spec := h.q_spec
    residue := h.residue
    boundary := boundary
    branch_bound := branch_bound }

end

end Li2Lean.B4.NegContourResidueProducer

#print axioms Li2Lean.B4.NegContourResidueProducer.HpTailRectangleDecompositionAssumptions.toDecomposition
#print axioms Li2Lean.B4.NegContourResidueProducer.HpNegContourResidueProvider.residue
#print axioms Li2Lean.B4.NegContourResidueProducer.HpNegContourResidueProvider.p1_consumer
#print axioms Li2Lean.B4.NegContourResidueProducer.hpNegContourProducerInput_of_provider
