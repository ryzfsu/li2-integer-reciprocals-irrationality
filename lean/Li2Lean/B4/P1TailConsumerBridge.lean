/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.B4.ContourPNT
import Li2Lean.B4.HPContourResidueBridge
import Li2Lean.B4.NegativeContourProducerBridge
import Li2Lean.B4.ResidueCertificateAllN_M0c
import Li2Lean.B4.ResidueTailConsumers

/-!
# Construction-bound P1/tail consumer bridge

This module only packages the already typed P1 input for the concrete
Hermite--Pade kernel. The P1 certificate is
HpTailResidueRectangleCertificate, whose residue value is
hpTailBranchValuePlus; no arbitrary BSequence or contour function is
introduced here. The all-n certificate and both tail identities are the
unconditional aliases from ResidueCertificateAllN_M0c.

Paper alignment:

* hp-tail.tex:20-27: the explicit double/simple-pole coefficients;
* hp-tail.tex:34-41: hpartial and the A_n/B_n/C_n tail coefficient;
* hp-tail.tex:256-266: the concrete exponential P1 residue value.

The rectangle estimate itself remains a producer obligation. In particular,
this file does not prove the exceptional q = 8, 9, 10 boundary estimates.
-/

open Finset Polynomial

namespace Li2Lean.B4

noncomputable section

open ResidueTailBridge Residues
open NegativeContour

/-! The P1 input is fixed to the actual branch kernel and rectangle
certificate. The q membership is retained so later consumers cannot
accidentally use an unrelated denominator. -/
structure HpTailP1ConsumerInput (q : ℕ) : Prop where
  q_mem : q ∈ negativeContourBases
  p1 : ∀ n : ℕ, 0 < n ->
    HpTailResidueRectangleCertificate q n (1 / 5 : ℝ)

theorem HpTailP1ConsumerInput.p1_certificate
    {q : ℕ} (h : HpTailP1ConsumerInput q) (n : ℕ) (hn : 0 < n) :
    HpTailResidueRectangleCertificate q n (1 / 5 : ℝ) :=
  h.p1 n hn

/-! M0 is unconditional for the concrete numerator and residue summands. -/
theorem HpTailP1ConsumerInput.explicit_residue
    {q : ℕ} (_h : HpTailP1ConsumerInput q) (n : ℕ) :
    ExplicitResidueCertificate n :=
  explicitResidueCertificate_all n

/-! v13 hpartial and the high-tail coefficient identity, now available
without a conclusion-shaped certificate field. -/
theorem HpTailP1ConsumerInput.hpartial
    {q : ℕ} (_h : HpTailP1ConsumerInput q) (n : ℕ) :
    ∀ k, n < k -> hpResidueConvolution n k = hpPhiValue n k :=
  hpartial_for_residueTailAlgebra_all n

theorem HpTailP1ConsumerInput.tail_coeff
    {q : ℕ} (_h : HpTailP1ConsumerInput q) (n : ℕ) :
    ∀ k, 3 * n + 2 ≤ k -> hpThreeFormCoeff n k = hpPhiValue n k :=
  hpTailCoeff_all n

/-! The finite residue sum is exactly the concrete B_n + lambda C_n
combination used by the P1 branch. -/
theorem hpTailBranchValuePlus_eq_contourResidueSum
    (q n : ℕ) :
    hpTailBranchValuePlus q n =
      hpContourResidueSum n (-((1 : ℚ) / (q : ℚ)))
        (-((Real.log (q : ℝ)) : ℂ) + (Real.pi : ℂ) * Complex.I) := by
  rw [hpContourResidueSum_eq_forms]
  unfold hpTailBranchValuePlus
  have hB :
      Polynomial.eval₂ (algebraMap ℚ ℂ)
          ((-((1 : ℚ) / (q : ℚ))) : ℂ) (hpBpoly n) =
        ((Polynomial.eval (-((1 : ℚ) / (q : ℚ))) (hpBpoly n) : ℚ) : ℂ) := by
    convert (Polynomial.eval₂_at_apply (p := hpBpoly n)
      (algebraMap ℚ ℂ) (-((1 : ℚ) / (q : ℚ)))) using 1 <;> norm_num
  have hC :
      Polynomial.eval₂ (algebraMap ℚ ℂ)
          ((-((1 : ℚ) / (q : ℚ))) : ℂ) (hpCpoly n) =
        ((Polynomial.eval (-((1 : ℚ) / (q : ℚ))) (hpCpoly n) : ℚ) : ℂ) := by
    convert (Polynomial.eval₂_at_apply (p := hpCpoly n)
      (algebraMap ℚ ℂ) (-((1 : ℚ) / (q : ℚ)))) using 1 <;> norm_num
  rw [hB, hC]
  ring

/-! A P1 input carries both the typed residue certificate and the concrete
algebraic tail consumers. This is a projection theorem only; it does not
assert any analytic boundary estimate. -/
theorem HpTailP1ConsumerInput.p1_and_tail
    {q : ℕ} (h : HpTailP1ConsumerInput q) (n : ℕ) (hn : 0 < n) :
    HpTailResidueRectangleCertificate q n (1 / 5 : ℝ) ∧
      ExplicitResidueCertificate n ∧
      (∀ k, 3 * n + 2 ≤ k ->
        hpThreeFormCoeff n k = hpPhiValue n k) := by
  exact ⟨h.p1_certificate n hn, h.explicit_residue n, h.tail_coeff n⟩

end

end Li2Lean.B4

#print axioms Li2Lean.B4.HpTailP1ConsumerInput.p1_certificate
#print axioms Li2Lean.B4.HpTailP1ConsumerInput.explicit_residue
#print axioms Li2Lean.B4.HpTailP1ConsumerInput.hpartial
#print axioms Li2Lean.B4.HpTailP1ConsumerInput.tail_coeff
#print axioms Li2Lean.B4.hpTailBranchValuePlus_eq_contourResidueSum
#print axioms Li2Lean.B4.HpTailP1ConsumerInput.p1_and_tail
