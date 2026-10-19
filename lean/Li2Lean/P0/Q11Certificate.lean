/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.Q11EndpointArithmetic

namespace Li2Lean.P0.Q11Data

/-!
Integer/Boolean certificate layer for the q = 11 endpoint data.

Source locks (paper v13):
* `chapters/p0-reference-data.tex:29-40` gives the denominator, edge lists,
  masses, and the eight independent contour pair masses.
* `chapters/p0-analytic.tex:749-765` gives the q = 11 alpha and frequency
  thresholds; `:804-826` gives the directed scalar penalties.
* `chapters/p0-analytic.tex:850-855` gives the q = 11 tangent and gap.
* `chapters/p0-arithmetic.tex:705-716` gives the fixed-base rate context.
* `chapters/certificate-algorithm.tex:29-42` specifies exact parsing,
  reflection, mass checks, and the directed certificate obligations.

This module certifies only finite integer inputs and printed scalar
comparisons. It does not claim the continuum contour, positive-part, or
omitted-tail estimates; those remain separate obligations. Boolean checks
avoid deciding expressions containing Rat multiplication.
-/

def ratioLtBool (x y : IntRatio) : Bool :=
  x.num * (y.den : ℤ) < y.num * (x.den : ℤ)

def ratioLeBool (x y : IntRatio) : Bool :=
  x.num * (y.den : ℤ) ≤ y.num * (x.den : ℤ)

def ratioEqBool (x y : IntRatio) : Bool :=
  x.num * (y.den : ℤ) == y.num * (x.den : ℤ)

def q11MassCertificate : Bool :=
  (denominator == 3000000000000) &&
  (pinnedEdge32Units == [8, 12, 16, 20, 24, 28, 32, 36, 40]) &&
  (pinnedMassUnits ==
    [28, 0, 107702656325, 206939134529, 260854191850,
     321658806124, 374999999996, 374999999996]) &&
  (frequencyEdge2Units == [1, 3, 5, 7, 9]) &&
  (frequencyMassUnits == [2334546252656, 652078675810, 13375071534, 0]) &&
  (contourPairMassUnits ==
    [105521636098, 103136532801, 98660112985, 92490547592,
     84344850292, 75717735060, 60802883424, 55748307324]) &&
  (pinnedMassUnits.length == 8) &&
  (frequencyMassUnits.length == 4) &&
  (contourPairMassUnits.length == 8) &&
  (frequencyMassUnits.sum == denominator) &&
  (pinnedMassUnits.sum + 2 * contourPairMassUnits.sum == denominator)

theorem q11MassCertificate_true : q11MassCertificate = true := by
  decide +kernel

def q11SymmetryCertificate : Bool :=
  (contourNodeCount == 64) &&
  (contourFejerDegree == 48) &&
  ((List.ofFn fun j : Fin contourNodeCount =>
      contourMassUnit j.val == contourMassUnit (contourNodeCount - 1 - j.val)).all id)

theorem q11SymmetryCertificate_true : q11SymmetryCertificate = true := by
  decide +kernel

def q11ScalarCertificate : Bool :=
  ratioEqBool alphaLower ⟨77597, 100000⟩ &&
  ratioEqBool frequencyFloor ⟨1217, 200⟩ &&
  ratioEqBool etaFloor ⟨-3359, 500⟩ &&
  ratioEqBool qLogLower ⟨-635537, 1000000⟩ &&
  ratioEqBool endpointTangentUpper ⟨772577360778, 1000000000000⟩ &&
  ratioLtBool endpointTangentUpper alphaLower &&
  ratioLeBool pinnedPenaltyUpper ⟨1, 1000000⟩ &&
  ratioLeBool frequencyPenaltyUpper ⟨107, 100⟩ &&
  ratioLeBool arithmeticConstantUpper ⟨2543, 1000⟩

theorem q11ScalarCertificate_true : q11ScalarCertificate = true := by
  norm_num [q11ScalarCertificate, ratioEqBool, ratioLtBool, ratioLeBool,
    alphaLower, frequencyFloor, etaFloor, qLogLower, endpointTangentUpper,
    pinnedPenaltyUpper, frequencyPenaltyUpper, arithmeticConstantUpper]

structure Q11FiniteInputCertificate : Prop where
  mass : q11MassCertificate = true
  symmetry : q11SymmetryCertificate = true
  scalar : q11ScalarCertificate = true
  endpoint_gap : (3 : ℝ) / 1000 <
    ratioToReal alphaLower - ratioToReal endpointTangentUpper

theorem q11FiniteInputCertificate : Q11FiniteInputCertificate where
  mass := q11MassCertificate_true
  symmetry := q11SymmetryCertificate_true
  scalar := q11ScalarCertificate_true
  endpoint_gap := q11_endpoint_alpha_minus_tangent_gt_three_per_thousand

end Li2Lean.P0.Q11Data
