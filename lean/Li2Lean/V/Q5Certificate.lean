/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Mathlib
import Li2Lean.Statement
import Li2Lean.Kit.EndpointCriterion
import Li2Lean.V.Q5ReferenceRows

set_option autoImplicit false
set_option maxRecDepth 100000

/-!
  q = 5 certificate interfaces for the signed V construction.

  The construction is the one in the Li2(1/n) paper v13.  In particular,
  the row ranges and the three signed determinant blocks come from
  `v-arithmetic.tex:13-35`, the signed energy and field formulas from
  `v-analytic.tex:1-48`, and the seed data from `nonvanishing.tex:148-198`.
  This file deliberately stores the q=5 headers and finite certificate
  interfaces without claiming that the large decimal row tables have been
  kernel-checked.  Such a claim belongs only after the row data and its
  Boolean receipts have been imported and checked by Lean.
-/

namespace Li2Lean.V.Q5Certificate

open scoped BigOperators

/-! ## Fixed base and reference-data headers

The q=5 rows are printed in `v-reference-data.tex:224-292`: x at lines
224-235, y at 236-249, z at 250-267, and the Poisson prefix at 268-292.
The introductory encoding convention is `v-reference-data.tex:1-11`.
-/

def q5 : Nat := 5

def q5Base : Int := -5

theorem q5_base_eq_neg_five : q5Base = (-5 : Int) := by
  norm_num [q5Base]

theorem q5_base_is_neg_q : q5Base = -(q5 : Int) := by
  norm_num [q5Base, q5]

structure VChainHeader where
  q : Nat
  rows : Nat
  endpointUnits : Int
  correctionIndex : Nat
  correctionUnits : Int

structure VPoissonHeader where
  q : Nat
  rows : Nat
  prefixRows : Nat

def q5XHeader : VChainHeader :=
  { q := 5
    rows := 39
    endpointUnits := 3349364905389
    correctionIndex := 1
    correctionUnits := 94611 }

def q5YHeader : VChainHeader :=
  { q := 5
    rows := 48
    endpointUnits := 480367989919
    correctionIndex := 1
    correctionUnits := 10081 }

def q5ZHeader : VChainHeader :=
  { q := 5
    rows := 62
    endpointUnits := -250000000000000
    correctionIndex := 0
    correctionUnits := 0 }

def q5PoissonHeader : VPoissonHeader :=
  { q := 5
    rows := 137
    prefixRows := 69 }

theorem q5_headers_have_base :
    q5XHeader.q = q5 ∧ q5YHeader.q = q5 ∧ q5ZHeader.q = q5 ∧
      q5PoissonHeader.q = q5 := by
  simp [q5XHeader, q5YHeader, q5ZHeader, q5PoissonHeader, q5]

def q5ReferenceRowsExpected : Nat :=
  q5XHeader.rows + q5YHeader.rows + q5ZHeader.rows + q5PoissonHeader.rows

theorem q5_reference_rows_expected : q5ReferenceRowsExpected = 286 := by
  norm_num [q5ReferenceRowsExpected, q5XHeader, q5YHeader, q5ZHeader,
    q5PoissonHeader]

theorem q5_reference_rows_match_raw_data :
    Li2Lean.V.Q5ReferenceRows.q5XReferenceIncrements.length +
        Li2Lean.V.Q5ReferenceRows.q5YReferenceIncrements.length +
        Li2Lean.V.Q5ReferenceRows.q5ZReferenceIncrements.length +
        (2 * Li2Lean.V.Q5ReferenceRows.q5PoissonPrefixIncrements.length - 1) =
      q5ReferenceRowsExpected := by
  rw [Li2Lean.V.Q5ReferenceRows.q5_reference_rows_total,
    q5_reference_rows_expected]

def q5RealScale : Nat := 100000000

def q5CorrectionDenominator : Nat := 50000000000000

theorem q5_correction_denominator_value : q5CorrectionDenominator = 5 * 10 ^ 13 := by
  norm_num [q5CorrectionDenominator]

/-!
`q5_reference_rows_expected` checks only the header arithmetic.  It does not
assert that the 286 source rows are present or that their decimal receipts
are sound; those are separate Lean obligations for the imported table.
-/

structure Q5ReferenceHeaderReceipt where
  x : VChainHeader
  y : VChainHeader
  z : VChainHeader
  poisson : VPoissonHeader
  x_is_source_header : x = q5XHeader
  y_is_source_header : y = q5YHeader
  z_is_source_header : z = q5ZHeader
  poisson_is_source_header : poisson = q5PoissonHeader

def q5ReferenceHeaderReceipt : Q5ReferenceHeaderReceipt :=
  { x := q5XHeader
    y := q5YHeader
    z := q5ZHeader
    poisson := q5PoissonHeader
    x_is_source_header := rfl
    y_is_source_header := rfl
    z_is_source_header := rfl
    poisson_is_source_header := rfl }

/-! ## q=5 directed numerical bounds

The field thresholds, energy endpoint, and margin are the q=5 rows of
`v-analytic.tex:337-394`; endpoint and transfer constants are its
`v-analytic.tex:410-491`.  The arithmetic rate is the q=5 row in
`v-arithmetic.tex:389-407`.
-/

def q5EnergyLower : ℚ := (-4684191 : ℚ) / 1000000

def q5Kx : ℚ := (-5670 : ℚ) / 1000

def q5Kv : ℚ := (-4791 : ℚ) / 1000

def q5Kz : ℚ := 1108002 / 1000000

def q5AlphaLower : ℚ := 345240 / 100000

def q5TauUpper : ℚ := 330591 / 100000

def q5MarginLower : ℚ := 14649 / 100000

def q5EndpointEx : ℚ := (-73835 : ℚ) / 10000

def q5EndpointEv : ℚ := (-48208 : ℚ) / 10000

def q5SigmaUpper : ℚ := 12351983 / 1000

def q5TransferCoefficient : ℚ := 10 + 3 * q5SigmaUpper

def q5PathLengthUpper : ℚ := 6917916 / 1000000

theorem q5_alpha_tau_margin : q5AlphaLower - q5TauUpper = q5MarginLower := by
  norm_num [q5AlphaLower, q5TauUpper, q5MarginLower]

theorem q5_alpha_gt_tau : q5TauUpper < q5AlphaLower := by
  norm_num [q5AlphaLower, q5TauUpper]

theorem q5_transfer_coefficient_value : q5TransferCoefficient = 37065949 / 1000 := by
  norm_num [q5TransferCoefficient, q5SigmaUpper]

theorem q5_endpoint_fields_below_threshold :
    q5EndpointEx < q5Kx ∧ q5EndpointEv < q5Kv := by
  norm_num [q5EndpointEx, q5EndpointEv, q5Kx, q5Kv]

structure Q5DirectedBounds where
  energyLower : ℚ
  fieldXUpper : ℚ
  fieldVUpper : ℚ
  fieldZUpper : ℚ
  alphaLower : ℚ
  tauUpper : ℚ
  marginLower : ℚ
  transferCoefficient : ℚ
  pathLengthUpper : ℚ

def q5DirectedBounds : Q5DirectedBounds :=
  { energyLower := q5EnergyLower
    fieldXUpper := q5Kx
    fieldVUpper := q5Kv
    fieldZUpper := q5Kz
    alphaLower := q5AlphaLower
    tauUpper := q5TauUpper
    marginLower := q5MarginLower
    transferCoefficient := q5TransferCoefficient
    pathLengthUpper := q5PathLengthUpper }

theorem q5_directed_bounds_margin :
    q5DirectedBounds.tauUpper < q5DirectedBounds.alphaLower := by
  exact q5_alpha_gt_tau

/-!
The following proposition is the analytic input consumed by a later q=5
endpoint assembly.  It is intentionally conditional: the decimal rows and
their energy/field soundness must be proved by the directed checker first.
The all-m smoothing quantifier and threshold `m = 4 n >= 64` are from
`v-analytic.tex:493-630`.
-/

def Q5AnalyticBound (G : Nat -> Real) : Prop :=
  ∀ n : Nat, 64 ≤ 4 * n ->
    |G (4 * n)| ≤
      Real.exp
        (-((q5AlphaLower : Real)) * (4 * n : Real) ^ 2 +
          ((q5TransferCoefficient : Real)) * (4 * n : Real) *
            Real.log (4 * n : Real))

structure Q5AnalyticInput where
  determinantAbs : Nat -> Real
  smoothingBound : Q5AnalyticBound determinantAbs

/-! ## Signed residue blocks

The integer inequalities below are the left-closed/right-open definitions of
`K`, `L`, and `W` in `v-arithmetic.tex:180-250`; they are equivalent to the
displayed x/rho inequalities when `m = 4 n`.  The only deliberately credited
rank-one saving is the profile stated in `v-arithmetic.tex:214-221`.
-/

def q5K (m p u : Nat) : Finset Nat :=
  (Finset.range (3 * m + 1)).filter (fun k =>
    m ≤ 2 * u + 2 * k * p ∧ 2 * u + 2 * k * p < 3 * m)

def q5L (m p u : Nat) : Finset Nat :=
  (Finset.range (3 * m + 1)).filter (fun k =>
    m ≤ 4 * u + 4 * k * p ∧ 4 * u + 4 * k * p < 10 * m)

def q5W (m p u : Nat) : Finset Nat :=
  (Finset.range (3 * m + 2)).filter (fun w =>
    0 < w ∧ u < w * p ∧ 4 * (w * p - u) ≤ m)

def q5RankSaving (m p u : Nat) : Nat :=
  if q5K m p u = ({0} : Finset Nat) ∧
      q5L m p u = ({0, 1} : Finset Nat) ∧
      q5W m p u = (∅ : Finset Nat) then 1 else 0

def q5RankProfile (m p u : Nat) : Int :=
  (min (2 * (q5K m p u).card + (q5W m p u).card) (q5L m p u).card : Int) -
    (q5RankSaving m p u : Int)

def q5ResidueExponent (m p : Nat) : Int :=
  m + ∑ u ∈ Finset.range p, q5RankProfile m p u

theorem q5_rank_saving_special
    {m p u : Nat}
    (hK : q5K m p u = ({0} : Finset Nat))
    (hL : q5L m p u = ({0, 1} : Finset Nat))
    (hW : q5W m p u = (∅ : Finset Nat)) :
    q5RankSaving m p u = 1 := by
  simp [q5RankSaving, hK, hL, hW]

theorem q5_rank_profile_special
    {m p u : Nat}
    (hK : q5K m p u = ({0} : Finset Nat))
    (hL : q5L m p u = ({0, 1} : Finset Nat))
    (hW : q5W m p u = (∅ : Finset Nat)) :
    q5RankProfile m p u = 1 := by
  simp [q5RankProfile, q5RankSaving, hK, hL, hW]

/-!
`Q5ResidueBlockBound` is the exact coefficientwise valuation conclusion of
the q=5 specialization.  Its hypotheses expose the p-unit condition
`p !| 5*6` and `p^2 > max(N,U)` from `v-arithmetic.tex:147-213`; no rank
claim is smuggled in as an axiom.
-/

def Q5ResidueBlockBound (valuation : Nat -> Nat -> Int) : Prop :=
  ∀ {n p : Nat},
    0 < n -> Nat.Prime p ->
      ¬ p ∣ q5 * (q5 + 1) ->
      max (10 * n - 1) (11 * n - 1) < p ^ 2 ->
      -q5ResidueExponent (4 * n) p ≤ valuation (4 * n) p

structure Q5ResidueBlockCertificate where
  valuation : Nat -> Nat -> Int
  bound : Q5ResidueBlockBound valuation

theorem q5_residue_bound_of_certificate
    (c : Q5ResidueBlockCertificate) : Q5ResidueBlockBound c.valuation :=
  c.bound

/-! ## Outer-pole assignment

The four branches below are the q=5 instance of the common signed outer
assignment in `v-arithmetic.tex:289-317`.  The q value affects only the fixed
exceptional-prime set; the p-unit pole locations and costs are unchanged.
-/

def q5U (n : Nat) : Nat := 11 * n - 1

def q5OuterLambdaB (n p i : Nat) : Nat :=
  if 5 * n < p ∧ p < 6 * n then
    1 + if p ≤ i then 1 else 0
  else if 6 * n ≤ p ∧ p < 8 * n then
    if i + p < 10 * n then 1 else 0
  else 0

def q5OuterLambdaV (n p ell : Nat) : Nat :=
  if 5 * n < p ∧ p < 10 * n then 1
  else if 10 * n ≤ p ∧ p ≤ q5U n then
    if n ≤ p - ell ∧ p - ell < 10 * n then 1 else 0
  else 0

def q5OuterChi (n p j : Nat) : Nat :=
  if 5 * n < p ∧ p < 6 * n then
    if p + 2 * n ≤ j then 1 else 0
  else if 6 * n ≤ p ∧ p < 10 * n then
    if p ≤ j then 1 else 0
  else 0

def q5OuterCost (n p : Nat) : Int :=
  if 5 * n < p ∧ p < 8 * n then
    19 * (n : Int) - 2 * (p : Int)
  else if 8 * n ≤ p ∧ p ≤ q5U n then
    11 * (n : Int) - (p : Int)
  else 0

theorem q5_outer_partition
    {n p : Nat} (hn : 0 < n) (hp : 5 * n < p) (hpU : p ≤ q5U n) :
    (5 * n < p ∧ p < 6 * n) ∨
      (6 * n ≤ p ∧ p < 8 * n) ∨
      (8 * n ≤ p ∧ p < 10 * n) ∨
      (10 * n ≤ p ∧ p ≤ q5U n) := by
  have hpU' : p < 11 * n := by
    dsimp [q5U] at hpU
    omega
  by_cases h6 : p < 6 * n
  · exact Or.inl ⟨hp, h6⟩
  by_cases h8 : p < 8 * n
  · exact Or.inr (Or.inl ⟨by omega, h8⟩)
  by_cases h10 : p < 10 * n
  · exact Or.inr (Or.inr (Or.inl ⟨by omega, h10⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨by omega, hpU⟩))

theorem q5_outer_cost_first_band
    {n p : Nat} (h5 : 5 * n < p) (h8 : p < 8 * n) :
    q5OuterCost n p = 19 * (n : Int) - 2 * (p : Int) := by
  have houter : 5 * n < p ∧ p < 8 * n := ⟨h5, h8⟩
  simp [q5OuterCost, houter]

theorem q5_outer_cost_second_band
    {n p : Nat} (h8 : 8 * n ≤ p) (hU : p ≤ q5U n) :
    q5OuterCost n p = 11 * (n : Int) - (p : Int) := by
  have houter : ¬ (5 * n < p ∧ p < 8 * n) := by omega
  simp [q5OuterCost, houter, h8, hU]

theorem q5_outer_cost_nonnegative
    {n p : Nat} (hn : 0 < n) (hp : 5 * n < p) (hpU : p ≤ q5U n) :
    0 ≤ q5OuterCost n p := by
  rcases q5_outer_partition hn hp hpU with h56 | h68 | h810 | h10U
  · rw [q5_outer_cost_first_band h56.1 (by omega)]
    omega
  · rw [q5_outer_cost_first_band (by omega) (by omega)]
    omega
  · rw [q5_outer_cost_second_band h810.1 (by omega)]
    omega
  · rw [q5_outer_cost_second_band (by omega) h10U.2]
    have hpLt : p < 11 * n := by
      dsimp [q5U] at h10U
      omega
    omega

def Q5OuterPoleBound (valuation : Nat -> Nat -> Int) : Prop :=
  ∀ {n p : Nat},
    0 < n -> 5 * n < p -> p ≤ q5U n ->
    -(q5OuterCost n p) ≤ valuation (4 * n) p

structure Q5OuterPoleCertificate where
  valuation : Nat -> Nat -> Int
  bound : Q5OuterPoleBound valuation

theorem q5_outer_bound_of_certificate
    (c : Q5OuterPoleCertificate) : Q5OuterPoleBound c.valuation :=
  c.bound

/-! ## p=11 seed constant

The q=5 row of the signed seed table is
`nonvanishing.tex:179-198`: p_5 = 11 and coefficient vector
(5,2,5,8,7), with constant residue 5.  This is only the seed constant
interface; Frobenius transport remains a separate proof obligation.
-/

def q5SeedPrime : Nat := 11

noncomputable def q5SeedPolynomial : Polynomial (ZMod 11) :=
  Polynomial.C (5 : ZMod 11) +
    Polynomial.C (2 : ZMod 11) * Polynomial.X +
    Polynomial.C (5 : ZMod 11) * Polynomial.X ^ 2 +
    Polynomial.C (8 : ZMod 11) * Polynomial.X ^ 3 +
    Polynomial.C (7 : ZMod 11) * Polynomial.X ^ 4

noncomputable def q5SeedConstant : ZMod 11 := q5SeedPolynomial.eval 0

theorem q5_seed_prime : Nat.Prime q5SeedPrime := by
  norm_num [q5SeedPrime]

theorem q5_seed_constant_residue : q5SeedConstant = (5 : ZMod 11) := by
  simp [q5SeedConstant, q5SeedPolynomial]

theorem q5_seed_constant_nonzero : q5SeedConstant ≠ 0 := by
  rw [q5_seed_constant_residue]
  decide

structure Q5SeedConstantReceipt where
  determinantConstant : ZMod 11
  determinantConstant_eq : determinantConstant = q5SeedConstant

theorem q5_seed_determinant_nonzero (c : Q5SeedConstantReceipt) :
    c.determinantConstant ≠ 0 := by
  rw [c.determinantConstant_eq, q5_seed_constant_residue]
  decide

/-! ## Reuse hook for the common endpoint criterion

The endpoint certificate itself is the base-independent object from the
frozen 1/2 code (`Li2Lean/Kit/EndpointCriterion.lean`).  The q=5 work only
provides the signed V inputs above.
-/

noncomputable abbrev q5Value : Real := Li2Lean.li2InvValue q5Base

abbrev Q5EndpointCertificate := Li2Lean.EndpointCertificate q5Value

end Li2Lean.V.Q5Certificate
