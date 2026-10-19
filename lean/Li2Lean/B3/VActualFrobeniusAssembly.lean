/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com)
-/

import Li2Lean.B3.VScaledConstantUnit            -- lanes A1, A2 (master), C, B, D
import Li2Lean.B3.NonvanishingProducerWiring     -- target structures
import Li2Lean.B3.ActualFrobeniusCarrierGeneric  -- vActualStrictTail_of_coefficient_fields
import Li2Lean.B3.Q234SeedConstantFacts          -- q = 2, 3, 4 constant_ne_zero / constant_unit
import Li2Lean.B3.Q2ActualSeedResidueProof       -- Q2I fields; imports Q2SeedT0LU (q2_constant_eq)
import Li2Lean.B3.H3RowResQ2ZMod                 -- q2_row_residue_zmod (imports Q2SeedT0LU)
import Li2Lean.B3.H3RowResQ3ZMod                 -- q3_row_residue_zmod (imports H3E3Q3SeedEval)
import Li2Lean.B3.H3RowResQ4ZMod                 -- q4_row_residue_zmod (imports Q4T0LU)
import Li2Lean.B3.H3RowResQ5ZMod                 -- q5_row_residue_zmod (imports H3E5Q5SeedEval)
import Li2Lean.B3.H3RowResQ6ZMod                 -- q6_row_residue_zmod (imports H3E6Q6SeedEval)
import Li2Lean.B3.H3RowResQ7ZMod                 -- q7_row_residue_zmod (imports H3E7Q7SeedEval)

/-!
# Assembly of the actual signed-V Frobenius tower carrier

Integration revision h3-integration-20261018.  This file closes
`vActualFrobeniusTowerCarrier_generic` (`ActualFrobeniusTowerCarriers.lean:43`)
with no remaining placeholder.  Source: v13 `nonvanishing.tex:146-275`.

Per-field sources (for `q = 2..7`, `p = vSeedPrime q`):

* `scaled_coefficients_integral`: `vFrobeniusScaled_coeff_integral`
  (`VScaledPencilGood`);
* `scaled_constant_unit`: `vScaledConstantUnit`;
* `strict_tail`: `vActualStrictTail_of_coefficient_fields` (master);
* `seed_boundary.denominator_coprime`: uniform, `seedRow_coeff_good`
  (at `k = 0`, `H3RowResidueZMod`);
* `seed_boundary.row_residue`: `qN_row_residue_zmod` (`H3RowResQNZMod`, a
  `ZMod p` LU certificate at `T = 0..4` and an inverse Vandermonde matrix);
* `seed_boundary.constant_eq`: `qN_constant_eq` (master: `Q2SeedT0LU`,
  `H3E3Q3SeedEval`, `Q4T0LU`, `H3E5/6/7QNSeedEval`);
* `seed_boundary.constant_ne_zero`, `.constant_unit`: `Q234SeedConstantFacts`
  (q = 2, 3, 4) and the local copies `h3_qN_constant_*` below (q = 5, 6, 7;
  the originals live in `ActualFrobeniusTowerCarriers.lean`, which imports
  this file);
* q = 2 interface: `q2_source_entry_representative`,
  `q2_determinant_representative`, `q2_seed_residue_det_eq_four`
  (`Q2ActualSeedResidueProof`, master).

`VActualScaledCoefficientCarrier.coefficientwise_frobenius` (false without the
sign `ε`) is not used.
-/

namespace Li2Lean.B3

noncomputable section

open Li2Lean
open Li2Lean.P0.PositiveTower

/-! ## 1. Small uniform facts -/

/-- The paper prime does not divide the base. -/
theorem vSeedPrime_not_dvd_base {q : ℕ} (hq : SignedVBaseRange q) :
    ¬ ((vSeedPrime q : ℤ) ∣ (q : ℤ)) := by
  obtain ⟨h2, h7⟩ := hq
  interval_cases q <;> norm_num [vSeedPrime]
  -- note: alternative `<;> decide`.

/-- The master constants are stated at `(-N : ℤ)`; the structures use
`-((N : ℕ) : ℤ)`.  Abstract transport avoids a definitional-equality
comparison on `V.vPolynomial`. -/
theorem seed_constant_eq_cast {q : ℕ} {a : ℤ} (ha : -((q : ℕ) : ℤ) = a)
    (h : (V.vPolynomial 1 a).coeff 0 = vSeedConstant q) :
    (V.vPolynomial 1 (-(q : ℤ))).coeff 0 = vSeedConstant q := by
  rw [ha]
  exact h

/-! ## 2. Seed boundary and producer -/

/-- Seed boundary from `constant_eq`, the constant facts and the rows; the
denominator field is uniform (at `k = 0`). -/
theorem vActualSeedBoundary_of_rows {q : ℕ} (hq : SignedVBaseRange q)
    (hconst : (V.vPolynomial 1 (-(q : ℤ))).coeff 0 = vSeedConstant q)
    (hne : vSeedConstant q ≠ 0)
    (hunit : padicValRat (vSeedPrime q) (vSeedConstant q) = 0)
    (hrow : ∀ i : Fin 5, vSeedCoeffResidue q i.val =
      (vSeedResidueRow q i : ZMod (vSeedPrime q))) :
    VActualSeedBoundary q hq := by
  haveI : Fact (Nat.Prime (vSeedPrime q)) := ⟨(vSeedPrime_spec hq).1⟩
  have hden : ∀ i : Fin 5,
      Nat.Coprime (vSeedPrime q) ((V.vPolynomial 1 (-(q : ℤ))).coeff i).den := by
    intro i
    have h : Nat.Coprime ((V.vPolynomial 1 (-(q : ℤ))).coeff i.val).den (vSeedPrime q) :=
      seedRow_coeff_good (vSeedPrime_spec hq).2 q i.val
    exact h.symm
    -- note: `GoodP p` membership is `Nat.Coprime x.den p` by definition
    -- (`P0/PositiveTower/LocalRing.lean:26`); master uses the same `change`.
  exact
    { denominator_coprime := hden
      row_residue := hrow
      constant_eq := hconst
      constant_ne_zero := hne
      constant_unit := hunit }

/-- Producer from a seed boundary; every infinite field is uniform. -/
theorem vActualFrobeniusTowerProducer_of_seedBoundary
    {q : ℕ} {hq : SignedVBaseRange q}
    (hB : VActualSeedBoundary q hq) :
    VActualFrobeniusTowerProducer q hq := by
  have hp : Nat.Prime (vSeedPrime q) := (vSeedPrime_spec hq).1
  have hp11 : 11 ≤ vSeedPrime q := (vSeedPrime_spec hq).2
  haveI : Fact (Nat.Prime (vSeedPrime q)) := ⟨hp⟩
  have hqp : ¬ ((vSeedPrime q : ℤ) ∣ (q : ℤ)) := vSeedPrime_not_dvd_base hq
  have h0 : (V.vPolynomial 1 (-(q : ℤ))).coeff 0 ≠ 0 := by
    rw [hB.constant_eq]
    exact hB.constant_ne_zero
  have hu : padicValRat (vSeedPrime q) ((V.vPolynomial 1 (-(q : ℤ))).coeff 0) = 0 := by
    rw [hB.constant_eq]
    exact hB.constant_unit
  have hint : ∀ k : ℕ, 0 < k → ∀ i : ℕ,
      (V.vFrobeniusScaledPolynomial q (vSeedPrime q) k).coeff i ≠ 0 →
        0 ≤ padicValRat (vSeedPrime q)
          ((V.vFrobeniusScaledPolynomial q (vSeedPrime q) k).coeff i) :=
    fun k _ i => vFrobeniusScaled_coeff_integral hp11 q k i
  have hcu : ∀ k : ℕ, 0 < k →
      (V.vFrobeniusScaledPolynomial q (vSeedPrime q) k).coeff 0 ≠ 0 ∧
        padicValRat (vSeedPrime q)
          ((V.vFrobeniusScaledPolynomial q (vSeedPrime q) k).coeff 0) = 0 :=
    fun k _ => vScaledConstantUnit hp11 q hqp h0 hu k
  exact
    { seed_boundary := hB
      scaled_coefficients_integral := hint
      scaled_constant_unit := hcu
      strict_tail := vActualStrictTail_of_coefficient_fields hp hint hcu }

/-! ## 3. Constant facts for q = 5, 6, 7 (copies of the target-file leaves) -/

theorem h3_q5_constant_ne_zero : vSeedConstant 5 ≠ 0 := by
  norm_num [vSeedConstant]

theorem h3_q5_constant_unit : padicValRat (vSeedPrime 5) (vSeedConstant 5) = 0 := by
  norm_num [vSeedPrime, vSeedConstant, padicValRat]
  have hn : ¬(11 : ℤ) ∣ 40320536130840508931350036296875 := by norm_num
  have hd : ¬11 ∣ 2788079616 := by norm_num
  rw [padicValInt.eq_zero_of_not_dvd hn, padicValNat.eq_zero_of_not_dvd hd]
  norm_num

theorem h3_q6_constant_ne_zero : vSeedConstant 6 ≠ 0 := by
  norm_num [vSeedConstant]

theorem h3_q6_constant_unit : padicValRat (vSeedPrime 6) (vSeedConstant 6) = 0 := by
  norm_num [vSeedPrime, vSeedConstant, padicValRat]
  have hn : ¬(17 : ℤ) ∣ 376202458002139670340998058226513923 := by norm_num
  have hd : ¬17 ∣ 28000000000 := by norm_num
  rw [padicValInt.eq_zero_of_not_dvd hn, padicValNat.eq_zero_of_not_dvd hd]
  norm_num

theorem h3_q7_constant_ne_zero : vSeedConstant 7 ≠ 0 := by
  norm_num [vSeedConstant]

theorem h3_q7_constant_unit : padicValRat (vSeedPrime 7) (vSeedConstant 7) = 0 := by
  norm_num [vSeedPrime, vSeedConstant, padicValRat]
  have hn : ¬(17 : ℤ) ∣ 1824058729423489878071240450876107476590203 := by norm_num
  have hd : ¬17 ∣ 398580750000000 := by norm_num
  rw [padicValInt.eq_zero_of_not_dvd hn, padicValNat.eq_zero_of_not_dvd hd]
  norm_num

/-! ## 4. Seed boundaries per base (rows through `ZMod p`) -/

theorem vActualSeedBoundary_neg2 : VActualSeedBoundary 2 q2SignedRange :=
  vActualSeedBoundary_of_rows q2SignedRange
    (seed_constant_eq_cast (by norm_num) q2_constant_eq)
    vActualFrobeniusTowerCarrier_q2_constant_ne_zero
    vActualFrobeniusTowerCarrier_q2_constant_unit
    q2_row_residue_zmod

theorem vActualSeedBoundary_neg3 (hq : SignedVBaseRange 3) : VActualSeedBoundary 3 hq :=
  vActualSeedBoundary_of_rows hq
    (seed_constant_eq_cast (by norm_num) q3_constant_eq)
    vActualFrobeniusTowerCarrier_q3_constant_ne_zero
    vActualFrobeniusTowerCarrier_q3_constant_unit
    q3_row_residue_zmod

theorem vActualSeedBoundary_neg4 (hq : SignedVBaseRange 4) : VActualSeedBoundary 4 hq :=
  vActualSeedBoundary_of_rows hq
    (seed_constant_eq_cast (by norm_num) q4_constant_eq)
    vActualFrobeniusTowerCarrier_q4_constant_ne_zero
    vActualFrobeniusTowerCarrier_q4_constant_unit
    q4_row_residue_zmod

theorem vActualSeedBoundary_neg5 (hq : SignedVBaseRange 5) : VActualSeedBoundary 5 hq :=
  vActualSeedBoundary_of_rows hq
    (seed_constant_eq_cast (by norm_num) q5_constant_eq)
    h3_q5_constant_ne_zero h3_q5_constant_unit
    q5_row_residue_zmod

theorem vActualSeedBoundary_neg6 (hq : SignedVBaseRange 6) : VActualSeedBoundary 6 hq :=
  vActualSeedBoundary_of_rows hq
    (seed_constant_eq_cast (by norm_num) q6_constant_eq)
    h3_q6_constant_ne_zero h3_q6_constant_unit
    q6_row_residue_zmod

theorem vActualSeedBoundary_neg7 (hq : SignedVBaseRange 7) : VActualSeedBoundary 7 hq :=
  vActualSeedBoundary_of_rows hq
    (seed_constant_eq_cast (by norm_num) q7_constant_eq)
    h3_q7_constant_ne_zero h3_q7_constant_unit
    q7_row_residue_zmod
  -- Note (all six): the `by norm_num` goal is `-((N : ℕ) : ℤ) = -N` once `q`
  -- is fixed by the expected type; alternative `(by push_cast; rfl)` or `rfl`.

/-! ## 5. The q = 2 residue interface -/

theorem q2ActualSeedResidueInterface_proof : Q2ActualSeedResidueInterface where
  boundary := vActualSeedBoundary_neg2
  source_entry_representative := q2_source_entry_representative
  determinant_representative := q2_determinant_representative
  residue_det_eq_four := q2_seed_residue_det_eq_four
  -- note: the two `*_representative` theorems are stated with the private
  -- reducible abbrev `q2Prime := vSeedPrime 2`; the fields use `vSeedPrime 2`.

/-! ## 6. The H3 target -/

/-- Final proof of the H3 carrier, assembled from the concrete seed-boundary
and residue certificates above. -/
theorem vActualFrobeniusTowerCarrier_assembled : VActualFrobeniusTowerRangeInputs := by
  have P2 := vActualFrobeniusTowerProducer_of_seedBoundary vActualSeedBoundary_neg2
  exact
    { q2 :=
        { residue := q2ActualSeedResidueInterface_proof
          scaled_coefficients_integral := P2.scaled_coefficients_integral
          scaled_constant_unit := P2.scaled_constant_unit
          strict_tail := P2.strict_tail }
      q3 := fun hq => vActualFrobeniusTowerProducer_of_seedBoundary (vActualSeedBoundary_neg3 hq)
      q4 := fun hq => vActualFrobeniusTowerProducer_of_seedBoundary (vActualSeedBoundary_neg4 hq)
      q5 := fun hq => vActualFrobeniusTowerProducer_of_seedBoundary (vActualSeedBoundary_neg5 hq)
      q6 := fun hq => vActualFrobeniusTowerProducer_of_seedBoundary (vActualSeedBoundary_neg6 hq)
      q7 := fun hq => vActualFrobeniusTowerProducer_of_seedBoundary (vActualSeedBoundary_neg7 hq) }

end
end Li2Lean.B3

#print axioms Li2Lean.B3.vActualFrobeniusTowerProducer_of_seedBoundary
#print axioms Li2Lean.B3.vActualFrobeniusTowerCarrier_assembled
