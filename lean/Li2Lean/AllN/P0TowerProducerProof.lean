/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/

import Li2Lean.AllN.P0TowerCaseAssembly
import Li2Lean.P0.PositiveTower.FrobeniusFieldUnconditional
import Li2Lean.P0.PositiveTower.SeedArgumentFromResidue
import Li2Lean.P0.PositiveTower.SeedChecks345Interface
import Li2Lean.P0.PositiveTower.SeedsQ6Q8
import Li2Lean.P0.PositiveTower.Q9Q11SeedChecks

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

/-!
# Complete proof of `p0Tower_producer` (`H2-assembly`, r2)

Combines:
* `seed_argument_of_ratResidueOf_ne_zero` (`SeedArgumentFromResidue.lean`),
* `frobenius_field_m4_unconditional` and `m4SeedResidueMatrix_det_eq_source_eval_zero`
  (`FrobeniusFieldUnconditional.lean`),
* `m4SourceResidue_eq_of_div_local` (built here from public `LocalRing.lean` lemmas
  `GoodP`, `reducedOfP`, `reducedRational_value_good`, and
  `Li2Lean.P0.PositiveTower.residue_eq_of_value_eq`),
* `SeedChecks345.tower_q3_seed_nonzero`, `tower_q4_seed_nonzero`,
  `tower_q5_seed_nonzero` (`SeedChecks345.lean`),
* `Q6Q8.tower_q6_seed_entry_table`, `tower_q7_seed_entry_table`,
  `tower_q8_seed_entry_table` and `tower_q6/7/8_inverse_mod` (`SeedsQ6Q8.lean`),
* the `q = 9, 10, 11` source-entry and inverse checks (`SeedTables.lean`,
  `P0PositiveTowerSeeds.lean`, `Q9Q11SeedChecks.lean`), and
* `p0Tower_producer_of_case_inputs` (`P0TowerCaseAssembly.lean`).

Source: v13 `chapters/nonvanishing.tex:70-145,200-275`.
-/

namespace Li2Lean.AllNAssembly

open Li2Lean
open Li2Lean.P0
open Li2Lean.P0.PositiveBase
open Li2Lean.P0.PositiveTower

noncomputable section

/-! ## Generic certificate constructor at `M = 4` from `ratResidueOf ≠ 0` -/

/-- Build a `P0FrobeniusTowerCertificate F 4 p` from `ratResidueOf p (p0SourceEvalQ F 4 0) ≠ 0`
by combining `seed_argument_of_ratResidueOf_ne_zero` with `frobenius_field_m4_unconditional`. -/
theorem towerCertificate_of_ratResidueOf_ne_zero
    {F : P0Family} {p : ℕ} [hp : Fact (Nat.Prime p)]
    (hp10 : 10 < p)
    (hunit : ¬ (p : ℤ) ∣ F.a * (F.a - 1))
    (hres : ratResidueOf p (p0SourceEvalQ F 4 0) ≠ 0) :
    Nonempty (P0FrobeniusTowerCertificate F 4 p) := by
  have hcut : 2 * 4 + 4 / 2 < p := by omega
  obtain ⟨seed, hseed_val, hseed_ne, hseed_arg⟩ :=
    seed_argument_of_ratResidueOf_ne_zero (by decide : 4 ∣ 4) hcut hunit hres
  refine ⟨{
    M_pos := by decide
    M_multiple_four := by decide
    p_prime := hp.out
    p_gt_twoM_plus_h := hcut
    seed := seed
    seed_value := hseed_val
    seed_residue_nonzero := hseed_ne
    seed_argument := hseed_arg
    frobenius := frobenius_field_m4_unconditional rfl hp10 hunit seed hseed_val
  }⟩

/-- Identify `ratResidueOf p (p0SourceEvalQ F 4 0)` with `Matrix.det (m4SeedResidueMatrix F.a p)`. -/
theorem ratResidueOf_source_eval_zero_eq_m4SeedResidueMatrix_det
    {F : P0Family} {p : ℕ} [Fact (Nat.Prime p)]
    (hp10 : 10 < p)
    (hunit : ¬ (p : ℤ) ∣ F.a * (F.a - 1)) :
    ratResidueOf p (p0SourceEvalQ F 4 0) =
      Matrix.det (m4SeedResidueMatrix F.a p) := by
  have hcop : Nat.Coprime (F.a - 1).natAbs p :=
    base_sub_one_coprime_of_not_dvd (p := p) hunit
  rw [m4SeedResidueMatrix_det_eq_source_eval_zero (p := p) F hp10 hcop]
  unfold ratResidueOf
  rw [Rat.cast_def, div_eq_mul_inv]

/-- Compute `m4SourceResidue` at `(i, j)` from a rational quotient `n / d`
and a modular check `n ≡ r * d (mod p)`, using only public declarations from
`Li2Lean.P0.PositiveTower` (`GoodP`, `reducedOfP`, `reducedRational_value_good`,
and `residue_eq_of_value_eq`). -/
theorem m4SourceResidue_eq_of_div_local {p : ℕ} [Fact (Nat.Prime p)]
    (a : ℤ) (i j : Fin 8) (n : ℤ) (d r : ℕ)
    (hval : (p0MatrixQ (a : ℚ) 4 i j).eval 0 = (n : ℚ) / (d : ℚ))
    (hd : (d : ZMod p) ≠ 0)
    (hmod : (n : ZMod p) = (r : ZMod p) * (d : ZMod p)) :
    m4SourceResidue a i j p = (r : ZMod p) := by
  let x : ℚ := (p0MatrixQ (a : ℚ) 4 i j).eval 0
  have hd_cast : ((d : ℤ) : ZMod p) = (d : ZMod p) := Int.cast_natCast d
  have hdZ : ((d : ℤ) : ZMod p) ≠ 0 := by
    rw [hd_cast]
    exact hd
  have hd0 : (d : ℤ) ≠ 0 := by
    intro h0
    apply hdZ
    rw [h0, Int.cast_zero]
  let z₂ : ContourKit.ReducedRational p :=
    { value := (n : ℚ) / (d : ℚ)
      numerator := n
      denominator := (d : ℤ)
      denominator_ne_zero := hd0
      denominator_residue_ne_zero := hdZ
      value_eq := by rw [Int.cast_natCast d]
      residue := (r : ZMod p)
      residue_eq := by
        rw [hd_cast, hmod, mul_assoc, mul_inv_cancel₀ hd, mul_one] }
  have hcop : Nat.Coprime x.den p := by
    change x ∈ GoodP p
    change (p0MatrixQ (a : ℚ) 4 i j).eval 0 ∈ GoodP p
    rw [hval]
    exact reducedRational_value_good p z₂
  let z₁ : ContourKit.ReducedRational p := reducedOfP p x hcop
  exact Li2Lean.P0.PositiveTower.residue_eq_of_value_eq (p := p)
    (x := z₁) (y := z₂) hval

private lemma det_ne_zero_of_mul_eq_one {p : ℕ} [Fact (Nat.Prime p)]
    {A B : Matrix (Fin 8) (Fin 8) (ZMod p)} (hAB : A * B = 1) :
    A.det ≠ 0 := by
  intro hzero
  have hdet := congrArg Matrix.det hAB
  rw [Matrix.det_mul, hzero, zero_mul, Matrix.det_one] at hdet
  exact zero_ne_one hdet

/-! The q = 6, 7, 8 tables already carry a kernel-cheap Boolean residue
check.  Extracting its two cell clauses avoids re-evaluating the large
`ZMod 247229` arithmetic in each matrix entry. -/

private lemma nat_mod_ne_zero_of_bool
    {d p : Nat} (h : (d % p != 0) = true) : d % p ≠ 0 := by
  change decide (d % p ≠ 0) = true at h
  exact of_decide_eq_true h

private lemma int_mod_eq_zero_of_bool
    {n : Int} {p : Nat} (h : (n % (p : Int) == 0) = true) :
    n % (p : Int) = 0 := by
  change decide (n % (p : Int) = 0) = true at h
  exact of_decide_eq_true h

private lemma q6q8_residue_check_cell (q : Nat)
    (hq : Q6Q8.residueCheck q = true) (i j : Fin 8) :
    (Q6Q8.getN (Q6Q8.q6q8Den q) i.val j.val % Q6Q8.q6q8Prime q != 0) = true ∧
      ((Q6Q8.getI (Q6Q8.q6q8Num q) i.val j.val -
        (Q6Q8.getN (Q6Q8.q6q8Res q) i.val j.val : Int) *
          (Q6Q8.getN (Q6Q8.q6q8Den q) i.val j.val : Int)) %
        (Q6Q8.q6q8Prime q : Int) == 0) = true := by
  have h := hq
  simp only [Q6Q8.residueCheck] at h
  rw [List.all_eq_true] at h
  have hi := h i.val (by simp)
  rw [List.all_eq_true] at hi
  have hij := hi j.val (by simp)
  exact Bool.and_eq_true_iff.mp hij

private lemma q6q8_zmod_eq_nat_mul_of_dvd_intmul
    {p : Nat} {n : Int} {r d : Nat}
    (h : (p : Int) ∣ n - (r : Int) * (d : Int)) :
    (n : ZMod p) = (r : ZMod p) * (d : ZMod p) := by
  rw [← sub_eq_zero]
  have hzero :
      (((n - (r : Int) * (d : Int) : Int) : Int) : ZMod p) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr h
  simpa only [Int.cast_sub, Int.cast_mul, Int.cast_natCast] using hzero

private lemma q6q8_den_ne_zero (q : Nat)
    (hq : Q6Q8.residueCheck q = true) (i j : Fin 8) :
    (Q6Q8.getN (Q6Q8.q6q8Den q) i.val j.val :
      ZMod (Q6Q8.q6q8Prime q)) ≠ 0 := by
  have hmodne :
      Q6Q8.getN (Q6Q8.q6q8Den q) i.val j.val % Q6Q8.q6q8Prime q ≠ 0 :=
    nat_mod_ne_zero_of_bool (q6q8_residue_check_cell q hq i j).1
  intro hz
  have hz' :
      ((Q6Q8.getN (Q6Q8.q6q8Den q) i.val j.val : Int) :
        ZMod (Q6Q8.q6q8Prime q)) = 0 := by
    simpa using hz
  have hdvdZ : (Q6Q8.q6q8Prime q : Int) ∣
      (Q6Q8.getN (Q6Q8.q6q8Den q) i.val j.val : Int) :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hz'
  have hdvdN : Q6Q8.q6q8Prime q ∣
      Q6Q8.getN (Q6Q8.q6q8Den q) i.val j.val := by
    exact_mod_cast hdvdZ
  exact hmodne (Nat.mod_eq_zero_of_dvd hdvdN)

private lemma q6q8_num_mod_eq (q : Nat)
    (hq : Q6Q8.residueCheck q = true) (i j : Fin 8) :
    (Q6Q8.getI (Q6Q8.q6q8Num q) i.val j.val :
      ZMod (Q6Q8.q6q8Prime q)) =
      (Q6Q8.getN (Q6Q8.q6q8Res q) i.val j.val :
        ZMod (Q6Q8.q6q8Prime q)) *
        (Q6Q8.getN (Q6Q8.q6q8Den q) i.val j.val :
          ZMod (Q6Q8.q6q8Prime q)) := by
  have hmod := int_mod_eq_zero_of_bool
    (q6q8_residue_check_cell q hq i j).2
  have hdvd : (Q6Q8.q6q8Prime q : Int) ∣
      Q6Q8.getI (Q6Q8.q6q8Num q) i.val j.val -
        (Q6Q8.getN (Q6Q8.q6q8Res q) i.val j.val : Int) *
          (Q6Q8.getN (Q6Q8.q6q8Den q) i.val j.val : Int) :=
    Int.dvd_of_emod_eq_zero hmod
  exact q6q8_zmod_eq_nat_mul_of_dvd_intmul hdvd

/-! ## `q = 3, 4, 5` via `SeedChecks345` -/

theorem tower_case_q3 (hq : InRange (3 : ℤ)) :
    Nonempty (P0FrobeniusTowerCertificate (family (3 : ℤ) hq) 4 17) := by
  haveI : Fact (Nat.Prime 17) := ⟨by decide⟩
  apply towerCertificate_of_ratResidueOf_ne_zero (by decide)
  · change ¬ (17 : ℤ) ∣ (3 : ℤ) * ((3 : ℤ) - 1)
    decide
  · simpa [ratResidueOf, SeedChecks345.ratResidue] using
      SeedChecks345.tower_q3_seed_nonzero

theorem tower_case_q4 (hq : InRange (4 : ℤ)) :
    Nonempty (P0FrobeniusTowerCertificate (family (4 : ℤ) hq) 4 53) := by
  haveI : Fact (Nat.Prime 53) := ⟨by decide⟩
  apply towerCertificate_of_ratResidueOf_ne_zero (by decide)
  · change ¬ (53 : ℤ) ∣ (4 : ℤ) * ((4 : ℤ) - 1)
    decide
  · simpa [ratResidueOf, SeedChecks345.ratResidue] using
      SeedChecks345.tower_q4_seed_nonzero

theorem tower_case_q5 (hq : InRange (5 : ℤ)) :
    Nonempty (P0FrobeniusTowerCertificate (family (5 : ℤ) hq) 4 11) := by
  haveI : Fact (Nat.Prime 11) := ⟨by decide⟩
  apply towerCertificate_of_ratResidueOf_ne_zero (by decide)
  · change ¬ (11 : ℤ) ∣ (5 : ℤ) * ((5 : ℤ) - 1)
    decide
  · simpa [ratResidueOf, SeedChecks345.ratResidue] using
      SeedChecks345.tower_q5_seed_nonzero

/-! ## `q = 6, 7, 8` via `SeedsQ6Q8` -/

private lemma m4SeedResidueMatrix_eq_q6 :
    m4SeedResidueMatrix 6 (Q6Q8.q6q8Prime 6) =
      Q6Q8.residueMatrix 6 := by
  haveI : Fact (Nat.Prime (Q6Q8.q6q8Prime 6)) := ⟨Q6Q8.prime_q6⟩
  refine Matrix.ext fun (i : Fin 8) (j : Fin 8) => ?_
  exact m4SourceResidue_eq_of_div_local 6 i j
    (Q6Q8.getI (Q6Q8.q6q8Num 6) i j)
    (Q6Q8.getN (Q6Q8.q6q8Den 6) i j)
    (Q6Q8.getN (Q6Q8.q6q8Res 6) i j)
    (Q6Q8.tower_q6_seed_entry_table i j)
    (q6q8_den_ne_zero 6 Q6Q8.residue_check_q6 i j)
    (q6q8_num_mod_eq 6 Q6Q8.residue_check_q6 i j)

theorem tower_case_q6 (hq : InRange (6 : ℤ)) :
    Nonempty (P0FrobeniusTowerCertificate (family (6 : ℤ) hq) 4 13) := by
  haveI : Fact (Nat.Prime (Q6Q8.q6q8Prime 6)) := ⟨Q6Q8.prime_q6⟩
  change Nonempty (P0FrobeniusTowerCertificate (family (6 : ℤ) hq) 4 (Q6Q8.q6q8Prime 6))
  have hunit : ¬ (Q6Q8.q6q8Prime 6 : ℤ) ∣
      (family (6 : ℤ) hq).a * ((family (6 : ℤ) hq).a - 1) := by
    change ¬ (13 : ℤ) ∣ (6 : ℤ) * ((6 : ℤ) - 1)
    decide
  apply towerCertificate_of_ratResidueOf_ne_zero Q6Q8.prime_gt_ten_q6 hunit
  rw [ratResidueOf_source_eval_zero_eq_m4SeedResidueMatrix_det Q6Q8.prime_gt_ten_q6 hunit]
  change Matrix.det (m4SeedResidueMatrix 6 (Q6Q8.q6q8Prime 6)) ≠ 0
  rw [m4SeedResidueMatrix_eq_q6]
  exact det_ne_zero_of_mul_eq_one Q6Q8.tower_q6_inverse_mod

private lemma m4SeedResidueMatrix_eq_q7 :
    m4SeedResidueMatrix 7 (Q6Q8.q6q8Prime 7) =
      Q6Q8.residueMatrix 7 := by
  haveI : Fact (Nat.Prime (Q6Q8.q6q8Prime 7)) := ⟨Q6Q8.prime_q7⟩
  refine Matrix.ext fun (i : Fin 8) (j : Fin 8) => ?_
  exact m4SourceResidue_eq_of_div_local 7 i j
    (Q6Q8.getI (Q6Q8.q6q8Num 7) i j)
    (Q6Q8.getN (Q6Q8.q6q8Den 7) i j)
    (Q6Q8.getN (Q6Q8.q6q8Res 7) i j)
    (Q6Q8.tower_q7_seed_entry_table i j)
    (q6q8_den_ne_zero 7 Q6Q8.residue_check_q7 i j)
    (q6q8_num_mod_eq 7 Q6Q8.residue_check_q7 i j)

theorem tower_case_q7 (hq : InRange (7 : ℤ)) :
    Nonempty (P0FrobeniusTowerCertificate (family (7 : ℤ) hq) 4 11) := by
  haveI : Fact (Nat.Prime (Q6Q8.q6q8Prime 7)) := ⟨Q6Q8.prime_q7⟩
  change Nonempty (P0FrobeniusTowerCertificate (family (7 : ℤ) hq) 4 (Q6Q8.q6q8Prime 7))
  have hunit : ¬ (Q6Q8.q6q8Prime 7 : ℤ) ∣
      (family (7 : ℤ) hq).a * ((family (7 : ℤ) hq).a - 1) := by
    change ¬ (11 : ℤ) ∣ (7 : ℤ) * ((7 : ℤ) - 1)
    decide
  apply towerCertificate_of_ratResidueOf_ne_zero Q6Q8.prime_gt_ten_q7 hunit
  rw [ratResidueOf_source_eval_zero_eq_m4SeedResidueMatrix_det Q6Q8.prime_gt_ten_q7 hunit]
  change Matrix.det (m4SeedResidueMatrix 7 (Q6Q8.q6q8Prime 7)) ≠ 0
  rw [m4SeedResidueMatrix_eq_q7]
  exact det_ne_zero_of_mul_eq_one Q6Q8.tower_q7_inverse_mod

private lemma m4SeedResidueMatrix_eq_q8 :
    m4SeedResidueMatrix 8 (Q6Q8.q6q8Prime 8) =
      Q6Q8.residueMatrix 8 := by
  haveI : Fact (Nat.Prime (Q6Q8.q6q8Prime 8)) := ⟨Q6Q8.prime_q8⟩
  refine Matrix.ext fun (i : Fin 8) (j : Fin 8) => ?_
  exact m4SourceResidue_eq_of_div_local 8 i j
    (Q6Q8.getI (Q6Q8.q6q8Num 8) i j)
    (Q6Q8.getN (Q6Q8.q6q8Den 8) i j)
    (Q6Q8.getN (Q6Q8.q6q8Res 8) i j)
    (Q6Q8.tower_q8_seed_entry_table i j)
    (q6q8_den_ne_zero 8 Q6Q8.residue_check_q8 i j)
    (q6q8_num_mod_eq 8 Q6Q8.residue_check_q8 i j)

theorem tower_case_q8 (hq : InRange (8 : ℤ)) :
    Nonempty (P0FrobeniusTowerCertificate (family (8 : ℤ) hq) 4 247229) := by
  haveI : Fact (Nat.Prime (Q6Q8.q6q8Prime 8)) := ⟨Q6Q8.prime_q8⟩
  change Nonempty (P0FrobeniusTowerCertificate (family (8 : ℤ) hq) 4 (Q6Q8.q6q8Prime 8))
  have hunit : ¬ (Q6Q8.q6q8Prime 8 : ℤ) ∣
      (family (8 : ℤ) hq).a * ((family (8 : ℤ) hq).a - 1) := by
    change ¬ (247229 : ℤ) ∣ (8 : ℤ) * ((8 : ℤ) - 1)
    decide
  apply towerCertificate_of_ratResidueOf_ne_zero Q6Q8.prime_gt_ten_q8 hunit
  rw [ratResidueOf_source_eval_zero_eq_m4SeedResidueMatrix_det Q6Q8.prime_gt_ten_q8 hunit]
  change Matrix.det (m4SeedResidueMatrix 8 (Q6Q8.q6q8Prime 8)) ≠ 0
  rw [m4SeedResidueMatrix_eq_q8]
  exact det_ne_zero_of_mul_eq_one Q6Q8.tower_q8_inverse_mod

/-! ## `q = 9` (`p = 41`) -/

private theorem tower_q9_seed_entry_row0 (j : Fin 8) :
    sourceMatrix 9 (0 : Fin 8) j =
      (Q6Q8.getI SeedTables.num9 (0 : Fin 8) j : ℚ) /
        (PositiveTower.getN SeedTables.den9 (0 : Fin 8) j : ℚ) := by
  fin_cases j <;>
    norm_num [sourceMatrix, Q6Q8.getI, PositiveTower.getN,
      SeedTables.num9, SeedTables.den9, Nat.choose,
      Finset.sum_range_succ, Finset.sum_range_zero,
      p0MatrixQ, p0CQ, p0BQ, p0BQQ, p0TQ, p0UQ, p0Q, p0AQ]

private theorem tower_q9_seed_entry_row1 (j : Fin 8) :
    sourceMatrix 9 (1 : Fin 8) j =
      (Q6Q8.getI SeedTables.num9 (1 : Fin 8) j : ℚ) /
        (PositiveTower.getN SeedTables.den9 (1 : Fin 8) j : ℚ) := by
  fin_cases j <;>
    norm_num [sourceMatrix, Q6Q8.getI, PositiveTower.getN,
      SeedTables.num9, SeedTables.den9, Nat.choose,
      Finset.sum_range_succ, Finset.sum_range_zero,
      p0MatrixQ, p0CQ, p0BQ, p0BQQ, p0TQ, p0UQ, p0Q, p0AQ]

private theorem tower_q9_seed_entry_row2 (j : Fin 8) :
    sourceMatrix 9 (2 : Fin 8) j =
      (Q6Q8.getI SeedTables.num9 (2 : Fin 8) j : ℚ) /
        (PositiveTower.getN SeedTables.den9 (2 : Fin 8) j : ℚ) := by
  fin_cases j <;>
    norm_num [sourceMatrix, Q6Q8.getI, PositiveTower.getN,
      SeedTables.num9, SeedTables.den9, Nat.choose,
      Finset.sum_range_succ, Finset.sum_range_zero,
      p0MatrixQ, p0CQ, p0BQ, p0BQQ, p0TQ, p0UQ, p0Q, p0AQ]

private theorem tower_q9_seed_entry_row3 (j : Fin 8) :
    sourceMatrix 9 (3 : Fin 8) j =
      (Q6Q8.getI SeedTables.num9 (3 : Fin 8) j : ℚ) /
        (PositiveTower.getN SeedTables.den9 (3 : Fin 8) j : ℚ) := by
  fin_cases j <;>
    norm_num [sourceMatrix, Q6Q8.getI, PositiveTower.getN,
      SeedTables.num9, SeedTables.den9, Nat.choose,
      Finset.sum_range_succ, Finset.sum_range_zero,
      p0MatrixQ, p0CQ, p0BQ, p0BQQ, p0TQ, p0UQ, p0Q, p0AQ]

private theorem tower_q9_seed_entry_row4 (j : Fin 8) :
    sourceMatrix 9 (4 : Fin 8) j =
      (Q6Q8.getI SeedTables.num9 (4 : Fin 8) j : ℚ) /
        (PositiveTower.getN SeedTables.den9 (4 : Fin 8) j : ℚ) := by
  fin_cases j <;>
    norm_num [sourceMatrix, Q6Q8.getI, PositiveTower.getN,
      SeedTables.num9, SeedTables.den9, Nat.choose,
      Finset.sum_range_succ, Finset.sum_range_zero,
      p0MatrixQ, p0CQ, p0BQ, p0BQQ, p0TQ, p0UQ, p0Q, p0AQ]

private theorem tower_q9_seed_entry_row5 (j : Fin 8) :
    sourceMatrix 9 (5 : Fin 8) j =
      (Q6Q8.getI SeedTables.num9 (5 : Fin 8) j : ℚ) /
        (PositiveTower.getN SeedTables.den9 (5 : Fin 8) j : ℚ) := by
  fin_cases j <;>
    norm_num [sourceMatrix, Q6Q8.getI, PositiveTower.getN,
      SeedTables.num9, SeedTables.den9, Nat.choose,
      Finset.sum_range_succ, Finset.sum_range_zero,
      p0MatrixQ, p0CQ, p0BQ, p0BQQ, p0TQ, p0UQ, p0Q, p0AQ]

private theorem tower_q9_seed_entry_row6 (j : Fin 8) :
    sourceMatrix 9 (6 : Fin 8) j =
      (Q6Q8.getI SeedTables.num9 (6 : Fin 8) j : ℚ) /
        (PositiveTower.getN SeedTables.den9 (6 : Fin 8) j : ℚ) := by
  fin_cases j <;>
    norm_num [sourceMatrix, Q6Q8.getI, PositiveTower.getN,
      SeedTables.num9, SeedTables.den9, Nat.choose,
      Finset.sum_range_succ, Finset.sum_range_zero,
      p0MatrixQ, p0CQ, p0BQ, p0BQQ, p0TQ, p0UQ, p0Q, p0AQ]

private theorem tower_q9_seed_entry_row7 (j : Fin 8) :
    sourceMatrix 9 (7 : Fin 8) j =
      (Q6Q8.getI SeedTables.num9 (7 : Fin 8) j : ℚ) /
        (PositiveTower.getN SeedTables.den9 (7 : Fin 8) j : ℚ) := by
  fin_cases j <;>
    norm_num [sourceMatrix, Q6Q8.getI, PositiveTower.getN,
      SeedTables.num9, SeedTables.den9, Nat.choose,
      Finset.sum_range_succ, Finset.sum_range_zero,
      p0MatrixQ, p0CQ, p0BQ, p0BQQ, p0TQ, p0UQ, p0Q, p0AQ]

theorem tower_q9_seed_entry_table (i j : Fin 8) :
    sourceMatrix 9 i j =
      (Q6Q8.getI SeedTables.num9 i j : ℚ) /
        (PositiveTower.getN SeedTables.den9 i j : ℚ) := by
  fin_cases i
  · exact tower_q9_seed_entry_row0 j
  · exact tower_q9_seed_entry_row1 j
  · exact tower_q9_seed_entry_row2 j
  · exact tower_q9_seed_entry_row3 j
  · exact tower_q9_seed_entry_row4 j
  · exact tower_q9_seed_entry_row5 j
  · exact tower_q9_seed_entry_row6 j
  · exact tower_q9_seed_entry_row7 j

theorem tower_q9_inverse_Matrix_mod :
    residueMatrix9 * inverseMatrix9 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

private lemma q9_den_ne_zero (i j : Fin 8) :
    (PositiveTower.getN SeedTables.den9 i j : ZMod 41) ≠ 0 := by
  fin_cases i <;> fin_cases j <;> decide

private lemma q9_num_mod_eq (i j : Fin 8) :
    (Q6Q8.getI SeedTables.num9 i j : ZMod 41) =
      (PositiveTower.getN SeedTables.res9 i j : ZMod 41) *
        (PositiveTower.getN SeedTables.den9 i j : ZMod 41) := by
  fin_cases i <;> fin_cases j <;> decide

private lemma m4SeedResidueMatrix_eq_q9 :
    m4SeedResidueMatrix 9 41 = residueMatrix9 := by
  haveI : Fact (Nat.Prime 41) := ⟨q9_prime⟩
  refine Matrix.ext fun (i : Fin 8) (j : Fin 8) => ?_
  exact m4SourceResidue_eq_of_div_local 9 i j
    (Q6Q8.getI SeedTables.num9 i j)
    (PositiveTower.getN SeedTables.den9 i j)
    (PositiveTower.getN SeedTables.res9 i j)
    (tower_q9_seed_entry_table i j)
    (q9_den_ne_zero i j)
    (q9_num_mod_eq i j)

theorem tower_case_q9 (hq : InRange (9 : ℤ)) :
    Nonempty (P0FrobeniusTowerCertificate (family (9 : ℤ) hq) 4 41) := by
  haveI : Fact (Nat.Prime 41) := ⟨by decide⟩
  have hunit : ¬ (41 : ℤ) ∣
      (family (9 : ℤ) hq).a * ((family (9 : ℤ) hq).a - 1) := by
    change ¬ (41 : ℤ) ∣ (9 : ℤ) * ((9 : ℤ) - 1)
    decide
  apply towerCertificate_of_ratResidueOf_ne_zero (by decide) hunit
  rw [ratResidueOf_source_eval_zero_eq_m4SeedResidueMatrix_det (by decide) hunit]
  change Matrix.det (m4SeedResidueMatrix 9 41) ≠ 0
  rw [m4SeedResidueMatrix_eq_q9]
  exact det_ne_zero_of_mul_eq_one tower_q9_inverse_Matrix_mod

/-! ## `q = 10` (`p = 59`) -/

private theorem tower_q10_seed_entry_row0 (j : Fin 8) :
    sourceMatrix 10 (0 : Fin 8) j =
      (Q6Q8.getI SeedTables.num10 (0 : Fin 8) j : ℚ) /
        (PositiveTower.getN SeedTables.den10 (0 : Fin 8) j : ℚ) := by
  fin_cases j <;>
    norm_num [sourceMatrix, Q6Q8.getI, PositiveTower.getN,
      SeedTables.num10, SeedTables.den10, Nat.choose,
      Finset.sum_range_succ, Finset.sum_range_zero,
      p0MatrixQ, p0CQ, p0BQ, p0BQQ, p0TQ, p0UQ, p0Q, p0AQ]

private theorem tower_q10_seed_entry_row1 (j : Fin 8) :
    sourceMatrix 10 (1 : Fin 8) j =
      (Q6Q8.getI SeedTables.num10 (1 : Fin 8) j : ℚ) /
        (PositiveTower.getN SeedTables.den10 (1 : Fin 8) j : ℚ) := by
  fin_cases j <;>
    norm_num [sourceMatrix, Q6Q8.getI, PositiveTower.getN,
      SeedTables.num10, SeedTables.den10, Nat.choose,
      Finset.sum_range_succ, Finset.sum_range_zero,
      p0MatrixQ, p0CQ, p0BQ, p0BQQ, p0TQ, p0UQ, p0Q, p0AQ]

private theorem tower_q10_seed_entry_row2 (j : Fin 8) :
    sourceMatrix 10 (2 : Fin 8) j =
      (Q6Q8.getI SeedTables.num10 (2 : Fin 8) j : ℚ) /
        (PositiveTower.getN SeedTables.den10 (2 : Fin 8) j : ℚ) := by
  fin_cases j <;>
    norm_num [sourceMatrix, Q6Q8.getI, PositiveTower.getN,
      SeedTables.num10, SeedTables.den10, Nat.choose,
      Finset.sum_range_succ, Finset.sum_range_zero,
      p0MatrixQ, p0CQ, p0BQ, p0BQQ, p0TQ, p0UQ, p0Q, p0AQ]

private theorem tower_q10_seed_entry_row3 (j : Fin 8) :
    sourceMatrix 10 (3 : Fin 8) j =
      (Q6Q8.getI SeedTables.num10 (3 : Fin 8) j : ℚ) /
        (PositiveTower.getN SeedTables.den10 (3 : Fin 8) j : ℚ) := by
  fin_cases j <;>
    norm_num [sourceMatrix, Q6Q8.getI, PositiveTower.getN,
      SeedTables.num10, SeedTables.den10, Nat.choose,
      Finset.sum_range_succ, Finset.sum_range_zero,
      p0MatrixQ, p0CQ, p0BQ, p0BQQ, p0TQ, p0UQ, p0Q, p0AQ]

private theorem tower_q10_seed_entry_row4 (j : Fin 8) :
    sourceMatrix 10 (4 : Fin 8) j =
      (Q6Q8.getI SeedTables.num10 (4 : Fin 8) j : ℚ) /
        (PositiveTower.getN SeedTables.den10 (4 : Fin 8) j : ℚ) := by
  fin_cases j <;>
    norm_num [sourceMatrix, Q6Q8.getI, PositiveTower.getN,
      SeedTables.num10, SeedTables.den10, Nat.choose,
      Finset.sum_range_succ, Finset.sum_range_zero,
      p0MatrixQ, p0CQ, p0BQ, p0BQQ, p0TQ, p0UQ, p0Q, p0AQ]

private theorem tower_q10_seed_entry_row5 (j : Fin 8) :
    sourceMatrix 10 (5 : Fin 8) j =
      (Q6Q8.getI SeedTables.num10 (5 : Fin 8) j : ℚ) /
        (PositiveTower.getN SeedTables.den10 (5 : Fin 8) j : ℚ) := by
  fin_cases j <;>
    norm_num [sourceMatrix, Q6Q8.getI, PositiveTower.getN,
      SeedTables.num10, SeedTables.den10, Nat.choose,
      Finset.sum_range_succ, Finset.sum_range_zero,
      p0MatrixQ, p0CQ, p0BQ, p0BQQ, p0TQ, p0UQ, p0Q, p0AQ]

private theorem tower_q10_seed_entry_row6 (j : Fin 8) :
    sourceMatrix 10 (6 : Fin 8) j =
      (Q6Q8.getI SeedTables.num10 (6 : Fin 8) j : ℚ) /
        (PositiveTower.getN SeedTables.den10 (6 : Fin 8) j : ℚ) := by
  fin_cases j <;>
    norm_num [sourceMatrix, Q6Q8.getI, PositiveTower.getN,
      SeedTables.num10, SeedTables.den10, Nat.choose,
      Finset.sum_range_succ, Finset.sum_range_zero,
      p0MatrixQ, p0CQ, p0BQ, p0BQQ, p0TQ, p0UQ, p0Q, p0AQ]

private theorem tower_q10_seed_entry_row7 (j : Fin 8) :
    sourceMatrix 10 (7 : Fin 8) j =
      (Q6Q8.getI SeedTables.num10 (7 : Fin 8) j : ℚ) /
        (PositiveTower.getN SeedTables.den10 (7 : Fin 8) j : ℚ) := by
  fin_cases j <;>
    norm_num [sourceMatrix, Q6Q8.getI, PositiveTower.getN,
      SeedTables.num10, SeedTables.den10, Nat.choose,
      Finset.sum_range_succ, Finset.sum_range_zero,
      p0MatrixQ, p0CQ, p0BQ, p0BQQ, p0TQ, p0UQ, p0Q, p0AQ]

theorem tower_q10_seed_entry_table (i j : Fin 8) :
    sourceMatrix 10 i j =
      (Q6Q8.getI SeedTables.num10 i j : ℚ) /
        (PositiveTower.getN SeedTables.den10 i j : ℚ) := by
  fin_cases i
  · exact tower_q10_seed_entry_row0 j
  · exact tower_q10_seed_entry_row1 j
  · exact tower_q10_seed_entry_row2 j
  · exact tower_q10_seed_entry_row3 j
  · exact tower_q10_seed_entry_row4 j
  · exact tower_q10_seed_entry_row5 j
  · exact tower_q10_seed_entry_row6 j
  · exact tower_q10_seed_entry_row7 j

theorem tower_q10_inverse_Matrix_mod :
    residueMatrix10 * inverseMatrix10 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

private lemma q10_den_ne_zero (i j : Fin 8) :
    (PositiveTower.getN SeedTables.den10 i j : ZMod 59) ≠ 0 := by
  fin_cases i <;> fin_cases j <;> decide

private lemma q10_num_mod_eq (i j : Fin 8) :
    (Q6Q8.getI SeedTables.num10 i j : ZMod 59) =
      (PositiveTower.getN SeedTables.res10 i j : ZMod 59) *
        (PositiveTower.getN SeedTables.den10 i j : ZMod 59) := by
  fin_cases i <;> fin_cases j <;> decide

private lemma m4SeedResidueMatrix_eq_q10 :
    m4SeedResidueMatrix 10 59 = residueMatrix10 := by
  haveI : Fact (Nat.Prime 59) := ⟨q10_prime⟩
  refine Matrix.ext fun (i : Fin 8) (j : Fin 8) => ?_
  exact m4SourceResidue_eq_of_div_local 10 i j
    (Q6Q8.getI SeedTables.num10 i j)
    (PositiveTower.getN SeedTables.den10 i j)
    (PositiveTower.getN SeedTables.res10 i j)
    (tower_q10_seed_entry_table i j)
    (q10_den_ne_zero i j)
    (q10_num_mod_eq i j)

theorem tower_case_q10 (hq : InRange (10 : ℤ)) :
    Nonempty (P0FrobeniusTowerCertificate (family (10 : ℤ) hq) 4 59) := by
  haveI : Fact (Nat.Prime 59) := ⟨by decide⟩
  have hunit : ¬ (59 : ℤ) ∣
      (family (10 : ℤ) hq).a * ((family (10 : ℤ) hq).a - 1) := by
    change ¬ (59 : ℤ) ∣ (10 : ℤ) * ((10 : ℤ) - 1)
    decide
  apply towerCertificate_of_ratResidueOf_ne_zero (by decide) hunit
  rw [ratResidueOf_source_eval_zero_eq_m4SeedResidueMatrix_det (by decide) hunit]
  change Matrix.det (m4SeedResidueMatrix 10 59) ≠ 0
  rw [m4SeedResidueMatrix_eq_q10]
  exact det_ne_zero_of_mul_eq_one tower_q10_inverse_Matrix_mod

/-! ## `q = 11` (`p = 197`) -/

private theorem tower_q11_seed_entry_row0 (j : Fin 8) :
    sourceMatrix 11 (0 : Fin 8) j =
      (Q6Q8.getI SeedTables.num11 (0 : Fin 8) j : ℚ) /
        (PositiveTower.getN SeedTables.den11 (0 : Fin 8) j : ℚ) := by
  fin_cases j <;>
    norm_num [sourceMatrix, Q6Q8.getI, PositiveTower.getN,
      SeedTables.num11, SeedTables.den11, Nat.choose,
      Finset.sum_range_succ, Finset.sum_range_zero,
      p0MatrixQ, p0CQ, p0BQ, p0BQQ, p0TQ, p0UQ, p0Q, p0AQ]

private theorem tower_q11_seed_entry_row1 (j : Fin 8) :
    sourceMatrix 11 (1 : Fin 8) j =
      (Q6Q8.getI SeedTables.num11 (1 : Fin 8) j : ℚ) /
        (PositiveTower.getN SeedTables.den11 (1 : Fin 8) j : ℚ) := by
  fin_cases j <;>
    norm_num [sourceMatrix, Q6Q8.getI, PositiveTower.getN,
      SeedTables.num11, SeedTables.den11, Nat.choose,
      Finset.sum_range_succ, Finset.sum_range_zero,
      p0MatrixQ, p0CQ, p0BQ, p0BQQ, p0TQ, p0UQ, p0Q, p0AQ]

private theorem tower_q11_seed_entry_row2 (j : Fin 8) :
    sourceMatrix 11 (2 : Fin 8) j =
      (Q6Q8.getI SeedTables.num11 (2 : Fin 8) j : ℚ) /
        (PositiveTower.getN SeedTables.den11 (2 : Fin 8) j : ℚ) := by
  fin_cases j <;>
    norm_num [sourceMatrix, Q6Q8.getI, PositiveTower.getN,
      SeedTables.num11, SeedTables.den11, Nat.choose,
      Finset.sum_range_succ, Finset.sum_range_zero,
      p0MatrixQ, p0CQ, p0BQ, p0BQQ, p0TQ, p0UQ, p0Q, p0AQ]

private theorem tower_q11_seed_entry_row3 (j : Fin 8) :
    sourceMatrix 11 (3 : Fin 8) j =
      (Q6Q8.getI SeedTables.num11 (3 : Fin 8) j : ℚ) /
        (PositiveTower.getN SeedTables.den11 (3 : Fin 8) j : ℚ) := by
  fin_cases j <;>
    norm_num [sourceMatrix, Q6Q8.getI, PositiveTower.getN,
      SeedTables.num11, SeedTables.den11, Nat.choose,
      Finset.sum_range_succ, Finset.sum_range_zero,
      p0MatrixQ, p0CQ, p0BQ, p0BQQ, p0TQ, p0UQ, p0Q, p0AQ]

private theorem tower_q11_seed_entry_row4 (j : Fin 8) :
    sourceMatrix 11 (4 : Fin 8) j =
      (Q6Q8.getI SeedTables.num11 (4 : Fin 8) j : ℚ) /
        (PositiveTower.getN SeedTables.den11 (4 : Fin 8) j : ℚ) := by
  fin_cases j <;>
    norm_num [sourceMatrix, Q6Q8.getI, PositiveTower.getN,
      SeedTables.num11, SeedTables.den11, Nat.choose,
      Finset.sum_range_succ, Finset.sum_range_zero,
      p0MatrixQ, p0CQ, p0BQ, p0BQQ, p0TQ, p0UQ, p0Q, p0AQ]

private theorem tower_q11_seed_entry_row5 (j : Fin 8) :
    sourceMatrix 11 (5 : Fin 8) j =
      (Q6Q8.getI SeedTables.num11 (5 : Fin 8) j : ℚ) /
        (PositiveTower.getN SeedTables.den11 (5 : Fin 8) j : ℚ) := by
  fin_cases j <;>
    norm_num [sourceMatrix, Q6Q8.getI, PositiveTower.getN,
      SeedTables.num11, SeedTables.den11, Nat.choose,
      Finset.sum_range_succ, Finset.sum_range_zero,
      p0MatrixQ, p0CQ, p0BQ, p0BQQ, p0TQ, p0UQ, p0Q, p0AQ]

private theorem tower_q11_seed_entry_row6 (j : Fin 8) :
    sourceMatrix 11 (6 : Fin 8) j =
      (Q6Q8.getI SeedTables.num11 (6 : Fin 8) j : ℚ) /
        (PositiveTower.getN SeedTables.den11 (6 : Fin 8) j : ℚ) := by
  fin_cases j <;>
    norm_num [sourceMatrix, Q6Q8.getI, PositiveTower.getN,
      SeedTables.num11, SeedTables.den11, Nat.choose,
      Finset.sum_range_succ, Finset.sum_range_zero,
      p0MatrixQ, p0CQ, p0BQ, p0BQQ, p0TQ, p0UQ, p0Q, p0AQ]

private theorem tower_q11_seed_entry_row7 (j : Fin 8) :
    sourceMatrix 11 (7 : Fin 8) j =
      (Q6Q8.getI SeedTables.num11 (7 : Fin 8) j : ℚ) /
        (PositiveTower.getN SeedTables.den11 (7 : Fin 8) j : ℚ) := by
  fin_cases j <;>
    norm_num [sourceMatrix, Q6Q8.getI, PositiveTower.getN,
      SeedTables.num11, SeedTables.den11, Nat.choose,
      Finset.sum_range_succ, Finset.sum_range_zero,
      p0MatrixQ, p0CQ, p0BQ, p0BQQ, p0TQ, p0UQ, p0Q, p0AQ]

theorem tower_q11_seed_entry_table (i j : Fin 8) :
    sourceMatrix 11 i j =
      (Q6Q8.getI SeedTables.num11 i j : ℚ) /
        (PositiveTower.getN SeedTables.den11 i j : ℚ) := by
  fin_cases i
  · exact tower_q11_seed_entry_row0 j
  · exact tower_q11_seed_entry_row1 j
  · exact tower_q11_seed_entry_row2 j
  · exact tower_q11_seed_entry_row3 j
  · exact tower_q11_seed_entry_row4 j
  · exact tower_q11_seed_entry_row5 j
  · exact tower_q11_seed_entry_row6 j
  · exact tower_q11_seed_entry_row7 j

theorem tower_q11_inverse_Matrix_mod :
    residueMatrix11 * inverseMatrix11 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

private lemma q11_den_ne_zero (i j : Fin 8) :
    (PositiveTower.getN SeedTables.den11 i j : ZMod 197) ≠ 0 := by
  fin_cases i <;> fin_cases j <;> decide

private lemma q11_num_mod_eq (i j : Fin 8) :
    (Q6Q8.getI SeedTables.num11 i j : ZMod 197) =
      (PositiveTower.getN SeedTables.res11 i j : ZMod 197) *
        (PositiveTower.getN SeedTables.den11 i j : ZMod 197) := by
  fin_cases i <;> fin_cases j <;> decide

private lemma m4SeedResidueMatrix_eq_q11 :
    m4SeedResidueMatrix 11 197 = residueMatrix11 := by
  haveI : Fact (Nat.Prime 197) := ⟨q11_prime⟩
  refine Matrix.ext fun (i : Fin 8) (j : Fin 8) => ?_
  exact m4SourceResidue_eq_of_div_local 11 i j
    (Q6Q8.getI SeedTables.num11 i j)
    (PositiveTower.getN SeedTables.den11 i j)
    (PositiveTower.getN SeedTables.res11 i j)
    (tower_q11_seed_entry_table i j)
    (q11_den_ne_zero i j)
    (q11_num_mod_eq i j)

theorem tower_case_q11 (hq : InRange (11 : ℤ)) :
    Nonempty (P0FrobeniusTowerCertificate (family (11 : ℤ) hq) 4 197) := by
  haveI : Fact (Nat.Prime 197) := ⟨by decide⟩
  have hunit : ¬ (197 : ℤ) ∣
      (family (11 : ℤ) hq).a * ((family (11 : ℤ) hq).a - 1) := by
    change ¬ (197 : ℤ) ∣ (11 : ℤ) * ((11 : ℤ) - 1)
    decide
  apply towerCertificate_of_ratResidueOf_ne_zero (by decide) hunit
  rw [ratResidueOf_source_eval_zero_eq_m4SeedResidueMatrix_det (by decide) hunit]
  change Matrix.det (m4SeedResidueMatrix 11 197) ≠ 0
  rw [m4SeedResidueMatrix_eq_q11]
  exact det_ne_zero_of_mul_eq_one tower_q11_inverse_Matrix_mod

/-! ## Final `P0TowerCaseInputs` and `p0Tower_producer_proof` -/

theorem p0TowerCaseInputs_proof : P0TowerCaseInputs where
  q3 := tower_case_q3
  q4 := tower_case_q4
  q5 := tower_case_q5
  q6 := tower_case_q6
  q7 := tower_case_q7
  q8 := tower_case_q8
  q9 := tower_case_q9
  q10 := tower_case_q10
  q11 := tower_case_q11

/-- Unconditional proof of the exact statement of `AllNAssembly.p0Tower_producer`
(`Li2Lean/AllN/Producers.lean:733-737`). -/
theorem p0Tower_producer_proof :
    ∀ (q : ℕ) (hq : InRange (q : ℤ)), 3 ≤ q →
      ∃ M p : ℕ,
        Nonempty (P0FrobeniusTowerCertificate (family (q : ℤ) hq) M p) :=
  p0Tower_producer_of_case_inputs p0TowerCaseInputs_proof

end
end Li2Lean.AllNAssembly

#print axioms Li2Lean.AllNAssembly.p0Tower_producer_proof
