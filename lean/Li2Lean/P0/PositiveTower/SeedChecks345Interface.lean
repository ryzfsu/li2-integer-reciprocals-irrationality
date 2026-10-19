/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.PositiveTower.SeedChecks345

/-!
q = 3, 4, 5 finite tower interface.

This is the finite-data aggregation used by the construction-bound P0 tower
route.  It follows v13 `nonvanishing.tex:95-145` (the seed and auxiliary
prime table) and exposes the already proved residue/inverse certificates in a
single q-parametric theorem; no new determinant or seed construction is
introduced here.
-/

namespace Li2Lean.P0.PositiveTower.SeedChecks345

noncomputable section

open Li2Lean.P0.PositiveBase

theorem tower_q345_finite_facts :
    ∀ (q : ℕ) (hq : InRange (q : ℤ)), 3 ≤ q → q ≤ 5 →
      Nat.Prime (towerPrime q) ∧
        10 < towerPrime q ∧
        ¬ (towerPrime q : ℤ) ∣ (q : ℤ) ∧
        ¬ (towerPrime q : ℤ) ∣ (q : ℤ) - 1 ∧
        residueCheck q = true ∧
        inverseCheck q = true ∧
        residueMatrix q * inverseMatrix q = 1 ∧
        ratResidue (towerPrime q)
          (p0SourceEvalQ (family (q : ℤ) hq) 4 0) ≠ 0 := by
  intro q hq hq3 hq5
  interval_cases q
  · have hbase := q3_base_conditions
    refine ⟨q3_prime, hbase.1, hbase.2.1, hbase.2.2,
      residueCheck_q3, inverseCheck_q3, tower_q3_inverse_mod, ?_⟩
    change ratResidue 17
      (p0SourceEvalQ (family (3 : ℤ) hq) 4 0) ≠ 0
    simpa [q3InRange] using tower_q3_seed_nonzero
  · have hbase := q4_base_conditions
    refine ⟨q4_prime, hbase.1, hbase.2.1, hbase.2.2,
      residueCheck_q4, inverseCheck_q4, tower_q4_inverse_mod, ?_⟩
    change ratResidue 53
      (p0SourceEvalQ (family (4 : ℤ) hq) 4 0) ≠ 0
    simpa [q4InRange] using tower_q4_seed_nonzero
  · have hbase := q5_base_conditions
    refine ⟨q5_prime, hbase.1, hbase.2.1, hbase.2.2,
      residueCheck_q5, inverseCheck_q5, tower_q5_inverse_mod, ?_⟩
    change ratResidue 11
      (p0SourceEvalQ (family (5 : ℤ) hq) 4 0) ≠ 0
    simpa [q5InRange] using tower_q5_seed_nonzero

end
end Li2Lean.P0.PositiveTower.SeedChecks345

#print axioms Li2Lean.P0.PositiveTower.SeedChecks345.tower_q345_finite_facts
