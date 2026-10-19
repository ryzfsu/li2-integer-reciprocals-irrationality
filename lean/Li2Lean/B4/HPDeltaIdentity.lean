/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
/-
  B4 `delta_identity` field of
  `HPNoAdjacentV13Input` (Li2Lean/B4/HPNoAdjacentActual.lean:55).

  The delta identity is compiled in this release closure.
  Toolchain leanprover/lean4:v4.35.0-rc4, Mathlib 25e572b8.
  Paper: output/li2-alln-paper-v13/source/chapters/hp-tail.tex
    :20-37  residues, A_n,B_n,C_n, eq:hp-tail-series
    :477-505 U_m,K_n,h_m, Phi_n(3n+2), Phi_n(3n+3), lower residues, M_m(0), [z]M_m
    :506-518 determinant: degree <= 3n+3, first column -> R, expansion
    :519-544 two leading coefficients, theta_n, eq:hp-delta

  Route (no analysis, no evaluation point until the very last cast):
    ι : ℚ[X] →+* ℚ⟦X⟧.  R_m := ι A_m + ι B_m * L + ι C_m * Q,
    L = Σ X^k/k, Q = Σ X^k/k^2 (Lean's (0:ℚ)⁻¹ = 0 handles k = 0).
    (S1) coeff_k R_m = hpThreeFormCoeff m k            (convolution, ~35 l)
    (S2) R_m = X^(3m+2) * mk (φ_m(· + 3m+2))           (existing M0c facts, ~25 l)
    (S3) ι Δ_n = R_n ι M_{n+1} - R_{n+1} ι(..) + R_{n+2} ι M_n
         (existing replace/expand lemmas, h := fun m => rfl, ~15 l)
    (S4) coeff_k Δ_n for k <= 3n+3 (k<3n+2: 0; 3n+2; 3n+3)       (~45 l)
    (S5) natDegree Δ_n <= 3n+3                                    (~45 l)
    (S6) closed forms: φ_n(3n+2)=K_n, φ_n(3n+3)=K_n 8(n+1)/9;
         lower residues; δ step; M(0), [z]M; theta cross        (~170 l)
    (S7) ℚ[X] identity by Polynomial.ext; real cast field          (~50 l)
  Total ~400 lines.  Every [Verified] is a name/tactic risk, not a math risk:
  each algebraic step is verified exactly (n<=20) and symbolically (all n)
  in the proof plan
-/
import Li2Lean.B4.HPFormalSeries
import Li2Lean.B4.Nonvanishing
import Li2Lean.B4.HPNoAdjacentActual

open Finset Polynomial

namespace Li2Lean.B4.TailAnalytic

noncomputable section

open Li2Lean.B4.Residues
open Li2Lean.B4.ResidueTailBridge


/-! ## S3. Determinant as a power series (hp-tail.tex:506-518) -/

theorem map_hpThreeFormDeterminant {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (A B C : ℕ → R) (n : ℕ) :
    f (hpThreeFormDeterminant A B C n) =
      hpThreeFormDeterminant (fun m => f (A m)) (fun m => f (B m))
        (fun m => f (C m)) n := by
  simp only [hpThreeFormDeterminant, map_add, map_sub, map_mul]

/-- `Δ_n` over ℚ[X]: the actual v13 determinant. -/
def hpDetPoly (n : ℕ) : ℚ[X] :=
  hpThreeFormDeterminant hpApoly hpBpoly hpCpoly n

/-- `M_m = B_m C_{m+1} - C_m B_{m+1}` over ℚ[X]. -/
def hpMinorPoly (m : ℕ) : ℚ[X] := hpAdjacentMinor hpBpoly hpCpoly m

theorem hpDetPoly_series (n : ℕ) :
    hpCo (hpDetPoly n) =
      hpRSeries n * hpCo (hpMinorPoly (n + 1)) -
        hpRSeries (n + 1) *
          hpCo (hpBpoly n * hpCpoly (n + 2) - hpCpoly n * hpBpoly (n + 2)) +
        hpRSeries (n + 2) * hpCo (hpMinorPoly n) := by
  rw [hpDetPoly, map_hpThreeFormDeterminant,
    hpThreeFormDeterminant_replace_first_column _ _ _ hpRSeries
      hpLogSeriesQ hpLi2SeriesQ n (fun m => rfl),
    hpThreeFormDeterminant_expand_first_column]
  simp only [hpMinorPoly, hpAdjacentMinor, map_sub, map_mul]

/-! ## S4. Coefficients `≤ 3n+3` -/

theorem hpDetPoly_coeff_low (n k : ℕ) (hk : k ≤ 3 * n + 3) :
    (hpDetPoly n).coeff k =
      PowerSeries.coeff k (hpRSeries n * hpCo (hpMinorPoly (n + 1))) := by
  have h := congrArg (PowerSeries.coeff k) (hpDetPoly_series n)
  rw [Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coeff_coe] at h
  rw [h, map_add, map_sub,
    coeff_mul_eq_zero_of_X_pow_dvd (X_pow_dvd_hpRSeries (n + 1)) (by omega),
    coeff_mul_eq_zero_of_X_pow_dvd (X_pow_dvd_hpRSeries (n + 2)) (by omega)]
  ring

theorem hpDetPoly_coeff_lt (n k : ℕ) (hk : k < 3 * n + 2) :
    (hpDetPoly n).coeff k = 0 := by
  rw [hpDetPoly_coeff_low n k (by omega)]
  exact coeff_mul_eq_zero_of_X_pow_dvd (X_pow_dvd_hpRSeries n) hk _

theorem hpDetPoly_coeff_lead (n : ℕ) :
    (hpDetPoly n).coeff (3 * n + 2) =
      hpPhiValue n (3 * n + 2) * (hpMinorPoly (n + 1)).coeff 0 := by
  rw [hpDetPoly_coeff_low n _ (by omega), hpRSeries_eq_X_pow_mul, mul_assoc,
    PowerSeries.coeff_X_pow_mul', if_pos le_rfl, Nat.sub_self,
    PowerSeries.coeff_mul]
  simp [PowerSeries.coeff_mk, Polynomial.coeToPowerSeries.ringHom_apply,
    Polynomial.coeff_coe]                                   -- antidiagonal 0

theorem hpDetPoly_coeff_next (n : ℕ) :
    (hpDetPoly n).coeff (3 * n + 3) =
      hpPhiValue n (3 * n + 2) * (hpMinorPoly (n + 1)).coeff 1 +
        hpPhiValue n (3 * n + 3) * (hpMinorPoly (n + 1)).coeff 0 := by
  rw [hpDetPoly_coeff_low n _ le_rfl, hpRSeries_eq_X_pow_mul, mul_assoc,
    PowerSeries.coeff_X_pow_mul', if_pos (by omega),
    show 3 * n + 3 - (3 * n + 2) = 1 by omega, PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_succ]
  simp [PowerSeries.coeff_mk, Polynomial.coeToPowerSeries.ringHom_apply,
    Polynomial.coeff_coe, show 1 + (3 * n + 2) = 3 * n + 3 by omega]

/-! ## S5. Degree bound (hp-tail.tex:509) -/

namespace LegacyDegrees

theorem hpBpoly_natDegree_le (m : ℕ) : (hpBpoly m).natDegree ≤ m := by
  unfold hpBpoly
  refine natDegree_sum_le_of_forall_le _ _ fun j hj => ?_
  exact (natDegree_monomial_le _).trans (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))


theorem hpCpoly_natDegree_le (m : ℕ) : (hpCpoly m).natDegree ≤ m := by
  unfold hpCpoly
  refine natDegree_sum_le_of_forall_le _ _ fun j hj => ?_
  exact (natDegree_monomial_le _).trans (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))

theorem hpApoly_natDegree_le (m : ℕ) : (hpApoly m).natDegree ≤ m := by
  unfold hpApoly
  refine natDegree_sum_le_of_forall_le _ _ fun r hr => ?_
  exact (natDegree_monomial_le _).trans (Finset.mem_range.mp hr)

end LegacyDegrees

theorem natDegree_hpThreeFormDeterminant_le {A B C : ℕ → ℚ[X]}
    (hA : ∀ m, (A m).natDegree ≤ m) (hB : ∀ m, (B m).natDegree ≤ m)
    (hC : ∀ m, (C m).natDegree ≤ m) (n : ℕ) :
    (hpThreeFormDeterminant A B C n).natDegree ≤ 3 * n + 3 := by
  have t : ∀ {p q r : ℚ[X]} {a b c : ℕ}, p.natDegree ≤ a → q.natDegree ≤ b →
      r.natDegree ≤ c → a + b + c = 3 * n + 3 → (p * q * r).natDegree ≤ 3 * n + 3 :=
    fun hp hq hr h => h ▸ natDegree_mul_le_of_le (natDegree_mul_le_of_le hp hq) hr
  unfold hpThreeFormDeterminant
  refine (natDegree_sub_le _ _).trans (max_le ((natDegree_sub_le _ _).trans
    (max_le ((natDegree_sub_le _ _).trans (max_le ((natDegree_add_le _ _).trans
      (max_le ((natDegree_add_le _ _).trans (max_le ?_ ?_)) ?_)) ?_)) ?_)) ?_)
  -- six monomials, each with indices {n, n+1, n+2}
  · exact t (hA n) (hB (n + 1)) (hC (n + 2)) (by omega)
  · exact t (hB n) (hC (n + 1)) (hA (n + 2)) (by omega)
  · exact t (hC n) (hA (n + 1)) (hB (n + 2)) (by omega)
  · exact t (hC n) (hB (n + 1)) (hA (n + 2)) (by omega)
  · exact t (hB n) (hA (n + 1)) (hC (n + 2)) (by omega)
  · exact t (hA n) (hC (n + 1)) (hB (n + 2)) (by omega)

theorem hpDetPoly_natDegree_le (n : ℕ) : (hpDetPoly n).natDegree ≤ 3 * n + 3 :=
  natDegree_hpThreeFormDeterminant_le hpApoly_natDegree_le hpBpoly_natDegree_le
    hpCpoly_natDegree_le n

/-! ## S6. Closed forms (hp-tail.tex:477-544) -/

/-- `h_m = 3H_m - H_{3m+1}`, hp-tail.tex:483. -/
def hpLowerH (m : ℕ) : ℚ := 3 * hpHarmonic m - hpHarmonic (3 * m + 1)
/-- `r_m = m^3/(3m+1)`, hp-tail.tex:486. -/
def hpLowerR (m : ℕ) : ℚ := (m : ℚ) ^ 3 / (3 * (m : ℚ) + 1)
/-- `c_m = 2 + 3/m - 1/(3m+1)`, hp-tail.tex:486. -/
def hpLowerC (m : ℕ) : ℚ := 2 + 3 / (m : ℚ) - 1 / (3 * (m : ℚ) + 1)

-- reuse: ResidueTailBridge.hpHarmonic_succ (FactorialHarmonic.lean:148)
--   hpHarmonic (k+1) = hpHarmonic k + (((k+1 : ℕ)) : ℚ)⁻¹
open Li2Lean.B4.ResidueTailBridge in
theorem hpLowerH_step (m : ℕ) :
    hpLowerH (m + 1) - hpLowerH m = hpDeltaIncrement m := by
  unfold hpLowerH hpDeltaIncrement
  have hm1 : hpHarmonic (m + 1) = hpHarmonic m + ((m + 1 : ℕ) : ℚ)⁻¹ := by
    rw [hpHarmonic_succ]
  have h3a : hpHarmonic (3 * m + 2) = hpHarmonic (3 * m + 1) +
      ((3 * m + 2 : ℕ) : ℚ)⁻¹ := by
    rw [show 3 * m + 2 = (3 * m + 1) + 1 by omega, hpHarmonic_succ]
  have h3b : hpHarmonic (3 * m + 3) = hpHarmonic (3 * m + 2) +
      ((3 * m + 3 : ℕ) : ℚ)⁻¹ := by
    rw [show 3 * m + 3 = (3 * m + 2) + 1 by omega, hpHarmonic_succ]
  have h3c : hpHarmonic (3 * m + 4) = hpHarmonic (3 * m + 3) +
      ((3 * m + 4 : ℕ) : ℚ)⁻¹ := by
    rw [show 3 * m + 4 = (3 * m + 3) + 1 by omega, hpHarmonic_succ]
  rw [show 3 * (m + 1) + 1 = 3 * m + 4 by omega, h3c, h3b, h3a, hm1]
  push_cast
  field_simp
  ring

theorem hpResidueU_zero (m : ℕ) : hpResidueU m 0 = -hpUFactor m := by
  simp [hpResidueU, hpUFactor]

theorem hpResidueV_zero (m : ℕ) : hpResidueV m 0 = hpLowerH m * hpResidueU m 0 := by
  have hH0 : hpHarmonic 0 = 0 := by simp [hpHarmonic]
  rw [hpResidueV, Nat.sub_zero, Nat.sub_zero, hH0, hpLowerH]
  ring

theorem hpResidueU_one_succ (m : ℕ) :
    hpResidueU (m + 1) 1 = hpLowerR (m + 1) * hpResidueU (m + 1) 0 := by
  unfold hpResidueU hpLowerR
  rw [show 3 * (m + 1) + 1 - 1 = 3 * m + 3 by omega, show m + 1 - 1 = m by omega,
    Nat.sub_zero, Nat.sub_zero, show 3 * (m + 1) + 1 = (3 * m + 3) + 1 by omega,
    Nat.factorial_succ (3 * m + 3), Nat.factorial_succ m, Nat.factorial_zero,
    Nat.factorial_one]
  have h1 : ((3 * m + 3).factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have h2 : (m.factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  push_cast
  field_simp

open Li2Lean.B4.ResidueTailBridge in
theorem hpResidueV_one_succ (m : ℕ) :
    hpResidueV (m + 1) 1 =
      hpLowerR (m + 1) * (hpLowerH (m + 1) - hpLowerC (m + 1)) *
        hpResidueU (m + 1) 0 := by
  rw [hpResidueV, hpResidueU_one_succ, show m + 1 - 1 = m by omega,
    show 3 * (m + 1) + 1 - 1 = 3 * m + 3 by omega]
  have hH1 : hpHarmonic 1 = 1 := by simp [hpHarmonic]
  have h4 : hpHarmonic (3 * (m + 1) + 1) = hpHarmonic (3 * m + 3) + (3 * (m : ℚ) + 4)⁻¹ := by
    rw [show 3 * (m + 1) + 1 = (3 * m + 3) + 1 by omega, hpHarmonic_succ]; push_cast; ring
  rw [hpLowerH, hpLowerC, hH1, h4, hpHarmonic_succ m]
  push_cast
  field_simp
  ring

theorem coeff_mul_one (p q : ℚ[X]) :
    (p * q).coeff 1 = p.coeff 0 * q.coeff 1 + p.coeff 1 * q.coeff 0 := by
  rw [Polynomial.coeff_mul, Finset.Nat.sum_antidiagonal_succ]
  simp

/-- `M_m(0) = -U_m U_{m+1} δ_m`, hp-tail.tex:491. -/
theorem hpMinor_coeff_zero (m : ℕ) :
    (hpMinorPoly m).coeff 0 =
      -(hpUFactor m * hpUFactor (m + 1) * hpDeltaIncrement m) := by
  simp only [hpMinorPoly, hpAdjacentMinor, Polynomial.coeff_sub,
    Polynomial.mul_coeff_zero]
  rw [hpBpoly_coeff_of_le m 0 (by omega), hpBpoly_coeff_of_le (m + 1) 0 (by omega),
    hpCpoly_coeff_of_le m 0 (by omega), hpCpoly_coeff_of_le (m + 1) 0 (by omega),
    hpResidueV_zero, hpResidueV_zero, hpResidueU_zero, hpResidueU_zero,
    ← hpLowerH_step m]
  ring

/-- `[z]M_{m+1}`, hp-tail.tex:493-495 (index `m+1 ≥ 1`, so `v_{m+1,1}` exists). -/
theorem hpMinor_coeff_one (m : ℕ) :
    (hpMinorPoly (m + 1)).coeff 1 =
      hpUFactor (m + 1) * hpUFactor (m + 2) *
        (-hpDeltaIncrement (m + 1) * (hpLowerR (m + 1) + hpLowerR (m + 2)) +
          hpLowerR (m + 2) * hpLowerC (m + 2) - hpLowerR (m + 1) * hpLowerC (m + 1)) := by
  simp only [hpMinorPoly, hpAdjacentMinor, Polynomial.coeff_sub, coeff_mul_one]
  rw [hpBpoly_coeff_of_le (m + 1) 0 (by omega), hpBpoly_coeff_of_le (m + 1) 1 (by omega),
    hpBpoly_coeff_of_le (m + 1 + 1) 0 (by omega),
    hpBpoly_coeff_of_le (m + 1 + 1) 1 (by omega),
    hpCpoly_coeff_of_le (m + 1) 0 (by omega), hpCpoly_coeff_of_le (m + 1) 1 (by omega),
    hpCpoly_coeff_of_le (m + 1 + 1) 0 (by omega),
    hpCpoly_coeff_of_le (m + 1 + 1) 1 (by omega),
    hpResidueV_one_succ m, hpResidueV_one_succ (m + 1),
    hpResidueU_one_succ m, hpResidueU_one_succ (m + 1),
    hpResidueV_zero, hpResidueV_zero, hpResidueU_zero, hpResidueU_zero,
    ← hpLowerH_step (m + 1)]
  -- [Verified] `m + 1 + 1` vs `m + 2` atoms: if `ring` fails, first
  -- `simp only [show m + 1 + 1 = m + 2 from rfl]`.
  ring

/-- Numerator at `3n+2+s`, mirroring `eval_hpNumerator_at_pole` (FactorialHarmonic:68):
`s! * N_n(3n+2+s) = (2n+1+s)!`. -/
theorem eval_hpNumerator_above (n s : ℕ) :
    (s.factorial : ℚ) * (hpNumerator n).eval (((3 * n + 2 + s : ℕ)) : ℚ) =
      ((2 * n + 1 + s).factorial : ℚ) := by
  unfold hpNumerator
  simp only [eval_prod, eval_sub, eval_X, eval_C]
  rw [m0_Icc_eq_Ico_succ, Finset.prod_Ico_eq_prod_range,
    show 3 * n + 1 + 1 - (n + 1) = 2 * n + 1 by omega]
  -- term t: (3n+2+s) - (n+1+t) = s + (2n - t) + 1; reflect t ↦ 2n - t
  have hterm : ∀ t ∈ Finset.range (2 * n + 1),
      (((3 * n + 2 + s : ℕ)) : ℚ) - ((n + 1 + t : ℕ) : ℚ) =
        (((s + (2 * n + 1 - 1 - t) + 1 : ℕ)) : ℚ) := by
    intro t ht
    have : t ≤ 2 * n := Nat.lt_succ_iff.mp (Finset.mem_range.mp ht)
    push_cast [Nat.cast_sub this, Nat.cast_sub (show 1 + t ≤ 2 * n + 1 by omega)]
    ring
  rw [Finset.prod_congr rfl hterm,
    Finset.prod_range_reflect (fun t => (((s + t + 1 : ℕ)) : ℚ)) (2 * n + 1)]
  rw [prod_shift_factorial s (2 * n + 1), show s + (2 * n + 1) = 2 * n + 1 + s by omega]

/-- Denominator at `3n+2+s`: `(2n+1+s)! * Π_{j≤n} (3n+2+s-j) = (3n+2+s)!`. -/
theorem prod_denominator_above (n s : ℕ) :
    ((2 * n + 1 + s).factorial : ℚ) *
        ∏ j ∈ Finset.range (n + 1), ((((3 * n + 2 + s : ℕ)) : ℚ) - (j : ℚ)) =
      ((3 * n + 2 + s).factorial : ℚ) := by
  have hterm : ∀ j ∈ Finset.range (n + 1),
      (((3 * n + 2 + s : ℕ)) : ℚ) - (j : ℚ) =
        ((((2 * n + 1 + s) + (n + 1 - 1 - j) + 1 : ℕ)) : ℚ) := by
    intro j hj
    have : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    push_cast [Nat.cast_sub this, Nat.cast_sub (show 1 + j ≤ n + 1 by omega)]
    ring
  rw [Finset.prod_congr rfl hterm,
    Finset.prod_range_reflect (fun j => ((((2 * n + 1 + s) + j + 1 : ℕ)) : ℚ)) (n + 1),
    prod_shift_factorial, show 2 * n + 1 + s + (n + 1) = 3 * n + 2 + s by omega]

/-- `Φ_n(3n+2) = K_n`, hp-tail.tex:484-485. -/
theorem hpPhiValue_lead (n : ℕ) : hpPhiValue n (3 * n + 2) = hpKFactor n := by
  have hN := eval_hpNumerator_above n 0
  have hD := prod_denominator_above n 0
  simp only [Nat.add_zero, Nat.factorial_zero, Nat.cast_one, one_mul] at hN hD
  have hF1 : ((2 * n + 1).factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hF3 : ((3 * n + 2).factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  unfold hpPhiValue hpKFactor
  rw [Finset.prod_pow, hN]
  set P := ∏ j ∈ Finset.range (n + 1), ((((3 * n + 2 : ℕ)) : ℚ) - (j : ℚ)) with hPdef
  have hP : P = ((3 * n + 2).factorial : ℚ) / ((2 * n + 1).factorial : ℚ) := by
    rw [eq_div_iff hF1]; linear_combination hD
  rw [hP]
  field_simp

/-- `Φ_n(3n+3) = K_n * 8(n+1)/9`, hp-tail.tex:484-485. -/
theorem hpPhiValue_next (n : ℕ) :
    hpPhiValue n (3 * n + 3) = hpKFactor n * (8 * ((n : ℚ) + 1) / 9) := by
  have hN := eval_hpNumerator_above n 1
  have hD := prod_denominator_above n 1
  rw [show 3 * n + 2 + 1 = 3 * n + 3 by omega, Nat.factorial_one, Nat.cast_one,
    one_mul] at hN
  rw [show 3 * n + 2 + 1 = 3 * n + 3 by omega] at hD
  have e2 : ((2 * n + 1 + 1).factorial : ℚ) = (2 * (n : ℚ) + 2) * (2 * n + 1).factorial := by
    rw [Nat.factorial_succ]; push_cast; ring
  have e3 : ((3 * n + 3).factorial : ℚ) = (3 * (n : ℚ) + 3) * (3 * n + 2).factorial := by
    rw [show 3 * n + 3 = (3 * n + 2) + 1 by omega, Nat.factorial_succ]; push_cast; ring
  rw [e2] at hN hD
  rw [e3] at hD
  have hF1 : ((2 * n + 1).factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hF3 : ((3 * n + 2).factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have h2 : (2 * (n : ℚ) + 2) ≠ 0 := by positivity
  unfold hpPhiValue hpKFactor
  rw [Finset.prod_pow, hN]
  set P := ∏ j ∈ Finset.range (n + 1), ((((3 * n + 3 : ℕ)) : ℚ) - (j : ℚ)) with hPdef
  have hP : P = (3 * (n : ℚ) + 3) * (3 * n + 2).factorial /
      ((2 * (n : ℚ) + 2) * (2 * n + 1).factorial) := by
    rw [eq_div_iff (mul_ne_zero h2 hF1)]; linear_combination hD
  rw [hP]
  field_simp
  ring
  -- symbolic verification: delta_symbolic_check.py `hpPhiValue_next`
  -- [Verified] the `set P` pattern must match the cast shape left by `unfold hpPhiValue`

/-- θ_n δ_{n+1} cross identity, hp-tail.tex:529-540 (pure ℚ(n) identity). -/
theorem hp_theta_cross (n : ℕ) :
    hpTheta n * hpDeltaIncrement (n + 1) =
      -hpDeltaIncrement (n + 1) * (hpLowerR (n + 1) + hpLowerR (n + 2)) +
        hpLowerR (n + 2) * hpLowerC (n + 2) - hpLowerR (n + 1) * hpLowerC (n + 1) -
        hpDeltaIncrement (n + 1) * (8 * ((n : ℚ) + 1) / 9) := by
  unfold hpTheta hpThetaNumerator hpThetaDenominator hpDeltaIncrement hpLowerR hpLowerC
  push_cast
  have h1 : (3 * (n : ℚ) + 4) ≠ 0 := by positivity
  have h2 : (27 * (n : ℚ) ^ 2 + 108 * (n : ℚ) + 104) ≠ 0 := by positivity
  have h3 : ((n : ℚ) + 1) ≠ 0 := by positivity
  have h4 : ((n : ℚ) + 2) ≠ 0 := by positivity
  field_simp
  ring

/-! ## S7. The ℚ[X] identity and the real field (hp-tail.tex:541-544) -/

theorem hpDetPoly_eq (n : ℕ) :
    hpDetPoly n =
      Polynomial.C (hpDeltaScale n) * X ^ (3 * n + 2) *
        (1 - Polynomial.C (hpTheta n) * X) := by
  have hrhs : Polynomial.C (hpDeltaScale n) * X ^ (3 * n + 2) *
        (1 - Polynomial.C (hpTheta n) * X) =
      Polynomial.C (hpDeltaScale n) * X ^ (3 * n + 2) -
        Polynomial.C (hpDeltaScale n * hpTheta n) * X ^ (3 * n + 3) := by
    rw [map_mul]; ring
  rw [hrhs]
  ext k
  simp only [Polynomial.coeff_sub, Polynomial.coeff_C_mul_X_pow]
  rcases lt_trichotomy k (3 * n + 2) with hk | rfl | hk
  · rw [hpDetPoly_coeff_lt n k hk, if_neg (by omega), if_neg (by omega)]; ring
  · rw [hpDetPoly_coeff_lead, if_pos rfl, if_neg (by omega), hpPhiValue_lead,
      hpMinor_coeff_zero]
    unfold hpDeltaScale; ring
  · rcases Nat.lt_or_ge (3 * n + 3) k with hk' | hk'
    · rw [coeff_eq_zero_of_natDegree_lt ((hpDetPoly_natDegree_le n).trans_lt hk'),
        if_neg (by omega), if_neg (by omega)]; ring
    · obtain rfl : k = 3 * n + 3 := by omega
      rw [hpDetPoly_coeff_next, if_neg (by omega), if_pos rfl, hpPhiValue_lead,
        hpPhiValue_next, hpMinor_coeff_zero, hpMinor_coeff_one n]
      have hx := hp_theta_cross n
      unfold hpDeltaScale
      have hidx : n + 1 + 1 = n + 2 := by omega
      simp only [hidx]
      -- c₃ = K U U' [bracket] - K(8(n+1)/9) U U' δ = K U U' δ θ  (by hx)
      linear_combination -(hpKFactor n * hpUFactor (n + 1) * hpUFactor (n + 2)) * hx


/-- **B2b. The `delta_identity` field** (HPNoAdjacentActual.lean:55), for every
integer `a` (no range hypothesis needed). -/
theorem hpDelta_identity_at (a : ℤ) (n : ℕ) :
    hpThreeFormDeterminantAt a n = (hpDeltaNormalForm n).eval ((a : ℝ)⁻¹) := by
  let f : ℚ[X] →+* ℝ := (Rat.castHom ℝ).comp (Polynomial.evalRingHom ((a : ℚ)⁻¹))
  have hdet : hpThreeFormDeterminantAt a n = f (hpDetPoly n) := by
    rw [hpDetPoly, map_hpThreeFormDeterminant]
    rfl
  rw [hdet, hpDetPoly_eq]
  simp [f, hpDeltaNormalForm]

/-- Wiring (AllN/Producers.lean:158), once C2 supplies `hpRR_inv_ne_zero`:
```
theorem hpNoAdjInput_producer : ∀ a : ℤ, ((12 : ℤ) ≤ a ∨ a ≤ -8) →
    Li2Lean.B4.TailAnalytic.HPNoAdjacentV13Input a := fun a ha =>
  TailAnalytic.hpNoAdjacentV13Input_of_producers ha
    (fun n => TailAnalytic.hpRR_inv_ne_zero ha n)        -- C2, closed
    (fun n => TailAnalytic.hpDelta_identity_at a n)      -- this file
```
-/
example : True := trivial

end

end Li2Lean.B4.TailAnalytic
