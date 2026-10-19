/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Mathlib
import Li2Lean.Kit.EndpointCriterion
import Li2Lean.Kit.PNTAdapter
import Li2Lean.P0.IntegerizationBottom

open Polynomial Filter Topology
open Li2Lean.P0.Integerization

namespace Li2Lean.B4

noncomputable section

/-- The v13 common denominator `d_N = lcm(1,...,N)`; see `hp-tail.tex:177-184`.
This reuses the frozen 1/2 denominator-LCM API.
-/
def hpDenominator (N : ℕ) : ℕ := denominatorLcm N

/-- Every positive index through `N` divides the v13 common denominator;
`hp-tail.tex:183-184`, via the frozen 1/2 `dvd_denominatorLcm` lemma.
-/
theorem hpDenominator_dvd {N r : ℕ} (hr : 1 ≤ r) (hrN : r ≤ N) :
    r ∣ hpDenominator N :=
  dvd_denominatorLcm hr hrN

/-- The coefficient of `Q(z) Li₂(z)` at degree `k`, using the v13 series
coefficient `1/r²`; see `hp-tail.tex:179-184`.
-/
def hpLi2ProductCoeff (Q : Polynomial ℤ) (k : ℕ) : ℚ :=
  ∑ j ∈ Finset.range k,
    (Q.coeff j : ℚ) / (((k - j : ℕ) : ℚ) ^ 2)

/-- Two applications of the frozen 1/2 integerization kit clear each square
denominator in the v13 convolution; `hp-tail.tex:183-184`.
-/
theorem hpLi2ProductCoeff_integerized {N d : ℕ}
    (hdiv : ∀ r, 1 ≤ r → r ≤ N → r ∣ d)
    (Q : Polynomial ℤ) (k : ℕ) (hk : k ≤ N) :
    IsIntMultiple (d * d) (hpLi2ProductCoeff Q k) := by
  classical
  unfold hpLi2ProductCoeff
  apply intMultiple_sum (d * d) (Finset.range k)
  intro j hj
  have hjk : j < k := Finset.mem_range.mp hj
  let r : ℕ := k - j
  have hr : 0 < r := by dsimp [r]; omega
  have hrN : r ≤ N := by dsimp [r]; omega
  have hrd : r ∣ d := hdiv r (by omega) hrN
  have hfirst : IsIntMultiple d ((Q.coeff j : ℚ) / (r : ℚ)) :=
    intMultiple_div_int_of_dvd hr hrd (Q.coeff j)
  have hsecond : IsIntMultiple (d * d)
      (((Q.coeff j : ℚ) / (r : ℚ)) / (r : ℚ)) :=
    intMultiple_div_of_scaled hr hrd hfirst
  have hrq : (r : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hr)
  have hterm :
      (Q.coeff j : ℚ) / (((k - j : ℕ) : ℚ) ^ 2) =
        ((Q.coeff j : ℚ) / (r : ℚ)) / (r : ℚ) := by
    dsimp [r]
    push_cast
    field_simp [hrq]
  rw [hterm]
  exact hsecond

/-- The exact v13 scale `d_N² / b_n²`; see `hp-tail.tex:177-196`.
-/
def hpIntegerizationScale (d b : ℕ) : ℚ :=
  (d : ℚ) ^ 2 / (b : ℚ) ^ 2

/-- A bounded-degree rational polynomial with integral coefficients comes
from an integer polynomial. This packages the coefficient conclusions in
`hp-tail.tex:185-187` without changing the v13 construction.
-/
theorem hp_exists_integer_polynomial_of_coeffs
    (p : Polynomial ℚ) (N : ℕ)
    (hdeg : p.natDegree ≤ N)
    (hcoeff : ∀ k, k ≤ N → ∃ z : ℤ, (z : ℚ) = p.coeff k) :
    ∃ P : Polynomial ℤ, Polynomial.map (Int.castRingHom ℚ) P = p := by
  classical
  have hall : ∀ k, ∃ z : ℤ, (z : ℚ) = p.coeff k := by
    intro k
    by_cases hk : k ≤ N
    · exact hcoeff k hk
    · have hkn : p.natDegree < k := lt_of_le_of_lt hdeg (lt_of_not_ge hk)
      refine ⟨0, ?_⟩
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt hkn]
      norm_num
  let z : ℕ → ℤ := fun k => Classical.choose (hall k)
  have hz (k : ℕ) :
      (Int.castRingHom ℚ) (z k) = p.coeff k := by
    simpa [z] using (Classical.choose_spec (hall k))
  refine ⟨∑ k ∈ p.support, Polynomial.monomial k (z k), ?_⟩
  simp_rw [Polynomial.map_sum, Polynomial.map_monomial, hz,
    ← Polynomial.as_sum_support]

/-- Exact arithmetic content of v13 `eq:hp-integer-poly` (`hp-tail.tex:177-187`).
The hypotheses are precisely the paper's two inputs: the normalized
Casoratian coefficient polynomial `Q=V/b²` has integer coefficients, and
the polynomial part agrees through degree `N` with minus `Q Li₂`.
-/
theorem hp_exact_integerization {N b : ℕ} (hb : 0 < b)
    (W V : Polynomial ℚ) (Q : Polynomial ℤ)
    (hWdeg : W.natDegree ≤ N) (hVdeg : V.natDegree ≤ N)
    (hW : ∀ k, k ≤ N →
      W.coeff k / (b : ℚ) ^ 2 = -hpLi2ProductCoeff Q k)
    (hV : ∀ k, k ≤ N →
      V.coeff k / (b : ℚ) ^ 2 = (Q.coeff k : ℚ)) :
    ∃ WZ VZ : Polynomial ℤ,
      Polynomial.map (Int.castRingHom ℚ) WZ =
        Polynomial.C (hpIntegerizationScale (hpDenominator N) b) * W ∧
      Polynomial.map (Int.castRingHom ℚ) VZ =
        Polynomial.C (hpIntegerizationScale (hpDenominator N) b) * V := by
  classical
  let d := hpDenominator N
  let s := hpIntegerizationScale d b
  have hd : 0 < d := by
    unfold d hpDenominator
    unfold denominatorLcm
    apply Nat.pos_of_ne_zero
    rw [Finset.lcm_ne_zero_iff]
    intro r hr
    exact Nat.ne_of_gt (Finset.mem_Icc.mp hr).1
  have hbq : (b : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hb)
  have hsq : 0 < s := by
    dsimp [s, hpIntegerizationScale]
    positivity
  have hdiv : ∀ r, 1 ≤ r → r ≤ N → r ∣ d := by
    intro r hr hrN
    exact hpDenominator_dvd hr hrN
  have hWcoeff : ∀ k, k ≤ N →
      ∃ z : ℤ, (z : ℚ) = (Polynomial.C s * W).coeff k := by
    intro k hk
    rw [Polynomial.coeff_C_mul]
    have hscale : s * W.coeff k =
        ((d * d : ℕ) : ℚ) * (W.coeff k / (b : ℚ) ^ 2) := by
      dsimp [s, hpIntegerizationScale]
      push_cast
      field_simp [hbq]
    have hconv := hpLi2ProductCoeff_integerized hdiv Q k hk
    rcases hconv with ⟨z, hz⟩
    refine ⟨-z, ?_⟩
    calc
      (-z : ℚ) = -(((d * d : ℕ) : ℚ) * hpLi2ProductCoeff Q k) := by rw [hz]
      _ = ((d * d : ℕ) : ℚ) * (W.coeff k / (b : ℚ) ^ 2) := by rw [hW k hk]; ring
      _ = s * W.coeff k := hscale.symm
  have hVcoeff : ∀ k, k ≤ N →
      ∃ z : ℤ, (z : ℚ) = (Polynomial.C s * V).coeff k := by
    intro k hk
    rw [Polynomial.coeff_C_mul]
    have hscale : s * V.coeff k =
        ((d * d : ℕ) : ℚ) * (V.coeff k / (b : ℚ) ^ 2) := by
      dsimp [s, hpIntegerizationScale]
      push_cast
      field_simp [hbq]
    have hmult : IsIntMultiple (d * d) (Q.coeff k : ℚ) :=
      intMultiple_intCast (d * d) (Q.coeff k)
    rcases hmult with ⟨z, hz⟩
    refine ⟨z, ?_⟩
    calc
      (z : ℚ) = ((d * d : ℕ) : ℚ) * (Q.coeff k : ℚ) := hz.symm
      _ = ((d * d : ℕ) : ℚ) * (V.coeff k / (b : ℚ) ^ 2) := by rw [hV k hk]
      _ = s * V.coeff k := hscale.symm
  have hWscaleDeg : (Polynomial.C s * W).natDegree ≤ N := by
    rw [Polynomial.natDegree_C_mul (ne_of_gt hsq)]
    exact hWdeg
  have hVscaleDeg : (Polynomial.C s * V).natDegree ≤ N := by
    rw [Polynomial.natDegree_C_mul (ne_of_gt hsq)]
    exact hVdeg
  obtain ⟨WZ, hWZ⟩ := hp_exists_integer_polynomial_of_coeffs
    (Polynomial.C s * W) N hWscaleDeg hWcoeff
  obtain ⟨VZ, hVZ⟩ := hp_exists_integer_polynomial_of_coeffs
    (Polynomial.C s * V) N hVscaleDeg hVcoeff
  exact ⟨WZ, VZ, hWZ, hVZ⟩

end

end Li2Lean.B4
