/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.IntegerizationFormalMoments
import Li2Lean.P0.IntegerizationFormalBaseParam

namespace Li2Lean.P0.Integerization

noncomputable section

open Li2Lean

/-! Base-parametric specialization of the formal moment bank.

Unlike the q=2 regression, the scale `(a - 1)^g` remains visible.  This is
the exact interface needed by the q-adic and pole ports; setting `a = 2`
reduces each statement to the existing `_two` theorem.
-/

theorem formalTScaled_outerEval_param (a : ℚ) (ha : a ≠ 1) (g i : ℕ) :
    outerEval a (formalTScaled g i) =
      Polynomial.C ((a - 1) ^ g * p0TQ a g i) := by
  let coeff : ℕ → ℚ := fun s =>
    ((-1 : ℚ) ^ s / (s + 1 : ℚ)) * (Nat.choose (i + g) (g - (s + 1)) : ℚ)
  have hfirst :
      outerEval a ((aVar - ratConst 1) ^ g *
          (∑ r ∈ Finset.range i,
            formalU g (i - (r + 1)) * ratConst ((r + 1 : ℚ)⁻¹))) =
        Polynomial.C ((a - 1) ^ g *
          (∑ r ∈ Finset.range i,
            p0UQ a g (i - (r + 1)) / (r + 1 : ℚ))) := by
    simp only [map_mul, map_pow, map_sub, map_sum, formalU_outerEval,
      outerEval_aVar, outerEval_ratConst]
    simp [div_eq_mul_inv]
  have hterm (s : ℕ) (hs : s ∈ Finset.range g) :
      outerEval a (ratConst (coeff s) * formalQNum g (s + 1)) =
        Polynomial.C (coeff s * ((a - 1) ^ g * p0Q a (s + 1))) := by
    have hsle : s + 1 ≤ g := by simpa using hs
    rw [map_mul, outerEval_ratConst,
      formalQNum_outerEval_eq_scale_mul_p0Q a g (s + 1) hsle ha]
    simp [Polynomial.C_mul]
  have hsum :
      (∑ s ∈ Finset.range g,
        outerEval a (ratConst (coeff s) * formalQNum g (s + 1))) =
        Polynomial.C ((a - 1) ^ g *
          (∑ s ∈ Finset.range g, coeff s * p0Q a (s + 1))) := by
    calc
      (∑ s ∈ Finset.range g,
        outerEval a (ratConst (coeff s) * formalQNum g (s + 1))) =
          ∑ s ∈ Finset.range g,
            Polynomial.C (coeff s * ((a - 1) ^ g * p0Q a (s + 1)) ) := by
              apply Finset.sum_congr rfl
              intro s hs
              exact hterm s hs
      _ = Polynomial.C
          (∑ s ∈ Finset.range g,
            coeff s * ((a - 1) ^ g * p0Q a (s + 1))) := by
              rw [← map_sum]
      _ = Polynomial.C ((a - 1) ^ g *
          (∑ s ∈ Finset.range g, coeff s * p0Q a (s + 1))) := by
              congr 1
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro s hs
              ring
  have hsecond :
      outerEval a (aVar ^ i *
          (∑ s ∈ Finset.range g,
            ratConst (coeff s) * formalQNum g (s + 1))) =
        Polynomial.C (a ^ i * ((a - 1) ^ g *
          (∑ s ∈ Finset.range g, coeff s * p0Q a (s + 1)))) := by
    rw [map_mul, map_pow, outerEval_aVar, map_sum, hsum]
    simp
  rw [formalTScaled, map_add, hfirst, hsecond]
  simp [p0TQ, coeff, div_eq_mul_inv]
  ring

theorem formalBScaled_outerEval_param (a : ℚ) (ha : a ≠ 1) (g i : ℕ) :
    outerEval a (formalBScaled g i) =
      Polynomial.C ((a - 1) ^ g * p0BQQ a g i) := by
  let scale : ℚ := (a - 1) ^ g
  let outerCoeff : ℕ → ℚ := fun s =>
    ((-1 : ℚ) ^ s / (s : ℚ)) * (Nat.choose (i + g) (g - s) : ℚ)
  let innerCoeff : ℕ → ℚ := fun r => (r + 1 : ℚ)⁻¹
  have hfirstSum :
      (∑ r ∈ Finset.range i,
        Polynomial.C (p0UQ a g (i - (r + 1))) *
          Polynomial.C ((r + 1 : ℚ)⁻¹) ^ 2) =
        ∑ r ∈ Finset.range i,
          Polynomial.C (p0UQ a g (i - (r + 1)) / (r + 1 : ℚ) ^ 2) := by
    apply Finset.sum_congr rfl
    intro r hr
    rw [← Polynomial.C_pow, ← Polynomial.C_mul]
    congr 1
    rw [div_eq_mul_inv, inv_pow]
  have hfirst :
      outerEval a ((aVar - ratConst 1) ^ g *
          (∑ r ∈ Finset.range i,
            formalU g (i - (r + 1)) * ratConst ((r + 1 : ℚ)⁻¹ ^ 2))) =
        Polynomial.C (scale *
          (∑ r ∈ Finset.range i,
            p0UQ a g (i - (r + 1)) / (r + 1 : ℚ) ^ 2)) := by
    simp only [map_mul, map_pow, map_sub, map_sum, formalU_outerEval,
      outerEval_aVar, outerEval_ratConst]
    rw [hfirstSum]
    rw [← Polynomial.C_sub, Polynomial.C_pow]
  have hqterm (s r : ℕ) (hs : s ∈ Finset.Icc 2 g)
      (hr : r ∈ Finset.range (s - 1)) :
      outerEval a (ratConst (innerCoeff r) * formalQNum g (r + 1)) =
        Polynomial.C (innerCoeff r * (scale * p0Q a (r + 1))) := by
    have hsg : s ≤ g := (Finset.mem_Icc.mp hs).2
    have hrlt : r < s - 1 := Finset.mem_range.mp hr
    have hrg : r + 1 ≤ g := by omega
    rw [map_mul, outerEval_ratConst,
      formalQNum_outerEval_eq_scale_mul_p0Q a g (r + 1) hrg ha]
    simp [innerCoeff, scale, Polynomial.C_mul]
  have hinner (s : ℕ) (hs : s ∈ Finset.Icc 2 g) :
      outerEval a
          (∑ r ∈ Finset.range (s - 1),
            ratConst (innerCoeff r) * formalQNum g (r + 1)) =
        Polynomial.C (scale *
          (∑ r ∈ Finset.range (s - 1), innerCoeff r * p0Q a (r + 1))) := by
    calc
      outerEval a
          (∑ r ∈ Finset.range (s - 1),
            ratConst (innerCoeff r) * formalQNum g (r + 1)) =
          ∑ r ∈ Finset.range (s - 1),
            outerEval a (ratConst (innerCoeff r) * formalQNum g (r + 1)) := by
              rw [map_sum]
      _ = ∑ r ∈ Finset.range (s - 1),
          Polynomial.C (innerCoeff r * (scale * p0Q a (r + 1))) := by
            apply Finset.sum_congr rfl
            intro r hr
            exact hqterm s r hs hr
      _ = Polynomial.C
          (∑ r ∈ Finset.range (s - 1),
            innerCoeff r * (scale * p0Q a (r + 1))) := by
              rw [← map_sum]
      _ = Polynomial.C (scale *
          (∑ r ∈ Finset.range (s - 1), innerCoeff r * p0Q a (r + 1))) := by
            congr 1
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro r hr
            ring
  have houterTerm (s : ℕ) (hs : s ∈ Finset.Icc 2 g) :
      outerEval a
          (ratConst (outerCoeff s) *
            (∑ r ∈ Finset.range (s - 1),
              ratConst (innerCoeff r) * formalQNum g (r + 1))) =
        Polynomial.C (outerCoeff s *
          (scale *
            (∑ r ∈ Finset.range (s - 1), innerCoeff r * p0Q a (r + 1)))) := by
    rw [map_mul, outerEval_ratConst, hinner s hs]
    simp [Polynomial.C_mul]
  have houter :
      (∑ s ∈ Finset.Icc 2 g,
        outerEval a
          (ratConst (outerCoeff s) *
            (∑ r ∈ Finset.range (s - 1),
              ratConst (innerCoeff r) * formalQNum g (r + 1)))) =
        Polynomial.C (scale *
          (∑ s ∈ Finset.Icc 2 g,
            outerCoeff s *
              (∑ r ∈ Finset.range (s - 1), innerCoeff r * p0Q a (r + 1)))) := by
    calc
      (∑ s ∈ Finset.Icc 2 g,
        outerEval a
          (ratConst (outerCoeff s) *
            (∑ r ∈ Finset.range (s - 1),
              ratConst (innerCoeff r) * formalQNum g (r + 1)))) =
        ∑ s ∈ Finset.Icc 2 g,
          Polynomial.C (outerCoeff s *
            (scale *
              (∑ r ∈ Finset.range (s - 1), innerCoeff r * p0Q a (r + 1)))) := by
                apply Finset.sum_congr rfl
                intro s hs
                exact houterTerm s hs
      _ = Polynomial.C
          (∑ s ∈ Finset.Icc 2 g,
            outerCoeff s *
              (scale *
                (∑ r ∈ Finset.range (s - 1), innerCoeff r * p0Q a (r + 1)))) := by
                  rw [← map_sum]
      _ = Polynomial.C (scale *
          (∑ s ∈ Finset.Icc 2 g,
            outerCoeff s *
              (∑ r ∈ Finset.range (s - 1), innerCoeff r * p0Q a (r + 1)))) := by
                congr 1
                rw [Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro s hs
                ring
  have hsecond :
      outerEval a (aVar ^ i *
          (∑ s ∈ Finset.Icc 2 g,
            ratConst (outerCoeff s) *
              (∑ r ∈ Finset.range (s - 1),
                ratConst (innerCoeff r) * formalQNum g (r + 1)))) =
        Polynomial.C (a ^ i * (scale *
          (∑ s ∈ Finset.Icc 2 g,
            outerCoeff s *
              (∑ r ∈ Finset.range (s - 1), innerCoeff r * p0Q a (r + 1)))) ) := by
    rw [map_mul, map_pow, outerEval_aVar, map_sum, houter]
    simp
  have hinnerQ (s : ℕ) :
      (∑ r ∈ Finset.range (s - 1), innerCoeff r * p0Q a (r + 1)) =
        ∑ r ∈ Finset.range (s - 1), p0Q a (r + 1) / (r + 1 : ℚ) := by
    apply Finset.sum_congr rfl
    intro r hr
    simp [innerCoeff, div_eq_mul_inv, mul_comm]
  have houterQ :
      (∑ s ∈ Finset.Icc 2 g,
        outerCoeff s *
          (∑ r ∈ Finset.range (s - 1), innerCoeff r * p0Q a (r + 1))) =
        ∑ s ∈ Finset.Icc 2 g,
          ((-1 : ℚ) ^ s / (s : ℚ)) *
            (Nat.choose (i + g) (g - s) : ℚ) *
            (∑ r ∈ Finset.range (s - 1), p0Q a (r + 1) / (r + 1 : ℚ)) := by
    apply Finset.sum_congr rfl
    intro s hs
    rw [hinnerQ s]
  rw [formalBScaled, map_sub, hfirst, hsecond]
  rw [← Polynomial.C_sub]
  apply congrArg Polynomial.C
  dsimp [p0BQQ, scale]
  rw [houterQ]
  ring

end

end Li2Lean.P0.Integerization

#print axioms Li2Lean.P0.Integerization.formalTScaled_outerEval_param
