/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.Q11ContourExteriorFourier
import Li2Lean.P0.Q11ContourSelfEnergyEnclosure
import Li2Lean.P0.ActualReferenceQLogOutsideCheck

open scoped BigOperators

namespace Li2Lean.P0.Q11Data

noncomputable section

open Li2Lean.P0.ConfigContourReference
open Li2Lean.P0.ConfigContourKernel
open Li2Lean.P0.ConfigContourFormula
open Li2Lean.P0.CA.Contour
open Li2Lean.P0.CA.Contour.QI
open Li2Lean.P0.ActualReferenceQLogOutsideCheck

/-!
The q = 11 exterior potential enclosure follows the v13 finite Fourier
formula (`certificate-algorithm.tex:64-75`).  The interval arithmetic is the
same QI construction used by the q = 2 checker; only the q11 mass and Fourier
moments are specialized here.
-/

def q11ContourMomentI (n : ℕ) : QI :=
  smul (1 - (n : ℚ) / 49)
    (sumIdx 64 (fun j =>
      smul ((contourMassUnit j : ℚ) / (3000000000000 : ℚ))
        (cosTab.getD ((n * (2 * j + 1)) % 128) ⟨0, 0⟩)))

theorem q11ContourMomentI_mem {n : ℕ} (hn : n ≤ 48) :
    (q11ContourMomentI n).mem (q11ExteriorContourMoment n) := by
  unfold q11ContourMomentI
  have hsum : q11ExteriorContourMoment n =
      (1 - (n : ℝ) / 49) *
        ∑ j : Fin contourNodeCount,
          q11ContourWeight j * Real.cos ((n : ℝ) * contourAngle j) := by
    rfl
  rw [hsum]
  have hK : ((1 - (n : ℚ) / 49 : ℚ) : ℝ) =
      (1 - (n : ℝ) / 49 : ℝ) := by
    push_cast
    ring
  rw [← hK]
  apply QI.mem_smul
  set g : ℕ → ℝ := fun j =>
    (contourMassUnit j : ℝ) / (3000000000000 : ℝ) *
      Real.cos (n * (Real.pi * (2 * (j : ℝ) + 1) / 64)) with hg
  have hs :
      (∑ j : Fin contourNodeCount,
        q11ContourWeight j * Real.cos ((n : ℝ) * contourAngle j)) =
        ∑ j ∈ Finset.range 64, g j := by
    rw [← Fin.sum_univ_eq_sum_range g]
    rfl
  rw [hs]
  change (sumIdx 64 (fun j =>
    smul ((contourMassUnit j : ℚ) / (3000000000000 : ℚ))
      (cosTab.getD ((n * (2 * j + 1)) % 128) ⟨0, 0⟩))).mem
    (∑ j ∈ Finset.range 64, g j)
  apply QI.mem_sumIdx
  intro j hj
  have h := QI.mem_smul ((contourMassUnit j : ℚ) / (3000000000000 : ℚ))
    (cosTab_mem_any (n * (2 * j + 1)))
  refine QI.mem_of_eq h ?_
  simp only [q11ContourWeight, contourAngle, denominator, hg]
  push_cast
  ring_nf

def q11ContourRatioQ : ℚ := 1333 / 24233

theorem q11ContourRatioQ_cast : (q11ContourRatioQ : ℝ) = contourRatio := by
  norm_num [q11ContourRatioQ, contourRatio]

def q11CoeffI (n : ℕ) : QI :=
  if n = 0 then pt 0 else
    rnd (smul (1 / (n : ℚ))
      (mul (pt (1 + q11ContourRatioQ ^ n)) (q11ContourMomentI n)))

def q11LogPrimitiveI (t : ℚ) : QI :=
  rnd (smul q11ContourMassQ (li t))

def q11TermI (n : ℕ) (t : ℚ) : QI :=
  rnd (mul (q11CoeffI n) (powI (pi t) n))

def q11TermSumI (t : ℚ) : QI :=
  sumIdx 49 (fun n => q11TermI n t)

def q11NuI (t : ℚ) : QI :=
  sub (q11LogPrimitiveI t) (q11TermSumI t)

def q11NuHiF (t : ℚ) : ℚ := (q11NuI t).hi

theorem q11CoeffI_mem {n : ℕ} (hn : n < 49) :
    (q11CoeffI n).mem
      ((1 + contourRatio ^ n) * q11ExteriorContourMoment n / (n : ℝ)) := by
  by_cases h0 : n = 0
  · subst n
    simpa [q11CoeffI, q11ExteriorContourMoment] using (QI.mem_pt 0)
  · have hn48 : n ≤ 48 := by omega
    have hm := q11ContourMomentI_mem (n := n) hn48
    have hmul := QI.mem_mul (QI.mem_pt (1 + q11ContourRatioQ ^ n)) hm
    have hsmul := QI.mem_smul (1 / (n : ℚ)) hmul
    have hcast : ((q11ContourRatioQ : ℚ) : ℝ) = contourRatio := q11ContourRatioQ_cast
    convert QI.mem_rnd hsmul using 1
    · simp [q11CoeffI, q11ContourMomentI, h0]
    · push_cast
      rw [q11ContourRatioQ_cast]
      field_simp

theorem q11TermI_mem {t : ℚ} (ht : (1 / 2 : ℚ) ≤ t) (n : ℕ) (hn : n < 49) :
    (q11TermI n t).mem
      (((1 + contourRatio ^ n) * q11ExteriorContourMoment n / (n : ℝ)) *
        outsideParameter (t : ℝ) ^ n) := by
  exact QI.mem_rnd (QI.mem_mul (q11CoeffI_mem hn)
    (powI_mem (pi_mem ht) n))

theorem q11LogPrimitiveI_mem {t : ℚ} (ht : (1 / 2 : ℚ) ≤ t) :
    (q11LogPrimitiveI t).mem
      (q11ContourMass * Real.log (outsideRadius (t : ℝ))) := by
  have h := QI.mem_rnd (QI.mem_smul q11ContourMassQ (li_mem ht))
  have hm : (q11ContourMassQ : ℝ) = q11ContourMass := by
    unfold q11ContourMassQ q11ContourMass
    rw [contour_pair_mass_sum]
    norm_num [denominator]
  simpa [q11LogPrimitiveI, hm] using h

theorem q11TermSumI_mem {t : ℚ} (ht : (1 / 2 : ℚ) ≤ t) :
    (q11TermSumI t).mem
      (∑ n ∈ Finset.range 49,
        ((1 + contourRatio ^ n) * q11ExteriorContourMoment n / (n : ℝ)) *
          outsideParameter (t : ℝ) ^ n) := by
  exact QI.mem_sumIdx (fun n hn => q11TermI_mem ht n hn)

theorem q11NuHiF_mem {t : ℚ} (ht : (1 / 2 : ℚ) ≤ t) :
    (q11NuI t).lo ≤ q11ContourPotential (-((t : ℝ) : ℂ)) ∧
      q11ContourPotential (-((t : ℝ) : ℂ)) ≤ (q11NuI t).hi := by
  have hlog := q11LogPrimitiveI_mem ht
  have hsum := q11TermSumI_mem ht
  have hsub := QI.mem_sub hlog hsum
  have htR : (1 / 2 : ℝ) ≤ (t : ℝ) :=
    Li2Lean.P0.CA.Frequency.half_le_cast ht
  rw [q11ExteriorContourPotential_neg (t : ℝ) htR]
  exact hsub

theorem q11ContourPotential_neg_le_q11NuHiF {t : ℚ}
    (ht : (1 / 2 : ℚ) ≤ t) :
    q11ContourPotential (-((t : ℝ) : ℂ)) ≤ (q11NuI t).hi :=
  (q11NuHiF_mem ht).2


end
end Li2Lean.P0.Q11Data
