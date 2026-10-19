/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.Q11ContourSelfEnergy
import Li2Lean.P0.ActualReferenceQLogEnclosure

open MeasureTheory Set
open scoped BigOperators Interval ENNReal

namespace Li2Lean.P0.Q11Data

noncomputable section

open Li2Lean.P0.ConfigContourReference
open Li2Lean.P0.ConfigContourKernel
open Li2Lean.P0.CA.Contour
open Li2Lean.P0.CA.Contour.QI
open Li2Lean.P0.ActualReferenceQLogEnclosure

/-! The q = 11 self-energy uses the same Fourier construction as the literal
q = 2 certificate.  The only q-specific input is the contour mass array from
`tab:q11data` (v13 `p0-reference-data.tex`, q = 11 table). -/

def q11Wq (j : ℕ) : ℚ :=
  (contourMassUnit j : ℚ) / (denominator : ℚ)

def q11MomI (k : ℕ) : QI :=
  smul (1 - (k : ℚ) / 49)
    (sumIdx 64 (fun j =>
      smul (q11Wq j)
        (cosTab.getD ((k * (2 * j + 1)) % 128) ⟨0, 0⟩)))

theorem q11MomI_mem {k : ℕ} (hk : k ≤ 48) :
    (q11MomI k).mem (q11ContourFourierMoment k) := by
  unfold q11MomI
  have hmoment : q11ContourFourierMoment k =
      (1 - (k : ℝ) / 49) *
        ∑ j : Fin contourNodeCount, q11ContourWeight j *
          Real.cos ((k : ℝ) * contourAngle j) := by
    unfold q11ContourFourierMoment
    rw [if_pos hk]
  rw [hmoment]
  have hK : ((1 - (k : ℚ) / 49 : ℚ) : ℝ) =
      (1 - (k : ℝ) / 49 : ℝ) := by
    push_cast
    ring
  rw [← hK]
  apply QI.mem_smul
  set g : ℕ → ℝ := fun j =>
    (contourMassUnit j : ℝ) / (denominator : ℝ) *
      Real.cos (k * (Real.pi * (2 * (j : ℝ) + 1) / 64)) with hg
  have hs :
      (∑ j : Fin contourNodeCount,
        q11ContourWeight j * Real.cos ((k : ℝ) * contourAngle j)) =
        ∑ j ∈ Finset.range contourNodeCount, g j := by
    rw [← Fin.sum_univ_eq_sum_range g]
    rfl
  rw [hs]
  change (sumIdx 64 (fun j =>
    smul (q11Wq j)
      (cosTab.getD ((k * (2 * j + 1)) % 128) ⟨0, 0⟩))).mem
    (∑ j ∈ Finset.range 64, g j)
  apply QI.mem_sumIdx
  intro j hj
  have h := QI.mem_smul (q11Wq j)
    (cosTab_mem_any (k * (2 * j + 1)))
  refine QI.mem_of_eq h ?_
  simp only [hg, q11Wq, q11ContourWeight, contourAngle, denominator]
  push_cast
  ring_nf

def q11BComp (n : ℕ) : QI :=
  rnd (smul ((1 + (1333 / 24233 : ℚ) ^ (n + 1)) / (n + 1 : ℚ))
    (rnd (q11MomI (n + 1))))

theorem q11BComp_mem {n : ℕ} (hn : n < 48) :
    (q11BComp n).mem
      ((1 + contourRatio ^ (n + 1)) *
        q11ContourFourierMoment (n + 1) / (n + 1 : ℝ)) := by
  have h := mem_rnd (mem_smul
    ((1 + (1333 / 24233 : ℚ) ^ (n + 1)) / (n + 1 : ℚ))
    (mem_rnd (q11MomI_mem (k := n + 1) (by omega))))
  unfold q11BComp
  convert h using 1
  · unfold contourRatio
    push_cast
    ring

theorem q11EnergyFactor_eq (n : ℕ) :
    (energyFactor n : ℝ) *
        ((1 + contourRatio ^ (n + 1)) *
          q11ContourFourierMoment (n + 1) / (n + 1 : ℝ)) ^ 2 =
      (1 + contourRatio ^ (n + 1)) *
        q11ContourFourierMoment (n + 1) ^ 2 / (n + 1 : ℝ) := by
  have hnp : (0 : ℝ) < n + 1 := by positivity
  have hq : 0 ≤ contourRatio ^ (n + 1) :=
    pow_nonneg contourRatio_nonneg _
  have hqp : (0 : ℝ) < 1 + contourRatio ^ (n + 1) := by linarith
  unfold energyFactor
  push_cast
  change ((n + 1 : ℝ) / (1 + contourRatio ^ (n + 1))) *
    ((1 + contourRatio ^ (n + 1)) *
      q11ContourFourierMoment (n + 1) / (n + 1 : ℝ)) ^ 2 = _
  field_simp [hnp.ne', hqp.ne']

def q11SelfEnergyTermI (n : ℕ) : QI :=
  rnd (smul (energyFactor n) (mul (q11BComp n) (q11BComp n)))

theorem q11SelfEnergyTermI_mem {n : ℕ} (hn : n < 48) :
    (q11SelfEnergyTermI n).mem
      ((1 + contourRatio ^ (n + 1)) *
        q11ContourFourierMoment (n + 1) ^ 2 / (n + 1 : ℝ)) := by
  rw [← q11EnergyFactor_eq]
  unfold q11SelfEnergyTermI
  have hb := q11BComp_mem hn
  simpa only [pow_two] using
    QI.mem_rnd (QI.mem_smul (energyFactor n) (QI.mem_mul hb hb))

def q11ContourMassQ : ℚ :=
  (2 * 676422605576 : ℚ) / (3000000000000 : ℚ)

def q11SelfEnergyI : QI :=
  sub (smul (q11ContourMassQ ^ 2) logScaleI)
    (sumIdx 48 q11SelfEnergyTermI)

theorem q11ContourMassQ_eq :
    (q11ContourMassQ : ℝ) = q11ContourMass := by
  unfold q11ContourMassQ q11ContourMass
  rw [contour_pair_mass_sum]
  norm_num [denominator]

theorem q11SelfEnergyI_mem :
    q11SelfEnergyI.mem q11ContourSelfEnergyFourier := by
  have hsum := mem_sumIdx (fun n hn => q11SelfEnergyTermI_mem hn)
  have hmass := QI.mem_smul (q11ContourMassQ ^ 2) logScaleI_mem
  unfold q11SelfEnergyI q11ContourSelfEnergyFourier
  have hmass_eq : ((q11ContourMassQ ^ 2 : ℚ) : ℝ) =
      q11ContourMass ^ 2 := by
    norm_num [Rat.cast_pow, q11ContourMassQ_eq]
  rw [hmass_eq] at hmass
  exact mem_sub hmass hsum

def lowerContourContour : IntRatio :=
  ⟨q11SelfEnergyI.lo.num, q11SelfEnergyI.lo.den⟩

theorem lowerContourContour_den_pos : 0 < lowerContourContour.den :=
  q11SelfEnergyI.lo.pos

theorem q11Eνν_lower :
    ratioToReal lowerContourContour ≤ q11Eνν := by
  have hratio : ratioToReal lowerContourContour =
      (q11SelfEnergyI.lo : ℝ) := by
    change (q11SelfEnergyI.lo.num : ℝ) /
        (q11SelfEnergyI.lo.den : ℝ) = (q11SelfEnergyI.lo : ℝ)
    exact_mod_cast (Rat.num_div_den q11SelfEnergyI.lo)
  rw [q11Eνν_eq_fourier]
  rw [hratio]
  exact q11SelfEnergyI_mem.1

end

end Li2Lean.P0.Q11Data
