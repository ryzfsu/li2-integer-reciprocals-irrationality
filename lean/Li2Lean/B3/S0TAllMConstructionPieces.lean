/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Mathlib
import Li2Lean.B3.ReferencePackage
import Li2Lean.B3.SmoothedEnergy

namespace Li2Lean.B3

noncomputable section

open MeasureTheory
open scoped BigOperators

/-- The off-diagonal discrete self-energy of one empirical block after the
paper's circle displacement. -/
def p4C6DiscreteSelf {d : ℕ} (u : Fin d → ℂ) (m : ℕ) : ℝ :=
  ∑ i : Fin d, ∑ j : Fin d,
    if i = j then 0 else
      v13LogKernel (translatedAtomCenter (u i) m)
        (translatedAtomCenter (u j) m)

/-- The self-energy of the corresponding circle-smoothed empirical measure. -/
def p4C6SmoothedSelf {d : ℕ} (u : Fin d → ℂ) (m : ℕ) : ℝ :=
  ∫ p : ℂ × ℂ, v13LogKernel p.1 p.2
    ∂((translatedEmpiricalMeasure u m).prod
      (translatedEmpiricalMeasure u m))

theorem p4_c6_self_energy_unnormalised
    {d m : ℕ} (u : Fin d → ℂ) (hm : 0 < m)
    (hcenter : ∀ i j, i ≠ j →
      translatedAtomCenter (u i) m ≠
        translatedAtomCenter (u j) m) :
    p4C6DiscreteSelf u m ≤
      (m : ℝ) ^ 2 * p4C6SmoothedSelf u m +
        2 * (d : ℝ) * Real.log (m : ℝ) := by
  unfold p4C6DiscreteSelf p4C6SmoothedSelf
  have hmR : (0 : ℝ) < (m : ℝ) := by
    exact_mod_cast hm
  have hmR0 : (m : ℝ) ≠ 0 := ne_of_gt hmR
  have heps : 1 / smoothingEpsilon m = (m : ℝ) ^ 2 := by
    rw [smoothingEpsilon_eq_inv_sq]
    field_simp [hmR0]
  have hlog : Real.log (1 / smoothingEpsilon m) =
      2 * Real.log (m : ℝ) := by
    rw [heps, Real.log_pow]
    norm_num
  have h :=
    translatedEmpiricalMeasure_v13_energy_transfer
      u hm hcenter
  rw [hlog] at h
  have h' :
      (∑ i : Fin d, ∑ j : Fin d,
        if i = j then 0 else
          v13LogKernel (translatedAtomCenter (u i) m)
            (translatedAtomCenter (u j) m)) / (m : ℝ) ^ 2 ≤
      (∫ p : ℂ × ℂ, v13LogKernel p.1 p.2
        ∂((translatedEmpiricalMeasure u m).prod
          (translatedEmpiricalMeasure u m))) +
        (2 * (d : ℝ) / (m : ℝ) ^ 2) * Real.log (m : ℝ) := by
    convert h using 1 <;> ring
  calc
    (∑ i : Fin d, ∑ j : Fin d,
        if i = j then 0 else
          v13LogKernel (translatedAtomCenter (u i) m)
            (translatedAtomCenter (u j) m)) ≤
        ((∫ p : ℂ × ℂ, v13LogKernel p.1 p.2
          ∂((translatedEmpiricalMeasure u m).prod
            (translatedEmpiricalMeasure u m))) +
          (2 * (d : ℝ) / (m : ℝ) ^ 2) *
            Real.log (m : ℝ)) * (m : ℝ) ^ 2 :=
      (div_le_iff₀ (pow_pos hmR 2)).mp h'
    _ = (m : ℝ) ^ 2 *
          (∫ p : ℂ × ℂ, v13LogKernel p.1 p.2
            ∂((translatedEmpiricalMeasure u m).prod
              (translatedEmpiricalMeasure u m))) +
        2 * (d : ℝ) * Real.log (m : ℝ) := by
      field_simp [hmR0] <;> ring

theorem p4_c6_three_self_energies
    {n : ℕ} (hn : 0 < n)
    (x : Fin (4 * n) → ℂ)
    (v : Fin (5 * n) → ℂ)
    (z : Fin (4 * n) → ℂ)
    (hx : ∀ i j, i ≠ j →
      translatedAtomCenter (x i) (4 * n) ≠
        translatedAtomCenter (x j) (4 * n))
    (hv : ∀ i j, i ≠ j →
      translatedAtomCenter (v i) (4 * n) ≠
        translatedAtomCenter (v j) (4 * n))
    (hz : ∀ i j, i ≠ j →
      translatedAtomCenter (z i) (4 * n) ≠
        translatedAtomCenter (z j) (4 * n)) :
    p4C6DiscreteSelf x (4 * n) +
        p4C6DiscreteSelf v (4 * n) +
        p4C6DiscreteSelf z (4 * n) ≤
      ((4 * n : ℕ) : ℝ) ^ 2 *
        (p4C6SmoothedSelf x (4 * n) +
          p4C6SmoothedSelf v (4 * n) +
          p4C6SmoothedSelf z (4 * n)) +
        (13 / 2 : ℝ) * ((4 * n : ℕ) : ℝ) *
          Real.log ((4 * n : ℕ) : ℝ) := by
  have hm : 0 < 4 * n := by omega
  have hX := p4_c6_self_energy_unnormalised x hm hx
  have hV := p4_c6_self_energy_unnormalised v hm hv
  have hZ := p4_c6_self_energy_unnormalised z hm hz
  calc
    p4C6DiscreteSelf x (4 * n) +
        p4C6DiscreteSelf v (4 * n) +
        p4C6DiscreteSelf z (4 * n) ≤
      (((4 * n : ℕ) : ℝ) ^ 2 *
          p4C6SmoothedSelf x (4 * n) +
        2 * ((4 * n : ℕ) : ℝ) *
          Real.log ((4 * n : ℕ) : ℝ)) +
      (((4 * n : ℕ) : ℝ) ^ 2 *
          p4C6SmoothedSelf v (4 * n) +
        2 * ((5 * n : ℕ) : ℝ) *
          Real.log ((4 * n : ℕ) : ℝ)) +
      (((4 * n : ℕ) : ℝ) ^ 2 *
          p4C6SmoothedSelf z (4 * n) +
        2 * ((4 * n : ℕ) : ℝ) *
          Real.log ((4 * n : ℕ) : ℝ)) :=
      add_le_add (add_le_add hX hV) hZ
    _ = ((4 * n : ℕ) : ℝ) ^ 2 *
          (p4C6SmoothedSelf x (4 * n) +
            p4C6SmoothedSelf v (4 * n) +
            p4C6SmoothedSelf z (4 * n)) +
        (13 / 2 : ℝ) * ((4 * n : ℕ) : ℝ) *
          Real.log ((4 * n : ℕ) : ℝ) := by
      push_cast
      ring

/-- The package's strict energy lower bound yields the negative-energy bound
used in the C4 comparison. -/
theorem p4_reference_negative_energy_bound
    {q : ℕ} {hq : SignedVBaseRange q}
    (P : VReferencePackage q hq) :
    -V.signedVQuadratic P.measure ≤
      -(((vQlow q : ℚ) : ℝ)) := by
  exact le_of_lt (neg_lt_neg P.facts.energy_lower)

theorem p4_c7_positive_one_body_scalar
    {m : ℕ} (hm : 64 ≤ m) :
    (m : ℝ) ^ 2 *
        ((17 / 2 : ℝ) * smoothingEpsilon m ^ 2 /
          (1 / 250 : ℝ) ^ 2) < 130 := by
  have hmR : (64 : ℝ) ≤ (m : ℝ) := by
    exact_mod_cast hm
  have hmpos : 0 < (m : ℝ) := by
    linarith
  have hmsq : (4096 : ℝ) ≤ (m : ℝ) ^ 2 := by
    nlinarith [sq_nonneg ((m : ℝ) - 64)]
  have hsqpos : 0 < (m : ℝ) ^ 2 := by
    positivity
  have hbound : (531250 : ℝ) / (m : ℝ) ^ 2 < 130 := by
    apply (div_lt_iff₀ hsqpos).2
    nlinarith
  calc
    (m : ℝ) ^ 2 *
        ((17 / 2 : ℝ) * smoothingEpsilon m ^ 2 /
          (1 / 250 : ℝ) ^ 2) =
        (531250 : ℝ) / (m : ℝ) ^ 2 := by
      rw [smoothingEpsilon_eq_inv_sq]
      field_simp [ne_of_gt hmpos] <;> ring
    _ < 130 := hbound

end

end Li2Lean.B3
