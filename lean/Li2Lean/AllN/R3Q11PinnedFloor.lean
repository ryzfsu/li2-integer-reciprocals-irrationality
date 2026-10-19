/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.Q11PenaltyRows
import Li2Lean.P0.CA.Frequency.Arith

/-!
# A complete pinned floor for the printed q = 11 reference

The q = 2 frequency checker supplies certified hulls of the primitive
`F(x) = x (log |x| - 1)`.  Here the exact q = 11 masses produce fourteen
merged terms.  Sixteen closed intervals and four coarse contour radii
certify the whole pinned support.  No Fourier approximation is needed.
-/

open MeasureTheory Set Filter

namespace Li2Lean.P0.Q11Data

noncomputable section

open Li2Lean.LogSegment ConfigSegment CA.Frequency

def r3Q11PinnedTerms : List (ℚ × ℚ) :=
  [(46874999993 / 46875000000, -1 / 4),
   (46874999999 / 46875000000, -5 / 4),
   (2, 0), (-1, -2),
   (-41590859209 / 187500000000, 1 / 2),
   (7 / 46875000000, -3 / 8),
   (-4308106253 / 7500000000, -1 / 2),
   (-8269706517 / 15625000000, -5 / 8),
   (-53915057321 / 187500000000, -3 / 4),
   (-10134102379 / 31250000000, -7 / 8),
   (-3333824617 / 11718750000, -1),
   (-841233788423 / 1500000000000, 3 / 2),
   (-159675901069 / 750000000000, 5 / 2),
   (-2229178589 / 500000000000, 7 / 2)]

def r3TermsVal (l : List (ℚ × ℚ)) (x : ℝ) : ℝ :=
  (l.map (fun p => (p.1 : ℝ) * primitive (x + (p.2 : ℝ)))).sum

theorem r3_q11Weta_terms (x : ℝ) :
    q11Weta (x : ℂ) = r3TermsVal r3Q11PinnedTerms x -
      x * Real.log 11 - 1 / 2 - Real.log 2 / 2 -
      2 * q11ContourPotential (x : ℂ) := by
  have hp : q11PinnedComplexPotential (x : ℂ) = q11PinnedRealPotential x := by
    simp only [q11PinnedComplexPotential, q11PinnedRealPotential,
      ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  have hf : q11ReflectedFrequencyPotential (x : ℂ) =
      q11FrequencyPotential (-x) := by
    unfold q11ReflectedFrequencyPotential q11FrequencyPotential
    apply integral_congr_ae
    filter_upwards [] with y
    rw [← Complex.ofReal_add, Complex.norm_real, Real.norm_eq_abs,
      show -x - y = -(x + y) by ring, abs_neg]
  have hneg (e : ℝ) : primitive (-x - e) = -primitive (x + e) := by
    rw [show -x - e = -(x + e) by ring, ConfigPinnedTail.primitive_neg]
  have hlog : Real.log 2 + q11Lambda = Real.log 11 := by
    unfold q11Lambda
    rw [← Real.log_mul (by norm_num : (2 : ℝ) ≠ 0)
      (by norm_num : (11 / 2 : ℝ) ≠ 0)]
    norm_num
  have hhalf : Real.log (1 / 2 : ℝ) = -Real.log 2 := by
    rw [one_div, Real.log_inv]
  simp only [q11Weta, q11Phi, q11ActualReference, q11EtaReferencePotential,
    hp, hf, Complex.ofReal_re, q11PinnedRealPotential,
    q11PinnedPotential_eq_endpoints, q11FrequencyPotential_eq_endpoints,
    A0_ofReal_eq_endpoints, phi_ofReal_eq_endpoints]
  simp_rw [hneg]
  norm_num [Finset.sum_range_succ, q11IntervalDensity, q11MassUnitReal,
    pinnedMassUnits, frequencyMassUnits, denominator,
    q11PinnedEdgeReal, q11FrequencyEdgeReal, pinnedEdge, frequencyEdge,
    pinnedEdge32Units, frequencyEdge2Units, r3TermsVal, r3Q11PinnedTerms]
  simp only [hhalf, sub_eq_add_neg]
  nlinarith [congrArg (fun y : ℝ => x * y) hlog]

theorem r3_norm_sub_center_le {z : ℂ} (hz : z ∈ Gamma) :
    ‖z - (center : ℂ)‖ ≤ semiMajor := by
  rcases hz with ⟨u, rfl⟩
  apply (sq_le_sq₀ (norm_nonneg _) (by norm_num [semiMajor])).mp
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp only [gammaPoint, Complex.sub_re, Complex.sub_im, Complex.add_re,
    Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, zero_mul, one_mul,
    mul_zero, add_zero, zero_add, sub_zero, mul_one]
  have hs := Real.sin_sq_add_cos_sq u
  have hsin := sq_nonneg (Real.sin u)
  norm_num [semiMajor, semiMinor]
  nlinarith

def r3Q11ContourMassQ : ℚ := 84552825697 / 187500000000

theorem r3_q11ContourPotential_le_radius {x R : ℝ}
    (hR : 1 ≤ R) (hbound : ∀ z ∈ Gamma, ‖(x : ℂ) - z‖ ≤ R) :
    q11ContourPotential (x : ℂ) ≤
      (r3Q11ContourMassQ : ℝ) * Real.log R := by
  rw [q11ContourPotential_eq_integral]
  by_cases hInt : Integrable (fun z : ℂ => Real.log ‖(x : ℂ) - z‖)
      q11ContourReferenceMeasure
  · have hmono := integral_mono_ae hInt
      (integrable_const (μ := q11ContourReferenceMeasure) (Real.log R))
      (q11ContourReferenceMeasure_ae_Gamma.mono (fun z hz => by
        change Real.log ‖(x : ℂ) - z‖ ≤ Real.log R
        by_cases hzero : ‖(x : ℂ) - z‖ = 0
        · rw [hzero, Real.log_zero]
          exact Real.log_nonneg hR
        · exact Real.log_le_log (lt_of_le_of_ne (norm_nonneg _) (Ne.symm hzero))
            (hbound z hz)))
    calc
      _ ≤ ∫ _ : ℂ, Real.log R ∂q11ContourReferenceMeasure := hmono
      _ = (r3Q11ContourMassQ : ℝ) * Real.log R := by
        rw [integral_const, Measure.real, q11ContourReferenceMeasure_univ]
        norm_num [contour_pair_mass_sum, denominator, r3Q11ContourMassQ,
          smul_eq_mul]
  · rw [integral_undef hInt]
    exact mul_nonneg (by norm_num [r3Q11ContourMassQ]) (Real.log_nonneg hR)

def r3PinnedLo (j : ℕ) : ℚ := 1 / 4 + (j : ℚ) / 16
def r3PinnedHi (j : ℕ) : ℚ := 1 / 4 + ((j + 1 : ℕ) : ℚ) / 16
def r3PinnedRadius (j : ℕ) : ℚ :=
  if j < 4 then 9 / 4 else if j < 8 then 2 else if j < 12 then 7 / 4 else 3 / 2

theorem r3_pinned_radius {j : ℕ} (hj : j < 16) {x : ℝ}
    (hlo : (r3PinnedLo j : ℝ) ≤ x) (hhi : x ≤ (r3PinnedHi j : ℝ)) :
    (1 : ℝ) ≤ (r3PinnedRadius j : ℝ) ∧
      ∀ z ∈ Gamma, ‖(x : ℂ) - z‖ ≤ (r3PinnedRadius j : ℝ) := by
  have hgeom : |x - center| + semiMajor ≤ (r3PinnedRadius j : ℝ) := by
    norm_num [r3PinnedLo, r3PinnedHi] at hlo hhi
    interval_cases j <;>
      norm_num [r3PinnedRadius, center, semiMajor, abs_le] at * <;>
      cases le_total 0 (x - 11281 / 10000) with
      | inl hp => rw [abs_of_nonneg hp]; linarith
      | inr hn => rw [abs_of_nonpos hn]; linarith
  constructor
  · interval_cases j <;> norm_num [r3PinnedRadius]
  · intro z hz
    calc
      ‖(x : ℂ) - z‖ ≤ ‖(x : ℂ) - (center : ℂ)‖ + ‖(center : ℂ) - z‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ |x - center| + semiMajor := by
        rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
          norm_sub_rev (center : ℂ) z]
        exact add_le_add (le_refl _) (r3_norm_sub_center_le hz)
      _ ≤ (r3PinnedRadius j : ℝ) := hgeom

def r3TermLower (a b : ℚ) (p : ℚ × ℚ) : ℚ :=
  if 0 ≤ p.1 then p.1 * hullLo (a + p.2) (b + p.2)
  else p.1 * hullHi (a + p.2) (b + p.2)

def r3TermsLower (a b : ℚ) (l : List (ℚ × ℚ)) : ℚ :=
  (l.map (r3TermLower a b)).sum

theorem r3_term_lower_le {a b : ℚ} {x : ℝ}
    (ha : (a : ℝ) ≤ x) (hb : x ≤ (b : ℝ)) (p : ℚ × ℚ) :
    (r3TermLower a b p : ℝ) ≤ (p.1 : ℝ) * primitive (x + (p.2 : ℝ)) := by
  have hlo : ((a + p.2 : ℚ) : ℝ) ≤ x + (p.2 : ℝ) := by
    push_cast
    linarith
  have hhi : x + (p.2 : ℝ) ≤ ((b + p.2 : ℚ) : ℝ) := by
    push_cast
    linarith
  unfold r3TermLower
  split_ifs with hp
  · push_cast
    exact mul_le_mul_of_nonneg_left (hullLo_le hlo hhi) (by exact_mod_cast hp)
  · push_cast
    exact mul_le_mul_of_nonpos_left (le_hullHi hlo hhi)
      (by exact_mod_cast (le_of_not_ge hp))

theorem r3_terms_lower_le {a b : ℚ} {x : ℝ}
    (ha : (a : ℝ) ≤ x) (hb : x ≤ (b : ℝ)) (l : List (ℚ × ℚ)) :
    (r3TermsLower a b l : ℝ) ≤ r3TermsVal l x := by
  induction l with
  | nil => simp [r3TermsLower, r3TermsVal]
  | cons p ps ih =>
    simp only [r3TermsLower, r3TermsVal, List.map_cons, List.sum_cons,
      Rat.cast_add] at ih ⊢
    exact add_le_add (r3_term_lower_le ha hb p) ih

def r3PinnedLower (j : ℕ) : ℚ :=
  r3TermsLower (r3PinnedLo j) (r3PinnedHi j) r3Q11PinnedTerms -
    r3PinnedHi j * (logBnd 11).2 - 1 / 2 - l2hi / 2 -
    2 * r3Q11ContourMassQ * (logBnd (r3PinnedRadius j)).2

theorem r3_pinned_lower_le {j : ℕ} (hj : j < 16) {x : ℝ}
    (hlo : (r3PinnedLo j : ℝ) ≤ x) (hhi : x ≤ (r3PinnedHi j : ℝ)) :
    (r3PinnedLower j : ℝ) ≤ q11Weta (x : ℂ) := by
  have hr := r3_pinned_radius hj hlo hhi
  have hcont := r3_q11ContourPotential_le_radius hr.1 hr.2
  have ht := r3_terms_lower_le hlo hhi r3Q11PinnedTerms
  have hl11 := (logBnd_sound (by norm_num : (0 : ℚ) < 11)).2
  norm_num only [Rat.cast_ofNat] at hl11
  have hlr := (logBnd_sound (show (0 : ℚ) < r3PinnedRadius j by
    interval_cases j <;> norm_num [r3PinnedRadius])).2
  have hlog11 : (0 : ℝ) ≤ Real.log 11 := Real.log_nonneg (by norm_num)
  have hhi0 : (0 : ℝ) ≤ (r3PinnedHi j : ℝ) := by
    norm_num [r3PinnedHi]
    positivity
  have hlin : x * Real.log 11 ≤
      (r3PinnedHi j : ℝ) * ((logBnd 11).2 : ℝ) :=
    (mul_le_mul_of_nonneg_right hhi hlog11).trans
      (mul_le_mul_of_nonneg_left hl11 hhi0)
  have hc := mul_le_mul_of_nonneg_left hlr
    (by norm_num [r3Q11ContourMassQ] : (0 : ℝ) ≤ r3Q11ContourMassQ)
  rw [r3_q11Weta_terms]
  unfold r3PinnedLower
  push_cast
  linarith [le_l2hi]

/-- Exact rational replay of all sixteen continuum hull bounds. -/
theorem r3_pinned_all_check :
    (List.range 16).all (fun j =>
      decide ((-3359 / 500 : ℚ) ≤ r3PinnedLower j)) = true := by
  set_option maxRecDepth 100000 in
    decide +kernel

/-- A pointwise q = 11 pinned floor stronger than the required penalty cap. -/
theorem r3_q11_pinned_floor {x : ℝ}
    (hx : x ∈ Icc (1 / 4 : ℝ) (5 / 4 : ℝ)) :
    (-3359 / 500 : ℝ) ≤ q11Weta (x : ℂ) := by
  let j : ℕ := min ⌊16 * (x - 1 / 4)⌋₊ 15
  have hj : j < 16 := by dsimp [j]; omega
  have hjlo : (j : ℝ) ≤ 16 * (x - 1 / 4) := by
    have hmin : j ≤ ⌊16 * (x - 1 / 4)⌋₊ := Nat.min_le_left _ _
    have hminR : (j : ℝ) ≤ (⌊16 * (x - 1 / 4)⌋₊ : ℝ) := by exact_mod_cast hmin
    exact hminR.trans (Nat.floor_le (by nlinarith [hx.1]))
  have hjhi : 16 * (x - 1 / 4) ≤ (j : ℝ) + 1 := by
    by_cases hs : ⌊16 * (x - 1 / 4)⌋₊ ≤ 15
    · rw [show j = ⌊16 * (x - 1 / 4)⌋₊ from Nat.min_eq_left hs]
      exact (Nat.lt_floor_add_one _).le
    · rw [show j = 15 from Nat.min_eq_right (by omega)]
      norm_num
      linarith [hx.2]
  have hlo : (r3PinnedLo j : ℝ) ≤ x := by
    norm_num [r3PinnedLo]
    linarith
  have hhi : x ≤ (r3PinnedHi j : ℝ) := by
    norm_num [r3PinnedHi]
    linarith
  have hcheck := List.all_eq_true.mp r3_pinned_all_check j (List.mem_range.mpr hj)
  have hnum : (-3359 / 500 : ℚ) ≤ r3PinnedLower j := of_decide_eq_true hcheck
  have hnumR : (-3359 / 500 : ℝ) ≤ (r3PinnedLower j : ℝ) := by exact_mod_cast hnum
  exact hnumR.trans (r3_pinned_lower_le hj hlo hhi)

/-- The literal q = 11 pinned positive-part penalty is zero. -/
theorem r3_q11_pinned_penalty_eq_zero :
    (∫ x in Icc (1 / 4 : ℝ) (5 / 4 : ℝ),
      max ((q11EtaFloorQ : ℝ) - q11Weta (x : ℂ)) 0) = 0 := by
  apply integral_eq_zero_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
  apply max_eq_right
  apply sub_nonpos.mpr
  have h := r3_q11_pinned_floor hx
  simpa [q11EtaFloorQ_eq, neg_div] using h

theorem r3_q11_pinned_penalty_le :
    (∫ x in Icc (1 / 4 : ℝ) (5 / 4 : ℝ),
      max ((q11EtaFloorQ : ℝ) - q11Weta (x : ℂ)) 0) ≤
        (1 / 1000000 : ℝ) := by
  rw [r3_q11_pinned_penalty_eq_zero]
  norm_num

end

end Li2Lean.P0.Q11Data

#print axioms Li2Lean.P0.Q11Data.r3_q11_pinned_floor
#print axioms Li2Lean.P0.Q11Data.r3_q11_pinned_penalty_eq_zero
#print axioms Li2Lean.P0.Q11Data.r3_q11_pinned_penalty_le
