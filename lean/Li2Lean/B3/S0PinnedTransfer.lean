import Li2Lean.B3.S0ActualInterface

/-!
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Pinned signed-V S0 transfer carrier

This is the construction-bound successor to the older S0 transfer record.
The v13 maximum point is one fixed phiMax for a base, not a new value for
each index. The logarithmic input is recorded before multiplying by the S0
prefactor; the adapter below derives the multiplicative/logarithmic consumer
from that decomposed field.

Sources: v13 v-analytic.tex:106-145,493-631.
-/

namespace Li2Lean.B3

noncomputable section

/-- The fixed S0 prefactor for m = 4 n and L = 5 n. -/
def s0PinnedPrefactor (q n : ℕ) : ℝ :=
  (q : ℝ) ^ s0Exponent (4 * n) /
    (((Nat.factorial (4 * n) : ℕ) : ℝ) ^ 2 *
      ((Nat.factorial (5 * n) : ℕ) : ℝ))

/-- The v13 transfer budget left for the fixed maximum point after the
prefactor and T_q^(4n) have been separated. -/
def s0PinnedPhiBudget (q : ℕ) (alpha sigma Tq phiMax : ℝ) (n : ℕ) : ℝ :=
  -alpha * ((4 * n : ℕ) : ℝ) ^ 2 +
    (13 / 2 : ℝ) * ((4 * n : ℕ) : ℝ) *
      Real.log ((4 * n : ℕ) : ℝ) +
    3 * sigma *
      (1 + Real.log (((4 * n : ℕ) : ℝ) ^ 2 / 3)) +
    (2 * denominatorTransferCost q + 7 + 130) +
      ((4 * n : ℕ) : ℝ) -
    Real.log (s0PinnedPrefactor q n * Tq ^ (4 * n))

/-- Decomposed logarithmic transfer for the actual v13 contour value.
The field is a bound for the fixed maximum point, while the prefactor and
path power are handled by the adapter theorem. -/
structure VContourS0PinnedLogTransfer
    (q : ℕ) (alpha sigma Tq phiMax : ℝ) : Prop where
  phi_log_bound : ∀ n : ℕ, 64 ≤ 4 * n →
    Real.log |phiMax| ≤ s0PinnedPhiBudget q alpha sigma Tq phiMax n

/-- Construction-bound S0 data with one fixed maximum point. -/
structure VContourS0PinnedTransferData
    (q : ℕ) (alpha sigma : ℝ) : Type where
  q_ge_two : 2 ≤ q
  q_le_seven : q ≤ 7
  Tq : ℝ
  Tq_pos : 0 < Tq
  phiMax : ℝ
  phiMax_pos : 0 < phiMax
  s0_data : ∀ n : ℕ, VContourS0Data q n Tq phiMax
  log_transfer :
    VContourS0PinnedLogTransfer q alpha sigma Tq phiMax

theorem s0PinnedPrefactor_pos {q n : ℕ} (hq : 2 ≤ q) :
    0 < s0PinnedPrefactor q n := by
  unfold s0PinnedPrefactor
  have hq0 : 0 < (q : ℝ) := by exact_mod_cast (show 0 < q by omega)
  positivity

theorem s0MagnitudeRhs_eq_pinned
    {q n : ℕ} {Tq phiMax : ℝ} :
    s0MagnitudeRhs q (4 * n) (5 * n) Tq phiMax =
      s0PinnedPrefactor q n * Tq ^ (4 * n) * |phiMax| := by
  rfl

theorem s0_log_rhs_le_of_pinned_transfer
    {q : ℕ} {alpha sigma : ℝ}
    (H : VContourS0PinnedTransferData q alpha sigma)
    {n : ℕ} (hn : 64 ≤ 4 * n) :
    Real.log (s0MagnitudeRhs q (4 * n) (5 * n) H.Tq H.phiMax) ≤
      -alpha * ((4 * n : ℕ) : ℝ) ^ 2 +
        (13 / 2 : ℝ) * ((4 * n : ℕ) : ℝ) *
          Real.log ((4 * n : ℕ) : ℝ) +
        3 * sigma *
          (1 + Real.log (((4 * n : ℕ) : ℝ) ^ 2 / 3)) +
        (2 * denominatorTransferCost q + 7 + 130) +
          ((4 * n : ℕ) : ℝ) := by
  have hpref : 0 < s0PinnedPrefactor q n := s0PinnedPrefactor_pos H.q_ge_two
  have hpow : 0 < H.Tq ^ (4 * n) := pow_pos H.Tq_pos _
  have hphi : 0 < |H.phiMax| := abs_pos.mpr H.phiMax_pos.ne'
  have hfirst : s0PinnedPrefactor q n * H.Tq ^ (4 * n) ≠ 0 :=
    (mul_pos hpref hpow).ne'
  rw [s0MagnitudeRhs_eq_pinned]
  rw [Real.log_mul hfirst hphi.ne']
  have hbound := H.log_transfer.phi_log_bound n hn
  unfold s0PinnedPhiBudget at hbound
  linarith

theorem vRawPrebound_of_pinned_transfer
    {q : ℕ} {alpha sigma : ℝ}
    (H : VContourS0PinnedTransferData q alpha sigma) :
    VRawPrebound q alpha sigma := by
  intro n hn hreal
  have D := H.s0_data n
  have hcomplex : vContourActualGValue q n ≠ 0 := by
    rw [vContourActualGValue_eq_vRealPoly]
    exact Complex.ofReal_ne_zero.mpr hreal
  have hRhs : 0 < s0MagnitudeRhs q (4 * n) (5 * n) H.Tq H.phiMax := by
    rw [s0MagnitudeRhs_eq_pinned]
    exact mul_pos (mul_pos (s0PinnedPrefactor_pos H.q_ge_two)
      (pow_pos H.Tq_pos _)) (abs_pos.mpr H.phiMax_pos.ne')
  have hmag := vContourS0Magnitude_of_data D
  have hlog := Real.log_le_log (norm_pos_iff.mpr hcomplex) hmag
  rw [vContourActualGValue_eq_vRealPoly] at hlog
  rw [Complex.norm_real, Real.norm_eq_abs] at hlog
  exact hlog.trans (s0_log_rhs_le_of_pinned_transfer H hn)

theorem vAllMPreboundProducer_of_pinned_transfer
    {q : ℕ} {alpha sigma : ℝ}
    (H : VContourS0PinnedTransferData q alpha sigma)
    (hSigma : ∃ Ax Av Az : ℝ,
      0 ≤ Ax ∧ 0 ≤ Av ∧ 0 ≤ Az ∧
        sigma = sigmaBudget Ax Av Az) :
    VAllMPreboundProducer q alpha sigma :=
  producer_of_rawPrebound H.q_ge_two H.q_le_seven hSigma
    (vRawPrebound_of_pinned_transfer H)

/- The frozen a = 2 route is unchanged. -/
theorem vRawPrebound_of_pinned_transfer_q2
    {alpha sigma : ℝ} (H : VContourS0PinnedTransferData 2 alpha sigma) :
    VRawPrebound 2 alpha sigma :=
  vRawPrebound_of_pinned_transfer H

end
end Li2Lean.B3

#print axioms Li2Lean.B3.s0_log_rhs_le_of_pinned_transfer
#print axioms Li2Lean.B3.vRawPrebound_of_pinned_transfer
