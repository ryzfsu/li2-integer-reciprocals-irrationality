/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.Q11PenaltyRows
import Li2Lean.P0.Q11ContourRows
import Li2Lean.P0.Q11QLogEnvelopeProducer

/-!
The q = 11 penalty-row source boundary.

`Q11PenaltyRows` deliberately stores the analytic row facts consumed by the
shifted-dual endpoint.  The finite integer tables alone do not prove these
facts.  This module splits the source into named pinned, frequency, contour,
and q-log leaves, then assembles them without hiding a conclusion-shaped
hypothesis.  A future certificate producer supplies the leaves.
-/

open MeasureTheory Set

namespace Li2Lean.P0.Q11Data

noncomputable section

open Li2Lean.F_L8
open Li2Lean.P0.CA.Receipt
open Li2Lean.P0.Q11QLogEnvelopeProducer

/-- The pinned q = 11 row packet, including its continuum lower rows and
the two non-numeric measure obligations. -/
structure Q11PinnedPenaltyRowsV13 where
  cells : List ReceiptCell
  allowance : ℚ
  chain : ExactChain cells (1 / 4) (5 / 4)
  lower : ∀ c ∈ cells, ∀ x : ℝ,
    (c.lo : ℝ) ≤ x → x ≤ (c.hi : ℝ) →
      ((c.lower : ℝ) - (allowance : ℝ)) ≤ q11Weta (x : ℂ)
  mass_le :
    penaltyMass q11EtaFloorQ allowance cells ≤ q11PinnedPenaltyUpperQ
  integrable :
    IntegrableOn
      (fun x : ℝ => max ((q11EtaFloorQ : ℝ) - q11Weta (x : ℂ)) 0)
      (Icc (1 / 4 : ℝ) (5 / 4 : ℝ))

/-- The frequency q = 11 row packet.  The half-line tail is already proved;
the packet only supplies the finite interval rows and its exact mass bound. -/
structure Q11FrequencyPenaltyRowsV13 where
  cells : List ReceiptCell
  allowance : ℚ
  chain : ExactChain cells (1 / 2) (81 / 10)
  lower : ∀ c ∈ cells, ∀ t : ℝ,
    (c.lo : ℝ) ≤ t → t ≤ (c.hi : ℝ) →
      ((c.lower : ℝ) - (allowance : ℝ)) ≤ q11Wmu t
  mass_le :
    penaltyMass q11FrequencyFloorQ allowance cells ≤
      q11FrequencyPenaltyUpperQ
  integrable :
    IntegrableOn
      (fun t : ℝ => max ((q11FrequencyFloorQ : ℝ) - q11Wmu t) 0)
      (Ici (1 / 2 : ℝ))

/-- All actual q = 11 penalty-row leaves, with the contour and q-log leaves
kept separate from the finite row packets. -/
structure Q11PenaltyRowsV13Inputs where
  pinned : Q11PinnedPenaltyRowsV13
  frequency : Q11FrequencyPenaltyRowsV13
  contour : Q11GammaContourCertificate
  qLog_lower : q11QLogLower

private theorem q11_contour_floor_of_rows
    (C : Q11GammaContourCertificate) :
    ∀ z ∈ Gamma, (q11EtaFloorQ : ℝ) ≤ q11Weta z := by
  intro z hz
  have h := q11GammaContourFloor_of_certificate C z hz
  have hfloor : ratioToReal etaFloor = (q11EtaFloorQ : ℝ) := by
    simp [ratioToReal, q11EtaFloorQ]
  rw [hfloor] at h
  simpa [q11EtaFloorQ_eq] using h

/-!
This is the sole constructor consumed by the endpoint provider.  It merely
copies the named leaves and derives the contour floor from the separate
continuous row certificate.  No finite Boolean row check is used as an
analytic inequality.
-/
def q11_penalty_rows_v13 (I : Q11PenaltyRowsV13Inputs) : Q11PenaltyRows :=
  { pinnedCells := I.pinned.cells
    pinnedAllowance := I.pinned.allowance
    pinnedChain := I.pinned.chain
    pinnedLower := I.pinned.lower
    pinned_mass_le := I.pinned.mass_le
    pinned_integrable := I.pinned.integrable
    frequencyCells := I.frequency.cells
    frequencyAllowance := I.frequency.allowance
    frequencyChain := I.frequency.chain
    frequencyLower := I.frequency.lower
    frequency_mass_le := I.frequency.mass_le
    frequency_integrable := I.frequency.integrable
    contour_lower := q11_contour_floor_of_rows I.contour
    qLog_lower := I.qLog_lower }

/-- The q-log envelope producer supplies the q-log leaf; the other leaves
remain exactly the pinned/frequency/contour obligations above. -/
def q11_penalty_rows_v13_of_qlog_envelope
    (P : Q11PinnedPenaltyRowsV13)
    (F : Q11FrequencyPenaltyRowsV13)
    (C : Q11GammaContourCertificate)
    (Q : Q11QLogEnvelopeInputs) :
    Q11PenaltyRows :=
  q11_penalty_rows_v13
    { pinned := P
      frequency := F
      contour := C
      qLog_lower := q11ActualReference_qLog_lower_of_envelope Q }

end

end Li2Lean.P0.Q11Data

#print axioms Li2Lean.P0.Q11Data.q11_penalty_rows_v13
#print axioms Li2Lean.P0.Q11Data.q11_penalty_rows_v13_of_qlog_envelope
