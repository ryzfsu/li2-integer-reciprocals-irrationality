/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Mathlib

namespace Li2Lean
namespace V
namespace Q7Reference

/-!
The q = 7 reference-data contract from v13.  The source rows are deliberately
represented by a payload that a later importer must fill and check.  The
header constants and directed thresholds below are the printed v13 data; no
theorem here claims that an unchecked payload has those properties.

Source ledger:

* `v-reference-data.tex:1-11,363-430`: scales, q=7 chain headers and rows;
* `v-analytic.tex:337-408,410-491`: field thresholds, energy endpoint and
  smoothing transfer constants.
-/

inductive ChainKind
  | x
  | v
  | z
  deriving DecidableEq, Repr

structure ChainHeader where
  q : Nat
  kind : ChainKind
  rowCount : Nat
  startUnits : Int
  correctionIndex : Nat
  correctionNumerator : Int
  sourceFirstLine : Nat
  sourceLastLine : Nat
  deriving DecidableEq, Repr

/-- v13 `v-reference-data.tex:363-374`, q=7 x chain. -/
def q7XHeader : ChainHeader :=
  { q := 7
    kind := .x
    rowCount := 39
    startUnits := 3349364905389
    correctionIndex := 1
    correctionNumerator := 94611
    sourceFirstLine := 363
    sourceLastLine := 374 }

/-- v13 `v-reference-data.tex:375-388`, q=7 v chain. -/
def q7VHeader : ChainHeader :=
  { q := 7
    kind := .v
    rowCount := 47
    startUnits := 480367989919
    correctionIndex := 1
    correctionNumerator := 10081
    sourceFirstLine := 375
    sourceLastLine := 388 }

/-- v13 `v-reference-data.tex:389-406`, q=7 negative-real z chain. -/
def q7ZHeader : ChainHeader :=
  { q := 7
    kind := .z
    rowCount := 62
    startUnits := -350000000000000
    correctionIndex := 0
    correctionNumerator := 0
    sourceFirstLine := 389
    sourceLastLine := 406 }

structure PoissonHeader where
  q : Nat
  fullRowCount : Nat
  prefixTriples : Nat
  sourceFirstLine : Nat
  sourceLastLine : Nat
  deriving DecidableEq, Repr

/-- v13 `v-reference-data.tex:407-430`, q=7 Poisson rows. -/
def q7PoissonHeader : PoissonHeader :=
  { q := 7
    fullRowCount := 131
    prefixTriples := 66
    sourceFirstLine := 407
    sourceLastLine := 430 }

def lengthScale : Rat := 1 / 100000000

def massScale : Rat := 1 / 100000000

def correctionScale : Rat := 1 / (5 * 10000000000000)

theorem q7XHeader_rows : q7XHeader.rowCount = 39 := rfl

theorem q7VHeader_rows : q7VHeader.rowCount = 47 := rfl

theorem q7ZHeader_rows : q7ZHeader.rowCount = 62 := rfl

theorem q7PoissonHeader_rows : q7PoissonHeader.fullRowCount = 131 := rfl

theorem q7PoissonHeader_prefix : q7PoissonHeader.prefixTriples = 66 := rfl

structure ChainRow where
  lengthIncrement : Int
  massIncrement : Int
  deriving DecidableEq, Repr

structure PoissonRow where
  deltaX : Int
  deltaY : Int
  massIncrement : Int
  deriving DecidableEq, Repr

/-!
The four payload lists are intentionally abstract.  Their lengths, endpoint
accumulations, support conditions, and conjugate completion are obligations
of the certificate consumer.  This prevents a source transcription from being
silently promoted to a checked table.
-/
structure Q7ReferencePayload where
  xRows : List ChainRow
  vRows : List ChainRow
  zRows : List ChainRow
  poissonPrefix : List PoissonRow
  xRows_length : xRows.length = q7XHeader.rowCount
  vRows_length : vRows.length = q7VHeader.rowCount
  zRows_length : zRows.length = q7ZHeader.rowCount
  poissonPrefix_length : poissonPrefix.length = q7PoissonHeader.prefixTriples

def q7ExpectedChainRows : Nat :=
  q7XHeader.rowCount + q7VHeader.rowCount + q7ZHeader.rowCount

theorem q7ExpectedChainRows_eq : q7ExpectedChainRows = 148 := by
  norm_num [q7ExpectedChainRows, q7XHeader, q7VHeader, q7ZHeader]

def q7FieldKx : Rat := -(6071 : Rat) / 1000

def q7FieldKv : Rat := -(4876 : Rat) / 1000

def q7FieldKz : Rat := 1639 / 1000

def q7EnergyLower : Rat := -(4511619 : Rat) / 1000000

def q7AlphaLower : Rat := 309651 / 100000

def q7TauUpper : Rat := 293439 / 100000

def q7EndpointEx : Rat := -(77947 : Rat) / 10000

def q7EndpointEv : Rat := -(49057 : Rat) / 10000

def q7SigmaUpper : Rat := 11898583 / 1000

def q7PathUpper : Rat := 9017257 / 1000000

theorem q7Alpha_gt_q7Tau : q7TauUpper < q7AlphaLower := by
  norm_num [q7TauUpper, q7AlphaLower]

theorem q7Endpoint_x_below_field : q7EndpointEx < q7FieldKx := by
  norm_num [q7EndpointEx, q7FieldKx]

theorem q7Endpoint_v_below_field : q7EndpointEv < q7FieldKv := by
  norm_num [q7EndpointEv, q7FieldKv]

structure Q7ReferenceCertificate where
  payload : Q7ReferencePayload
  x_start_and_correction_checked :
    q7XHeader.startUnits = 3349364905389 ∧
      q7XHeader.correctionIndex = 1 ∧ q7XHeader.correctionNumerator = 94611
  v_start_and_correction_checked :
    q7VHeader.startUnits = 480367989919 ∧
      q7VHeader.correctionIndex = 1 ∧ q7VHeader.correctionNumerator = 10081
  z_start_checked : q7ZHeader.startUnits = -350000000000000
  poisson_header_checked :
    q7PoissonHeader.fullRowCount = 131 ∧ q7PoissonHeader.prefixTriples = 66
  field_thresholds_checked :
    q7FieldKx = -(6071 : Rat) / 1000 ∧
      q7FieldKv = -(4876 : Rat) / 1000 ∧ q7FieldKz = 1639 / 1000
  energy_endpoint_checked : q7EnergyLower = -(4511619 : Rat) / 1000000
  transfer_constants_checked :
    q7EndpointEx = -(77947 : Rat) / 10000 ∧
      q7EndpointEv = -(49057 : Rat) / 10000 ∧
      q7SigmaUpper = 11898583 / 1000 ∧ q7PathUpper = 9017257 / 1000000

theorem certificate_margin (c : Q7ReferenceCertificate) : q7TauUpper < q7AlphaLower :=
  q7Alpha_gt_q7Tau

end Q7Reference
end V
end Li2Lean
