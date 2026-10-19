/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
/-
Construction-backed q = 3 row and raw-mass bridges.

The q3 source is the same decoded `q3D` table used by the reference-measure
facts.  These declarations only transport already proved finite facts to the
generic `q3DecodedRows` source; they do not supply normalization, field, energy,
or total-identity certificates.
-/

import Li2Lean.B3.Q3ReferenceMeasureFacts
import Li2Lean.B3.Q3ReferenceRawVMass
import Li2Lean.B3.Q3ReferenceRowBounds

namespace Li2Lean.B3

noncomputable section

open MeasureTheory Set
open scoped ENNReal

theorem q3_decoded_rows_bounds_bridge :
    V13DecodedRowBounds 3 q3DecodedRows := by
  exact q3_decoded_row_bounds

theorem q3_raw_x_mass_bridge :
    (v13RefRaw q3DecodedRows).μx Set.univ = (1 : ℝ≥0∞) := by
  simpa [v13RefRaw, q3DecodedRows, q3RawReferenceMeasures,
    q3DecodedReferenceRows] using q3ReferenceRaw_x_mass

theorem q3_raw_v_mass_bridge :
    (v13RefRaw q3DecodedRows).μv Set.univ = (5 / 4 : ℝ≥0∞) := by
  simpa [v13RefRaw, q3DecodedRows, q3RawReferenceMeasures,
    q3DecodedReferenceRows] using q3ReferenceRaw_v_mass

end

end Li2Lean.B3

#print axioms Li2Lean.B3.q3_decoded_rows_bounds_bridge
#print axioms Li2Lean.B3.q3_raw_x_mass_bridge
#print axioms Li2Lean.B3.q3_raw_v_mass_bridge
