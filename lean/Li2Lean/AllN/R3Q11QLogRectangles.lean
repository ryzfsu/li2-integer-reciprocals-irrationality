/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.AllN.R3Q11QLogFields
import Li2Lean.P0.Q11FrequencyTerms
import Li2Lean.P0.ConfigQLogSegments
import Li2Lean.P0.ConfigRectangleTable

/-!
# Three numerical q = 11 logarithmic-energy leaves

The actual q = 11 interval measures are integrated by the second logarithmic
primitive.  Their endpoints lie on the existing certified 1/32 mesh, so the
kernel-checked `meshH` enclosures can be reused with the q = 11 table weights.
-/

open MeasureTheory Set Filter

namespace Li2Lean.P0.Q11Data

noncomputable section

open Li2Lean.LogSegment ConfigQLogSegments ConfigRectangleBounds CA.Pinned

theorem q11IntervalReferenceMeasure_integral_of_continuous
    {f : ℝ → ℝ} (hf : Continuous f)
    (left right : ℕ → ℝ) (count : ℕ) (units : List ℕ) {width : ℝ}
    (hwidth : 0 < width) :
    (∫ x, f x ∂q11IntervalReferenceMeasure left right count units width) =
      ∑ i ∈ Finset.range count,
        q11IntervalDensity units width i * ∫ x in Ico (left i) (right i), f x := by
  unfold q11IntervalReferenceMeasure
  rw [integral_finsetSum_measure]
  · apply Finset.sum_congr rfl
    intro i hi
    rw [integral_smul_measure,
      ENNReal.toReal_ofReal (q11IntervalDensity_nonneg units hwidth i)]
    rfl
  · intro i hi
    exact (hf.integrableOn_Icc.mono_set Ico_subset_Icc_self).smul_measure
      ENNReal.ofReal_ne_top

private theorem q11_integral_difference_primitive {a b : ℝ} (hab : a ≤ b)
    (c d : ℝ) :
    (∫ x in Ico a b, primitive (x - c) - primitive (x - d)) =
      rectangleLogValue a b c d := by
  have hc : IntegrableOn (fun x : ℝ => primitive (x - c)) (Ico a b) :=
    (continuous_primitive.comp (continuous_id.sub continuous_const)).integrableOn_Icc.mono_set
      Ico_subset_Icc_self
  have hd : IntegrableOn (fun x : ℝ => primitive (x - d)) (Ico a b) :=
    (continuous_primitive.comp (continuous_id.sub continuous_const)).integrableOn_Icc.mono_set
      Ico_subset_Icc_self
  rw [integral_sub hc hd, integral_Ico_primitive_sub _ hab,
    integral_Ico_primitive_sub _ hab]
  unfold rectangleLogValue
  ring

private theorem q11_integral_sum_primitive {a b : ℝ} (hab : a ≤ b)
    (c d : ℝ) :
    (∫ x in Ico a b, primitive (x + d) - primitive (x + c)) =
      rectangleLogAddValue a b c d := by
  have hc : IntegrableOn (fun x : ℝ => primitive (x + c)) (Ico a b) :=
    (continuous_primitive.comp (continuous_id.add continuous_const)).integrableOn_Icc.mono_set
      Ico_subset_Icc_self
  have hd : IntegrableOn (fun x : ℝ => primitive (x + d)) (Ico a b) :=
    (continuous_primitive.comp (continuous_id.add continuous_const)).integrableOn_Icc.mono_set
      Ico_subset_Icc_self
  rw [integral_sub hd hc, integral_Ico_primitive_add _ hab,
    integral_Ico_primitive_add _ hab]
  unfold rectangleLogAddValue
  ring

theorem q11IntervalSelfEnergy_eq_rectangleSum
    (left right : ℕ → ℝ) (count : ℕ) (units : List ℕ) {width : ℝ}
    (hwidth : 0 < width)
    (hleft : ∀ i ∈ Finset.range count, left i ≤ right i) :
    (∫ x, (∫ y, Real.log |x - y|
      ∂q11IntervalReferenceMeasure left right count units width)
      ∂q11IntervalReferenceMeasure left right count units width) =
      ∑ i ∈ Finset.range count, ∑ j ∈ Finset.range count,
        q11IntervalDensity units width i * q11IntervalDensity units width j *
          rectangleLogValue (left i) (right i) (left j) (right j) := by
  have hform : (fun x : ℝ => ∫ y, Real.log |x - y|
      ∂q11IntervalReferenceMeasure left right count units width) = fun x =>
      ∑ j ∈ Finset.range count, q11IntervalDensity units width j *
        (primitive (x - left j) - primitive (x - right j)) := by
    funext x
    exact q11IntervalReferenceMeasure_potential_eq_endpoints
      left right count units width hwidth hleft x
  have hcont : Continuous (fun x : ℝ => ∑ j ∈ Finset.range count,
      q11IntervalDensity units width j *
        (primitive (x - left j) - primitive (x - right j))) := by
    apply continuous_finsetSum
    intro j hj
    exact continuous_const.mul
      ((continuous_primitive.comp (continuous_id.sub continuous_const)).sub
        (continuous_primitive.comp (continuous_id.sub continuous_const)))
  rw [hform, q11IntervalReferenceMeasure_integral_of_continuous hcont
    left right count units hwidth]
  apply Finset.sum_congr rfl
  intro i hi
  rw [integral_finsetSum]
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [integral_const_mul, q11_integral_difference_primitive (hleft i hi)]
    ring
  · intro j hj
    exact ((continuous_const.mul
      ((continuous_primitive.comp (continuous_id.sub continuous_const)).sub
        (continuous_primitive.comp (continuous_id.sub continuous_const)))).integrableOn_Icc).mono_set
      Ico_subset_Icc_self

theorem q11Eκκ_eq_rectangleSum :
    q11Eκκ = ∑ i ∈ Finset.range 8, ∑ j ∈ Finset.range 8,
      q11IntervalDensity pinnedMassUnits (1 / 8 : ℝ) i *
        q11IntervalDensity pinnedMassUnits (1 / 8 : ℝ) j *
        rectangleLogValue (q11PinnedEdgeReal i) (q11PinnedEdgeReal (i + 1))
          (q11PinnedEdgeReal j) (q11PinnedEdgeReal (j + 1)) := by
  unfold q11Eκκ
  simp_rw [q11PinnedComplexPotential_real]
  unfold q11PinnedRealPotential q11PinnedReferenceMeasure
  apply q11IntervalSelfEnergy_eq_rectangleSum
  · norm_num
  · intro i hi
    linarith [q11PinnedEdgeReal_width (Finset.mem_range.mp hi)]

theorem q11Eμμ_eq_rectangleSum :
    q11Eμμ = ∑ i ∈ Finset.range 4, ∑ j ∈ Finset.range 4,
      q11IntervalDensity frequencyMassUnits 1 i *
        q11IntervalDensity frequencyMassUnits 1 j *
        rectangleLogValue (q11FrequencyEdgeReal i) (q11FrequencyEdgeReal (i + 1))
          (q11FrequencyEdgeReal j) (q11FrequencyEdgeReal (j + 1)) := by
  unfold q11Eμμ q11QmuMu q11FrequencyPotential q11FrequencyReferenceMeasure
  apply q11IntervalSelfEnergy_eq_rectangleSum
  · norm_num
  · intro i hi
    linarith [q11FrequencyEdgeReal_width (Finset.mem_range.mp hi)]

theorem q11ReflectedFrequencyPotential_real_eq_endpoints (x : ℝ) :
    q11ReflectedFrequencyPotential (x : ℂ) =
      ∑ j ∈ Finset.range 4, q11IntervalDensity frequencyMassUnits 1 j *
        (primitive (x + q11FrequencyEdgeReal (j + 1)) -
          primitive (x + q11FrequencyEdgeReal j)) := by
  rw [q11ReflectedFrequencyPotential_real, q11FrequencyPotential_eq_endpoints]
  apply Finset.sum_congr rfl
  intro j hj
  rw [show -x - q11FrequencyEdgeReal j = -(x + q11FrequencyEdgeReal j) by ring,
    show -x - q11FrequencyEdgeReal (j + 1) =
      -(x + q11FrequencyEdgeReal (j + 1)) by ring,
    ConfigPinnedTail.primitive_neg, ConfigPinnedTail.primitive_neg]
  ring

theorem q11Eκμ_eq_rectangleSum :
    q11Eκμ = ∑ i ∈ Finset.range 8, ∑ j ∈ Finset.range 4,
      q11IntervalDensity pinnedMassUnits (1 / 8 : ℝ) i *
        q11IntervalDensity frequencyMassUnits 1 j *
        rectangleLogAddValue (q11PinnedEdgeReal i) (q11PinnedEdgeReal (i + 1))
          (q11FrequencyEdgeReal j) (q11FrequencyEdgeReal (j + 1)) := by
  have hcont : Continuous (fun x : ℝ => ∑ j ∈ Finset.range 4,
      q11IntervalDensity frequencyMassUnits 1 j *
        (primitive (x + q11FrequencyEdgeReal (j + 1)) -
          primitive (x + q11FrequencyEdgeReal j))) := by
    apply continuous_finsetSum
    intro j hj
    exact continuous_const.mul
      ((continuous_primitive.comp (continuous_id.add continuous_const)).sub
        (continuous_primitive.comp (continuous_id.add continuous_const)))
  unfold q11Eκμ
  simp_rw [q11ReflectedFrequencyPotential_real_eq_endpoints]
  rw [q11PinnedReferenceMeasure,
    q11IntervalReferenceMeasure_integral_of_continuous hcont
      q11PinnedEdgeReal (fun j => q11PinnedEdgeReal (j + 1)) 8 pinnedMassUnits
      (show 0 < (1 / 8 : ℝ) by norm_num)]
  apply Finset.sum_congr rfl
  intro i hi
  rw [integral_finsetSum]
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [integral_const_mul, q11_integral_sum_primitive
      (show q11PinnedEdgeReal i ≤ q11PinnedEdgeReal (i + 1) from
        by linarith [q11PinnedEdgeReal_width (Finset.mem_range.mp hi)])]
    ring
  · intro j hj
    exact ((continuous_const.mul
      ((continuous_primitive.comp (continuous_id.add continuous_const)).sub
        (continuous_primitive.comp (continuous_id.add continuous_const)))).integrableOn_Icc).mono_set
      Ico_subset_Icc_self

def q11RectI (a b c d : ℤ) : QI :=
  QI.add (QI.sub (QI.sub (meshH (b - c)) (meshH (a - c)))
    (meshH (b - d))) (meshH (a - d))

def q11RectAddI (a b c d : ℤ) : QI :=
  QI.add (QI.sub (QI.sub (meshH (b + d)) (meshH (a + d)))
    (meshH (b + c))) (meshH (a + c))

theorem q11RectI_sound (a b c d : ℤ) :
    (q11RectI a b c d).Contains
      (rectangleLogValue ((a : ℝ) / 32) ((b : ℝ) / 32)
        ((c : ℝ) / 32) ((d : ℝ) / 32)) := by
  have h := QI.mem_add (QI.mem_sub (QI.mem_sub (meshH_sound (b - c))
    (meshH_sound (a - c))) (meshH_sound (b - d))) (meshH_sound (a - d))
  simpa only [q11RectI, rectangleLogValue, Int.cast_sub, sub_div] using h

theorem q11RectAddI_sound (a b c d : ℤ) :
    (q11RectAddI a b c d).Contains
      (rectangleLogAddValue ((a : ℝ) / 32) ((b : ℝ) / 32)
        ((c : ℝ) / 32) ((d : ℝ) / 32)) := by
  have h := QI.mem_add (QI.mem_sub (QI.mem_sub (meshH_sound (b + d))
    (meshH_sound (a + d))) (meshH_sound (b + c))) (meshH_sound (a + c))
  simpa only [q11RectAddI, rectangleLogAddValue, Int.cast_add, add_div] using h

def q11EnergyI (m n : ℕ) (units1 units2 : List ℕ) (width1 width2 : ℚ)
    (r : ℕ → ℕ → QI) : QI :=
  sumIdx m (fun i => sumIdx n (fun j =>
    QI.smul (q11DensityQ units1 width1 i * q11DensityQ units2 width2 j) (r i j)))

theorem q11EnergyI_sound (m n : ℕ) (units1 units2 : List ℕ) (width1 width2 : ℚ)
    (r : ℕ → ℕ → QI) (f : ℕ → ℕ → ℝ)
    (h : ∀ i < m, ∀ j < n, (r i j).Contains (f i j)) :
    (q11EnergyI m n units1 units2 width1 width2 r).Contains
      (∑ i ∈ Finset.range m, ∑ j ∈ Finset.range n,
        q11IntervalDensity units1 width1 i * q11IntervalDensity units2 width2 j * f i j) := by
  apply sumIdx_sound
  intro i hi
  apply sumIdx_sound
  intro j hj
  simpa only [Rat.cast_mul, q11DensityQ_cast] using
    QI.mem_smul (q11DensityQ units1 width1 i * q11DensityQ units2 width2 j)
      (h i hi j hj)

def q11PinnedMeshEdge (j : ℕ) : ℤ := pinnedEdge32Units.getD j 0
def q11FrequencyMeshEdge (j : ℕ) : ℤ := 16 * (frequencyEdge2Units.getD j 0 : ℤ)

theorem q11PinnedMeshEdge_cast (j : ℕ) :
    (q11PinnedMeshEdge j : ℝ) / 32 = q11PinnedEdgeReal j := by
  simp [q11PinnedMeshEdge, q11PinnedEdgeReal, pinnedEdge]

theorem q11FrequencyMeshEdge_cast (j : ℕ) :
    (q11FrequencyMeshEdge j : ℝ) / 32 = q11FrequencyEdgeReal j := by
  dsimp [q11FrequencyMeshEdge, q11FrequencyEdgeReal, frequencyEdge]
  push_cast
  ring

def q11PinnedRectangleI : QI :=
  q11EnergyI 8 8 pinnedMassUnits pinnedMassUnits (1 / 8) (1 / 8) (fun i j =>
    q11RectI (q11PinnedMeshEdge i) (q11PinnedMeshEdge (i + 1))
      (q11PinnedMeshEdge j) (q11PinnedMeshEdge (j + 1)))

def q11FrequencyRectangleI : QI :=
  q11EnergyI 4 4 frequencyMassUnits frequencyMassUnits 1 1 (fun i j =>
    q11RectI (q11FrequencyMeshEdge i) (q11FrequencyMeshEdge (i + 1))
      (q11FrequencyMeshEdge j) (q11FrequencyMeshEdge (j + 1)))

def q11CrossRectangleI : QI :=
  q11EnergyI 8 4 pinnedMassUnits frequencyMassUnits (1 / 8) 1 (fun i j =>
    q11RectAddI (q11PinnedMeshEdge i) (q11PinnedMeshEdge (i + 1))
      (q11FrequencyMeshEdge j) (q11FrequencyMeshEdge (j + 1)))

theorem q11PinnedRectangleI_sound : q11PinnedRectangleI.Contains q11Eκκ := by
  rw [q11Eκκ_eq_rectangleSum]
  simpa only [q11PinnedRectangleI, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using
    q11EnergyI_sound 8 8 pinnedMassUnits pinnedMassUnits (1 / 8) (1 / 8)
      (fun i j => q11RectI (q11PinnedMeshEdge i) (q11PinnedMeshEdge (i + 1))
        (q11PinnedMeshEdge j) (q11PinnedMeshEdge (j + 1)))
      (fun i j => rectangleLogValue (q11PinnedEdgeReal i) (q11PinnedEdgeReal (i + 1))
        (q11PinnedEdgeReal j) (q11PinnedEdgeReal (j + 1)))
      (fun i hi j hj => by
        simpa only [q11PinnedMeshEdge_cast] using
          q11RectI_sound (q11PinnedMeshEdge i) (q11PinnedMeshEdge (i + 1))
            (q11PinnedMeshEdge j) (q11PinnedMeshEdge (j + 1)))

theorem q11FrequencyRectangleI_sound : q11FrequencyRectangleI.Contains q11Eμμ := by
  rw [q11Eμμ_eq_rectangleSum]
  simpa only [q11FrequencyRectangleI, Rat.cast_one] using
    q11EnergyI_sound 4 4 frequencyMassUnits frequencyMassUnits 1 1
      (fun i j => q11RectI (q11FrequencyMeshEdge i) (q11FrequencyMeshEdge (i + 1))
        (q11FrequencyMeshEdge j) (q11FrequencyMeshEdge (j + 1)))
      (fun i j => rectangleLogValue (q11FrequencyEdgeReal i) (q11FrequencyEdgeReal (i + 1))
        (q11FrequencyEdgeReal j) (q11FrequencyEdgeReal (j + 1)))
      (fun i hi j hj => by
        simpa only [q11FrequencyMeshEdge_cast] using
          q11RectI_sound (q11FrequencyMeshEdge i) (q11FrequencyMeshEdge (i + 1))
            (q11FrequencyMeshEdge j) (q11FrequencyMeshEdge (j + 1)))

theorem q11CrossRectangleI_sound : q11CrossRectangleI.Contains q11Eκμ := by
  rw [q11Eκμ_eq_rectangleSum]
  simpa only [q11CrossRectangleI, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using
    q11EnergyI_sound 8 4 pinnedMassUnits frequencyMassUnits (1 / 8) 1
      (fun i j => q11RectAddI (q11PinnedMeshEdge i) (q11PinnedMeshEdge (i + 1))
        (q11FrequencyMeshEdge j) (q11FrequencyMeshEdge (j + 1)))
      (fun i j => rectangleLogAddValue (q11PinnedEdgeReal i) (q11PinnedEdgeReal (i + 1))
        (q11FrequencyEdgeReal j) (q11FrequencyEdgeReal (j + 1)))
      (fun i hi j hj => by
        simpa only [q11PinnedMeshEdge_cast, q11FrequencyMeshEdge_cast] using
          q11RectAddI_sound (q11PinnedMeshEdge i) (q11PinnedMeshEdge (i + 1))
            (q11FrequencyMeshEdge j) (q11FrequencyMeshEdge (j + 1)))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
theorem q11PinnedRectangle_check :
    QI.subset q11PinnedRectangleI ⟨-573876243 / 1000000000, -573876220 / 1000000000⟩ =
      true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
theorem q11FrequencyRectangle_check :
    QI.subset q11FrequencyRectangleI ⟨-1013277437 / 1000000000, -1013277435 / 1000000000⟩ =
      true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
theorem q11CrossRectangle_check :
    QI.subset q11CrossRectangleI ⟨408988084 / 1000000000, 408988090 / 1000000000⟩ =
      true := by decide +kernel

theorem q11Eκκ_bounds :
    (-573876243 / 1000000000 : ℝ) ≤ q11Eκκ ∧
      q11Eκκ ≤ (-573876220 / 1000000000 : ℝ) := by
  have h := QI.mem_of_subset q11PinnedRectangle_check q11PinnedRectangleI_sound
  norm_num [QI.Contains] at h ⊢
  exact h

theorem q11Eμμ_bounds :
    (-1013277437 / 1000000000 : ℝ) ≤ q11Eμμ ∧
      q11Eμμ ≤ (-1013277435 / 1000000000 : ℝ) := by
  have h := QI.mem_of_subset q11FrequencyRectangle_check q11FrequencyRectangleI_sound
  norm_num [QI.Contains] at h ⊢
  exact h

theorem q11Eκμ_bounds :
    (408988084 / 1000000000 : ℝ) ≤ q11Eκμ ∧
      q11Eκμ ≤ (408988090 / 1000000000 : ℝ) := by
  have h := QI.mem_of_subset q11CrossRectangle_check q11CrossRectangleI_sound
  norm_num [QI.Contains] at h ⊢
  exact h

end

end Li2Lean.P0.Q11Data

#print axioms Li2Lean.P0.Q11Data.q11Eκκ_bounds
#print axioms Li2Lean.P0.Q11Data.q11Eμμ_bounds
#print axioms Li2Lean.P0.Q11Data.q11Eκμ_bounds
