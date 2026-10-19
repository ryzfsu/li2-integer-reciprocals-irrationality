/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

The concrete measure layer for the v13 signed-V reference data.

This module deliberately separates construction from its analytic facts.  The
decoded rows determine a raw triple of measures.  The conversion to
`V.SignedVMeasures` requires an explicit normalization witness, so no mass,
support, or energy statement is hidden in a definition.
-/

import Mathlib
import Li2Lean.B3.EnergySoundnessInputs
import Li2Lean.P0.TubeExteriorPoisson
import Li2Lean.V.EnergyCertI.IData
import Li2Lean.V.SignedEnergy

namespace Li2Lean

noncomputable section

namespace B3

open MeasureTheory Set
open V
open V.EnergyCertI
open V.EnergyCertI.IK
open scoped ENNReal

/-! ## Chain cells -/

/-- One real interval carrying a constant density.  The density is allowed to
be an arbitrary real at this layer; `ENNReal.ofReal` records the positive
measure that is actually constructed, while the F-layer proves nonnegativity
for the v13 rows. -/
structure V13ChainCell where
  left : ℝ
  right : ℝ
  density : ℝ

/-- The finite piecewise-uniform measure represented by a list of cells. -/
def v13ChainMeasure (cells : List V13ChainCell) : Measure ℝ :=
  cells.foldr
    (fun c μ => ENNReal.ofReal c.density •
      volume.restrict (Ioc c.left c.right) + μ) 0

/-- Push a real chain to the complex line. -/
def v13ChainMeasureComplex (cells : List V13ChainCell) : Measure ℂ :=
  Measure.map Complex.ofReal (v13ChainMeasure cells)

/-! A decoded chain stores jumps of its piecewise-constant density.  Prefixing
the jumps recovers the density on the interval starting at each endpoint. -/

def v13ChainCellsAux : ℝ → List CP → List V13ChainCell
  | _, [] => []
  | _, [_] => []
  | h, c :: d :: rest =>
      { left := IK.val c.e
        right := IK.val d.e
        density := h + IK.val c.J } ::
        v13ChainCellsAux (h + IK.val c.J) (d :: rest)

def v13ChainCells (rows : List CP) : List V13ChainCell :=
  v13ChainCellsAux 0 rows

def v13DecodedChainMeasure (rows : List CP) : Measure ℂ :=
  v13ChainMeasureComplex (v13ChainCells rows)

/-! ## Poisson rows -/

/-- Complex point represented by a decoded Poisson row. -/
def v13PoissonPoint (r : PR) : ℂ :=
  ⟨IK.val r.cx, IK.val r.cy⟩

/-! The fixed-radius circle law used by the v13 interaction rows. -/

/-- The fixed global circle radius used by the v13 Poisson interaction rows. -/
def v13GlobalPoissonRadius : ℝ := 3 / 5

/-- Normalized angular density for harmonic measure on the circle of radius `3/5`.
The interior point is rescaled to the unit disk before applying the standard
unit-circle Poisson kernel. -/
def v13GlobalPoissonAngleDensity (p : ℂ) (θ : ℝ) : ℝ :=
  (2 * Real.pi)⁻¹ * poissonKernel 0 (p / (v13GlobalPoissonRadius : ℂ))
    (circleMap 0 1 θ)

/-- Global-radius Poisson law on the circle `|z| = 3/5`. -/
def v13GlobalCirclePoissonMeasure (p : ℂ) : Measure ℂ :=
  Measure.map (circleMap 0 v13GlobalPoissonRadius)
    ((volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))).withDensity
      (fun θ => ENNReal.ofReal (v13GlobalPoissonAngleDensity p θ)))

theorem v13GlobalPoissonParameter_norm_lt {p : ℂ}
    (hp : ‖p‖ < v13GlobalPoissonRadius) :
    ‖p / (v13GlobalPoissonRadius : ℂ)‖ < 1 := by
  have hr : v13GlobalPoissonRadius = (3 / 5 : ℝ) := by
    norm_num [v13GlobalPoissonRadius]
  rw [hr] at hp ⊢
  rw [norm_div]
  have hnorm : ‖((3 / 5 : ℝ) : ℂ)‖ = (3 / 5 : ℝ) := by
    rw [Complex.norm_real]
    norm_num
  rw [hnorm]
  apply (div_lt_iff₀ (by norm_num : (0 : ℝ) < 3 / 5)).2
  simpa only [one_mul] using hp

theorem v13GlobalPoissonAngleDensity_nonneg {p : ℂ}
    (hp : ‖p‖ < v13GlobalPoissonRadius) (θ : ℝ) :
    0 ≤ v13GlobalPoissonAngleDensity p θ := by
  apply mul_nonneg (by positivity : 0 ≤ (2 * Real.pi)⁻¹)
  apply P0.poissonKernel_unit_nonneg (v13GlobalPoissonParameter_norm_lt hp)
  simp

theorem integrable_v13GlobalPoissonAngleDensity {p : ℂ}
    (hp : ‖p‖ < v13GlobalPoissonRadius) :
    Integrable (v13GlobalPoissonAngleDensity p)
      (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))) := by
  have hp' := v13GlobalPoissonParameter_norm_lt hp
  have hi := (P0.poissonKernel_unit_continuous hp').circleIntegrable
    (by norm_num : (0 : ℝ) ≤ 1)
  change IntervalIntegrable
    (fun θ => poissonKernel 0 (p / (v13GlobalPoissonRadius : ℂ))
      (circleMap 0 1 θ)) volume 0 (2 * Real.pi) at hi
  apply (intervalIntegrable_iff_integrableOn_Ioc_of_le
    (by positivity : (0 : ℝ) ≤ 2 * Real.pi)).mp
  exact hi.const_mul (2 * Real.pi)⁻¹

theorem integral_v13GlobalPoissonAngleDensity {p : ℂ}
    (hp : ‖p‖ < v13GlobalPoissonRadius) :
    ∫ θ in Ioc (0 : ℝ) (2 * Real.pi), v13GlobalPoissonAngleDensity p θ = 1 := by
  have h := P0.poissonKernel_unit_mass (v13GlobalPoissonParameter_norm_lt hp)
  rw [Real.circleAverage_def,
    intervalIntegral.integral_of_le (by positivity : (0 : ℝ) ≤ 2 * Real.pi)] at h
  simpa only [v13GlobalPoissonAngleDensity, integral_const_mul, smul_eq_mul] using h

theorem v13GlobalCirclePoissonMeasure_univ {p : ℂ}
    (hp : ‖p‖ < v13GlobalPoissonRadius) :
    v13GlobalCirclePoissonMeasure p Set.univ = 1 := by
  rw [v13GlobalCirclePoissonMeasure,
    Measure.map_apply (continuous_circleMap 0 v13GlobalPoissonRadius).measurable
      MeasurableSet.univ,
    Set.preimage_univ, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal
      (integrable_v13GlobalPoissonAngleDensity hp)
      (Filter.Eventually.of_forall (v13GlobalPoissonAngleDensity_nonneg hp)),
    integral_v13GlobalPoissonAngleDensity hp]
  norm_num

theorem v13GlobalCirclePoissonMeasure_sphere_compl (p : ℂ) :
    v13GlobalCirclePoissonMeasure p (Metric.sphere 0 v13GlobalPoissonRadius)ᶜ = 0 := by
  rw [v13GlobalCirclePoissonMeasure,
    Measure.map_apply (continuous_circleMap 0 v13GlobalPoissonRadius).measurable
      Metric.isClosed_sphere.measurableSet.compl]
  have hpre : circleMap 0 v13GlobalPoissonRadius ⁻¹'
      (Metric.sphere 0 v13GlobalPoissonRadius)ᶜ = ∅ := by
    ext θ
    simp only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_empty_iff_false,
      iff_false, not_not]
    exact circleMap_mem_sphere 0 (by norm_num [v13GlobalPoissonRadius] :
      0 ≤ v13GlobalPoissonRadius) θ
  rw [hpre, measure_empty]

/-- One decoded Poisson row as a weighted Poisson law on the global circle.
The row multiplicity is part of the printed data and is folded into its mass. -/
def v13PoissonAtom (r : PR) : Measure ℂ :=
  ENNReal.ofReal ((r.mult : ℝ) * IK.val r.w) •
    v13GlobalCirclePoissonMeasure (v13PoissonPoint r)

/-- The finite Poisson measure represented by decoded rows. -/
def v13PoissonMeasure (rows : List PR) : Measure ℂ :=
  rows.foldr (fun r μ => v13PoissonAtom r + μ) 0

/-! ## The q-indexed raw reference triple -/

/-- A raw triple before the mass and finiteness facts are proved. -/
structure V13RawMeasures (q : ℕ) where
  μx : Measure ℂ
  μv : Measure ℂ
  μz : Measure ℂ

/-- Build the raw q-indexed reference triple from decoded integer rows. -/
def v13RefRaw {q : ℕ} (R : V13DecodedRows q) : V13RawMeasures q :=
  { μx := v13DecodedChainMeasure R.data.xp
    μv := v13DecodedChainMeasure R.data.vp
    μz := v13DecodedChainMeasure R.data.zp + v13PoissonMeasure R.data.full }

/-- The same constructor when a caller has an `IData` value but is still
working below the row-source boundary. -/
def v13RefRawOfData (q : ℕ) (D : IData) : V13RawMeasures q :=
  { μx := v13DecodedChainMeasure D.xp
    μv := v13DecodedChainMeasure D.vp
    μz := v13DecodedChainMeasure D.zp + v13PoissonMeasure D.full }

/-! ## Explicit normalization boundary -/

/-- Facts needed to turn a raw triple into the signed-V structure.  These are
deliberately propositions supplied by the measure/fact layer, not defaults. -/
structure V13MeasureNormalization {q : ℕ} (hq : SignedVBaseRange q)
    (M : V13RawMeasures q) : Prop where
  mass_x : M.μx Set.univ = (1 : ℝ≥0∞)
  mass_v : M.μv Set.univ = (5 / 4 : ℝ≥0∞)
  mass_z : M.μz Set.univ = (1 : ℝ≥0∞)
  finite_x : M.μx Set.univ ≠ ⊤
  finite_v : M.μv Set.univ ≠ ⊤
  finite_z : M.μz Set.univ ≠ ⊤

/-- Package a raw triple only after its normalization witness has been proved. -/
def V13RawMeasures.toSigned {q : ℕ} {hq : SignedVBaseRange q}
    (M : V13RawMeasures q) (N : V13MeasureNormalization hq M) :
    V.SignedVMeasures :=
  { q := q
    q_lower := hq.1
    q_upper := hq.2
    μx := M.μx
    μv := M.μv
    μz := M.μz
    mass_x := N.mass_x
    mass_v := N.mass_v
    mass_z := N.mass_z
    finite_x := N.finite_x
    finite_v := N.finite_v
    finite_z := N.finite_z }

/-- Final q-indexed constructor used by the package integrator. -/
def v13RefMeasure {q : ℕ} {hq : SignedVBaseRange q}
    (R : V13DecodedRows q)
    (N : V13MeasureNormalization hq (v13RefRaw R)) : V.SignedVMeasures :=
  (v13RefRaw R).toSigned N

end B3

end

end Li2Lean

#print axioms Li2Lean.B3.v13RefMeasure
