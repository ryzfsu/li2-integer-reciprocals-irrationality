/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.Q11FrequencySubcell
import Li2Lean.P0.Q11WmuMeasurable
import Li2Lean.P0.Q11PenaltyIntegrability
import Li2Lean.P0.Q11PenaltyRowsProducer

/-!
# H7-freq: Reflected Frequency Row Checker, Cell-0 Refined Subcell Consolidation, and `Q11FrequencyPenaltyRowsV13` Producer

This module provides:
1. Consolidation of the 19 refined subcell bounds on `[1/2, 20499/40960]`
   from `Li2Lean.P0.Q11FrequencySubcell` into:
   - `q11FirstRefinedFrequencyCells` and `q11FirstRefinedFrequencyCells_exactChain`,
   - `q11FirstRefinedFrequencyCells_lower` (pointwise bound on every subcell),
   - `q11FirstFrequencyCell_lower` (pointwise bound on the full first cell
     `[1/2, 20499/40960]` obtained via `exactChain_covers`).
2. The reflected rational row/shard checkers `q11RowLowerIWeightedTight`,
   `q11RowCheckIWeightedTight`, `q11ChainCheckWeightedTight`, and
   `q11ShardCheckWeightedTight`, with full soundness theorems
   (`q11RowLowerIWeightedTight_le`, `q11RowCheckIWeightedTight_sound`,
   `q11ShardCheckWeightedTight_sound`).
3. Constructors assembling `Q11FrequencyPenaltyRowsV13`
   (`Li2Lean/P0/Q11PenaltyRowsProducer.lean:43`) from checked frequency shards
   together with `q11FrequencyPenalty_integrable_of_lower_audit` and
   `measurable_q11Wmu`.
-/

open MeasureTheory Set
open scoped BigOperators

namespace Li2Lean.P0.Q11Data

noncomputable section

open Li2Lean.F_L8
open Li2Lean.P0.CA.Receipt
open Li2Lean.P0.CA.Frequency

/-! ## 1. Cell-0 Refined Subcell Chain and Pointwise Lower Bound -/

/- The refined cell list and exact chain are provided by
   `Q11FrequencySubcell`; this module supplies their semantic lower bound
   and the tail assembly. -/

private theorem subcell_le_q11Wmu {ln hn : ℤ}
    (h0 : (1 / 2 : ℝ) ≤ (ln : ℝ) / (40960 : ℕ))
    (hend : (hn : ℝ) / (40960 : ℕ) ≤ (81 / 10 : ℝ))
    (htight : (27435768107 / 10000000000 : ℝ) ≤
      q11RowLowerRealWeightedTight ln 40960 hn 40960)
    {x : ℝ} (hlo : (ln : ℝ) / (40960 : ℕ) ≤ x)
    (hhi : x ≤ (hn : ℝ) / (40960 : ℕ)) :
    (27435768107 / 10000000000 : ℝ) ≤ q11Wmu x :=
  htight.trans
    (q11RowLowerRealWeightedTight_le (by decide) (by decide) h0 hend hlo hhi)

/-- Pointwise lower bound on each of the 19 refined subcells of cell 0. -/
theorem q11FirstRefinedFrequencyCells_lower :
    ∀ c ∈ q11FirstRefinedFrequencyCells, ∀ x : ℝ,
      (c.lo : ℝ) ≤ x → x ≤ (c.hi : ℝ) → (c.lower : ℝ) ≤ q11Wmu x := by
  intro c hc x hlo hhi
  simp only [q11FirstRefinedFrequencyCells, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    norm_num at hlo hhi ⊢
    ring_nf at hlo hhi ⊢
  · exact subcell_le_q11Wmu (by norm_num) (by norm_num)
      q11_first_frequency_subcell_weighted_tight
      (by linarith [hlo]) (by linarith [hhi])
  · exact subcell_le_q11Wmu (by norm_num) (by norm_num)
      q11_second_frequency_subcell_weighted_tight
      (by linarith [hlo]) (by linarith [hhi])
  · exact subcell_le_q11Wmu (by norm_num) (by norm_num)
      q11_third_frequency_subcell_weighted_tight
      (by linarith [hlo]) (by linarith [hhi])
  · exact subcell_le_q11Wmu (by norm_num) (by norm_num)
      q11_fourth_frequency_subcell_weighted_tight
      (by linarith [hlo]) (by linarith [hhi])
  · exact subcell_le_q11Wmu (by norm_num) (by norm_num)
      q11_fifth_frequency_subcell_weighted_tight
      (by linarith [hlo]) (by linarith [hhi])
  · exact subcell_le_q11Wmu (by norm_num) (by norm_num)
      q11_sixth_frequency_subcell_weighted_tight
      (by linarith [hlo]) (by linarith [hhi])
  · exact subcell_le_q11Wmu (by norm_num) (by norm_num)
      q11_seventh_frequency_subcell_weighted_tight
      (by linarith [hlo]) (by linarith [hhi])
  · exact subcell_le_q11Wmu (by norm_num) (by norm_num)
      q11_eighth_frequency_subcell_weighted_tight
      (by linarith [hlo]) (by linarith [hhi])
  · exact subcell_le_q11Wmu (by norm_num) (by norm_num)
      q11_ninth_frequency_subcell_weighted_tight
      (by linarith [hlo]) (by linarith [hhi])
  · exact subcell_le_q11Wmu (by norm_num) (by norm_num)
      q11_tenth_frequency_subcell_weighted_tight
      (by linarith [hlo]) (by linarith [hhi])
  · exact subcell_le_q11Wmu (by norm_num) (by norm_num)
      q11_eleventh_frequency_subcell_weighted_tight
      (by linarith [hlo]) (by linarith [hhi])
  · exact subcell_le_q11Wmu (by norm_num) (by norm_num)
      q11_twelfth_frequency_subcell_weighted_tight
      (by linarith [hlo]) (by linarith [hhi])
  · exact subcell_le_q11Wmu (by norm_num) (by norm_num)
      q11_thirteenth_frequency_subcell_weighted_tight
      (by linarith [hlo]) (by linarith [hhi])
  · exact subcell_le_q11Wmu (by norm_num) (by norm_num)
      q11_fourteenth_frequency_subcell_weighted_tight
      (by linarith [hlo]) (by linarith [hhi])
  · exact subcell_le_q11Wmu (by norm_num) (by norm_num)
      q11_fifteenth_frequency_subcell_weighted_tight
      (by linarith [hlo]) (by linarith [hhi])
  · exact subcell_le_q11Wmu (by norm_num) (by norm_num)
      q11_sixteenth_frequency_subcell_weighted_tight
      (by linarith [hlo]) (by linarith [hhi])
  · exact subcell_le_q11Wmu (by norm_num) (by norm_num)
      q11_seventeenth_frequency_subcell_weighted_tight
      (by linarith [hlo]) (by linarith [hhi])
  · exact subcell_le_q11Wmu (by norm_num) (by norm_num)
      q11_eighteenth_frequency_subcell_weighted_tight
      (by linarith [hlo]) (by linarith [hhi])
  · exact subcell_le_q11Wmu (by norm_num) (by norm_num)
      q11_nineteenth_frequency_subcell_weighted_tight
      (by linarith [hlo]) (by linarith [hhi])

/-- The coarse first frequency cell `[1 / 2, 20499 / 40960]`. -/
def q11FirstFrequencyCell : ReceiptCell :=
  ⟨1 / 2, 20499 / 40960, 27435768107 / 10000000000⟩

/-- Covering `[1 / 2, 20499 / 40960]` by the 19 refined subcells establishes the
    original floor `27435768107 / 10000000000 ≤ q11Wmu x` on the entire first cell. -/
theorem q11FirstFrequencyCell_lower :
    ∀ x : ℝ, (q11FirstFrequencyCell.lo : ℝ) ≤ x →
      x ≤ (q11FirstFrequencyCell.hi : ℝ) →
      (q11FirstFrequencyCell.lower : ℝ) ≤ q11Wmu x := by
  intro x hlo hhi
  have hlo' : ((1 / 2 : ℚ) : ℝ) ≤ x := by simpa [q11FirstFrequencyCell] using hlo
  have hhi' : x ≤ ((20499 / 40960 : ℚ) : ℝ) := by simpa [q11FirstFrequencyCell] using hhi
  obtain ⟨c, hc, _, hclo, hchi⟩ :=
    exactChain_covers q11FirstRefinedFrequencyCells_exactChain x hlo' hhi'
  have hlow := q11FirstRefinedFrequencyCells_lower c hc x hclo hchi
  have hfloor : c.lower = q11FirstFrequencyCell.lower := by
    simp only [q11FirstRefinedFrequencyCells, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  rwa [← hfloor]

/-! ## 2. Reflected Rational Row and Shard Checkers for `q11Wmu` -/

/-- Exact rational counterpart of `q11RowLowerRealWeightedTight`. -/
def q11RowLowerIWeightedTight (ln : ℤ) (ld : ℕ) (hn : ℤ) (hd : ℕ) : ℚ :=
  ((termsLowM ln ld hn hd q11FrequencyTermsIWeighted : ℤ) : ℚ) / twoE +
    (-1 / 2 - l2hi / 2 +
      (ln : ℚ) / ld * (2397895272 / 1000000000 : ℚ) -
      q11NuHiF ((hn : ℚ) / hd))

theorem q11RowLowerIWeightedTight_cast (ln : ℤ) (ld : ℕ) (hn : ℤ) (hd : ℕ) :
    (q11RowLowerIWeightedTight ln ld hn hd : ℝ) =
      q11RowLowerRealWeightedTight ln ld hn hd := by
  unfold q11RowLowerIWeightedTight q11RowLowerRealWeightedTight
  push_cast
  rfl

/-- Pointwise soundness of `q11RowLowerIWeightedTight` on `[ln/ld, hn/hd]`. -/
theorem q11RowLowerIWeightedTight_le {ln hn : ℤ} {ld hd : ℕ}
    (hld : 0 < ld) (hhd : 0 < hd)
    (h0 : (ld : ℤ) ≤ 2 * ln)
    (hend : 10 * hn ≤ 81 * (hd : ℤ)) {x : ℝ}
    (hlo : (ln : ℝ) / ld ≤ x) (hhi : x ≤ (hn : ℝ) / hd) :
    (q11RowLowerIWeightedTight ln ld hn hd : ℝ) ≤ q11Wmu x := by
  have hldR : (0 : ℝ) < ld := by exact_mod_cast hld
  have hhdR : (0 : ℝ) < hd := by exact_mod_cast hhd
  have h0R : (1 / 2 : ℝ) ≤ (ln : ℝ) / ld := by
    rw [le_div_iff₀ hldR]
    have : (ld : ℝ) ≤ 2 * ln := by exact_mod_cast h0
    linarith
  have hendR : (hn : ℝ) / hd ≤ (81 / 10 : ℝ) := by
    rw [div_le_iff₀ hhdR]
    have : 10 * (hn : ℝ) ≤ 81 * (hd : ℝ) := by exact_mod_cast hend
    linarith
  rw [q11RowLowerIWeightedTight_cast]
  exact q11RowLowerRealWeightedTight_le hld hhd h0R hendR hlo hhi

/-- Boolean row checker for a single integer-encoded frequency row. -/
def q11RowCheckIWeightedTight (r : RowI) : Bool :=
  decide (0 < r.2.1) && decide (0 < r.2.2.2.1) &&
    decide ((r.2.1 : ℤ) ≤ 2 * r.1) &&
    decide (10 * r.2.2.1 ≤ 81 * (r.2.2.2.1 : ℤ)) &&
    decide (r.2.2.2.2 ≤ q11RowLowerIWeightedTight r.1 r.2.1 r.2.2.1 r.2.2.2.1)

theorem q11Row_lower_of_check {ln hn : ℤ} {ld hd : ℕ} {low : ℚ}
    (hld : 0 < ld) (hhd : 0 < hd)
    (h0 : (ld : ℤ) ≤ 2 * ln)
    (hend : 10 * hn ≤ 81 * (hd : ℤ))
    (hlow : low ≤ q11RowLowerIWeightedTight ln ld hn hd)
    {x : ℝ} (hxlo : ((RowI.toCell (ln, ld, hn, hd, low)).lo : ℝ) ≤ x)
    (hxhi : x ≤ ((RowI.toCell (ln, ld, hn, hd, low)).hi : ℝ)) :
    ((RowI.toCell (ln, ld, hn, hd, low)).lower : ℝ) ≤ q11Wmu x := by
  simp only [RowI.toCell, Rat.cast_div, Rat.cast_intCast, Rat.cast_natCast] at hxlo hxhi ⊢
  have hb := q11RowLowerIWeightedTight_le hld hhd h0 hend hxlo hxhi
  have hl : (low : ℝ) ≤ (q11RowLowerIWeightedTight ln ld hn hd : ℝ) := by exact_mod_cast hlow
  exact hl.trans hb

theorem q11RowCheckIWeightedTight_sound {r : RowI}
    (h : q11RowCheckIWeightedTight r = true) {x : ℝ}
    (hxlo : (r.toCell.lo : ℝ) ≤ x) (hxhi : x ≤ (r.toCell.hi : ℝ)) :
    (r.toCell.lower : ℝ) ≤ q11Wmu x := by
  obtain ⟨ln, ld, hn, hd, low⟩ := r
  simp only [q11RowCheckIWeightedTight, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨hld, hhd⟩, h0⟩, hend⟩, hlow⟩ := h
  exact q11Row_lower_of_check hld hhd h0 hend hlow hxlo hxhi

/-- Endpoint vector of primitive bounds at `p / q` for `q11FrequencyTermsIWeighted`. -/
def q11EndValsWeighted (p : ℤ) (q : ℕ) : List ℤ :=
  q11FrequencyTermsIWeighted.map (endVal p q)

/-- Chained rational lower bound reusing precomputed endpoint vectors `vl, vh`. -/
def q11RowLowerVWeightedTight (ln : ℤ) (ld : ℕ) (hn : ℤ) (hd : ℕ)
    (vl vh : List ℤ) : ℚ :=
  ((termsLowV ln ld hn hd q11FrequencyTermsIWeighted vl vh : ℤ) : ℚ) / twoE +
    (-1 / 2 - l2hi / 2 +
      (ln : ℚ) / ld * (2397895272 / 1000000000 : ℚ) -
      q11NuHiF ((hn : ℚ) / hd))

theorem q11RowLowerVWeightedTight_eq (ln : ℤ) (ld : ℕ) (hn : ℤ) (hd : ℕ) :
    q11RowLowerVWeightedTight ln ld hn hd
      (q11EndValsWeighted ln ld) (q11EndValsWeighted hn hd) =
    q11RowLowerIWeightedTight ln ld hn hd := by
  unfold q11RowLowerVWeightedTight q11RowLowerIWeightedTight q11EndValsWeighted
  rw [termsLowV_eq]

/-- Chained reflected check across adjacent frequency rows. -/
def q11ChainCheckWeightedTight : List RowI → ℤ → ℕ → List ℤ → Bool
  | [], _, _, _ => true
  | r :: rs, ln, ld, vl =>
      (decide (r.1 = ln) && decide (r.2.1 = ld) && decide (0 < ld) &&
        decide (0 < r.2.2.2.1) && decide ((ld : ℤ) ≤ 2 * ln) &&
        decide (10 * r.2.2.1 ≤ 81 * (r.2.2.2.1 : ℤ)) &&
        decide (r.2.2.2.2 ≤
          q11RowLowerVWeightedTight ln ld r.2.2.1 r.2.2.2.1 vl
            (q11EndValsWeighted r.2.2.1 r.2.2.2.1))) &&
      q11ChainCheckWeightedTight rs r.2.2.1 r.2.2.2.1
        (q11EndValsWeighted r.2.2.1 r.2.2.2.1)

/-- Shard entry point for a contiguous list of frequency rows. -/
def q11ShardCheckWeightedTight : List RowI → Bool
  | [] => true
  | r :: rs =>
      q11ChainCheckWeightedTight (r :: rs) r.1 r.2.1
        (q11EndValsWeighted r.1 r.2.1)

theorem q11ChainCheckWeightedTight_sound :
    ∀ (rows : List RowI) (ln : ℤ) (ld : ℕ),
      q11ChainCheckWeightedTight rows ln ld (q11EndValsWeighted ln ld) = true →
      ∀ r ∈ rows, ∀ x : ℝ,
        (r.toCell.lo : ℝ) ≤ x → x ≤ (r.toCell.hi : ℝ) →
          (r.toCell.lower : ℝ) ≤ q11Wmu x
  | [], _, _, _ => by simp
  | r :: rs, ln, ld, h => by
      obtain ⟨rln, rld, rhn, rhd, rlow⟩ := r
      simp only [q11ChainCheckWeightedTight, Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, hld⟩, hhd⟩, h0⟩, hend⟩, hlow⟩, hrest⟩ := h
      subst h1 h2
      intro r' hr' x hxlo hxhi
      rcases List.mem_cons.mp hr' with rfl | hmem
      · rw [q11RowLowerVWeightedTight_eq] at hlow
        exact q11Row_lower_of_check hld hhd h0 hend hlow hxlo hxhi
      · exact q11ChainCheckWeightedTight_sound rs rhn rhd hrest r' hmem x hxlo hxhi

theorem q11ShardCheckWeightedTight_sound {rows : List RowI}
    (h : q11ShardCheckWeightedTight rows = true) :
    ∀ c ∈ rows.map RowI.toCell, ∀ x : ℝ,
      (c.lo : ℝ) ≤ x → x ≤ (c.hi : ℝ) → (c.lower : ℝ) ≤ q11Wmu x := by
  intro c hc x hxlo hxhi
  obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hc
  cases rows with
  | nil => simp at hr
  | cons r0 rs =>
      exact q11ChainCheckWeightedTight_sound (r0 :: rs) r0.1 r0.2.1 h r hr x hxlo hxhi

/-! ## 3. Constructing `Q11FrequencyPenaltyRowsV13` -/

/-- Pointwise lower-bound predicate for a list of frequency receipt cells. -/
def Q11FrequencyCellsLower (cells : List ReceiptCell) : Prop :=
  ∀ c ∈ cells, ∀ t : ℝ, (c.lo : ℝ) ≤ t → t ≤ (c.hi : ℝ) → (c.lower : ℝ) ≤ q11Wmu t

theorem q11FrequencyCellsLower_append {l1 l2 : List ReceiptCell}
    (h1 : Q11FrequencyCellsLower l1) (h2 : Q11FrequencyCellsLower l2) :
    Q11FrequencyCellsLower (l1 ++ l2) := by
  intro c hc t hlo hhi
  rcases List.mem_append.mp hc with h | h
  · exact h1 c h t hlo hhi
  · exact h2 c h t hlo hhi

theorem q11FirstRefinedFrequencyCells_lower_prop :
    Q11FrequencyCellsLower q11FirstRefinedFrequencyCells :=
  q11FirstRefinedFrequencyCells_lower

theorem q11FirstFrequencyCell_singleton_lower :
    Q11FrequencyCellsLower [q11FirstFrequencyCell] := by
  intro c hc t hlo hhi
  rw [List.mem_singleton.mp hc] at hlo hhi ⊢
  exact q11FirstFrequencyCell_lower t hlo hhi

/-- Assemble `Q11FrequencyPenaltyRowsV13` (`Li2Lean/P0/Q11PenaltyRowsProducer.lean:43`)
    from any exact chain `cells` on `[1 / 2, 81 / 10]` with zero allowance,
    verified lower bounds, and verified penalty mass. -/
def q11FrequencyPenaltyRowsV13_of_cells
    (cells : List ReceiptCell)
    (hchain : ExactChain cells (1 / 2) (81 / 10))
    (hlower : Q11FrequencyCellsLower cells)
    (hmass : penaltyMass q11FrequencyFloorQ 0 cells ≤ q11FrequencyPenaltyUpperQ) :
    Q11FrequencyPenaltyRowsV13 where
  cells := cells
  allowance := 0
  chain := hchain
  lower := fun c hc t hlo hhi => by
    have h := hlower c hc t hlo hhi
    simpa using h
  mass_le := hmass
  integrable :=
    q11FrequencyPenalty_integrable_of_lower_audit
      cells 0 hchain
      (fun c hc t hlo hhi => by simpa using hlower c hc t hlo hhi)
      measurable_q11Wmu

/-- Assemble `Q11FrequencyPenaltyRowsV13` directly from the 19 refined subcells
    on `[1 / 2, 20499 / 40960]` joined with a checked tail chain on
    `[20499 / 40960, 81 / 10]`. -/
def q11FrequencyPenaltyRowsV13_of_refined_first_and_tail
    (tailCells : List ReceiptCell)
    (htailChain : ExactChain tailCells (20499 / 40960) (81 / 10))
    (htailLower : Q11FrequencyCellsLower tailCells)
    (hmass : penaltyMass q11FrequencyFloorQ 0
      (q11FirstRefinedFrequencyCells ++ tailCells) ≤ q11FrequencyPenaltyUpperQ) :
    Q11FrequencyPenaltyRowsV13 :=
  q11FrequencyPenaltyRowsV13_of_cells
    (q11FirstRefinedFrequencyCells ++ tailCells)
    (exactChain_join q11FirstRefinedFrequencyCells_exactChain htailChain)
    (q11FrequencyCellsLower_append q11FirstRefinedFrequencyCells_lower_prop htailLower)
    hmass

end

end Li2Lean.P0.Q11Data
