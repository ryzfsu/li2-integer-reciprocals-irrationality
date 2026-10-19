/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.V.EnergyCertI.ISoundTrans
import Li2Lean.V.EnergyCertI.IFieldEval

/-!
# Glue G-1 .. G-3: from the Boolean shard checks to the real statements

Generated the release date (release source, elaborated).  Verification notes are retained for context.

These lemmas are purely combinatorial.  They take the *per-cell analytic
obligation* (v1 F-a .. F-g, now with K-1 .. K-9 instead of the P0 `mem_*`
lemmas) and the *per-shard energy obligation* (v1 E-a .. E-d, idem) as
hypotheses `hub` / `hEd`, and discharge everything that the kernel `decide`
theorems (`cellsOK`, `chainOK`, `energyShardOK`, `energyPlanTiles`,
`claimsGt`) certify.

* G-1 `cellsOK_sound`: `cellsOK ub K (a :: b :: rest) = true` + cellwise
  enclosure of an upper bound ⟹ `f t < val K` on `[val a, val last]`.
* G-2 `chainOK_cover` / `field_lt_of_chain`: `chainOK lo hi blocks = true`
  ⟹ the blocks cover `[val lo, val hi]`; with G-1 on every block, `f < val K`
  on `[val lo, val hi]`.  `field_lt_Ioc` adds the endpoint disk on `(0, δ]`
  (the shape of `VReferenceFacts.x_field` / `v_field`).
* G-3 `energy_lower_of_plan`: the plan tiles every kind, every shard check
  holds, and `Σ claims > Qlow` ⟹ `val Qlow < T` for the real total `T`.
-/

namespace Li2Lean.V.EnergyCertI

open IK

/-! ## Small list facts -/

theorem qeq_val {a b : QF} (ha : 0 < a.2) (hb : 0 < b.2) (h : qeq a b = true) :
    val a = val b := by
  unfold qeq at h
  rw [Bool.and_eq_true] at h
  exact le_antisymm ((IK.qle_spec ha hb).mp h.1) ((IK.qle_spec hb ha).mp h.2)

theorem lastQ_cons2 (a b : QF) (rest : List QF) :
    lastQ (a :: b :: rest) = lastQ (b :: rest) := by
  simp only [lastQ, List.getLastD_cons]

theorem lastQ_pair (a b : QF) : lastQ [a, b] = b := by
  simp only [lastQ, List.getLastD_cons, List.getLastD_nil]

theorem getLastD_mem' {α : Type*} : ∀ (l : List α) (d : α), l.getLastD d ∈ d :: l
  | [], d => by simp [List.getLastD_nil]
  | x :: l, d => by
      rw [List.getLastD_cons]
      exact List.mem_cons_of_mem d (getLastD_mem' l x)

theorem cellsOK_cons2 (ub : QF → QF → IV) (K a b : QF) (rest : List QF) :
    cellsOK ub K (a :: b :: rest) = (qlt a b && hiLt (ub a b) K && cellsOK ub K (b :: rest)) := by
  first
    | rfl
    | simp only [cellsOK]   -- structural-recursion unfolding  [Verified]

/-! ## G-1 -/

/-- G-1.  `hub` is the analytic cell obligation (v1 F-a .. F-g with K-1 .. K-9):
on a nonempty cell the evaluator's interval encloses some real upper bound
`U` of the field on the cell. -/
theorem cellsOK_sound {f : ℝ → ℝ} {ub : QF → QF → IV} {K : QF} (hK : 0 < K.2)
    (hub : ∀ a b : QF, 0 < a.2 → 0 < b.2 → val a < val b →
      ∃ U : ℝ, IV.mem (ub a b) U ∧ ∀ t, val a ≤ t → t ≤ val b → f t ≤ U) :
    ∀ (rest : List QF) (a b : QF), (∀ c ∈ a :: b :: rest, 0 < c.2) →
      cellsOK ub K (a :: b :: rest) = true →
      ∀ t, val a ≤ t → t ≤ val (lastQ (a :: b :: rest)) → f t < val K := by
  intro rest
  induction rest with
  | nil =>
      intro a b hden h t ht1 ht2
      rw [cellsOK_cons2, Bool.and_eq_true, Bool.and_eq_true] at h
      have ha := hden a (by simp)
      have hb := hden b (by simp)
      have hab := (IK.qlt_spec ha hb).mp h.1.1
      obtain ⟨U, hU, hfU⟩ := hub a b ha hb hab
      rw [lastQ_pair] at ht2
      exact lt_of_le_of_lt (hfU t ht1 ht2) (IK.hiLt_spec hK hU h.1.2)
  | cons c rest ih =>
      intro a b hden h t ht1 ht2
      rw [cellsOK_cons2, Bool.and_eq_true, Bool.and_eq_true] at h
      have ha := hden a (by simp)
      have hb := hden b (by simp)
      have hab := (IK.qlt_spec ha hb).mp h.1.1
      rw [lastQ_cons2] at ht2
      by_cases htb : t ≤ val b
      · obtain ⟨U, hU, hfU⟩ := hub a b ha hb hab
        exact lt_of_le_of_lt (hfU t ht1 htb) (IK.hiLt_spec hK hU h.1.2)
      · exact ih b c (fun x hx => hden x (List.mem_cons_of_mem a hx)) h.2 t
          (le_of_lt (lt_of_not_ge htb)) ht2

/-! ## G-2 -/

/-- G-2: `chainOK lo hi blocks` makes the blocks cover `[val lo, val hi]`. -/
theorem chainOK_cover (hi : QF) (hhi : 0 < hi.2) (blocks : List (List QF))
    (hpos : ∀ s ∈ blocks, 0 < (headQ s).2 ∧ 0 < (lastQ s).2) :
    ∀ lo : QF, 0 < lo.2 → chainOK lo hi blocks = true →
      ∀ t, val lo ≤ t → t ≤ val hi →
        ∃ s ∈ blocks, val (headQ s) ≤ t ∧ t ≤ val (lastQ s) := by
  induction blocks with
  | nil => intro lo _ h; simp [chainOK] at h
  | cons s tl ih =>
      intro lo hlo h t ht1 ht2
      have hs := hpos s (by simp)
      have ih' := ih (fun x hx => hpos x (List.mem_cons_of_mem s hx))
      cases tl with
      | nil =>
          have h' : qeq (headQ s) lo = true ∧ qeq (lastQ s) hi = true := by
            simpa [chainOK] using h
          have e1 := qeq_val hs.1 hlo h'.1
          have e2 := qeq_val hs.2 hhi h'.2
          exact ⟨s, by simp, by rw [e1]; exact ht1, by rw [e2]; exact ht2⟩
      | cons s' tl' =>
          have h' : qeq (headQ s) lo = true ∧ chainOK (lastQ s) hi (s' :: tl') = true := by
            simpa [chainOK] using h
          have e1 := qeq_val hs.1 hlo h'.1
          by_cases hts : t ≤ val (lastQ s)
          · exact ⟨s, by simp, by rw [e1]; exact ht1, hts⟩
          · obtain ⟨s'', hmem, hh⟩ := ih' (lastQ s) hs.2 h'.2 t
              (le_of_lt (lt_of_not_ge hts)) ht2
            exact ⟨s'', List.mem_cons_of_mem s hmem, hh⟩

/-- Data well-formedness of one breakpoint block (decidable; checked once per
piece by `decide +kernel` in the assembly file). -/
def blockWF (s : List QF) : Bool := decide (2 ≤ s.length) && s.all fun c => decide (0 < c.2)

/-- G-1 + G-2: a field bound on the whole interval `[val lo, val hi]`. -/
theorem field_lt_of_chain {f : ℝ → ℝ} {ub : QF → QF → IV} {K : QF} (hK : 0 < K.2)
    (hub : ∀ a b : QF, 0 < a.2 → 0 < b.2 → val a < val b →
      ∃ U : ℝ, IV.mem (ub a b) U ∧ ∀ t, val a ≤ t → t ≤ val b → f t ≤ U)
    {lo hi : QF} (hlo : 0 < lo.2) (hhi : 0 < hi.2) {blocks : List (List QF)}
    (hwf : ∀ s ∈ blocks, blockWF s = true) (hcells : ∀ s ∈ blocks, cellsOK ub K s = true)
    (hchain : chainOK lo hi blocks = true) :
    ∀ t, val lo ≤ t → t ≤ val hi → f t < val K := by
  have hden : ∀ s ∈ blocks, ∀ c ∈ s, 0 < c.2 := by
    intro s hs c hc
    have h := hwf s hs
    unfold blockWF at h
    rw [Bool.and_eq_true, List.all_eq_true] at h
    exact of_decide_eq_true (h.2 c hc)
  have hpos : ∀ s ∈ blocks, 0 < (headQ s).2 ∧ 0 < (lastQ s).2 := by
    intro s hs
    have hw := hwf s hs
    rcases s with _ | ⟨a, _ | ⟨b, rest⟩⟩
    · simp [blockWF] at hw
    · simp [blockWF] at hw
    · refine ⟨hden _ hs a (by simp), hden _ hs _ ?_⟩
      unfold lastQ
      rw [List.getLastD_cons]
      exact getLastD_mem' (b :: rest) a
  intro t ht1 ht2
  obtain ⟨s, hs, hts1, hts2⟩ := chainOK_cover hi hhi blocks hpos lo hlo hchain t ht1 ht2
  have hw := hwf s hs
  rcases s with _ | ⟨a, _ | ⟨b, rest⟩⟩
  · simp [blockWF] at hw
  · simp [blockWF] at hw
  · exact cellsOK_sound hK hub rest a b (hden _ hs) (hcells _ hs) t hts1 hts2

/-- The `Ioc 0 1` shape of `VReferenceFacts.x_field` / `v_field`: endpoint disk
on `(0, δ]` (bound `E < K`) plus the chain bound on `[δ, 1]`. -/
theorem field_lt_Ioc {f : ℝ → ℝ} {δ E Kr : ℝ} (hE : E < Kr)
    (hdisk : ∀ t, 0 < t → t ≤ δ → f t ≤ E) (hchain : ∀ t, δ ≤ t → t ≤ 1 → f t < Kr) :
    ∀ t ∈ Set.Ioc (0 : ℝ) 1, f t < Kr := by
  intro t ht
  by_cases htd : t ≤ δ
  · exact lt_of_le_of_lt (hdisk t ht.1 htd) hE
  · exact hchain t (le_of_lt (lt_of_not_ge htd)) ht.2

/-! ## G-3 -/

def allKinds : List EKind := [.selfX, .selfV, .selfZ, .crossVZ, .intPoi, .pp, .dq]

theorem foldl_add_eq (l : List ℤ) (a : ℤ) : l.foldl (· + ·) a = a + l.sum := by
  induction l generalizing a with
  | nil => simp
  | cons x l ih => simp [List.foldl, ih, add_assoc]

theorem tilesFrom_le : ∀ (rs : List (ℕ × ℕ)) (cur n : ℕ), tilesFrom cur n rs = true → cur ≤ n
  | [], cur, n, h => by
      simp only [tilesFrom, beq_iff_eq] at h
      omega
  | (a, b) :: rest, cur, n, h => by
      simp only [tilesFrom, Bool.and_eq_true, beq_iff_eq, Nat.blt_eq] at h
      obtain ⟨⟨h1, h2⟩, h3⟩ := h
      have := tilesFrom_le rest b n h3
      omega

theorem tilesFrom_sum (g : ℕ → ℝ) :
    ∀ (rs : List (ℕ × ℕ)) (cur n : ℕ), tilesFrom cur n rs = true →
      (rs.map fun r => ∑ i ∈ Finset.Ico r.1 r.2, g i).sum = ∑ i ∈ Finset.Ico cur n, g i
  | [], cur, n, h => by
      simp only [tilesFrom, beq_iff_eq] at h
      subst h
      simp
  | (a, b) :: rest, cur, n, h => by
      simp only [tilesFrom, Bool.and_eq_true, beq_iff_eq, Nat.blt_eq] at h
      obtain ⟨⟨h1, h2⟩, h3⟩ := h
      have hbn := tilesFrom_le rest b n h3
      simp only [List.map_cons, List.sum_cons]
      rw [tilesFrom_sum g rest b n h3]
      subst h1
      exact Finset.sum_Ico_consecutive g h2.le hbn

/-- Regroup a plan sum by kind. -/
theorem sum_by_kind {β : Type*} (l : List (EKind × β)) (g : EKind × β → ℝ) :
    (l.map g).sum =
      (allKinds.map fun k => ((l.filter fun e => decide (e.1 = k)).map g).sum).sum := by
  induction l with
  | nil => simp [allKinds]
  | cons e rest ih =>
      rw [List.map_cons, List.sum_cons, ih]
      obtain ⟨k, x⟩ := e
      cases k <;> simp [allKinds, List.filter_cons] <;> ring   -- [Verified]

theorem sum_cast_le {α : Type*} (l : List α) (c : α → ℤ) (g : α → ℝ)
    (h : ∀ e ∈ l, (c e : ℝ) ≤ g e * S) :
    (((l.map c).sum : ℤ) : ℝ) ≤ (l.map g).sum * S := by
  induction l with
  | nil => simp
  | cons e rest ih =>
      simp only [List.map_cons, List.sum_cons, Int.cast_add]
      have h1 := h e (by simp)
      have h2 := ih (fun x hx => h x (List.mem_cons_of_mem e hx))
      have e1 : (g e + (rest.map g).sum) * (S : ℝ) = g e * S + (rest.map g).sum * S := by ring
      linarith

/-- G-3.  `hEd` is the per-shard analytic obligation (v1 E-a .. E-d with
K-1 .. K-9): each planned shard's interval encloses the real partial sum
`Σ_{i ∈ [i0, i1)} term k i`; `hT` identifies the real total (for the reference
measure, `T = signedVQuadratic ν`, which is again E-a .. E-c). -/
theorem energy_lower_of_plan (D : IData) (q : Nat) (lr : IV)
    (plan : List (EKind × Nat × Nat × Int)) (qlow : QF) (hq : 0 < qlow.2)
    (term : EKind → ℕ → ℝ) (T : ℝ)
    (hT : T = (allKinds.map fun k => ∑ i ∈ Finset.range (kindCount D k), term k i).sum)
    (htiles : energyPlanTiles D plan = true)
    (hclaims : claimsGt plan qlow = true)
    (hshard : ∀ e ∈ plan, energyShardOK D q lr e.1 e.2.1 e.2.2.1 e.2.2.2 = true)
    (hEd : ∀ e ∈ plan, IV.mem (energyShard D q lr e.1 e.2.1 e.2.2.1)
      (∑ i ∈ Finset.Ico e.2.1 e.2.2.1, term e.1 i)) :
    val qlow < T := by
  set g : EKind × Nat × Nat × Int → ℝ := fun e => ∑ i ∈ Finset.Ico e.2.1 e.2.2.1, term e.1 i
    with hg
  -- (1) the planned partial sums add up to `T`
  have hsum : (plan.map g).sum = T := by
    rw [sum_by_kind plan g, hT]
    congr 1
    apply List.map_congr_left
    intro k hk
    have ht : tilesFrom 0 (kindCount D k) (rangesOf k plan) = true := by
      unfold energyPlanTiles at htiles
      rw [List.all_eq_true] at htiles
      exact htiles k hk
    rw [Finset.range_eq_Ico, ← tilesFrom_sum (term k) _ 0 _ ht]
    unfold rangesOf
    rw [List.map_map]
    congr 1
    apply List.map_congr_left
    intro e he
    have hek : e.1 = k := by
      have := (List.mem_filter.mp he).2
      simpa using this
    simp only [hg, Function.comp_apply, hek]
  -- (2) every claim is below `2^64 ×` its partial sum
  have hcl : ∀ e ∈ plan, ((e.2.2.2 : ℤ) : ℝ) ≤ g e * S := by
    intro e he
    have h1 := hshard e he
    unfold energyShardOK at h1
    have h1' : ((e.2.2.2 : ℤ) : ℝ) ≤ ((energyShard D q lr e.1 e.2.1 e.2.2.1).1 : ℝ) := by
      exact_mod_cast of_decide_eq_true h1
    have h2 := (IK.mem_iff.mp (hEd e he)).1
    exact h1'.trans h2
  have hsc := sum_cast_le plan (fun e => e.2.2.2) g hcl
  rw [hsum] at hsc
  -- (3) `claimsGt`
  unfold claimsGt at hclaims
  have hlt := (IK.qlt_spec (b := ((plan.map fun e => e.2.2.2).foldl (· + ·) 0, S))
    hq IK.S_pos_nat).mp hclaims
  rw [foldl_add_eq, zero_add] at hlt
  have hS := IK.S_pos
  calc val qlow < (((plan.map fun e => e.2.2.2).sum : ℤ) : ℝ) / (S : ℝ) := hlt
    _ ≤ T := by rw [div_le_iff₀ hS]; exact hsc

end Li2Lean.V.EnergyCertI
