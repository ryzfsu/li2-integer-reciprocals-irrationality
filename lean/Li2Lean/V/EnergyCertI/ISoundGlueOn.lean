/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.V.EnergyCertI.ISoundGlue

namespace Li2Lean.V.EnergyCertI

open IK

/- Restricted chain soundness for the piece-domain CellSoundnessOn interface.
   This probe keeps the existing unrestricted lemmas unchanged. -/

theorem lastQ_ge_first_h6 {ub : QF → QF → IV} {K : QF} :
    ∀ (rest : List QF) (a b : QF),
      (∀ c ∈ a :: b :: rest, 0 < c.2) →
      cellsOK ub K (a :: b :: rest) = true →
      val a < val (lastQ (a :: b :: rest))
  | [], a, b, hden, h => by
      rw [cellsOK_cons2, Bool.and_eq_true, Bool.and_eq_true] at h
      rw [lastQ_pair]
      exact (IK.qlt_spec (hden a (by simp)) (hden b (by simp))).mp h.1.1
  | c :: rest, a, b, hden, h => by
      rw [cellsOK_cons2, Bool.and_eq_true, Bool.and_eq_true] at h
      rw [lastQ_cons2]
      have hab := (IK.qlt_spec (hden a (by simp)) (hden b (by simp))).mp h.1.1
      have hbc := lastQ_ge_first_h6 rest b c
        (fun x hx => hden x (List.mem_cons_of_mem a hx)) h.2
      exact lt_trans hab hbc

theorem cellsOK_sound_on_h6 {f : ℝ → ℝ} {ub : QF → QF → IV} {K lo hi : QF}
    (hK : 0 < K.2)
    (hub : ∀ a b : QF, 0 < a.2 → 0 < b.2 → val lo ≤ val a → val b ≤ val hi →
      val a < val b →
      ∃ U : ℝ, IV.mem (ub a b) U ∧ ∀ t, val a ≤ t → t ≤ val b → f t ≤ U) :
    ∀ (rest : List QF) (a b : QF), (∀ c ∈ a :: b :: rest, 0 < c.2) →
      val lo ≤ val a → val (lastQ (a :: b :: rest)) ≤ val hi →
      cellsOK ub K (a :: b :: rest) = true →
      ∀ t, val a ≤ t → t ≤ val (lastQ (a :: b :: rest)) → f t < val K := by
  intro rest
  induction rest with
  | nil =>
      intro a b hden hlo_a hhi_last h t ht1 ht2
      rw [cellsOK_cons2, Bool.and_eq_true, Bool.and_eq_true] at h
      rw [lastQ_pair] at hhi_last ht2
      have ha := hden a (by simp)
      have hb := hden b (by simp)
      have hab := (IK.qlt_spec ha hb).mp h.1.1
      obtain ⟨U, hU, hfU⟩ := hub a b ha hb hlo_a hhi_last hab
      exact lt_of_le_of_lt (hfU t ht1 ht2) (IK.hiLt_spec hK hU h.1.2)
  | cons c rest ih =>
      intro a b hden hlo_a hhi_last h t ht1 ht2
      rw [cellsOK_cons2, Bool.and_eq_true, Bool.and_eq_true] at h
      rw [lastQ_cons2] at hhi_last ht2
      have ha := hden a (by simp)
      have hb := hden b (by simp)
      have hab := (IK.qlt_spec ha hb).mp h.1.1
      have hden' : ∀ x ∈ b :: c :: rest, 0 < x.2 :=
        fun x hx => hden x (List.mem_cons_of_mem a hx)
      have hb_last : val b ≤ val (lastQ (b :: c :: rest)) :=
        le_of_lt (lastQ_ge_first_h6 rest b c hden' h.2)
      by_cases htb : t ≤ val b
      · obtain ⟨U, hU, hfU⟩ := hub a b ha hb hlo_a
          (le_trans hb_last hhi_last) hab
        exact lt_of_le_of_lt (hfU t ht1 htb) (IK.hiLt_spec hK hU h.1.2)
      · exact ih b c hden' (le_trans hlo_a (le_of_lt hab)) hhi_last h.2 t
          (le_of_lt (lt_of_not_ge htb)) ht2

theorem chainOK_endpoints_le_h6 (hi : QF) (hhi : 0 < hi.2) :
    ∀ (blocks : List (List QF)),
      (∀ s ∈ blocks, 0 < (headQ s).2 ∧ 0 < (lastQ s).2 ∧
        val (headQ s) ≤ val (lastQ s)) →
      ∀ lo : QF, 0 < lo.2 → chainOK lo hi blocks = true → val lo ≤ val hi
  | [], _, lo, _, h => by simp [chainOK] at h
  | [s], hpos, lo, hlo, h => by
      have hs := hpos s (by simp)
      have h' : qeq (headQ s) lo = true ∧ qeq (lastQ s) hi = true := by
        simpa [chainOK] using h
      have e1 := qeq_val hs.1 hlo h'.1
      have e2 := qeq_val hs.2.1 hhi h'.2
      linarith [hs.2.2]
  | s :: s' :: tl, hpos, lo, hlo, h => by
      have hs := hpos s (by simp)
      have h' : qeq (headQ s) lo = true ∧ chainOK (lastQ s) hi (s' :: tl) = true := by
        simpa [chainOK] using h
      have e1 := qeq_val hs.1 hlo h'.1
      have hrec := chainOK_endpoints_le_h6 hi hhi (s' :: tl)
        (fun x hx => hpos x (List.mem_cons_of_mem s hx)) (lastQ s) hs.2.1 h'.2
      linarith [hs.2.2]

theorem chainOK_cover_on_h6 {ub : QF → QF → IV} {K : QF} (hi : QF)
    (hhi : 0 < hi.2) (blocks : List (List QF))
    (hwf : ∀ s ∈ blocks, blockWF s = true)
    (hcells : ∀ s ∈ blocks, cellsOK ub K s = true) :
    ∀ lo : QF, 0 < lo.2 → chainOK lo hi blocks = true →
      ∀ t, val lo ≤ t → t ≤ val hi →
        ∃ s ∈ blocks, val lo ≤ val (headQ s) ∧ val (lastQ s) ≤ val hi ∧
          val (headQ s) ≤ t ∧ t ≤ val (lastQ s) := by
  have hden : ∀ s ∈ blocks, ∀ c ∈ s, 0 < c.2 := by
    intro s hs c hc
    have h := hwf s hs
    unfold blockWF at h
    rw [Bool.and_eq_true, List.all_eq_true] at h
    exact of_decide_eq_true (h.2 c hc)
  have hpos : ∀ s ∈ blocks,
      0 < (headQ s).2 ∧ 0 < (lastQ s).2 ∧ val (headQ s) ≤ val (lastQ s) := by
    intro s hs
    have hw := hwf s hs
    rcases s with _ | ⟨a, _ | ⟨b, rest⟩⟩
    · simp [blockWF] at hw
    · simp [blockWF] at hw
    · refine ⟨hden _ hs a (by simp), ?_, ?_⟩
      · unfold lastQ
        rw [List.getLastD_cons]
        exact hden _ hs _ (getLastD_mem' (b :: rest) a)
      · exact le_of_lt (lastQ_ge_first_h6 rest a b (hden _ hs) (hcells _ hs))
  induction blocks with
  | nil => intro lo _ h; simp [chainOK] at h
  | cons s tl ih =>
      intro lo hlo h t ht1 ht2
      have hs := hpos s (by simp)
      have ih' := ih (fun x hx => hwf x (List.mem_cons_of_mem s hx))
        (fun x hx => hcells x (List.mem_cons_of_mem s hx))
      cases tl with
      | nil =>
          have h' : qeq (headQ s) lo = true ∧ qeq (lastQ s) hi = true := by
            simpa [chainOK] using h
          have e1 := qeq_val hs.1 hlo h'.1
          have e2 := qeq_val hs.2.1 hhi h'.2
          exact ⟨s, by simp, by linarith, by linarith, by linarith, by linarith⟩
      | cons s' tl' =>
          have h' : qeq (headQ s) lo = true ∧
              chainOK (lastQ s) hi (s' :: tl') = true := by
            simpa [chainOK] using h
          have e1 := qeq_val hs.1 hlo h'.1
          have hlast_le_hi := chainOK_endpoints_le_h6 hi hhi (s' :: tl')
            (fun x hx => hpos x (List.mem_cons_of_mem s hx))
            (lastQ s) hs.2.1 h'.2
          by_cases hts : t ≤ val (lastQ s)
          · exact ⟨s, by simp, by linarith, by linarith, by linarith, hts⟩
          · obtain ⟨s'', hmem, hhead, hlast, hleft, hright⟩ :=
              ih' (fun x hx => hden x (List.mem_cons_of_mem s hx))
                (fun x hx => hpos x (List.mem_cons_of_mem s hx))
                (lastQ s) hs.2.1 h'.2 t (le_of_lt (lt_of_not_ge hts)) ht2
            exact ⟨s'', List.mem_cons_of_mem s hmem, by linarith [e1, hs.2.2, hhead],
              hlast, by linarith [hs.2.2, hleft], hright⟩

theorem field_lt_of_chain_on_h6 {f : ℝ → ℝ} {ub : QF → QF → IV}
    {K lo hi : QF} (hK : 0 < K.2)
    (hub : ∀ a b : QF, 0 < a.2 → 0 < b.2 → val lo ≤ val a → val b ≤ val hi →
      val a < val b →
      ∃ U : ℝ, IV.mem (ub a b) U ∧ ∀ t, val a ≤ t → t ≤ val b → f t ≤ U)
    (hlo : 0 < lo.2) (hhi : 0 < hi.2) {blocks : List (List QF)}
    (hwf : ∀ s ∈ blocks, blockWF s = true)
    (hcells : ∀ s ∈ blocks, cellsOK ub K s = true)
    (hchain : chainOK lo hi blocks = true) :
    ∀ t, val lo ≤ t → t ≤ val hi → f t < val K := by
  intro t ht1 ht2
  obtain ⟨s, hs, hsl, hsr, hts1, hts2⟩ :=
    chainOK_cover_on_h6 hi hhi blocks hwf hcells lo hlo hchain t ht1 ht2
  have hden_block : ∀ c ∈ s, 0 < c.2 := by
    intro c hc
    have hw := hwf s hs
    unfold blockWF at hw
    rw [Bool.and_eq_true, List.all_eq_true] at hw
    exact of_decide_eq_true (hw.2 c hc)
  have hw := hwf s hs
  have hc := hcells s hs
  rcases s with _ | ⟨a, _ | ⟨b, rest⟩⟩
  · simp [blockWF] at hw
  · simp [blockWF] at hw
  · have hden_s : ∀ c ∈ a :: b :: rest, 0 < c.2 := by
      intro c hc'
      exact hden_block c hc'
    exact cellsOK_sound_on_h6 hK hub rest a b hden_s hsl hsr hc t hts1 hts2

/- Public name used by the B3 reference-package adapters.  The restricted
   hypothesis is definitionally the existing `CellSoundnessOn` predicate. -/
theorem field_lt_of_chain_on {f : ℝ → ℝ} {ub : QF → QF → IV}
    {K lo hi : QF} (hK : 0 < K.2)
    (hub : ∀ a b : QF, 0 < a.2 → 0 < b.2 → val lo ≤ val a → val b ≤ val hi →
      val a < val b →
      ∃ U : ℝ, IV.mem (ub a b) U ∧ ∀ t, val a ≤ t → t ≤ val b → f t ≤ U)
    (hlo : 0 < lo.2) (hhi : 0 < hi.2) {blocks : List (List QF)}
    (hwf : ∀ s ∈ blocks, blockWF s = true)
    (hcells : ∀ s ∈ blocks, cellsOK ub K s = true)
    (hchain : chainOK lo hi blocks = true) :
    ∀ t, val lo ≤ t → t ≤ val hi → f t < val K :=
  field_lt_of_chain_on_h6 hK hub hlo hhi hwf hcells hchain

end Li2Lean.V.EnergyCertI

#print axioms Li2Lean.V.EnergyCertI.field_lt_of_chain_on_h6
