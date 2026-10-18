/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
import ULHC.NearLemma
import ULHC.HP.GeoChainLoc
import ULHC.HP.CompCleanPF
import ULHC.HP.ChainTg
import ULHC.HP.PhantomTouch

/-!
# ULHC's `touch_outcome` for path-factors

A restricted strip `z` touching the strip `a = (c, s, k + 2)` reaches `a`'s end cell, or the cell
beyond it, or runs against `s` to a cell beside `c` (ULHC `NearLemma.lean`). Path-factor setting:
`Deg2Off`, no Type III cell away from the endpoints before (`hTR`) and after (`hT'`) the strip, the
strip count-neutral (`hneut`) and restricted (`hcor`), the cells beside `c` not Type III (`hTs`:
hypothesis E1 of `comp_clean_tg`), and `z` restricted (`hzR`).
-/

namespace ULHC

namespace HP

open Finset Classical

lemma corner_mem {V : Finset Pt} {w z : Pt} (hw : IsCell V w) (hz : IsCorner z w) : z ∈ V := by
  obtain ⟨h1, h2, h3, h4⟩ := hw
  rcases hz with rfl | rfl | rfl | rfl <;> assumption

-- The corners of a restricted strip's cells have degree 2.
--
lemma corners_deg2 {V : Finset Pt} {F : Finset Edge} {s0 t0 c : Pt} {s : Side} {k : ℕ}
    (hF : Deg2Off V F s0 t0) (hcell : ∀ j ≤ k + 1, IsCell V (cellJ c s j))
    (hcor : ∀ j ≤ k + 1, ¬ IsCorner s0 (cellJ c s j) ∧ ¬ IsCorner t0 (cellJ c s j)) :
    ∀ j ≤ k + 1, ∀ z, IsCorner z (cellJ c s j) → deg F z = 2 := by
  intro j hj z hz
  exact hF.2 z (corner_mem (hcell j hj) hz) (fun h => (hcor j hj).1 (h ▸ hz))
    (fun h => (hcor j hj).2 (h ▸ hz))

-- A cell of `V ∪ {s0, t0}` without `t0` as a corner is a cell of `V` (`s0 ∈ V`).
--
lemma cellW_V {V : Finset Pt} {s0 t0 c : Pt} (hs0 : s0 ∈ V)
    (h : IsCell (insert s0 (insert t0 V)) c) (ht : ¬ IsCorner t0 c) : IsCell V c := by
  obtain ⟨x, y⟩ := c
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨memW h1 hs0 ?_, memW h2 hs0 ?_, memW h3 hs0 ?_, memW h4 hs0 ?_⟩ <;>
    intro e <;> exact absurd (by subst e; simp [IsCorner]) ht

-- The local lemmas run over `W = V ∪ {s0, t0}` (the factor may use a phantom edge to `t0`).
-- "Not Type III" ignores the vertex set, so a hypothesis over `V` serves for the cells of `W`
-- without the phantom corner, and the phantom cells need their own fact `hph`.
--
lemma notT3W {V : Finset Pt} {F : Finset Edge} {s0 t0 c : Pt} (hs0 : s0 ∈ V)
    (h : IsCell V c → NotTypeIII V F c) (hph : IsCorner t0 c → NotTypeIII V F c) :
    IsCell (insert s0 (insert t0 V)) c → NotTypeIII (insert s0 (insert t0 V)) F c := fun hc => by
  by_cases ht : IsCorner t0 c
  · exact hph ht
  · exact h (cellW_V hs0 hc ht)

lemma restr_notT3 {V : Finset Pt} {F : Finset Edge} {s0 t0 d : Pt} (hTR : NoTypeIIIR V F s0 t0)
    (hd : IsCell V d) (hr : ¬ IsCorner s0 d ∧ ¬ IsCorner t0 d) : NotTypeIII V F d :=
  hTR d hd hr.1 hr.2

-- The cell ahead of the start cell is the strip's cell 1.
--
lemma ahead_notT3 {V : Finset Pt} {F : Finset Edge} {s0 t0 c : Pt} {s : Side} {k : ℕ}
    (hTR : NoTypeIIIR V F s0 t0) (hcell : ∀ j ≤ k + 1, IsCell V (cellJ c s j))
    (hcor : ∀ j ≤ k + 1, ¬ IsCorner s0 (cellJ c s j) ∧ ¬ IsCorner t0 (cellJ c s j))
    (hk : k % 2 = 0) : IsCell V (nb c s) → NotTypeIII V F (nb c s) := by
  intro _
  have h1 : nb c s = cellJ c s 1 := by rw [← nb_cellJ, cellJ_zero]
  rw [h1]; exact restr_notT3 hTR (hcell 1 (by omega)) (hcor 1 (by omega))

-- The corners of the square beside `e` across `latA s`: its far back corner, a corner of `e`, or
-- a corner of the square ahead of it (the next cell of a strip starting beyond `e` toward `latA s`).
--
lemma corner_besideA {t0 e : Pt} {s : Side} (h : IsCorner t0 (nb e (latA s))) :
    t0 = back1 (nb e (latA s)) s ∨ IsCorner t0 e ∨ IsCorner t0 (nb (nb e s) (latA s)) := by
  obtain ⟨x, y⟩ := e; obtain ⟨a, b⟩ := t0
  cases s <;> rcases h with h | h | h | h <;>
    simp only [nb, latA, Prod.mk.injEq] at h <;> obtain ⟨rfl, rfl⟩ := h <;>
    simp [IsCorner, nb, latA, back1]

lemma corner_besideB {t0 e : Pt} {s : Side} (h : IsCorner t0 (nb e (latB s))) :
    t0 = back2 (nb e (latB s)) s ∨ IsCorner t0 e ∨ IsCorner t0 (nb (nb e s) (latB s)) := by
  obtain ⟨x, y⟩ := e; obtain ⟨a, b⟩ := t0
  cases s <;> rcases h with h | h | h | h <;>
    simp only [nb, latB, Prod.mk.injEq] at h <;> obtain ⟨rfl, rfl⟩ := h <;>
    simp [IsCorner, nb, latB, back2]

-- **NEW MATH (phantom P2b, end side).** `beyond_cross_pf` when `t0 ∉ V`. Its proof closes except
-- where `t0` is the far back corner of the square beside the end cell (a pseudo-Type III square).
-- Without the hypothesis that `F ⊕ a` has no restricted Tg chain the statement is false (the P2b
-- configuration occurs, `runs/2026-10-15/taut/p2b_detect.py`); with it, it says that in the P2b
-- configuration `F ⊕ a` has a chain (all tested P2b states do, `rchain_p2b.py`).
--
def Gap_beyond : Prop :=
  ∀ {V : Finset Pt} {F : Finset Edge} {c : Pt} {s : Side} {k : ℕ} {s0 t0 : Pt}
    {z : Pt} {tf : Side} {m : ℕ},
    Deg2Off V F s0 t0 → s0 ∈ V → deg F s0 = 1 → (∀ z, deg F z ≤ 2) → NoTypeIIIR V F s0 t0 →
    k % 2 = 0 → (∀ j ≤ k + 1, IsCell V (cellJ c s j)) →
    (∀ j ≤ k + 1, ¬ IsCorner s0 (cellJ c s j) ∧ ¬ IsCorner t0 (cellJ c s j)) →
    StripPat F c s (k + 2) → ¬ Conn F (back1 c s) (front1 c s) →
    NoTypeIIIR V (flipCol F c s (k + 2)) s0 t0 → ncomp V (flipCol F c s (k + 2)) = ncomp V F →
    (∀ tf, (tf = latA s ∨ tf = latB s) → IsCell V (nb c tf) → NotTypeIII V F (nb c tf)) →
    (∀ tf, (tf = latA s ∨ tf = latB s) → IsCell V (nb (cellJ c s (k + 1)) tf) →
      NotTypeIII V (flipCol F c s (k + 2)) (nb (cellJ c s (k + 1)) tf)) →
    StripPat F z tf m → (∀ j < m, ¬ IsCorner s0 (cellJ z tf j) ∧ ¬ IsCorner t0 (cellJ z tf j)) →
    (tf = latA s ∨ tf = latB s) → z = nb (cellJ c s (k + 1)) s → 2 ≤ m →
    ¬ PDang V t0 → (¬ ∃ σ L', RPathTg V (flipCol F c s (k + 2)) s0 t0 σ L') → t0 ∉ V → False

-- The endpoint `t0` is in `V`, or the P2b gap holds (phantom endpoints).
--
class NearOK1 (V : Finset Pt) (t0 : Pt) : Prop where
  ok : t0 ∈ V ∨ PDang V t0 ∨ Gap_beyond

section classifyW

variable {V : Finset Pt} {F : Finset Edge} {c : Pt} {s : Side} {k : ℕ}
  (hs : Solid V) (x0 : Pt) (hconn : ∀ z ∈ V, Conn (GE V) x0 z)
  {s0 t0 : Pt} (hF : Deg2Off V F s0 t0) (hs0 : s0 ∈ V) (hds : deg F s0 = 1)
  (hle : ∀ z, deg F z ≤ 2) (hTR : NoTypeIIIR V F s0 t0) (hk : k % 2 = 0)
  (hcell : ∀ j ≤ k + 1, IsCell V (cellJ c s j))
  (hcor : ∀ j ≤ k + 1, ¬ IsCorner s0 (cellJ c s j) ∧ ¬ IsCorner t0 (cellJ c s j))
  (hpat : StripPat F c s (k + 2))
  (hsep : ¬ Conn F (back1 c s) (front1 c s)) (hT' : NoTypeIIIR V (flipCol F c s (k + 2)) s0 t0)
  (hneut : ncomp V (flipCol F c s (k + 2)) = ncomp V F)
  (hTs : ∀ tf, (tf = latA s ∨ tf = latB s) → IsCell V (nb c tf) → NotTypeIII V F (nb c tf))
  -- PHANTOM-T: a phantom cell beside `c` (one with `t0` as a corner) is not Type III.
  (hTsP : ∀ tf, (tf = latA s ∨ tf = latB s) → IsCorner t0 (nb c tf) → NotTypeIII V F (nb c tf))
  {z : Pt} {tf : Side} {m i0 : ℕ} (hzw : SigFrom F z tf m i0)
  (hzR : ∀ j < m, ¬ IsCorner s0 (cellJ z tf j) ∧ ¬ IsCorner t0 (cellJ z tf j))
include hF hs0 hds hle hTR hk hcell hcor hpat hsep hT' hneut hTs hTsP hzw hzR

omit hle in
-- `touch_outcome` for a pattern holding from index `i0`, reporting indices from the touching
-- one on.
--
theorem touch_outcomeW_pf {i j : ℕ} (hi0 : i0 ≤ i) (hi : i < m) (hj : j < k + 2) {x : Edge}
    (hx1 : x ∈ cellE (cellJ z tf i)) (hx2 : x ∈ cellE (cellJ c s j)) :
    (∃ i', i ≤ i' ∧ i' < m ∧ cellJ z tf i' = cellJ c s (k + 1)) ∨
      (∃ i', i ≤ i' ∧ i' < m ∧ cellJ z tf i' = nb (cellJ c s (k + 1)) s) ∨
      (tf = s.opp ∧ ∃ ie, i ≤ ie ∧ ie < m ∧ ie % 2 = 0 ∧
        (cellJ z tf ie = nb c (latA s) ∨ cellJ z tf ie = nb c (latB s))) := by
  have hDc := corners_deg2 hF hcell hcor
  have hTr := ahead_notT3 hTR hcell hcor hk
  have hcellW : ∀ j ≤ k + 1, IsCell (insert s0 (insert t0 V)) (cellJ c s j) :=
    fun j hj => isCell_mono (hcell j hj) (sub_insST V s0 t0)
  have hTrW := notT3W (t0 := t0) hs0 hTr (fun ht => absurd
    (show IsCorner t0 (cellJ c s 1) by rw [← nb_cellJ, cellJ_zero]; exact ht) (hcor 1 (by omega)).2)
  have hTsW := fun tf htf => notT3W (t0 := t0) hs0 (hTs tf htf) (hTsP tf htf)
  have hTe : NotTypeIII V F (cellJ c s (k + 1)) := restr_notT3 hTR (hcell (k + 1) le_rfl) (hcor (k + 1) le_rfl)
  have hsame := end_same_loc hTe hk hcell hpat
  have re : ∀ i' j', i ≤ i' → i' < m → j' ≤ k + 1 → cellJ z tf i' = cellJ c s j' →
      ∃ i'', i ≤ i'' ∧ i'' < m ∧ cellJ z tf i'' = cellJ c s (k + 1) := fun i' j' hii hi' hj' hq => by
    obtain ⟨i'', h0, h1, h2⟩ := reach_end_L hk hpat hzw (k + 1 - j') i' j' (by omega) (by omega) hi' hq
    exact ⟨i'', by omega, h1, h2⟩
  rcases touch_cases s hx1 hx2 with hq | hq | hq | hq | hq
  · exact Or.inl (re i j le_rfl hi (by omega) hq)
  · by_cases hjk : j ≤ k
    · exact Or.inl (re i (j + 1) le_rfl hi (by omega) (by rw [hq, nb_cellJ]))
    · exact Or.inr (Or.inl ⟨i, le_rfl, hi, by rw [hq, show j = k + 1 by omega]⟩)
  · rcases j with _ | j
    · rw [cellJ_zero] at hq
      obtain ⟨ht, _, hi1⟩ := touch_behind_L hF.1 hDc hTsW hTrW hk hcellW hpat hsep hzw hi0 hi hq
      refine Or.inl (re (i + 1) 0 (by omega) hi1 (by omega) ?_)
      rw [← nb_cellJ, hq, ht, behind_up, cellJ_zero]
    · exact Or.inl (re i j le_rfl hi (by omega) (by rw [hq, cellJ_down]))
  · by_cases hjk : j ≤ k
    · obtain ⟨ht, ie, hle, h1, h2, h3⟩ := side_chain1_L hF.1 hDc hTsW hk hcellW hpat hsep hzw j i hjk hi0 hi hq
      exact Or.inr (Or.inr ⟨ht, ie, hle, h1, h2, Or.inl h3⟩)
    · obtain rfl : j = k + 1 := by omega
      rcases touch_side1_end_L hDc hk hpat hzw hi0 hi hq with ⟨ht, _, hi1⟩ | ⟨_, hf, hl⟩
      · obtain ⟨ht', ie, hle, h1, h2, h3⟩ := side_chain1_L hF.1 hDc hTsW hk hcellW hpat hsep hzw k (i + 1) le_rfl (by omega)
          hi1 (by rw [← nb_cellJ, hq, ht, side1_down])
        exact Or.inr (Or.inr ⟨ht', ie, by omega, h1, h2, Or.inl h3⟩)
      · obtain ⟨hcL, hnot⟩ := beside_end1_pf hF hs0 hds hk hcell hcor hpat hsep hsame hneut
          ((outer1_body_L hDc hpat le_rfl).2 hk) hf hl (by rw [← hq]; exact (hzR i hi).2)
        rw [← hq] at hcL hnot
        exact (hnot (hT' _ hcL (hzR i hi).1 (hzR i hi).2)).elim
  · by_cases hjk : j ≤ k
    · obtain ⟨ht, ie, hle, h1, h2, h3⟩ := side_chain2_L hF.1 hDc hTsW hTrW hk hcellW hpat hsep hzw j i hjk hi0 hi hq
      exact Or.inr (Or.inr ⟨ht, ie, hle, h1, h2, Or.inr h3⟩)
    · obtain rfl : j = k + 1 := by omega
      rcases touch_side2_end_L hDc hk hpat hzw hi0 hi hq with ⟨ht, _, hi1⟩ | ⟨_, hf, hl⟩
      · obtain ⟨ht', ie, hle, h1, h2, h3⟩ := side_chain2_L hF.1 hDc hTsW hTrW hk hcellW hpat hsep hzw k (i + 1) le_rfl (by omega)
          hi1 (by rw [← nb_cellJ, hq, ht, side2_down])
        exact Or.inr (Or.inr ⟨ht', ie, by omega, h1, h2, Or.inr h3⟩)
      · obtain ⟨hcL, hnot⟩ := beside_end2_pf hF hs0 hds hk hcell hcor hpat hsep hsame hneut
          ((outer2_body_L hDc hpat le_rfl).2 hk) hf hl (by rw [← hq]; exact (hzR i hi).2)
        rw [← hq] at hcL hnot
        exact (hnot (hT' _ hcL (hzR i hi).1 (hzR i hi).2)).elim

omit hTsP hle in
-- **`touch_outcome` at a phantom start (configuration A).** The strip `a` starts on the
-- endpoint's edge: the square beside `c` across `latA` is no cell (it has the missing point as a
-- corner), the side of the cell behind `c` under `back1 c` is light, and the square beside that
-- cell is no cell either. The hypothesis `hTsP` on the phantom side is not needed (it is false
-- here); the touching strip's cells are cells of `V` (`hzc`). Then a touching strip reaches the
-- end cell or the cell beyond it, or runs against `s` to the cell beside `c` across `latB`: the
-- side across `latA` is never reached.
--
theorem touch_outcomeW_pfA
    (hTsPB : IsCorner t0 (nb c (latB s)) → NotTypeIII V F (nb c (latB s)))
    (hzc : ∀ j < m, IsCell V (cellJ z tf j))
    (hL0 : ¬ IsCell V (nb c (latA s)))
    (hbeh : ∀ i, i0 ≤ i → i < m → cellJ z tf i = nb c s.opp → False)
    {i j : ℕ} (hi0 : i0 ≤ i) (hi : i < m) (hj : j < k + 2) {x : Edge}
    (hx1 : x ∈ cellE (cellJ z tf i)) (hx2 : x ∈ cellE (cellJ c s j)) :
    (∃ i', i ≤ i' ∧ i' < m ∧ cellJ z tf i' = cellJ c s (k + 1)) ∨
      (∃ i', i ≤ i' ∧ i' < m ∧ cellJ z tf i' = nb (cellJ c s (k + 1)) s) ∨
      (tf = s.opp ∧ ∃ ie, i ≤ ie ∧ ie < m ∧ ie % 2 = 0 ∧ cellJ z tf ie = nb c (latB s)) := by
  have hDc := corners_deg2 hF hcell hcor
  have hTr := ahead_notT3 hTR hcell hcor hk
  have hTrW := notT3W (t0 := t0) hs0 hTr (fun ht => absurd
    (show IsCorner t0 (cellJ c s 1) by rw [← nb_cellJ, cellJ_zero]; exact ht) (hcor 1 (by omega)).2)
  have hTsWB := notT3W (t0 := t0) hs0 (hTs (latB s) (Or.inr rfl)) hTsPB
  have hc0 : IsCell V c := by have := hcell 0 (by omega); rwa [cellJ_zero] at this
  have hc0W := isCell_mono hc0 (sub_insST V s0 t0)
  have hd0 : ∀ z, IsCorner z c → deg F z = 2 := fun z hz => hDc 0 (by omega) z (by rw [cellJ_zero]; exact hz)
  have hTe : NotTypeIII V F (cellJ c s (k + 1)) := restr_notT3 hTR (hcell (k + 1) le_rfl) (hcor (k + 1) le_rfl)
  have hsame := end_same_loc hTe hk hcell hpat
  -- The side facts across `latB`, at every cell beside the body.
  --
  have hfB : ∀ j ≤ k, (lat1 (nb (cellJ c s j) (latB s)) s ∈ F ↔ j % 2 = 1) ∧
      (back (nb (cellJ c s j) (latB s)) s ∈ F ↔ j % 2 = 1) ∧
      (front (nb (cellJ c s j) (latB s)) s ∈ F ↔ j % 2 = 0) := by
    intro j hj
    rcases Nat.eq_zero_or_pos j with rfl | hj1
    · refine ⟨by rw [side2_lat1]; exact (strip_sig hpat (show 0 < k + 2 by omega)).2.1, ?_, ?_⟩
      · rw [cellJ_zero]
        simp only [Nat.zero_mod, zero_ne_one, iff_false]
        exact back_outer2_light_loc hF.1 hpat (by omega) hc0W hsep (hd0 _ (isCorner_front1 c s))
          (hd0 _ (isCorner_front2 c s)) hTrW hTsWB
      · rw [side2_front]; exact outer2_body_L hDc hpat hj
    · exact side2_facts_succ hDc hpat hj1 hj
  have re : ∀ i' j', i ≤ i' → i' < m → j' ≤ k + 1 → cellJ z tf i' = cellJ c s j' →
      ∃ i'', i ≤ i'' ∧ i'' < m ∧ cellJ z tf i'' = cellJ c s (k + 1) := fun i' j' hii hi' hj' hq => by
    obtain ⟨i'', h0, h1, h2⟩ := reach_end_L hk hpat hzw (k + 1 - j') i' j' (by omega) (by omega) hi' hq
    exact ⟨i'', by omega, h1, h2⟩
  rcases touch_cases s hx1 hx2 with hq | hq | hq | hq | hq
  · exact Or.inl (re i j le_rfl hi (by omega) hq)
  · by_cases hjk : j ≤ k
    · exact Or.inl (re i (j + 1) le_rfl hi (by omega) (by rw [hq, nb_cellJ]))
    · exact Or.inr (Or.inl ⟨i, le_rfl, hi, by rw [hq, show j = k + 1 by omega]⟩)
  · rcases j with _ | j
    · rw [cellJ_zero] at hq
      exact (hbeh i hi0 hi hq).elim
    · exact Or.inl (re i j le_rfl hi (by omega) (by rw [hq, cellJ_down]))
  · exfalso
    by_cases hjk : j ≤ k
    · exact side_chain1_noncell hDc hcell hpat hL0 hzw hzc j i hjk hi0 hi hq
    · obtain rfl : j = k + 1 := by omega
      rcases touch_side1_end_L hDc hk hpat hzw hi0 hi hq with ⟨ht, _, hi1⟩ | ⟨_, hf, hl⟩
      · exact side_chain1_noncell hDc hcell hpat hL0 hzw hzc k (i + 1) le_rfl (by omega) hi1
          (by rw [← nb_cellJ, hq, ht, side1_down])
      · obtain ⟨hcL, hnot⟩ := beside_end1_pf hF hs0 hds hk hcell hcor hpat hsep hsame hneut
          ((outer1_body_L hDc hpat le_rfl).2 hk) hf hl (by rw [← hq]; exact (hzR i hi).2)
        rw [← hq] at hcL hnot
        exact hnot (hT' _ hcL (hzR i hi).1 (hzR i hi).2)
  · by_cases hjk : j ≤ k
    · obtain ⟨ht, ie, hle, h1, h2⟩ := side_chain2_of_facts hfB hzw j i hjk hi0 hi hq
      exact Or.inr (Or.inr ⟨ht, ie, hle, h1, h2⟩)
    · obtain rfl : j = k + 1 := by omega
      rcases touch_side2_end_L hDc hk hpat hzw hi0 hi hq with ⟨ht, _, hi1⟩ | ⟨_, hf, hl⟩
      · obtain ⟨ht', ie, hle, h1, h2⟩ := side_chain2_of_facts hfB hzw k (i + 1) le_rfl (by omega)
          hi1 (by rw [← nb_cellJ, hq, ht, side2_down])
        exact Or.inr (Or.inr ⟨ht', ie, by omega, h1, h2⟩)
      · obtain ⟨hcL, hnot⟩ := beside_end2_pf hF hs0 hds hk hcell hcor hpat hsep hsame hneut
          ((outer2_body_L hDc hpat le_rfl).2 hk) hf hl (by rw [← hq]; exact (hzR i hi).2)
        rw [← hq] at hcL hnot
        exact (hnot (hT' _ hcL (hzR i hi).1 (hzR i hi).2)).elim

omit hTsP hle in
-- **`touch_outcome` at a phantom start across `latB`** (mirror of `touch_outcomeW_pfA`): the
-- square beside `c` across `latB` is no cell, and no strip passes through the cell behind `c`.
--
theorem touch_outcomeW_pfAB
    (hTsPA : IsCorner t0 (nb c (latA s)) → NotTypeIII V F (nb c (latA s)))
    (hzc : ∀ j < m, IsCell V (cellJ z tf j))
    (hL0 : ¬ IsCell V (nb c (latB s)))
    (hbeh : ∀ i, i0 ≤ i → i < m → cellJ z tf i = nb c s.opp → False)
    {i j : ℕ} (hi0 : i0 ≤ i) (hi : i < m) (hj : j < k + 2) {x : Edge}
    (hx1 : x ∈ cellE (cellJ z tf i)) (hx2 : x ∈ cellE (cellJ c s j)) :
    (∃ i', i ≤ i' ∧ i' < m ∧ cellJ z tf i' = cellJ c s (k + 1)) ∨
      (∃ i', i ≤ i' ∧ i' < m ∧ cellJ z tf i' = nb (cellJ c s (k + 1)) s) ∨
      (tf = s.opp ∧ ∃ ie, i ≤ ie ∧ ie < m ∧ ie % 2 = 0 ∧ cellJ z tf ie = nb c (latA s)) := by
  have hDc := corners_deg2 hF hcell hcor
  have hTr := ahead_notT3 hTR hcell hcor hk
  have hTsWA := notT3W (t0 := t0) hs0 (hTs (latA s) (Or.inl rfl)) hTsPA
  have hd0 : ∀ z, IsCorner z c → deg F z = 2 := fun z hz => hDc 0 (by omega) z (by rw [cellJ_zero]; exact hz)
  have hTe : NotTypeIII V F (cellJ c s (k + 1)) := restr_notT3 hTR (hcell (k + 1) le_rfl) (hcor (k + 1) le_rfl)
  have hsame := end_same_loc hTe hk hcell hpat
  -- The side facts across `latA`, at every cell beside the body.
  --
  have hfA : ∀ j ≤ k, (lat2 (nb (cellJ c s j) (latA s)) s ∈ F ↔ j % 2 = 1) ∧
      (back (nb (cellJ c s j) (latA s)) s ∈ F ↔ j % 2 = 1) ∧
      (front (nb (cellJ c s j) (latA s)) s ∈ F ↔ j % 2 = 0) := by
    intro j hj
    rcases Nat.eq_zero_or_pos j with rfl | hj1
    · refine ⟨by rw [side_lat2]; exact (strip_sig hpat (show 0 < k + 2 by omega)).1, ?_, ?_⟩
      · rw [cellJ_zero]
        simp only [Nat.zero_mod, zero_ne_one, iff_false]
        exact back_outer_light_loc hF.1 hpat (by omega) hsep (hd0 _ (isCorner_front1 c s)) hTsWA
      · rw [side_front]; exact outer1_body_L hDc hpat hj
    · exact side1_facts_succ hDc hpat hj1 hj
  have re : ∀ i' j', i ≤ i' → i' < m → j' ≤ k + 1 → cellJ z tf i' = cellJ c s j' →
      ∃ i'', i ≤ i'' ∧ i'' < m ∧ cellJ z tf i'' = cellJ c s (k + 1) := fun i' j' hii hi' hj' hq => by
    obtain ⟨i'', h0, h1, h2⟩ := reach_end_L hk hpat hzw (k + 1 - j') i' j' (by omega) (by omega) hi' hq
    exact ⟨i'', by omega, h1, h2⟩
  rcases touch_cases s hx1 hx2 with hq | hq | hq | hq | hq
  · exact Or.inl (re i j le_rfl hi (by omega) hq)
  · by_cases hjk : j ≤ k
    · exact Or.inl (re i (j + 1) le_rfl hi (by omega) (by rw [hq, nb_cellJ]))
    · exact Or.inr (Or.inl ⟨i, le_rfl, hi, by rw [hq, show j = k + 1 by omega]⟩)
  · rcases j with _ | j
    · rw [cellJ_zero] at hq
      exact (hbeh i hi0 hi hq).elim
    · exact Or.inl (re i j le_rfl hi (by omega) (by rw [hq, cellJ_down]))
  · by_cases hjk : j ≤ k
    · obtain ⟨ht, ie, hle, h1, h2⟩ := side_chain1_of_facts hfA hzw j i hjk hi0 hi hq
      exact Or.inr (Or.inr ⟨ht, ie, hle, h1, h2⟩)
    · obtain rfl : j = k + 1 := by omega
      rcases touch_side1_end_L hDc hk hpat hzw hi0 hi hq with ⟨ht, _, hi1⟩ | ⟨_, hf, hl⟩
      · obtain ⟨ht', ie, hle, h1, h2⟩ := side_chain1_of_facts hfA hzw k (i + 1) le_rfl (by omega)
          hi1 (by rw [← nb_cellJ, hq, ht, side1_down])
        exact Or.inr (Or.inr ⟨ht', ie, by omega, h1, h2⟩)
      · obtain ⟨hcL, hnot⟩ := beside_end1_pf hF hs0 hds hk hcell hcor hpat hsep hsame hneut
          ((outer1_body_L hDc hpat le_rfl).2 hk) hf hl (by rw [← hq]; exact (hzR i hi).2)
        rw [← hq] at hcL hnot
        exact (hnot (hT' _ hcL (hzR i hi).1 (hzR i hi).2)).elim
  · exfalso
    by_cases hjk : j ≤ k
    · exact side_chain2_noncell hDc hcell hpat hL0 hzw hzc j i hjk hi0 hi hq
    · obtain rfl : j = k + 1 := by omega
      rcases touch_side2_end_L hDc hk hpat hzw hi0 hi hq with ⟨ht, _, hi1⟩ | ⟨_, hf, hl⟩
      · exact side_chain2_noncell hDc hcell hpat hL0 hzw hzc k (i + 1) le_rfl (by omega) hi1
          (by rw [← nb_cellJ, hq, ht, side2_down])
      · obtain ⟨hcL, hnot⟩ := beside_end2_pf hF hs0 hds hk hcell hcor hpat hsep hsame hneut
          ((outer2_body_L hDc hpat le_rfl).2 hk) hf hl (by rw [← hq]; exact (hzR i hi).2)
        rw [← hq] at hcL hnot
        exact hnot (hT' _ hcL (hzR i hi).1 (hzR i hi).2)

end classifyW

section classify

variable {V : Finset Pt} {F : Finset Edge} {c : Pt} {s : Side} {k : ℕ}
  (hs : Solid V) (x0 : Pt) (hconn : ∀ z ∈ V, Conn (GE V) x0 z)
  {s0 t0 : Pt} (hF : Deg2Off V F s0 t0) (hs0 : s0 ∈ V) (hds : deg F s0 = 1)
  (hle : ∀ z, deg F z ≤ 2) (hTR : NoTypeIIIR V F s0 t0) (hk : k % 2 = 0)
  (hcell : ∀ j ≤ k + 1, IsCell V (cellJ c s j))
  (hcor : ∀ j ≤ k + 1, ¬ IsCorner s0 (cellJ c s j) ∧ ¬ IsCorner t0 (cellJ c s j))
  (hpat : StripPat F c s (k + 2))
  (hsep : ¬ Conn F (back1 c s) (front1 c s)) (hT' : NoTypeIIIR V (flipCol F c s (k + 2)) s0 t0)
  (hneut : ncomp V (flipCol F c s (k + 2)) = ncomp V F)
  (hTs : ∀ tf, (tf = latA s ∨ tf = latB s) → IsCell V (nb c tf) → NotTypeIII V F (nb c tf))
  -- PHANTOM-T: a phantom cell beside `c` (one with `t0` as a corner) is not Type III.
  (hTsP : ∀ tf, (tf = latA s ∨ tf = latB s) → IsCorner t0 (nb c tf) → NotTypeIII V F (nb c tf))
  -- E2 of comp_clean: the cells beside `a`'s end cell are not Type III after `a`.
  (hTend : ∀ tf, (tf = latA s ∨ tf = latB s) → IsCell V (nb (cellJ c s (k + 1)) tf) →
    NotTypeIII V (flipCol F c s (k + 2)) (nb (cellJ c s (k + 1)) tf))
  {z : Pt} {tf : Side} {m : ℕ} (hz : StripPat F z tf m)
  (hzR : ∀ j < m, ¬ IsCorner s0 (cellJ z tf j) ∧ ¬ IsCorner t0 (cellJ z tf j))
include hF hs0 hds hle hTR hk hcell hcor hpat hsep hT' hneut hTs hTsP hTend hz hzR

omit hle hTend in
-- A strip touching `a` reaches the end cell, or the cell beyond it, or runs against `s`
-- to a cell beside `c_0`, which it meets at an even index.
--
theorem touch_outcome_pf {i j : ℕ} (hi : i < m) (hj : j < k + 2) {x : Edge}
    (hx1 : x ∈ cellE (cellJ z tf i)) (hx2 : x ∈ cellE (cellJ c s j)) :
    (∃ i' < m, cellJ z tf i' = cellJ c s (k + 1)) ∨
      (∃ i' < m, cellJ z tf i' = nb (cellJ c s (k + 1)) s) ∨
      (tf = s.opp ∧ ∃ i0 < m, i0 % 2 = 0 ∧
        (cellJ z tf i0 = nb c (latA s) ∨ cellJ z tf i0 = nb c (latB s))) := by
  have hDc := corners_deg2 hF hcell hcor
  have hTr := ahead_notT3 hTR hcell hcor hk
  have hcellW : ∀ j ≤ k + 1, IsCell (insert s0 (insert t0 V)) (cellJ c s j) :=
    fun j hj => isCell_mono (hcell j hj) (sub_insST V s0 t0)
  have hTrW := notT3W (t0 := t0) hs0 hTr (fun ht => absurd
    (show IsCorner t0 (cellJ c s 1) by rw [← nb_cellJ, cellJ_zero]; exact ht) (hcor 1 (by omega)).2)
  have hTsW := fun tf htf => notT3W (t0 := t0) hs0 (hTs tf htf) (hTsP tf htf)
  have hTe : NotTypeIII V F (cellJ c s (k + 1)) := restr_notT3 hTR (hcell (k + 1) le_rfl) (hcor (k + 1) le_rfl)
  have hsame := end_same_loc hTe hk hcell hpat
  have re : ∀ i' j', i' < m → j' ≤ k + 1 → cellJ z tf i' = cellJ c s j' →
      ∃ i'' < m, cellJ z tf i'' = cellJ c s (k + 1) := fun i' j' hi' hj' hq => by
    obtain ⟨i'', -, h1, h2⟩ := reach_end_L hk hpat (sig_of_pat hz) (k + 1 - j') i' j' (by omega) (Nat.zero_le _) hi' hq
    exact ⟨i'', h1, h2⟩
  rcases touch_cases s hx1 hx2 with hq | hq | hq | hq | hq
  · exact Or.inl (re i j hi (by omega) hq)
  · by_cases hjk : j ≤ k
    · exact Or.inl (re i (j + 1) hi (by omega) (by rw [hq, nb_cellJ]))
    · exact Or.inr (Or.inl ⟨i, hi, by rw [hq, show j = k + 1 by omega]⟩)
  · rcases j with _ | j
    · rw [cellJ_zero] at hq
      obtain ⟨ht, _, hi1⟩ := touch_behind_L hF.1 hDc hTsW hTrW hk hcellW hpat hsep (sig_of_pat hz) (Nat.zero_le _) hi hq
      refine Or.inl (re (i + 1) 0 hi1 (by omega) ?_)
      rw [← nb_cellJ, hq, ht, behind_up, cellJ_zero]
    · exact Or.inl (re i j hi (by omega) (by rw [hq, cellJ_down]))
  · by_cases hjk : j ≤ k
    · obtain ⟨ht, i0, -, h1, h2, h3⟩ := side_chain1_L hF.1 hDc hTsW hk hcellW hpat hsep (sig_of_pat hz) j i hjk (Nat.zero_le _) hi hq
      exact Or.inr (Or.inr ⟨ht, i0, h1, h2, Or.inl h3⟩)
    · obtain rfl : j = k + 1 := by omega
      rcases touch_side1_end_L hDc hk hpat (sig_of_pat hz) (Nat.zero_le _) hi hq with ⟨ht, _, hi1⟩ | ⟨_, hf, hl⟩
      · obtain ⟨ht', i0, -, h1, h2, h3⟩ := side_chain1_L hF.1 hDc hTsW hk hcellW hpat hsep (sig_of_pat hz) k (i + 1) le_rfl (Nat.zero_le _)
          hi1 (by rw [← nb_cellJ, hq, ht, side1_down])
        exact Or.inr (Or.inr ⟨ht', i0, h1, h2, Or.inl h3⟩)
      · obtain ⟨hcL, hnot⟩ := beside_end1_pf hF hs0 hds hk hcell hcor hpat hsep hsame hneut
          ((outer1_body_L hDc hpat le_rfl).2 hk) hf hl (by rw [← hq]; exact (hzR i hi).2)
        rw [← hq] at hcL hnot
        exact (hnot (hT' _ hcL (hzR i hi).1 (hzR i hi).2)).elim
  · by_cases hjk : j ≤ k
    · obtain ⟨ht, i0, -, h1, h2, h3⟩ := side_chain2_L hF.1 hDc hTsW hTrW hk hcellW hpat hsep (sig_of_pat hz) j i hjk (Nat.zero_le _) hi hq
      exact Or.inr (Or.inr ⟨ht, i0, h1, h2, Or.inr h3⟩)
    · obtain rfl : j = k + 1 := by omega
      rcases touch_side2_end_L hDc hk hpat (sig_of_pat hz) (Nat.zero_le _) hi hq with ⟨ht, _, hi1⟩ | ⟨_, hf, hl⟩
      · obtain ⟨ht', i0, -, h1, h2, h3⟩ := side_chain2_L hF.1 hDc hTsW hTrW hk hcellW hpat hsep (sig_of_pat hz) k (i + 1) le_rfl (Nat.zero_le _)
          hi1 (by rw [← nb_cellJ, hq, ht, side2_down])
        exact Or.inr (Or.inr ⟨ht', i0, h1, h2, Or.inr h3⟩)
      · obtain ⟨hcL, hnot⟩ := beside_end2_pf hF hs0 hds hk hcell hcor hpat hsep hsame hneut
          ((outer2_body_L hDc hpat le_rfl).2 hk) hf hl (by rw [← hq]; exact (hzR i hi).2)
        rw [← hq] at hcL hnot
        exact (hnot (hT' _ hcL (hzR i hi).1 (hzR i hi).2)).elim

omit hTsP hTend hle in
-- **`touch_outcome` at a phantom start (configuration A)**, from `touch_outcomeW_pfA`.
--
theorem touch_outcome_pfA
    (hTsPB : IsCorner t0 (nb c (latB s)) → NotTypeIII V F (nb c (latB s)))
    (hzc : ∀ j < m, IsCell V (cellJ z tf j))
    (hL0 : ¬ IsCell V (nb c (latA s)))
    (hbeh : ∀ i < m, cellJ z tf i = nb c s.opp → False)
    {i j : ℕ} (hi : i < m) (hj : j < k + 2) {x : Edge}
    (hx1 : x ∈ cellE (cellJ z tf i)) (hx2 : x ∈ cellE (cellJ c s j)) :
    (∃ i' < m, cellJ z tf i' = cellJ c s (k + 1)) ∨
      (∃ i' < m, cellJ z tf i' = nb (cellJ c s (k + 1)) s) ∨
      (tf = s.opp ∧ ∃ i0 < m, i0 % 2 = 0 ∧ cellJ z tf i0 = nb c (latB s)) := by
  rcases touch_outcomeW_pfA hF hs0 hds hTR hk hcell hcor hpat hsep hT' hneut hTs (sig_of_pat hz) hzR
      hTsPB hzc hL0 (fun i' _ h1 hq => hbeh i' h1 hq) (Nat.zero_le i) hi hj hx1 hx2 with
    ⟨i', _, h1, h2⟩ | ⟨i', _, h1, h2⟩ | ⟨ht, ie, _, h1, h2, h3⟩
  · exact Or.inl ⟨i', h1, h2⟩
  · exact Or.inr (Or.inl ⟨i', h1, h2⟩)
  · exact Or.inr (Or.inr ⟨ht, ie, h1, h2, h3⟩)

omit hz hzR hds hle hT' hneut hTend in
-- The only alternating cells sharing a side with `a` are the end cell and the cell beyond.
--
theorem alt_touch_pf {w : Pt} {tw : Side} (l1 : lat1 w tw ∈ F) (l2 : lat2 w tw ∈ F)
    (bw : back w tw ∉ F) (fw : front w tw ∉ F) {j : ℕ} (hj : j < k + 2) {x : Edge}
    (hx1 : x ∈ cellE w) (hx2 : x ∈ cellE (cellJ c s j)) :
    w = cellJ c s (k + 1) ∨ w = nb (cellJ c s (k + 1)) s := by
  have hDc := corners_deg2 hF hcell hcor
  have hTr := ahead_notT3 hTR hcell hcor hk
  have hcellW : ∀ j ≤ k + 1, IsCell (insert s0 (insert t0 V)) (cellJ c s j) :=
    fun j hj => isCell_mono (hcell j hj) (sub_insST V s0 t0)
  have hTrW := notT3W (t0 := t0) hs0 hTr (fun ht => absurd
    (show IsCorner t0 (cellJ c s 1) by rw [← nb_cellJ, cellJ_zero]; exact ht) (hcor 1 (by omega)).2)
  have hTsW := fun tf htf => notT3W (t0 := t0) hs0 (hTs tf htf) (hTsP tf htf)
  have hTe : NotTypeIII V F (cellJ c s (k + 1)) := restr_notT3 hTR (hcell (k + 1) le_rfl) (hcor (k + 1) le_rfl)
  have hsame := end_same_loc hTe hk hcell hpat
  have af := alt_frame s l1 l2 bw fw
  have body : ∀ j' ≤ k + 1, w = cellJ c s j' → w = cellJ c s (k + 1) := by
    intro j' hj' hw
    by_cases h : j' = k + 1
    · rw [hw, h]
    · rw [hw] at l1 l2 bw fw
      exact (ULHC.body_not_alt hk hpat (by omega) l1 l2 bw fw).elim
  rcases touch_cases s hx1 hx2 with hq | hq | hq | hq | hq
  · exact Or.inl (body j (by omega) hq)
  · by_cases hjk : j ≤ k
    · exact Or.inl (body (j + 1) (by omega) (by rw [hq, nb_cellJ]))
    · exact Or.inr (by rw [hq, show j = k + 1 by omega])
  · rcases j with _ | j
    · exfalso
      rw [cellJ_zero] at hq
      have hc0 : IsCell V c := by have := hcell 0 (by omega); rwa [cellJ_zero] at this
      have hd0 : ∀ z, IsCorner z c → deg F z = 2 := fun z hz => hDc 0 (by omega) z (by rw [cellJ_zero]; exact hz)
      have d1 := back_down_loc hF.1 hpat (by omega) hsep (hd0 _ (isCorner_back1 c s)) (hd0 _ (isCorner_front1 c s)) (hTsW (latA s) (Or.inl rfl))
      have df : front (nb c s.opp) s ∈ F := by rw [front_nb_opp]; exact hpat.1
      rw [← hq] at d1 df
      have := af.2.2; have := af.1; tauto
    · exact Or.inl (body j (by omega) (by rw [hq, cellJ_down]))
  · exfalso
    by_cases hjk : j ≤ k
    · obtain ⟨_, fb, ff⟩ := side1_facts_L hF.1 hDc hTsW hk hcellW hpat hsep hjk
      rw [← hq] at fb ff
      have := af.1; rw [fb, ff] at this; omega
    · obtain rfl : j = k + 1 := by omega
      have fn : lat2 w s ∈ F := by
        rw [hq, side_lat2]; exact (strip_sig hpat (show k + 1 < k + 2 by omega)).1.2 (by omega)
      have fb : back w s ∈ F := by
        rw [hq, show back (nb (cellJ c s (k + 1)) (latA s)) s = outer1 (cellJ c s k) s by
          rw [← side_back_next, nb_cellJ]]
        exact (outer1_body_L hDc hpat le_rfl).2 hk
      have := af.2.1; have := af.2.2; tauto
  · exfalso
    by_cases hjk : j ≤ k
    · obtain ⟨_, fb, ff⟩ := side2_facts_L hF.1 hDc hTsW hTrW hk hcellW hpat hsep hjk
      rw [← hq] at fb ff
      have := af.1; rw [fb, ff] at this; omega
    · obtain rfl : j = k + 1 := by omega
      have fn : lat1 w s ∈ F := by
        rw [hq, side2_lat1]; exact (strip_sig hpat (show k + 1 < k + 2 by omega)).2.1.2 (by omega)
      have fb : back w s ∈ F := by
        rw [hq, show back (nb (cellJ c s (k + 1)) (latB s)) s = outer2 (cellJ c s k) s by
          rw [outer2_side_nb_next, nb_cellJ]; rfl]
        exact (outer2_body_L hDc hpat le_rfl).2 hk
      have := af.2.1; have := af.2.2; tauto

omit hz hzR hTsP hds hle hT' hneut hTend in
-- **`alt_touch` at a phantom start (configuration A)**, without `hTsP`: the alternating cell is a
-- cell of `V`, so it is not the square beside the start; the cell behind the start has one light
-- and one dark lateral side, so it is not alternating.
--
theorem alt_touch_pfA
    (hTsPB : IsCorner t0 (nb c (latB s)) → NotTypeIII V F (nb c (latB s)))
    (hL0 : ¬ IsCell V (nb c (latA s))) (hn1 : lat1 (nb c s.opp) s ∉ F)
    {w : Pt} {tw : Side} (hwc : IsCell V w) (l1 : lat1 w tw ∈ F) (l2 : lat2 w tw ∈ F)
    (bw : back w tw ∉ F) (fw : front w tw ∉ F) {j : ℕ} (hj : j < k + 2) {x : Edge}
    (hx1 : x ∈ cellE w) (hx2 : x ∈ cellE (cellJ c s j)) :
    w = cellJ c s (k + 1) ∨ w = nb (cellJ c s (k + 1)) s := by
  have hDc := corners_deg2 hF hcell hcor
  have hTr := ahead_notT3 hTR hcell hcor hk
  have hTrW := notT3W (t0 := t0) hs0 hTr (fun ht => absurd
    (show IsCorner t0 (cellJ c s 1) by rw [← nb_cellJ, cellJ_zero]; exact ht) (hcor 1 (by omega)).2)
  have hTsWB := notT3W (t0 := t0) hs0 (hTs (latB s) (Or.inr rfl)) hTsPB
  have hc0 : IsCell V c := by have := hcell 0 (by omega); rwa [cellJ_zero] at this
  have hc0W := isCell_mono hc0 (sub_insST V s0 t0)
  have hd0 : ∀ z, IsCorner z c → deg F z = 2 := fun z hz => hDc 0 (by omega) z (by rw [cellJ_zero]; exact hz)
  have af := alt_frame s l1 l2 bw fw
  have body : ∀ j' ≤ k + 1, w = cellJ c s j' → w = cellJ c s (k + 1) := by
    intro j' hj' hw
    by_cases h : j' = k + 1
    · rw [hw, h]
    · rw [hw] at l1 l2 bw fw
      exact (ULHC.body_not_alt hk hpat (by omega) l1 l2 bw fw).elim
  rcases touch_cases s hx1 hx2 with hq | hq | hq | hq | hq
  · exact Or.inl (body j (by omega) hq)
  · by_cases hjk : j ≤ k
    · exact Or.inl (body (j + 1) (by omega) (by rw [hq, nb_cellJ]))
    · exact Or.inr (by rw [hq, show j = k + 1 by omega])
  · rcases j with _ | j
    · exfalso
      rw [cellJ_zero] at hq
      have d2 := back_down2_loc hF.1 hpat (by omega) hc0W hsep (hd0 _ (isCorner_back2 c s))
        (hd0 _ (isCorner_front1 c s)) (hd0 _ (isCorner_front2 c s)) hTrW hTsWB
      rw [← hq] at d2 hn1
      exact hn1 (af.2.1.2 d2)
    · exact Or.inl (body j (by omega) (by rw [hq, cellJ_down]))
  · exfalso
    by_cases hjk : j ≤ k
    · rcases Nat.eq_zero_or_pos j with rfl | hj1
      · rw [cellJ_zero] at hq; exact hL0 (hq ▸ hwc)
      · obtain ⟨_, fb, ff⟩ := side1_facts_succ hDc hpat hj1 hjk
        rw [← hq] at fb ff
        have := af.1; rw [fb, ff] at this; omega
    · obtain rfl : j = k + 1 := by omega
      have fn : lat2 w s ∈ F := by
        rw [hq, side_lat2]; exact (strip_sig hpat (show k + 1 < k + 2 by omega)).1.2 (by omega)
      have fb : back w s ∈ F := by
        rw [hq, show back (nb (cellJ c s (k + 1)) (latA s)) s = outer1 (cellJ c s k) s by
          rw [← side_back_next, nb_cellJ]]
        exact (outer1_body_L hDc hpat le_rfl).2 hk
      have := af.2.1; have := af.2.2; tauto
  · exfalso
    by_cases hjk : j ≤ k
    · have hfb : back (nb (cellJ c s j) (latB s)) s ∈ F ↔ j % 2 = 1 := by
        rcases Nat.eq_zero_or_pos j with rfl | hj1
        · rw [cellJ_zero]
          simp only [Nat.zero_mod, zero_ne_one, iff_false]
          exact back_outer2_light_loc hF.1 hpat (by omega) hc0W hsep (hd0 _ (isCorner_front1 c s))
            (hd0 _ (isCorner_front2 c s)) hTrW hTsWB
        · exact (side2_facts_succ hDc hpat hj1 hjk).2.1
      have hff : front (nb (cellJ c s j) (latB s)) s ∈ F ↔ j % 2 = 0 := by
        rw [side2_front]; exact outer2_body_L hDc hpat hjk
      rw [← hq] at hfb hff
      have := af.1; rw [hfb, hff] at this; omega
    · obtain rfl : j = k + 1 := by omega
      have fn : lat1 w s ∈ F := by
        rw [hq, side2_lat1]; exact (strip_sig hpat (show k + 1 < k + 2 by omega)).2.1.2 (by omega)
      have fb : back w s ∈ F := by
        rw [hq, show back (nb (cellJ c s (k + 1)) (latB s)) s = outer2 (cellJ c s k) s by
          rw [outer2_side_nb_next, nb_cellJ]; rfl]
        exact (outer2_body_L hDc hpat le_rfl).2 hk
      have := af.2.1; have := af.2.2; tauto

omit hz hzR hTsP hds hle hTR hT' hneut hTend in
-- **`alt_touch` at a phantom start across `latB`** (mirror of `alt_touch_pfA`).
--
theorem alt_touch_pfAB
    (hTsPA : IsCorner t0 (nb c (latA s)) → NotTypeIII V F (nb c (latA s)))
    (hL0 : ¬ IsCell V (nb c (latB s))) (hn2 : lat2 (nb c s.opp) s ∉ F)
    {w : Pt} {tw : Side} (hwc : IsCell V w) (l1 : lat1 w tw ∈ F) (l2 : lat2 w tw ∈ F)
    (bw : back w tw ∉ F) (fw : front w tw ∉ F) {j : ℕ} (hj : j < k + 2) {x : Edge}
    (hx1 : x ∈ cellE w) (hx2 : x ∈ cellE (cellJ c s j)) :
    w = cellJ c s (k + 1) ∨ w = nb (cellJ c s (k + 1)) s := by
  have hDc := corners_deg2 hF hcell hcor
  have hTsWA := notT3W (t0 := t0) hs0 (hTs (latA s) (Or.inl rfl)) hTsPA
  have hd0 : ∀ z, IsCorner z c → deg F z = 2 := fun z hz => hDc 0 (by omega) z (by rw [cellJ_zero]; exact hz)
  have af := alt_frame s l1 l2 bw fw
  have body : ∀ j' ≤ k + 1, w = cellJ c s j' → w = cellJ c s (k + 1) := by
    intro j' hj' hw
    by_cases h : j' = k + 1
    · rw [hw, h]
    · rw [hw] at l1 l2 bw fw
      exact (ULHC.body_not_alt hk hpat (by omega) l1 l2 bw fw).elim
  rcases touch_cases s hx1 hx2 with hq | hq | hq | hq | hq
  · exact Or.inl (body j (by omega) hq)
  · by_cases hjk : j ≤ k
    · exact Or.inl (body (j + 1) (by omega) (by rw [hq, nb_cellJ]))
    · exact Or.inr (by rw [hq, show j = k + 1 by omega])
  · rcases j with _ | j
    · exfalso
      rw [cellJ_zero] at hq
      have d1 := back_down_loc hF.1 hpat (by omega) hsep (hd0 _ (isCorner_back1 c s))
        (hd0 _ (isCorner_front1 c s)) hTsWA
      rw [← hq] at d1 hn2
      exact hn2 (af.2.1.1 d1)
    · exact Or.inl (body j (by omega) (by rw [hq, cellJ_down]))
  · exfalso
    by_cases hjk : j ≤ k
    · have hfb : back (nb (cellJ c s j) (latA s)) s ∈ F ↔ j % 2 = 1 := by
        rcases Nat.eq_zero_or_pos j with rfl | hj1
        · rw [cellJ_zero]
          simp only [Nat.zero_mod, zero_ne_one, iff_false]
          exact back_outer_light_loc hF.1 hpat (by omega) hsep (hd0 _ (isCorner_front1 c s)) hTsWA
        · exact (side1_facts_succ hDc hpat hj1 hjk).2.1
      have hff : front (nb (cellJ c s j) (latA s)) s ∈ F ↔ j % 2 = 0 := by
        rw [side_front]; exact outer1_body_L hDc hpat hjk
      rw [← hq] at hfb hff
      have := af.1; rw [hfb, hff] at this; omega
    · obtain rfl : j = k + 1 := by omega
      have fn : lat2 w s ∈ F := by
        rw [hq, side_lat2]; exact (strip_sig hpat (show k + 1 < k + 2 by omega)).1.2 (by omega)
      have fb : back w s ∈ F := by
        rw [hq, show back (nb (cellJ c s (k + 1)) (latA s)) s = outer1 (cellJ c s k) s by
          rw [← side_back_next, nb_cellJ]]
        exact (outer1_body_L hDc hpat le_rfl).2 hk
      have := af.2.1; have := af.2.2; tauto
  · exfalso
    by_cases hjk : j ≤ k
    · rcases Nat.eq_zero_or_pos j with rfl | hj1
      · rw [cellJ_zero] at hq; exact hL0 (hq ▸ hwc)
      · obtain ⟨_, fb, ff⟩ := side2_facts_succ hDc hpat hj1 hjk
        rw [← hq] at fb ff
        have := af.1; rw [fb, ff] at this; omega
    · obtain rfl : j = k + 1 := by omega
      have fn : lat1 w s ∈ F := by
        rw [hq, side2_lat1]; exact (strip_sig hpat (show k + 1 < k + 2 by omega)).2.1.2 (by omega)
      have fb : back w s ∈ F := by
        rw [hq, show back (nb (cellJ c s (k + 1)) (latB s)) s = outer2 (cellJ c s k) s by
          rw [outer2_side_nb_next, nb_cellJ]; rfl]
        exact (outer2_body_L hDc hpat le_rfl).2 hk
      have := af.2.1; have := af.2.2; tauto

omit hTsP in
-- A strip starting across `s` at the cell beyond the end cell, of length at least 2, forces
-- a dark outer edge at the end cell's front, hence a Type III cell after `a`.
--
theorem beyond_cross_pf [hg : NearOK1 V t0] (ht : tf = latA s ∨ tf = latB s)
    (hq : z = nb (cellJ c s (k + 1)) s) (hm : 2 ≤ m)
    (hnoA : t0 ∉ V → ¬ PDang V t0 → ¬ ∃ σ L', RPathTg V (flipCol F c s (k + 2)) s0 t0 σ L') : False := by
  by_cases ht0 : t0 ∈ V ∨ PDang V t0
  swap
  · have h1 : t0 ∉ V := fun h => ht0 (Or.inl h)
    have h2 : ¬ PDang V t0 := fun h => ht0 (Or.inr h)
    exact ((hg.ok.resolve_left h1).resolve_left h2) hF hs0 hds hle hTR hk hcell hcor hpat hsep hT' hneut hTs hTend
      hz hzR ht hq hm h2 (hnoA h1 h2) h1
  have hDc := corners_deg2 hF hcell hcor
  have hTr := ahead_notT3 hTR hcell hcor hk
  have hcellW : ∀ j ≤ k + 1, IsCell (insert s0 (insert t0 V)) (cellJ c s j) :=
    fun j hj => isCell_mono (hcell j hj) (sub_insST V s0 t0)
  have hTrW := notT3W (t0 := t0) hs0 hTr (fun ht => absurd
    (show IsCorner t0 (cellJ c s 1) by rw [← nb_cellJ, cellJ_zero]; exact ht) (hcor 1 (by omega)).2)
  have hTe : NotTypeIII V F (cellJ c s (k + 1)) := restr_notT3 hTR (hcell (k + 1) le_rfl) (hcor (k + 1) le_rfl)
  have hsame := end_same_loc hTe hk hcell hpat
  set e := cellJ c s (k + 1)
  obtain ⟨_, _, gb, gf⟩ := strip_sig hz (show 0 < m by omega)
  rw [cellJ_zero, hq] at gb gf
  have hfz : front (nb e s) tf ∉ F := fun h => by have := (gf.1 h).2 (by omega); omega
  obtain ⟨a1, a2, _, af⟩ := strip_sig hpat (show k + 1 < k + 2 by omega)
  have l1 : lat1 e s ∈ F := a1.2 (by omega)
  have l2 : lat2 e s ∈ F := a2.2 (by omega)
  have hfe : front e s ∉ F := fun h => by have := (af.1 h).1 (by omega); omega
  have he := hcell (k + 1) le_rfl
  rcases ht with rfl | rfl
  · rw [(frame_latA (nb e s) s).1] at hfz
    have hd := hDc (k + 1) le_rfl _ (isCorner_front1 _ s)
    rw [deg_front1, ind_of_mem l1, ind_of_not_mem hfe, ind_of_not_mem hfz] at hd
    have ho : outer1 e s ∈ F := by by_contra ho; rw [ind_of_not_mem ho] at hd; omega
    have hb := (outer1_body_L hDc hpat le_rfl).2 hk
    obtain ⟨hcL, hnot⟩ := beside_end1_pfW hF hs0 hds hk hcell hcor hpat hsep hsame hneut hb ho
      (end_side_far1_L hF.1 hle hTe hk hcellW hpat hb ho)
      (by
        intro hc
        rcases corner_besideA hc with hbk | he' | hA
        · -- PHANTOM-P2b (remaining case): `t0` is the far back corner of the square beside the
          -- end cell. The other corners are excluded: two are corners of the end cell (`hcor`),
          -- two are corners of the next cell of the strip `z` (`hzR`). With `PDang` the square
          -- is a cell of `V ∪ {t0}` with corner `t0`, which cannot be.
          --
          rcases ht0 with ht0 | hpd
          · exact ht0
          · exact absurd hc (hpd _ (beside_end1_cellT hF hs0 hb ho))
        · exact absurd he' (hcor (k + 1) le_rfl).2
        · refine absurd ?_ (hzR 1 (by omega)).2
          rw [show cellJ z _ 1 = nb z _ by rw [← nb_cellJ, cellJ_zero], hq]
          exact hA)
    exact hnot (hTend (latA s) (by simp) hcL)
  · rw [(frame_latB (nb e s) s).1] at hfz
    have hd := hDc (k + 1) le_rfl _ (isCorner_front2 _ s)
    rw [deg_front2, ind_of_mem l2, ind_of_not_mem hfe, ind_of_not_mem hfz] at hd
    have ho : outer2 e s ∈ F := by by_contra ho; rw [ind_of_not_mem ho] at hd; omega
    have hb := (outer2_body_L hDc hpat le_rfl).2 hk
    obtain ⟨hcL, hnot⟩ := beside_end2_pfW hF hs0 hds hk hcell hcor hpat hsep hsame hneut hb ho
      (end_side_far2_L hF.1 hle hTe hk hcellW hpat hb ho)
      (by
        intro hc
        rcases corner_besideB hc with hbk | he' | hA
        · -- PHANTOM-P2b (remaining case): `t0` is the far back corner of the square beside the
          -- end cell. The other corners are excluded: two are corners of the end cell (`hcor`),
          -- two are corners of the next cell of the strip `z` (`hzR`). With `PDang` the square
          -- is a cell of `V ∪ {t0}` with corner `t0`, which cannot be.
          --
          rcases ht0 with ht0 | hpd
          · exact ht0
          · exact absurd hc (hpd _ (beside_end2_cellT hF hs0 hb ho))
        · exact absurd he' (hcor (k + 1) le_rfl).2
        · refine absurd ?_ (hzR 1 (by omega)).2
          rw [show cellJ z _ 1 = nb z _ by rw [← nb_cellJ, cellJ_zero], hq]
          exact hA)
    exact hnot (hTend (latB s) (by simp) hcL)

omit hz hzR hTsP hTs hTend in
-- An alternating cell `w` other than the end cell and the cell beyond cannot split the end
-- cell's lateral sides (`split_end_t3`).
--
theorem split_core_pf {w : Pt} {tw : Side}
    (halt : ∀ {j : ℕ}, j < k + 2 → ∀ {x : Edge}, x ∈ cellE w → x ∈ cellE (cellJ c s j) →
      w = cellJ c s (k + 1) ∨ w = nb (cellJ c s (k + 1)) s) (hw : IsCell V w) (l1 : lat1 w tw ∈ F)
    (l2 : lat2 w tw ∈ F) (bw : back w tw ∉ F) (fw : front w tw ∉ F)
    (hwe : w ≠ cellJ c s (k + 1)) (hwu : w ≠ nb (cellJ c s (k + 1)) s)
    (hwR : ¬ IsCorner s0 w ∧ ¬ IsCorner t0 w) (hspw : ncomp V (flip F w) = ncomp V F + 1)
    (hsplit : ¬ Conn (flip F w) (back1 (cellJ c s (k + 1)) s) (back2 (cellJ c s (k + 1)) s)) :
    False := by
  have hDc := corners_deg2 hF hcell hcor
  have hTr := ahead_notT3 hTR hcell hcor hk
  have hcellW : ∀ j ≤ k + 1, IsCell (insert s0 (insert t0 V)) (cellJ c s j) :=
    fun j hj => isCell_mono (hcell j hj) (sub_insST V s0 t0)
  have hTrW := notT3W (t0 := t0) hs0 hTr (fun ht => absurd
    (show IsCorner t0 (cellJ c s 1) by rw [← nb_cellJ, cellJ_zero]; exact ht) (hcor 1 (by omega)).2)
  have hTe : NotTypeIII V F (cellJ c s (k + 1)) := restr_notT3 hTR (hcell (k + 1) le_rfl) (hcor (k + 1) le_rfl)
  have hsame := end_same_loc hTe hk hcell hpat
  have hdisj : ∀ j < k + 2, ∀ x ∈ cellE w, x ∉ cellE (cellJ c s j) := by
    intro j hj x hx1 hx2
    rcases halt hj hx1 hx2 with h | h
    · exact hwe h
    · exact hwu h
  have hmid : ∀ y, y = lat1 w tw ∨ y = lat2 w tw → y ∈ cellE w := by
    intro y hy; rw [cellE_frame w tw]; rcases hy with rfl | rfl <;> simp
  have hm1 : ¬ IsMid c s k (back1 w tw) := fun hm => by
    obtain ⟨j, hj, hx⟩ := mid_touch_L hle hpat hm l1 ((ends_lat1 w tw).inc_iff _ |>.2 (Or.inl rfl))
    exact hdisj j hj _ (hmid _ (Or.inl rfl)) hx
  have hm2 : ¬ IsMid c s k (back2 w tw) := fun hm => by
    obtain ⟨j, hj, hx⟩ := mid_touch_L hle hpat hm l2 ((ends_lat2 w tw).inc_iff _ |>.2 (Or.inl rfl))
    exact hdisj j hj _ (hmid _ (Or.inr rfl)) hx
  exact split_end_t3_pf hF hs0 hds hk hcell hcor hpat hsep hsame hneut hw l1 l2 bw fw
    (restr_notT3 hTR hw hwR) hdisj hm1 hm2 hspw hsplit (hT' w hw hwR.1 hwR.2)


end classify

end HP

end ULHC
