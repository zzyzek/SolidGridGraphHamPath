/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
import ULHC.HP.Sheffield.CertOf

/-!
# Lemma C: the column after a cut square (docs/COL_SIDE.md §3)

A cut cell `g` with dark back and light laterals (frame `a`), entered across its back in
direction `o`, and not paired with the square behind it, starts a column that ends at a pair
square of direction `o` (`ColEnds`) or leaves `V` (`ColOut`):
* front dark: `g` is a merging square, hence a pair square, with its partner in front; sink or
  source decides top or bottom;
* front light, front corners joined: `g` is critical, and the column invariant for `g` applies;
* front light, front corners apart: the square in front is merging if it is a cell, and its
  lateral partner would have two dark perpendicular sides, so it is not a cell.
-/

namespace ULHC

namespace HP

open Finset Classical

section lemmaC

variable {V : Finset Pt} {H : Finset Edge} {FP : List FixedPr}

lemma uncut_of {F : Finset Edge} {c : Pt} {s : Side} (h1 : Conn F (back1 c s) (back2 c s))
    (h2 : Conn F (back1 c s) (front1 c s)) (h3 : Conn F (back2 c s) (front2 c s)) :
    ¬ CutSq F c := by
  intro hc
  apply hc
  have all : ∀ z, IsCorner z c → Conn F (back1 c s) z := by
    intro z hz
    rcases corner_cases c s hz with rfl | rfl | rfl | rfl
    · exact Conn.refl _ _
    · exact h1
    · exact h2
    · exact h1.trans h3
  obtain ⟨x, y⟩ := c
  refine ⟨(all _ (Or.inl rfl)).symm.trans (all _ (Or.inr (Or.inl rfl))),
    (all _ (Or.inl rfl)).symm.trans (all _ (Or.inr (Or.inr (Or.inr rfl)))),
    (all _ (Or.inl rfl)).symm.trans (all _ (Or.inr (Or.inr (Or.inl rfl))))⟩

lemma arc_opp_diff {F : Finset Edge} {c : Pt} {s : Side} (h1 : sideEdge c s.opp ∈ F)
    (h2 : sideEdge c s ∉ F) : outArc F c s = !outArc F c s.opp := by
  rw [outArc_eq, outArc_eq, horiz_opp]
  simp only [h1, h2, decide_true, decide_false]
  cases par c <;> cases s.horiz <;> rfl

-- A dark side of a cell with light laterals (frame `a`) is its back or front.
--
lemma dark_bf {c : Pt} {a s' : Side} (hl1 : lat1 c a ∉ H) (hl2 : lat2 c a ∉ H)
    (h : sideEdge c s' ∈ H) : s' = a ∨ s' = a.opp := by
  rcases side_cases a s' with rfl | rfl | rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr rfl
  · rw [← lat1_eq] at h; exact absurd h hl1
  · rw [← lat2_eq] at h; exact absurd h hl2

variable (hdegc : ∀ f, IsCell V f → ∀ z, IsCorner z f → deg H z = 2)
  (hf2 : ∀ q, IsCell V q → Alt H q → CutSq H q → ∃ i ∈ FP, q = i.top ∨ q = i.bot)
  (hpok : ∀ i ∈ FP, PairOK H i) (hpalt : ∀ i ∈ FP, Alt H i.top ∧ Alt H i.bot)
  (hpdark : ∀ i ∈ FP, sideEdge i.bot i.s ∈ H)
  (hpcell : ∀ i ∈ FP, IsCell V i.top ∧ IsCell V i.bot)
include hdegc hf2 hpok hpalt hpdark hpcell

-- **Lemma C.**
--
theorem lemmaC {g : Pt} {a : Side} {o : Bool} (hg : IsCell V g) (hb : back g a ∈ H)
    (hl1 : lat1 g a ∉ H) (hl2 : lat2 g a ∉ H) (hcut : CutSq H g)
    (harc : outArc H g a.opp = !o)
    (hHb : ∀ i ∈ FP, ¬ ((g = i.top ∧ nb g a.opp = i.bot) ∨ (g = i.bot ∧ nb g a.opp = i.top)))
    (hcolg : CriticalIn H g a → (∀ i ∈ FP, g ≠ i.top ∧ g ≠ i.bot) →
      ColEnds V H FP g a (outArc H g a) ∨ ColOut V H g a (outArc H g a)) :
    ColEnds V H FP g a o ∨ ColOut V H g a o := by
  by_cases hf : front g a ∈ H
  · -- The front is dark: `g` is a pair square with its partner in front.
    --
    left
    have halt := alt_of_bf hb hf hl1 hl2
    obtain ⟨i, hi, hgi⟩ := hf2 g hg halt hcut
    have pat1 : StripPat H g a 1 := by
      refine ⟨hb, fun j hj => ?_, fun j hj => ?_⟩
      · obtain rfl : j = 0 := by omega
        rw [cellJ_zero]; exact ⟨⟨fun h => absurd h hl1, fun h => by omega⟩,
          ⟨fun h => absurd h hl2, fun h => by omega⟩⟩
      · obtain rfl : j = 0 := by omega
        rw [cellJ_zero]; exact ⟨fun _ => by omega, fun _ => hf⟩
    have hsrc : o = false → Source H g := fun ho =>
      source_of_alt halt (s := a.opp) (by rw [harc, ho]; rfl)
    have hsnk : o = true → Sink H g := fun ho =>
      sink_of_alt halt (s := a.opp) (by rw [harc, ho]; rfl)
    have l1 : sideEdge g (latA a) ∉ H := by rw [← lat1_eq]; exact hl1
    rcases hgi with rfl | rfl
    · -- `g` is the top: its bottom is across `i.s.opp`.
      have hbot : i.bot = nb i.top i.s.opp := by unfold FixedPr.top; rw [nb_nb_opp]
      have hd : sideEdge i.top i.s.opp ∈ H := by
        unfold FixedPr.top; rw [sideEdge_nb_opp]; exact hpdark i hi
      rcases dark_bf hl1 hl2 hd with h | h
      · have hs : i.s = a.opp := by rw [← h, opp_opp]
        cases o
        · exact absurd ((hpok i hi).1 _ l1) (by rw [hsrc rfl]; simp)
        · refine ⟨0, fun j hj => ?_, pat1, i, hi, Or.inl ⟨rfl, ?_, hs⟩⟩
          · rcases (show j = 0 ∨ j = 1 by omega) with rfl | rfl
            · rw [cellJ_zero]; exact hg
            · rw [show cellJ i.top a 1 = i.bot by
                rw [hbot, h, show (1 : ℕ) = 0 + 1 from rfl, ← nb_cellJ, cellJ_zero]]
              exact (hpcell i hi).2
          · rw [hbot, h, show (0 + 1 : ℕ) = 0 + 1 from rfl, ← nb_cellJ, cellJ_zero]
      · exact absurd (Or.inl ⟨rfl, by rw [← h, hbot]⟩) (hHb i hi)
    · -- `g` is the bottom: its top is across `i.s`.
      rcases dark_bf hl1 hl2 (hpdark i hi) with h | h
      · cases o
        · refine ⟨0, fun j hj => ?_, pat1, i, hi, Or.inr ⟨rfl, by rw [cellJ_zero], h⟩⟩
          rcases (show j = 0 ∨ j = 1 by omega) with rfl | rfl
          · rw [cellJ_zero]; exact hg
          · rw [show cellJ i.bot a 1 = i.top by
              unfold FixedPr.top; rw [h, show (1 : ℕ) = 0 + 1 from rfl, ← nb_cellJ, cellJ_zero]]
            exact (hpcell i hi).1
        · exact absurd ((hpok i hi).2.1 _ l1) (by rw [hsnk rfl]; simp)
      · exact absurd (Or.inr ⟨rfl, by unfold FixedPr.top; rw [h]⟩) (hHb i hi)
  · -- The front is light: the arc across it points `o`.
    --
    have hao : outArc H g a = o := by
      rw [arc_opp_diff (by unfold back at hb; exact hb) hf, harc]; simp
    have hdF1 := hdegc g hg _ (isCorner_front1 g a)
    have hdF2 := hdegc g hg _ (isCorner_front2 g a)
    have kb := (ends_back (c := g) (s := a)).conn hb
    by_cases hfc : Conn H (front1 g a) (front2 g a)
    · -- `g` is critical.
      have hn : ¬ Conn H (back1 g a) (front1 g a) := fun h =>
        uncut_of kb h ((kb.symm.trans h).trans hfc) hcut
      have hcr : CriticalIn H g a := ⟨kb, hfc, hn, Or.inl ⟨hb, hf⟩⟩
      have hnp : ∀ i ∈ FP, g ≠ i.top ∧ g ≠ i.bot := by
        have hna : ¬ Alt H g := not_alt_of_ne (s' := a) (by
          unfold back at hb; unfold front at hf; tauto)
        exact fun i hi => ⟨fun e => hna (e ▸ (hpalt i hi).1), fun e => hna (e ▸ (hpalt i hi).2)⟩
      rw [← hao]; exact hcolg hcr hnp
    · by_cases hc1 : IsCell V (cellJ g a 1)
      · exfalso
        obtain ⟨oA, lA⟩ := forcedA hl1 hf hdF1
        obtain ⟨oB, lB⟩ := forcedB hl2 hf hdF2
        have hc1' : IsCell V (nb g a) := by rw [← cellJ_zero g a, nb_cellJ]; exact hc1
        have hb1 : back (nb g a) a ∉ H := by rw [back_nb]; exact hf
        have hf1 : front (nb g a) a ∉ H := by
          intro h
          apply hfc
          have e1 := (ends_lat1 (c := nb g a) (s := a)).conn lA
          have e2 := (ends_lat2 (c := nb g a) (s := a)).conn lB
          have e3 := (ends_front (c := nb g a) (s := a)).conn h
          rw [back1_nb] at e1; rw [back2_nb] at e2
          exact e1.trans (e3.trans e2.symm)
        have halt1 := alt_of_lats lA lB hb1 hf1
        have hcut1 : CutSq H (nb g a) := by
          refine cutSq_of_corners (u := back1 (nb g a) a) (v := back2 (nb g a) a)
            (isCorner_back1 _ _) (isCorner_back2 _ _) ?_
          rw [back1_nb, back2_nb]; exact hfc
        obtain ⟨s', hd, hP⟩ := pair_partner hpalt hpdark (hf2 _ hc1' halt1 hcut1)
        rcases side_cases a s' with rfl | rfl | rfl | rfl
        · exact hf1 hd
        · exact hb1 hd
        · rw [← nb_side_comm] at hP; exact partnerA oA lA hP
        · rw [← nb_sideB_comm] at hP; exact partnerB oB lB hP
      · right
        refine ⟨0, fun j hj => ?_, fun j hj => ?_, hc1⟩
        · obtain rfl : j = 0 := by omega
          rw [cellJ_zero]; exact hg
        · obtain rfl : j = 0 := by omega
          rw [cellJ_zero]; exact hao

end lemmaC

end HP

end ULHC
