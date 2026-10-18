/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
module

public import SolidGridHam.Path.Cert
public import SolidGridHam.Algorithm

@[expose] public section

/-!
# L4 in a stuck state (the partner argument)

A 2+2 cell `q` (back pair joined, front pair joined, the two pairs apart) with all four sides light
does not occur once every alternating cut square is a pair square (F2), pair squares are alternating
with a dark shared side, every cell corner has degree 2, and the only edges leaving `V` end at `t0`.

* Degree 2 at `q`'s corners darkens the two edges leaving each corner. The square `q_L` across
  `q`'s side `latA` then has dark front and back (in different pieces) and light laterals, so it is a
  merging square if it is a cell (`sideA_cut`).
* A pair square has its partner across a dark side, and the partner is alternating. Each square
  across a dark side of `q_L` has two dark perpendicular sides at a corner of `q`, so it is not
  alternating (`partnerA`). Hence `q_L` is not a cell, and neither is `q_R` (side `latB`).
* `q_L` not a cell puts `t0` at a corner of `q` on the `latA` side, and `q_R` puts it on the `latB`
  side: impossible.
-/

namespace SolidGridHam

namespace HP

open Finset Classical

-- Two points within king distance 2.
--
def Close (a b : Pt) : Prop := |a.1 - b.1| ≤ 2 ∧ |a.2 - b.2| ≤ 2

-- Two points within king distance 1.
--
def Close1 (a b : Pt) : Prop := |a.1 - b.1| ≤ 1 ∧ |a.2 - b.2| ≤ 1

-- The out-vertices are equal or at king distance at least 2.
--
def Far (t0 u0 : Pt) : Prop := t0 = u0 ∨ ¬ Close1 t0 u0

lemma opp_symm {a ma b mb : Pt} (h : Opp a ma b mb) : Opp b mb a ma := by
  unfold Opp at *
  rcases h with ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩
  · right; left; exact ⟨by omega, by rw [abs_sub_comm]; exact h2, h4, h3⟩
  · left; exact ⟨by omega, by rw [abs_sub_comm]; exact h2, h4, h3⟩
  · right; right; right; exact ⟨by omega, by rw [abs_sub_comm]; exact h2, h4, h3⟩
  · right; right; left; exact ⟨by omega, by rw [abs_sub_comm]; exact h2, h4, h3⟩

-- No two distinct out-vertices of `H` carry opposed phantoms (edges of `H` leaving `V`).
--
def NoOpp (V : Finset Pt) (H : Finset Edge) (t0 u0 : Pt) : Prop :=
  ∀ e ∈ H, ∀ f ∈ H, ∀ a ma b mb : Pt, (a = t0 ∨ a = u0) → (b = t0 ∨ b = u0) → a ≠ b →
    Ends e a ma → ma ∉ V → Ends f b mb → mb ∉ V → ¬ Opp a ma b mb

lemma noOpp_same (V : Finset Pt) (H : Finset Edge) (t : Pt) : NoOpp V H t t := by
  intro _ _ _ _ a _ b _ ha hb hab
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> exact absurd rfl hab

lemma out_dup {V : Finset Pt} {H : Finset Edge} {t : Pt}
    (h : ∀ e ∈ H, (e.p ∉ V → e.q = t) ∧ (e.q ∉ V → e.p = t)) :
    ∀ e ∈ H, (e.p ∉ V → e.q = t ∨ e.q = t) ∧ (e.q ∉ V → e.p = t ∨ e.p = t) :=
  fun e he => ⟨fun hx => Or.inl ((h e he).1 hx), fun hx => Or.inl ((h e he).2 hx)⟩

lemma close_comm {a b : Pt} (h : Close a b) : Close b a := by
  unfold Close at *
  rw [abs_sub_comm, abs_sub_comm b.2]; exact h

lemma close1_comm {a b : Pt} (h : Close1 a b) : Close1 b a := by
  unfold Close1 at *
  rw [abs_sub_comm, abs_sub_comm b.2]; exact h

lemma far_close {a b : Pt} (hf : Far a b) (hne : a ≠ b) (hc : Close1 a b) : False := by
  rcases hf with h | h
  · exact hne h
  · exact h hc

lemma corners_close {a b q : Pt} (ha : IsCorner a q) (hb : IsCorner b q) : Close1 a b := by
  obtain ⟨x, y⟩ := q
  unfold Close1
  rcases ha with rfl | rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl | rfl <;>
    simp only [abs_le] <;> constructor <;> constructor <;> omega

-- An out-vertex at a `latA` corner and one at a `latB` corner of one cell: impossible when the
-- out-vertices are equal (one point is not on both sides) or far apart.
--
lemma two_sides {t0 u0 q : Pt} {s : Side} (hfar : Far t0 u0)
    (hA : ∃ w, (w = t0 ∨ w = u0) ∧ (w = front1 q s ∨ w = back1 q s))
    (hB : ∃ w, (w = t0 ∨ w = u0) ∧ (w = front2 q s ∨ w = back2 q s)) : False := by
  obtain ⟨w, hw, hwA⟩ := hA
  obtain ⟨w', hw', hwB⟩ := hB
  by_cases hww : w = w'
  · subst hww
    obtain ⟨x, y⟩ := q
    rcases hwA with h | h <;> rcases hwB with h' | h' <;> rw [h] at h' <;>
      cases s <;> simp [front1, front2, back1, back2, Prod.ext_iff] at h'
  · have cw : IsCorner w q := by
      rcases hwA with rfl | rfl
      · exact isCorner_front1 q s
      · exact isCorner_back1 q s
    have cw' : IsCorner w' q := by
      rcases hwB with rfl | rfl
      · exact isCorner_front2 q s
      · exact isCorner_back2 q s
    have hcl := corners_close cw cw'
    rcases hw with rfl | rfl <;> rcases hw' with rfl | rfl
    · exact hww rfl
    · exact far_close hfar hww hcl
    · exact far_close hfar (Ne.symm hww) (close1_comm hcl)
    · exact hww rfl

section l4

variable {V : Finset Pt} {H : Finset Edge} {FP : List FixedPr} {t0 u0 : Pt}

lemma front1_sopp (q : Pt) (s : Side) : front1 q s.opp = back1 q s := by
  obtain ⟨x, y⟩ := q; cases s <;> rfl

lemma front2_sopp (q : Pt) (s : Side) : front2 q s.opp = back2 q s := by
  obtain ⟨x, y⟩ := q; cases s <;> rfl

lemma lat1_sopp (q : Pt) (s : Side) : lat1 q s.opp = lat1 q s := by cases s <;> rfl

lemma lat2_sopp (q : Pt) (s : Side) : lat2 q s.opp = lat2 q s := by cases s <;> rfl

lemma cutSq_of_corners {u v c : Pt} (hu : IsCorner u c) (hv : IsCorner v c) (huv : ¬ Conn H u v) :
    CutSq H c := by
  rintro ⟨h1, h2, h3⟩
  have hc : ∀ w, IsCorner w c → Conn H c w := by
    intro w hw
    rcases hw with rfl | rfl | rfl | rfl
    · exact Conn.refl _ _
    · exact h1
    · exact h3
    · exact h2
  exact huv ((hc u hu).symm.trans (hc v hv))

lemma out_end {u v : Pt} {e : Edge} (hout : ∀ e ∈ H, (e.p ∉ V → e.q = t0 ∨ e.q = u0) ∧ (e.q ∉ V → e.p = t0 ∨ e.p = u0))
    (he : Ends e u v) (hH : e ∈ H) (hu : u ∉ V) : v = t0 ∨ v = u0 := by
  rcases he with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [← h2]; exact (hout e hH).1 (h1 ▸ hu)
  · rw [← h1]; exact (hout e hH).2 (h2 ▸ hu)

-- Degree 2 at `front1 q s` with `q`'s two sides there light.
--
lemma forcedA {q : Pt} {s : Side} (hl : lat1 q s ∉ H) (hf : front q s ∉ H)
    (hd : deg H (front1 q s) = 2) : outer1 q s ∈ H ∧ lat1 (nb q s) s ∈ H := by
  rw [deg_front1, ind_of_not_mem hl, ind_of_not_mem hf] at hd
  have a := ind_le_one H (lat1 (nb q s) s)
  have b := ind_le_one H (outer1 q s)
  have ha : ind H (lat1 (nb q s) s) = 1 := by omega
  have hb : ind H (outer1 q s) = 1 := by omega
  unfold ind at ha hb
  split_ifs at ha hb with h1 h2
  exact ⟨h2, h1⟩

lemma forcedB {q : Pt} {s : Side} (hl : lat2 q s ∉ H) (hf : front q s ∉ H)
    (hd : deg H (front2 q s) = 2) : outer2 q s ∈ H ∧ lat2 (nb q s) s ∈ H := by
  rw [deg_front2, ind_of_not_mem hl, ind_of_not_mem hf] at hd
  have a := ind_le_one H (lat2 (nb q s) s)
  have b := ind_le_one H (outer2 q s)
  have ha : ind H (lat2 (nb q s) s) = 1 := by omega
  have hb : ind H (outer2 q s) = 1 := by omega
  unfold ind at ha hb
  split_ifs at ha hb with h1 h2
  exact ⟨h2, h1⟩

-- The square across the front of `q_L` has two dark perpendicular sides.
--
lemma partnerA {q : Pt} {s : Side} (h1 : outer1 q s ∈ H) (h2 : lat1 (nb q s) s ∈ H) :
    ¬ Alt H (nb (nb q (latA s)) s) := by
  intro ha
  have hb : sideEdge (nb (nb q (latA s)) s) s.opp ∈ H := by
    rw [sideEdge_nb_opp]; rw [← side_front q s] at h1; exact h1
  have hl : sideEdge (nb (nb q (latA s)) s) (latB s.opp) ∈ H := by
    rw [latB_opp, ← lat2_eq, nb_side_comm, side_near]; exact h2
  exact (alt_lats ha hb).2 hl

lemma partnerB {q : Pt} {s : Side} (h1 : outer2 q s ∈ H) (h2 : lat2 (nb q s) s ∈ H) :
    ¬ Alt H (nb (nb q (latB s)) s) := by
  intro ha
  have hb : sideEdge (nb (nb q (latB s)) s) s.opp ∈ H := by
    rw [sideEdge_nb_opp]; rw [← sideB_front q s] at h1; exact h1
  have hl : sideEdge (nb (nb q (latB s)) s) (latA s.opp) ∈ H := by
    rw [latA_opp, ← lat1_eq, nb_sideB_comm, sideB_near]; exact h2
  exact (alt_lats ha hb).1 hl

-- A pair square has an alternating partner across a dark side.
--
lemma pair_partner (hpalt : ∀ i ∈ FP, Alt H i.top ∧ Alt H i.bot)
    (hpdark : ∀ i ∈ FP, sideEdge i.bot i.s ∈ H) {g : Pt} (hg : ∃ i ∈ FP, g = i.top ∨ g = i.bot) :
    ∃ s', sideEdge g s' ∈ H ∧ Alt H (nb g s') := by
  obtain ⟨i, hi, rfl | rfl⟩ := hg
  · refine ⟨i.s.opp, ?_, ?_⟩
    · unfold FixedPr.top; rw [sideEdge_nb_opp]; exact hpdark i hi
    · unfold FixedPr.top; rw [nb_nb_opp]; exact (hpalt i hi).2
  · exact ⟨i.s, hpdark i hi, (hpalt i hi).1⟩

-- **L4 in a stuck state.**
--
theorem l4_of (hfar : Far t0 u0) (hdegc : ∀ f, IsCell V f → ∀ z, IsCorner z f → deg H z = 2)
    (hf2 : ∀ q, IsCell V q → Alt H q → CutSq H q → ∃ i ∈ FP, q = i.top ∨ q = i.bot)
    (hpalt : ∀ i ∈ FP, Alt H i.top ∧ Alt H i.bot) (hpdark : ∀ i ∈ FP, sideEdge i.bot i.s ∈ H)
    (hout : ∀ e ∈ H, (e.p ∉ V → e.q = t0 ∨ e.q = u0) ∧ (e.q ∉ V → e.p = t0 ∨ e.p = u0)) :
    ∀ q s, IsCell V q → Conn H (back1 q s) (back2 q s) → Conn H (front1 q s) (front2 q s) →
      ¬ Conn H (back1 q s) (front1 q s) → back q s ∈ H ∨ front q s ∈ H := by
  intro q s hq hbb hff hn
  by_contra hc
  push Not at hc
  obtain ⟨hb, hf⟩ := hc
  have hl1 : lat1 q s ∉ H := fun h => hn ((ends_lat1 (c := q) (s := s)).conn h)
  have hl2 : lat2 q s ∉ H := fun h =>
    hn (hbb.trans (((ends_lat2 (c := q) (s := s)).conn h).trans hff.symm))
  have dF1 := hdegc q hq _ (isCorner_front1 q s)
  have dF2 := hdegc q hq _ (isCorner_front2 q s)
  have dB1 := hdegc q hq _ (isCorner_back1 q s)
  have dB2 := hdegc q hq _ (isCorner_back2 q s)
  -- Forced edges, front (frame `s`) and back (frame `s.opp`).
  --
  obtain ⟨oA, lA⟩ := forcedA hl1 hf dF1
  obtain ⟨oB, lB⟩ := forcedB hl2 hf dF2
  obtain ⟨oA', lA'⟩ := forcedA (s := s.opp) (q := q) (by rw [lat1_sopp]; exact hl1) hb
    (by rw [front1_sopp]; exact dB1)
  obtain ⟨oB', lB'⟩ := forcedB (s := s.opp) (q := q) (by rw [lat2_sopp]; exact hl2) hb
    (by rw [front2_sopp]; exact dB2)
  -- `q_L` is not a cell.
  --
  have notL : ¬ IsCell V (nb q (latA s)) := by
    intro hL
    have fr : front (nb q (latA s)) s ∈ H := by rw [side_front]; exact oA
    have bk : back (nb q (latA s)) s ∈ H := by
      have := side_front q s.opp; rw [latA_opp] at this
      unfold back; rw [← this] at oA'; exact oA'
    have l2 : lat2 (nb q (latA s)) s ∉ H := by rw [side_near]; exact hl1
    have l1 : lat1 (nb q (latA s)) s ∉ H := by
      intro h
      have c1 := (ends_lat1 (c := nb q (latA s)) (s := s)).conn h
      have cf := (ends_front (c := nb q (latA s)) (s := s)).conn fr
      have cb := (ends_back (c := nb q (latA s)) (s := s)).conn bk
      rw [sideA_front2] at cf; rw [sideA_back2] at cb
      exact hn (cb.symm.trans (c1.trans cf))
    have halt := alt_of_bf bk fr l1 l2
    have hcut : CutSq H (nb q (latA s)) := by
      refine cutSq_of_corners (u := back2 (nb q (latA s)) s) (v := front2 (nb q (latA s)) s)
        (isCorner_back2 _ _) (isCorner_front2 _ _) ?_
      rw [sideA_back2, sideA_front2]; exact hn
    obtain ⟨s', hd, hP⟩ := pair_partner hpalt hpdark (hf2 _ hL halt hcut)
    rcases side_cases s s' with rfl | rfl | rfl | rfl
    · exact partnerA oA lA hP
    · have := partnerA (q := q) (s := s.opp) oA' lA'
      rw [latA_opp] at this; exact this hP
    · rw [← lat1_eq] at hd; exact l1 hd
    · rw [← lat2_eq] at hd; exact l2 hd
  have notR : ¬ IsCell V (nb q (latB s)) := by
    intro hR
    have fr : front (nb q (latB s)) s ∈ H := by rw [sideB_front]; exact oB
    have bk : back (nb q (latB s)) s ∈ H := by
      have := sideB_front q s.opp; rw [latB_opp] at this
      unfold back; rw [← this] at oB'; exact oB'
    have l1 : lat1 (nb q (latB s)) s ∉ H := by rw [sideB_near]; exact hl2
    have l2 : lat2 (nb q (latB s)) s ∉ H := by
      intro h
      have c1 := (ends_lat2 (c := nb q (latB s)) (s := s)).conn h
      have cf := (ends_front (c := nb q (latB s)) (s := s)).conn fr
      have cb := (ends_back (c := nb q (latB s)) (s := s)).conn bk
      rw [sideB_front1] at cf; rw [sideB_back1] at cb
      exact hn (hbb.trans (cb.trans (c1.trans (cf.symm.trans hff.symm))))
    have halt := alt_of_bf bk fr l1 l2
    have hcut : CutSq H (nb q (latB s)) := by
      refine cutSq_of_corners (u := back1 (nb q (latB s)) s) (v := front1 (nb q (latB s)) s)
        (isCorner_back1 _ _) (isCorner_front1 _ _) ?_
      rw [sideB_back1, sideB_front1]
      exact fun h => hn (hbb.trans (h.trans hff.symm))
    obtain ⟨s', hd, hP⟩ := pair_partner hpalt hpdark (hf2 _ hR halt hcut)
    rcases side_cases s s' with rfl | rfl | rfl | rfl
    · exact partnerB oB lB hP
    · have := partnerB (q := q) (s := s.opp) oB' lB'
      rw [latB_opp] at this; exact this hP
    · rw [← lat1_eq] at hd; exact l1 hd
    · rw [← lat2_eq] at hd; exact l2 hd
  -- `t0` would be at a `latA` corner and at a `latB` corner of `q`.
  --
  have qV1 : back1 q s ∈ V ∧ back2 q s ∈ V ∧ front1 q s ∈ V ∧ front2 q s ∈ V := by
    obtain ⟨x, y⟩ := q
    obtain ⟨a, b, c, d⟩ := hq
    cases s <;> simp only [back1, back2, front1, front2] <;> exact ⟨by assumption, by assumption,
      by assumption, by assumption⟩
  have eFA : Ends (outer1 q s) (front1 (nb q (latA s)) s) (front1 q s) := by
    have e := ends_front (c := nb q (latA s)) (s := s)
    rwa [side_front, sideA_front2] at e
  have eBA : Ends (outer1 q s.opp) (back1 (nb q (latA s)) s) (back1 q s) := by
    have e := ends_front (c := nb q (latA s.opp)) (s := s.opp)
    rw [side_front, sideA_front2, front1_sopp, front1_sopp, latA_opp] at e
    exact e
  have eFB : Ends (outer2 q s) (front2 (nb q (latB s)) s) (front2 q s) := by
    have e := ends_front (c := nb q (latB s)) (s := s)
    rw [sideB_front, sideB_front1] at e
    exact ends_swap e
  have eBB : Ends (outer2 q s.opp) (back2 (nb q (latB s)) s) (back2 q s) := by
    have e := ends_front (c := nb q (latB s.opp)) (s := s.opp)
    rw [sideB_front, sideB_front1, front2_sopp, front2_sopp, latB_opp] at e
    exact ends_swap e
  have tA : ∃ w, (w = t0 ∨ w = u0) ∧ (w = front1 q s ∨ w = back1 q s) := by
    by_contra hne
    push Not at hne
    apply notL
    apply isCell_of_corners (a := s)
    · by_contra hx
      rcases out_end hout eBA oA' hx with h | h
      · exact (hne _ (Or.inl rfl)).2 h.symm
      · exact (hne _ (Or.inr rfl)).2 h.symm
    · rw [sideA_back2]; exact qV1.1
    · by_contra hx
      rcases out_end hout eFA oA hx with h | h
      · exact (hne _ (Or.inl rfl)).1 h.symm
      · exact (hne _ (Or.inr rfl)).1 h.symm
    · rw [sideA_front2]; exact qV1.2.2.1
  have tB : ∃ w, (w = t0 ∨ w = u0) ∧ (w = front2 q s ∨ w = back2 q s) := by
    by_contra hne
    push Not at hne
    apply notR
    apply isCell_of_corners (a := s)
    · rw [sideB_back1]; exact qV1.2.1
    · by_contra hx
      rcases out_end hout eBB oB' hx with h | h
      · exact (hne _ (Or.inl rfl)).2 h.symm
      · exact (hne _ (Or.inr rfl)).2 h.symm
    · rw [sideB_front1]; exact qV1.2.2.2
    · by_contra hx
      rcases out_end hout eFB oB hx with h | h
      · exact (hne _ (Or.inl rfl)).1 h.symm
      · exact (hne _ (Or.inr rfl)).1 h.symm
  exact two_sides hfar tA tB

end l4

end HP

end SolidGridHam
