/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
module

public import SolidGridHam.Cycle.Enum
public import SolidGridHam.Cycle.L57
public import SolidGridHam.Cycle.Created

@[expose] public section

/-!
# Near contacts with the first strip

Local facts about the cells around a proper strip `a` in a Type III-free 2-factor, used to
show that no later strip of a minimum path touches `a`.

* `outer1_start`: the outer edge at `front1` of the start cell is dark (degree count).
* `back_outer_light`: the outer edge at `back1` of the start cell is light. Otherwise the
  cell beside the start cell, across `lat1`, has dark back and front sides; either its far
  side is dark, or it is alternating and, being not Type III, joins its two dark sides.
  Both join `back1` to `front1`, against properness.
* `back_down`: hence the edge leaving `back1` straight backwards is dark. A strip or cell
  behind the start cell whose side meets `back1` in a light edge cannot exist.
-/

namespace SolidGridHam

open Finset

section geo

variable (c : Pt) (s : Side)

-- The degree at `back1` is read off its four edges.
--
lemma deg_back1 (F : Finset Edge) :
    deg F (back1 c s) =
      ind F (lat1 c s) + ind F (back c s) + ind F (lat1 (nb c s.opp) s) +
        ind F (back (nb c (latA s)) s) := by
  obtain ⟨x, y⟩ := c
  cases s <;> simp only [deg, back1, lat1, back, nb, sideEdge, Side.opp, latA, eR, eL, eU, eD,
    lft, rgt, bot, top] <;> (try simp only [add_sub_cancel_right]) <;> omega

lemma side_back_ends : Ends (back (nb c (latA s)) s) (back1 (nb c (latA s)) s) (back1 c s) := by
  have := ends_back (nb c (latA s)) s
  rwa [side_back2] at this

lemma side_front_ends : Ends (outer1 c s) (front1 (nb c (latA s)) s) (front1 c s) := by
  have := ends_front (nb c (latA s)) s
  rwa [side_front2, side_front] at this

lemma deg_back2 (F : Finset Edge) :
    deg F (back2 c s) =
      ind F (lat2 c s) + ind F (back c s) + ind F (lat2 (nb c s.opp) s) +
        ind F (back (nb c (latB s)) s) := by
  obtain ⟨x, y⟩ := c
  cases s <;> simp only [deg, back2, lat2, back, nb, sideEdge, Side.opp, latB, eR, eL, eU, eD,
    lft, rgt, bot, top] <;> (try simp only [add_sub_cancel_right]) <;> omega

lemma side2_back1 : back1 (nb c (latB s)) s = back2 c s := by
  obtain ⟨x, y⟩ := c; cases s <;> simp [back1, back2, latB, nb]

lemma side2_front1 : front1 (nb c (latB s)) s = front2 c s := by
  obtain ⟨x, y⟩ := c; cases s <;> simp [front1, front2, latB, nb]

lemma side2_lat1 : lat1 (nb c (latB s)) s = lat2 c s := by
  rw [lat2_side_nb, lat1_eq]
  cases s <;> rfl

lemma side2_front : front (nb c (latB s)) s = outer2 c s := by
  rw [outer2_side_nb]; rfl

lemma side2_back_ends : Ends (back (nb c (latB s)) s) (back2 c s) (back2 (nb c (latB s)) s) := by
  have := ends_back (nb c (latB s)) s
  rwa [side2_back1] at this

lemma side2_front_ends : Ends (outer2 c s) (front2 c s) (front2 (nb c (latB s)) s) := by
  have := ends_front (nb c (latB s)) s
  rwa [side2_front1, side2_front] at this

end geo

lemma corners4 {V : Finset Pt} {c : Pt} (hc : IsCell V c) (s : Side) :
    back1 c s ∈ V ∧ back2 c s ∈ V ∧ front1 c s ∈ V ∧ front2 c s ∈ V := by
  obtain ⟨x, y⟩ := c
  obtain ⟨h1, h2, h3, h4⟩ := hc
  cases s <;> simp only [back1, back2, front1, front2] <;> exact ⟨‹_›, ‹_›, ‹_›, ‹_›⟩

lemma ind_of_mem {F : Finset Edge} {e : Edge} (h : e ∈ F) : ind F e = 1 := by simp [ind, h]
lemma ind_of_not_mem {F : Finset Edge} {e : Edge} (h : e ∉ F) : ind F e = 0 := by
  simp [ind, h]

section start

variable {V : Finset Pt} {F : Finset Edge} (hF : Deg2 V F) {c : Pt} {s : Side} {n : ℕ}
include hF

-- The outer edge at the start cell's `front1` is dark.
--
lemma outer1_start (hp : StripPat F c s n) (hn : 2 ≤ n) (hc : IsCell V c) :
    outer1 c s ∈ F := by
  obtain ⟨_, hl, hf⟩ := hp
  have h0 := hl 0 (by omega)
  have h1 := hl 1 (by omega)
  have hf0 := hf 0 (by omega)
  rw [cellJ_zero] at h0 hf0
  have hl0 : lat1 c s ∉ F := fun h => by have := h0.1.1 h; omega
  have hfr : front c s ∉ F := fun h => by have := hf0.1 h; omega
  have hl1 : lat1 (nb c s) s ∈ F := by
    rw [show nb c s = cellJ c s 1 by rw [← nb_cellJ, cellJ_zero]]; exact h1.1.2 rfl
  have hd := hF.2 _ (corners4 hc s).2.2.1
  rw [deg_front1, ind_of_not_mem hl0, ind_of_not_mem hfr, ind_of_mem hl1] at hd
  by_contra ho
  rw [ind_of_not_mem ho] at hd
  omega

variable (hT : NoTypeIII V F)
include hT

-- The outer edge at the start cell's `back1` is light when the start separates.
--
lemma back_outer_light (hp : StripPat F c s n) (hn : 2 ≤ n) (hc : IsCell V c)
    (hsep : ¬ Conn F (back1 c s) (front1 c s)) : back (nb c (latA s)) s ∉ F := by
  intro hb
  set L := nb c (latA s)
  have ho := outer1_start hF hp hn hc
  have hfL : front L s ∈ F := by rw [side_front]; exact ho
  have hV1 := (side_back_ends c s).inV (hF.1 _ hb)
  have hV2 := (side_front_ends c s).inV (hF.1 _ ho)
  have hcL : IsCell V L := by
    refine isCell_of_corners L s hV1.1 ?_ hV2.1 ?_
    · rw [side_back2]; exact hV1.2
    · rw [side_front2]; exact hV2.2
  have hLL : Conn F (back1 L s) (front1 L s) := by
    by_cases hl : lat1 L s ∈ F
    · exact (ends_lat1 L s).conn hl
    · have hl2 : lat2 L s ∉ F := by
        rw [side_lat2]
        obtain ⟨_, hl', _⟩ := hp
        have h0 := hl' 0 (by omega)
        rw [cellJ_zero] at h0
        exact fun h => by have := h0.1.1 h; omega
      exact hT L hcL s hb hfL hl hl2
  exact hsep ((((side_back_ends c s).conn hb).symm.trans hLL).trans
    ((side_front_ends c s).conn ho))

-- The edge leaving `back1` straight backwards is dark.
--
lemma back_down (hp : StripPat F c s n) (hn : 2 ≤ n) (hc : IsCell V c)
    (hsep : ¬ Conn F (back1 c s) (front1 c s)) : lat1 (nb c s.opp) s ∈ F := by
  have hbo := back_outer_light hF hT hp hn hc hsep
  obtain ⟨hbk, hl, _⟩ := hp
  have h0 := hl 0 (by omega)
  rw [cellJ_zero] at h0
  have hl0 : lat1 c s ∉ F := fun h => by have := h0.1.1 h; omega
  have hd := hF.2 _ (corners4 hc s).1
  rw [deg_back1, ind_of_not_mem hl0, ind_of_mem hbk, ind_of_not_mem hbo] at hd
  by_contra hx
  rw [ind_of_not_mem hx] at hd
  omega

-- The front corners of a start cell with light lateral and front sides are joined.
--
lemma front_join (hp : StripPat F c s n) (hn : 2 ≤ n) (hc : IsCell V c) :
    Conn F (front1 c s) (front2 c s) := by
  obtain ⟨_, hl, hf⟩ := hp
  have h0 := hl 0 (by omega)
  have hf0 := hf 0 (by omega)
  rw [cellJ_zero] at h0 hf0
  have hl1 : lat1 c s ∉ F := fun h => by have := h0.1.1 h; omega
  have hl2 : lat2 c s ∉ F := fun h => by have := h0.2.1 h; omega
  have hfr : front c s ∉ F := fun h => by have := hf0.1 h; omega
  have he := ends_front c s
  by_contra hn'
  have hI : Inter V F (sideEdge c s) := by
    have hm := corners4 hc s
    refine ⟨he.isEdge hm.2.2.1 hm.2.2.2, hfr, ?_⟩
    rw [show sideEdge c s = front c s from rfl, he.conn_iff]; exact hn'
  rcases inter_dark_lat hF hT hc s hI with h | h
  · rw [← lat1_eq] at h; exact hl1 h
  · rw [← lat2_eq] at h; exact hl2 h

-- The cell beside the start cell (across `lat1`), with a light far side, has its far corners
-- in different classes: otherwise its light back side would be an inter side whose
-- neighbouring sides are both light.
--
lemma start_side_sep (hp : StripPat F c s n) (hn : 2 ≤ n) (hc : IsCell V c)
    (hsep : ¬ Conn F (back1 c s) (front1 c s)) (hfar : lat1 (nb c (latA s)) s ∉ F) :
    ¬ Conn F (back1 (nb c (latA s)) s) (front1 (nb c (latA s)) s) := by
  intro h
  set L := nb c (latA s)
  have ho := outer1_start hF hp hn hc
  have hbo := back_outer_light hF hT hp hn hc hsep
  have hV2 := (side_front_ends c s).inV (hF.1 _ ho)
  have hb1 : back1 L s ∈ V := conn_mem hF.1 hV2.1 h.symm
  have hcL : IsCell V L := by
    refine isCell_of_corners L s hb1 ?_ hV2.1 ?_
    · rw [side_back2]; exact (corners4 hc s).1
    · rw [side_front2]; exact hV2.2
  have hbe := side_back_ends c s
  have hI : Inter V F (sideEdge L s.opp) := by
    refine ⟨hbe.isEdge hb1 (corners4 hc s).1, hbo, ?_⟩
    rw [show sideEdge L s.opp = back L s from rfl, hbe.conn_iff]
    intro hx
    exact hsep ((hx.symm.trans h).trans ((side_front_ends c s).conn ho))
  rcases inter_dark_lat hF hT hcL s.opp hI with hx | hx
  · rw [latA_opp, ← lat1_eq] at hx; exact hfar hx
  · rw [latB_opp, ← lat2_eq, side_lat2] at hx
    obtain ⟨_, hl, _⟩ := hp
    have h0 := hl 0 (by omega)
    rw [cellJ_zero] at h0
    have := h0.1.1 hx; omega

-- Mirror of `back_outer_light` on the `lat2` side.
--
lemma back_outer2_light (hp : StripPat F c s n) (hn : 2 ≤ n) (hc : IsCell V c)
    (hsep : ¬ Conn F (back1 c s) (front1 c s)) : back (nb c (latB s)) s ∉ F := by
  intro hb
  set L := nb c (latB s)
  have hsep2 : ¬ Conn F (back2 c s) (front2 c s) := fun h => hsep
    ((((ends_back c s).conn hp.1).trans h).trans (front_join hF hT hp hn hc).symm)
  have ho : outer2 c s ∈ F := by
    obtain ⟨_, hl, hf⟩ := hp
    have h0 := hl 0 (by omega)
    have h1 := hl 1 (by omega)
    have hf0 := hf 0 (by omega)
    rw [cellJ_zero] at h0 hf0
    have hl0 : lat2 c s ∉ F := fun h => by have := h0.2.1 h; omega
    have hfr : front c s ∉ F := fun h => by have := hf0.1 h; omega
    have hl1 : lat2 (nb c s) s ∈ F := by
      rw [show nb c s = cellJ c s 1 by rw [← nb_cellJ, cellJ_zero]]; exact h1.2.2 rfl
    have hd := hF.2 _ (corners4 hc s).2.2.2
    rw [deg_front2, ind_of_not_mem hl0, ind_of_not_mem hfr, ind_of_mem hl1] at hd
    by_contra ho
    rw [ind_of_not_mem ho] at hd
    omega
  have hfL : front L s ∈ F := by rw [side2_front]; exact ho
  have hV1 := (side2_back_ends c s).inV (hF.1 _ hb)
  have hV2 := (side2_front_ends c s).inV (hF.1 _ ho)
  have hcL : IsCell V L := by
    refine isCell_of_corners L s ?_ hV1.2 ?_ hV2.2
    · rw [side2_back1]; exact hV1.1
    · rw [side2_front1]; exact hV2.1
  have hl1 : lat1 L s ∉ F := by
    rw [side2_lat1]
    obtain ⟨_, hl', _⟩ := hp
    have h0 := hl' 0 (by omega)
    rw [cellJ_zero] at h0
    exact fun h => by have := h0.2.1 h; omega
  have hLL : Conn F (back1 L s) (front1 L s) := by
    by_cases hl : lat2 L s ∈ F
    · exact ((((ends_back L s).conn hb).trans ((ends_lat2 L s).conn hl)).trans
        ((ends_front L s).conn hfL).symm)
    · exact hT L hcL s hb hfL hl1 hl
  rw [side2_back1, side2_front1] at hLL
  exact hsep2 hLL

lemma back_down2 (hp : StripPat F c s n) (hn : 2 ≤ n) (hc : IsCell V c)
    (hsep : ¬ Conn F (back1 c s) (front1 c s)) : lat2 (nb c s.opp) s ∈ F := by
  have hbo := back_outer2_light hF hT hp hn hc hsep
  obtain ⟨hbk, hl, _⟩ := hp
  have h0 := hl 0 (by omega)
  rw [cellJ_zero] at h0
  have hl0 : lat2 c s ∉ F := fun h => by have := h0.2.1 h; omega
  have hd := hF.2 _ (corners4 hc s).2.1
  rw [deg_back2, ind_of_not_mem hl0, ind_of_mem hbk, ind_of_not_mem hbo] at hd
  by_contra hx
  rw [ind_of_not_mem hx] at hd
  omega

end start

lemma mem_flipCol_out {F : Finset Edge} {c : Pt} {s : Side} {n : ℕ} {e : Edge}
    (h : ∀ j < n, e ∉ cellE (cellJ c s j)) : e ∈ flipCol F c s n ↔ e ∈ F := by
  rw [mem_flipCol, nOn_eq c s n e ∅ (fun j hj => by simp [h j hj]) (by simp)]
  simp

lemma side2_lat2_not_mem (c : Pt) (s : Side) (j m : ℕ) :
    lat2 (nb (cellJ c s j) (latB s)) s ∉ cellE (cellJ c s m) := by
  obtain ⟨x, y⟩ := c
  cases s <;> simp [cellE, lat2, latB, nb, cellJ, bot, top, lft, rgt] <;> omega

section endside

variable {V : Finset Pt} {F : Finset Edge} {c : Pt} {s : Side} {k : ℕ}
  (hs : Solid V) (x0 : Pt) (hconn : ∀ z ∈ V, Conn (GE V) x0 z)
  (hF : Deg2 V F) (hT : NoTypeIII V F) (hk : k % 2 = 0)
  (hcell : ∀ j ≤ k + 1, IsCell V (cellJ c s j)) (hpat : StripPat F c s (k + 2))
  (hsep : ¬ Conn F (back1 c s) (front1 c s))
include hs x0 hconn hF hT hk hcell hpat hsep

-- A cell beside the end cell (across `lat1`) with dark outer sides and a light far side is
-- Type III after the strip: its near corners are the end cell's `lat1` corners, which the
-- strip separates.
--
omit hs x0 hconn in
theorem beside_end1 (hb : outer1 (cellJ c s k) s ∈ F) (hf : outer1 (cellJ c s (k + 1)) s ∈ F)
    (hl : lat1 (nb (cellJ c s (k + 1)) (latA s)) s ∉ F) :
    ¬ NoTypeIII V (flipCol F c s (k + 2)) := by
  intro hT'
  set u := cellJ c s (k + 1)
  set L := nb u (latA s)
  have hcu : IsCell V u := hcell (k + 1) le_rfl
  have hnbk : nb (cellJ c s k) s = u := nb_cellJ c s k
  have hbL : back L s = outer1 (cellJ c s k) s := by
    rw [← side_back_next, hnbk]
  have hfL : front L s = outer1 u s := side_front u s
  have hout : ∀ e, (e = outer1 (cellJ c s k) s ∨ e = outer1 u s ∨ e = lat1 L s) →
      ∀ j < k + 2, e ∉ cellE (cellJ c s j) := by
    rintro e (rfl | rfl | rfl) j _
    · exact outer1_not_mem c s k j
    · exact outer1_not_mem c s (k + 1) j
    · exact side_lat1_not_mem c s (k + 1) j
  have hb' : back L s ∈ flipCol F c s (k + 2) := by
    rw [hbL, mem_flipCol_out (hout _ (Or.inl rfl))]; exact hb
  have hf' : front L s ∈ flipCol F c s (k + 2) := by
    rw [hfL, mem_flipCol_out (hout _ (Or.inr (Or.inl rfl)))]; exact hf
  have hl' : lat1 L s ∉ flipCol F c s (k + 2) := by
    rw [mem_flipCol_out (hout _ (Or.inr (Or.inr rfl)))]; exact hl
  have hl2' : lat2 L s ∉ flipCol F c s (k + 2) := by
    rw [side_lat2, show k + 2 = (k + 1) + 1 from rfl,
      flipCol_off F c s (k + 1) (fun i hi => lat1_not_mem c s (by omega)), mem_flip_iff]
    have : lat1 u s ∈ F := (hpat.2.1 (k + 1) (by omega)).1.2 (by omega)
    intro h; exact (h.1 this) (by rw [cellE_frame u s]; simp [u])
  have hV1 := (side_back_ends u s).inV (hF.1 _ (hbL ▸ hb))
  have hV2 := (side_front_ends u s).inV (hF.1 _ hf)
  have hcL : IsCell V L := by
    refine isCell_of_corners L s hV1.1 ?_ hV2.1 ?_
    · rw [side_back2]; exact hV1.2
    · rw [side_front2]; exact hV2.2
  have hLL := hT' L hcL s hb' hf' hl' hl2'
  have hc := end_corners hF hT hk hcell hpat hsep
  apply hc.2.2
  have e1 := side_back_ends u s
  have e2 := side_front_ends u s
  rw [← hfL] at e2
  exact ((e1.conn hb').symm.trans hLL).trans (e2.conn hf')

-- Mirror of `beside_end1` across `lat2`.
--
omit hs x0 hconn in
theorem beside_end2 (hb : outer2 (cellJ c s k) s ∈ F) (hf : outer2 (cellJ c s (k + 1)) s ∈ F)
    (hl : lat2 (nb (cellJ c s (k + 1)) (latB s)) s ∉ F) :
    ¬ NoTypeIII V (flipCol F c s (k + 2)) := by
  intro hT'
  set u := cellJ c s (k + 1)
  set L := nb u (latB s)
  have hnbk : nb (cellJ c s k) s = u := nb_cellJ c s k
  have hbL : back L s = outer2 (cellJ c s k) s := by
    rw [outer2_side_nb_next, hnbk]; rfl
  have hfL : front L s = outer2 u s := side2_front u s
  have hout : ∀ e, (e = outer2 (cellJ c s k) s ∨ e = outer2 u s ∨ e = lat2 L s) →
      ∀ j < k + 2, e ∉ cellE (cellJ c s j) := by
    rintro e (rfl | rfl | rfl) j _
    · exact outer2_not_mem c s k j
    · exact outer2_not_mem c s (k + 1) j
    · exact side2_lat2_not_mem c s (k + 1) j
  have hb' : back L s ∈ flipCol F c s (k + 2) := by
    rw [hbL, mem_flipCol_out (hout _ (Or.inl rfl))]; exact hb
  have hf' : front L s ∈ flipCol F c s (k + 2) := by
    rw [hfL, mem_flipCol_out (hout _ (Or.inr (Or.inl rfl)))]; exact hf
  have hl' : lat2 L s ∉ flipCol F c s (k + 2) := by
    rw [mem_flipCol_out (hout _ (Or.inr (Or.inr rfl)))]; exact hl
  have hl1' : lat1 L s ∉ flipCol F c s (k + 2) := by
    rw [side2_lat1, show k + 2 = (k + 1) + 1 from rfl,
      flipCol_off F c s (k + 1) (fun i hi => lat2_not_mem c s (by omega)), mem_flip_iff]
    have : lat2 u s ∈ F := (hpat.2.1 (k + 1) (by omega)).2.2 (by omega)
    intro h; exact (h.1 this) (by rw [cellE_frame u s]; simp [u])
  have hV1 := (side2_back_ends u s).inV (hF.1 _ (hbL ▸ hb))
  have hV2 := (side2_front_ends u s).inV (hF.1 _ hf)
  have hcL : IsCell V L := by
    refine isCell_of_corners L s ?_ hV1.2 ?_ hV2.2
    · rw [side2_back1]; exact hV1.1
    · rw [side2_front1]; exact hV2.1
  have hLL := hT' L hcL s hb' hf' hl1' hl'
  rw [side2_back1, side2_front1] at hLL
  have hc := end_corners hF hT hk hcell hpat hsep
  exact hc.2.2 ((hc.1.trans hLL).trans hc.2.1.symm)

-- An alternating cell `w` sharing no side with the strip, whose flip splits the end cell's
-- lateral sides, is Type III after the strip. By `split_symm` the end cell splits `w`, and
-- the strip's odd remainder only merges the classes of `back1 c` and `front1 c`, which would
-- otherwise have to be joined in `F`.
--
omit hs x0 hconn in
theorem split_end_t3 {w : Pt} {tw : Side} (hw : IsCell V w)
    (l1 : lat1 w tw ∈ F) (l2 : lat2 w tw ∈ F) (bw : back w tw ∉ F) (fw : front w tw ∉ F)
    (hdisj : ∀ j < k + 2, ∀ x ∈ cellE w, x ∉ cellE (cellJ c s j))
    (hm1 : ¬ IsMid c s k (back1 w tw)) (hm2 : ¬ IsMid c s k (back2 w tw))
    (hsplit : ¬ Conn (flip F w) (back1 (cellJ c s (k + 1)) s) (back2 (cellJ c s (k + 1)) s)) :
    ¬ NoTypeIII V (flipCol F c s (k + 2)) := by
  intro hT'
  set u := cellJ c s (k + 1)
  have hu : IsCell V u := hcell (k + 1) le_rfl
  have hse := end_same hT hk hcell hpat
  have hsw : Conn F (back1 w tw) (back2 w tw) :=
    (frame_of_allConn (alt_corners_conn hT hw (alt_of_lats l1 l2 bw fw)) tw).1
  have hl := hpat.2.1
  have hf := hpat.2.2
  have uL1 : lat1 u s ∈ F := (hl (k + 1) (by omega)).1.2 (by omega)
  have uL2 : lat2 u s ∈ F := (hl (k + 1) (by omega)).2.2 (by omega)
  have uB : back u s ∉ F := by
    rw [back_cellJ_succ]; intro h; have := (hf k (by omega)).1 h; omega
  have uF : front u s ∉ F := by
    intro h; have := (hf (k + 1) (by omega)).1 h; omega
  have hdu : ∀ x, x ∈ cellE w → x ∉ cellE u := fun x hx => hdisj (k + 1) (by omega) x hx
  have hsym := split_symm hF hw hu l1 l2 bw fw uL1 uL2 uB uF hsw hse hdu
  have hne : ¬ Conn (flip F u) (back1 w tw) (back2 w tw) := fun h => hsplit (hsym.2 h)
  obtain ⟨F1, hF1, _, _, hsub, _, hodd⟩ := strip_even_rel k hk F hF hcell hpat hsep hse
  have hkeep : ∀ x ∈ cellE w, (x ∈ flipCol F c s (k + 2) ↔ x ∈ F) := fun x hx =>
    mem_flipCol_out (fun j hj => hdisj j hj x hx)
  have sw : ∀ x, x = lat1 w tw ∨ x = lat2 w tw ∨ x = back w tw ∨ x = front w tw → x ∈ cellE w := by
    intro x hx; rw [cellE_frame w tw]; rcases hx with rfl | rfl | rfl | rfl <;> simp
  have ha' : Alt (flipCol F c s (k + 2)) w := alt_of_lats
    ((hkeep _ (sw _ (Or.inl rfl))).2 l1) ((hkeep _ (sw _ (Or.inr (Or.inl rfl)))).2 l2)
    (fun h => bw ((hkeep _ (sw _ (Or.inr (Or.inr (Or.inl rfl))))).1 h))
    (fun h => fw ((hkeep _ (sw _ (Or.inr (Or.inr (Or.inr rfl))))).1 h))
  have hc := (frame_of_allConn (alt_corners_conn hT' hw ha') tw).1
  rw [hodd _ _ hm1 hm2] at hc
  rcases hc with h | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [hF1] at h; exact hne h
  · exact hsep (((hsub _ _ h1).symm.trans hsw).trans (hsub _ _ h2).symm)
  · exact hsep (((hsub _ _ h2).trans hsw.symm).trans (hsub _ _ h1))

end endside

end SolidGridHam
