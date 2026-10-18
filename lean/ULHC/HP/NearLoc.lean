/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
import ULHC.Near
import ULHC.HP.RelPF

/-!
# ULHC's near lemmas with local hypotheses

ULHC's near lemmas (Near.lean, Chain.lean, Walk.lean) assume degree 2 at every point and no
Type III cell anywhere. Their proofs use degree 2 only at named corners of the strip's cells and
"not Type III" only at named cells (audit of 2026-10-12). Here each lemma takes exactly those
facts, so the path-factor port can supply them: the corners of a restricted strip's cells are
never `s` or `t`, and the named cells are either cells of restricted strips or the E1-E3 cells.
The originals follow by instantiating the local facts from `Deg2` and `NoTypeIII`.
-/

namespace ULHC

namespace HP

open Finset Classical

section loc

variable {V : Finset Pt} {F : Finset Edge} {P : Finset Pt} (hV : Inside V F)
include hV

-- **A cut side has a dark neighbouring side** (`cut_has_dark_lat_l`), with degree 2 only at the
-- side's two far corners.
--
lemma cut_dark_lat_loc (hB : Border V F P) {w : Pt} (hw : IsCell V w) (s : Side)
    (hcut : Cut P (sideEdge w s))
    (hd1 : deg F (front1 w s) = 2) (hd2 : deg F (front2 w s) = 2)
    (hTr : IsCell V (nb w s) → NotTypeIII V F (nb w s)) :
    sideEdge w (latA s) ∈ F ∨ sideEdge w (latB s) ∈ F := by
  by_contra hn
  push Not at hn
  obtain ⟨n1, n2⟩ := hn
  rw [← lat1_eq] at n1
  rw [← lat2_eq] at n2
  have hfr : front w s ∉ F := fun h => hB.not_cut h hcut
  obtain ⟨wb1, wb2, wf1, wf2⟩ := isCell_corners hw s
  have d1 := deg_front1 w s F
  have d2 := deg_front2 w s F
  rw [hd1] at d1
  rw [hd2] at d2
  have i1 : ind F (lat1 w s) = 0 := by simp [ind, n1]
  have i2 : ind F (lat2 w s) = 0 := by simp [ind, n2]
  have i3 : ind F (front w s) = 0 := by simp [ind, hfr]
  have mem1 : ∀ e, ind F e = 1 → e ∈ F := by
    intro e h; unfold ind at h; split_ifs at h with h'; exact h'
  rw [i1, i3] at d1
  rw [i2, i3] at d2
  have l1 : lat1 (nb w s) s ∈ F := by
    have := ind_le_one F (lat1 (nb w s) s)
    have := ind_le_one F (outer1 w s)
    exact mem1 _ (by omega)
  have l2 : lat2 (nb w s) s ∈ F := by
    have := ind_le_one F (lat2 (nb w s) s)
    have := ind_le_one F (outer2 w s)
    exact mem1 _ (by omega)
  set r := nb w s
  have c1 : Conn F (back1 r s) (front1 r s) := (ends_lat1 r s).conn l1
  have c2 : Conn F (back2 r s) (front2 r s) := (ends_lat2 r s).conn l2
  have rf1 : front1 r s ∈ V := conn_mem hV (by rw [back1_nb]; exact wf1) c1
  have rf2 : front2 r s ∈ V := conn_mem hV (by rw [back2_nb]; exact wf2) c2
  have hr : IsCell V r := isCell_of_corners r s (by rw [back1_nb]; exact wf1)
    (by rw [back2_nb]; exact wf2) rf1 rf2
  have hjoin : Conn F (back1 r s) (back2 r s) := by
    by_cases hf : front r s ∈ F
    · exact (c1.trans ((ends_front r s).conn hf)).trans c2.symm
    · have hbk : back r s ∉ F := by rw [back_nb]; exact hfr
      have ha : Alt F r := by
        rw [lat1_eq] at l1
        rw [lat2_eq] at l2
        simp only [back, front, sideEdge] at hbk hf
        obtain ⟨x, y⟩ := r
        cases s <;> simp only [latA, latB, sideEdge, Side.opp] at l1 l2 hbk hf <;> unfold Alt <;>
          tauto
      obtain ⟨k1, k2, k3⟩ := alt_corners_conn' (hTr hr) ha
      obtain ⟨x, y⟩ := r
      cases s <;> simp only [back1, back2] at * <;>
        first
        | exact k1
        | exact k2.symm.trans k3
        | exact k1.symm.trans k3
        | exact k2
  rw [back1_nb, back2_nb] at hjoin
  apply hcut |> fun h => ?_
  have := hB.same_side hjoin
  have hends := ends_front w s
  unfold Cut at hcut
  rcases hends with ⟨q1, q2⟩ | ⟨q1, q2⟩ <;> simp only [front] at q1 q2 <;> rw [q1, q2] at hcut <;>
    tauto

-- **An inter side has a dark neighbouring side** (`inter_dark_lat_l`), local degrees.
--
lemma inter_dark_lat_loc {w : Pt} (hw : IsCell V w) (s : Side) (h : Inter V F (sideEdge w s))
    (hd1 : deg F (front1 w s) = 2) (hd2 : deg F (front2 w s) = 2)
    (hTr : IsCell V (nb w s) → NotTypeIII V F (nb w s)) :
    sideEdge w (latA s) ∈ F ∨ sideEdge w (latB s) ∈ F := by
  set e := sideEdge w s
  have hB : Border V F (cls V F e.p) :=
    ⟨Finset.filter_subset _ _, fun u hu v hv => closed_cls hV e.p u hu v hv⟩
  apply cut_dark_lat_loc hV hB hw s _ hd1 hd2 hTr
  unfold Cut
  have hp : e.p ∈ cls V F e.p := mem_cls_self h.1.1
  have hq : e.q ∉ cls V F e.p := by
    simp only [cls, Finset.mem_filter, not_and]; exact fun _ => h.2.2
  tauto

variable {c : Pt} {s : Side} {n : ℕ}

-- `outer1_start`, degree 2 only at `front1 c`.
--
omit hV in
lemma outer1_start_loc (hp : StripPat F c s n) (hn : 2 ≤ n) (hd : deg F (front1 c s) = 2) :
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
  have hd' := hd
  rw [deg_front1, ind_of_not_mem hl0, ind_of_not_mem hfr, ind_of_mem hl1] at hd'
  by_contra ho
  rw [ind_of_not_mem ho] at hd'
  omega

-- `back_outer_light`, local: degree 2 at `front1 c`, the cell beside not Type III.
--
lemma back_outer_light_loc (hp : StripPat F c s n) (hn : 2 ≤ n)
    (hsep : ¬ Conn F (back1 c s) (front1 c s)) (hd : deg F (front1 c s) = 2)
    (hTL : IsCell V (nb c (latA s)) → NotTypeIII V F (nb c (latA s))) :
    back (nb c (latA s)) s ∉ F := by
  intro hb
  set L := nb c (latA s)
  have ho := outer1_start_loc hp hn hd
  have hfL : front L s ∈ F := by rw [side_front]; exact ho
  have hV1 := (side_back_ends c s).inV (hV _ hb)
  have hV2 := (side_front_ends c s).inV (hV _ ho)
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
      exact hTL hcL s hb hfL hl hl2
  exact hsep ((((side_back_ends c s).conn hb).symm.trans hLL).trans
    ((side_front_ends c s).conn ho))

-- `back_down`, local: degree 2 at `back1 c` and `front1 c`, the cell beside not Type III.
--
lemma back_down_loc (hp : StripPat F c s n) (hn : 2 ≤ n)
    (hsep : ¬ Conn F (back1 c s) (front1 c s)) (hdb : deg F (back1 c s) = 2)
    (hd : deg F (front1 c s) = 2)
    (hTL : IsCell V (nb c (latA s)) → NotTypeIII V F (nb c (latA s))) :
    lat1 (nb c s.opp) s ∈ F := by
  have hbo := back_outer_light_loc hV hp hn hsep hd hTL
  obtain ⟨hbk, hl, _⟩ := hp
  have h0 := hl 0 (by omega)
  rw [cellJ_zero] at h0
  have hl0 : lat1 c s ∉ F := fun h => by have := h0.1.1 h; omega
  have hd' := hdb
  rw [deg_back1, ind_of_not_mem hl0, ind_of_mem hbk, ind_of_not_mem hbo] at hd'
  by_contra hx
  rw [ind_of_not_mem hx] at hd'
  omega

-- `front_join`, local: degree 2 at the front corners of `nb c s`'s ... (the inter side's
-- far corners) and the cell ahead not Type III.
--
lemma front_join_loc (hp : StripPat F c s n) (hn : 2 ≤ n) (hc : IsCell V c)
    (hd1 : deg F (front1 c s) = 2) (hd2 : deg F (front2 c s) = 2)
    (hTr : IsCell V (nb c s) → NotTypeIII V F (nb c s)) :
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
  rcases inter_dark_lat_loc hV hc s hI hd1 hd2 hTr with h | h
  · rw [← lat1_eq] at h; exact hl1 h
  · rw [← lat2_eq] at h; exact hl2 h

-- `start_side_sep`, local: degrees at `front1 c` and at the back corners of the cell beside
-- (the inter side's far corners for `L` in direction `s.opp`), cells beside / behind not Type III.
--
lemma start_side_sep_loc (hp : StripPat F c s n) (hn : 2 ≤ n) (hc : IsCell V c)
    (hsep : ¬ Conn F (back1 c s) (front1 c s)) (hfar : lat1 (nb c (latA s)) s ∉ F)
    (hd : deg F (front1 c s) = 2)
    (hd1 : deg F (front1 (nb c (latA s)) s.opp) = 2) (hd2 : deg F (front2 (nb c (latA s)) s.opp) = 2)
    (hTL : IsCell V (nb c (latA s)) → NotTypeIII V F (nb c (latA s)))
    (hTr : IsCell V (nb (nb c (latA s)) s.opp) → NotTypeIII V F (nb (nb c (latA s)) s.opp)) :
    ¬ Conn F (back1 (nb c (latA s)) s) (front1 (nb c (latA s)) s) := by
  intro h
  set L := nb c (latA s)
  have ho := outer1_start_loc hp hn hd
  have hbo := back_outer_light_loc hV hp hn hsep hd hTL
  have hV2 := (side_front_ends c s).inV (hV _ ho)
  have hb1 : back1 L s ∈ V := conn_mem hV hV2.1 h.symm
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
  rcases inter_dark_lat_loc hV hcL s.opp hI hd1 hd2 hTr with hx | hx
  · rw [latA_opp, ← lat1_eq] at hx; exact hfar hx
  · rw [latB_opp, ← lat2_eq, side_lat2] at hx
    obtain ⟨_, hl, _⟩ := hp
    have h0 := hl 0 (by omega)
    rw [cellJ_zero] at h0
    have := h0.1.1 hx; omega

-- `back_outer2_light`, local.
--
lemma back_outer2_light_loc (hp : StripPat F c s n) (hn : 2 ≤ n) (hc : IsCell V c)
    (hsep : ¬ Conn F (back1 c s) (front1 c s))
    (hdf1 : deg F (front1 c s) = 2) (hdf2 : deg F (front2 c s) = 2)
    (hTr : IsCell V (nb c s) → NotTypeIII V F (nb c s))
    (hTL : IsCell V (nb c (latB s)) → NotTypeIII V F (nb c (latB s))) :
    back (nb c (latB s)) s ∉ F := by
  intro hb
  set L := nb c (latB s)
  have hsep2 : ¬ Conn F (back2 c s) (front2 c s) := fun h => hsep
    ((((ends_back c s).conn hp.1).trans h).trans (front_join_loc hV hp hn hc hdf1 hdf2 hTr).symm)
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
    have hd := hdf2
    rw [deg_front2, ind_of_not_mem hl0, ind_of_not_mem hfr, ind_of_mem hl1] at hd
    by_contra ho
    rw [ind_of_not_mem ho] at hd
    omega
  have hfL : front L s ∈ F := by rw [side2_front]; exact ho
  have hV1 := (side2_back_ends c s).inV (hV _ hb)
  have hV2 := (side2_front_ends c s).inV (hV _ ho)
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
    · exact hTL hcL s hb hfL hl1 hl
  rw [side2_back1, side2_front1] at hLL
  exact hsep2 hLL

-- `back_down2`, local.
--
lemma back_down2_loc (hp : StripPat F c s n) (hn : 2 ≤ n) (hc : IsCell V c)
    (hsep : ¬ Conn F (back1 c s) (front1 c s))
    (hdb2 : deg F (back2 c s) = 2) (hdf1 : deg F (front1 c s) = 2) (hdf2 : deg F (front2 c s) = 2)
    (hTr : IsCell V (nb c s) → NotTypeIII V F (nb c s))
    (hTL : IsCell V (nb c (latB s)) → NotTypeIII V F (nb c (latB s))) :
    lat2 (nb c s.opp) s ∈ F := by
  have hbo := back_outer2_light_loc hV hp hn hc hsep hdf1 hdf2 hTr hTL
  obtain ⟨hbk, hl, _⟩ := hp
  have h0 := hl 0 (by omega)
  rw [cellJ_zero] at h0
  have hl0 : lat2 c s ∉ F := fun h => by have := h0.2.1 h; omega
  have hd := hdb2
  rw [deg_back2, ind_of_not_mem hl0, ind_of_mem hbk, ind_of_not_mem hbo] at hd
  by_contra hx
  rw [ind_of_not_mem hx] at hd
  omega

end loc

section endPF

variable {V : Finset Pt} {F : Finset Edge} {c : Pt} {s : Side} {k : ℕ} {s0 t0 : Pt}
  (hF : Deg2Off V F s0 t0) (hs0 : s0 ∈ V) (hds : deg F s0 = 1) (hk : k % 2 = 0)
  (hcell : ∀ j ≤ k + 1, IsCell V (cellJ c s j))
  (hcor : ∀ j ≤ k + 1, ¬ IsCorner s0 (cellJ c s j) ∧ ¬ IsCorner t0 (cellJ c s j))
  (hpat : StripPat F c s (k + 2)) (hsep : ¬ Conn F (back1 c s) (front1 c s))
  (hsame : Conn F (back1 (cellJ c s (k + 1)) s) (back2 (cellJ c s (k + 1)) s))
  (hneut : ncomp V (flipCol F c s (k + 2)) = ncomp V F)
include hF hs0 hds hk hcell hcor hpat hsep hsame hneut

-- **`end_corners` for path-factors**, for a count-neutral strip.
--
lemma end_corners_pf :
    Conn (flipCol F c s (k + 2)) (back1 (cellJ c s (k + 1)) s) (back2 (cellJ c s (k + 1)) s) ∧
      Conn (flipCol F c s (k + 2)) (front1 (cellJ c s (k + 1)) s)
        (front2 (cellJ c s (k + 1)) s) ∧
      ¬ Conn (flipCol F c s (k + 2)) (back1 (cellJ c s (k + 1)) s)
        (front1 (cellJ c s (k + 1)) s) := by
  refine ⟨?_, (ends_front _ s).conn (front_end_after hk hpat),
    even_end_border_pf k hk F hF hs0 hds hcell hcor hpat hsep hsame hneut⟩
  obtain ⟨F1, hF1, _, _, _, hodd, _, _⟩ :=
    strip_even_rel_pf k hk F hF hs0 hds hcell hcor hpat hsep hsame
  have hb : back (cellJ c s (k + 1)) s ∈ F1 := by
    rw [hF1, mem_flip_iff]
    have uB : back (cellJ c s (k + 1)) s ∉ F := by
      rw [back_cellJ_succ]; intro h; have := (hpat.2.2 k (by omega)).1 h; omega
    have : back (cellJ c s (k + 1)) s ∈ cellE (cellJ c s (k + 1)) := by
      rw [cellE_frame _ s]; simp
    tauto
  have n1 := (end_not_mid c s k).1
  have n2 : ¬ IsMid c s k (back2 (cellJ c s (k + 1)) s) := by
    rw [← nb_cellJ, back2_nb]
    rintro ⟨j, _, hj, h | h⟩
    · exact (front_corner_ne c s (i := k) (j := j) (by omega)).2.2.1 h
    · exact (front_corner_ne c s (i := k) (j := j) (by omega)).2.2.2 h
  exact (hodd _ _ n1 n2).2 (Or.inl ((ends_back _ s).conn hb))

-- **`beside_end1` for path-factors**: the cell `L` beside the end cell (across `lat1`), with dark
-- outer sides and a light far side, is Type III after a count-neutral strip.
--
theorem beside_end1_pfW (hb : outer1 (cellJ c s k) s ∈ F) (hf : outer1 (cellJ c s (k + 1)) s ∈ F)
    (hl : lat1 (nb (cellJ c s (k + 1)) (latA s)) s ∉ F)
    (hLt : IsCorner t0 (nb (cellJ c s (k + 1)) (latA s)) → t0 ∈ V) :
    IsCell V (nb (cellJ c s (k + 1)) (latA s)) ∧
      ¬ NotTypeIII V (flipCol F c s (k + 2)) (nb (cellJ c s (k + 1)) (latA s)) := by
  set u := cellJ c s (k + 1)
  set L := nb u (latA s)
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
  have hcu := isCell_corners (hcell (k + 1) le_rfl) s
  -- The outer corners of `L` come from the outer edges `hb`, `hf`; neither is a phantom `t0`,
  -- since `t0` is not a corner of `L`.
  --
  have hcL : IsCell V L := by
    refine isCell_of_corners L s
      (memW hV1.1 hs0 (fun h => hLt (h ▸ isCorner_back1 L s))) ?_
      (memW hV2.1 hs0 (fun h => hLt (h ▸ isCorner_front1 L s))) ?_
    · rw [side_back2]; exact hcu.1
    · rw [side_front2]; exact hcu.2.2.1
  refine ⟨hcL, fun hLL => ?_⟩
  have hc := end_corners_pf hF hs0 hds hk hcell hcor hpat hsep hsame hneut
  apply hc.2.2
  have e1 := side_back_ends u s
  have e2 := side_front_ends u s
  rw [← hfL] at e2
  exact ((e1.conn hb').symm.trans (hLL s hb' hf' hl' hl2')).trans (e2.conn hf')

-- `beside_end1_pfW` when `t0` is not a corner of the cell beside the end cell.
--
theorem beside_end1_pf (hb : outer1 (cellJ c s k) s ∈ F) (hf : outer1 (cellJ c s (k + 1)) s ∈ F)
    (hl : lat1 (nb (cellJ c s (k + 1)) (latA s)) s ∉ F)
    (hLt : ¬ IsCorner t0 (nb (cellJ c s (k + 1)) (latA s))) :
    IsCell V (nb (cellJ c s (k + 1)) (latA s)) ∧
      ¬ NotTypeIII V (flipCol F c s (k + 2)) (nb (cellJ c s (k + 1)) (latA s)) :=
  beside_end1_pfW hF hs0 hds hk hcell hcor hpat hsep hsame hneut hb hf hl (fun hc => absurd hc hLt)

-- **`beside_end2` for path-factors** (mirror across `lat2`).
--
theorem beside_end2_pfW (hb : outer2 (cellJ c s k) s ∈ F) (hf : outer2 (cellJ c s (k + 1)) s ∈ F)
    (hl : lat2 (nb (cellJ c s (k + 1)) (latB s)) s ∉ F)
    (hLt : IsCorner t0 (nb (cellJ c s (k + 1)) (latB s)) → t0 ∈ V) :
    IsCell V (nb (cellJ c s (k + 1)) (latB s)) ∧
      ¬ NotTypeIII V (flipCol F c s (k + 2)) (nb (cellJ c s (k + 1)) (latB s)) := by
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
  have hcu := isCell_corners (hcell (k + 1) le_rfl) s
  have hcL : IsCell V L := by
    refine isCell_of_corners L s ?_
      (memW hV1.2 hs0 (fun h => hLt (h ▸ isCorner_back2 L s))) ?_
      (memW hV2.2 hs0 (fun h => hLt (h ▸ isCorner_front2 L s)))
    · rw [side2_back1]; exact hcu.2.1
    · rw [side2_front1]; exact hcu.2.2.2
  refine ⟨hcL, fun hT' => ?_⟩
  have hLL := hT' s hb' hf' hl1' hl'
  rw [side2_back1, side2_front1] at hLL
  have hc := end_corners_pf hF hs0 hds hk hcell hcor hpat hsep hsame hneut
  exact hc.2.2 ((hc.1.trans hLL).trans hc.2.1.symm)

-- `beside_end2_pfW` when `t0` is not a corner of the cell beside the end cell.
--
theorem beside_end2_pf (hb : outer2 (cellJ c s k) s ∈ F) (hf : outer2 (cellJ c s (k + 1)) s ∈ F)
    (hl : lat2 (nb (cellJ c s (k + 1)) (latB s)) s ∉ F)
    (hLt : ¬ IsCorner t0 (nb (cellJ c s (k + 1)) (latB s))) :
    IsCell V (nb (cellJ c s (k + 1)) (latB s)) ∧
      ¬ NotTypeIII V (flipCol F c s (k + 2)) (nb (cellJ c s (k + 1)) (latB s)) :=
  beside_end2_pfW hF hs0 hds hk hcell hcor hpat hsep hsame hneut hb hf hl (fun hc => absurd hc hLt)

-- **`split_end_t3` for path-factors.** An alternating cell `w` sharing no side with the strip,
-- not Type III in `F`, whose flip splits (no twist) and separates the end cell's lateral sides,
-- is Type III after a count-neutral strip.
--
theorem split_end_t3_pf {w : Pt} {tw : Side} (hw : IsCell V w)
    (l1 : lat1 w tw ∈ F) (l2 : lat2 w tw ∈ F) (bw : back w tw ∉ F) (fw : front w tw ∉ F)
    (hTw : NotTypeIII V F w)
    (hdisj : ∀ j < k + 2, ∀ x ∈ cellE w, x ∉ cellE (cellJ c s j))
    (hm1 : ¬ IsMid c s k (back1 w tw)) (hm2 : ¬ IsMid c s k (back2 w tw))
    (hspw : ncomp V (flip F w) = ncomp V F + 1)
    (hsplit : ¬ Conn (flip F w) (back1 (cellJ c s (k + 1)) s) (back2 (cellJ c s (k + 1)) s)) :
    ¬ NotTypeIII V (flipCol F c s (k + 2)) w := by
  intro hT'
  set u := cellJ c s (k + 1)
  have hu : IsCell V u := hcell (k + 1) le_rfl
  have hsw : Conn F (back1 w tw) (back2 w tw) :=
    (frame_of_allConn (alt_corners_conn' hTw (alt_of_lats l1 l2 bw fw)) tw).1
  have hl := hpat.2.1
  have hf := hpat.2.2
  have uL1 : lat1 u s ∈ F := (hl (k + 1) (by omega)).1.2 (by omega)
  have uL2 : lat2 u s ∈ F := (hl (k + 1) (by omega)).2.2 (by omega)
  have uB : back u s ∉ F := by
    rw [back_cellJ_succ]; intro h; have := (hf k (by omega)).1 h; omega
  have uF : front u s ∉ F := by
    intro h; have := (hf (k + 1) (by omega)).1 h; omega
  have hdu : ∀ x, x ∈ cellE w → x ∉ cellE u := fun x hx => hdisj (k + 1) (by omega) x hx
  obtain ⟨F1, hF1, _, hsub, _, hodd, hcnt, _⟩ :=
    strip_even_rel_pf k hk F hF hs0 hds hcell hcor hpat hsep hsame
  have hspu : ncomp V (flip F u) = ncomp V F + 1 := by rw [← hF1]; omega
  have hsym := split_symm_pf hF hs0 hds hw hu l1 l2 bw fw uL1 uL2 uB uF hdu hspw hspu
  have hne : ¬ Conn (flip F u) (back1 w tw) (back2 w tw) := fun h => hsplit (hsym.2 h)
  have hkeep : ∀ x ∈ cellE w, (x ∈ flipCol F c s (k + 2) ↔ x ∈ F) := fun x hx =>
    mem_flipCol_out (fun j hj => hdisj j hj x hx)
  have sw : ∀ x, x = lat1 w tw ∨ x = lat2 w tw ∨ x = back w tw ∨ x = front w tw → x ∈ cellE w := by
    intro x hx; rw [cellE_frame w tw]; rcases hx with rfl | rfl | rfl | rfl <;> simp
  have ha' : Alt (flipCol F c s (k + 2)) w := alt_of_lats
    ((hkeep _ (sw _ (Or.inl rfl))).2 l1) ((hkeep _ (sw _ (Or.inr (Or.inl rfl)))).2 l2)
    (fun h => bw ((hkeep _ (sw _ (Or.inr (Or.inr (Or.inl rfl))))).1 h))
    (fun h => fw ((hkeep _ (sw _ (Or.inr (Or.inr (Or.inr rfl))))).1 h))
  have hc := (frame_of_allConn (alt_corners_conn' hT' ha') tw).1
  rw [hodd _ _ hm1 hm2] at hc
  rcases hc with h | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [hF1] at h; exact hne h
  · exact hsep (((hsub _ _ h1).symm.trans hsw).trans (hsub _ _ h2).symm)
  · exact hsep (((hsub _ _ h2).trans hsw.symm).trans (hsub _ _ h1))

end endPF

section pdang

-- `t0` is a corner of no cell of `V ∪ {t0}`: a phantom endpoint with no square around it.
--
def PDang (V : Finset Pt) (t0 : Pt) : Prop := ∀ c, IsCell (insert t0 V) c → ¬ IsCorner t0 c

lemma memT {V : Finset Pt} {s0 t0 z : Pt} (hz : z ∈ insert s0 (insert t0 V)) (hs0 : s0 ∈ V) :
    z ∈ insert t0 V := by
  rcases Finset.mem_insert.1 hz with h | h
  · exact Finset.mem_insert_of_mem (h ▸ hs0)
  · exact h

-- A square with dark back and front sides has its four corners on edges of `F`, so it is a cell
-- of `V ∪ {t0}`.
--
lemma cellT_of_bf {V : Finset Pt} {F : Finset Edge} {s0 t0 X : Pt} {s : Side}
    (hF : Deg2Off V F s0 t0) (hs0 : s0 ∈ V) (hb : back X s ∈ F) (hf : front X s ∈ F) :
    IsCell (insert t0 V) X := by
  have h1 := (ends_back X s).inV (hF.1 _ hb)
  have h2 := (ends_front X s).inV (hF.1 _ hf)
  exact isCell_of_corners X s (memT h1.1 hs0) (memT h1.2 hs0) (memT h2.1 hs0) (memT h2.2 hs0)

-- With `PDang`, a square with corner `t0` is never Type III.
--
lemma notT3_pdang {V : Finset Pt} {F : Finset Edge} {s0 t0 X : Pt} (hF : Deg2Off V F s0 t0)
    (hs0 : s0 ∈ V) (hpd : PDang V t0) (ht : IsCorner t0 X) : NotTypeIII V F X := by
  intro s hb hf _ _
  exact absurd ht (hpd X (cellT_of_bf hF hs0 hb hf))

-- The square beside a strip's end cell, with both outer edges at the end dark, is a cell of
-- `V ∪ {t0}`.
--
lemma beside_end1_cellT {V : Finset Pt} {F : Finset Edge} {c : Pt} {s : Side} {k : ℕ} {s0 t0 : Pt}
    (hF : Deg2Off V F s0 t0) (hs0 : s0 ∈ V) (hb : outer1 (cellJ c s k) s ∈ F)
    (hf : outer1 (cellJ c s (k + 1)) s ∈ F) :
    IsCell (insert t0 V) (nb (cellJ c s (k + 1)) (latA s)) := by
  have hbL : back (nb (cellJ c s (k + 1)) (latA s)) s = outer1 (cellJ c s k) s := by
    rw [← side_back_next, nb_cellJ]
  have hfL : front (nb (cellJ c s (k + 1)) (latA s)) s = outer1 (cellJ c s (k + 1)) s :=
    side_front _ s
  exact cellT_of_bf hF hs0 (hbL ▸ hb) (hfL ▸ hf)

lemma beside_end2_cellT {V : Finset Pt} {F : Finset Edge} {c : Pt} {s : Side} {k : ℕ} {s0 t0 : Pt}
    (hF : Deg2Off V F s0 t0) (hs0 : s0 ∈ V) (hb : outer2 (cellJ c s k) s ∈ F)
    (hf : outer2 (cellJ c s (k + 1)) s ∈ F) :
    IsCell (insert t0 V) (nb (cellJ c s (k + 1)) (latB s)) := by
  have hbL : back (nb (cellJ c s (k + 1)) (latB s)) s = outer2 (cellJ c s k) s := by
    rw [outer2_side_nb_next, nb_cellJ]; rfl
  have hfL : front (nb (cellJ c s (k + 1)) (latB s)) s = outer2 (cellJ c s (k + 1)) s :=
    side2_front _ s
  exact cellT_of_bf hF hs0 (hbL ▸ hb) (hfL ▸ hf)

end pdang

end HP

end ULHC
