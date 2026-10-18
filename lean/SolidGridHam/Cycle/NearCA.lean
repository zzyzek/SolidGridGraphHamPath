/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
import SolidGridHam.Cycle.ChainLinks
import SolidGridHam.Cycle.Complete

/-!
# The near lemma for chain links anywhere (class CA)

Same structure as `NearLemma.lean`, for minimum paths of the class `CRPathCA`.
* `e1_chain`: a strip linked from a strip ending beyond `a`'s end cell cannot share a side
  with that cell without touching `a`.
* `touch_contra_plain`: the last touching strip, for a link without a shared side.
* `touch_contra_chain`: the same for a chain link.
-/

namespace SolidGridHam

open Finset

section e1

variable {V : Finset Pt} {G : Finset Edge} {c : Pt} {s : Side} {k : ℕ}
  (hG : Deg2 V G) (hk : k % 2 = 0)
  (hcell : ∀ j ≤ k + 1, IsCell V (cellJ c s j)) (hpat : StripPat G c s (k + 2))
include hG hk hcell hpat

theorem e1_chain {τ w : StripSpec} (hl : CR2 V G τ w) (hok : ChainOK τ w)
    (hend : endCell τ = nb (cellJ c s (k + 1)) s) (ht : τ.s = s.opp)
    (hul1 : lat1 (nb (cellJ c s (k + 1)) s) s ∈ G) (hul2 : lat2 (nb (cellJ c s (k + 1)) s) s ∈ G)
    {y : Edge} (hy : y ∈ cellE (cellJ w.c w.s 0)) (hyu : y ∈ cellE (nb (cellJ c s (k + 1)) s))
    (hyl : y = lat1 (nb (cellJ c s (k + 1)) s) τ.s ∨ y = lat2 (nb (cellJ c s (k + 1)) s) τ.s) :
    Touches ⟨c, s, k + 2⟩ w := by
  set e := cellJ c s (k + 1)
  set u := nb e s
  have hc1 := hl.2.2.1
  have hpw := hl.2.2.2.1
  have hne := hl.2.2.2.2.2.2.1
  rw [hend] at hpw hne
  rw [cellJ_zero] at hy
  have hne0 : w.c ≠ u := by have := hne 0 hc1; rwa [cellJ_zero] at this
  rw [ht, (frame_opp u s).1, (frame_opp u s).2.1] at hyl
  obtain ⟨a1, a2, _, af⟩ := strip_sig hpat (show k + 1 < k + 2 by omega)
  have l1 : lat1 e s ∈ G := a1.2 (by omega)
  have l2 : lat2 e s ∈ G := a2.2 (by omega)
  have hfe : front e s ∉ G := fun h => by have := (af.1 h).1 (by omega); omega
  have hce := hcell (k + 1) le_rfl
  have hlu : lat1 (endCell τ) τ.s ∈ G ∧ lat2 (endCell τ) τ.s ∈ G := by
    rw [hend, ht, (frame_opp u s).1, (frame_opp u s).2.1]; exact ⟨hul1, hul2⟩
  have hyu' : y ∈ cellE (endCell τ) := by rw [hend]; exact hyu
  have hcl := chain_lat hl hok hlu hy hyu'
  have hu_eq : nb e s = cellJ c s (k + 2) := nb_cellJ c s (k + 1)
  rcases hyl with rfl | rfl
  · -- The shared side is `u`'s `lat1`: `w` starts at the cell across it.
    --
    have hw0 : w.c = nb u (latA s) := by
      rcases cell_of_side u (tf := latA s) (by rw [← lat1_eq]; exact hy) with h | h
      · exact absurd h hne0
      · exact h
    have hy2 : lat1 u s = lat2 w.c s := by
      rw [hw0, lat2_eq, latB_eq_opp, show sideEdge (nb u (latA s)) (latA s).opp = back (nb u (latA s)) (latA s)
        from rfl, back_nb, lat1_eq]; rfl
    have hbo : back w.c s = outer1 e s := by rw [hw0, outer1_side_nb_next]; rfl
    have hoff : outer1 e s ∉ G := by
      have hd := hG.2 _ (corners4 hce s).2.2.1
      rw [deg_front1, ind_of_mem l1, ind_of_not_mem hfe, ind_of_mem hul1] at hd
      intro ho; rw [ind_of_mem ho] at hd; omega
    have hbu : back w.c s ∉ cellE u := by
      intro h
      have := inter_unique hne0 (by rw [cellE_frame w.c s]; simp) h hy hyu
      rw [hy2] at this
      exact (frame_ne w.c s).2.1 this
    have hbF : back w.c s ∉ flip G u := by rw [mem_flip_off hbu, hbo]; exact hoff
    obtain ⟨n1, n2, n3, n4, n5, n6⟩ := frame_ne w.c s
    rcases side_cases s w.s with h | h | h | h
    · exfalso; have := hpw.1; rw [h] at this; exact hbF this
    · have hf0 := hpw.2.2 0 hc1
      rw [cellJ_zero, h, (frame_opp w.c s).2.2.2] at hf0
      have h1n : 1 < w.n := by
        by_contra hn; exact hbF (hf0.2 ⟨fun h' => by omega, fun h' => absurd h' hn⟩)
      refine ⟨1, h1n, k + 1, show k + 1 < k + 2 by omega, lat1 e s, ?_, by rw [cellE_frame e s]; simp⟩
      have hc1' : cellJ w.c w.s 1 = nb e (latA s) := by
        rw [← nb_cellJ, cellJ_zero, h, hw0, show u = cellJ c s (k + 2) from hu_eq, side1_down]
      rw [hc1', ← side_lat2, cellE_frame _ s]; simp
    · exfalso
      obtain ⟨_, _, fl⟩ := frame_latA w.c s
      rw [h] at hcl
      rcases fl with ⟨f1, f2⟩ | ⟨f1, f2⟩ <;> rw [f1, f2, hy2] at hcl <;>
        rcases hcl with hc | hc
      · exact n2 hc.symm
      · exact n4 hc.symm
      · exact n4 hc.symm
      · exact n2 hc.symm
    · exfalso
      obtain ⟨_, _, fl⟩ := frame_latB w.c s
      rw [h] at hcl
      rcases fl with ⟨f1, f2⟩ | ⟨f1, f2⟩ <;> rw [f1, f2, hy2] at hcl <;>
        rcases hcl with hc | hc
      · exact n2 hc.symm
      · exact n4 hc.symm
      · exact n4 hc.symm
      · exact n2 hc.symm
  · have hw0 : w.c = nb u (latB s) := by
      rcases cell_of_side u (tf := latB s) (by rw [← lat2_eq]; exact hy) with h | h
      · exact absurd h hne0
      · exact h
    have hy2 : lat2 u s = lat1 w.c s := by
      rw [hw0, lat1_eq, ← latB_opp_eq, show sideEdge (nb u (latB s)) (latB s).opp = back (nb u (latB s)) (latB s)
        from rfl, back_nb, lat2_eq]; rfl
    have hbo : back w.c s = outer2 e s := by rw [hw0, outer2_side_nb_next]; rfl
    have hoff : outer2 e s ∉ G := by
      have hd := hG.2 _ (corners4 hce s).2.2.2
      rw [deg_front2, ind_of_mem l2, ind_of_not_mem hfe, ind_of_mem hul2] at hd
      intro ho; rw [ind_of_mem ho] at hd; omega
    have hbu : back w.c s ∉ cellE u := by
      intro h
      have := inter_unique hne0 (by rw [cellE_frame w.c s]; simp) h hy hyu
      rw [hy2] at this
      exact (frame_ne w.c s).1 this
    have hbF : back w.c s ∉ flip G u := by rw [mem_flip_off hbu, hbo]; exact hoff
    obtain ⟨n1, n2, n3, n4, n5, n6⟩ := frame_ne w.c s
    rcases side_cases s w.s with h | h | h | h
    · exfalso; have := hpw.1; rw [h] at this; exact hbF this
    · have hf0 := hpw.2.2 0 hc1
      rw [cellJ_zero, h, (frame_opp w.c s).2.2.2] at hf0
      have h1n : 1 < w.n := by
        by_contra hn; exact hbF (hf0.2 ⟨fun h' => by omega, fun h' => absurd h' hn⟩)
      refine ⟨1, h1n, k + 1, show k + 1 < k + 2 by omega, lat2 e s, ?_, by rw [cellE_frame e s]; simp⟩
      have hc1' : cellJ w.c w.s 1 = nb e (latB s) := by
        rw [← nb_cellJ, cellJ_zero, h, hw0, show u = cellJ c s (k + 2) from hu_eq, side2_down]
      rw [hc1', ← side2_lat1, cellE_frame _ s]; simp
    · exfalso
      obtain ⟨_, _, fl⟩ := frame_latA w.c s
      rw [h] at hcl
      rcases fl with ⟨f1, f2⟩ | ⟨f1, f2⟩ <;> rw [f1, f2, hy2] at hcl <;>
        rcases hcl with hc | hc
      · exact n1 hc.symm
      · exact n3 hc.symm
      · exact n3 hc.symm
      · exact n1 hc.symm
    · exfalso
      obtain ⟨_, _, fl⟩ := frame_latB w.c s
      rw [h] at hcl
      rcases fl with ⟨f1, f2⟩ | ⟨f1, f2⟩ <;> rw [f1, f2, hy2] at hcl <;>
        rcases hcl with hc | hc
      · exact n1 hc.symm
      · exact n3 hc.symm
      · exact n3 hc.symm
      · exact n1 hc.symm

end e1

-- A start cell with a dark back and exactly one dark lateral side, read in `a`'s frame `s`.
--
lemma start_frame {F : Finset Edge} {d : Pt} {tf : Side} (s : Side) (hb : back d tf ∈ F)
    (hxl : (lat1 d tf ∈ F ∧ lat2 d tf ∉ F) ∨ (lat2 d tf ∈ F ∧ lat1 d tf ∉ F)) :
    ((tf = s ∨ tf = s.opp) ∧ (lat1 d s ∈ F ↔ lat2 d s ∉ F)) ∨
      ((tf = latA s ∨ tf = latB s) ∧ (lat1 d s ∈ F ∨ lat2 d s ∈ F) ∧
        (back d s ∈ F ↔ front d s ∉ F)) := by
  rcases side_cases s tf with h | h | h | h <;> subst h
  · left; refine ⟨Or.inl rfl, ?_⟩; tauto
  · left; refine ⟨Or.inr rfl, ?_⟩
    rw [(frame_opp d s).1, (frame_opp d s).2.1] at hxl; tauto
  · right; refine ⟨Or.inl rfl, ?_, ?_⟩
    · rw [(frame_latA d s).2.1] at hb; exact Or.inr hb
    · rcases (frame_latA d s).2.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2] at hxl <;> tauto
  · right; refine ⟨Or.inr rfl, ?_, ?_⟩
    · rw [(frame_latB d s).2.1] at hb; exact Or.inl hb
    · rcases (frame_latB d s).2.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2] at hxl <;> tauto

lemma body_not_alt' {F : Finset Edge} {c : Pt} {s : Side} {k : ℕ} (hk : k % 2 = 0)
    (hpat : StripPat F c s (k + 2)) {j : ℕ} (hj : j ≤ k) {tw : Side}
    (l1 : lat1 (cellJ c s j) tw ∈ F) (l2 : lat2 (cellJ c s j) tw ∈ F)
    (bw : back (cellJ c s j) tw ∉ F) (fw : front (cellJ c s j) tw ∉ F) : False := by
  obtain ⟨_, _, ab, af⟩ := strip_sig hpat (show j < k + 2 by omega)
  have := (alt_frame s l1 l2 bw fw).1
  rw [ab, af] at this; omega

section chainstart

variable {V : Finset Pt} {F : Finset Edge} {c : Pt} {s : Side} {k : ℕ}
  (hF : Deg2 V F) (hT : NoTypeIII V F) (hk : k % 2 = 0)
  (hcell : ∀ j ≤ k + 1, IsCell V (cellJ c s j)) (hpat : StripPat F c s (k + 2))
  (hsep : ¬ Conn F (back1 c s) (front1 c s))
  {d u : Pt} {tf tu : Side} {x : Edge}
  (hb : back d tf ∈ F) (hxd : x ∈ F) (hxlat : x = lat1 d tf ∨ x = lat2 d tf)
  (hxl : (lat1 d tf ∈ F ∧ lat2 d tf ∉ F) ∨ (lat2 d tf ∈ F ∧ lat1 d tf ∉ F))
  (lu1 : lat1 u tu ∈ F) (lu2 : lat2 u tu ∈ F) (bu : back u tu ∉ F) (fu : front u tu ∉ F)
  (hxu : x ∈ cellE u) (hdu : d ≠ u)

-- In a frame across `s`, the shared side is the start cell's back or front side in frame `s`.
--
include hxlat in
lemma perp_x (ht : tf = latA s ∨ tf = latB s) : x = back d s ∨ x = front d s := by
  rcases ht with rfl | rfl
  · rcases (frame_latA d s).2.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases hxlat with rfl | rfl <;> tauto
  · rcases (frame_latB d s).2.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases hxlat with rfl | rfl <;> tauto

include hxu hdu in
lemma u_across {dir : Side} (h : x = sideEdge d dir) : u = nb d dir := by
  rcases cell_of_side d (tf := dir) (h ▸ hxu) with h' | h'
  · exact absurd h'.symm hdu
  · exact h'

include hk hpat hb hxd hxlat hxl lu1 lu2 bu fu hxu hdu in
-- A chain strip does not start at a cell of `a`.
--
theorem start_not_body {j : ℕ} (hj : j ≤ k + 1) (hd : d = cellJ c s j) : False := by
  obtain ⟨a1, a2, ab, af⟩ := strip_sig hpat (show j < k + 2 by omega)
  rw [← hd] at a1 a2 ab af
  rcases start_frame s hb hxl with ⟨_, hdiff⟩ | ⟨ht, hlat, hbf⟩
  · rw [a1, a2] at hdiff; omega
  · by_cases hjk : j = k + 1
    · subst hjk
      rw [ab, af] at hbf; omega
    · have hodd : j % 2 = 1 := by rcases hlat with h | h; exacts [a1.1 h, a2.1 h]
      have hbF : back d s ∉ F := fun h => by have := ab.1 h; omega
      have hxf : x = front d s := by
        rcases perp_x hxlat ht with h | h
        · exact absurd (h ▸ hxd) hbF
        · exact h
      have hu' := u_across hxu hdu hxf
      rw [hd, nb_cellJ] at hu'
      rw [hu'] at lu1 lu2 bu fu
      exact body_not_alt' hk hpat (j := j + 1) (by omega) lu1 lu2 bu fu

include hF hT hk hcell hpat hsep hb hxd hxlat hxl lu1 lu2 bu fu hxu hdu in
-- A chain strip does not start behind `c_0`.
--
theorem start_not_behind (hd : d = nb c s.opp) : False := by
  have hc0 : IsCell V c := by have := hcell 0 (by omega); rwa [cellJ_zero] at this
  have d1 := back_down hF hT hpat (by omega) hc0 hsep
  have d2 := back_down2 hF hT hpat (by omega) hc0 hsep
  have df : front d s ∈ F := by rw [hd, front_nb_opp]; exact hpat.1
  rw [← hd] at d1 d2
  rcases start_frame s hb hxl with ⟨_, hdiff⟩ | ⟨ht, _, hbf⟩
  · exact (hdiff.1 d1) d2
  · have hbF : back d s ∉ F := fun h => hbf.1 h df
    have hxf : x = front d s := by
      rcases perp_x hxlat ht with h | h
      · exact absurd (h ▸ hxd) hbF
      · exact h
    have hu' := u_across hxu hdu hxf
    rw [hd, behind_up] at hu'
    rw [hu', ← cellJ_zero c s] at lu1 lu2 bu fu
    exact body_not_alt' hk hpat (j := 0) (by omega) lu1 lu2 bu fu

include hF hT hk hcell hpat hsep hb hxd hxlat hxl lu1 lu2 bu fu hxu hdu in
-- A chain strip starting beside the body (across `lat1`) runs against `s`, from an even index,
-- with the shared side on the far side.
--
theorem start_beside1 {j : ℕ} (hj : j ≤ k) (hd : d = nb (cellJ c s j) (latA s)) :
    tf = s.opp ∧ j % 2 = 0 ∧ x = lat1 d s := by
  obtain ⟨fn, fb, ff⟩ := side1_facts hF hT hk hcell hpat hsep hj
  rw [← hd] at fn fb ff
  have afu := alt_frame s lu1 lu2 bu fu
  -- `u` is not one of the cells beside the body.
  --
  have notside : ∀ j' ≤ k + 1, u ≠ nb (cellJ c s j') (latA s) := by
    intro j' hj' he
    have af := alt_frame s lu1 lu2 bu fu
    rw [he] at af
    by_cases hj'k : j' ≤ k
    · obtain ⟨_, fb', ff'⟩ := side1_facts hF hT hk hcell hpat hsep hj'k
      have := af.1; rw [fb', ff'] at this; omega
    · obtain rfl : j' = k + 1 := by omega
      have fn' : lat2 (nb (cellJ c s (k + 1)) (latA s)) s ∈ F := by
        rw [side_lat2]; exact (strip_sig hpat (show k + 1 < k + 2 by omega)).1.2 (by omega)
      have fb' : back (nb (cellJ c s (k + 1)) (latA s)) s ∈ F := by
        rw [show back (nb (cellJ c s (k + 1)) (latA s)) s = outer1 (cellJ c s k) s by
          rw [← side_back_next, nb_cellJ]]
        exact (outer1_body hF hcell hpat le_rfl).2 hk
      exact (af.2.2.1 fb') (af.2.1.2 fn')
  rcases start_frame s hb hxl with ⟨htp, hdiff⟩ | ⟨ht, hlat, hbf⟩
  · -- Along `s`: the dark lateral side is the far one.
    --
    have hxs : x = lat1 d s ∨ x = lat2 d s := by
      rcases htp with rfl | rfl
      · exact hxlat
      · rwa [(frame_opp d s).1, (frame_opp d s).2.1] at hxlat
    have hxfar : x = lat1 d s := by
      rcases hxs with h | h
      · exact h
      · exfalso
        have hu' := u_across hxu hdu (show x = sideEdge d (latB s) by rw [h, lat2_eq])
        rw [hd, latB_eq_opp, nb_nb_opp] at hu'
        rw [hu'] at lu1 lu2 bu fu
        exact body_not_alt' hk hpat hj lu1 lu2 bu fu
    have hl1 : lat1 d s ∈ F := hxfar ▸ hxd
    have he : j % 2 = 0 := by
      have := hdiff.1 hl1; rw [fn] at this; omega
    refine ⟨?_, he, hxfar⟩
    rcases htp with rfl | rfl
    · exfalso; have := fb.1 hb; omega
    · rfl
  · exfalso
    rcases perp_x hxlat ht with hx' | hx'
    · have hu' := u_across hxu hdu (show x = sideEdge d s.opp from hx')
      have hjo : j % 2 = 1 := fb.1 (hx' ▸ hxd)
      obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
      rw [hd, side1_down] at hu'
      exact notside j' (by omega) hu'
    · have hu' := u_across hxu hdu (show x = sideEdge d s from hx')
      rw [hd, (nb_comm_lat c s j).1] at hu'
      exact notside (j + 1) (by omega) hu'

include hF hT hk hcell hpat hsep hb hxd hxlat hxl lu1 lu2 bu fu hxu hdu in
-- A chain strip starting beside the body (across `lat2`) runs against `s`, from an even index,
-- with the shared side on the far side.
--
theorem start_beside2 {j : ℕ} (hj : j ≤ k) (hd : d = nb (cellJ c s j) (latB s)) :
    tf = s.opp ∧ j % 2 = 0 ∧ x = lat2 d s := by
  obtain ⟨fn, fb, ff⟩ := side2_facts hF hT hk hcell hpat hsep hj
  rw [← hd] at fn fb ff
  have afu := alt_frame s lu1 lu2 bu fu
  -- `u` is not one of the cells beside the body.
  --
  have notside : ∀ j' ≤ k + 1, u ≠ nb (cellJ c s j') (latB s) := by
    intro j' hj' he
    have af := alt_frame s lu1 lu2 bu fu
    rw [he] at af
    by_cases hj'k : j' ≤ k
    · obtain ⟨_, fb', ff'⟩ := side2_facts hF hT hk hcell hpat hsep hj'k
      have := af.1; rw [fb', ff'] at this; omega
    · obtain rfl : j' = k + 1 := by omega
      have fn' : lat1 (nb (cellJ c s (k + 1)) (latB s)) s ∈ F := by
        rw [side2_lat1]; exact (strip_sig hpat (show k + 1 < k + 2 by omega)).2.1.2 (by omega)
      have fb' : back (nb (cellJ c s (k + 1)) (latB s)) s ∈ F := by
        rw [show back (nb (cellJ c s (k + 1)) (latB s)) s = outer2 (cellJ c s k) s by
          rw [outer2_side_nb_next, nb_cellJ]; rfl]
        exact (outer2_body hF hcell hpat le_rfl).2 hk
      exact (af.2.2.1 fb') fn'
  rcases start_frame s hb hxl with ⟨htp, hdiff⟩ | ⟨ht, hlat, hbf⟩
  · -- Along `s`: the dark lateral side is the far one.
    --
    have hxs : x = lat1 d s ∨ x = lat2 d s := by
      rcases htp with rfl | rfl
      · exact hxlat
      · rwa [(frame_opp d s).1, (frame_opp d s).2.1] at hxlat
    have hxfar : x = lat2 d s := by
      rcases hxs with h | h
      · exfalso
        have hu' := u_across hxu hdu (show x = sideEdge d (latA s) by rw [h, lat1_eq])
        rw [hd, ← latB_opp_eq, nb_nb_opp] at hu'
        rw [hu'] at lu1 lu2 bu fu
        exact body_not_alt' hk hpat hj lu1 lu2 bu fu
      · exact h
    have hl2 : lat2 d s ∈ F := hxfar ▸ hxd
    have he : j % 2 = 0 := by
      have : lat1 d s ∉ F := fun h => hdiff.1 h hl2
      rw [fn] at this; omega
    refine ⟨?_, he, hxfar⟩
    rcases htp with rfl | rfl
    · exfalso; have := fb.1 hb; omega
    · rfl
  · exfalso
    rcases perp_x hxlat ht with hx' | hx'
    · have hu' := u_across hxu hdu (show x = sideEdge d s.opp from hx')
      have hjo : j % 2 = 1 := fb.1 (hx' ▸ hxd)
      obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
      rw [hd, side2_down] at hu'
      exact notside j' (by omega) hu'
    · have hu' := u_across hxu hdu (show x = sideEdge d s from hx')
      rw [hd, (nb_comm_lat c s j).2] at hu'
      exact notside (j + 1) (by omega) hu'

include hF hT hk hcell hpat hsep hb hxd hxlat hxl lu1 lu2 bu fu hxu hdu in
-- A chain strip starting beside the end cell (across `lat1`) is a chain strip of the end cell
-- itself, running along or against `s` (against `s` with a dark front).
--
theorem start_beside_end1 (hd : d = nb (cellJ c s (k + 1)) (latA s)) :
    u = cellJ c s (k + 1) ∧ (tf = s ∨ (tf = s.opp ∧ front d tf ∈ F)) := by
  have fn : lat2 d s ∈ F := by
    rw [hd, side_lat2]; exact (strip_sig hpat (show k + 1 < k + 2 by omega)).1.2 (by omega)
  have fb : back d s ∈ F := by
    rw [hd, show back (nb (cellJ c s (k + 1)) (latA s)) s = outer1 (cellJ c s k) s by
      rw [← side_back_next, nb_cellJ]]
    exact (outer1_body hF hcell hpat le_rfl).2 hk
  rcases start_frame s hb hxl with ⟨htp, hdiff⟩ | ⟨ht, _, hbf⟩
  · have hxs : x = lat1 d s ∨ x = lat2 d s := by
      rcases htp with rfl | rfl
      · exact hxlat
      · rwa [(frame_opp d s).1, (frame_opp d s).2.1] at hxlat
    have hl1 : lat1 d s ∉ F := fun h => hdiff.1 h fn
    have hx2 : x = lat2 d s := by
      rcases hxs with h | h
      · exact absurd (h ▸ hxd) hl1
      · exact h
    have hu' := u_across hxu hdu (show x = sideEdge d (latB s) by rw [hx2, lat2_eq])
    rw [hd, latB_eq_opp, nb_nb_opp] at hu'
    refine ⟨hu', ?_⟩
    rcases htp with h | h
    · exact Or.inl h
    · right; refine ⟨h, ?_⟩; rw [h, (frame_opp d s).2.2.2]; exact fb
  · exfalso
    have hfF : front d s ∉ F := fun h => (hbf.1 fb) h
    have hxb : x = back d s := by
      rcases perp_x hxlat ht with h | h
      · exact h
      · exact absurd (h ▸ hxd) hfF
    have hu' := u_across hxu hdu (show x = sideEdge d s.opp from hxb)
    rw [hd, side1_down] at hu'
    obtain ⟨_, fb', ff'⟩ := side1_facts hF hT hk hcell hpat hsep (le_refl k)
    have af := alt_frame s lu1 lu2 bu fu
    rw [hu'] at af
    have := af.1; rw [fb', ff'] at this; omega

include hF hT hk hcell hpat hsep hb hxd hxlat hxl lu1 lu2 bu fu hxu hdu in
theorem start_beside_end2 (hd : d = nb (cellJ c s (k + 1)) (latB s)) :
    u = cellJ c s (k + 1) ∧ (tf = s ∨ (tf = s.opp ∧ front d tf ∈ F)) := by
  have fn : lat1 d s ∈ F := by
    rw [hd, side2_lat1]; exact (strip_sig hpat (show k + 1 < k + 2 by omega)).2.1.2 (by omega)
  have fb : back d s ∈ F := by
    rw [hd, show back (nb (cellJ c s (k + 1)) (latB s)) s = outer2 (cellJ c s k) s by
      rw [outer2_side_nb_next, nb_cellJ]; rfl]
    exact (outer2_body hF hcell hpat le_rfl).2 hk
  rcases start_frame s hb hxl with ⟨htp, hdiff⟩ | ⟨ht, _, hbf⟩
  · have hxs : x = lat1 d s ∨ x = lat2 d s := by
      rcases htp with rfl | rfl
      · exact hxlat
      · rwa [(frame_opp d s).1, (frame_opp d s).2.1] at hxlat
    have hl2 : lat2 d s ∉ F := hdiff.1 fn
    have hx1 : x = lat1 d s := by
      rcases hxs with h | h
      · exact h
      · exact absurd (h ▸ hxd) hl2
    have hu' := u_across hxu hdu (show x = sideEdge d (latA s) by rw [hx1, lat1_eq])
    rw [hd, ← latB_opp_eq, nb_nb_opp] at hu'
    refine ⟨hu', ?_⟩
    rcases htp with h | h
    · exact Or.inl h
    · right; refine ⟨h, ?_⟩; rw [h, (frame_opp d s).2.2.2]; exact fb
  · exfalso
    have hfF : front d s ∉ F := fun h => (hbf.1 fb) h
    have hxb : x = back d s := by
      rcases perp_x hxlat ht with h | h
      · exact h
      · exact absurd (h ▸ hxd) hfF
    have hu' := u_across hxu hdu (show x = sideEdge d s.opp from hxb)
    rw [hd, side2_down] at hu'
    obtain ⟨_, fb', ff'⟩ := side2_facts hF hT hk hcell hpat hsep (le_refl k)
    have af := alt_frame s lu1 lu2 bu fu
    rw [hu'] at af
    have := af.1; rw [fb', ff'] at this; omega

include hF hT hk hcell hpat hsep hb hxd hxlat hxl hxu hdu in
-- A chain strip starting beyond the end cell runs into the end cell, or is a single cell with
-- three dark sides (both lateral sides in frame `s` and the front, shared with `u`).
--
theorem start_beyond (_hs : Solid V) (x0 : Pt) (_hconn : ∀ z ∈ V, Conn (GE V) x0 z)
    (hT' : NoTypeIII V (flipCol F c s (k + 2))) {m : ℕ} (hfr : front d tf ∈ F ↔ m = 1)
    (hd : d = nb (cellJ c s (k + 1)) s) :
    (tf = s.opp ∧ front d tf ∉ F) ∨
      (m = 1 ∧ u = nb d s ∧ lat1 d s ∈ F ∧ lat2 d s ∈ F ∧ front d s ∈ F) := by
  set e := cellJ c s (k + 1)
  obtain ⟨a1, a2, _, af⟩ := strip_sig hpat (show k + 1 < k + 2 by omega)
  have l1 : lat1 e s ∈ F := a1.2 (by omega)
  have l2 : lat2 e s ∈ F := a2.2 (by omega)
  have hfe : front e s ∉ F := fun h => by have := (af.1 h).1 (by omega); omega
  have hbd : back d s ∉ F := by rw [hd, back_nb]; exact hfe
  have hce := hcell (k + 1) le_rfl
  rcases start_frame s hb hxl with ⟨htp, _⟩ | ⟨ht, _, hbf⟩
  · rcases htp with rfl | rfl
    · exact absurd hb hbd
    · left; refine ⟨rfl, ?_⟩; rw [(frame_opp d s).2.2.2]; exact hbd
  · right
    have hfd : front d s ∈ F := by by_contra h; exact hbd (hbf.2 h)
    have hxf : x = front d s := by
      rcases perp_x hxlat ht with h | h
      · exact absurd (h ▸ hxd) hbd
      · exact h
    have hu' := u_across hxu hdu (show x = sideEdge d s from hxf)
    rcases ht with rfl | rfl
    · -- Frame `latA s`: back is `lat2 d s`, front is `lat1 d s`.
      --
      have hb2 : lat2 d s ∈ F := by rw [← (frame_latA d s).2.1]; exact hb
      by_cases hm : m = 1
      · exact ⟨hm, hu', by rw [← (frame_latA d s).1]; exact hfr.2 hm, hb2, hfd⟩
      · exfalso
        have hl1 : lat1 d s ∉ F := by rw [← (frame_latA d s).1]; exact fun h => hm (hfr.1 h)
        have hd1 := hF.2 _ (corners4 hce s).2.2.1
        rw [deg_front1, ind_of_mem l1, ind_of_not_mem hfe, ← hd, ind_of_not_mem hl1] at hd1
        have ho : outer1 e s ∈ F := by by_contra ho; rw [ind_of_not_mem ho] at hd1; omega
        have hb0 := (outer1_body hF hcell hpat le_rfl).2 hk
        exact beside_end1 hF hT hk hcell hpat hsep hb0 ho
          (end_side_far1 hF hT hk hcell hpat hb0 ho) hT'
    · have hb1 : lat1 d s ∈ F := by rw [← (frame_latB d s).2.1]; exact hb
      by_cases hm : m = 1
      · exact ⟨hm, hu', hb1, by rw [← (frame_latB d s).1]; exact hfr.2 hm, hfd⟩
      · exfalso
        have hl2 : lat2 d s ∉ F := by rw [← (frame_latB d s).1]; exact fun h => hm (hfr.1 h)
        have hd2 := hF.2 _ (corners4 hce s).2.2.2
        rw [deg_front2, ind_of_mem l2, ind_of_not_mem hfe, ← hd, ind_of_not_mem hl2] at hd2
        have ho : outer2 e s ∈ F := by by_contra ho; rw [ind_of_not_mem ho] at hd2; omega
        have hb0 := (outer2_body hF hcell hpat le_rfl).2 hk
        exact beside_end2 hF hT hk hcell hpat hsep hb0 ho
          (end_side_far2 hF hT hk hcell hpat hb0 ho) hT'

include hF hT hk hcell hpat hsep in
-- A chain strip starting beside `c_0` and running against `s`, with dark far side, joins `a`'s
-- two start classes through its second cell.
--
theorem start_L0 {m : ℕ} (hzs : SigFrom F (nb c (latA s)) s.opp m 1) (hm : 2 ≤ m)
    (hc1 : IsCell V (cellJ (nb c (latA s)) s.opp 1)) (hx : lat1 (nb c (latA s)) s ∈ F) :
    False := by
  set d := nb c (latA s)
  have hc0 : IsCell V c := by have := hcell 0 (by omega); rwa [cellJ_zero] at this
  have ho := outer1_start hF hpat (by omega) hc0
  have hbo := back_outer_light hF hT hpat (by omega) hc0 hsep
  have h1 : nb d s.opp = cellJ d s.opp 1 := by
    have := nb_cellJ d s.opp 0; rwa [cellJ_zero] at this
  set w := cellJ d s.opp 1
  have hwd : nb w s = d := by rw [← h1]; exact behind_up d s
  obtain ⟨g1, g2, _, gf⟩ := hzs 1 le_rfl (by omega)
  rw [(frame_opp w s).1] at g1
  rw [(frame_opp w s).2.1] at g2
  rw [(frame_opp w s).2.2.2] at gf
  have wl1 : lat1 w s ∈ F := g1.2 rfl
  have wl2 : lat2 w s ∈ F := g2.2 rfl
  have f1 : front1 w s = back1 d s := by rw [← hwd, back1_nb]
  have f2 : front2 w s = back1 c s := by
    have h2 : front2 w s = back2 d s := by rw [← hwd, back2_nb]
    rw [h2]; exact side_back2 c s
  have hfw : front w s ∉ F := by
    have := back_nb w s; rw [hwd] at this; rw [← this]; exact hbo
  have hQ : Conn F (front1 w s) (front1 c s) := by
    rw [f1]; exact ((ends_lat1 d s).conn hx).trans ((side_front_ends c s).conn ho)
  have hff : Conn F (front2 w s) (front1 w s) := by
    by_cases hm2 : m = 2
    · have hbw : back w s ∉ F := fun h => by have := (gf.1 h).1 rfl; omega
      have hall := alt_corners_conn hT hc1 (alt_of_lats wl1 wl2 hbw hfw)
      obtain ⟨_, a2, a3⟩ := frame_of_allConn hall s
      exact a3.symm.trans a2
    · have hbw : back w s ∈ F := gf.2 ⟨fun _ => by omega, fun _ => rfl⟩
      exact (((ends_lat2 w s).conn wl2).symm.trans ((ends_back w s).conn hbw).symm).trans
        ((ends_lat1 w s).conn wl1)
  rw [f2] at hff
  exact hsep (hff.trans hQ)

include hF hT hk hcell hpat hsep in
theorem start_R0 {m : ℕ} (hzs : SigFrom F (nb c (latB s)) s.opp m 1) (hm : 2 ≤ m)
    (hc1 : IsCell V (cellJ (nb c (latB s)) s.opp 1)) (hx : lat2 (nb c (latB s)) s ∈ F) :
    False := by
  set d := nb c (latB s)
  have hc0 : IsCell V c := by have := hcell 0 (by omega); rwa [cellJ_zero] at this
  have hbo := back_outer2_light hF hT hpat (by omega) hc0 hsep
  have hfj := front_join hF hT hpat (by omega) hc0
  have ho : outer2 c s ∈ F := by
    obtain ⟨_, hl, hf⟩ := hpat
    have h0 := hl 0 (by omega)
    have h1 := hl 1 (by omega)
    have hf0 := hf 0 (by omega)
    rw [cellJ_zero] at h0 hf0
    have hl0 : lat2 c s ∉ F := fun h => by have := h0.2.1 h; omega
    have hfr : front c s ∉ F := fun h => by have := hf0.1 h; omega
    have hl1 : lat2 (nb c s) s ∈ F := by
      rw [show nb c s = cellJ c s 1 by rw [← nb_cellJ, cellJ_zero]]; exact h1.2.2 rfl
    have hd := hF.2 _ (corners4 hc0 s).2.2.2
    rw [deg_front2, ind_of_not_mem hl0, ind_of_not_mem hfr, ind_of_mem hl1] at hd
    by_contra ho; rw [ind_of_not_mem ho] at hd; omega
  have h1 : nb d s.opp = cellJ d s.opp 1 := by
    have := nb_cellJ d s.opp 0; rwa [cellJ_zero] at this
  set w := cellJ d s.opp 1
  have hwd : nb w s = d := by rw [← h1]; exact behind_up d s
  obtain ⟨g1, g2, _, gf⟩ := hzs 1 le_rfl (by omega)
  rw [(frame_opp w s).1] at g1
  rw [(frame_opp w s).2.1] at g2
  rw [(frame_opp w s).2.2.2] at gf
  have wl1 : lat1 w s ∈ F := g1.2 rfl
  have wl2 : lat2 w s ∈ F := g2.2 rfl
  have f1 : front1 w s = back2 c s := by
    have h2 : front1 w s = back1 d s := by rw [← hwd, back1_nb]
    rw [h2]; exact side2_back1 c s
  have f2 : front2 w s = back2 d s := by rw [← hwd, back2_nb]
  have hfw : front w s ∉ F := by
    have := back_nb w s; rw [hwd] at this; rw [← this]; exact hbo
  have hQ : Conn F (front2 w s) (front1 c s) := by
    rw [f2]
    exact (((ends_lat2 d s).conn hx).trans ((side2_front_ends c s).conn ho).symm).trans hfj.symm
  have hff : Conn F (front1 w s) (front2 w s) := by
    by_cases hm2 : m = 2
    · have hbw : back w s ∉ F := fun h => by have := (gf.1 h).1 rfl; omega
      have hall := alt_corners_conn hT hc1 (alt_of_lats wl1 wl2 hbw hfw)
      obtain ⟨_, a2, a3⟩ := frame_of_allConn hall s
      exact a2.symm.trans a3
    · have hbw : back w s ∈ F := gf.2 ⟨fun _ => by omega, fun _ => rfl⟩
      exact (((ends_lat1 w s).conn wl1).symm.trans ((ends_back w s).conn hbw)).trans
        ((ends_lat2 w s).conn wl2)
  rw [f1] at hff
  exact hsep (((ends_back c s).conn hpat.1).trans (hff.trans hQ))

end chainstart

lemma endCell_mk2 (c : Pt) (s : Side) (k : ℕ) : endCell ⟨c, s, k + 2⟩ = cellJ c s (k + 1) := rfl

-- Cells beside the strip at height `m` share no side with the strip's cells below `m`.
--
lemma besideA_not_mem (c : Pt) (s : Side) {m j i : ℕ} (hi : i < m) {x : Edge}
    (hx : x ∈ cellE (cellJ (nb (cellJ c s m) (latA s)) s j)) : x ∉ cellE (cellJ c s i) := by
  obtain ⟨p, q⟩ := c
  cases s <;> simp [cellE, nb, latA, cellJ, bot, top, lft, rgt] at hx ⊢ <;>
    rcases hx with rfl | rfl | rfl | rfl <;> simp <;> omega

lemma besideB_not_mem (c : Pt) (s : Side) {m j i : ℕ} (hi : i < m) {x : Edge}
    (hx : x ∈ cellE (cellJ (nb (cellJ c s m) (latB s)) s j)) : x ∉ cellE (cellJ c s i) := by
  obtain ⟨p, q⟩ := c
  cases s <;> simp [cellE, nb, latB, cellJ, bot, top, lft, rgt] at hx ⊢ <;>
    rcases hx with rfl | rfl | rfl | rfl <;> simp <;> omega

lemma besideA_ne (c : Pt) (s : Side) (m j i : ℕ) :
    cellJ (nb (cellJ c s m) (latA s)) s j ≠ cellJ c s i := by
  obtain ⟨p, q⟩ := c; cases s <;> simp [nb, latA, cellJ]

lemma besideB_ne (c : Pt) (s : Side) (m j i : ℕ) :
    cellJ (nb (cellJ c s m) (latB s)) s j ≠ cellJ c s i := by
  obtain ⟨p, q⟩ := c; cases s <;> simp [nb, latB, cellJ]

lemma besideA_not_mid (c : Pt) (s : Side) (k : ℕ) {tf : Side} (ht : tf = s ∨ tf = s.opp) :
    ¬ IsMid c s k (back1 (nb (cellJ c s (k + 1)) (latA s)) tf) ∧
      ¬ IsMid c s k (front1 (nb (cellJ c s (k + 1)) (latA s)) tf) := by
  obtain ⟨p, q⟩ := c
  rcases ht with h0 | h0 <;> rw [h0] <;> constructor <;> rintro ⟨j, hj, hjk, h⟩ <;> cases s <;>
    simp [back1, front1, front2, nb, latA, cellJ, Side.opp] at h <;> omega

lemma besideB_not_mid (c : Pt) (s : Side) (k : ℕ) {tf : Side} (ht : tf = s ∨ tf = s.opp) :
    ¬ IsMid c s k (back1 (nb (cellJ c s (k + 1)) (latB s)) tf) ∧
      ¬ IsMid c s k (front1 (nb (cellJ c s (k + 1)) (latB s)) tf) := by
  obtain ⟨p, q⟩ := c
  rcases ht with h0 | h0 <;> rw [h0] <;> constructor <;> rintro ⟨j, hj, hjk, h⟩ <;> cases s <;>
    simp [back1, front1, front2, nb, latB, cellJ, Side.opp] at h <;> omega

-- **Direct link.** A chain strip of a strip ending at `a`'s end cell, starting beside it and
-- running along `s` (or a single cell), is a link from `a` itself.
--
theorem direct_link1 {V : Finset Pt} {G : Finset Edge} {c : Pt} {s : Side} {k : ℕ}
    (hk : k % 2 = 0) {σ τ : StripSpec} (hl : CR2 V G σ τ)
    (hσe : endCell σ = cellJ c s (k + 1)) (hd : τ.c = nb (cellJ c s (k + 1)) (latA s))
    (ht : τ.s = s ∨ (τ.s = s.opp ∧ τ.n = 1)) : CR2 V G ⟨c, s, k + 2⟩ τ := by
  obtain ⟨_, _, h1, hp, hc, _, _, _, _, _, hcg, hcu⟩ := hl
  rw [hσe] at hp hcu
  have hcellτ : ∀ j < τ.n, cellJ τ.c τ.s j = cellJ (nb (cellJ c s (k + 1)) (latA s)) s j := by
    intro j hj
    rcases ht with h | ⟨h, h1'⟩
    · rw [hd, h]
    · obtain rfl : j = 0 := by omega
      rw [cellJ_zero, cellJ_zero, hd]
  unfold CR2
  dsimp only
  refine ⟨by omega, by omega, h1, hp, hc, fun j hj i hi x hx => ?_, fun j hj => ?_, fun hev x hx => ?_,
    ?_, ?_, hcg, hcu⟩
  · rw [hcellτ j hj] at hx
    exact besideA_not_mem c s (show i < k + 1 by simp only at hi; omega) hx
  · rw [hcellτ j hj, endCell_mk2]; exact besideA_ne c s _ _ _
  · rcases ht with h | ⟨_, h1'⟩
    · have hn : 2 ≤ τ.n := by omega
      unfold endCell at hx; rw [hcellτ _ (by omega), show k + 1 + 0 = k + 1 from rfl] at hx
      rw [endCell_mk2]
      have : cellJ (nb (cellJ c s (k + 1)) (latA s)) s (τ.n - 1) =
          cellJ (nb (cellJ c s (k + 1 + (τ.n - 1))) (latA s)) s 0 := by
        obtain ⟨p, q⟩ := c; cases s <;> simp [nb, latA, cellJ] <;> omega
      rw [this] at hx
      exact besideA_not_mem c s (show k + 1 < k + 1 + (τ.n - 1) by omega) hx
    · omega
  · rw [show k + 2 - 2 = k from rfl, hd]
    exact (besideA_not_mid c s k (ht.elim Or.inl (fun h => Or.inr h.1))).1
  · rw [show k + 2 - 2 = k from rfl, hd]
    exact (besideA_not_mid c s k (ht.elim Or.inl (fun h => Or.inr h.1))).2

-- **Direct link.** A chain strip of a strip ending at `a`'s end cell, starting beside it and
-- running along `s` (or a single cell), is a link from `a` itself.
--
theorem direct_link2 {V : Finset Pt} {G : Finset Edge} {c : Pt} {s : Side} {k : ℕ}
    (hk : k % 2 = 0) {σ τ : StripSpec} (hl : CR2 V G σ τ)
    (hσe : endCell σ = cellJ c s (k + 1)) (hd : τ.c = nb (cellJ c s (k + 1)) (latB s))
    (ht : τ.s = s ∨ (τ.s = s.opp ∧ τ.n = 1)) : CR2 V G ⟨c, s, k + 2⟩ τ := by
  obtain ⟨_, _, h1, hp, hc, _, _, _, _, _, hcg, hcu⟩ := hl
  rw [hσe] at hp hcu
  have hcellτ : ∀ j < τ.n, cellJ τ.c τ.s j = cellJ (nb (cellJ c s (k + 1)) (latB s)) s j := by
    intro j hj
    rcases ht with h | ⟨h, h1'⟩
    · rw [hd, h]
    · obtain rfl : j = 0 := by omega
      rw [cellJ_zero, cellJ_zero, hd]
  unfold CR2
  dsimp only
  refine ⟨by omega, by omega, h1, hp, hc, fun j hj i hi x hx => ?_, fun j hj => ?_, fun hev x hx => ?_,
    ?_, ?_, hcg, hcu⟩
  · rw [hcellτ j hj] at hx
    exact besideB_not_mem c s (show i < k + 1 by simp only at hi; omega) hx
  · rw [hcellτ j hj, endCell_mk2]; exact besideB_ne c s _ _ _
  · rcases ht with h | ⟨_, h1'⟩
    · have hn : 2 ≤ τ.n := by omega
      unfold endCell at hx; rw [hcellτ _ (by omega), show k + 1 + 0 = k + 1 from rfl] at hx
      rw [endCell_mk2]
      have : cellJ (nb (cellJ c s (k + 1)) (latB s)) s (τ.n - 1) =
          cellJ (nb (cellJ c s (k + 1 + (τ.n - 1))) (latB s)) s 0 := by
        obtain ⟨p, q⟩ := c; cases s <;> simp [nb, latB, cellJ] <;> omega
      rw [this] at hx
      exact besideB_not_mem c s (show k + 1 < k + 1 + (τ.n - 1) by omega) hx
    · omega
  · rw [show k + 2 - 2 = k from rfl, hd]
    exact (besideB_not_mid c s k (ht.elim Or.inl (fun h => Or.inr h.1))).1
  · rw [show k + 2 - 2 = k from rfl, hd]
    exact (besideB_not_mid c s k (ht.elim Or.inl (fun h => Or.inr h.1))).2

lemma along_not_mem (c : Pt) (s : Side) {i i' : ℕ} (h : i' + 2 ≤ i) {x : Edge}
    (hx : x ∈ cellE (cellJ c s i)) : x ∉ cellE (cellJ c s i') := by
  obtain ⟨p, q⟩ := c
  cases s <;> simp [cellE, cellJ, bot, top, lft, rgt] at hx ⊢ <;>
    rcases hx with rfl | rfl | rfl | rfl <;> simp <;> omega

lemma along_not_mid (c : Pt) (s : Side) (k : ℕ) :
    ¬ IsMid c s k (back1 (cellJ c s (k + 3)) s) ∧ ¬ IsMid c s k (front1 (cellJ c s (k + 3)) s) := by
  obtain ⟨p, q⟩ := c
  constructor <;> rintro ⟨j, hj, hjk, h⟩ <;> cases s <;>
    simp [back1, front1, front2, cellJ] at h <;> omega

lemma front1_not_corner (d : Pt) (s : Side) :
    front1 (nb d s) s ∉ ({back1 d s, back2 d s, front1 d s, front2 d s} : Finset Pt) := by
  obtain ⟨p, q⟩ := d
  cases s <;> simp [back1, back2, front1, front2, nb] <;> omega

-- **Single cell beyond the end with three dark sides.** The previous end cell `u`, two cells
-- beyond `a`'s end, is then a single-cell link from `a`: after `e`'s flip the cell between has
-- four dark sides and closes off.
--
theorem single3_link {V : Finset Pt} {G : Finset Edge} {c : Pt} {s : Side} {k : ℕ}
    (hG : Deg2 V G) (hT : NoTypeIII V G) (hk : k % 2 = 0)
    (hcell : ∀ j ≤ k + 1, IsCell V (cellJ c s j)) (hpat : StripPat G c s (k + 2))
    (hd1 : lat1 (cellJ c s (k + 2)) s ∈ G) (hd2 : lat2 (cellJ c s (k + 2)) s ∈ G)
    (hdf : front (cellJ c s (k + 2)) s ∈ G) (hcu : IsCell V (cellJ c s (k + 3)))
    {tu : Side} (lu1 : lat1 (cellJ c s (k + 3)) tu ∈ G) (lu2 : lat2 (cellJ c s (k + 3)) tu ∈ G)
    (bu : back (cellJ c s (k + 3)) tu ∉ G) (fu : front (cellJ c s (k + 3)) tu ∉ G)
    (hcd : IsCell V (cellJ c s (k + 2))) :
    CR2 V G ⟨c, s, k + 2⟩ ⟨cellJ c s (k + 3), s, 1⟩ := by
  set e := cellJ c s (k + 1)
  set d := cellJ c s (k + 2)
  set u := cellJ c s (k + 3)
  have hde : nb e s = d := nb_cellJ c s (k + 1)
  have hdu : nb d s = u := nb_cellJ c s (k + 2)
  have afu := alt_frame s lu1 lu2 bu fu
  have hbu : back u s ∈ G := by rw [← hdu, back_nb]; exact hdf
  have hfu : front u s ∈ G := afu.1.1 hbu
  have hl1u : lat1 u s ∉ G := fun h => (afu.2.2.1 hbu) h
  have hl2u : lat2 u s ∉ G := fun h => hl1u (afu.2.1.2 h)
  have hoffe : ∀ x ∈ cellE u, x ∉ cellE e := fun x hx => along_not_mem c s (by omega) hx
  have hflipu : ∀ x ∈ cellE u, (x ∈ flip G e ↔ x ∈ G) := fun x hx => mem_flip_off (hoffe x hx)
  have memu : ∀ y, y = lat1 u s ∨ y = lat2 u s ∨ y = back u s ∨ y = front u s → y ∈ cellE u := by
    intro y hy; rw [cellE_frame _ s]; rcases hy with rfl | rfl | rfl | rfl <;> simp
  obtain ⟨a1, a2, ab, af⟩ := strip_sig hpat (show k + 1 < k + 2 by omega)
  have el1 : lat1 e s ∈ G := a1.2 (by omega)
  have el2 : lat2 e s ∈ G := a2.2 (by omega)
  have eb : back e s ∉ G := fun h => by have := ab.1 h; omega
  have ef : front e s ∉ G := fun h => by have := (af.1 h).1 (by omega); omega
  have hce := hcell (k + 1) le_rfl
  unfold CR2
  dsimp only
  refine ⟨by omega, by omega, le_rfl, ?_, fun j hj => ?_, fun j hj i hi x hx => ?_,
    fun j hj => ?_, fun h => by simp at h, ?_, ?_, ?_, ?_⟩
  · rw [endCell_mk2]
    exact single_pat ((hflipu _ (memu _ (Or.inr (Or.inr (Or.inl rfl))))).2 hbu)
      (fun h => hl1u ((hflipu _ (memu _ (Or.inl rfl))).1 h))
      (fun h => hl2u ((hflipu _ (memu _ (Or.inr (Or.inl rfl)))).1 h))
      ((hflipu _ (memu _ (Or.inr (Or.inr (Or.inr rfl))))).2 hfu)
  · obtain rfl : j = 0 := by omega
    rw [cellJ_zero]; exact hcu
  · simp only at hj hi
    obtain rfl : j = 0 := by omega
    rw [cellJ_zero] at hx
    exact along_not_mem c s (by omega) hx
  · obtain rfl : j = 0 := by omega
    rw [cellJ_zero, endCell_mk2]
    intro h; have := cellJ_inj c s h; omega
  · rw [show k + 2 - 2 = k from rfl]; exact (along_not_mid c s k).1
  · rw [show k + 2 - 2 = k from rfl]; exact (along_not_mid c s k).2
  · exact (frame_of_allConn (alt_corners_conn hT hcu (alt_of_lats lu1 lu2 bu fu)) s).2.1
  · rw [endCell_mk2]
    intro h
    -- In `flip G e`, the cell `d` has four dark sides.
    --
    have hGe : Deg2 V (flip G e) := hG.flip (mkLat e s) hce (mkLat_cellE e s) el1 el2 eb ef
    have hoffd : ∀ x ∈ cellE d, x ≠ back d s → x ∉ cellE e := by
      intro x hx hxb hxe
      apply hxb
      rw [shared_unique hde.symm hxe hx, ← hde, back_nb]; rfl
    have memd : ∀ y, y = lat1 d s ∨ y = lat2 d s ∨ y = back d s ∨ y = front d s → y ∈ cellE d := by
      intro y hy; rw [cellE_frame _ s]; rcases hy with rfl | rfl | rfl | rfl <;> simp
    have fne := frame_ne d s
    have f1 : lat1 d s ∈ flip G e :=
      (mem_flip_off (hoffd _ (memd _ (Or.inl rfl)) fne.1.symm)).2 hd1
    have f2 : lat2 d s ∈ flip G e :=
      (mem_flip_off (hoffd _ (memd _ (Or.inr (Or.inl rfl))) fne.2.1.symm)).2 hd2
    have f4 : front d s ∈ flip G e :=
      (mem_flip_off (hoffd _ (memd _ (Or.inr (Or.inr (Or.inr rfl)))) fne.2.2.2.2.2.symm)).2 hdf
    have f3 : back d s ∈ flip G e := by
      rw [mem_flip_iff]
      have hfe : back d s = front e s := by rw [← hde, back_nb]
      have hm : front e s ∈ cellE e := by rw [cellE_frame e s]; simp
      rw [hfe]; tauto
    have hb1 : back1 u s = front1 d s := by
      rw [← hdu]; obtain ⟨p, q⟩ := d; cases s <;> simp [back1, front1, nb]
    rw [hb1] at h
    have h' := (ends_lat1 d s).conn f1 |>.trans h
    have := four_sides_class hGe hcd s f3 f4 f1 f2 h'
    rw [← hdu] at this
    exact front1_not_corner d s this

-- The start corners of a chain strip carry dark edges of its first two cells (the chain strip's
-- version of `start_corner_edges`).
--
lemma chain_corner_edges {F : Finset Edge} {w : StripSpec} (h1 : 1 ≤ w.n)
    (hb : back w.c w.s ∈ F) (hfr : front w.c w.s ∈ F ↔ w.n = 1)
    (hzs : SigFrom F w.c w.s w.n 1) :
    (back w.c w.s ∈ F ∧ ((back w.c w.s).p = back1 w.c w.s ∨ (back w.c w.s).q = back1 w.c w.s) ∧
      back w.c w.s ∈ cellE (cellJ w.c w.s 0)) ∧
    ∃ j < w.n, ∃ x ∈ F, (x.p = front1 w.c w.s ∨ x.q = front1 w.c w.s) ∧
      x ∈ cellE (cellJ w.c w.s j) := by
  refine ⟨⟨hb, (ends_back w.c w.s).inc_iff _ |>.2 (Or.inl rfl), by
    rw [cellJ_zero, cellE_frame w.c w.s]; simp⟩, ?_⟩
  by_cases hn : w.n = 1
  · refine ⟨0, by omega, front w.c w.s, hfr.2 hn, (ends_front w.c w.s).inc_iff _ |>.2 (Or.inl rfl),
      ?_⟩
    rw [cellJ_zero, cellE_frame w.c w.s]; simp
  · refine ⟨1, by omega, lat1 (cellJ w.c w.s 1) w.s, (hzs 1 le_rfl (by omega)).1.2 rfl, ?_, ?_⟩
    · have he := ends_lat1 (cellJ w.c w.s 1) w.s
      rw [← nb_cellJ, cellJ_zero, back1_nb] at he
      rw [← nb_cellJ, cellJ_zero]
      exact he.inc_iff _ |>.2 (Or.inl rfl)
    · rw [cellE_frame _ w.s]; simp

-- Paths through `a` of weight below `W2` whose tail keeps off `a` do not exist. In a round
-- (`round_ca`) this follows from minimality (`W2 = W`); in completeness, any such path gives a
-- path of `G ⊕ a`.
--
def ViaFree (V : Finset Pt) (G : Finset Edge) (a : StripSpec) (W2 : ℕ) : Prop :=
  ∀ w R, CRPathCA V G a (w :: R) → (∀ x ∈ R, ¬ Touches a x) →
    (R ≠ [] → ∀ j < a.n, ∀ y ∈ cellE (endCell w), y ∉ cellE (cellJ a.c a.s j)) →
    wt a (w :: R) < W2 → False

lemma cellJ_nb_comm (z : Pt) (s tf : Side) (m : ℕ) : cellJ (nb z tf) s m = nb (cellJ z s m) tf := by
  obtain ⟨x, y⟩ := z
  cases s <;> cases tf <;> simp only [cellJ, nb] <;> ring_nf

lemma beside_end_farA (c : Pt) (s : Side) (k : ℕ) {n : ℕ} (hn : 2 ≤ n) {x : Edge}
    (hx : x ∈ cellE (cellJ (nb (cellJ c s (k + 1)) (latA s)) s (n - 1))) :
    ∀ j < k + 2, x ∉ cellE (cellJ c s j) := by
  intro j hj
  rw [cellJ_nb_comm, cellJ_add] at hx
  exact besideA_not_mem c s (j := 0) (show j < k + 1 + (n - 1) by omega) (by rw [cellJ_zero]; exact hx)

lemma beside_end_farB (c : Pt) (s : Side) (k : ℕ) {n : ℕ} (hn : 2 ≤ n) {x : Edge}
    (hx : x ∈ cellE (cellJ (nb (cellJ c s (k + 1)) (latB s)) s (n - 1))) :
    ∀ j < k + 2, x ∉ cellE (cellJ c s j) := by
  intro j hj
  rw [cellJ_nb_comm, cellJ_add] at hx
  exact besideB_not_mem c s (j := 0) (show j < k + 1 + (n - 1) by omega) (by rw [cellJ_zero]; exact hx)

section nearpathCA

variable {V : Finset Pt} {G : Finset Edge} {a : StripSpec}
  (hs : Solid V) (x0 : Pt) (hconn : ∀ z ∈ V, Conn (GE V) x0 z)
  (hG : Deg2 V G) (hT : NoTypeIII V G) (ha : ValidStrip V G a) (hae : a.n % 2 = 0)
  (ha2 : 2 ≤ a.n) (hT' : NoTypeIII V (applyS G a))
  {W : ℕ} (hmin : ∀ σ L', CRPathCA V G σ L' → W ≤ wt σ L')
include hs x0 hconn hG hT ha hae ha2 hT' hmin

-- **The last touching strip.** In a minimum path, a strip `τ` after the second, all of whose
-- successors keep off `a`, does not touch `a` either.
--
omit hs x0 hconn in
theorem touch_contra_plain {σ τ : StripSpec} {L2 : List StripSpec} (hl : CR2 V G σ τ)
    (hnc : NoChain σ τ) (hσ : EndOK V G σ) (hσe : σ.n % 2 = 0) (hch : CRChain V G τ L2)
    (hnct : CATail (τ :: L2)) (hfar2 : ∀ w ∈ L2, ¬ Touches a w)
    {W2 : ℕ} (hvia : ViaFree V G a W2) (hW1 : wt τ L2 < W) (hW2 : a.n + wt τ L2 < W2) :
    ¬ Touches a τ := by
  rintro ⟨i, hi, j, hj, x, hx1, hx2⟩
  have nopath : ∀ σ' L', CRPathCA V G σ' L' → wt σ' L' < W → False :=
    fun σ' L' h hlt => by have := hmin σ' L' h; omega
  obtain ⟨k, hk⟩ : ∃ k, a.n = k + 2 := ⟨a.n - 2, by omega⟩
  have hk2 : k % 2 = 0 := by omega
  obtain ⟨_, hpa, hca, hsep⟩ := ha
  rw [hk] at hpa hca hj
  have hcell : ∀ j ≤ k + 1, IsCell V (cellJ a.c a.s j) := fun j hj => hca j (by omega)
  have hT'' : NoTypeIII V (flipCol G a.c a.s (k + 2)) := by unfold applyS at hT'; rwa [hk] at hT'
  have hendA : endCell a = cellJ a.c a.s (k + 1) := by unfold endCell; rw [hk]; rfl
  set e := cellJ a.c a.s (k + 1) with he_def
  obtain ⟨h2σ, _, hτ1, hpτu, hcτ, hso, hne, hen, _, _, hcg, hcu⟩ := hl
  have hpτ : StripPat G τ.c τ.s τ.n := (pat_flip_off hτ1 hnc).1 hpτu
  obtain ⟨hu, lu1, lu2, bu, fu⟩ := hσ hσe
  set u' := endCell σ
  -- Shortcut through `a` to the successor `w` of `τ`, once `w`'s start is split by `e`.
  --
  have via_a : ∀ w L3, L2 = w :: L3 → StripPat G w.c w.s w.n →
      ¬ Conn (flip G e) (back1 w.c w.s) (front1 w.c w.s) → False := by
    intro w L3 hL hpw hsplit
    subst hL
    obtain ⟨_, hlw, hrest⟩ := hch
    have hnt := hfar2 w (List.mem_cons_self ..)
    have hw1 : 1 ≤ w.n := hlw.2.2.1
    have hlink : CR2 V G a w := link_a hG ⟨by omega, by rw [hk]; exact hpa,
      fun j hj => hca j (by rw [hk] at hj; exact hj), hsep⟩ hae ha2 hw1 hpw hlw.2.2.2.2.1 hnt
      hlw.2.2.2.2.2.2.2.2.2.2.1 (by rw [hendA]; exact hsplit)
    refine hvia w L3 ⟨⟨⟨by omega, by rw [hk]; exact hpa,
      fun j hj => hca j (by rw [hk] at hj; exact hj), hsep⟩, hae, hlink, hrest⟩,
      ⟨chainOK_of_noChain (fun jw hjw y hy hye => hnt ⟨jw, hjw, k + 1, by omega, y, hy,
        by rw [hendA] at hye; exact hye⟩), hnct.2⟩⟩
      (fun x hx => hfar2 x (List.mem_cons_of_mem _ hx))
      (fun _ j hj y hy hy' => hnt ⟨w.n - 1, by omega, j, hj, y, by unfold endCell at hy; exact hy, hy'⟩) ?_
    rw [wt_cons]; rw [wt_cons] at hW2; omega
  have hτc0 : cellJ τ.c τ.s 0 = τ.c := cellJ_zero τ.c τ.s
  obtain ⟨ea1, ea2, eab, eaf⟩ := strip_sig hpa (show k + 1 < k + 2 by omega)
  have el1 : lat1 e a.s ∈ G := ea1.2 (by omega)
  have el2 : lat2 e a.s ∈ G := ea2.2 (by omega)
  have eb : back e a.s ∉ G := fun h => by have := eab.1 h; omega
  have ef : front e a.s ∉ G := fun h => by have := (eaf.1 h).1 (by omega); omega
  have hce : IsCell V e := hcell (k + 1) le_rfl
  have hc0 : IsCell V a.c := by have := hcell 0 (by omega); rwa [cellJ_zero] at this
  -- `u'` (the previous end) differs from `e` and from the cell beyond, when `τ` starts at one
  -- of them and keeps off `u'`.
  --
  have off_e : ∀ y ∈ cellE e, y ∉ cellE u' → (y ∈ flip G u' ↔ y ∈ G) := fun y _ hy =>
    mem_flip_off hy
  -- **Through the end cell.**
  --
  have hR1 : ∀ i' < τ.n, cellJ τ.c τ.s i' = e → False := by
    intro i' hi' hq
    obtain ⟨hend, hdir⟩ := touch_end hk2 hpa (sig_of_pat hpτ) (Nat.zero_le _) hi' hq
    have hendτ : endCell τ = e := by
      unfold endCell; rw [← hq, show τ.n - 1 = i' by omega]
    rcases hdir with ⟨_, hodd⟩ | ⟨hperp, hev⟩
    · cases L2 with
      | nil => have : τ.n % 2 = 1 := hch; omega
      | cons w L3 =>
        have hlw := hch.2.1
        have hnt := hfar2 w (List.mem_cons_self ..)
        have hpw : StripPat G w.c w.s w.n := by
          have h := hlw.2.2.2.1
          rw [hendτ] at h
          exact (pat_flip_off hlw.2.2.1 (fun jw hjw y hy hy' =>
            hnt ⟨jw, hjw, k + 1, by omega, y, hy, hy'⟩)).1 h
        have hsplit := hlw.2.2.2.2.2.2.2.2.2.2.2
        rw [hendτ] at hsplit
        exact via_a w L3 rfl hpw hsplit
    · by_cases hi0 : i' = 0
      · subst hi0
        rw [hτc0] at hq
        have hwe : u' ≠ e := fun h => hne 0 (by omega) (by rw [hτc0, hq, h])
        have hwu : u' ≠ nb e a.s := fun h => hnc 0 (by omega) (sideEdge e a.s)
          (by rw [hτc0, hq]; exact side_mem_self e a.s)
          (by show sideEdge e a.s ∈ cellE u'; rw [h]; exact side_mem_nb e a.s)
        have hoff : ∀ y ∈ cellE e, y ∉ cellE u' := fun y hy =>
          hnc 0 (by omega) y (by rw [hτc0, hq]; exact hy)
        have m1 : lat1 e a.s ∈ cellE e := by rw [cellE_frame e a.s]; simp
        have m2 : lat2 e a.s ∈ cellE e := by rw [cellE_frame e a.s]; simp
        have hsp := hcu
        rw [hq] at hsp
        exact split_core hG hT hk2 hcell hpa hsep hT'' hu lu1 lu2 bu fu hwe hwu
          (cross_to_back hperp ((mem_flip_off (hoff _ m1)).2 el1)
            ((mem_flip_off (hoff _ m2)).2 el2) hsp)
      · have hp := cell_prev (z := τ.c) (tf := τ.s) (i := i') (by omega)
        rw [hq] at hp
        rcases hperp with ht | ht
        · rw [show τ.s.opp = latB a.s by rw [ht, latA_opp_eq]] at hp
          rcases touch_side2_end hG hk2 hcell hpa (sig_of_pat hpτ) (i := i' - 1) (Nat.zero_le _) (by omega) hp with
            ⟨ht', _⟩ | ⟨_, hf, hl⟩
          · exact latA_ne_opp a.s (ht.symm.trans ht')
          · exact beside_end2 hG hT hk2 hcell hpa hsep
              ((outer2_body hG hcell hpa le_rfl).2 hk2) hf hl hT''
        · rw [show τ.s.opp = latA a.s by rw [ht, latB_opp_eq]] at hp
          rcases touch_side1_end hG hk2 hcell hpa (sig_of_pat hpτ) (i := i' - 1) (Nat.zero_le _) (by omega) hp with
            ⟨ht', _⟩ | ⟨_, hf, hl⟩
          · exact latB_ne_opp a.s (ht.symm.trans ht')
          · exact beside_end1 hG hT hk2 hcell hpa hsep
              ((outer1_body hG hcell hpa le_rfl).2 hk2) hf hl hT''
  -- **Through the cell beyond the end cell.**
  --
  have hR2 : ∀ i' < τ.n, cellJ τ.c τ.s i' = nb e a.s → False := by
    intro i' hi' hq
    rcases touch_beyond hG hk2 hcell hpa (sig_of_pat hpτ) (Nat.zero_le _) hi' (fun _ _ => Nat.zero_le _) (fun _ => Nat.zero_le _) hq with ⟨ht, hodd, hend⟩ | ⟨ht, _, hi1⟩ |
      ⟨hperp, h0⟩
    · have hendτ : endCell τ = nb e a.s := by
        unfold endCell; rw [← hq, show τ.n - 1 = i' by omega]
      cases L2 with
      | nil => have : τ.n % 2 = 1 := hch; omega
      | cons w L3 =>
        have hlw := hch.2.1
        have hnt := hfar2 w (List.mem_cons_self ..)
        have hsplit := hlw.2.2.2.2.2.2.2.2.2.2.2
        rw [hendτ] at hsplit
        obtain ⟨g1, g2, gb, _⟩ := strip_sig hpτ hi'
        rw [hq, ht] at g1 g2 gb
        rw [(frame_opp (nb e a.s) a.s).1] at g1
        rw [(frame_opp (nb e a.s) a.s).2.1] at g2
        rw [(frame_opp (nb e a.s) a.s).2.2.1] at gb
        have ul1 := g1.2 hodd
        have ul2 := g2.2 hodd
        have hncw : NoChain τ w := by
          intro jw hjw y hy hyu
          obtain ⟨rfl, hyl⟩ := hnct.1 jw hjw y hy hyu
          rw [hendτ] at hyu hyl
          obtain ⟨i1, hi1, j1, hj1, x1, h1, h2⟩ := e1_chain hG hk2 hcell hpa hlw (hnct.1) hendτ ht ul1 ul2 hy hyu hyl
          exact hnt ⟨i1, hi1, j1, by rw [hk]; exact hj1, x1, h1, h2⟩
        have hpw : StripPat G w.c w.s w.n := (pat_flip_off hlw.2.2.1 hncw).1 hlw.2.2.2.1
        have uf : front (nb e a.s) a.s ∉ G := fun h => by have := gb.1 h; omega
        have hcu' : IsCell V (nb e a.s) := by rw [← hq]; exact hcτ i' hi'
        have hcorner : ∀ y ∈ G, ∀ jw < w.n, y ∈ cellE (cellJ w.c w.s jw) → ∀ r,
            (y.p = r ∨ y.q = r) → r ≠ front1 e a.s ∧ r ≠ front2 e a.s := by
          intro y hy jw hjw hyw r hr
          have touchy : y ∈ cellE e → False := fun h => hnt ⟨jw, hjw, k + 1, by omega, y, hyw, h⟩
          have chainy : y ∈ cellE (nb e a.s) → False := fun h =>
            hncw jw hjw y hyw (by rw [hendτ]; exact h)
          constructor
          · rintro rfl
            have i2 := (ends_lat1 (nb e a.s) a.s).inc_iff (front1 e a.s) |>.2
              (Or.inl (back1_nb e a.s).symm)
            have hne2 : lat1 e a.s ≠ lat1 (nb e a.s) a.s := (ends_lat1 e a.s).ne_at
              (by have := ends_lat1 (nb e a.s) a.s; rwa [back1_nb] at this)
              (back1_ne_front1_nb e a.s)
            rcases two_at (hG.2 _ (corners4 hce a.s).2.2.1) el1 ul1
              ((ends_lat1 e a.s).inc_iff _ |>.2 (Or.inr rfl)) i2 hne2 hy hr with h | h
            · exact touchy (by rw [h, cellE_frame e a.s]; simp)
            · exact chainy (by rw [h, cellE_frame (nb e a.s) a.s]; simp)
          · rintro rfl
            have i2 := (ends_lat2 (nb e a.s) a.s).inc_iff (front2 e a.s) |>.2
              (Or.inl (back2_nb e a.s).symm)
            have hne2 : lat2 e a.s ≠ lat2 (nb e a.s) a.s := (ends_lat2 e a.s).ne_at
              (by have := ends_lat2 (nb e a.s) a.s; rwa [back2_nb] at this)
              (back2_ne_front2_nb e a.s)
            rcases two_at (hG.2 _ (corners4 hce a.s).2.2.2) el2 ul2
              ((ends_lat2 e a.s).inc_iff _ |>.2 (Or.inr rfl)) i2 hne2 hy hr with h | h
            · exact touchy (by rw [h, cellE_frame e a.s]; simp)
            · exact chainy (by rw [h, cellE_frame (nb e a.s) a.s]; simp)
        have hw1 : 1 ≤ w.n := hlw.2.2.1
        obtain ⟨⟨hb, hbp, hb0⟩, jf, hjf, xf, hxf, hxfp, hxfw⟩ := start_corner_edges hpw hw1
        have cb := hcorner _ hb 0 (by omega) hb0 _ hbp
        have cf := hcorner _ hxf jf hjf hxfw _ hxfp
        have hss := stacked_split hG hce hcu' el1 el2 eb ef ul1 ul2 uf cb.1 cb.2 cf.1 cf.2
        exact via_a w L3 rfl hpw (fun h => hsplit (hss.1 h))
    · exact hR1 (i' + 1) hi1 (by rw [← nb_cellJ, hq, ht, nb_nb_opp])
    · subst h0
      rw [hτc0] at hq
      by_cases hm : 2 ≤ τ.n
      · exact beyond_cross hG hT hk2 hcell hpa hsep hT'' hpτ hperp hq hm
      · have hm1 : τ.n = 1 := by omega
        obtain ⟨_, _, gb, gf⟩ := strip_sig hpτ (show 0 < τ.n by omega)
        rw [hτc0, hq] at gb gf
        have hbz := gb.2 rfl
        have hfz := gf.2 ⟨fun h => by omega, fun h => by omega⟩
        have hl12 : lat1 (nb e a.s) a.s ∈ G ∧ lat2 (nb e a.s) a.s ∈ G := by
          rcases hperp with ht | ht <;> rw [ht] at hbz hfz
          · rw [(frame_latA _ _).1] at hfz; rw [(frame_latA _ _).2.1] at hbz; exact ⟨hfz, hbz⟩
          · rw [(frame_latB _ _).1] at hfz; rw [(frame_latB _ _).2.1] at hbz; exact ⟨hbz, hfz⟩
        have hoffu : ∀ y ∈ cellE (nb e a.s), y ∉ cellE u' := fun y hy =>
          hnc 0 (by omega) y (by rw [hτc0, hq]; exact hy)
        have hwu : u' ≠ nb e a.s := fun h => hne 0 (by omega) (by rw [hτc0, hq, h])
        have hwe : u' ≠ e := fun h => hoffu (sideEdge e a.s) (side_mem_nb e a.s)
          (by rw [h]; exact side_mem_self e a.s)
        have hoffe : ∀ y ∈ cellE e, y ∉ cellE u' := by
          intro y hy hy'
          rcases alt_touch hG hT hk2 hcell hpa hsep lu1 lu2 bu fu
            (show k + 1 < k + 2 by omega) hy' hy with h | h
          · exact hwe h
          · exact hwu h
        have m1 : lat1 (nb e a.s) a.s ∈ cellE (nb e a.s) := by rw [cellE_frame _ a.s]; simp
        have m2 : lat2 (nb e a.s) a.s ∈ cellE (nb e a.s) := by rw [cellE_frame _ a.s]; simp
        have m1e : lat1 e a.s ∈ cellE e := by rw [cellE_frame e a.s]; simp
        have m2e : lat2 e a.s ∈ cellE e := by rw [cellE_frame e a.s]; simp
        have hsp := hcu
        rw [hq] at hsp
        have h1 := cross_to_back hperp ((mem_flip_off (hoffu _ m1)).2 hl12.1)
          ((mem_flip_off (hoffu _ m2)).2 hl12.2) hsp
        rw [back1_nb, back2_nb] at h1
        exact split_core hG hT hk2 hcell hpa hsep hT'' hu lu1 lu2 bu fu hwe hwu
          (front_to_back ((mem_flip_off (hoffe _ m1e)).2 el1)
            ((mem_flip_off (hoffe _ m2e)).2 el2) h1)
  -- **Beside the start cell**: the suffix from there is a lighter path.
  --
  have hR3 : τ.s = a.s.opp → ∀ i0 < τ.n, i0 % 2 = 0 →
      (cellJ τ.c τ.s i0 = nb a.c (latA a.s) ∨ cellJ τ.c τ.s i0 = nb a.c (latB a.s)) → False := by
    intro ht i0 hi0 hev hq
    have hsep' : ¬ Conn G (back1 (cellJ τ.c τ.s i0) τ.s) (front1 (cellJ τ.c τ.s i0) τ.s) := by
      obtain ⟨g1, _, _, _⟩ := strip_sig hpτ hi0
      rcases hq with hq | hq <;> rw [hq] at g1 ⊢ <;> rw [ht] at g1 ⊢ <;> apply conn_lat1_opp
      · have hfar : lat1 (nb a.c (latA a.s)) a.s ∉ G := by
          rw [(frame_opp _ a.s).1] at g1; exact fun h => by have := g1.1 h; omega
        exact start_side_sep hG hT hpa (by omega) hc0 hsep hfar
      · rw [side2_back1, side2_front1]
        exact fun h => hsep ((((ends_back a.c a.s).conn hpa.1).trans h).trans
          (front_join hG hT hpa (by omega) hc0).symm)
    have hval := suf_valid hpτ hcτ hev hi0 hsep'
    cases L2 with
    | nil =>
      have hodd : τ.n % 2 = 1 := hch
      refine nopath (suf τ i0) [] ⟨⟨hval, ?_⟩, trivial⟩ ?_
      · show (τ.n - i0) % 2 = 1; omega
      · simp [wt, suf] at hW1 ⊢; omega
    | cons w L3 =>
      obtain ⟨hτe, hlw, hrest⟩ := hch
      have hcr := suf_cr2 hlw hev (by omega)
      have hok' : ChainOK (suf τ i0) w := by
        have := hnct.1
        unfold ChainOK at this ⊢
        rw [suf_end (by omega)]; exact this
      refine nopath (suf τ i0) (w :: L3) ⟨⟨hval, ⟨by show (τ.n - i0) % 2 = 0; omega, hcr, hrest⟩⟩,
        ⟨hok', hnct.2⟩⟩ ?_
      rw [wt_cons]; rw [wt_cons] at hW1; simp only [suf]; omega
  rcases touch_outcome hG hT hk2 hcell hpa hsep hT'' hpτ hi hj hx1 hx2 with
    ⟨i', hi', hq⟩ | ⟨i', hi', hq⟩ | ⟨ht, i0, hi0, hev, hq⟩
  · exact hR1 i' hi' hq
  · exact hR2 i' hi' hq
  · exact hR3 ht i0 hi0 hev hq

-- **The last touching strip.** In a minimum path, a strip `τ` after the second, all of whose
-- successors keep off `a`, does not touch `a` either.
omit hs x0 hconn in
--
theorem touch_core {σ τ : StripSpec} {i0 : ℕ} {L2 : List StripSpec} (hl : CR2 V G σ τ)
    (hzs : SigFrom G τ.c τ.s τ.n i0) (hi01 : i0 ≤ 1) (hz0 : i0 = 0 → NoChain σ τ)
    (hne_e : i0 = 1 → τ.c ≠ endCell a)
    (hσ : EndOK V G σ) (hσe : σ.n % 2 = 0) (hch : CRChain V G τ L2)
    (hnct : CATail (τ :: L2)) (hfar2 : ∀ w ∈ L2, ¬ Touches a w)
    {W2 : ℕ} (hvia : ViaFree V G a W2) (hW1 : wt τ L2 < W) (hW2 : a.n + wt τ L2 < W2) {i j : ℕ} (hii : i0 ≤ i) (hi : i < τ.n) (hj : j < a.n)
    {x : Edge} (hx1 : x ∈ cellE (cellJ τ.c τ.s i)) (hx2 : x ∈ cellE (cellJ a.c a.s j)) :
    False := by
  have nopath : ∀ σ' L', CRPathCA V G σ' L' → wt σ' L' < W → False :=
    fun σ' L' h hlt => by have := hmin σ' L' h; omega
  obtain ⟨k, hk⟩ : ∃ k, a.n = k + 2 := ⟨a.n - 2, by omega⟩
  have hk2 : k % 2 = 0 := by omega
  obtain ⟨_, hpa, hca, hsep⟩ := ha
  rw [hk] at hpa hca hj
  have hcell : ∀ j ≤ k + 1, IsCell V (cellJ a.c a.s j) := fun j hj => hca j (by omega)
  have hT'' : NoTypeIII V (flipCol G a.c a.s (k + 2)) := by unfold applyS at hT'; rwa [hk] at hT'
  have hendA : endCell a = cellJ a.c a.s (k + 1) := by unfold endCell; rw [hk]; rfl
  set e := cellJ a.c a.s (k + 1) with he_def
  obtain ⟨h2σ, _, hτ1, hpτu, hcτ, hso, hne, hen, _, _, hcg, hcu⟩ := hl
  -- Where the whole pattern of `τ` is needed (start cell cases), `τ` has no shared side.
  --
  have hpτ0 : i0 = 0 → StripPat G τ.c τ.s τ.n := fun h => (pat_flip_off hτ1 (hz0 h)).1 hpτu
  have hzi : ∀ i', i0 ≤ i' → i' < τ.n → _ := fun i' h1 h2 => hzs i' h1 h2
  obtain ⟨hu, lu1, lu2, bu, fu⟩ := hσ hσe
  set u' := endCell σ
  -- Shortcut through `a` to the successor `w` of `τ`, once `w`'s start is split by `e`.
  --
  have via_a : ∀ w L3, L2 = w :: L3 → StripPat G w.c w.s w.n →
      ¬ Conn (flip G e) (back1 w.c w.s) (front1 w.c w.s) → False := by
    intro w L3 hL hpw hsplit
    subst hL
    obtain ⟨_, hlw, hrest⟩ := hch
    have hnt := hfar2 w (List.mem_cons_self ..)
    have hw1 : 1 ≤ w.n := hlw.2.2.1
    have hlink : CR2 V G a w := link_a hG ⟨by omega, by rw [hk]; exact hpa,
      fun j hj => hca j (by rw [hk] at hj; exact hj), hsep⟩ hae ha2 hw1 hpw hlw.2.2.2.2.1 hnt
      hlw.2.2.2.2.2.2.2.2.2.2.1 (by rw [hendA]; exact hsplit)
    refine hvia w L3 ⟨⟨⟨by omega, by rw [hk]; exact hpa,
      fun j hj => hca j (by rw [hk] at hj; exact hj), hsep⟩, hae, hlink, hrest⟩,
      ⟨chainOK_of_noChain (fun jw hjw y hy hye => hnt ⟨jw, hjw, k + 1, by omega, y, hy,
        by rw [hendA] at hye; exact hye⟩), hnct.2⟩⟩
      (fun x hx => hfar2 x (List.mem_cons_of_mem _ hx))
      (fun _ j hj y hy hy' => hnt ⟨w.n - 1, by omega, j, hj, y, by unfold endCell at hy; exact hy, hy'⟩) ?_
    rw [wt_cons]; rw [wt_cons] at hW2; omega
  have hτc0 : cellJ τ.c τ.s 0 = τ.c := cellJ_zero τ.c τ.s
  obtain ⟨ea1, ea2, eab, eaf⟩ := strip_sig hpa (show k + 1 < k + 2 by omega)
  have el1 : lat1 e a.s ∈ G := ea1.2 (by omega)
  have el2 : lat2 e a.s ∈ G := ea2.2 (by omega)
  have eb : back e a.s ∉ G := fun h => by have := eab.1 h; omega
  have ef : front e a.s ∉ G := fun h => by have := (eaf.1 h).1 (by omega); omega
  have hce : IsCell V e := hcell (k + 1) le_rfl
  have hc0 : IsCell V a.c := by have := hcell 0 (by omega); rwa [cellJ_zero] at this
  -- `u'` (the previous end) differs from `e` and from the cell beyond, when `τ` starts at one
  -- of them and keeps off `u'`.
  --
  have off_e : ∀ y ∈ cellE e, y ∉ cellE u' → (y ∈ flip G u' ↔ y ∈ G) := fun y _ hy =>
    mem_flip_off hy
  -- **Through the end cell.**
  --
  have hR1 : ∀ i', i0 ≤ i' → i' < τ.n → cellJ τ.c τ.s i' = e → False := by
    intro i' hi0' hi' hq
    obtain ⟨hend, hdir⟩ := touch_end hk2 hpa hzs hi0' hi' hq
    have hendτ : endCell τ = e := by
      unfold endCell; rw [← hq, show τ.n - 1 = i' by omega]
    rcases hdir with ⟨_, hodd⟩ | ⟨hperp, hev⟩
    · cases L2 with
      | nil => have : τ.n % 2 = 1 := hch; omega
      | cons w L3 =>
        have hlw := hch.2.1
        have hnt := hfar2 w (List.mem_cons_self ..)
        have hpw : StripPat G w.c w.s w.n := by
          have h := hlw.2.2.2.1
          rw [hendτ] at h
          exact (pat_flip_off hlw.2.2.1 (fun jw hjw y hy hy' =>
            hnt ⟨jw, hjw, k + 1, by omega, y, hy, hy'⟩)).1 h
        have hsplit := hlw.2.2.2.2.2.2.2.2.2.2.2
        rw [hendτ] at hsplit
        exact via_a w L3 rfl hpw hsplit
    · by_cases hi0 : i' = 0
      · subst hi0
        have hz00 : i0 = 0 := by omega
        have hnc := hz0 hz00
        have hpτ := hpτ0 hz00
        rw [hτc0] at hq
        have hwe : u' ≠ e := fun h => hne 0 (by omega) (by rw [hτc0, hq, h])
        have hwu : u' ≠ nb e a.s := fun h => hnc 0 (by omega) (sideEdge e a.s)
          (by rw [hτc0, hq]; exact side_mem_self e a.s)
          (by show sideEdge e a.s ∈ cellE u'; rw [h]; exact side_mem_nb e a.s)
        have hoff : ∀ y ∈ cellE e, y ∉ cellE u' := fun y hy =>
          hnc 0 (by omega) y (by rw [hτc0, hq]; exact hy)
        have m1 : lat1 e a.s ∈ cellE e := by rw [cellE_frame e a.s]; simp
        have m2 : lat2 e a.s ∈ cellE e := by rw [cellE_frame e a.s]; simp
        have hsp := hcu
        rw [hq] at hsp
        exact split_core hG hT hk2 hcell hpa hsep hT'' hu lu1 lu2 bu fu hwe hwu
          (cross_to_back hperp ((mem_flip_off (hoff _ m1)).2 el1)
            ((mem_flip_off (hoff _ m2)).2 el2) hsp)
      · have hp := cell_prev (z := τ.c) (tf := τ.s) (i := i') (by omega)
        rw [hq] at hp
        rcases hperp with ht | ht
        · rw [show τ.s.opp = latB a.s by rw [ht, latA_opp_eq]] at hp
          rcases touch_side2_end hG hk2 hcell hpa hzs (i := i' - 1) (by omega) (by omega) hp with
            ⟨ht', _⟩ | ⟨_, hf, hl⟩
          · exact latA_ne_opp a.s (ht.symm.trans ht')
          · exact beside_end2 hG hT hk2 hcell hpa hsep
              ((outer2_body hG hcell hpa le_rfl).2 hk2) hf hl hT''
        · rw [show τ.s.opp = latA a.s by rw [ht, latB_opp_eq]] at hp
          rcases touch_side1_end hG hk2 hcell hpa hzs (i := i' - 1) (by omega) (by omega) hp with
            ⟨ht', _⟩ | ⟨_, hf, hl⟩
          · exact latB_ne_opp a.s (ht.symm.trans ht')
          · exact beside_end1 hG hT hk2 hcell hpa hsep
              ((outer1_body hG hcell hpa le_rfl).2 hk2) hf hl hT''
  -- **Through the cell beyond the end cell.**
  --
  have hR2 : ∀ i', i0 ≤ i' → i' < τ.n → cellJ τ.c τ.s i' = nb e a.s → False := by
    intro i' hi0' hi' hq
    have hpvs : τ.s = a.s → 1 ≤ i' → i0 ≤ i' - 1 := by
      intro ht hi1
      by_contra hc
      have hi1' : i' = 1 := by omega
      have hz1 : i0 = 1 := by omega
      have hp := cell_prev (z := τ.c) (tf := τ.s) (i := i') (by omega)
      rw [hq, ht, nb_nb_opp, hi1', show 1 - 1 = 0 from rfl, cellJ_zero] at hp
      exact hne_e hz1 (by rw [hendA]; exact hp)
    rcases touch_beyond hG hk2 hcell hpa hzs hi0' hi' hpvs (fun _ => by omega) hq with ⟨ht, hodd, hend⟩ | ⟨ht, _, hi1⟩ |
      ⟨hperp, h0⟩
    · have hendτ : endCell τ = nb e a.s := by
        unfold endCell; rw [← hq, show τ.n - 1 = i' by omega]
      cases L2 with
      | nil => have : τ.n % 2 = 1 := hch; omega
      | cons w L3 =>
        have hlw := hch.2.1
        have hnt := hfar2 w (List.mem_cons_self ..)
        have hsplit := hlw.2.2.2.2.2.2.2.2.2.2.2
        rw [hendτ] at hsplit
        obtain ⟨g1, g2, gb, _⟩ := hzs i' hi0' hi'
        rw [hq, ht] at g1 g2 gb
        rw [(frame_opp (nb e a.s) a.s).1] at g1
        rw [(frame_opp (nb e a.s) a.s).2.1] at g2
        rw [(frame_opp (nb e a.s) a.s).2.2.1] at gb
        have ul1 := g1.2 hodd
        have ul2 := g2.2 hodd
        have hncw : NoChain τ w := by
          intro jw hjw y hy hyu
          obtain ⟨rfl, hyl⟩ := hnct.1 jw hjw y hy hyu
          rw [hendτ] at hyu hyl
          obtain ⟨i1, hi1, j1, hj1, x1, h1, h2⟩ := e1_chain hG hk2 hcell hpa hlw (hnct.1) hendτ ht ul1 ul2 hy hyu hyl
          exact hnt ⟨i1, hi1, j1, by rw [hk]; exact hj1, x1, h1, h2⟩
        have hpw : StripPat G w.c w.s w.n := (pat_flip_off hlw.2.2.1 hncw).1 hlw.2.2.2.1
        have uf : front (nb e a.s) a.s ∉ G := fun h => by have := gb.1 h; omega
        have hcu' : IsCell V (nb e a.s) := by rw [← hq]; exact hcτ i' hi'
        have hcorner : ∀ y ∈ G, ∀ jw < w.n, y ∈ cellE (cellJ w.c w.s jw) → ∀ r,
            (y.p = r ∨ y.q = r) → r ≠ front1 e a.s ∧ r ≠ front2 e a.s := by
          intro y hy jw hjw hyw r hr
          have touchy : y ∈ cellE e → False := fun h => hnt ⟨jw, hjw, k + 1, by omega, y, hyw, h⟩
          have chainy : y ∈ cellE (nb e a.s) → False := fun h =>
            hncw jw hjw y hyw (by rw [hendτ]; exact h)
          constructor
          · rintro rfl
            have i2 := (ends_lat1 (nb e a.s) a.s).inc_iff (front1 e a.s) |>.2
              (Or.inl (back1_nb e a.s).symm)
            have hne2 : lat1 e a.s ≠ lat1 (nb e a.s) a.s := (ends_lat1 e a.s).ne_at
              (by have := ends_lat1 (nb e a.s) a.s; rwa [back1_nb] at this)
              (back1_ne_front1_nb e a.s)
            rcases two_at (hG.2 _ (corners4 hce a.s).2.2.1) el1 ul1
              ((ends_lat1 e a.s).inc_iff _ |>.2 (Or.inr rfl)) i2 hne2 hy hr with h | h
            · exact touchy (by rw [h, cellE_frame e a.s]; simp)
            · exact chainy (by rw [h, cellE_frame (nb e a.s) a.s]; simp)
          · rintro rfl
            have i2 := (ends_lat2 (nb e a.s) a.s).inc_iff (front2 e a.s) |>.2
              (Or.inl (back2_nb e a.s).symm)
            have hne2 : lat2 e a.s ≠ lat2 (nb e a.s) a.s := (ends_lat2 e a.s).ne_at
              (by have := ends_lat2 (nb e a.s) a.s; rwa [back2_nb] at this)
              (back2_ne_front2_nb e a.s)
            rcases two_at (hG.2 _ (corners4 hce a.s).2.2.2) el2 ul2
              ((ends_lat2 e a.s).inc_iff _ |>.2 (Or.inr rfl)) i2 hne2 hy hr with h | h
            · exact touchy (by rw [h, cellE_frame e a.s]; simp)
            · exact chainy (by rw [h, cellE_frame (nb e a.s) a.s]; simp)
        have hw1 : 1 ≤ w.n := hlw.2.2.1
        obtain ⟨⟨hb, hbp, hb0⟩, jf, hjf, xf, hxf, hxfp, hxfw⟩ := start_corner_edges hpw hw1
        have cb := hcorner _ hb 0 (by omega) hb0 _ hbp
        have cf := hcorner _ hxf jf hjf hxfw _ hxfp
        have hss := stacked_split hG hce hcu' el1 el2 eb ef ul1 ul2 uf cb.1 cb.2 cf.1 cf.2
        exact via_a w L3 rfl hpw (fun h => hsplit (hss.1 h))
    · exact hR1 (i' + 1) (by omega) hi1 (by rw [← nb_cellJ, hq, ht, nb_nb_opp])
    · subst h0
      have hz00 : i0 = 0 := by omega
      have hnc := hz0 hz00
      have hpτ := hpτ0 hz00
      rw [hτc0] at hq
      by_cases hm : 2 ≤ τ.n
      · exact beyond_cross hG hT hk2 hcell hpa hsep hT'' hpτ hperp hq hm
      · have hm1 : τ.n = 1 := by omega
        obtain ⟨_, _, gb, gf⟩ := strip_sig hpτ (show 0 < τ.n by omega)
        rw [hτc0, hq] at gb gf
        have hbz := gb.2 rfl
        have hfz := gf.2 ⟨fun h => by omega, fun h => by omega⟩
        have hl12 : lat1 (nb e a.s) a.s ∈ G ∧ lat2 (nb e a.s) a.s ∈ G := by
          rcases hperp with ht | ht <;> rw [ht] at hbz hfz
          · rw [(frame_latA _ _).1] at hfz; rw [(frame_latA _ _).2.1] at hbz; exact ⟨hfz, hbz⟩
          · rw [(frame_latB _ _).1] at hfz; rw [(frame_latB _ _).2.1] at hbz; exact ⟨hbz, hfz⟩
        have hoffu : ∀ y ∈ cellE (nb e a.s), y ∉ cellE u' := fun y hy =>
          hnc 0 (by omega) y (by rw [hτc0, hq]; exact hy)
        have hwu : u' ≠ nb e a.s := fun h => hne 0 (by omega) (by rw [hτc0, hq, h])
        have hwe : u' ≠ e := fun h => hoffu (sideEdge e a.s) (side_mem_nb e a.s)
          (by rw [h]; exact side_mem_self e a.s)
        have hoffe : ∀ y ∈ cellE e, y ∉ cellE u' := by
          intro y hy hy'
          rcases alt_touch hG hT hk2 hcell hpa hsep lu1 lu2 bu fu
            (show k + 1 < k + 2 by omega) hy' hy with h | h
          · exact hwe h
          · exact hwu h
        have m1 : lat1 (nb e a.s) a.s ∈ cellE (nb e a.s) := by rw [cellE_frame _ a.s]; simp
        have m2 : lat2 (nb e a.s) a.s ∈ cellE (nb e a.s) := by rw [cellE_frame _ a.s]; simp
        have m1e : lat1 e a.s ∈ cellE e := by rw [cellE_frame e a.s]; simp
        have m2e : lat2 e a.s ∈ cellE e := by rw [cellE_frame e a.s]; simp
        have hsp := hcu
        rw [hq] at hsp
        have h1 := cross_to_back hperp ((mem_flip_off (hoffu _ m1)).2 hl12.1)
          ((mem_flip_off (hoffu _ m2)).2 hl12.2) hsp
        rw [back1_nb, back2_nb] at h1
        exact split_core hG hT hk2 hcell hpa hsep hT'' hu lu1 lu2 bu fu hwe hwu
          (front_to_back ((mem_flip_off (hoffe _ m1e)).2 el1)
            ((mem_flip_off (hoffe _ m2e)).2 el2) h1)
  -- **Beside the start cell**: the suffix from there is a lighter path.
  --
  have hR3 : τ.s = a.s.opp → ∀ ie, i0 ≤ ie → ie < τ.n → ie % 2 = 0 →
      (cellJ τ.c τ.s ie = nb a.c (latA a.s) ∨ cellJ τ.c τ.s ie = nb a.c (latB a.s)) → False := by
    intro ht ie hie hi0 hev hq
    have hsep' : ¬ Conn G (back1 (cellJ τ.c τ.s ie) τ.s) (front1 (cellJ τ.c τ.s ie) τ.s) := by
      obtain ⟨g1, _, _, _⟩ := hzs ie hie hi0
      rcases hq with hq | hq <;> rw [hq] at g1 ⊢ <;> rw [ht] at g1 ⊢ <;> apply conn_lat1_opp
      · have hfar : lat1 (nb a.c (latA a.s)) a.s ∉ G := by
          rw [(frame_opp _ a.s).1] at g1; exact fun h => by have := g1.1 h; omega
        exact start_side_sep hG hT hpa (by omega) hc0 hsep hfar
      · rw [side2_back1, side2_front1]
        exact fun h => hsep ((((ends_back a.c a.s).conn hpa.1).trans h).trans
          (front_join hG hT hpa (by omega) hc0).symm)
    have hval := suf_validW hzs hcτ hie hev hi0 hsep'
    cases L2 with
    | nil =>
      have hodd : τ.n % 2 = 1 := hch
      refine nopath (suf τ ie) [] ⟨⟨hval, ?_⟩, trivial⟩ ?_
      · show (τ.n - ie) % 2 = 1; omega
      · simp [wt, suf] at hW1 ⊢; omega
    | cons w L3 =>
      obtain ⟨hτe, hlw, hrest⟩ := hch
      have hcr := suf_cr2 hlw hev (by omega)
      have hok' : ChainOK (suf τ ie) w := by
        have := hnct.1
        unfold ChainOK at this ⊢
        rw [suf_end (by omega)]; exact this
      refine nopath (suf τ ie) (w :: L3) ⟨⟨hval, ⟨by show (τ.n - ie) % 2 = 0; omega, hcr, hrest⟩⟩,
        ⟨hok', hnct.2⟩⟩ ?_
      rw [wt_cons]; rw [wt_cons] at hW1; simp only [suf]; omega
  rcases touch_outcomeW hG hT hk2 hcell hpa hsep hT'' hzs hii hi hj hx1 hx2 with
    ⟨i', hle, hi', hq⟩ | ⟨i', hle, hi', hq⟩ | ⟨ht, ie, hle, hi0, hev, hq⟩
  · exact hR1 i' (by omega) hi' hq
  · exact hR2 i' (by omega) hi' hq
  · exact hR3 ht ie (by omega) hi0 hev hq

-- **The last touching strip, chain case.** A chain strip `τ` after the second (sharing a lateral
-- side of the previous end cell), all of whose successors keep off `a`, does not touch `a`.
-- From its second cell on, `τ` has its pattern in `G` (`touch_core` at index 1). Its start
-- cell beside or beyond `a` either is impossible, or leads into `a` at index 1, or gives a
-- lighter path through `a` (`direct_link1/2`, `single3_link`).
--
theorem touch_contra_chain {σ τ : StripSpec} {L2 : List StripSpec} (hl : CR2 V G σ τ)
    (hok : ChainOK σ τ) (hch' : ¬ NoChain σ τ) (hσ : EndOK V G σ) (hσe : σ.n % 2 = 0)
    (hch : CRChain V G τ L2) (hnct : CATail (τ :: L2)) (hfar2 : ∀ w ∈ L2, ¬ Touches a w)
    {W2 : ℕ} (hvia : ViaFree V G a W2) (hW1 : wt τ L2 < W) (hW2 : a.n + wt τ L2 < W2) :
    ¬ Touches a τ := by
  rintro ⟨i, hi, j, hj, x, hx1, hx2⟩
  have nopath : ∀ σ' L', CRPathCA V G σ' L' → wt σ' L' < W → False :=
    fun σ' L' h hlt => by have := hmin σ' L' h; omega
  have hzs := chain_sig hl hok
  have core : ∀ {i j : ℕ} {x : Edge}, τ.c ≠ endCell a → 1 ≤ i → i < τ.n → j < a.n →
      x ∈ cellE (cellJ τ.c τ.s i) → x ∈ cellE (cellJ a.c a.s j) → False :=
    fun hne hii hi hj hx1 hx2 => touch_core hG hT ha hae ha2 hT' hmin hl hzs le_rfl
      (fun h => absurd h (by omega)) (fun _ => hne) hσ hσe hch hnct hfar2 hvia hW1 hW2 hii hi hj hx1 hx2
  obtain ⟨hu, lu1, lu2, bu, fu⟩ := hσ hσe
  obtain ⟨jy, hjy, y, hy, hyu⟩ : ∃ jy < τ.n, ∃ y ∈ cellE (cellJ τ.c τ.s jy),
      y ∈ cellE (endCell σ) := by
    by_contra hn; push Not at hn; exact hch' hn
  obtain ⟨rfl, -⟩ := hok jy hjy y hy hyu
  rw [cellJ_zero] at hy
  obtain ⟨hyG, hylat, hbG, hfr, hyl⟩ := chain_start hl hok ⟨lu1, lu2⟩ hy hyu
  have hdu : τ.c ≠ endCell σ := by
    have := hl.2.2.2.2.2.2.1 0 hl.2.2.1; rwa [cellJ_zero] at this
  have hτ1 : 1 ≤ τ.n := hl.2.2.1
  obtain ⟨k, hk⟩ : ∃ k, a.n = k + 2 := ⟨a.n - 2, by omega⟩
  have hk2 : k % 2 = 0 := by omega
  have hpa : StripPat G a.c a.s (k + 2) := by rw [← hk]; exact ha.2.1
  have hcell : ∀ j ≤ k + 1, IsCell V (cellJ a.c a.s j) := fun j hj => ha.2.2.1 j (by omega)
  have hsep := ha.2.2.2
  have hT'' : NoTypeIII V (flipCol G a.c a.s (k + 2)) := by unfold applyS at hT'; rwa [hk] at hT'
  have hendA : endCell a = cellJ a.c a.s (k + 1) := by unfold endCell; rw [hk]; rfl
  have haeq : (⟨a.c, a.s, k + 2⟩ : StripSpec) = a := by rw [← hk]
  -- A link from `a` straight to `τ`, when `τ` is a chain strip of `a`'s end cell.
  --
  have via_end : endCell σ = endCell a → CR2 V G a τ →
      (L2 ≠ [] → ∀ j < a.n, ∀ y ∈ cellE (endCell τ), y ∉ cellE (cellJ a.c a.s j)) → False := by
    intro hue hlink hfe
    have hokA : ChainOK a τ := by
      intro jj hjj z hz hze
      obtain ⟨hj0, hzl⟩ := hok jj hjj z hz (hue ▸ hze)
      refine ⟨hj0, ?_⟩
      have hzG : z ∈ G := by rcases hzl with rfl | rfl; exacts [lu1, lu2]
      obtain ⟨ea1, ea2, eab, eaf⟩ := strip_sig hpa (show k + 1 < k + 2 by omega)
      have eb : back (endCell a) a.s ∉ G := fun h => by rw [hendA] at h; have := eab.1 h; omega
      have ef : front (endCell a) a.s ∉ G := fun h => by
        rw [hendA] at h; have := (eaf.1 h).1 (by omega); omega
      rw [cellE_frame _ a.s] at hze
      simp only [Finset.mem_insert, Finset.mem_singleton] at hze
      rcases hze with rfl | rfl | rfl | rfl
      · exact absurd hzG eb
      · exact absurd hzG ef
      · exact Or.inl rfl
      · exact Or.inr rfl
    exact hvia τ L2 ⟨⟨ha, hae, hlink, hch⟩, hokA, hnct⟩ hfar2 hfe (by rw [wt_cons]; omega)
  have hce : τ.c ≠ endCell a := fun h =>
    start_not_body hk2 hpa hbG hyG hylat hyl lu1 lu2 bu fu hyu hdu (le_refl (k + 1)) (h.trans hendA)
  rcases Nat.eq_zero_or_pos i with rfl | hi1
  swap
  · exact core hce hi1 hi hj hx1 hx2
  rw [cellJ_zero] at hx1
  rw [hk] at hj
  rcases touch_cases a.s hx1 hx2 with h | h | h | h | h
  · exact start_not_body hk2 hpa hbG hyG hylat hyl lu1 lu2 bu fu hyu hdu (by omega) h
  · by_cases hjk : j ≤ k
    · exact start_not_body hk2 hpa hbG hyG hylat hyl lu1 lu2 bu fu hyu hdu (show j + 1 ≤ k + 1 by omega) (h.trans (nb_cellJ a.c a.s j))
    obtain rfl : j = k + 1 := by omega
    rcases start_beyond hG hT hk2 hcell hpa hsep hbG hyG hylat hyl hyu hdu hs x0 hconn hT'' hfr h with
      ⟨ht, hfn⟩ | ⟨hm1, hud, hd1, hd2, hdf⟩
    · -- `τ` runs into the end cell.
      --
      have hn2 : 2 ≤ τ.n := by
        by_contra hn; exact hfn (hfr.2 (by omega))
      have h1 : cellJ τ.c τ.s 1 = endCell a := by
        rw [← nb_cellJ, cellJ_zero, ht, h, nb_nb_opp, hendA]
      have hm : back (endCell a) a.s ∈ cellE (endCell a) := by rw [cellE_frame _ a.s]; simp
      exact core hce le_rfl hn2 (show k + 1 < a.n by omega) (by rw [h1]; exact hm)
        (by rw [← hendA]; exact hm)
    · -- `τ` is a single cell with three dark sides: a shortcut to `u`.
      --
      have hd' : τ.c = cellJ a.c a.s (k + 2) := h.trans (nb_cellJ a.c a.s (k + 1))
      have hu' : endCell σ = cellJ a.c a.s (k + 3) := hud.trans (by rw [hd', nb_cellJ])
      have hcd : IsCell V (cellJ a.c a.s (k + 2)) := by
        rw [← hd']; have := hl.2.2.2.2.1 0 hτ1; rwa [cellJ_zero] at this
      rw [hd'] at hd1 hd2 hdf
      rw [hu'] at hu lu1 lu2 bu fu
      have hlink := single3_link hG hT hk2 hcell hpa hd1 hd2 hdf hu lu1 lu2 bu fu hcd
      rw [haeq] at hlink
      have hL2 : L2 = [] := by
        cases L2 with
        | nil => rfl
        | cons w L3 => have := hch.1; omega
      subst hL2
      have hokA : ChainOK a ⟨cellJ a.c a.s (k + 3), a.s, 1⟩ := by
        intro jj hjj z hz hze
        exfalso
        obtain rfl : jj = 0 := by simp only at hjj; omega
        rw [cellJ_zero] at hz
        rw [hendA] at hze
        exact along_not_mem a.c a.s (show k + 1 + 2 ≤ k + 3 by omega) hz hze
      refine hvia _ [] ⟨⟨ha, hae, hlink, rfl⟩, hokA, trivial⟩ (by simp) (fun h => absurd rfl h) ?_
      simp only [wt, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at hW2 ⊢
      omega
  · rcases j with _ | j
    · rw [cellJ_zero] at h
      exact start_not_behind hG hT hk2 hcell hpa hsep hbG hyG hylat hyl lu1 lu2 bu fu hyu hdu h
    · exact start_not_body hk2 hpa hbG hyG hylat hyl lu1 lu2 bu fu hyu hdu (show j ≤ k + 1 by omega) (by rw [h, ← nb_cellJ, nb_nb_opp])
  · by_cases hjk : j ≤ k
    · obtain ⟨ht, hje, hyf⟩ := start_beside1 hG hT hk2 hcell hpa hsep hbG hyG hylat hyl lu1 lu2 bu fu hyu hdu hjk h
      have hfn : front τ.c τ.s ∉ G := by
        rw [ht, (frame_opp _ a.s).2.2.2, h]
        intro hb'
        have := (side1_facts hG hT hk2 hcell hpa hsep hjk).2.1.1 hb'; omega
      have hn2 : 2 ≤ τ.n := by
        by_contra hn; exact hfn (hfr.2 (by omega))
      rcases j with _ | j
      · rw [cellJ_zero] at h
        exact start_L0 hG hT hk2 hcell hpa hsep (by rw [← h, ← ht]; exact hzs) hn2
          (by rw [← h, ← ht]; exact hl.2.2.2.2.1 1 hn2) (by rw [← h, ← hyf]; exact hyG)
      · have h1 : cellJ τ.c τ.s 1 = nb (cellJ a.c a.s j) (latA a.s) := by
          rw [← nb_cellJ, cellJ_zero, ht, h, side1_down]
        exact core hce le_rfl hn2 (show j < a.n by omega) (by rw [h1]; exact side_mem_nb _ _)
          (side_mem_self _ _)
    · obtain rfl : j = k + 1 := by omega
      obtain ⟨hue, ht⟩ := start_beside_end1 hG hT hk2 hcell hpa hsep hbG hyG hylat hyl lu1 lu2 bu fu hyu hdu h
      have hfe : L2 ≠ [] → ∀ j < a.n, ∀ y ∈ cellE (endCell τ), y ∉ cellE (cellJ a.c a.s j) := by
        intro hL2 j hj y hy
        have hev : τ.n % 2 = 0 := by
          cases L2 with
          | nil => exact absurd rfl hL2
          | cons _ _ => exact hch.1
        have hτs : τ.s = a.s := ht.resolve_right (fun h' => by have := hfr.1 h'.2; omega)
        unfold endCell at hy
        rw [hτs, h] at hy
        exact beside_end_farA a.c a.s k (show 2 ≤ τ.n by omega) hy j (by omega)
      exact via_end (hue.trans hendA.symm) (haeq ▸ direct_link1 hk2 hl hue h
        (ht.imp_right fun h' => ⟨h'.1, hfr.1 h'.2⟩)) hfe
  · by_cases hjk : j ≤ k
    · obtain ⟨ht, hje, hyf⟩ := start_beside2 hG hT hk2 hcell hpa hsep hbG hyG hylat hyl lu1 lu2 bu fu hyu hdu hjk h
      have hfn : front τ.c τ.s ∉ G := by
        rw [ht, (frame_opp _ a.s).2.2.2, h]
        intro hb'
        have := (side2_facts hG hT hk2 hcell hpa hsep hjk).2.1.1 hb'; omega
      have hn2 : 2 ≤ τ.n := by
        by_contra hn; exact hfn (hfr.2 (by omega))
      rcases j with _ | j
      · rw [cellJ_zero] at h
        exact start_R0 hG hT hk2 hcell hpa hsep (by rw [← h, ← ht]; exact hzs) hn2
          (by rw [← h, ← ht]; exact hl.2.2.2.2.1 1 hn2) (by rw [← h, ← hyf]; exact hyG)
      · have h1 : cellJ τ.c τ.s 1 = nb (cellJ a.c a.s j) (latB a.s) := by
          rw [← nb_cellJ, cellJ_zero, ht, h, side2_down]
        exact core hce le_rfl hn2 (show j < a.n by omega) (by rw [h1]; exact side_mem_nb _ _)
          (side_mem_self _ _)
    · obtain rfl : j = k + 1 := by omega
      obtain ⟨hue, ht⟩ := start_beside_end2 hG hT hk2 hcell hpa hsep hbG hyG hylat hyl lu1 lu2 bu fu hyu hdu h
      have hfe : L2 ≠ [] → ∀ j < a.n, ∀ y ∈ cellE (endCell τ), y ∉ cellE (cellJ a.c a.s j) := by
        intro hL2 j hj y hy
        have hev : τ.n % 2 = 0 := by
          cases L2 with
          | nil => exact absurd rfl hL2
          | cons _ _ => exact hch.1
        have hτs : τ.s = a.s := ht.resolve_right (fun h' => by have := hfr.1 h'.2; omega)
        unfold endCell at hy
        rw [hτs, h] at hy
        exact beside_end_farB a.c a.s k (show 2 ≤ τ.n by omega) hy j (by omega)
      exact via_end (hue.trans hendA.symm) (haeq ▸ direct_link2 hk2 hl hue h
        (ht.imp_right fun h' => ⟨h'.1, hfr.1 h'.2⟩)) hfe

theorem notouch_CA {W2 : ℕ} (hvia : ViaFree V G a W2) : ∀ (L : List StripSpec) (σ : StripSpec),
    CRChain V G σ L → CATail (σ :: L) → EndOK V G σ → wt σ L ≤ W → a.n + wt σ L ≤ W2 →
    ∀ τ ∈ L, ¬ Touches a τ := by
  intro L
  induction L with
  | nil => intro _ _ _ _ _ _ τ h; simp at h
  | cons τ L' ih =>
    intro σ hch hnct hσ hW hW2
    obtain ⟨hσe, hl, hrest⟩ := hch
    have hfar2 := ih τ hrest hnct.2 (endOK_of_link hl) (by rw [wt_cons] at hW; omega)
      (by rw [wt_cons] at hW2; omega)
    have hW1' : wt τ L' < W := by rw [wt_cons] at hW; have := hl.1; omega
    have hW2' : a.n + wt τ L' < W2 := by rw [wt_cons] at hW2; have := hl.1; omega
    intro w hw
    rcases List.mem_cons.1 hw with rfl | hw'
    · by_cases hnc : NoChain σ w
      · exact touch_contra_plain hG hT ha hae ha2 hT' hmin hl hnc hσ hσe hrest
          hnct.2 hfar2 hvia hW1' hW2'
      · exact touch_contra_chain hs x0 hconn hG hT ha hae ha2 hT' hmin hl hnct.1 hnc hσ hσe
          hrest hnct.2 hfar2 hvia hW1' hW2'
    · exact hfar2 w hw'

omit hs x0 hconn hT hT' hmin in
theorem farchain_CA {W2 : ℕ} (hvia : ViaFree V G a W2) : ∀ (L : List StripSpec) (σ : StripSpec),
    CRChain V G σ L → CATail (σ :: L) → EndOK V G σ →
    (∀ j < a.n, ∀ y ∈ cellE (endCell σ), y ∉ cellE (cellJ a.c a.s j)) →
    (∀ τ ∈ L, ¬ Touches a τ) → a.n + wt σ L ≤ W2 → FarChainCA G a σ L := by
  intro L
  induction L with
  | nil => intro _ _ _ _ _ _ _; trivial
  | cons τ L' ih =>
    intro σ hch hnct hσ hσfar hnt hW
    obtain ⟨hσe, hl, hrest⟩ := hch
    obtain ⟨k, hk⟩ : ∃ k, a.n = k + 2 := ⟨a.n - 2, by omega⟩
    have ha' := ha
    obtain ⟨_, hpa, hca, hsep⟩ := ha'
    rw [hk] at hpa hca
    have hcell : ∀ j ≤ k + 1, IsCell V (cellJ a.c a.s j) := fun j hj => hca j (by omega)
    have hnτ := hnt τ (List.mem_cons_self ..)
    have hτ1 : 1 ≤ τ.n := hl.2.2.1
    obtain ⟨hu, lu1, lu2, _, _⟩ := hσ hσe
    have hmidτ : ∀ p, (∃ j < τ.n, ∃ x ∈ G, (x.p = p ∨ x.q = p) ∧ x ∈ cellE (cellJ τ.c τ.s j)) →
        ¬ IsMid a.c a.s (a.n - 2) p := by
      rintro p ⟨j, hj, x, hx, hxp, hxw⟩ hm
      rw [hk, show k + 2 - 2 = k by omega] at hm
      obtain ⟨i, hi, hxi⟩ := mid_touch hG hpa hcell hm hx hxp
      exact hnτ ⟨j, hj, i, by omega, x, hxw, hxi⟩
    have hmidσ : ∀ p (x : Edge), x ∈ G → (x.p = p ∨ x.q = p) → x ∈ cellE (endCell σ) →
        ¬ IsMid a.c a.s (a.n - 2) p := by
      intro p x hx hxp hxw hm
      rw [hk, show k + 2 - 2 = k by omega] at hm
      obtain ⟨i, hi, hxi⟩ := mid_touch hG hpa hcell hm hx hxp
      exact hσfar i (by omega) x hxw hxi
    -- The start corners of `τ` carry dark edges of `τ`, chain strip or not.
    --
    have hcorn : (back τ.c τ.s ∈ G ∧
        ((back τ.c τ.s).p = back1 τ.c τ.s ∨ (back τ.c τ.s).q = back1 τ.c τ.s) ∧
        back τ.c τ.s ∈ cellE (cellJ τ.c τ.s 0)) ∧
        ∃ j < τ.n, ∃ x ∈ G, (x.p = front1 τ.c τ.s ∨ x.q = front1 τ.c τ.s) ∧
          x ∈ cellE (cellJ τ.c τ.s j) := by
      by_cases hnc : NoChain σ τ
      · exact start_corner_edges ((pat_flip_off hτ1 hnc).1 hl.2.2.2.1) hτ1
      · obtain ⟨jy, hjy, y, hy, hyu⟩ : ∃ jy < τ.n, ∃ y ∈ cellE (cellJ τ.c τ.s jy),
            y ∈ cellE (endCell σ) := by
          by_contra hn; push Not at hn; exact hnc hn
        obtain ⟨rfl, -⟩ := hnct.1 jy hjy y hy hyu
        rw [cellJ_zero] at hy
        obtain ⟨_, _, hbG, hfr, _⟩ := chain_start hl hnct.1 ⟨lu1, lu2⟩ hy hyu
        exact chain_corner_edges hτ1 hbG hfr (chain_sig hl hnct.1)
    obtain ⟨⟨hb, hbp, hb0⟩, hfr⟩ := hcorn
    have mσ1 : lat1 (endCell σ) σ.s ∈ cellE (endCell σ) := by rw [cellE_frame _ σ.s]; simp
    have mσ2 : lat2 (endCell σ) σ.s ∈ cellE (endCell σ) := by rw [cellE_frame _ σ.s]; simp
    refine ⟨⟨hσfar, hmidσ _ _ lu1 ((ends_lat1 _ _).inc_iff _ |>.2 (Or.inl rfl)) mσ1,
      hmidσ _ _ lu2 ((ends_lat2 _ _).inc_iff _ |>.2 (Or.inl rfl)) mσ2,
      fun i hi j hj y hy hy' => hnτ ⟨i, hi, j, hj, y, hy, hy'⟩,
      hmidτ _ ⟨0, by omega, _, hb, hbp, hb0⟩, hmidτ _ hfr, ?_⟩, ?_⟩
    · rintro hnc ⟨hcg, hcu⟩
      have hpτ : StripPat G τ.c τ.s τ.n := (pat_flip_off hτ1 hnc).1 hl.2.2.2.1
      have hlink : CR2 V G a τ := link_a hG ha hae ha2 hτ1 hpτ hl.2.2.2.2.1 hnτ hcg hcu
      have hokA : ChainOK a τ := chainOK_of_noChain (fun j hj y hy hye =>
        hnτ ⟨j, hj, a.n - 1, by omega, y, hy, by unfold endCell at hye; exact hye⟩)
      refine hvia τ L' ⟨⟨ha, hae, hlink, hrest⟩, hokA, hnct.2⟩
        (fun x hx => hnt x (List.mem_cons_of_mem _ hx))
        (fun _ j hj y hy hy' => hnτ ⟨τ.n - 1, by omega, j, hj, y, by unfold endCell at hy; exact hy,
          hy'⟩) ?_
      rw [wt_cons]; rw [wt_cons] at hW; have := hl.1; omega
    · refine ih τ hrest hnct.2 (endOK_of_link hl) (fun j hj y hy hy' => hnτ ⟨τ.n - 1, by omega,
        j, hj, y, hy, hy'⟩) (fun w hw => hnt w (List.mem_cons_of_mem _ hw))
        (by rw [wt_cons] at hW; omega)

-- **The near lemma, class CA.** In a minimum path with chain links anywhere, the later links
-- are far from the first strip and are not created by its end cell.
--
theorem near_far_CA {b : StripSpec} {L : List StripSpec} (hP : CRPathCA V G a (b :: L))
    (hWeq : W = wt a (b :: L)) : FarChainCA G a b L := by
  obtain ⟨⟨_, _, hab, hch⟩, hcat⟩ := hP
  have hW : a.n + wt b L ≤ W := by rw [hWeq, wt_cons]
  have hvia0 : ViaFree V G a W := fun w R hP _ _ hlt => by have := hmin a (w :: R) hP; omega
  cases L with
  | nil => trivial
  | cons τ L' =>
    have hbe : b.n % 2 = 0 := hch.1
    have hbfar : ∀ j < a.n, ∀ y ∈ cellE (endCell b), y ∉ cellE (cellJ a.c a.s j) := by
      intro j hj y hy hy'
      by_cases hja : j + 1 < a.n
      · exact hab.2.2.2.2.2.1 (b.n - 1) (by have := hab.2.2.1; omega) j hja y hy hy'
      · exact hab.2.2.2.2.2.2.2.1 hbe y hy (by
          unfold endCell; rw [show a.n - 1 = j by omega]; exact hy')
    exact farchain_CA hG ha hae ha2 hvia0 (τ :: L') b hch hcat.2
      (endOK_of_link hab) hbfar
      (notouch_CA hs x0 hconn hG hT ha hae ha2 hT' hmin hvia0 (τ :: L') b hch hcat.2
        (endOK_of_link hab) (by omega) hW) hW

-- **One round, class CA.** After the first strip of a minimum path, the rest is a path of the
-- new factor, lighter by the first strip.
--
theorem round_ca {b : StripSpec} {L : List StripSpec} (hP : CRPathCA V G a (b :: L))
    (hWeq : W = wt a (b :: L)) :
    CRPathCA V (applyS G a) b L ∧ wt b L + a.n = wt a (b :: L) :=
  progress_step_CA hG hT ha hae ha2 hT' hP.1.2 hP.2
    (near_far_CA hs x0 hconn hG hT ha hae ha2 hT' hmin hP hWeq)

end nearpathCA

end SolidGridHam
