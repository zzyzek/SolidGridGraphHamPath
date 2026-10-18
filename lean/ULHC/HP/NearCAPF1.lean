/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
import ULHC.NearCA
import ULHC.HP.NearLemmaPF

/-!
# ULHC's NearCA, part 1, for path-factors: `e1_chain` and where a chain strip can start

`e1_chain` with degree 2 only at the end cell's corners; the `start_*` lemmas in the path-factor
setting of `NearLemmaPF` (E1 cells `hTs`, E2 cells `hTend`); `start_L0`/`start_R0` need the
touching strip's second cell to be restricted.
-/

namespace ULHC

namespace HP

open Finset Classical

section e1

variable {V : Finset Pt} {G : Finset Edge} {c : Pt} {s : Side} {k : ℕ}
  (hDc : ∀ j ≤ k + 1, ∀ z, IsCorner z (cellJ c s j) → deg G z = 2) (hk : k % 2 = 0)
  (hcell : ∀ j ≤ k + 1, IsCell V (cellJ c s j)) (hpat : StripPat G c s (k + 2))
include hDc hk hcell hpat

theorem e1_chain_L {τ w : StripSpec} (hl : CR2 V G τ w) (hok : ChainOK τ w)
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
      have hd := hDc (k + 1) le_rfl _ (isCorner_front1 _ s)
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
      have hd := hDc (k + 1) le_rfl _ (isCorner_front2 _ s)
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

lemma start_frame_L {F : Finset Edge} {d : Pt} {tf : Side} (s : Side) (hb : back d tf ∈ F)
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

lemma body_not_alt_L {F : Finset Edge} {c : Pt} {s : Side} {k : ℕ} (hk : k % 2 = 0)
    (hpat : StripPat F c s (k + 2)) {j : ℕ} (hj : j ≤ k) {tw : Side}
    (l1 : lat1 (cellJ c s j) tw ∈ F) (l2 : lat2 (cellJ c s j) tw ∈ F)
    (bw : back (cellJ c s j) tw ∉ F) (fw : front (cellJ c s j) tw ∉ F) : False := by
  obtain ⟨_, _, ab, af⟩ := strip_sig hpat (show j < k + 2 by omega)
  have := (alt_frame s l1 l2 bw fw).1
  rw [ab, af] at this; omega


-- **Side facts needing "not Type III" only at index 0** (beside the body, across `lat1`): from
-- index 1 on they hold outright (`side1_facts_succ`).
--
lemma side1_facts_R {V : Finset Pt} {F : Finset Edge} {c : Pt} {s : Side} {k : ℕ} {s0 t0 : Pt}
    (hV : Inside (insert s0 (insert t0 V)) F)
    (hDc : ∀ j ≤ k + 1, ∀ z, IsCorner z (cellJ c s j) → deg F z = 2)
    (_hcell : ∀ j ≤ k + 1, IsCell V (cellJ c s j)) (hpat : StripPat F c s (k + 2))
    (hsep : ¬ Conn F (back1 c s) (front1 c s)) {j : ℕ} (hj : j ≤ k)
    (hX : j = 0 → IsCell (insert s0 (insert t0 V)) (nb c (latA s)) →
      NotTypeIII (insert s0 (insert t0 V)) F (nb c (latA s))) :
    (lat2 (nb (cellJ c s j) (latA s)) s ∈ F ↔ j % 2 = 1) ∧
      (back (nb (cellJ c s j) (latA s)) s ∈ F ↔ j % 2 = 1) ∧
      (front (nb (cellJ c s j) (latA s)) s ∈ F ↔ j % 2 = 0) := by
  rcases Nat.eq_zero_or_pos j with rfl | hj1
  · refine ⟨by rw [side_lat2]; exact (strip_sig hpat (show 0 < k + 2 by omega)).1, ?_, ?_⟩
    · rw [cellJ_zero]
      simp only [Nat.zero_mod, zero_ne_one, iff_false]
      exact back_outer_light_loc hV hpat (by omega) hsep
        (hDc 0 (by omega) _ (by rw [cellJ_zero]; exact isCorner_front1 c s)) (hX rfl)
    · rw [side_front]; exact outer1_body_L hDc hpat hj
  · exact side1_facts_succ hDc hpat hj1 hj

lemma side2_facts_R {V : Finset Pt} {F : Finset Edge} {c : Pt} {s : Side} {k : ℕ} {s0 t0 : Pt}
    (hV : Inside (insert s0 (insert t0 V)) F)
    (hDc : ∀ j ≤ k + 1, ∀ z, IsCorner z (cellJ c s j) → deg F z = 2)
    (hcell : ∀ j ≤ k + 1, IsCell V (cellJ c s j)) (hpat : StripPat F c s (k + 2))
    (hsep : ¬ Conn F (back1 c s) (front1 c s))
    (hTrW : IsCell (insert s0 (insert t0 V)) (nb c s) →
      NotTypeIII (insert s0 (insert t0 V)) F (nb c s)) {j : ℕ} (hj : j ≤ k)
    (hX : j = 0 → IsCell (insert s0 (insert t0 V)) (nb c (latB s)) →
      NotTypeIII (insert s0 (insert t0 V)) F (nb c (latB s))) :
    (lat1 (nb (cellJ c s j) (latB s)) s ∈ F ↔ j % 2 = 1) ∧
      (back (nb (cellJ c s j) (latB s)) s ∈ F ↔ j % 2 = 1) ∧
      (front (nb (cellJ c s j) (latB s)) s ∈ F ↔ j % 2 = 0) := by
  have hc0 : IsCell V c := by have := hcell 0 (by omega); rwa [cellJ_zero] at this
  rcases Nat.eq_zero_or_pos j with rfl | hj1
  · refine ⟨by rw [side2_lat1]; exact (strip_sig hpat (show 0 < k + 2 by omega)).2.1, ?_, ?_⟩
    · rw [cellJ_zero]
      simp only [Nat.zero_mod, zero_ne_one, iff_false]
      exact back_outer2_light_loc hV hpat (by omega) (isCell_mono hc0 (sub_insST V s0 t0)) hsep
        (hDc 0 (by omega) _ (by rw [cellJ_zero]; exact isCorner_front1 c s))
        (hDc 0 (by omega) _ (by rw [cellJ_zero]; exact isCorner_front2 c s)) hTrW (hX rfl)
    · rw [side2_front]; exact outer2_body_L hDc hpat hj
  · exact side2_facts_succ hDc hpat hj1 hj

-- **NEW MATH (phantom P2b, chain start).** `start_beyond_pf` when `t0 ∉ V`. Its proof closes
-- except where `t0` is the far back corner of the square beside the end cell.
--
def Gap_start : Prop :=
  ∀ {V : Finset Pt} {F : Finset Edge} {c : Pt} {s : Side} {k : ℕ} {s0 t0 : Pt}
    {d u : Pt} {tf : Side} {x : Edge} {m : ℕ},
    Deg2Off V F s0 t0 → s0 ∈ V → deg F s0 = 1 → (∀ z, deg F z ≤ 2) → NoTypeIIIR V F s0 t0 →
    k % 2 = 0 → (∀ j ≤ k + 1, IsCell V (cellJ c s j)) →
    (∀ j ≤ k + 1, ¬ IsCorner s0 (cellJ c s j) ∧ ¬ IsCorner t0 (cellJ c s j)) →
    StripPat F c s (k + 2) → ¬ Conn F (back1 c s) (front1 c s) →
    NoTypeIIIR V (flipCol F c s (k + 2)) s0 t0 → ncomp V (flipCol F c s (k + 2)) = ncomp V F →
    (∀ tf, (tf = latA s ∨ tf = latB s) → IsCell V (nb c tf) → NotTypeIII V F (nb c tf)) →
    (∀ tf, (tf = latA s ∨ tf = latB s) → IsCell V (nb (cellJ c s (k + 1)) tf) →
      NotTypeIII V (flipCol F c s (k + 2)) (nb (cellJ c s (k + 1)) tf)) →
    back d tf ∈ F → x ∈ F → (x = lat1 d tf ∨ x = lat2 d tf) →
    ((lat1 d tf ∈ F ∧ lat2 d tf ∉ F) ∨ (lat2 d tf ∈ F ∧ lat1 d tf ∉ F)) →
    x ∈ cellE u → d ≠ u →
    (front d tf ∈ F ↔ m = 1) → d = nb (cellJ c s (k + 1)) s → (m ≠ 1 → ¬ IsCorner t0 (nb d tf)) →
    ¬ PDang V t0 → (¬ ∃ σ L', RPathTg V (flipCol F c s (k + 2)) s0 t0 σ L') → t0 ∉ V →
    (tf = s.opp ∧ front d tf ∉ F) ∨
      (m = 1 ∧ u = nb d s ∧ lat1 d s ∈ F ∧ lat2 d s ∈ F ∧ front d s ∈ F)

class NearOK2 (V : Finset Pt) (t0 : Pt) : Prop where
  ok : t0 ∈ V ∨ PDang V t0 ∨ Gap_start

section chainstart

variable {V : Finset Pt} {F : Finset Edge} {c : Pt} {s : Side} {k : ℕ}
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
  (hTend : ∀ tf, (tf = latA s ∨ tf = latB s) → IsCell V (nb (cellJ c s (k + 1)) tf) →
    NotTypeIII V (flipCol F c s (k + 2)) (nb (cellJ c s (k + 1)) tf))
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
theorem start_not_body_pf {j : ℕ} (hj : j ≤ k + 1) (hd : d = cellJ c s j) : False := by
  obtain ⟨a1, a2, ab, af⟩ := strip_sig hpat (show j < k + 2 by omega)
  rw [← hd] at a1 a2 ab af
  rcases start_frame_L s hb hxl with ⟨_, hdiff⟩ | ⟨ht, hlat, hbf⟩
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
      exact body_not_alt_L hk hpat (j := j + 1) (by omega) lu1 lu2 bu fu

include hF hs0 hTR hk hcell hcor hpat hsep hTs hTsP hb hxd hxlat hxl lu1 lu2 bu fu hxu hdu in
-- A chain strip does not start behind `c_0`.
--
theorem start_not_behind_pf (hd : d = nb c s.opp) : False := by
  have hDc := corners_deg2 hF hcell hcor
  have hTr := ahead_notT3 hTR hcell hcor hk
  have hcellW : ∀ j ≤ k + 1, IsCell (insert s0 (insert t0 V)) (cellJ c s j) :=
    fun j hj => isCell_mono (hcell j hj) (sub_insST V s0 t0)
  have hTrW := notT3W (t0 := t0) hs0 hTr (fun ht => absurd
    (show IsCorner t0 (cellJ c s 1) by rw [← nb_cellJ, cellJ_zero]; exact ht) (hcor 1 (by omega)).2)
  have hTsW := fun tf htf => notT3W (t0 := t0) hs0 (hTs tf htf) (hTsP tf htf)
  have hTe : NotTypeIII V F (cellJ c s (k + 1)) := restr_notT3 hTR (hcell (k + 1) le_rfl) (hcor (k + 1) le_rfl)
  have hsame := end_same_loc hTe hk hcell hpat
  have hc0 : IsCell V c := by have := hcell 0 (by omega); rwa [cellJ_zero] at this

  have hd0 : ∀ z, IsCorner z c → deg F z = 2 := fun z hz => hDc 0 (by omega) z (by rw [cellJ_zero]; exact hz)
  have d1 := back_down_loc hF.1 hpat (by omega) hsep (hd0 _ (isCorner_back1 c s)) (hd0 _ (isCorner_front1 c s)) (hTsW (latA s) (Or.inl rfl))
  have d2 := back_down2_loc hF.1 hpat (by omega) (isCell_mono hc0 (sub_insST V s0 t0)) hsep (hd0 _ (isCorner_back2 c s)) (hd0 _ (isCorner_front1 c s)) (hd0 _ (isCorner_front2 c s)) hTrW (hTsW (latB s) (Or.inr rfl))
  have df : front d s ∈ F := by rw [hd, front_nb_opp]; exact hpat.1
  rw [← hd] at d1 d2
  rcases start_frame_L s hb hxl with ⟨_, hdiff⟩ | ⟨ht, _, hbf⟩
  · exact (hdiff.1 d1) d2
  · have hbF : back d s ∉ F := fun h => hbf.1 h df
    have hxf : x = front d s := by
      rcases perp_x hxlat ht with h | h
      · exact absurd (h ▸ hxd) hbF
      · exact h
    have hu' := u_across hxu hdu hxf
    rw [hd, behind_up] at hu'
    rw [hu', ← cellJ_zero c s] at lu1 lu2 bu fu
    exact body_not_alt_L hk hpat (j := 0) (by omega) lu1 lu2 bu fu

include hF hs0 hTR hk hcell hcor hpat hsep hT' hneut hTs hTend hb hxd hxlat hxl lu1 lu2 bu fu hxu hdu in
-- A chain strip starting beside the body (across `lat1`) runs against `s`, from an even index,
-- with the shared side on the far side.
--
theorem start_beside1_pf {j : ℕ} (hj : j ≤ k) (hd : d = nb (cellJ c s j) (latA s))
    (hdR : ¬ IsCorner t0 d) (huR : ¬ IsCorner t0 u) :
    tf = s.opp ∧ j % 2 = 0 ∧ x = lat1 d s := by
  have hDc := corners_deg2 hF hcell hcor
  have hTr := ahead_notT3 hTR hcell hcor hk
  have hcellW : ∀ j ≤ k + 1, IsCell (insert s0 (insert t0 V)) (cellJ c s j) :=
    fun j hj => isCell_mono (hcell j hj) (sub_insST V s0 t0)
  have hTrW := notT3W (t0 := t0) hs0 hTr (fun ht => absurd
    (show IsCorner t0 (cellJ c s 1) by rw [← nb_cellJ, cellJ_zero]; exact ht) (hcor 1 (by omega)).2)
  have hTe : NotTypeIII V F (cellJ c s (k + 1)) := restr_notT3 hTR (hcell (k + 1) le_rfl) (hcor (k + 1) le_rfl)
  have hsame := end_same_loc hTe hk hcell hpat
  obtain ⟨fn, fb, ff⟩ := side1_facts_R hF.1 hDc hcell hpat hsep hj (fun h0 => notT3W (t0 := t0) hs0
    (hTs _ (Or.inl rfl)) (fun ht => absurd (by rw [hd, h0, cellJ_zero]; exact ht) hdR))
  rw [← hd] at fn fb ff
  have afu := alt_frame s lu1 lu2 bu fu
  -- `u` is not one of the cells beside the body.
  --
  have notside : ∀ j' ≤ k + 1, u ≠ nb (cellJ c s j') (latA s) := by
    intro j' hj' he
    have af := alt_frame s lu1 lu2 bu fu
    rw [he] at af
    by_cases hj'k : j' ≤ k
    · obtain ⟨_, fb', ff'⟩ := side1_facts_R hF.1 hDc hcell hpat hsep hj'k (fun h0 => notT3W (t0 := t0) hs0
        (hTs _ (Or.inl rfl)) (fun ht => absurd (by rw [he, h0, cellJ_zero]; exact ht) huR))
      have := af.1; rw [fb', ff'] at this; omega
    · obtain rfl : j' = k + 1 := by omega
      have fn' : lat2 (nb (cellJ c s (k + 1)) (latA s)) s ∈ F := by
        rw [side_lat2]; exact (strip_sig hpat (show k + 1 < k + 2 by omega)).1.2 (by omega)
      have fb' : back (nb (cellJ c s (k + 1)) (latA s)) s ∈ F := by
        rw [show back (nb (cellJ c s (k + 1)) (latA s)) s = outer1 (cellJ c s k) s by
          rw [← side_back_next, nb_cellJ]]
        exact (outer1_body_L hDc hpat le_rfl).2 hk
      exact (af.2.2.1 fb') (af.2.1.2 fn')
  rcases start_frame_L s hb hxl with ⟨htp, hdiff⟩ | ⟨ht, hlat, hbf⟩
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
        exact body_not_alt_L hk hpat hj lu1 lu2 bu fu
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

include hF hs0 hTR hk hcell hcor hpat hsep hT' hneut hTs hTend hb hxd hxlat hxl lu1 lu2 bu fu hxu hdu in
-- A chain strip starting beside the body (across `lat2`) runs against `s`, from an even index,
-- with the shared side on the far side.
--
theorem start_beside2_pf {j : ℕ} (hj : j ≤ k) (hd : d = nb (cellJ c s j) (latB s))
    (hdR : ¬ IsCorner t0 d) (huR : ¬ IsCorner t0 u) :
    tf = s.opp ∧ j % 2 = 0 ∧ x = lat2 d s := by
  have hDc := corners_deg2 hF hcell hcor
  have hTr := ahead_notT3 hTR hcell hcor hk
  have hcellW : ∀ j ≤ k + 1, IsCell (insert s0 (insert t0 V)) (cellJ c s j) :=
    fun j hj => isCell_mono (hcell j hj) (sub_insST V s0 t0)
  have hTrW := notT3W (t0 := t0) hs0 hTr (fun ht => absurd
    (show IsCorner t0 (cellJ c s 1) by rw [← nb_cellJ, cellJ_zero]; exact ht) (hcor 1 (by omega)).2)
  have hTe : NotTypeIII V F (cellJ c s (k + 1)) := restr_notT3 hTR (hcell (k + 1) le_rfl) (hcor (k + 1) le_rfl)
  have hsame := end_same_loc hTe hk hcell hpat
  obtain ⟨fn, fb, ff⟩ := side2_facts_R hF.1 hDc hcell hpat hsep hTrW hj (fun h0 => notT3W (t0 := t0) hs0
    (hTs _ (Or.inr rfl)) (fun ht => absurd (by rw [hd, h0, cellJ_zero]; exact ht) hdR))
  rw [← hd] at fn fb ff
  have afu := alt_frame s lu1 lu2 bu fu
  -- `u` is not one of the cells beside the body.
  --
  have notside : ∀ j' ≤ k + 1, u ≠ nb (cellJ c s j') (latB s) := by
    intro j' hj' he
    have af := alt_frame s lu1 lu2 bu fu
    rw [he] at af
    by_cases hj'k : j' ≤ k
    · obtain ⟨_, fb', ff'⟩ := side2_facts_R hF.1 hDc hcell hpat hsep hTrW hj'k (fun h0 => notT3W (t0 := t0) hs0
        (hTs _ (Or.inr rfl)) (fun ht => absurd (by rw [he, h0, cellJ_zero]; exact ht) huR))
      have := af.1; rw [fb', ff'] at this; omega
    · obtain rfl : j' = k + 1 := by omega
      have fn' : lat1 (nb (cellJ c s (k + 1)) (latB s)) s ∈ F := by
        rw [side2_lat1]; exact (strip_sig hpat (show k + 1 < k + 2 by omega)).2.1.2 (by omega)
      have fb' : back (nb (cellJ c s (k + 1)) (latB s)) s ∈ F := by
        rw [show back (nb (cellJ c s (k + 1)) (latB s)) s = outer2 (cellJ c s k) s by
          rw [outer2_side_nb_next, nb_cellJ]; rfl]
        exact (outer2_body_L hDc hpat le_rfl).2 hk
      exact (af.2.2.1 fb') fn'
  rcases start_frame_L s hb hxl with ⟨htp, hdiff⟩ | ⟨ht, hlat, hbf⟩
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
        exact body_not_alt_L hk hpat hj lu1 lu2 bu fu
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

include hF hs0 hTR hk hcell hcor hpat hsep hT' hneut hTs hTend hb hxd hxlat hxl lu1 lu2 bu fu hxu hdu in
-- A chain strip starting beside the end cell (across `lat1`) is a chain strip of the end cell
-- itself, running along or against `s` (against `s` with a dark front).
--
theorem start_beside_end1_pf (hd : d = nb (cellJ c s (k + 1)) (latA s)) (huR : ¬ IsCorner t0 u) :
    u = cellJ c s (k + 1) ∧ (tf = s ∨ (tf = s.opp ∧ front d tf ∈ F)) := by
  have hDc := corners_deg2 hF hcell hcor
  have hTr := ahead_notT3 hTR hcell hcor hk
  have hcellW : ∀ j ≤ k + 1, IsCell (insert s0 (insert t0 V)) (cellJ c s j) :=
    fun j hj => isCell_mono (hcell j hj) (sub_insST V s0 t0)
  have hTrW := notT3W (t0 := t0) hs0 hTr (fun ht => absurd
    (show IsCorner t0 (cellJ c s 1) by rw [← nb_cellJ, cellJ_zero]; exact ht) (hcor 1 (by omega)).2)
  have hTe : NotTypeIII V F (cellJ c s (k + 1)) := restr_notT3 hTR (hcell (k + 1) le_rfl) (hcor (k + 1) le_rfl)
  have hsame := end_same_loc hTe hk hcell hpat
  have fn : lat2 d s ∈ F := by
    rw [hd, side_lat2]; exact (strip_sig hpat (show k + 1 < k + 2 by omega)).1.2 (by omega)
  have fb : back d s ∈ F := by
    rw [hd, show back (nb (cellJ c s (k + 1)) (latA s)) s = outer1 (cellJ c s k) s by
      rw [← side_back_next, nb_cellJ]]
    exact (outer1_body_L hDc hpat le_rfl).2 hk
  rcases start_frame_L s hb hxl with ⟨htp, hdiff⟩ | ⟨ht, _, hbf⟩
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
    obtain ⟨_, fb', ff'⟩ := side1_facts_R hF.1 hDc hcell hpat hsep (le_refl k) (fun h0 => notT3W (t0 := t0) hs0
      (hTs _ (Or.inl rfl)) (fun ht => absurd (by rw [hu', h0, cellJ_zero]; exact ht) huR))
    have af := alt_frame s lu1 lu2 bu fu
    rw [hu'] at af
    have := af.1; rw [fb', ff'] at this; omega

include hF hs0 hTR hk hcell hcor hpat hsep hT' hneut hTs hTend hb hxd hxlat hxl lu1 lu2 bu fu hxu hdu in
theorem start_beside_end2_pf (hd : d = nb (cellJ c s (k + 1)) (latB s)) (huR : ¬ IsCorner t0 u) :
    u = cellJ c s (k + 1) ∧ (tf = s ∨ (tf = s.opp ∧ front d tf ∈ F)) := by
  have hDc := corners_deg2 hF hcell hcor
  have hTr := ahead_notT3 hTR hcell hcor hk
  have hcellW : ∀ j ≤ k + 1, IsCell (insert s0 (insert t0 V)) (cellJ c s j) :=
    fun j hj => isCell_mono (hcell j hj) (sub_insST V s0 t0)
  have hTrW := notT3W (t0 := t0) hs0 hTr (fun ht => absurd
    (show IsCorner t0 (cellJ c s 1) by rw [← nb_cellJ, cellJ_zero]; exact ht) (hcor 1 (by omega)).2)
  have hTe : NotTypeIII V F (cellJ c s (k + 1)) := restr_notT3 hTR (hcell (k + 1) le_rfl) (hcor (k + 1) le_rfl)
  have hsame := end_same_loc hTe hk hcell hpat
  have fn : lat1 d s ∈ F := by
    rw [hd, side2_lat1]; exact (strip_sig hpat (show k + 1 < k + 2 by omega)).2.1.2 (by omega)
  have fb : back d s ∈ F := by
    rw [hd, show back (nb (cellJ c s (k + 1)) (latB s)) s = outer2 (cellJ c s k) s by
      rw [outer2_side_nb_next, nb_cellJ]; rfl]
    exact (outer2_body_L hDc hpat le_rfl).2 hk
  rcases start_frame_L s hb hxl with ⟨htp, hdiff⟩ | ⟨ht, _, hbf⟩
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
    obtain ⟨_, fb', ff'⟩ := side2_facts_R hF.1 hDc hcell hpat hsep hTrW (le_refl k) (fun h0 => notT3W (t0 := t0) hs0
      (hTs _ (Or.inr rfl)) (fun ht => absurd (by rw [hu', h0, cellJ_zero]; exact ht) huR))
    have af := alt_frame s lu1 lu2 bu fu
    rw [hu'] at af
    have := af.1; rw [fb', ff'] at this; omega

include hF hs0 hds hle hTR hk hcell hcor hpat hsep hT' hneut hTs hTend hb hxd hxlat hxl hxu hdu in
-- A chain strip starting beyond the end cell runs into the end cell, or is a single cell with
-- three dark sides (both lateral sides in frame `s` and the front, shared with `u`).
--
theorem start_beyond_pf [hg : NearOK2 V t0] {m : ℕ} (hfr : front d tf ∈ F ↔ m = 1)
    (hd : d = nb (cellJ c s (k + 1)) s) (hdR : m ≠ 1 → ¬ IsCorner t0 (nb d tf))
    (hnoA : t0 ∉ V → ¬ PDang V t0 → ¬ ∃ σ L', RPathTg V (flipCol F c s (k + 2)) s0 t0 σ L') :
    (tf = s.opp ∧ front d tf ∉ F) ∨
      (m = 1 ∧ u = nb d s ∧ lat1 d s ∈ F ∧ lat2 d s ∈ F ∧ front d s ∈ F) := by
  by_cases ht0 : t0 ∈ V ∨ PDang V t0
  swap
  · have h1 : t0 ∉ V := fun h => ht0 (Or.inl h)
    have h2 : ¬ PDang V t0 := fun h => ht0 (Or.inr h)
    exact ((hg.ok.resolve_left h1).resolve_left h2) hF hs0 hds hle hTR hk hcell hcor hpat hsep hT' hneut hTs hTend
      hb hxd hxlat hxl hxu hdu hfr hd hdR h2 (hnoA h1 h2) h1
  have hDc := corners_deg2 hF hcell hcor
  have hTr := ahead_notT3 hTR hcell hcor hk
  have hcellW : ∀ j ≤ k + 1, IsCell (insert s0 (insert t0 V)) (cellJ c s j) :=
    fun j hj => isCell_mono (hcell j hj) (sub_insST V s0 t0)
  have hTrW := notT3W (t0 := t0) hs0 hTr (fun ht => absurd
    (show IsCorner t0 (cellJ c s 1) by rw [← nb_cellJ, cellJ_zero]; exact ht) (hcor 1 (by omega)).2)
  have hTe : NotTypeIII V F (cellJ c s (k + 1)) := restr_notT3 hTR (hcell (k + 1) le_rfl) (hcor (k + 1) le_rfl)
  have hsame := end_same_loc hTe hk hcell hpat
  set e := cellJ c s (k + 1)
  obtain ⟨a1, a2, _, af⟩ := strip_sig hpat (show k + 1 < k + 2 by omega)
  have l1 : lat1 e s ∈ F := a1.2 (by omega)
  have l2 : lat2 e s ∈ F := a2.2 (by omega)
  have hfe : front e s ∉ F := fun h => by have := (af.1 h).1 (by omega); omega
  have hbd : back d s ∉ F := by rw [hd, back_nb]; exact hfe
  have hce := hcell (k + 1) le_rfl
  rcases start_frame_L s hb hxl with ⟨htp, _⟩ | ⟨ht, _, hbf⟩
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
        have hd1 := hDc (k + 1) le_rfl _ (isCorner_front1 _ s)
        rw [deg_front1, ind_of_mem l1, ind_of_not_mem hfe, ← hd, ind_of_not_mem hl1] at hd1
        have ho : outer1 e s ∈ F := by by_contra ho; rw [ind_of_not_mem ho] at hd1; omega
        have hb0 := (outer1_body_L hDc hpat le_rfl).2 hk
        obtain ⟨hcL, hnot⟩ := beside_end1_pfW hF hs0 hds hk hcell hcor hpat hsep hsame hneut hb0 ho
          (end_side_far1_L hF.1 hle hTe hk hcellW hpat hb0 ho)
          (by
            intro hc
            rcases corner_besideA hc with hbk | he' | hA
            · -- PHANTOM-P2b (remaining case): `t0` is the far back corner of the square beside
              -- the end cell. The other corners are corners of the end cell (`hcor`) or of the
              -- chain strip's second cell (`hdR`). With `PDang` it is a cell of `V ∪ {t0}`
              -- with corner `t0`, which cannot be.
              --
              rcases ht0 with ht0 | hpd
              · exact ht0
              · exact absurd hc (hpd _ (beside_end1_cellT hF hs0 hb0 ho))
            · exact absurd he' (hcor (k + 1) le_rfl).2
            · exact absurd (by rw [hd]; exact hA) (hdR hm))
        exact hnot (hTend (latA s) (by simp) hcL)
    · have hb1 : lat1 d s ∈ F := by rw [← (frame_latB d s).2.1]; exact hb
      by_cases hm : m = 1
      · exact ⟨hm, hu', hb1, by rw [← (frame_latB d s).1]; exact hfr.2 hm, hfd⟩
      · exfalso
        have hl2 : lat2 d s ∉ F := by rw [← (frame_latB d s).1]; exact fun h => hm (hfr.1 h)
        have hd2 := hDc (k + 1) le_rfl _ (isCorner_front2 _ s)
        rw [deg_front2, ind_of_mem l2, ind_of_not_mem hfe, ← hd, ind_of_not_mem hl2] at hd2
        have ho : outer2 e s ∈ F := by by_contra ho; rw [ind_of_not_mem ho] at hd2; omega
        have hb0 := (outer2_body_L hDc hpat le_rfl).2 hk
        obtain ⟨hcL, hnot⟩ := beside_end2_pfW hF hs0 hds hk hcell hcor hpat hsep hsame hneut hb0 ho
          (end_side_far2_L hF.1 hle hTe hk hcellW hpat hb0 ho)
          (by
            intro hc
            rcases corner_besideB hc with hbk | he' | hA
            · -- PHANTOM-P2b (remaining case): `t0` is the far back corner of the square beside
              -- the end cell. The other corners are corners of the end cell (`hcor`) or of the
              -- chain strip's second cell (`hdR`). With `PDang` it is a cell of `V ∪ {t0}`
              -- with corner `t0`, which cannot be.
              --
              rcases ht0 with ht0 | hpd
              · exact ht0
              · exact absurd hc (hpd _ (beside_end2_cellT hF hs0 hb0 ho))
            · exact absurd he' (hcor (k + 1) le_rfl).2
            · exact absurd (by rw [hd]; exact hA) (hdR hm))
        exact hnot (hTend (latB s) (by simp) hcL)

include hF hs0 hTR hk hcell hcor hpat hsep hTs in
-- A chain strip starting beside `c_0` and running against `s`, with dark far side, joins `a`'s
-- two start classes through its second cell.
--
theorem start_L0_pf {m : ℕ} (hzs : SigFrom F (nb c (latA s)) s.opp m 1) (hm : 2 ≤ m)
    (hc1 : IsCell V (cellJ (nb c (latA s)) s.opp 1))
    (hc1R : ¬ IsCorner s0 (cellJ (nb c (latA s)) s.opp 1) ∧ ¬ IsCorner t0 (cellJ (nb c (latA s)) s.opp 1)) (hx : lat1 (nb c (latA s)) s ∈ F)
    (hXR : ¬ IsCorner t0 (nb c (latA s))) :
    False := by
  have hDc := corners_deg2 hF hcell hcor
  have hTr := ahead_notT3 hTR hcell hcor hk
  have hcellW : ∀ j ≤ k + 1, IsCell (insert s0 (insert t0 V)) (cellJ c s j) :=
    fun j hj => isCell_mono (hcell j hj) (sub_insST V s0 t0)
  have hTrW := notT3W (t0 := t0) hs0 hTr (fun ht => absurd
    (show IsCorner t0 (cellJ c s 1) by rw [← nb_cellJ, cellJ_zero]; exact ht) (hcor 1 (by omega)).2)
  have hTe : NotTypeIII V F (cellJ c s (k + 1)) := restr_notT3 hTR (hcell (k + 1) le_rfl) (hcor (k + 1) le_rfl)
  have hsame := end_same_loc hTe hk hcell hpat
  set d := nb c (latA s)
  have hc0 : IsCell V c := by have := hcell 0 (by omega); rwa [cellJ_zero] at this
  have hd0 : ∀ z, IsCorner z c → deg F z = 2 := fun z hz => hDc 0 (by omega) z (by rw [cellJ_zero]; exact hz)
  have ho := outer1_start_loc hpat (by omega) (hd0 _ (isCorner_front1 c s))
  have hbo := back_outer_light_loc hF.1 hpat (by omega) hsep (hd0 _ (isCorner_front1 c s)) (notT3W (t0 := t0) hs0 (hTs _ (Or.inl rfl)) (fun ht => absurd ht hXR))
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
      have hall := alt_corners_conn' (restr_notT3 hTR hc1 hc1R) (alt_of_lats wl1 wl2 hbw hfw)
      obtain ⟨_, a2, a3⟩ := frame_of_allConn hall s
      exact a3.symm.trans a2
    · have hbw : back w s ∈ F := gf.2 ⟨fun _ => by omega, fun _ => rfl⟩
      exact (((ends_lat2 w s).conn wl2).symm.trans ((ends_back w s).conn hbw).symm).trans
        ((ends_lat1 w s).conn wl1)
  rw [f2] at hff
  exact hsep (hff.trans hQ)

include hF hs0 hTR hk hcell hcor hpat hsep hTs in
theorem start_R0_pf {m : ℕ} (hzs : SigFrom F (nb c (latB s)) s.opp m 1) (hm : 2 ≤ m)
    (hc1 : IsCell V (cellJ (nb c (latB s)) s.opp 1))
    (hc1R : ¬ IsCorner s0 (cellJ (nb c (latB s)) s.opp 1) ∧ ¬ IsCorner t0 (cellJ (nb c (latB s)) s.opp 1)) (hx : lat2 (nb c (latB s)) s ∈ F)
    (hXR : ¬ IsCorner t0 (nb c (latB s))) :
    False := by
  have hDc := corners_deg2 hF hcell hcor
  have hTr := ahead_notT3 hTR hcell hcor hk
  have hcellW : ∀ j ≤ k + 1, IsCell (insert s0 (insert t0 V)) (cellJ c s j) :=
    fun j hj => isCell_mono (hcell j hj) (sub_insST V s0 t0)
  have hTrW := notT3W (t0 := t0) hs0 hTr (fun ht => absurd
    (show IsCorner t0 (cellJ c s 1) by rw [← nb_cellJ, cellJ_zero]; exact ht) (hcor 1 (by omega)).2)
  have hTe : NotTypeIII V F (cellJ c s (k + 1)) := restr_notT3 hTR (hcell (k + 1) le_rfl) (hcor (k + 1) le_rfl)
  have hsame := end_same_loc hTe hk hcell hpat
  set d := nb c (latB s)
  have hc0 : IsCell V c := by have := hcell 0 (by omega); rwa [cellJ_zero] at this

  have hd0 : ∀ z, IsCorner z c → deg F z = 2 := fun z hz => hDc 0 (by omega) z (by rw [cellJ_zero]; exact hz)
  have hbo := back_outer2_light_loc hF.1 hpat (by omega) (isCell_mono hc0 (sub_insST V s0 t0)) hsep (hd0 _ (isCorner_front1 c s)) (hd0 _ (isCorner_front2 c s)) hTrW (notT3W (t0 := t0) hs0 (hTs _ (Or.inr rfl)) (fun ht => absurd ht hXR))
  have hfj := front_join_loc hF.1 hpat (by omega) (isCell_mono hc0 (sub_insST V s0 t0)) (hd0 _ (isCorner_front1 c s)) (hd0 _ (isCorner_front2 c s)) hTrW
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
    have hd := hd0 _ (isCorner_front2 c s)
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
      have hall := alt_corners_conn' (restr_notT3 hTR hc1 hc1R) (alt_of_lats wl1 wl2 hbw hfw)
      obtain ⟨_, a2, a3⟩ := frame_of_allConn hall s
      exact a2.symm.trans a3
    · have hbw : back w s ∈ F := gf.2 ⟨fun _ => by omega, fun _ => rfl⟩
      exact (((ends_lat1 w s).conn wl1).symm.trans ((ends_back w s).conn hbw)).trans
        ((ends_lat2 w s).conn wl2)
  rw [f1] at hff
  exact hsep (((ends_back c s).conn hpat.1).trans (hff.trans hQ))

end chainstart

-- **`single3_link` for path-factors**: degree at most 2 and the cell `u` not Type III.
--
theorem single3_link_pf {V : Finset Pt} {G : Finset Edge} {c : Pt} {s : Side} {k : ℕ}
    (hle : ∀ z, deg G z ≤ 2) (hk : k % 2 = 0)
    (hcell : ∀ j ≤ k + 1, IsCell V (cellJ c s j)) (hpat : StripPat G c s (k + 2))
    (hd1 : lat1 (cellJ c s (k + 2)) s ∈ G) (hd2 : lat2 (cellJ c s (k + 2)) s ∈ G)
    (hdf : front (cellJ c s (k + 2)) s ∈ G) (hcu : IsCell V (cellJ c s (k + 3)))
    {tu : Side} (lu1 : lat1 (cellJ c s (k + 3)) tu ∈ G) (lu2 : lat2 (cellJ c s (k + 3)) tu ∈ G)
    (bu : back (cellJ c s (k + 3)) tu ∉ G) (fu : front (cellJ c s (k + 3)) tu ∉ G)
    (hcd : IsCell V (cellJ c s (k + 2))) (hTu : NotTypeIII V G (cellJ c s (k + 3))) :
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
  · exact (frame_of_allConn (alt_corners_conn' hTu (alt_of_lats lu1 lu2 bu fu)) s).2.1
  · rw [endCell_mk2]
    intro h
    -- In `flip G e`, the cell `d` has four dark sides.
    --
    have hle' : ∀ z, deg (flip G e) z ≤ 2 := by
      intro z
      rw [(mkLat e s).flip_eq (mkLat_cellE e s) el1 el2 eb ef, (mkLat e s).deg_res el1 el2 eb ef]
      exact hle z
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
    have := four_sides_class_le hle' hcd s f3 f4 f1 f2 h'
    rw [← hdu] at this
    exact front1_not_corner d s this


end HP

end ULHC
