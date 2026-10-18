/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
import SolidGridHam.Cycle.Reverse
import SolidGridHam.Cycle.ChainLinks

/-!
# Completeness, part 1: Type III cells after an even strip are links

For a proper even strip `a = (c, s, k + 2)` of a Type III-free factor `F` whose flip has a Type
III cell, some single cell is a `CR2` link from `a` (`t3_link`):
* a Type III cell sharing no side with `a` keeps its sides; it is not Type III in `F`, and the
  end cell's flip already splits it (`far_link`);
* otherwise it sits beside or beyond the end cell, which forces a dark outer edge at the end
  cell's front; then the cell beside the end cell is a link (`end_side_link1/2`);
* the other cells touching `a` are never Type III after the flip.
-/

namespace SolidGridHam

open Finset

lemma single_pat {F : Finset Edge} {d : Pt} {tf : Side} (hb : back d tf ∈ F) (hl1 : lat1 d tf ∉ F)
    (hl2 : lat2 d tf ∉ F) (hf : front d tf ∈ F) : StripPat F d tf 1 := by
  refine ⟨hb, fun j hj => ?_, fun j hj => ?_⟩
  · obtain rfl : j = 0 := by omega
    rw [cellJ_zero]; simp [hl1, hl2]
  · obtain rfl : j = 0 := by omega
    rw [cellJ_zero]; simp [hf]

-- An alternating cell with dark back and front, read in any frame.
--
lemma alt_frame2 {F : Finset Edge} {w : Pt} {tw : Side} (s : Side)
    (bw : back w tw ∈ F) (fw : front w tw ∈ F) (l1 : lat1 w tw ∉ F) (l2 : lat2 w tw ∉ F) :
    (back w s ∈ F ↔ front w s ∈ F) ∧ (lat1 w s ∈ F ↔ lat2 w s ∈ F) ∧
      (back w s ∈ F ↔ lat1 w s ∉ F) := by
  rcases side_cases s tw with h | h | h | h <;> subst h
  · tauto
  · obtain ⟨f1, f2, fb, ff⟩ := frame_opp w s
    rw [f1] at l1; rw [f2] at l2; rw [fb] at bw; rw [ff] at fw
    tauto
  · obtain ⟨ff, fb, fl⟩ := frame_latA w s
    rw [ff] at fw; rw [fb] at bw
    rcases fl with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1] at l1 <;> rw [h2] at l2 <;> tauto
  · obtain ⟨ff, fb, fl⟩ := frame_latB w s
    rw [ff] at fw; rw [fb] at bw
    rcases fl with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1] at l1 <;> rw [h2] at l2 <;> tauto

lemma front1_nb_opp (c : Pt) (s : Side) : front1 (nb c s.opp) s = back1 c s := by
  obtain ⟨x, y⟩ := c; cases s <;> simp [front1, back1, nb, Side.opp]

lemma front2_nb_opp (c : Pt) (s : Side) : front2 (nb c s.opp) s = back2 c s := by
  obtain ⟨x, y⟩ := c; cases s <;> simp [front2, back2, nb, Side.opp]

lemma behind_lat1_not_mem (c : Pt) (s : Side) (j : ℕ) :
    lat1 (nb c s.opp) s ∉ cellE (cellJ c s j) := by
  obtain ⟨x, y⟩ := c; cases s <;> simp [cellE, lat1, nb, cellJ, Side.opp, bot, top, lft, rgt] <;> omega

lemma behind_lat2_not_mem (c : Pt) (s : Side) (j : ℕ) :
    lat2 (nb c s.opp) s ∉ cellE (cellJ c s j) := by
  obtain ⟨x, y⟩ := c; cases s <;> simp [cellE, lat2, nb, cellJ, Side.opp, bot, top, lft, rgt] <;> omega

lemma nbA_ne (d : Pt) (s : Side) : nb d (latA s) ≠ d := by
  obtain ⟨x, y⟩ := d; cases s <;> simp [nb, latA]

lemma nbB_ne (d : Pt) (s : Side) : nb d (latB s) ≠ d := by
  obtain ⟨x, y⟩ := d; cases s <;> simp [nb, latB]

lemma endCell_mk (c : Pt) (s : Side) (k : ℕ) : endCell ⟨c, s, k + 2⟩ = cellJ c s (k + 1) := rfl

-- Single cells beside the end cell, or sharing no side with it, are chain-compatible.
--
lemma chainOK_besideA (c : Pt) (s : Side) (k : ℕ) :
    ChainOK ⟨c, s, k + 2⟩ ⟨nb (cellJ c s (k + 1)) (latA s), s, 1⟩ := by
  intro j hj z hz hze
  simp only at hj
  obtain rfl : j = 0 := by omega
  rw [cellJ_zero] at hz
  rw [endCell_mk] at hze ⊢
  refine ⟨rfl, Or.inl ?_⟩
  rw [shared_unique rfl hze hz, lat1_eq]

lemma chainOK_besideB (c : Pt) (s : Side) (k : ℕ) :
    ChainOK ⟨c, s, k + 2⟩ ⟨nb (cellJ c s (k + 1)) (latB s), s, 1⟩ := by
  intro j hj z hz hze
  simp only at hj
  obtain rfl : j = 0 := by omega
  rw [cellJ_zero] at hz
  rw [endCell_mk] at hze ⊢
  refine ⟨rfl, Or.inr ?_⟩
  rw [shared_unique rfl hze hz, lat2_eq]

lemma chainOK_far {b τ : StripSpec}
    (h : ∀ j < τ.n, ∀ x ∈ cellE (cellJ τ.c τ.s j), x ∉ cellE (endCell b)) : ChainOK b τ :=
  chainOK_of_noChain h

lemma back_side0_not_mem (c : Pt) (s : Side) (i : ℕ) :
    back (nb c (latA s)) s ∉ cellE (cellJ c s i) := by
  obtain ⟨x, y⟩ := c; cases s <;> simp [cellE, back, nb, latA, cellJ, sideEdge, Side.opp, bot, top, lft, rgt]

lemma back_side0_not_mem2 (c : Pt) (s : Side) (i : ℕ) :
    back (nb c (latB s)) s ∉ cellE (cellJ c s i) := by
  obtain ⟨x, y⟩ := c; cases s <;> simp [cellE, back, nb, latB, cellJ, sideEdge, Side.opp, bot, top, lft, rgt]

section t3

variable {V : Finset Pt} {F : Finset Edge} {c : Pt} {s : Side} {k : ℕ}
  (hF : Deg2 V F) (hT : NoTypeIII V F) (hk : k % 2 = 0)
  (hcell : ∀ j ≤ k + 1, IsCell V (cellJ c s j)) (hpat : StripPat F c s (k + 2))
  (hsep : ¬ Conn F (back1 c s) (front1 c s))
include hF hT hk hcell hpat hsep

-- The end cell's own flip separates its `lat1` corners.
--
lemma end_flip_sep : ¬ Conn (flip F (cellJ c s (k + 1))) (back1 (cellJ c s (k + 1)) s)
    (front1 (cellJ c s (k + 1)) s) := by
  obtain ⟨F1, hF1, _, hab, _⟩ := strip_even_rel k hk F hF hcell hpat hsep (end_same hT hk hcell hpat)
  rw [← hF1]; exact hab

theorem end_side_link1 (hf : outer1 (cellJ c s (k + 1)) s ∈ F) :
    CR2 V F ⟨c, s, k + 2⟩ ⟨nb (cellJ c s (k + 1)) (latA s), s, 1⟩ := by
  set e := cellJ c s (k + 1)
  set L := nb e (latA s)
  have hb0 := (outer1_body hF hcell hpat le_rfl).2 hk
  have hbL : back L s = outer1 (cellJ c s k) s := by rw [← side_back_next, nb_cellJ]
  have hfL : front L s = outer1 e s := side_front e s
  have hfar := end_side_far1 hF hT hk hcell hpat hb0 hf
  have hl1e : lat1 e s ∈ F := (strip_sig hpat (show k + 1 < k + 2 by omega)).1.2 (by omega)
  have offL : ∀ i ≤ k + 1, back L s ∉ cellE (cellJ c s i) ∧ front L s ∉ cellE (cellJ c s i) ∧
      lat1 L s ∉ cellE (cellJ c s i) := fun i _ =>
    ⟨by rw [hbL]; exact outer1_not_mem c s k i, by rw [hfL]; exact outer1_not_mem c s (k + 1) i,
      side_lat1_not_mem c s (k + 1) i⟩
  have hV1 := (side_back_ends e s).inV (hF.1 _ (hbL ▸ hb0))
  have hV2 := (side_front_ends e s).inV (hF.1 _ hf)
  have hcL : IsCell V L := by
    refine isCell_of_corners L s hV1.1 ?_ hV2.1 ?_
    · rw [side_back2]; exact hV1.2
    · rw [side_front2]; exact hV2.2
  have hmemL : ∀ y ∈ cellE L, y = back L s ∨ y = front L s ∨ y = lat1 L s ∨ y = lat2 L s := by
    intro y hy; rw [cellE_frame L s] at hy; simpa using hy
  have hmid : ∀ p (x : Edge), x ∈ F → (x.p = p ∨ x.q = p) →
      (∀ i ≤ k + 1, x ∉ cellE (cellJ c s i)) → ¬ IsMid c s k p := fun p x hx hxp hoff hm => by
    obtain ⟨i, hi, hxi⟩ := mid_touch hF hpat hcell hm hx hxp
    exact hoff i (by omega) hxi
  unfold CR2
  dsimp only
  refine ⟨by omega, by omega, le_rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [endCell_mk]
    refine single_pat ?_ ?_ ?_ ?_
    · rw [mem_flip_off (offL (k + 1) le_rfl).1]; rw [hbL]; exact hb0
    · rw [mem_flip_off (offL (k + 1) le_rfl).2.2]; exact hfar
    · rw [side_lat2, mem_flip_iff]
      intro h; exact (h.1 hl1e) (by rw [cellE_frame e s]; simp)
    · rw [mem_flip_off (offL (k + 1) le_rfl).2.1, hfL]; exact hf
  · intro j hj; obtain rfl : j = 0 := by omega
    rw [cellJ_zero]; exact hcL
  · intro j hj i hi y hy
    simp only at hj hi
    obtain rfl : j = 0 := by omega
    rw [cellJ_zero] at hy
    rcases hmemL y hy with rfl | rfl | rfl | rfl
    · exact (offL i (by omega)).1
    · exact (offL i (by omega)).2.1
    · exact (offL i (by omega)).2.2
    · rw [side_lat2]; exact lat1_not_mem c s (by omega)
  · intro j hj; obtain rfl : j = 0 := by omega
    rw [cellJ_zero, endCell_mk]; exact nbA_ne e s
  · intro h; simp at h
  · show ¬ IsMid c s (k + 2 - 2) _
    rw [show k + 2 - 2 = k by omega]
    exact hmid _ _ (hbL ▸ hb0) ((ends_back L s).inc_iff _ |>.2 (Or.inl rfl))
      (fun i hi => (offL i hi).1)
  · show ¬ IsMid c s (k + 2 - 2) _
    rw [show k + 2 - 2 = k by omega]
    exact hmid _ _ (hfL ▸ hf) ((ends_front L s).inc_iff _ |>.2 (Or.inl rfl))
      (fun i hi => (offL i hi).2.1)
  · have e1 := side_back_ends e s
    have e2 := side_front_ends e s
    rw [← hbL] at hb0
    exact ((e1.conn hb0).trans ((ends_lat1 e s).conn hl1e)).trans (e2.conn hf).symm
  · rw [endCell_mk]
    intro h
    have e1 := side_back_ends e s
    have e2 := side_front_ends e s
    have hb' : back L s ∈ flip F e := by rw [mem_flip_off (offL (k + 1) le_rfl).1, hbL]; exact hb0
    have hf' : outer1 e s ∈ flip F e := by rw [← hfL, mem_flip_off (offL (k + 1) le_rfl).2.1, hfL]; exact hf
    exact end_flip_sep hF hT hk hcell hpat hsep
      (((e1.conn hb').symm.trans h).trans (e2.conn hf'))

theorem end_side_link2 (hf : outer2 (cellJ c s (k + 1)) s ∈ F) :
    CR2 V F ⟨c, s, k + 2⟩ ⟨nb (cellJ c s (k + 1)) (latB s), s, 1⟩ := by
  set e := cellJ c s (k + 1)
  set L := nb e (latB s)
  have hb0 := (outer2_body hF hcell hpat le_rfl).2 hk
  have hbL : back L s = outer2 (cellJ c s k) s := by rw [outer2_side_nb_next, nb_cellJ]; rfl
  have hfL : front L s = outer2 e s := side2_front e s
  have hfar := end_side_far2 hF hT hk hcell hpat hb0 hf
  have hl2e : lat2 e s ∈ F := (strip_sig hpat (show k + 1 < k + 2 by omega)).2.1.2 (by omega)
  have offL : ∀ i ≤ k + 1, back L s ∉ cellE (cellJ c s i) ∧ front L s ∉ cellE (cellJ c s i) ∧
      lat2 L s ∉ cellE (cellJ c s i) := fun i _ =>
    ⟨by rw [hbL]; exact outer2_not_mem c s k i, by rw [hfL]; exact outer2_not_mem c s (k + 1) i,
      side2_lat2_not_mem c s (k + 1) i⟩
  have hV1 := (side2_back_ends e s).inV (hF.1 _ (hbL ▸ hb0))
  have hV2 := (side2_front_ends e s).inV (hF.1 _ hf)
  have hcL : IsCell V L := by
    refine isCell_of_corners L s ?_ hV1.2 ?_ hV2.2
    · rw [side2_back1]; exact hV1.1
    · rw [side2_front1]; exact hV2.1
  have hmemL : ∀ y ∈ cellE L, y = back L s ∨ y = front L s ∨ y = lat1 L s ∨ y = lat2 L s := by
    intro y hy; rw [cellE_frame L s] at hy; simpa using hy
  have hmid : ∀ p (x : Edge), x ∈ F → (x.p = p ∨ x.q = p) →
      (∀ i ≤ k + 1, x ∉ cellE (cellJ c s i)) → ¬ IsMid c s k p := fun p x hx hxp hoff hm => by
    obtain ⟨i, hi, hxi⟩ := mid_touch hF hpat hcell hm hx hxp
    exact hoff i (by omega) hxi
  unfold CR2
  dsimp only
  refine ⟨by omega, by omega, le_rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [endCell_mk]
    refine single_pat ?_ ?_ ?_ ?_
    · rw [mem_flip_off (offL (k + 1) le_rfl).1]; rw [hbL]; exact hb0
    · rw [side2_lat1, mem_flip_iff]
      intro h; exact (h.1 hl2e) (by rw [cellE_frame e s]; simp)
    · rw [mem_flip_off (offL (k + 1) le_rfl).2.2]; exact hfar
    · rw [mem_flip_off (offL (k + 1) le_rfl).2.1, hfL]; exact hf
  · intro j hj; obtain rfl : j = 0 := by omega
    rw [cellJ_zero]; exact hcL
  · intro j hj i hi y hy
    simp only at hj hi
    obtain rfl : j = 0 := by omega
    rw [cellJ_zero] at hy
    rcases hmemL y hy with rfl | rfl | rfl | rfl
    · exact (offL i (by omega)).1
    · exact (offL i (by omega)).2.1
    · rw [side2_lat1]; exact lat2_not_mem c s (by omega)
    · exact (offL i (by omega)).2.2
  · intro j hj; obtain rfl : j = 0 := by omega
    rw [cellJ_zero, endCell_mk]; exact nbB_ne e s
  · intro h; simp at h
  · show ¬ IsMid c s (k + 2 - 2) _
    rw [show k + 2 - 2 = k by omega]
    exact hmid _ _ (hbL ▸ hb0) ((ends_back L s).inc_iff _ |>.2 (Or.inl rfl))
      (fun i hi => (offL i hi).1)
  · show ¬ IsMid c s (k + 2 - 2) _
    rw [show k + 2 - 2 = k by omega]
    exact hmid _ _ (hfL ▸ hf) ((ends_front L s).inc_iff _ |>.2 (Or.inl rfl))
      (fun i hi => (offL i hi).2.1)
  · rw [side2_back1, side2_front1]; exact (ends_lat2 e s).conn hl2e
  · rw [endCell_mk, side2_back1, side2_front1]
    intro h
    have hbe : back e s ∈ flip F e := by
      rw [mem_flip_iff]
      have : back e s ∉ F := fun h' => by
        have := (strip_sig hpat (show k + 1 < k + 2 by omega)).2.2.1.1 h'; omega
      exact ⟨fun h' => absurd h' this, fun hn => absurd (by rw [cellE_frame e s]; simp) hn⟩
    have hfe : front e s ∈ flip F e := by
      rw [mem_flip_iff]
      have : front e s ∉ F := fun h' => by
        have := ((strip_sig hpat (show k + 1 < k + 2 by omega)).2.2.2.1 h').1 (by omega); omega
      exact ⟨fun h' => absurd h' this, fun hn => absurd (by rw [cellE_frame e s]; simp) hn⟩
    exact end_flip_sep hF hT hk hcell hpat hsep
      ((((ends_back e s).conn hbe).trans h).trans ((ends_front e s).conn hfe).symm)

-- A Type III cell of the flipped factor that shares no side with the strip is a link.
--
theorem far_link {d : Pt} {tf : Side} (hd : IsCell V d)
    (hb : back d tf ∈ flipCol F c s (k + 2)) (hf : front d tf ∈ flipCol F c s (k + 2))
    (hl1 : lat1 d tf ∉ flipCol F c s (k + 2)) (hl2 : lat2 d tf ∉ flipCol F c s (k + 2))
    (hn : ¬ Conn (flipCol F c s (k + 2)) (back1 d tf) (front1 d tf))
    (hfar : ∀ j < k + 2, ∀ x ∈ cellE d, x ∉ cellE (cellJ c s j)) :
    CR2 V F ⟨c, s, k + 2⟩ ⟨d, tf, 1⟩ := by
  have hsame : ∀ x ∈ cellE d, (x ∈ flipCol F c s (k + 2) ↔ x ∈ F) := fun x hx =>
    mem_flipCol_out (fun j hj => hfar j hj x hx)
  have hfl : ∀ x ∈ cellE d, (x ∈ flip F (cellJ c s (k + 1)) ↔ x ∈ F) := fun x hx =>
    mem_flip_off (hfar (k + 1) (by omega) x hx)
  have mem : ∀ x, x = back d tf ∨ x = front d tf ∨ x = lat1 d tf ∨ x = lat2 d tf → x ∈ cellE d := by
    intro x hx; rw [cellE_frame d tf]; rcases hx with rfl | rfl | rfl | rfl <;> simp
  have bF := (hsame _ (mem _ (Or.inl rfl))).1 hb
  have fF := (hsame _ (mem _ (Or.inr (Or.inl rfl)))).1 hf
  have l1F : lat1 d tf ∉ F := fun h => hl1 ((hsame _ (mem _ (Or.inr (Or.inr (Or.inl rfl))))).2 h)
  have l2F : lat2 d tf ∉ F := fun h => hl2 ((hsame _ (mem _ (Or.inr (Or.inr (Or.inr rfl))))).2 h)
  have hm1 : ¬ IsMid c s k (back1 d tf) := fun hm => by
    obtain ⟨i, hi, hxi⟩ := mid_touch hF hpat hcell hm bF ((ends_back d tf).inc_iff _ |>.2 (Or.inl rfl))
    exact hfar i hi _ (mem _ (Or.inl rfl)) hxi
  have hm2 : ¬ IsMid c s k (front1 d tf) := fun hm => by
    obtain ⟨i, hi, hxi⟩ := mid_touch hF hpat hcell hm fF ((ends_front d tf).inc_iff _ |>.2 (Or.inl rfl))
    exact hfar i hi _ (mem _ (Or.inr (Or.inl rfl))) hxi
  obtain ⟨F1, hF1, _, _, _, _, hodd⟩ :=
    strip_even_rel k hk F hF hcell hpat hsep (end_same hT hk hcell hpat)
  unfold CR2
  dsimp only
  refine ⟨by omega, by omega, le_rfl, ?_, fun j hj => ?_, fun j hj i hi x hx => ?_, fun j hj => ?_,
    fun h => by simp at h, by rw [show k + 2 - 2 = k by omega]; exact hm1,
    by rw [show k + 2 - 2 = k by omega]; exact hm2, hT d hd tf bF fF l1F l2F, ?_⟩
  · rw [endCell_mk]
    exact single_pat ((hfl _ (mem _ (Or.inl rfl))).2 bF)
      (fun h => l1F ((hfl _ (mem _ (Or.inr (Or.inr (Or.inl rfl))))).1 h))
      (fun h => l2F ((hfl _ (mem _ (Or.inr (Or.inr (Or.inr rfl))))).1 h))
      ((hfl _ (mem _ (Or.inr (Or.inl rfl)))).2 fF)
  · obtain rfl : j = 0 := by omega
    rw [cellJ_zero]; exact hd
  · simp only at hj hi
    obtain rfl : j = 0 := by omega
    rw [cellJ_zero] at hx
    exact hfar i (by omega) x hx
  · obtain rfl : j = 0 := by omega
    rw [cellJ_zero, endCell_mk]
    intro h
    exact hfar (k + 1) (by omega) _ (mem _ (Or.inl rfl)) (by rw [← h]; exact mem _ (Or.inl rfl))
  · rw [endCell_mk]
    intro h
    exact hn ((hodd _ _ hm1 hm2).2 (Or.inl (hF1 ▸ h)))

-- **Type III after an even strip.** Some single cell is then a link from the strip.
--
theorem t3_link (h3 : ¬ NoTypeIII V (flipCol F c s (k + 2))) :
    ∃ τ : StripSpec, τ.n = 1 ∧ CR2 V F ⟨c, s, k + 2⟩ τ ∧ ChainOK ⟨c, s, k + 2⟩ τ := by
  set F' := flipCol F c s (k + 2)
  unfold NoTypeIII at h3
  push Not at h3
  obtain ⟨d, hd, tf, hb, hf, hl1, hl2, hn⟩ := h3
  by_cases hfar : ∀ j < k + 2, ∀ x ∈ cellE d, x ∉ cellE (cellJ c s j)
  · refine ⟨_, rfl, far_link hF hT hk hcell hpat hsep hd hb hf hl1 hl2 hn hfar,
      chainOK_far fun j hj x hx hxe => ?_⟩
    simp only at hj
    obtain rfl : j = 0 := by omega
    rw [cellJ_zero] at hx
    exact hfar (k + 1) (by omega) x hx hxe
  push Not at hfar
  obtain ⟨j, hj, x, hx, hxj⟩ := hfar
  have alt := alt_frame2 s hb hf hl1 hl2
  have hc0 : IsCell V c := by have := hcell 0 (by omega); rwa [cellJ_zero] at this
  -- `d` is not a cell of the strip.
  --
  have body : ∀ j' ≤ k + 1, d ≠ cellJ c s j' := by
    intro j' hj' hdj
    rw [hdj] at alt hn hb hf hl1 hl2
    rcases j' with _ | j'
    · rw [cellJ_zero] at alt hn hb hf hl1 hl2
      exact hn (start_notTypeIII hF hT hk hcell hpat hsep tf hb hf hl1 hl2)
    · by_cases hjk : j' + 1 ≤ k
      · have := alt.1
        rw [back_after_j hk hpat (by omega) (by omega), front_after hk hpat hjk] at this
        omega
      · obtain rfl : j' = k := by omega
        have := alt.1
        rw [back_after_j hk hpat (by omega) le_rfl] at this
        have := this.2 (front_end_after hk hpat); omega
  -- From a dark outer edge at the end cell's front, a link beside the end cell.
  --
  have ldeg : lat1 (nb (cellJ c s (k + 1)) s) s ∉ F → outer1 (cellJ c s (k + 1)) s ∈ F := by
    intro hu
    have l1 := (strip_sig hpat (show k + 1 < k + 2 by omega)).1.2 (by omega)
    have hfe : front (cellJ c s (k + 1)) s ∉ F := fun h => by
      have := ((strip_sig hpat (show k + 1 < k + 2 by omega)).2.2.2.1 h).1 (by omega); omega
    have hd := hF.2 _ (corners4 (hcell (k + 1) le_rfl) s).2.2.1
    rw [deg_front1, ind_of_mem l1, ind_of_not_mem hfe, ind_of_not_mem hu] at hd
    by_contra ho; rw [ind_of_not_mem ho] at hd; omega
  rcases touch_cases s hx hxj with hq | hq | hq | hq | hq
  · exact absurd hq (body j (by omega))
  · by_cases hjk : j ≤ k
    · exact absurd (by rw [hq, nb_cellJ]) (body (j + 1) (by omega))
    · obtain rfl : j = k + 1 := by omega
      rw [hq] at alt
      have hbu : back (nb (cellJ c s (k + 1)) s) s ∈ F' := by
        rw [back_nb]; exact front_end_after hk hpat
      have hlu : lat1 (nb (cellJ c s (k + 1)) s) s ∉ F' := alt.2.2.1 hbu
      have hlu' : lat1 (nb (cellJ c s (k + 1)) s) s ∉ F := by
        rw [nb_cellJ] at hlu ⊢
        rwa [mem_flipCol_out (fun i hi => lat1_not_mem c s (by omega))] at hlu
      exact ⟨_, rfl, end_side_link1 hF hT hk hcell hpat hsep (ldeg hlu'), chainOK_besideA c s k⟩
  · rcases j with _ | j
    · exfalso
      rw [cellJ_zero] at hq
      rw [hq] at alt hn hb hf hl1 hl2
      have d1 := back_down hF hT hpat (by omega) hc0 hsep
      have d2 := back_down2 hF hT hpat (by omega) hc0 hsep
      have d1' : lat1 (nb c s.opp) s ∈ F' := by
        rw [show cellJ c s 0 = c from cellJ_zero c s] at *
        rw [mem_flipCol_out (fun i _ => behind_lat1_not_mem c s i)]; exact d1
      have d2' : lat2 (nb c s.opp) s ∈ F' := by
        rw [mem_flipCol_out (fun i _ => behind_lat2_not_mem c s i)]; exact d2
      have hbB : back (nb c s.opp) s ∉ F' := fun h => (alt.2.2.1 h) d1'
      -- `c` is alternating after the flip and not Type III, so its corners are joined.
      --
      have l1c : lat1 c s ∈ F' := by
        have := (lat1_after hk hpat (j := 0) (by omega)).2 rfl; rwa [cellJ_zero] at this
      have l2c : lat2 c s ∈ F' := by
        have := (lat2_after hk hpat (j := 0) (by omega)).2 rfl; rwa [cellJ_zero] at this
      have fc : front c s ∉ F' := fun h => by
        have := (front_after hk hpat (j := 0) (by omega)).1 (by rw [cellJ_zero]; exact h); omega
      have hac : Alt F' c := alt_of_lats l1c l2c (back_after hk hpat) fc
      have hcc : AllConn F' c := alt_corners_conn' (start_notTypeIII hF hT hk hcell hpat hsep) hac
      have hbb := (frame_of_allConn hcc s).1
      have e1 := ends_lat1 (nb c s.opp) s
      have e2 := ends_lat2 (nb c s.opp) s
      rw [front1_nb_opp] at e1; rw [front2_nb_opp] at e2
      have h2 : Conn F' (back1 (nb c s.opp) s) (back1 c s) := e1.conn d1'
      have h3 : Conn F' (back1 (nb c s.opp) s) (back2 c s) := h2.trans hbb
      have h1 : Conn F' (back1 (nb c s.opp) s) (back2 (nb c s.opp) s) := h3.trans (e2.conn d2').symm
      have hall : AllConn F' (nb c s.opp) := allConn_of_frame s h1
        (by rw [front1_nb_opp]; exact h2) (by rw [front2_nb_opp]; exact h3)
      exact hn (notTypeIII_of_allConn (V := V) hall tf hb hf hl1 hl2)
    · exact absurd (by rw [hq, cellJ_down]) (body j (by omega))
  · by_cases hjk : j ≤ k
    · exfalso
      obtain ⟨_, fb, ff⟩ := side1_facts hF hT hk hcell hpat hsep hjk
      rw [hq] at alt
      have fb' : back (nb (cellJ c s j) (latA s)) s ∈ F' ↔ j % 2 = 1 := by
        rcases j with _ | j
        · rw [mem_flipCol_out (fun i _ => by rw [cellJ_zero]; exact back_side0_not_mem c s i)]
          exact fb
        · rw [← nb_cellJ, side_back_next, mem_flipCol_out (fun i _ => outer1_not_mem c s j i)]
          rw [← nb_cellJ, side_back_next] at fb; exact fb
      have ff' : front (nb (cellJ c s j) (latA s)) s ∈ F' ↔ j % 2 = 0 := by
        rw [side_front, mem_flipCol_out (fun i _ => outer1_not_mem c s j i), ← side_front]
        exact ff
      have := alt.1; rw [fb', ff'] at this; omega
    · obtain rfl : j = k + 1 := by omega
      rw [hq] at alt
      have hn' : lat2 (nb (cellJ c s (k + 1)) (latA s)) s ∉ F' := by
        rw [side_lat2, lat1_after hk hpat le_rfl]; omega
      have hl1' : lat1 (nb (cellJ c s (k + 1)) (latA s)) s ∉ F' := fun h => hn' (alt.2.1.1 h)
      have hbk := (alt.2.2).2 hl1'
      have hfr := alt.1.1 hbk
      rw [side_front, mem_flipCol_out (fun i _ => outer1_not_mem c s (k + 1) i)] at hfr
      exact ⟨_, rfl, end_side_link1 hF hT hk hcell hpat hsep hfr, chainOK_besideA c s k⟩
  · by_cases hjk : j ≤ k
    · exfalso
      obtain ⟨_, fb, ff⟩ := side2_facts hF hT hk hcell hpat hsep hjk
      rw [hq] at alt
      have fb' : back (nb (cellJ c s j) (latB s)) s ∈ F' ↔ j % 2 = 1 := by
        rcases j with _ | j
        · rw [mem_flipCol_out (fun i _ => by rw [cellJ_zero]; exact back_side0_not_mem2 c s i)]
          exact fb
        · have hbo : back (nb (cellJ c s (j + 1)) (latB s)) s = outer2 (cellJ c s j) s := by
            rw [outer2_side_nb_next, nb_cellJ]; rfl
          rw [hbo, mem_flipCol_out (fun i _ => outer2_not_mem c s j i)]
          rw [hbo] at fb; exact fb
      have ff' : front (nb (cellJ c s j) (latB s)) s ∈ F' ↔ j % 2 = 0 := by
        rw [side2_front, mem_flipCol_out (fun i _ => outer2_not_mem c s j i), ← side2_front]
        exact ff
      have := alt.1; rw [fb', ff'] at this; omega
    · obtain rfl : j = k + 1 := by omega
      rw [hq] at alt
      have hn' : lat1 (nb (cellJ c s (k + 1)) (latB s)) s ∉ F' := by
        rw [side2_lat1, lat2_after hk hpat le_rfl]; omega
      have hbk := (alt.2.2).2 hn'
      have hfr := alt.1.1 hbk
      rw [side2_front, mem_flipCol_out (fun i _ => outer2_not_mem c s (k + 1) i)] at hfr
      exact ⟨_, rfl, end_side_link2 hF hT hk hcell hpat hsep hfr, chainOK_besideB c s k⟩

end t3

end SolidGridHam
