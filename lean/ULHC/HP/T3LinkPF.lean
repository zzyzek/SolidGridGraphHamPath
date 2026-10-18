/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
import ULHC.HP.CompCleanTg

/-!
# `t3_link` for path-factors

ULHC `t3_link`: after an even strip, a Type III cell gives a one-cell link. For path-factors
with a count-neutral restricted strip, a restricted Type III cell `d` of `F ⊕ σ` gives a
restricted one-cell link, given E2 (the cells beside `σ`'s start are not Type III in `F`) and,
when `d` is the cell beyond `σ`'s end, that the cell beside the end cell across `latA` is
restricted (it is the link then).
-/

namespace ULHC

namespace HP

open Finset Classical

section t3pf

variable {V : Finset Pt} {F : Finset Edge} {c : Pt} {s : Side} {k : ℕ} {s0 t0 : Pt}
  (hF : Deg2Off V F s0 t0) (hs0 : s0 ∈ V) (hds : deg F s0 = 1) (hle : ∀ z, deg F z ≤ 2)
  (hTR : NoTypeIIIR V F s0 t0) (hk : k % 2 = 0)
  (hcell : ∀ j ≤ k + 1, IsCell V (cellJ c s j))
  (hcor : ∀ j ≤ k + 1, ¬ IsCorner s0 (cellJ c s j) ∧ ¬ IsCorner t0 (cellJ c s j))
  (hpat : StripPat F c s (k + 2)) (hsep : ¬ Conn F (back1 c s) (front1 c s))
  (hneut : ncomp V (flipCol F c s (k + 2)) = ncomp V F)
  (hTs : ∀ tf, (tf = latA s ∨ tf = latB s) → IsCell V (nb c tf) → NotTypeIII V F (nb c tf))
include hF hs0 hds hle hTR hk hcell hcor hpat hsep hneut hTs

omit hle hneut hTs in
-- The first cell is not Type III after the flip: all its corners are joined.
--
lemma start_notTypeIII_pf : NotTypeIII V (flipCol F c s (k + 2)) c := by
  obtain ⟨F1, hF1, _, _, _, hodd, _, _⟩ :=
    strip_even_rel_pf k hk F hF hs0 hds hcell hcor hpat hsep
      (end_same_loc (restr_notT3 hTR (hcell (k + 1) le_rfl) (hcor (k + 1) le_rfl)) hk hcell hpat)
  have hl1 := (lat1_after hk hpat (j := 0) (by omega)).2 rfl
  have hl2 := (lat2_after hk hpat (j := 0) (by omega)).2 rfl
  rw [cellJ_zero] at hl1 hl2
  have c1 : Conn (flipCol F c s (k + 2)) (back1 c s) (front1 c s) := (ends_lat1 c s).conn hl1
  have c2 : Conn (flipCol F c s (k + 2)) (back2 c s) (front2 c s) := (ends_lat2 c s).conn hl2
  have hbF1 : back c s ∈ F1 := by
    rw [hF1, mem_flip_iff]
    have := back_not_mem c s (m := k + 1) (by omega)
    have := hpat.1
    tauto
  have c3 : Conn F1 (back1 c s) (back2 c s) := (ends_back c s).conn hbF1
  have c3' : Conn (flipCol F c s (k + 2)) (back1 c s) (back2 c s) :=
    (hodd _ _ (not_mid_start c s k).1 (not_mid_back2 c s k)).2 (Or.inl c3)
  exact notTypeIII_of_allConn (allConn_of_frame s c3' c1 (c3'.trans c2))

omit hle hTs in
-- The end cell's own flip separates its `lat1` corners.
--
lemma end_flip_sep_pf : ¬ Conn (flip F (cellJ c s (k + 1))) (back1 (cellJ c s (k + 1)) s)
    (front1 (cellJ c s (k + 1)) s) :=
  neutral_end_splits k hk F hF hs0 hds hcell hcor hpat hsep
    (end_same_loc (restr_notT3 hTR (hcell (k + 1) le_rfl) (hcor (k + 1) le_rfl)) hk hcell hpat) hneut

omit hTs in
theorem end_side_link1_pf (hf : outer1 (cellJ c s (k + 1)) s ∈ F)
    (hLt : ¬ IsCorner t0 (nb (cellJ c s (k + 1)) (latA s))) :
    CR2 V F ⟨c, s, k + 2⟩ ⟨nb (cellJ c s (k + 1)) (latA s), s, 1⟩ := by
  have hDc := corners_deg2 hF hcell hcor
  have hTe : NotTypeIII V F (cellJ c s (k + 1)) :=
    restr_notT3 hTR (hcell (k + 1) le_rfl) (hcor (k + 1) le_rfl)
  set e := cellJ c s (k + 1)
  set L := nb e (latA s)
  have hb0 := (outer1_body_L hDc hpat le_rfl).2 hk
  have hbL : back L s = outer1 (cellJ c s k) s := by rw [← side_back_next, nb_cellJ]
  have hfL : front L s = outer1 e s := side_front e s
  have hfar := end_side_far1_L hF.1 hle hTe hk
    (fun j hj => isCell_mono (hcell j hj) (sub_insST V s0 t0)) hpat hb0 hf
  have hl1e : lat1 e s ∈ F := (strip_sig hpat (show k + 1 < k + 2 by omega)).1.2 (by omega)
  have offL : ∀ i ≤ k + 1, back L s ∉ cellE (cellJ c s i) ∧ front L s ∉ cellE (cellJ c s i) ∧
      lat1 L s ∉ cellE (cellJ c s i) := fun i _ =>
    ⟨by rw [hbL]; exact outer1_not_mem c s k i, by rw [hfL]; exact outer1_not_mem c s (k + 1) i,
      side_lat1_not_mem c s (k + 1) i⟩
  have hV1 := (side_back_ends e s).inV (hF.1 _ (hbL ▸ hb0))
  have hV2 := (side_front_ends e s).inV (hF.1 _ hf)
  have hcL : IsCell V L := by
    refine isCell_of_corners L s (memW hV1.1 hs0 (fun h => absurd (h ▸ isCorner_back1 L s) hLt)) ?_
      (memW hV2.1 hs0 (fun h => absurd (h ▸ isCorner_front1 L s) hLt)) ?_
    · rw [side_back2]; exact memW hV1.2 hs0 (fun h => absurd (h ▸ isCorner_back1 e s) (hcor (k + 1) le_rfl).2)
    · rw [side_front2]; exact memW hV2.2 hs0 (fun h => absurd (h ▸ isCorner_front1 e s) (hcor (k + 1) le_rfl).2)
  have hmemL : ∀ y ∈ cellE L, y = back L s ∨ y = front L s ∨ y = lat1 L s ∨ y = lat2 L s := by
    intro y hy; rw [cellE_frame L s] at hy; simpa using hy
  have hmid : ∀ p (x : Edge), x ∈ F → (x.p = p ∨ x.q = p) →
      (∀ i ≤ k + 1, x ∉ cellE (cellJ c s i)) → ¬ IsMid c s k p := fun p x hx hxp hoff hm => by
    obtain ⟨i, hi, hxi⟩ := mid_touch_L hle hpat hm hx hxp
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
    exact end_flip_sep_pf hF hs0 hds hTR hk hcell hcor hpat hsep hneut
      (((e1.conn hb').symm.trans h).trans (e2.conn hf'))

omit hTs in
theorem end_side_link2_pf (hf : outer2 (cellJ c s (k + 1)) s ∈ F)
    (hLt : ¬ IsCorner t0 (nb (cellJ c s (k + 1)) (latB s))) :
    CR2 V F ⟨c, s, k + 2⟩ ⟨nb (cellJ c s (k + 1)) (latB s), s, 1⟩ := by
  have hDc := corners_deg2 hF hcell hcor
  have hTe : NotTypeIII V F (cellJ c s (k + 1)) :=
    restr_notT3 hTR (hcell (k + 1) le_rfl) (hcor (k + 1) le_rfl)
  set e := cellJ c s (k + 1)
  set L := nb e (latB s)
  have hb0 := (outer2_body_L hDc hpat le_rfl).2 hk
  have hbL : back L s = outer2 (cellJ c s k) s := by rw [outer2_side_nb_next, nb_cellJ]; rfl
  have hfL : front L s = outer2 e s := side2_front e s
  have hfar := end_side_far2_L hF.1 hle hTe hk
    (fun j hj => isCell_mono (hcell j hj) (sub_insST V s0 t0)) hpat hb0 hf
  have hl2e : lat2 e s ∈ F := (strip_sig hpat (show k + 1 < k + 2 by omega)).2.1.2 (by omega)
  have offL : ∀ i ≤ k + 1, back L s ∉ cellE (cellJ c s i) ∧ front L s ∉ cellE (cellJ c s i) ∧
      lat2 L s ∉ cellE (cellJ c s i) := fun i _ =>
    ⟨by rw [hbL]; exact outer2_not_mem c s k i, by rw [hfL]; exact outer2_not_mem c s (k + 1) i,
      side2_lat2_not_mem c s (k + 1) i⟩
  have hV1 := (side2_back_ends e s).inV (hF.1 _ (hbL ▸ hb0))
  have hV2 := (side2_front_ends e s).inV (hF.1 _ hf)
  have hcL : IsCell V L := by
    refine isCell_of_corners L s ?_ (memW hV1.2 hs0 (fun h => absurd (h ▸ isCorner_back2 L s) hLt)) ?_
      (memW hV2.2 hs0 (fun h => absurd (h ▸ isCorner_front2 L s) hLt))
    · rw [side2_back1]; exact memW hV1.1 hs0 (fun h => absurd (h ▸ isCorner_back2 e s) (hcor (k + 1) le_rfl).2)
    · rw [side2_front1]; exact memW hV2.1 hs0 (fun h => absurd (h ▸ isCorner_front2 e s) (hcor (k + 1) le_rfl).2)
  have hmemL : ∀ y ∈ cellE L, y = back L s ∨ y = front L s ∨ y = lat1 L s ∨ y = lat2 L s := by
    intro y hy; rw [cellE_frame L s] at hy; simpa using hy
  have hmid : ∀ p (x : Edge), x ∈ F → (x.p = p ∨ x.q = p) →
      (∀ i ≤ k + 1, x ∉ cellE (cellJ c s i)) → ¬ IsMid c s k p := fun p x hx hxp hoff hm => by
    obtain ⟨i, hi, hxi⟩ := mid_touch_L hle hpat hm hx hxp
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
    exact end_flip_sep_pf hF hs0 hds hTR hk hcell hcor hpat hsep hneut
      ((((ends_back e s).conn hbe).trans h).trans ((ends_front e s).conn hfe).symm)

omit hneut hTs in
-- A Type III cell of the flipped factor that shares no side with the strip is a link.
--
theorem far_link_pf {d : Pt} {tf : Side} (hd : IsCell V d)
    (hdR : ¬ IsCorner s0 d ∧ ¬ IsCorner t0 d)
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
    obtain ⟨i, hi, hxi⟩ := mid_touch_L hle hpat hm bF ((ends_back d tf).inc_iff _ |>.2 (Or.inl rfl))
    exact hfar i hi _ (mem _ (Or.inl rfl)) hxi
  have hm2 : ¬ IsMid c s k (front1 d tf) := fun hm => by
    obtain ⟨i, hi, hxi⟩ := mid_touch_L hle hpat hm fF ((ends_front d tf).inc_iff _ |>.2 (Or.inl rfl))
    exact hfar i hi _ (mem _ (Or.inr (Or.inl rfl))) hxi
  obtain ⟨F1, hF1, _, _, _, hodd, _, _⟩ :=
    strip_even_rel_pf k hk F hF hs0 hds hcell hcor hpat hsep
      (end_same_loc (restr_notT3 hTR (hcell (k + 1) le_rfl) (hcor (k + 1) le_rfl)) hk hcell hpat)
  unfold CR2
  dsimp only
  refine ⟨by omega, by omega, le_rfl, ?_, fun j hj => ?_, fun j hj i hi x hx => ?_, fun j hj => ?_,
    fun h => by simp at h, by rw [show k + 2 - 2 = k by omega]; exact hm1,
    by rw [show k + 2 - 2 = k by omega]; exact hm2, hTR d hd hdR.1 hdR.2 tf bF fF l1F l2F, ?_⟩
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
theorem t3_link_pf {d : Pt} {tf : Side} (hd : IsCell V d)
    (hdR : ¬ IsCorner s0 d ∧ ¬ IsCorner t0 d)
    (hb : back d tf ∈ flipCol F c s (k + 2)) (hf : front d tf ∈ flipCol F c s (k + 2))
    (hl1 : lat1 d tf ∉ flipCol F c s (k + 2)) (hl2 : lat2 d tf ∉ flipCol F c s (k + 2))
    (hn : ¬ Conn (flipCol F c s (k + 2)) (back1 d tf) (front1 d tf))
    (hLR : d = nb (cellJ c s (k + 1)) s →
      (IsCell (insert s0 (insert t0 V)) (nb (cellJ c s (k + 1)) (latA s)) →
        ¬ IsCorner s0 (nb (cellJ c s (k + 1)) (latA s)) ∧
        ¬ IsCorner t0 (nb (cellJ c s (k + 1)) (latA s))) ∨
      (IsCell (insert s0 (insert t0 V)) (nb (cellJ c s (k + 1)) (latB s)) →
        ¬ IsCorner s0 (nb (cellJ c s (k + 1)) (latB s)) ∧
        ¬ IsCorner t0 (nb (cellJ c s (k + 1)) (latB s)))) :
    ∃ τ : StripSpec, τ.n = 1 ∧ CR2 V F ⟨c, s, k + 2⟩ τ ∧ ChainOK ⟨c, s, k + 2⟩ τ ∧
      Restr s0 t0 τ := by
  set F' := flipCol F c s (k + 2)
  have hDc := corners_deg2 hF hcell hcor
  have hTr := ahead_notT3 hTR hcell hcor hk
  have hcellW : ∀ j ≤ k + 1, IsCell (insert s0 (insert t0 V)) (cellJ c s j) :=
    fun j hj => isCell_mono (hcell j hj) (sub_insST V s0 t0)
  have hTrW := notT3W (t0 := t0) hs0 hTr (fun ht => absurd
    (show IsCorner t0 (cellJ c s 1) by rw [← nb_cellJ, cellJ_zero]; exact ht) (hcor 1 (by omega)).2)
  have r1 : ∀ e : Pt, (¬ IsCorner s0 e ∧ ¬ IsCorner t0 e) → Restr s0 t0 ⟨e, s, 1⟩ := by
    intro e he j hj
    obtain rfl : j = 0 := by simp only at hj; omega
    rw [cellJ_zero]; exact he
  have r1' : ∀ e : Pt, (¬ IsCorner s0 e ∧ ¬ IsCorner t0 e) → Restr s0 t0 ⟨e, tf, 1⟩ := by
    intro e he j hj
    obtain rfl : j = 0 := by simp only at hj; omega
    rw [cellJ_zero]; exact he
  by_cases hfar : ∀ j < k + 2, ∀ x ∈ cellE d, x ∉ cellE (cellJ c s j)
  · refine ⟨_, rfl, far_link_pf hF hs0 hds hle hTR hk hcell hcor hpat hsep hd hdR hb hf hl1 hl2 hn hfar,
      chainOK_far fun j hj x hx hxe => ?_, r1' d hdR⟩
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
      exact hn (start_notTypeIII_pf hF hs0 hds hTR hk hcell hcor hpat hsep tf hb hf hl1 hl2)
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
    have hd := hDc (k + 1) le_rfl _ (isCorner_front1 (cellJ c s (k + 1)) s)
    rw [deg_front1, ind_of_mem l1, ind_of_not_mem hfe, ind_of_not_mem hu] at hd
    by_contra ho; rw [ind_of_not_mem ho] at hd; omega
  have ldeg2 : lat2 (nb (cellJ c s (k + 1)) s) s ∉ F → outer2 (cellJ c s (k + 1)) s ∈ F := by
    intro hu
    have l2 := (strip_sig hpat (show k + 1 < k + 2 by omega)).2.1.2 (by omega)
    have hfe : front (cellJ c s (k + 1)) s ∉ F := fun h => by
      have := ((strip_sig hpat (show k + 1 < k + 2 by omega)).2.2.2.1 h).1 (by omega); omega
    have hd := hDc (k + 1) le_rfl _ (isCorner_front2 (cellJ c s (k + 1)) s)
    rw [deg_front2, ind_of_mem l2, ind_of_not_mem hfe, ind_of_not_mem hu] at hd
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
      rcases hLR hq with hA | hB
      · -- The cell beside the end on side A has both outer sides in `F`: it is a cell.
        --
        have hbA : back (nb (cellJ c s (k + 1)) (latA s)) s ∈ F := by
          have h := (outer1_body_L hDc hpat le_rfl).2 hk
          rw [← side_back_next, nb_cellJ] at h; exact h
        have hV1 := (side_back_ends (cellJ c s (k + 1)) s).inV (hF.1 _ hbA)
        have hV2 := (side_front_ends (cellJ c s (k + 1)) s).inV (hF.1 _ (ldeg hlu'))
        have hcA : IsCell (insert s0 (insert t0 V)) (nb (cellJ c s (k + 1)) (latA s)) :=
          isCell_of_corners _ s hV1.1 (by rw [side_back2]; exact hV1.2) hV2.1
            (by rw [side_front2]; exact hV2.2)
        exact ⟨_, rfl, end_side_link1_pf hF hs0 hds hle hTR hk hcell hcor hpat hsep hneut
          (ldeg hlu') (hA hcA).2, chainOK_besideA c s k, r1 _ (hA hcA)⟩
      · have hlu2 : lat2 (nb (cellJ c s (k + 1)) s) s ∉ F' := fun h => hlu (alt.2.1.2 h)
        have hlu2' : lat2 (nb (cellJ c s (k + 1)) s) s ∉ F := by
          rw [nb_cellJ] at hlu2 ⊢
          rwa [mem_flipCol_out (fun i hi => lat2_not_mem c s (by omega))] at hlu2
        have hbB : back (nb (cellJ c s (k + 1)) (latB s)) s ∈ F := by
          have h := (outer2_body_L hDc hpat le_rfl).2 hk
          rw [outer2_side_nb_next, nb_cellJ] at h; exact h
        have hV1 := (side2_back_ends (cellJ c s (k + 1)) s).inV (hF.1 _ hbB)
        have hV2 := (side2_front_ends (cellJ c s (k + 1)) s).inV (hF.1 _ (ldeg2 hlu2'))
        have hcB : IsCell (insert s0 (insert t0 V)) (nb (cellJ c s (k + 1)) (latB s)) :=
          isCell_of_corners _ s (by rw [side2_back1]; exact hV1.1) hV1.2
            (by rw [side2_front1]; exact hV2.1) hV2.2
        exact ⟨_, rfl, end_side_link2_pf hF hs0 hds hle hTR hk hcell hcor hpat hsep hneut
          (ldeg2 hlu2') (hB hcB).2, chainOK_besideB c s k, r1 _ (hB hcB)⟩
  · rcases j with _ | j
    · exfalso
      rw [cellJ_zero] at hq
      rw [hq] at alt hn hb hf hl1 hl2
      have hd0 : ∀ z, IsCorner z c → deg F z = 2 := fun z hz =>
        hDc 0 (by omega) z (by rw [cellJ_zero]; exact hz)
      have hc0t : ¬ IsCorner t0 c := by have := (hcor 0 (by omega)).2; rwa [cellJ_zero] at this
      -- A phantom Type III square beside `c`: the cell behind `c` has unequal lateral sides, so
      -- it is not alternating.
      --
      by_cases hPA : IsCorner t0 (nb c (latA s)) ∧ ¬ NotTypeIII V F (nb c (latA s))
      · obtain ⟨_, _, _, hn1, _⟩ := phantom_sideA hF hs0 hpat (by omega) hc0 hc0t hd0
          (hTs _ (Or.inl rfl)) hPA.1 hPA.2
        have hTBW := notT3W (t0 := t0) hs0 (hTs (latB s) (Or.inr rfl))
          (fun hB => (corner_sides_disj hPA.1 hB).elim)
        have d2 := back_down2_loc hF.1 hpat (by omega) (isCell_mono hc0 (sub_insST V s0 t0)) hsep
          (hd0 _ (isCorner_back2 c s)) (hd0 _ (isCorner_front1 c s)) (hd0 _ (isCorner_front2 c s))
          hTrW hTBW
        have d2' : lat2 (nb c s.opp) s ∈ F' := by
          rw [mem_flipCol_out (fun i _ => behind_lat2_not_mem c s i)]; exact d2
        have n1' : lat1 (nb c s.opp) s ∉ F' := by
          rw [mem_flipCol_out (fun i _ => behind_lat1_not_mem c s i)]; exact hn1
        exact n1' (alt.2.1.2 d2')
      by_cases hPB : IsCorner t0 (nb c (latB s)) ∧ ¬ NotTypeIII V F (nb c (latB s))
      · obtain ⟨_, _, _, hn2, _⟩ := phantom_sideB hF hs0 hpat (by omega) hc0 hc0t hd0
          (hTs _ (Or.inr rfl)) hPB.1 hPB.2
        have hTAW := notT3W (t0 := t0) hs0 (hTs (latA s) (Or.inl rfl))
          (fun hA => (corner_sides_disj hA hPB.1).elim)
        have d1 := back_down_loc hF.1 hpat (by omega) hsep (hd0 _ (isCorner_back1 c s))
          (hd0 _ (isCorner_front1 c s)) hTAW
        have d1' : lat1 (nb c s.opp) s ∈ F' := by
          rw [mem_flipCol_out (fun i _ => behind_lat1_not_mem c s i)]; exact d1
        have n2' : lat2 (nb c s.opp) s ∉ F' := by
          rw [mem_flipCol_out (fun i _ => behind_lat2_not_mem c s i)]; exact hn2
        exact n2' (alt.2.1.1 d1')
      have hTsW : ∀ tf, (tf = latA s ∨ tf = latB s) → IsCell (insert s0 (insert t0 V)) (nb c tf) →
          NotTypeIII (insert s0 (insert t0 V)) F (nb c tf) := by
        rintro tf (rfl | rfl)
        · exact notT3W (t0 := t0) hs0 (hTs _ (Or.inl rfl)) (fun hc => by
            by_contra hn; exact hPA ⟨hc, hn⟩)
        · exact notT3W (t0 := t0) hs0 (hTs _ (Or.inr rfl)) (fun hc => by
            by_contra hn; exact hPB ⟨hc, hn⟩)
      have d1 := back_down_loc hF.1 hpat (by omega) hsep
        (hDc 0 (by omega) _ (by rw [cellJ_zero]; exact isCorner_back1 c s))
        (hDc 0 (by omega) _ (by rw [cellJ_zero]; exact isCorner_front1 c s)) (hTsW _ (Or.inl rfl))
      have d2 := back_down2_loc hF.1 hpat (by omega) (isCell_mono hc0 (sub_insST V s0 t0)) hsep
        (hDc 0 (by omega) _ (by rw [cellJ_zero]; exact isCorner_back2 c s))
        (hDc 0 (by omega) _ (by rw [cellJ_zero]; exact isCorner_front1 c s))
        (hDc 0 (by omega) _ (by rw [cellJ_zero]; exact isCorner_front2 c s)) hTrW (hTsW _ (Or.inr rfl))
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
      have hcc : AllConn F' c := alt_corners_conn' (start_notTypeIII_pf hF hs0 hds hTR hk hcell hcor hpat hsep) hac
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
      obtain ⟨_, fb, ff⟩ := side1_facts_R hF.1 hDc hcell hpat hsep hjk (fun h0 => notT3W (t0 := t0) hs0
        (hTs _ (Or.inl rfl)) (fun ht => absurd (by rw [hq, h0, cellJ_zero]; exact ht) hdR.2))
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
      exact ⟨_, rfl, end_side_link1_pf hF hs0 hds hle hTR hk hcell hcor hpat hsep hneut hfr (hq ▸ hdR).2, chainOK_besideA c s k, r1 _ (hq ▸ hdR)⟩
  · by_cases hjk : j ≤ k
    · exfalso
      obtain ⟨_, fb, ff⟩ := side2_facts_R hF.1 hDc hcell hpat hsep hTrW hjk (fun h0 => notT3W (t0 := t0) hs0
        (hTs _ (Or.inr rfl)) (fun ht => absurd (by rw [hq, h0, cellJ_zero]; exact ht) hdR.2))
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
      exact ⟨_, rfl, end_side_link2_pf hF hs0 hds hle hTR hk hcell hcor hpat hsep hneut hfr (hq ▸ hdR).2, chainOK_besideB c s k, r1 _ (hq ▸ hdR)⟩

end t3pf

end HP

end ULHC
