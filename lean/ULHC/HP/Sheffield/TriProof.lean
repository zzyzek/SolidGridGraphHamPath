/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
import ULHC.HP.Sheffield.SideProof

/-!
# The field `tri` at the end of a phase

Every three-piece cell has E1's shape or the diagonal shape (`tri_of`). The key step is local
(`across_noncell`): when the two corners on one side of a cell are each alone on that cell's
sides there, the square across that side is merging if it is a cell; its possible partners have two
dark sides at a corner, so it is no pair square, hence (F2) not a cell, and the edge leaving `V`
puts `t0` at one of the two corners.
* A side whose corners are joined leaves the two opposite corners alone: E1's shape.
* No side joined but a diagonal joined: the diagonal shape.
* Four pieces: `t0` would be on two opposite sides.
-/

namespace ULHC

namespace HP

open Finset Classical

section tri

variable {V : Finset Pt} {H : Finset Edge} {FP : List FixedPr} {t0 u0 : Pt}
  (hdegc : ∀ f, IsCell V f → ∀ z, IsCorner z f → deg H z = 2)
  (hf2 : ∀ q, IsCell V q → Alt H q → CutSq H q → ∃ i ∈ FP, q = i.top ∨ q = i.bot)
  (hpalt : ∀ i ∈ FP, Alt H i.top ∧ Alt H i.bot) (hpdark : ∀ i ∈ FP, sideEdge i.bot i.s ∈ H)
  (hout : ∀ e ∈ H, (e.p ∉ V → e.q = t0 ∨ e.q = u0) ∧ (e.q ∉ V → e.p = t0 ∨ e.p = u0))
include hdegc hf2 hpalt hpdark hout

theorem across_noncell {f : Pt} {sd : Side} (hf : IsCell V f) (hl1 : lat1 f sd ∉ H)
    (hl2 : lat2 f sd ∉ H) (hfr : front f sd ∉ H) (hn : ¬ Conn H (front1 f sd) (front2 f sd)) :
    ¬ IsCell V (nb f sd) ∧ ∃ w, (w = t0 ∨ w = u0) ∧ (w = front1 f sd ∨ w = front2 f sd) := by
  obtain ⟨oA, lA⟩ := forcedA hl1 hfr (hdegc f hf _ (isCorner_front1 f sd))
  obtain ⟨oB, lB⟩ := forcedB hl2 hfr (hdegc f hf _ (isCorner_front2 f sd))
  have hb1 : back (nb f sd) sd ∉ H := by rw [back_nb]; exact hfr
  have hf1 : front (nb f sd) sd ∉ H := by
    intro h
    apply hn
    have e1 := (ends_lat1 (c := nb f sd) (s := sd)).conn lA
    have e2 := (ends_lat2 (c := nb f sd) (s := sd)).conn lB
    have e3 := (ends_front (c := nb f sd) (s := sd)).conn h
    rw [back1_nb] at e1; rw [back2_nb] at e2
    exact e1.trans (e3.trans e2.symm)
  have notCell : ¬ IsCell V (nb f sd) := by
    intro hc1
    have halt1 := alt_of_lats lA lB hb1 hf1
    have hcut1 : CutSq H (nb f sd) := by
      refine cutSq_of_corners (u := back1 (nb f sd) sd) (v := back2 (nb f sd) sd)
        (isCorner_back1 _ _) (isCorner_back2 _ _) ?_
      rw [back1_nb, back2_nb]; exact hn
    obtain ⟨s', hd, hP⟩ := pair_partner hpalt hpdark (hf2 _ hc1 halt1 hcut1)
    rcases side_cases sd s' with rfl | rfl | rfl | rfl
    · exact hf1 hd
    · exact hb1 hd
    · rw [← nb_side_comm] at hP; exact partnerA oA lA hP
    · rw [← nb_sideB_comm] at hP; exact partnerB oB lB hP
  refine ⟨notCell, ?_⟩
  have fV := isCell_corners hf sd
  by_contra hne
  push Not at hne
  apply notCell
  apply isCell_of_corners (a := sd)
  · rw [back1_nb]; exact fV.2.2.1
  · rw [back2_nb]; exact fV.2.2.2
  · by_contra hx
    have e := ends_swap (ends_lat1 (c := nb f sd) (s := sd))
    rw [back1_nb] at e
    rcases out_end hout e lA hx with h | h
    · exact (hne _ (Or.inl rfl)).1 h.symm
    · exact (hne _ (Or.inr rfl)).1 h.symm
  · by_contra hx
    have e := ends_swap (ends_lat2 (c := nb f sd) (s := sd))
    rw [back2_nb] at e
    rcases out_end hout e lB hx with h | h
    · exact (hne _ (Or.inl rfl)).2 h.symm
    · exact (hne _ (Or.inr rfl)).2 h.symm

-- **E1's shape or the diagonal shape for every three-piece cell.**
--
theorem tri_of (hfar : Far t0 u0) : ∀ f, IsCell V f → Three H f → TriOK V H t0 u0 f := by
  intro f hf h3
  by_cases hside : ∃ sd, Conn H (back1 f sd) (back2 f sd)
  · obtain ⟨sd, hbb⟩ := hside
    have n12 : ¬ Conn H (front1 f sd) (front2 f sd) := fun h =>
      noThree_two (A := back1 f sd) (B := front1 f sd) (fun u hu => by
        rcases corner_cases f sd hu with rfl | rfl | rfl | rfl
        · exact Or.inl (Conn.refl _ _)
        · exact Or.inl hbb.symm
        · exact Or.inr (Conn.refl _ _)
        · exact Or.inr h.symm) h3
    have n11 : ¬ Conn H (front1 f sd) (back1 f sd) := fun h =>
      noThree_two (A := back1 f sd) (B := front2 f sd) (fun u hu => by
        rcases corner_cases f sd hu with rfl | rfl | rfl | rfl
        · exact Or.inl (Conn.refl _ _)
        · exact Or.inl hbb.symm
        · exact Or.inl h
        · exact Or.inr (Conn.refl _ _)) h3
    have n22 : ¬ Conn H (front2 f sd) (back2 f sd) := fun h =>
      noThree_two (A := back1 f sd) (B := front1 f sd) (fun u hu => by
        rcases corner_cases f sd hu with rfl | rfl | rfl | rfl
        · exact Or.inl (Conn.refl _ _)
        · exact Or.inl hbb.symm
        · exact Or.inr (Conn.refl _ _)
        · exact Or.inl (h.trans hbb.symm)) h3
    have hl1 : lat1 f sd ∉ H := fun h => n11 ((ends_lat1 (c := f) (s := sd)).conn h).symm
    have hl2 : lat2 f sd ∉ H := fun h => n22 ((ends_lat2 (c := f) (s := sd)).conn h).symm
    have hfr : front f sd ∉ H := fun h => n12 ((ends_front (c := f) (s := sd)).conn h)
    obtain ⟨hnc, w, hw, ht⟩ := across_noncell hdegc hf2 hpalt hpdark hout hf hl1 hl2 hfr n12
    rcases hw with rfl | rfl
    · exact Or.inl (Or.inl ⟨sd, ht, hnc, hbb, n12, n11, n22⟩)
    · exact Or.inl (Or.inr ⟨sd, ht, hnc, hbb, n12, n11, n22⟩)
  push Not at hside
  have nside : ∀ sd, ¬ Conn H (front1 f sd) (front2 f sd) := fun sd => by
    have := hside sd.opp; rw [back1_sopp, back2_sopp] at this; exact this
  by_cases hdiag : Conn H (f.1, f.2) (f.1 + 1, f.2 + 1) ∨ Conn H (f.1 + 1, f.2) (f.1, f.2 + 1)
  · exact Or.inr ⟨nside, hdiag⟩
  exfalso
  push Not at hdiag
  -- Four pieces: the squares across the bottom and the top both put `t0` at their corners.
  --
  have light : ∀ sd, lat1 f sd ∉ H ∧ lat2 f sd ∉ H ∧ front f sd ∉ H := by
    intro sd
    refine ⟨fun h => ?_, fun h => ?_, fun h => nside sd ((ends_front (c := f) (s := sd)).conn h)⟩
    · have := (ends_lat1 (c := f) (s := sd)).conn h
      have h2 := hside (latA sd)
      obtain ⟨x, y⟩ := f
      cases sd <;> simp only [back1, back2, front1, front2, latA] at this h2 hdiag nside <;>
        first | exact h2 this | exact h2 this.symm | exact (nside .b) this |
          exact (nside .b) this.symm | exact (nside .t) this | exact (nside .t) this.symm |
          exact (nside .l) this | exact (nside .l) this.symm
    · have := (ends_lat2 (c := f) (s := sd)).conn h
      obtain ⟨x, y⟩ := f
      cases sd <;> simp only [back2, front1, front2] at this nside <;>
        first | exact (nside .b) this | exact (nside .b) this.symm | exact (nside .t) this |
          exact (nside .t) this.symm | exact (nside .l) this | exact (nside .l) this.symm |
          exact (nside .r) this | exact (nside .r) this.symm
  obtain ⟨b1, b2, b3⟩ := light .b
  obtain ⟨t1, t2, t3⟩ := light .t
  obtain ⟨_, wb, hwb, hb⟩ := across_noncell hdegc hf2 hpalt hpdark hout hf b1 b2 b3 (nside .b)
  obtain ⟨_, wt, hwt, ht⟩ := across_noncell hdegc hf2 hpalt hpdark hout hf t1 t2 t3 (nside .t)
  -- two different out-vertices at corners of `f` are too close; one cannot be on both sides
  have cb : IsCorner wb f := by
    rcases hb with rfl | rfl
    · exact isCorner_front1 f .b
    · exact isCorner_front2 f .b
  have ct : IsCorner wt f := by
    rcases ht with rfl | rfl
    · exact isCorner_front1 f .t
    · exact isCorner_front2 f .t
  by_cases hbt : wb = wt
  · subst hbt
    obtain ⟨x, y⟩ := f
    simp only [front1, front2] at hb ht
    rcases hb with rfl | rfl <;> rcases ht with h | h <;> simp [Prod.ext_iff] at h
  · have hcl := corners_close cb ct
    rcases hwb with rfl | rfl <;> rcases hwt with rfl | rfl
    · exact hbt rfl
    · exact far_close hfar hbt hcl
    · exact far_close hfar (Ne.symm hbt) (close1_comm hcl)
    · exact hbt rfl

end tri

section final

variable {V W : Finset Pt} {d : Pt → ℕ} {t0 u0 : Pt}

-- **S3: the certificate at the end of a phase.** A state reached from a factor `H0` by bridge
-- steps, where every merging cell is a pair square and every critical square is a bridge square or
-- stuck, satisfies `Cert`.
--
theorem cert_of_stuck (hVW : V ⊆ W) (hdc : ∀ q, IsCell V q → ∀ z, IsCorner z q → d z = 2)
    {H0 : Finset Edge} (h0 : IsFactor W d H0)
    (hout0 : ∀ e ∈ H0, (e.p ∉ V → e.q = t0 ∨ e.q = u0) ∧ (e.q ∉ V → e.p = t0 ∨ e.p = u0))
    {H : Finset Edge} {BS : List Bridge} (hr : Reach V H0 H BS) (hmerge : MergeOK V H BS)
    (hstuck : Stuck V H BS) (hfar : Far t0 u0) :
    Cert V H (BS.map (Bridge.pairOf H)) t0 u0 := by
  have hinv := pinv_reach hVW hdc h0 hout0 hr
  have hdegc := degc_of hVW hdc hinv.fac
  obtain ⟨hf2, _, hpalt, hpdark, _⟩ := phase_fp hVW hdc hinv hmerge
  exact cert_of_phase hVW hdc hinv hmerge hfar (tri_of hdegc hf2 hpalt hpdark hinv.out hfar)
    (col_of_stuck hVW hdc hinv hmerge hstuck) (side_of_stuck hVW hdc hinv hmerge hstuck)

end final

end HP

end ULHC
