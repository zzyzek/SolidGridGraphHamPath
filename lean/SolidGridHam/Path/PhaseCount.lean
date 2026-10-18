/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
import SolidGridHam.Path.TriProof
import SolidGridHam.Path.Prelim.RelPF

/-!
# Each bridge step adds one piece

The flipped square `E` is uncut with dark laterals. By `split_rel_pf`, a connection before the
flip is one after it, possibly through one jump between the ends of `E`'s lateral `lat1`, which is
exactly a connection after inserting that edge. The step's split condition says those ends are
apart after the flip, so inserting the edge merges two classes: one piece more (`step_count`).
Along a phase, `ncomp H = ncomp H0 + |BS|` (`reach_count`).
-/

namespace SolidGridHam

namespace HP

open Finset Classical

section count

variable {V W : Finset Pt} {d : Pt → ℕ} {H : Finset Edge} {t0 u0 : Pt}

theorem step_count (hVW : V ⊆ W) {b : Bridge} (hrs : RowStep V H b)
    (hdegc : ∀ f, IsCell V f → ∀ z, IsCorner z f → deg H z = 2) :
    ncomp W (flip H b.E) = ncomp W H + 1 := by
  obtain ⟨Fl1, Fl2, Fbk, Ffr, _, _, Fun⟩ := rowStep_pre hrs hdegc
  have hEcell : IsCell V b.E := hrs.cells _ (by have := hrs.two; omega)
  set C := mkLat b.E b.a with hC
  have hres : flip H b.E = C.res H := C.flip_eq (mkLat_cellE b.E b.a) Fl1 Fl2 Fbk Ffr
  have hsame : Conn H C.a C.d :=
    conn_of_uncut Fun (isCorner_back1 _ _) (isCorner_back2 _ _)
  have rel := split_rel_pf C Fl1 Fl2 hsame
  have nsplit : ¬ Conn (C.res H) C.a C.b := by rw [← hres]; exact hrs.split
  have corners := isCell_corners hEcell b.a
  have hab : C.e1.p ∈ W ∧ C.e1.q ∈ W := by
    rcases C.h1 with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2]
    · exact ⟨hVW corners.1, hVW corners.2.2.1⟩
    · exact ⟨hVW corners.2.2.1, hVW corners.1⟩
  have ne1 : ¬ Conn (C.res H) C.e1.p C.e1.q := by
    rcases C.h1 with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2]
    · exact nsplit
    · exact fun h => nsplit h.symm
  have e1 : ncomp W H = ncomp W (insert C.e1 (C.res H)) := by
    apply ncomp_congr
    intro x _ y _
    rw [rel x y, conn_insert]
    rcases C.h1 with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2]; tauto
  have e2 := ncomp_insert_merge hab.1 hab.2 ne1
  rw [hres]; omega

-- **The count along a phase.**
--
theorem reach_count (hVW : V ⊆ W) (hdc : ∀ q, IsCell V q → ∀ z, IsCorner z q → d z = 2)
    {H0 : Finset Edge} (h0 : IsFactor W d H0)
    (hout0 : ∀ e ∈ H0, (e.p ∉ V → e.q = t0 ∨ e.q = u0) ∧ (e.q ∉ V → e.p = t0 ∨ e.p = u0))
    {H : Finset Edge} {BS : List Bridge} (hr : Reach V H0 H BS) :
    ncomp W H = ncomp W H0 + BS.length := by
  induction hr with
  | base => simp
  | step hr' hrs _ _ ih =>
    have hinv := pinv_reach (t0 := t0) (u0 := u0) hVW hdc h0 hout0 hr'
    rw [step_count hVW hrs (degc_of hVW hdc hinv.fac), ih]
    simp; omega

end count

end HP

end SolidGridHam
