/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
module

public import SolidGridHam.Path.S4RowSpec

@[expose] public section

/-!
# S4 for the merging-cell outcome, given a good cell

`reduceOut` on `.merge c` takes the first cell of `cellList V` that is alternating, cut, not a
pair square, and whose plan passes `candOK` (rule (a*), docs/S4_RESIDUAL.md). Here: when such a
cell exists, the result is a notch state with one piece fewer than the start of the phase.
Existence of a good cell is Theorem R (separate).
-/

namespace SolidGridHam

namespace HP

open Finset Classical

-- A good merging cell for the state `(H, BS)` (the test in `reduceOut`).
--
def GoodCell (W : Finset Pt) (s0 p0 : Pt) (H : Finset Edge) (BS : List Bridge) (X : Pt) : Prop :=
  Alt H X ∧ CutSq H X ∧ ¬ (∃ b ∈ BS, X = b.cell (b.r - 2) ∨ X = b.E) ∧
    candOK W H ((mergeJoin H X).apply H) BS (mergeJoin H X) 0
      (reduceOut.rowStartPair' (mergeJoin H X)) s0 p0

-- A cut alternating cell is a strip of one cell in its `altFrame`.
--
lemma merge_join_alt {G : Finset Edge} {c : Pt} (ha : Alt G c) (hcut : CutSq G c) :
    StripPat G c (altFrame G c) 1 ∧
      ¬ Conn G (back1 c (altFrame G c)) (front1 c (altFrame G c)) := by
  have frame : back c (altFrame G c) ∈ G ∧ front c (altFrame G c) ∈ G ∧
      lat1 c (altFrame G c) ∉ G ∧ lat2 c (altFrame G c) ∉ G := by
    unfold altFrame
    unfold Alt at ha
    split_ifs with hb
    · rcases ha with ⟨h1, h2, h3, h4⟩ | ⟨h1, _, _, _⟩
      · exact ⟨h1, h2, h3, h4⟩
      · exact absurd hb h1
    · rcases ha with ⟨h1, _, _, _⟩ | ⟨h1, h2, h3, h4⟩
      · exact absurd h1 hb
      · exact ⟨h3, h4, h1, h2⟩
  obtain ⟨hb, hf, hl1, hl2⟩ := frame
  refine ⟨⟨hb, fun j hj => ?_, fun j hj => ?_⟩, fun h => ?_⟩
  · obtain rfl : j = 0 := by omega
    rw [cellJ_zero]
    exact ⟨⟨fun h => absurd h hl1, fun h => by omega⟩, ⟨fun h => absurd h hl2, fun h => by omega⟩⟩
  · obtain rfl : j = 0 := by omega
    rw [cellJ_zero]; exact ⟨fun _ => by omega, fun _ => hf⟩
  · have kb := (ends_back (c := c) (s := altFrame G c)).conn hb
    have kf := (ends_front (c := c) (s := altFrame G c)).conn hf
    exact uncut_of kb h ((kb.symm.trans h).trans kf) hcut

lemma getD_spec {α : Type*} (l : List α) (f : α → Bool) (c : α) (P : α → Prop)
    (h1 : ∀ X ∈ l, f X = true → P X) (h2 : ∃ X ∈ l, f X = true) : P ((l.find? f).getD c) := by
  cases hf : l.find? f with
  | none =>
    obtain ⟨X, hX, hfX⟩ := h2
    exact absurd hfX (by simpa using List.find?_eq_none.1 hf X hX)
  | some X => exact h1 X (List.mem_of_find?_eq_some hf) (List.find?_some hf)

section s4merge

variable {V : Finset Pt} {s t p : Pt} {e0 : Edge}

def MergeGoodSpec (V : Finset Pt) (s p : Pt) (e0 : Edge) : Prop :=
  ∀ (H0 H : Finset Edge) (BS : List Bridge) (c : Pt), NotchF V s p e0 H0 →
    2 ≤ ncomp (insert p V) H0 → POK V H0 H BS (.merge c) →
      ∃ X, IsCell V X ∧ X ∈ V ∧ GoodCell (insert p V) s p H BS X

end s4merge

end HP

end SolidGridHam
