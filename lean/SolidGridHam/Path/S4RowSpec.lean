/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
module

public import SolidGridHam.Path.S4Rows

@[expose] public section

/-!
# S4 for the row outcomes

For the `.odd` and `.twist` outcomes of a phase, `reduceOut` is a notch state with one piece
fewer than the start of the phase.  The counting runs with the degree-one points in the order
`p`, `s`, since `p ∈ insert p V` holds outright.
-/

namespace SolidGridHam

namespace HP

open Finset Classical

lemma OpsOK.swap {W : Finset Pt} {G : Finset Edge} {ops : List Join} {P : Pt → Prop} {a b : Pt}
    (h : OpsOK W G ops P a b) : OpsOK W G ops P b a :=
  ⟨fun o ho => by
    obtain ⟨h1, h2, h3, h4, h5⟩ := h.each o ho
    exact ⟨h1, h2, h3, fun j hj => (h4 j hj).symm, h5⟩, h.compat⟩

section s4rowspec

variable {V : Finset Pt} {s t p : Pt} {e0 : Edge}

lemma notCorner_out (hpV : p ∉ V) {c : Pt} (hc : IsCell V c) : ¬ IsCorner p c := by
  intro hz
  apply hpV
  obtain ⟨x, y⟩ := c
  rcases hz with h | h | h | h <;> rw [h]
  · exact hc.1
  · exact hc.2.1
  · exact hc.2.2.1
  · exact hc.2.2.2

-- The phase's flips are on cells of `V`, so they keep the edges at `p`.
--
lemma reach_pat (hpV : p ∉ V) {H0 H : Finset Edge} {BS : List Bridge} (hr : Reach V H0 H BS)
    (h : PAt p e0 H0) : PAt p e0 H := by
  induction hr with
  | base => exact h
  | step _ hrs _ _ ih => exact ih.flip hpV (hrs.cells _ (by have := hrs.two; omega))

lemma dST_two (z : Pt) (h1 : z ≠ p) (h2 : z ≠ s) : dST s p z = 2 := by
  unfold dST; rw [ite_eq_right]; tauto

lemma dST_p : dST s p p = 1 := by unfold dST; simp

end s4rowspec

end HP

end SolidGridHam
