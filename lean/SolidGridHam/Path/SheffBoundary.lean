/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
module

public import SolidGridHam.Path.SheffCost
public import SolidGridHam.Algorithm

@[expose] public section

/-!
# Dangling `s`, `t` on the boundary

`hpB V s t`: if a lattice neighbour of `t` is missing, run `hpSheffC` with it as the phantom;
otherwise try deleting `t` towards each neighbour `w ≠ s` (`hp_delete`), with `t` as the phantom of
`V.erase t`. Correct when `t` has a missing king neighbour, and polynomial.
-/

namespace SolidGridHam

namespace HP

open Finset Classical

lemma nbrsL_ends {t : Pt} {x : Pt × Edge} (hx : x ∈ nbrsL t) :
    (x.2.p = t ∧ x.2.q = x.1) ∨ (x.2.p = x.1 ∧ x.2.q = t) := by
  obtain ⟨a, b⟩ := t
  simp only [nbrsL, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl <;> simp [eR, eL, eU, eD, Edge.q]

lemma mem_nbrsL {t w : Pt} {ew : Edge} (h : (ew.p = t ∧ ew.q = w) ∨ (ew.p = w ∧ ew.q = t)) :
    (w, ew) ∈ nbrsL t := by
  obtain ⟨d, ⟨z1, z2⟩⟩ := ew
  obtain ⟨a, b⟩ := t
  obtain ⟨u, v⟩ := w
  cases d <;> simp only [Edge.q, Prod.mk.injEq] at h <;>
    simp only [nbrsL, eR, eL, eU, eD, List.mem_cons, Prod.mk.injEq, Edge.mk.injEq,
      List.not_mem_nil, or_false, reduceCtorEq, false_and, true_and, and_false] <;> omega

def hpB (V : Finset Pt) (s t : Pt) : Bool :=
  match (nbrsL t).find? (fun x => decide (x.1 ∉ V)) with
  | some x => hpSheffC V s t x.1 x.2
  | none => (nbrsL t).any fun x => decide (x.1 ≠ s) && hpSheffC (V.erase t) s x.1 t x.2

def hpBCost (V : Finset Pt) (s t : Pt) : ℕ :=
  8 +
    match (nbrsL t).find? (fun x => decide (x.1 ∉ V)) with
    | some x => hpSheffCCost V s t x.1 x.2
    | none => ((nbrsL t).map fun x =>
        2 + if x.1 ≠ s then hpSheffCCost (V.erase t) s x.1 t x.2 else 0).sum

section boundary

variable {V : Finset Pt} {s t : Pt}

lemma edge_ne {t w : Pt} {ew : Edge} (h : (ew.p = t ∧ ew.q = w) ∨ (ew.p = w ∧ ew.q = t)) :
    t ≠ w := by
  have hpq : ew.p ≠ ew.q := by obtain ⟨dir, ⟨x, y⟩⟩ := ew; cases dir <;> simp [Edge.q]
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [← h1, ← h2]; exact hpq
  · rw [← h1, ← h2]; exact Ne.symm hpq

end boundary

end HP

end SolidGridHam
