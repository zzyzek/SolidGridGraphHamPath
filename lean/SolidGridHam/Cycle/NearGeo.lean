/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
module

public import SolidGridHam.Cycle.Touch
public import SolidGridHam.Cycle.Stacked

@[expose] public section

/-!
# Geometry for the near lemma

* `Touches a z`: some cell of `z` shares a side with some cell of `a`.
* `touch_cases`: a cell sharing a side with `d` is `d` or one of its four neighbours.
* `mid_touch`: a dark edge at a middle corner of `a` is a side of a cell of `a` (the middle
  corner already has its two dark edges from `a`'s pattern).
-/

namespace SolidGridHam

open Finset

def Touches (a z : StripSpec) : Prop :=
  ∃ i < z.n, ∃ j < a.n, ∃ x ∈ cellE (cellJ z.c z.s i), x ∈ cellE (cellJ a.c a.s j)

lemma side_mem_self (c : Pt) (tf : Side) : sideEdge c tf ∈ cellE c := by
  cases tf <;> simp [cellE, sideEdge]

lemma side_mem_nb (c : Pt) (tf : Side) : sideEdge c tf ∈ cellE (nb c tf) := by
  obtain ⟨x, y⟩ := c
  cases tf <;> simp [cellE, sideEdge, nb, bot, top, lft, rgt]

lemma touch_cases {q d : Pt} (s : Side) {x : Edge} (h1 : x ∈ cellE q) (h2 : x ∈ cellE d) :
    q = d ∨ q = nb d s ∨ q = nb d s.opp ∨ q = nb d (latA s) ∨ q = nb d (latB s) := by
  rw [cellE_frame d s] at h2
  simp only [Finset.mem_insert, Finset.mem_singleton] at h2
  rcases h2 with rfl | rfl | rfl | rfl
  · rcases cell_of_side d (tf := s.opp) h1 with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inl h))
  · rcases cell_of_side d (tf := s) h1 with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · rw [lat1_eq] at h1
    rcases cell_of_side d (tf := latA s) h1 with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · rw [lat2_eq] at h1
    rcases cell_of_side d (tf := latB s) h1 with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inr (Or.inr h)))

section mid

variable {V : Finset Pt} {F : Finset Edge} {c : Pt} {s : Side} {k : ℕ}
  (hF : Deg2 V F) (hpat : StripPat F c s (k + 2))
  (hcell : ∀ j ≤ k + 1, IsCell V (cellJ c s j))
include hF hpat hcell

-- A dark edge at a middle corner of `a` is a side of a cell of `a`.
--
theorem mid_touch {p : Pt} (hm : IsMid c s k p) {x : Edge} (hx : x ∈ F) (hxp : x.p = p ∨ x.q = p) :
    ∃ j < k + 2, x ∈ cellE (cellJ c s j) := by
  obtain ⟨j, hj, hjk, hp⟩ := hm
  obtain ⟨a1, a2, _, af⟩ := strip_sig hpat (show j < k + 2 by omega)
  have l1 := a1.2 hj
  have l2 := a2.2 hj
  have fr : front (cellJ c s j) s ∈ F := af.2 ⟨fun _ => by omega, fun _ => hj⟩
  have hdeg := hF.2 _ (corners4 (hcell j (by omega)) s).2.2.1
  have hdeg2 := hF.2 _ (corners4 (hcell j (by omega)) s).2.2.2
  set d := cellJ c s j
  have mem : ∀ y, y = lat1 d s ∨ y = lat2 d s ∨ y = front d s → y ∈ cellE d := by
    intro y hy; rw [cellE_frame d s]; rcases hy with rfl | rfl | rfl <;> simp
  refine ⟨j, by omega, ?_⟩
  rcases hp with rfl | rfl
  · by_contra hn
    have n1 : x ≠ lat1 d s := fun h => hn (mem _ (Or.inl h))
    have n2 : x ≠ front d s := fun h => hn (mem _ (Or.inr (Or.inr h)))
    have n12 : lat1 d s ≠ front d s :=
      (ends_lat1 d s).ne_at (ends_front d s) (stk_b1_f2 d s)
    have := three_le_deg l1 fr hx ((ends_lat1 d s).inc_iff _ |>.2 (Or.inr rfl))
      ((ends_front d s).inc_iff _ |>.2 (Or.inl rfl)) hxp n12 n1.symm n2.symm
    omega
  · by_contra hn
    have n1 : x ≠ lat2 d s := fun h => hn (mem _ (Or.inr (Or.inl h)))
    have n2 : x ≠ front d s := fun h => hn (mem _ (Or.inr (Or.inr h)))
    have n12 : lat2 d s ≠ front d s :=
      (ends_lat2 d s).ne_at (ends_front d s).swap (stk_b2_f1 d s)
    have := three_le_deg l2 fr hx ((ends_lat2 d s).inc_iff _ |>.2 (Or.inr rfl))
      ((ends_front d s).inc_iff _ |>.2 (Or.inr rfl)) hxp n12 n1.symm n2.symm
    omega

end mid

end SolidGridHam
