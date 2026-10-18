/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
import SolidGridHam.Path.Compat2

/-!
# Lemma 4, (C2): reduction to neighbours

If an earlier operation `O` toggles a side `e` of a square `Y` of a later operation, and no square
of `O` is `Y`, then `O` has a square `X` across `e` from `Y`, and `e` is a lateral of `X`, or the
back of `O`'s start, or the front of `O`'s last square (`c2_reduce`).
-/

namespace SolidGridHam

namespace HP

open Finset Classical

theorem c2_reduce {o : Join} {Y : Pt} {e : Edge} (htog : o.tog e) (he : e ∈ cellE Y)
    (hc1 : ∀ j < o.n, cellJ o.c o.a j ≠ Y) :
    ∃ j < o.n, ∃ s', e = sideEdge Y s' ∧ cellJ o.c o.a j = nb Y s' ∧
      (e = lat1 (cellJ o.c o.a j) o.a ∨ e = lat2 (cellJ o.c o.a j) o.a ∨
        (j = 0 ∧ e = back o.c o.a) ∨ (j + 1 = o.n ∧ e = front (cellJ o.c o.a j) o.a)) := by
  obtain ⟨j, hj, hX⟩ := tog_cell htog
  obtain ⟨s', rfl⟩ := cellE_side he
  rw [sideEdge_mem_cellE] at hX
  rcases hX with hX | hX
  · exact absurd hX (hc1 j hj)
  · exact ⟨j, hj, s', rfl, hX, tog_side htog hj (by rw [hX, ← sideEdge_nb_opp, sideEdge_mem_cellE]; left; rfl)⟩

end HP

end SolidGridHam
