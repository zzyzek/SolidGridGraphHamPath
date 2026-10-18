/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
import SolidGridHam.Path.Prelim.StripEvenPF
import SolidGridHam.Cycle.Dual

/-!
# The smallest fence (notes P15)

`ArcTo F q c`: `F`'s arc between neighbouring cells `q` and `c` points from `q` into `c`.
`AncP F b c`: an arc path leads from `c` to `b`. `R` = the cells with an arc path to `b`.

`smallest_fence`: if every cell with an arc path to `b` is a cell of the graph, then flipping
`R` gives a factor with the same degrees; for every `H` with `D F H b ≤ -2` (in the notes'
terms, `H` lower than `F` at `b`), `μ` drops by `2 |R|`; and `R` lies inside every set of
cells containing `b` that no arc enters from outside. The proof uses only that `D` never
decreases along an arc (so every cell of `R` has `D ≤ D b`) and `D_rflip`.
-/

namespace SolidGridHam

open Finset Classical

namespace HP

def ArcTo (F : Finset Edge) (q c : Pt) : Prop := ∃ s, nb c s = q ∧ outArc F c s = false

def AncP (F : Finset Edge) (b c : Pt) : Prop := Relation.ReflTransGen (ArcTo F) c b

def InClosed (F : Finset Edge) (R : Finset Pt) : Prop := ∀ c ∈ R, ∀ q, ArcTo F q c → q ∈ R

-- `D` never decreases along an arc.
--
lemma D_arc {V : Finset Pt} {d : Pt → ℕ} {F H : Finset Edge} (hF : IsFactor V d F)
    (hH : IsFactor V d H) {q c : Pt} (h : ArcTo F q c) : D F H q ≤ D F H c := by
  obtain ⟨s, rfl, ho⟩ := h
  have := D_step hF hH c s
  rw [ho] at this
  simp only [Bool.false_eq_true, ite_false] at this
  split_ifs at this <;> omega

lemma D_le_anc {V : Finset Pt} {d : Pt → ℕ} {F H : Finset Edge} (hF : IsFactor V d F)
    (hH : IsFactor V d H) {b c : Pt} (h : AncP F b c) : D F H c ≤ D F H b := by
  induction h with
  | refl => exact le_rfl
  | tail _ hyz ih => exact ih.trans (D_arc hF hH hyz)

lemma isEdge_of_cellE {V : Finset Pt} {c : Pt} (hc : IsCell V c) {e : Edge} (he : e ∈ cellE c) :
    IsEdge V e := by
  simp only [cellE, Finset.mem_insert, Finset.mem_singleton] at he
  rcases he with rfl | rfl | rfl | rfl
  · exact isEdge_side hc .b
  · exact isEdge_side hc .t
  · exact isEdge_side hc .l
  · exact isEdge_side hc .r

end HP

end SolidGridHam
