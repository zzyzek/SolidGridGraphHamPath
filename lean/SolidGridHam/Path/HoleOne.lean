/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
import SolidGridHam.Path.HoleTwo
import SolidGridHam.Path.HoleTryCost

/-!
# An inner endpoint, the other dangling: decided

`hpI1 V s t`: over the path's last edge `w–t` (each neighbour `w ≠ s` of `t`), take a reference
factor of `V.erase t` through `w–t`, and in each class (`classRange`) the factor `classSearchOne` returns, and run
the loop on `V.erase t` with phantom `t`. Correct when `t` is inner in the solid `V` and `s` is a
corner of no cell of `V.erase t` (`hpI1_correct`).
-/

namespace SolidGridHam

namespace HP

open Finset Classical

-- The box of a set connected by a Hamiltonian path is narrow (`narrow_of_ncomp`).
--
def isNarrow (U : Finset Pt) : Bool :=
  decide (bx1 U - bx0 U < U.card) && decide (by1 U - by0 U < U.card)

def hpI1 (V : Finset Pt) (s t : Pt) : Bool :=
  (nbrsL t).any fun x => decide (x.1 ∈ V) && decide (x.1 ≠ s) && isNarrow (V.erase t) &&
    match findFactor (V.erase t) (dST s x.1) with
    | none => false
    | some R => (classRange (V.erase t)).any fun h =>
        match classSearchOne (V.erase t) (insert x.2 R) t h with
        | some G => runSC (V.erase t) t ((V.erase t).card + 2) G
        | none => false

section holeOne

variable {V : Finset Pt} {s t : Pt}

-- A factor agreeing with a notch state off the inner edges is a notch state.
--
lemma notch_of_symm {U : Finset Pt} {p : Pt} {e0 : Edge} {F G : Finset Edge} (hpU : p ∉ U)
    (hF : NotchF U s p e0 F) (hG : IsFactor (insert p U) (dST s p) G)
    (hFG : ∀ e ∈ symmDiff F G, e.p ∈ U ∧ e.q ∈ U) : NotchF U s p e0 G := by
  refine ⟨hG, fun e he => ?_⟩
  rw [← hF.pat e he]
  constructor
  · intro h
    by_contra hn
    have := hFG e (Finset.mem_symmDiff.2 (Or.inr ⟨h, hn⟩))
    rcases he with h' | h'
    · exact hpU (h' ▸ this.1)
    · exact hpU (h' ▸ this.2)
  · intro h
    by_contra hn
    have := hFG e (Finset.mem_symmDiff.2 (Or.inl ⟨h, hn⟩))
    rcases he with h' | h'
    · exact hpU (h' ▸ this.1)
    · exact hpU (h' ▸ this.2)

end holeOne

end HP

end SolidGridHam
