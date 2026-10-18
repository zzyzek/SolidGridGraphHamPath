/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
import ULHC.HP.Sheffield.HoleOneCost

/-!
# An inner endpoint, the other exposed

If `s` has an exposed missing neighbour `q`, adding `q` as a pendant keeps `V` solid, makes `q` a
corner of no cell, and keeps `t` inner; so `hpI1` on `V ∪ {q}` with endpoint `q` decides the
problem (`hpIX_main`).
-/

namespace ULHC

namespace HP

open Finset Classical

def hpIX (V : Finset Pt) (s t : Pt) : Bool :=
  match exposedB V s with
  | some x => hpI1 (insert x.1 V) x.1 t
  | none => false

noncomputable def hpIXCost (V : Finset Pt) (s t : Pt) : ℕ :=
  20 + match exposedB V s with
  | some x => hpI1Cost (insert x.1 V) x.1 t
  | none => 0

section exposedI

variable {V : Finset Pt} {s t : Pt}

-- **An inner endpoint, the other exposed: decided in polynomial time.**
--
theorem hpIX_main (hs : Solid V) (ht : Inner V t) (hst : s ≠ t) (hsV : s ∈ V) (h2 : 2 ≤ V.card)
    {x : Pt × Edge} (hx : exposedB V s = some x) :
    (hpIX V s t = true ↔ ∃ H, IsFactor V (dST s t) H ∧ ncomp V H = 1) ∧
      hpIXCost V s t ≤ 60000 * (V.card + 4) ^ 8 := by
  obtain ⟨hq, hends, hpe⟩ := exposedB_some hx
  have hsol := pendant_solid hq hsV hends hpe hs
  have htV : t ∈ V := ht.2.2.2.1
  have hqt : x.1 ≠ t := fun h => hq (h ▸ htV)
  have ht' : Inner (insert x.1 V) t := by
    obtain ⟨i1, i2, i3, i4⟩ := ht
    exact ⟨isCell_mono i1 (Finset.subset_insert _ _), isCell_mono i2 (Finset.subset_insert _ _),
      isCell_mono i3 (Finset.subset_insert _ _), isCell_mono i4 (Finset.subset_insert _ _)⟩
  have hsD : ∀ c, IsCell ((insert x.1 V).erase t) c → ¬ IsCorner x.1 c := fun c hc =>
    pendant_not_corner hpe (isCell_mono hc (Finset.erase_subset _ _))
  have h3 : 3 ≤ (insert x.1 V).card := by rw [Finset.card_insert_of_notMem hq]; omega
  obtain ⟨c1, c2⟩ := hpI1_main hsol ht' hqt hsD h3
  have hc : (insert x.1 V).card = V.card + 1 := Finset.card_insert_of_notMem hq
  refine ⟨?_, ?_⟩
  · unfold hpIX; rw [hx]; simp only
    rw [c1, ← hp_pendS hst hsV htV hx]
  · unfold hpIXCost; rw [hx]; simp only
    rw [hc, show V.card + 1 + 3 = V.card + 4 by omega] at c2
    have : 1 ≤ (V.card + 4) ^ 8 := Nat.one_le_pow _ _ (by omega)
    omega

end exposedI

end HP

end ULHC
