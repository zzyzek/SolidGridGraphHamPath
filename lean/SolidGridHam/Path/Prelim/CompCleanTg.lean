/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
import SolidGridHam.Cycle.NearCA
import SolidGridHam.Cycle.NearLemma
import SolidGridHam.Cycle.NearGeo
import SolidGridHam.Cycle.NearChain
import SolidGridHam.Cycle.Touch
import SolidGridHam.Cycle.L57
import SolidGridHam.Cycle.Near
import SolidGridHam.Path.Prelim.RelPF
import SolidGridHam.Cycle.PathComplete
import SolidGridHam.Cycle.Algorithm
import SolidGridHam.Cycle.Phase2
import SolidGridHam.Path.Prelim.TheoremAPF
import SolidGridHam.Cycle.Stacked

/-!
# `comp_clean` for path-factors with rule Tg

ULHC's `PathComplete` source/via lemmas and `comp_clean`, for path-factors, restricted strips,
count-neutral strips and Tg chains (`RPathTg`). The cells next to the strip where ULHC uses
"not Type III" and which may be endpoint cells are hypotheses E1, E2, E3.
-/

namespace SolidGridHam

namespace HP

open Finset Classical

-- **A strip flip keeps every degree.**
--
lemma degs_flipCol {V : Finset Pt} {c : Pt} {s : Side} :
    ∀ n (F : Finset Edge), Inside V F → StripPat F c s n → (∀ j < n, IsCell V (cellJ c s j)) →
      Inside V (flipCol F c s n) ∧ ∀ z, deg (flipCol F c s n) z = deg F z := by
  intro n
  induction n with
  | zero => intro F hF _ _; exact ⟨hF, fun _ => rfl⟩
  | succ n ih =>
    intro F hF hpat hcell
    rw [flipCol_succ]
    have hce := hcell n (by omega)
    obtain ⟨hb, hl, hf⟩ := hpat
    have mF : front (cellJ c s n) s ∈ F ↔ n % 2 = 0 := by
      have := hf n (by omega); simp only [lt_self_iff_false, iff_false] at this; rw [this]; omega
    have mB : back (cellJ c s n) s ∈ F ↔ n % 2 = 0 := by
      rcases n with _ | n
      · simp only [cellJ_zero]; simp [hb]
      · rw [back_cellJ_succ]
        have := hf n (by omega)
        have q : n + 1 < n + 1 + 1 := by omega
        simp only [q, iff_true] at this
        rw [this]; omega
    have mL1 := (hl n (by omega)).1
    have mL2 := (hl n (by omega)).2
    have hF' : Inside V (SolidGridHam.flip F (cellJ c s n)) ∧
        ∀ z, deg (SolidGridHam.flip F (cellJ c s n)) z = deg F z := by
      refine ⟨inside_flip hF hce, fun z => ?_⟩
      rcases Nat.mod_two_eq_zero_or_one n with h | h
      · have n1 : lat1 (cellJ c s n) s ∉ F := fun h' => by have := mL1.1 h'; omega
        have n2 : lat2 (cellJ c s n) s ∉ F := fun h' => by have := mL2.1 h'; omega
        rw [(mkBF _ s).flip_eq (mkBF_cellE _ s) (mB.2 h) (mF.2 h) n1 n2,
          (mkBF _ s).deg_res (mB.2 h) (mF.2 h) n1 n2]
      · have n1 : back (cellJ c s n) s ∉ F := fun h' => by have := mB.1 h'; omega
        have n2 : front (cellJ c s n) s ∉ F := fun h' => by have := mF.1 h'; omega
        rw [(mkLat _ s).flip_eq (mkLat_cellE _ s) (mL1.2 h) (mL2.2 h) n1 n2,
          (mkLat _ s).deg_res (mL1.2 h) (mL2.2 h) n1 n2]
    rcases n with _ | n
    · simpa [flipCol] using hF'
    · obtain ⟨h1, h2⟩ := ih _ hF'.1 (pat_flip_end ⟨hb, hl, hf⟩) (fun j hj => hcell j (by omega))
      exact ⟨h1, fun z => (h2 z).trans (hF'.2 z)⟩

-- Neighbours commute.
--
lemma nb_nb_comm (z : Pt) (s s' : Side) : nb (nb z s) s' = nb (nb z s') s := by
  obtain ⟨x, y⟩ := z
  cases s <;> cases s' <;> simp only [nb] <;> ring_nf

end HP

end SolidGridHam
