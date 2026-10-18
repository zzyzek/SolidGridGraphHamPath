/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
module

public import SolidGridHam.Cycle.Reroute

@[expose] public section

/-!
# Strip counts without the Type III hypothesis

* `strip_odd_conn`: an odd strip whose first back and front corners are already joined
  raises the count by one.
* `strip_even_gen`: an even strip whose start separates changes the count by 0 or −2
  (−2 when the end cell is a Type III cell).
-/

namespace SolidGridHam

open Finset Classical

section counts

variable {V : Finset Pt} {c : Pt} {s : Side}

theorem strip_odd_conn : ∀ k : ℕ, k % 2 = 0 → ∀ F : Finset Edge, Deg2 V F →
    (∀ j ≤ k, IsCell V (cellJ c s j)) → StripPat F c s (k + 1) →
    Conn F (back1 c s) (front1 c s) → ncomp V (flipCol F c s (k + 1)) = ncomp V F + 1 := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro hk F hF hcell hpat hsep
  rcases (show k = 0 ∨ 2 ≤ k by omega) with rfl | hk2
  · -- One alternating cell: a merge.
    rw [flipCol_succ]
    simp only [flipCol]
    rw [cellJ_zero]
    have hc : IsCell V c := by have := hcell 0 le_rfl; rwa [cellJ_zero] at this
    obtain ⟨hb, hl, hf⟩ := hpat
    have l1 := (hl 0 (by omega)).1
    have l2 := (hl 0 (by omega)).2
    have f0 := hf 0 (by omega)
    rw [cellJ_zero] at l1 l2 f0
    simp at l1 l2 f0
    have C := mkBF c s
    rw [(mkBF c s).flip_eq (mkBF_cellE c s) hb f0 l1 l2]
    obtain ⟨cb1, cb2, cf1, cf2⟩ := isCell_corners hc s
    exact ((mkBF c s).split hF.1 cb1 cb2 cf1 cf2 hb f0 l1
      (fun z hz => by rcases hz with hz | hz
                      · exact hF.class cb1 hz
                      · exact hF.class cf1 hz) hsep hF.le_two
      (fun G h1 h2 h3 h4 h5 => planar_lat G c s h2 h1 h3.symm h4 (fun h => h5 (h.trans h3.symm)))).1
  · -- Two more cells: the pair changes nothing.
    obtain ⟨m, rfl⟩ : ∃ m, k = m + 2 := ⟨k - 2, by omega⟩
    have hm : m % 2 = 0 := by omega
    rw [show m + 2 + 1 = m + 3 from rfl, flipCol_succ, flipCol_succ]
    set u := cellJ c s (m + 1)
    have hnb : nb u s = cellJ c s (m + 2) := nb_cellJ c s (m + 1)
    obtain ⟨hb, hl, hf⟩ := hpat
    -- Memberships around the pair.
    have uL1 : lat1 u s ∈ F := (hl (m + 1) (by omega)).1.2 (by omega)
    have uL2 : lat2 u s ∈ F := (hl (m + 1) (by omega)).2.2 (by omega)
    have uF : front u s ∈ F := (hf (m + 1) (by omega)).2 (by omega)
    have uB : back u s ∉ F := by
      rw [back_cellJ_succ]
      intro h; have := (hf m (by omega)).1 h; omega
    have wL1 : lat1 (nb u s) s ∉ F := by
      rw [hnb]; intro h; have := (hl (m + 2) (by omega)).1.1 h; omega
    have wL2 : lat2 (nb u s) s ∉ F := by
      rw [hnb]; intro h; have := (hl (m + 2) (by omega)).2.1 h; omega
    have wF : front (nb u s) s ∈ F := by
      rw [hnb]; exact (hf (m + 2) (by omega)).2 (by omega)
    have hdouble : flip (flip F (cellJ c s (m + 2))) (cellJ c s (m + 1)) = (mkPair u s).res F := by
      rw [← hnb]; exact pair_flip_eq u s uL1 uL2 wF uB wL1 wL2
    have hcu : IsCell V u := hcell (m + 1) (by omega)
    have hcw : IsCell V (nb u s) := by rw [hnb]; exact hcell (m + 2) (by omega)
    obtain ⟨ub1, ub2, uf1, uf2⟩ := isCell_corners hcu s
    obtain ⟨_, _, wf1, wf2⟩ := isCell_corners hcw s
    obtain ⟨hcount, hrel⟩ := (mkPair u s).flip ub2 uf1 uf2 wf1 uL1 uL2 uF wF
      (hF.2 _ uf1) (hF.2 _ uf2)
    -- The new factor.
    rw [hdouble]
    have hF2' : Deg2 V ((mkPair u s).res F) := by
      rw [← hdouble]
      have hw : cellJ c s (m + 2) = nb u s := hnb.symm
      have d1 : Deg2 V (flip F (cellJ c s (m + 2))) := by
        rw [hw]
        exact hF.flip (mkBF (nb u s) s) hcw (mkBF_cellE _ s)
          (by show back (nb u s) s ∈ F; rw [back_nb]; exact uF) wF wL1 wL2
      have m1 : lat1 u s ∈ flip F (cellJ c s (m + 2)) := by
        rw [mem_flip_iff]; have := lat1_not_mem c s (j := m + 1) (m := m + 2) (by omega); tauto
      have m2 : lat2 u s ∈ flip F (cellJ c s (m + 2)) := by
        rw [mem_flip_iff]; have := lat2_not_mem c s (j := m + 1) (m := m + 2) (by omega); tauto
      have m3 : back u s ∉ flip F (cellJ c s (m + 2)) := by
        rw [mem_flip_iff, back_cellJ_succ]
        have := front_not_mem c s (j := m) (m := m + 2) (by omega) (by omega)
        rw [back_cellJ_succ] at uB; tauto
      have m4 : front u s ∉ flip F (cellJ c s (m + 2)) := by
        rw [mem_flip_iff]; have := front_mem_next c s (m + 1); tauto
      exact d1.flip (mkLat u s) hcu (mkLat_cellE u s) m1 m2 m3 m4
    have hpat2 : StripPat ((mkPair u s).res F) c s (m + 1) := by
      rw [← hdouble]; exact pat_flip_pair hm ⟨hb, hl, hf⟩
    have hsep2 : Conn ((mkPair u s).res F) (back1 c s) (front1 c s) := by
      obtain ⟨n1, n2, n3, n4⟩ := corner_ne c s (m := m + 1) (by omega)
      rw [hrel _ _ n1 n2 n3 n4]; exact hsep
    have := ih m (by omega) hm _ hF2' (fun j hj => hcell j (by omega)) hpat2 hsep2
    omega

theorem strip_even_gen (k : ℕ) (hk : k % 2 = 0) (F : Finset Edge) (hF : Deg2 V F)
    (hcell : ∀ j ≤ k + 1, IsCell V (cellJ c s j)) (hpat : StripPat F c s (k + 2))
    (hsep : ¬ Conn F (back1 c s) (front1 c s)) :
    ncomp V (flipCol F c s (k + 2)) = ncomp V F ∨
      ncomp V (flipCol F c s (k + 2)) + 2 = ncomp V F := by
  by_cases hsame : Conn F (back1 (cellJ c s (k + 1)) s) (back2 (cellJ c s (k + 1)) s)
  · exact Or.inl (strip_even k hk F hF hcell hpat hsep hsame)
  rw [flipCol_succ]
  set u := cellJ c s (k + 1)
  obtain ⟨hb, hl, hf⟩ := hpat
  have uL1 : lat1 u s ∈ F := (hl (k + 1) (by omega)).1.2 (by omega)
  have uL2 : lat2 u s ∈ F := (hl (k + 1) (by omega)).2.2 (by omega)
  have uB : back u s ∉ F := by
    rw [back_cellJ_succ]; intro h; have := (hf k (by omega)).1 h; omega
  have uF : front u s ∉ F := by
    intro h; have := (hf (k + 1) (by omega)).1 h; omega
  have hcu : IsCell V u := hcell (k + 1) le_rfl
  obtain ⟨ub1, ub2, uf1, uf2⟩ := isCell_corners hcu s
  have hE := mkLat_cellE u s
  rw [(mkLat u s).flip_eq hE uL1 uL2 uB uF]
  obtain ⟨hcount, hrel⟩ := (mkLat u s).merge hF.1 ub1 ub2 uL1 uL2
    (fun z hz => by rcases hz with hz | hz
                    · exact hF.class ub1 hz
                    · exact hF.class ub2 hz) hsame
  have hF' : Deg2 V ((mkLat u s).res F) := by
    rw [← (mkLat u s).flip_eq hE uL1 uL2 uB uF]
    exact hF.flip (mkLat u s) hcu hE uL1 uL2 uB uF
  have hpat' : StripPat ((mkLat u s).res F) c s (k + 1) := by
    rw [← (mkLat u s).flip_eq hE uL1 uL2 uB uF]; exact pat_flip_last hk ⟨hb, hl, hf⟩
  by_cases hsep' : Conn ((mkLat u s).res F) (back1 c s) (front1 c s)
  · have := strip_odd_conn k hk _ hF' (fun j hj => hcell j (by omega)) hpat' hsep'
    left; omega
  · have := (strip_odd k hk _ hF' (fun j hj => hcell j (by omega)) hpat' hsep').1
    right; omega

end counts

end SolidGridHam
