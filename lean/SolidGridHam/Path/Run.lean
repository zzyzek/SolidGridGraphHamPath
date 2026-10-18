/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
module

public import SolidGridHam.Path.Cert

@[expose] public section

/-!
# Runs of equal arcs from a critical square

From a critical square `q` (frame `a`, dark back, light front), walk across the front while the
arcs across side `a` all point the same way. Degree 2 at the front corners forces the strip pattern
(`run_pat`): the lateral and front sides of `cellJ q a j` are dark exactly for odd `j`.
-/

namespace SolidGridHam

namespace HP

open Finset Classical

section run

variable {F : Finset Edge} {q : Pt} {a : Side}

-- Equal arcs across side `a` along the column: the fronts alternate, starting light.
--
lemma run_front (hf0 : front q a ∉ F) {j : ℕ}
    (harc : outArc F (cellJ q a j) a = outArc F q a) :
    front (cellJ q a j) a ∈ F ↔ j % 2 = 1 := by
  rw [outArc_eq, outArc_eq, par_cellJ] at harc
  have m0 : decide (sideEdge q a ∈ F) = false := by simp only [front] at hf0; simp [hf0]
  rw [m0] at harc
  simp only [front]
  constructor
  · intro h
    rw [show decide (sideEdge (cellJ q a j) a ∈ F) = true by simp [h]] at harc
    by_contra hj
    rw [show decide (j % 2 = 1) = false by simp [hj]] at harc
    cases par q <;> cases hh : a.horiz <;> simp [hh] at harc
  · intro hj
    rw [show decide (j % 2 = 1) = true by simp [hj]] at harc
    by_contra h
    rw [show decide (sideEdge (cellJ q a j) a ∈ F) = false by simp [h]] at harc
    cases par q <;> cases hh : a.horiz <;> simp [hh] at harc

-- **The strip pattern of a run.**
--
theorem run_pat (hcr : CriticalIn F q a) (hb : back q a ∈ F) {n : ℕ}
    (hdeg : ∀ j < n, deg F (front1 (cellJ q a j) a) = 2 ∧ deg F (front2 (cellJ q a j) a) = 2)
    (harc : ∀ j ≤ n, outArc F (cellJ q a j) a = outArc F q a) :
    ∀ j ≤ n, (lat1 (cellJ q a j) a ∈ F ↔ j % 2 = 1) ∧ (lat2 (cellJ q a j) a ∈ F ↔ j % 2 = 1) ∧
      (front (cellJ q a j) a ∈ F ↔ j % 2 = 1) := by
  obtain ⟨hbb, hff, hbf, hx⟩ := hcr
  have hf0 : front q a ∉ F := fun h => by
    rcases hx with ⟨_, h2⟩ | ⟨_, h1⟩
    · exact h2 h
    · exact h1 hb
  have hfr : ∀ j ≤ n, front (cellJ q a j) a ∈ F ↔ j % 2 = 1 := fun j hj =>
    run_front hf0 (harc j hj)
  intro j
  induction j with
  | zero =>
    intro _
    rw [cellJ_zero]
    refine ⟨⟨fun h => absurd ((ends_lat1 (c := q) (s := a)).conn h) hbf, fun h => by omega⟩,
      ⟨fun h => absurd (hbb.trans (((ends_lat2 (c := q) (s := a)).conn h).trans hff.symm)) hbf,
        fun h => by omega⟩, ?_⟩
    have := hfr 0 (by omega); rwa [cellJ_zero] at this
  | succ j ih =>
    intro hj
    obtain ⟨l1, l2, f1⟩ := ih (by omega)
    obtain ⟨d1, d2⟩ := hdeg j (by omega)
    rw [deg_front1, nb_cellJ] at d1
    rw [deg_front2, nb_cellJ] at d2
    refine ⟨?_, ?_, hfr (j + 1) hj⟩
    · rcases Nat.mod_two_eq_zero_or_one j with h | h
      · rw [ind_of_not_mem (fun h' => by have := l1.1 h'; omega),
          ind_of_not_mem (fun h' => by have := f1.1 h'; omega)] at d1
        have := ind_le_one F (lat1 (cellJ q a (j + 1)) a)
        have := ind_le_one F (outer1 (cellJ q a j) a)
        have hi : ind F (lat1 (cellJ q a (j + 1)) a) = 1 := by omega
        constructor
        · intro _; omega
        · intro _; unfold ind at hi; split_ifs at hi with hh; exact hh
      · rw [ind_of_mem (l1.2 h), ind_of_mem (f1.2 h)] at d1
        constructor
        · intro hh; rw [ind_of_mem hh] at d1; omega
        · intro hh; omega
    · rcases Nat.mod_two_eq_zero_or_one j with h | h
      · rw [ind_of_not_mem (fun h' => by have := l2.1 h'; omega),
          ind_of_not_mem (fun h' => by have := f1.1 h'; omega)] at d2
        have := ind_le_one F (lat2 (cellJ q a (j + 1)) a)
        have := ind_le_one F (outer2 (cellJ q a j) a)
        have hi : ind F (lat2 (cellJ q a (j + 1)) a) = 1 := by omega
        constructor
        · intro _; omega
        · intro _; unfold ind at hi; split_ifs at hi with hh; exact hh
      · rw [ind_of_mem (l2.2 h), ind_of_mem (f1.2 h)] at d2
        constructor
        · intro hh; rw [ind_of_mem hh] at d2; omega
        · intro hh; omega

end run

end HP

end SolidGridHam
