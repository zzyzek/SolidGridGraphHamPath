/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
module

public import SolidGridHam.Path.SheffBoundary

@[expose] public section

/-!
# One dangling endpoint, the other on the boundary

`hpD V s t` decides the Hamiltonian `s`–`t` path problem when one endpoint is a corner of no cell
and the other has a missing king neighbour (in either order: a path read backwards swaps its
endpoints). Correct and polynomial (`hpD_main`).
-/

namespace SolidGridHam

namespace HP

open Finset Classical

-- `z` is a corner of no cell of `V`.
--
def danglingB (V : Finset Pt) (z : Pt) : Bool :=
  !(decide (IsCell V z) || decide (IsCell V (z.1 - 1, z.2)) || decide (IsCell V (z.1, z.2 - 1)) ||
    decide (IsCell V (z.1 - 1, z.2 - 1)))

def kingOff : List (ℤ × ℤ) := [(-1, -1), (-1, 0), (-1, 1), (0, -1), (0, 1), (1, -1), (1, 0), (1, 1)]

-- `z` has a missing king neighbour.
--
def bdB (V : Finset Pt) (z : Pt) : Bool := kingOff.any fun d => decide ((z.1 + d.1, z.2 + d.2) ∉ V)

lemma danglingB_iff {V : Finset Pt} {z : Pt} :
    danglingB V z = true ↔ ∀ c, IsCell V c → ¬ IsCorner z c := by
  obtain ⟨x, y⟩ := z
  unfold danglingB
  simp only [Bool.not_eq_true', Bool.or_eq_false_iff, decide_eq_false_iff_not]
  constructor
  · rintro ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ ⟨u, v⟩ hc hz
    unfold IsCorner at hz
    simp only [Prod.mk.injEq] at hz
    rcases hz with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact h1 hc
    · exact h2 (by simpa using hc)
    · exact h3 (by simpa using hc)
    · exact h4 (by simpa using hc)
  · intro h
    refine ⟨⟨⟨fun hc => h _ hc (Or.inl rfl), fun hc => h _ hc ?_⟩, fun hc => h _ hc ?_⟩,
      fun hc => h _ hc ?_⟩
    · right; left; simp
    · right; right; left; simp
    · right; right; right; simp

lemma bdB_iff {V : Finset Pt} {z : Pt} (hz : z ∈ V) :
    bdB V z = true ↔ ∃ q, q ∉ V ∧ |q.1 - z.1| ≤ 1 ∧ |q.2 - z.2| ≤ 1 := by
  obtain ⟨x, y⟩ := z
  unfold bdB
  rw [List.any_eq_true]
  constructor
  · rintro ⟨d, hd, hq⟩
    simp only [decide_eq_true_eq] at hq
    refine ⟨_, hq, ?_, ?_⟩ <;>
    · simp only [kingOff, List.mem_cons, List.not_mem_nil, or_false] at hd
      rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · rintro ⟨⟨u, v⟩, hq, hx, hy⟩
    simp only at hx hy
    rw [abs_le] at hx hy
    have hne : (u, v) ≠ (x, y) := fun h => hq (h ▸ hz)
    refine ⟨(u - x, v - y), ?_, by simp only [decide_eq_true_eq]; ring_nf; exact hq⟩
    simp only [kingOff, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq]
    simp only [ne_eq, Prod.mk.injEq, not_and] at hne
    omega

def hpD (V : Finset Pt) (s t : Pt) : Bool :=
  if danglingB V s && bdB V t then hpB V s t
  else if danglingB V t && bdB V s then hpB V t s
  else false

def hpDCost (V : Finset Pt) (s t : Pt) : ℕ :=
  40 +
    if danglingB V s && bdB V t then hpBCost V s t
    else if danglingB V t && bdB V s then hpBCost V t s
    else 0

section endpoints

variable {V : Finset Pt} {s t : Pt}

lemma three_of_card (h : 3 ≤ V.card) (s t : Pt) : ∃ z ∈ V, z ≠ s ∧ z ≠ t := by
  have h1 : 1 ≤ ((V.erase s).erase t).card := by
    have a := Finset.pred_card_le_card_erase (s := V) (a := s)
    have b := Finset.pred_card_le_card_erase (s := V.erase s) (a := t)
    omega
  obtain ⟨z, hz⟩ := Finset.card_pos.1 (show 0 < ((V.erase s).erase t).card by omega)
  simp only [Finset.mem_erase] at hz
  exact ⟨z, hz.2.2, hz.2.1, hz.1⟩

lemma hp_swap : (∃ H, IsFactor V (dST s t) H ∧ ncomp V H = 1) ↔
    ∃ H, IsFactor V (dST t s) H ∧ ncomp V H = 1 := by
  rw [dST_comm]

end endpoints

end HP

end SolidGridHam
