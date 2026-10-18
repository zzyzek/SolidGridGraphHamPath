/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
import ULHC.HP.Sheffield.SheffBoundary

/-!
# One dangling endpoint, the other on the boundary

`hpD V s t` decides the Hamiltonian `s`–`t` path problem when one endpoint is a corner of no cell
and the other has a missing king neighbour (in either order: a path read backwards swaps its
endpoints). Correct and polynomial (`hpD_main`).
-/

namespace ULHC

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

-- **One dangling endpoint, the other on the boundary.**
--
theorem hpD_main (hs : Solid V) (hst : s ≠ t) (hsV : s ∈ V) (htV : t ∈ V) (h3 : 3 ≤ V.card)
    (hcov : (danglingB V s = true ∧ bdB V t = true) ∨ (danglingB V t = true ∧ bdB V s = true)) :
    (hpD V s t = true ↔ ∃ H, IsFactor V (dST s t) H ∧ ncomp V H = 1) ∧
      hpDCost V s t ≤ 60000 * (V.card + 2) ^ 6 := by
  have a0 : 1 ≤ (V.card + 2) ^ 6 := Nat.one_le_pow _ _ (by omega)
  unfold hpD hpDCost
  by_cases h1 : danglingB V s = true ∧ bdB V t = true
  · have hb : (danglingB V s && bdB V t) = true := by simp [h1.1, h1.2]
    simp only [hb, ↓reduceIte]
    obtain ⟨q, hq, hqx, hqy⟩ := (bdB_iff htV).1 h1.2
    obtain ⟨c1, c2⟩ := hpB_main hs hst htV (danglingB_iff.1 h1.1) hq hqx hqy (three_of_card h3 s t)
    exact ⟨c1, by omega⟩
  · have h2 : danglingB V t = true ∧ bdB V s = true := hcov.resolve_left h1
    have hb : (danglingB V s && bdB V t) = false := by
      cases ha : danglingB V s <;> cases hb : bdB V t <;> simp_all
    have hb2 : (danglingB V t && bdB V s) = true := by simp [h2.1, h2.2]
    simp only [hb, hb2, Bool.false_eq_true, ↓reduceIte]
    obtain ⟨q, hq, hqx, hqy⟩ := (bdB_iff hsV).1 h2.2
    obtain ⟨c1, c2⟩ := hpB_main hs (Ne.symm hst) hsV (danglingB_iff.1 h2.1) hq hqx hqy
      (by obtain ⟨z, hz, a, b⟩ := three_of_card h3 s t; exact ⟨z, hz, b, a⟩)
    rw [c1, ← hp_swap]
    exact ⟨Iff.rfl, by omega⟩

end endpoints

end HP

end ULHC
