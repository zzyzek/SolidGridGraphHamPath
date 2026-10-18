/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
module

public import SolidGridHam.Path.HoleTwoVCost
public import SolidGridHam.Path.TwoPhWalkCost
public import SolidGridHam.Algorithm

@[expose] public section

/-!
# Hamiltonian `s`–`t` paths in solid grid graphs: decided in polynomial time

`decideHamPath` dispatches on whether each endpoint is inner (all four cells around it present):
* neither inner: both have a missing king neighbour, `boundaryEndpoints` (two phantoms and a deletion walk);
* exactly one inner: `oneHoleCase` (one hole, the walk on the other side);
* both inner: `twoHoleCase` (two holes).

`decideHamPath_main`: for solid `V` and distinct `s, t ∈ V`, `decideHamPath V s t = true` exactly when `V` has a
Hamiltonian `s`–`t` path, within `5 220 000 (|V| + 3)⁶` steps.
-/

namespace SolidGridHam

namespace HP

open Finset Classical

lemma isInner_iff {V : Finset Pt} {p : Pt} : isInner V p = true ↔ Inner V p := by
  simp only [isInner, Inner, Bool.and_eq_true, decide_eq_true_eq, and_assoc]

-- A point of `V` that is not inner has a missing king neighbour.
--
lemma miss_of_not_inner {V : Finset Pt} {p : Pt} (hp : ¬ Inner V p) :
    ∃ m, m ∉ V ∧ |m.1 - p.1| ≤ 1 ∧ |m.2 - p.2| ≤ 1 := by
  by_contra h
  push Not at h
  have hin : ∀ i j : ℤ, |i| ≤ 1 → |j| ≤ 1 → (p.1 + i, p.2 + j) ∈ V := by
    intro i j hi hj
    by_contra hm
    have := h _ hm (by simpa using hi)
    simp only [add_sub_cancel_left] at this
    exact absurd hj (not_le.2 this)
  apply hp
  obtain ⟨x, y⟩ := p
  have g : ∀ a b : ℤ, |a - x| ≤ 1 → |b - y| ≤ 1 → (a, b) ∈ V := by
    intro a b ha hb
    have := hin (a - x) (b - y) ha hb
    simpa using this
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩⟩ <;>
    apply g <;> simp

noncomputable def decideHamPathCost (V : Finset Pt) (s t : Pt) : ℕ :=
  10 + if isInner V s then (if isInner V t then twoHoleCaseCost V s t else oneHoleCaseCost V t s)
    else if isInner V t then oneHoleCaseCost V s t else boundaryEndpointsCost V s t

section final

variable {V : Finset Pt} {s t : Pt}

-- **Hamiltonian `s`–`t` paths in solid grid graphs are decided in polynomial time.** For solid `V`
-- and distinct `s, t ∈ V`, `decideHamPath V s t = true` exactly when `V` has a Hamiltonian `s`–`t` path
-- (a spanning subgraph with degree 1 at `s` and `t`, degree 2 elsewhere, and one component), and
-- `decideHamPath` takes at most `5 220 000 (|V| + 3)⁶` steps.
--
theorem decideHamPath_main (hs : Solid V) (hst : s ≠ t) (hsV : s ∈ V) (htV : t ∈ V) :
    (decideHamPath V s t = true ↔ ∃ H, IsFactor V (dST s t) H ∧ ncomp V H = 1) ∧
      decideHamPathCost V s t ≤ 5220000 * (V.card + 3) ^ 6 := by
  have p68 : (V.card + 3) ^ 4 ≤ (V.card + 3) ^ 6 := Nat.pow_le_pow_right (by omega) (by omega)
  have p89 : (V.card + 3) ^ 5 ≤ (V.card + 3) ^ 6 := Nat.pow_le_pow_right (by omega) (by omega)
  have p0 : 1 ≤ (V.card + 3) ^ 6 := Nat.one_le_pow _ _ (by omega)
  have q6 : 1060000 * (V.card + 3) ^ 4 + 10 ≤ 5220000 * (V.card + 3) ^ 6 := by omega
  have q8 : (208 * 12000 + 17000) * (V.card + 3) ^ 5 + 10 ≤ 5220000 * (V.card + 3) ^ 6 := by
    omega
  have q9 : (208 * 25000 + 17000) * (V.card + 3) ^ 6 + 10 ≤ 5220000 * (V.card + 3) ^ 6 := by
    omega
  unfold decideHamPath decideHamPathCost
  by_cases hs1 : isInner V s = true
  · have hsI := isInner_iff.1 hs1
    rw [ite_eq_left hs1, ite_eq_left hs1]
    by_cases ht1 : isInner V t = true
    · have htI := isInner_iff.1 ht1
      rw [ite_eq_left ht1, ite_eq_left ht1]
      obtain ⟨c1, c2⟩ := twoHoleCase_main hs htI hsI hst
      exact ⟨c1, by omega⟩
    · have htm := miss_of_not_inner (fun h => ht1 (isInner_iff.2 h))
      rw [ite_eq_right ht1, ite_eq_right ht1]
      obtain ⟨c1, c2⟩ := oneHoleCase_main hs hsI (Ne.symm hst) htV htm
      exact ⟨by rw [c1, hp_swap], by omega⟩
  · have hsm := miss_of_not_inner (fun h => hs1 (isInner_iff.2 h))
    rw [ite_eq_right hs1, ite_eq_right hs1]
    by_cases ht1 : isInner V t = true
    · have htI := isInner_iff.1 ht1
      rw [ite_eq_left ht1, ite_eq_left ht1]
      obtain ⟨c1, c2⟩ := oneHoleCase_main hs htI hst hsV hsm
      exact ⟨c1, by omega⟩
    · have htm := miss_of_not_inner (fun h => ht1 (isInner_iff.2 h))
      rw [ite_eq_right ht1, ite_eq_right ht1]
      obtain ⟨c1, c2⟩ := boundaryEndpoints_main hs hst hsV htV hsm htm
      exact ⟨c1, by omega⟩

-- **Correctness alone** (the statement registered with Palomar, `Challenge.lean`): for solid `V`
-- and distinct `s, t ∈ V`, `decideHamPath V s t = true` exactly when `V` has a Hamiltonian
-- `s`–`t` path.
--
theorem decideHamPath_correct (hs : Solid V) (hst : s ≠ t) (hsV : s ∈ V) (htV : t ∈ V) :
    decideHamPath V s t = true ↔ ∃ H, IsFactor V (dST s t) H ∧ ncomp V H = 1 :=
  (decideHamPath_main hs hst hsV htV).1

end final

end HP

end SolidGridHam
