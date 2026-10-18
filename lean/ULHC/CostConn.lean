/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
import ULHC.Algorithm

/-!
# Running time, part 1: the cost model and reachability

## Cost model

The step counts are defined by the counted algorithm `T.ulhcT` (`Timed/`), built from the
counted operations of `Timed/TimeM.lean` (the cost model is the table there). The cost
functions in `Cost*.lean` are upper bounds: each counted function is proved to take at most its
cost function's value (`T.fooT_time_le`), and the cost functions are bounded by polynomials in
`N = |V| + 1` here.

## This file

* `fnbrCost`, `creachCost`, `cclsCost`, `connBCost`, `cncompCost`: breadth-first search.
* `card_creach_le`: inside a factor of `V`, a reachable set has at most `|V| + 1` points.
* `creachCost_le`, `connBCost_le : connBCost ≤ 30 N²`, `cncompCost_le : cncompCost ≤ 32 N³`.
-/

namespace ULHC

open Finset

/-! ## Breadth-first search -/

-- `fnbr F u`: four membership tests, four `other`s, a set of at most four points.
--
def fnbrCost : ℕ := 20

lemma card_fnbr_le (F : Finset Edge) (u : Pt) : (fnbr F u).card ≤ 4 := by
  unfold fnbr
  refine (List.toFinset_card_le _).trans ?_
  rw [List.length_map]
  exact (List.length_filter_le _ _).trans (by simp [TF.inc4])

-- One round: the neighbour sets of the current set, and the union.
--
def creachCost (F : Finset Edge) (x : Pt) : ℕ → ℕ
  | 0 => 1
  | k + 1 =>
    creachCost F x k + ∑ u ∈ creach F x k, (fnbrCost + (fnbr F u).card) +
      (creach F x k).card + ((creach F x k).biUnion (fnbr F)).card

def cclsCost (V : Finset Pt) (F : Finset Edge) (x : Pt) : ℕ := creachCost F x V.card + V.card + 1

def connBCost (V : Finset Pt) (F : Finset Edge) (x : Pt) : ℕ := cclsCost V F x + 1

-- `cncomp`: one class per point of `V`, inserted into a set of classes, then counted.
--
def cncompCost (V : Finset Pt) (F : Finset Edge) : ℕ :=
  ∑ x ∈ V, (cclsCost V F x + (ccls V F x).card + 1) + V.card + 1

lemma fnbr_sub {V : Finset Pt} {F : Finset Edge} (hFV : Inside V F) (u : Pt) : fnbr F u ⊆ V := by
  intro z hz
  simp only [fnbr, List.mem_toFinset, List.mem_map, List.mem_filter, decide_eq_true_eq] at hz
  obtain ⟨e, ⟨_, he⟩, rfl⟩ := hz
  rcases (other_inc (e := e) (y := u)) with h | h
  · rw [← h]; exact (hFV e he).1
  · rw [← h]; exact (hFV e he).2

lemma creach_subI {V : Finset Pt} {F : Finset Edge} (hFV : Inside V F) (x : Pt) :
    ∀ k, creach F x k ⊆ insert x V := by
  intro k
  induction k with
  | zero => simp [creach]
  | succ k ih =>
    intro z hz
    simp only [creach, mem_union, mem_biUnion] at hz
    rcases hz with hz | ⟨u, _, hz⟩
    · exact ih hz
    · exact mem_insert_of_mem (fnbr_sub hFV u hz)

lemma card_creach_le {V : Finset Pt} {F : Finset Edge} (hFV : Inside V F) (x : Pt) (k : ℕ) :
    (creach F x k).card ≤ V.card + 1 :=
  (card_le_card (creach_subI hFV x k)).trans (card_insert_le _ _)

lemma creachCost_le {V : Finset Pt} {F : Finset Edge} (hFV : Inside V F) (x : Pt) :
    ∀ k, creachCost F x k ≤ 1 + 29 * (V.card + 1) * k := by
  intro k
  induction k with
  | zero => simp [creachCost]
  | succ k ih =>
    simp only [creachCost]
    set C := creach F x k
    have hC : C.card ≤ V.card + 1 := card_creach_le hFV x k
    have h1 : ∑ u ∈ C, (fnbrCost + (fnbr F u).card) ≤ C.card * 24 := by
      have := Finset.sum_le_card_nsmul C (fun u => fnbrCost + (fnbr F u).card) 24
        (fun u _ => by have := card_fnbr_le F u; unfold fnbrCost; omega)
      simpa using this
    have h2 : (C.biUnion (fnbr F)).card ≤ C.card * 4 := by
      refine card_biUnion_le.trans ?_
      have := Finset.sum_le_card_nsmul C (fun u => (fnbr F u).card) 4
        (fun u _ => card_fnbr_le F u)
      simpa using this
    nlinarith

lemma connBCost_le {V : Finset Pt} {F : Finset Edge} (hFV : Inside V F) (x : Pt) :
    connBCost V F x ≤ 30 * (V.card + 1) ^ 2 := by
  unfold connBCost cclsCost
  have := creachCost_le hFV x V.card
  nlinarith

lemma cncompCost_le {V : Finset Pt} {F : Finset Edge} (hFV : Inside V F) :
    cncompCost V F ≤ 32 * (V.card + 1) ^ 3 := by
  unfold cncompCost
  have h : ∑ x ∈ V, (cclsCost V F x + (ccls V F x).card + 1) ≤
      V.card * (30 * (V.card + 1) ^ 2 + (V.card + 1)) := by
    have := Finset.sum_le_card_nsmul V (fun x => cclsCost V F x + (ccls V F x).card + 1)
      (30 * (V.card + 1) ^ 2 + (V.card + 1)) (fun x _ => by
        have h1 := connBCost_le hFV x
        have h2 := card_creach_le hFV x V.card
        unfold connBCost at h1; unfold ccls; omega)
    simpa using this
  nlinarith

end ULHC
