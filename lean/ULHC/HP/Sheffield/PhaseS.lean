/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
import ULHC.HP.Sheffield.ConnSet

/-!
# The phase with connections computed once per step

`runPhase` is `phase` with every connection test of a step answered by one membership test in
`connectedPairs W H`, built once at the start of the step. It returns exactly what `phase` returns on
states inside `W` (`runPhase_eq`).
-/

namespace ULHC

namespace HP

open Finset Classical

lemma find?_congr {α : Type*} {p q : α → Bool} :
    ∀ {l : List α}, (∀ x ∈ l, p x = q x) → l.find? p = l.find? q
  | [], _ => rfl
  | x :: l, h => by
    simp only [List.find?_cons]
    rw [h x (by simp), find?_congr (fun y hy => h y (by simp [hy]))]

lemma findSome?_congr {α β : Type*} {f g : α → Option β} :
    ∀ {l : List α}, (∀ x ∈ l, f x = g x) → l.findSome? f = l.findSome? g
  | [], _ => rfl
  | x :: l, h => by
    simp only [List.findSome?_cons]
    rw [h x (by simp), findSome?_congr (fun y hy => h y (by simp [hy]))]

def isCutCell (S : Finset (Pt × Pt)) (c : Pt) : Bool :=
  !(isConnected S c (c.1 + 1, c.2) && isConnected S c (c.1 + 1, c.2 + 1) && isConnected S c (c.1, c.2 + 1))

def findMergingCell (V : Finset Pt) (S : Finset (Pt × Pt)) (H : Finset Edge) (BS : List Bridge) :
    Option Pt :=
  (cellList V).find? fun c => decide (Alt H c) && isCutCell S c && !pairSqB BS c

def isCritical (S : Finset (Pt × Pt)) (H : Finset Edge) (q : Pt) (a : Side) : Bool :=
  isConnected S (back1 q a) (back2 q a) && isConnected S (front1 q a) (front2 q a) &&
    !isConnected S (back1 q a) (front1 q a) && decide (back q a ∈ H) && decide (front q a ∉ H)

def scanRowAux (V : Finset Pt) (S : Finset (Pt × Pt)) (H : Finset Edge) (q : Pt) (a : Side)
    (o : Bool) : ℕ → ℕ → Option RunEnd
  | 0, _ => none
  | fuel + 1, j =>
    if outArc H (cellJ q a (j - 1)) a ≠ o then some (.row j)
    else if ¬ IsCell V (cellJ q a j) ∨ isCutCell S (cellJ q a j) = true then some (.stuck j)
    else scanRowAux V S H q a o fuel (j + 1)

def scanRow (V : Finset Pt) (S : Finset (Pt × Pt)) (H : Finset Edge) (q : Pt) (a : Side) :
    Option RunEnd :=
  scanRowAux V S H q a (outArc H q a) (V.card + 1) 1

-- The squares of the bridges, as one set.
--
def bridgeSquares (BS : List Bridge) : Finset Pt :=
  (BS.flatMap fun b => (List.range b.r).map b.cell).toFinset

lemma bridgeSquares_iff {BS : List Bridge} {q : Pt} : decide (q ∈ bridgeSquares BS) = bridgeSqB BS q := by
  by_cases h : bridgeSqB BS q = true
  · rw [h]
    simp only [decide_eq_true_eq]
    obtain ⟨b, hb, j, hj, hq⟩ := bridgeSqB_iff.1 h
    simp only [bridgeSquares, List.mem_toFinset, List.mem_flatMap, List.mem_map, List.mem_range]
    exact ⟨b, hb, j, hj, hq.symm⟩
  · rw [Bool.not_eq_true] at h
    rw [h]
    simp only [decide_eq_false_iff_not]
    intro hm
    simp only [bridgeSquares, List.mem_toFinset, List.mem_flatMap, List.mem_map, List.mem_range] at hm
    obtain ⟨b, hb, j, hj, hq⟩ := hm
    have := bridgeSqB_iff.2 ⟨b, hb, j, hj, hq.symm⟩
    rw [h] at this; exact absurd this (by simp)

def rowOf (V : Finset Pt) (S : Finset (Pt × Pt)) (H : Finset Edge) (B : Finset Pt)
    (x : Pt × Side) : Option Bridge :=
  if isCritical S H x.1 x.2 && !decide (x.1 ∈ B) then
    match scanRow V S H x.1 x.2 with
    | some (.row r) => some ⟨x.1, x.2, r⟩
    | _ => none
  else none

def findRow (V : Finset Pt) (S : Finset (Pt × Pt)) (H : Finset Edge) (BS : List Bridge) :
    Option Bridge :=
  let B := bridgeSquares BS
  ((cellList V).flatMap fun q => sidesL.map fun a => (q, a)).findSome? (rowOf V S H B)

def runPhase (V W : Finset Pt) : ℕ → Finset Edge → List Bridge → Finset Edge × List Bridge × POut
  | 0, H, BS => (H, BS, .fuel)
  | n + 1, H, BS =>
    let S := connectedPairs W H
    match findMergingCell V S H BS with
    | some c => (H, BS, .merge c)
    | none =>
      match findRow V S H BS with
      | none => (H, BS, .stuck)
      | some b =>
        if b.r % 2 = 1 then (H, BS, .odd b)
        else if flipSplits W H b then runPhase V W n (flip H b.E) (b :: BS)
        else (H, BS, .twist b)

section eq

variable {V W : Finset Pt} {H : Finset Edge} (hVW : V ⊆ W) (hHW : Inside W H)
include hVW hHW

lemma isCutCell_eq {c : Pt} (hc : IsCell V c) : isCutCell (connectedPairs W H) c = cutB W H c := by
  have hcW : c ∈ W := hVW hc.1
  unfold isCutCell cutB
  rw [isConnected_eq hHW hcW, isConnected_eq hHW hcW, isConnected_eq hHW hcW]

lemma isCritical_eq {q : Pt} (hq : IsCell V q) (a : Side) :
    isCritical (connectedPairs W H) H q a = critB W H q a := by
  obtain ⟨hb1, _, hf1, _⟩ := corners4 hq a
  unfold isCritical critB
  rw [isConnected_eq hHW (hVW hb1), isConnected_eq hHW (hVW hf1), isConnected_eq hHW (hVW hb1)]

lemma findMergingCell_eq (BS : List Bridge) : findMergingCell V (connectedPairs W H) H BS = findMerge V W H BS := by
  unfold findMergingCell findMerge
  apply find?_congr
  intro c hc
  rw [isCutCell_eq hVW hHW (mem_cellList.1 hc).2]

lemma scanRowAux_eq (q : Pt) (a : Side) (o : Bool) :
    ∀ fuel j, scanRowAux V (connectedPairs W H) H q a o fuel j = scanAux V W H q a o fuel j := by
  intro fuel
  induction fuel with
  | zero => intro j; rfl
  | succ fuel ih =>
    intro j
    simp only [scanRowAux, scanAux]
    by_cases h1 : outArc H (cellJ q a (j - 1)) a ≠ o
    · rw [ite_eq_left h1, ite_eq_left h1]
    · rw [ite_eq_right h1, ite_eq_right h1, ih]
      by_cases hc : IsCell V (cellJ q a j)
      · rw [isCutCell_eq hVW hHW hc]
      · rw [ite_eq_left (Or.inl hc), ite_eq_left (Or.inl hc)]

lemma rowOf_eq (BS : List Bridge) {x : Pt × Side} (hx : IsCell V x.1) :
    rowOf V (connectedPairs W H) H (bridgeSquares BS) x = moveOf V W H BS x := by
  unfold rowOf moveOf scanRow scan
  rw [isCritical_eq hVW hHW hx, scanRowAux_eq hVW hHW, bridgeSquares_iff]
  split_ifs
  · rcases scanAux V W H x.1 x.2 (outArc H x.1 x.2) (V.card + 1) 1 with _ | (r | k) <;> rfl
  · rfl

lemma findRow_eq (BS : List Bridge) : findRow V (connectedPairs W H) H BS = findMove V W H BS := by
  unfold findRow findMove
  apply findSome?_congr
  intro x hx
  simp only [List.mem_flatMap, List.mem_map] at hx
  obtain ⟨q, hq, a, _, rfl⟩ := hx
  exact rowOf_eq hVW hHW BS (mem_cellList.1 hq).2

end eq

-- **`runPhase` is `phase`** on states satisfying the phase invariant.
--
theorem runPhase_eq {V W : Finset Pt} (hVW : V ⊆ W) :
    ∀ n (H : Finset Edge) (BS : List Bridge), PhI V W H BS → runPhase V W n H BS = phase V W n H BS := by
  intro n
  induction n with
  | zero => intro H BS _; rfl
  | succ n ih =>
    intro H BS hI
    simp only [runPhase, phase]
    rw [findMergingCell_eq hVW hI.1, findRow_eq hVW hI.1]
    rcases hm : findMerge V W H BS with _ | c
    · simp only
      rcases hmv : findMove V W H BS with _ | b
      · rfl
      · simp only
        split_ifs
        · rfl
        · exact ih _ _ (phI_step hVW hI hmv)
        · rfl
    · rfl

end HP

end ULHC
