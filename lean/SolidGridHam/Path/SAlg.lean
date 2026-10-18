/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
module

public import SolidGridHam.Path.PhaseCount
public import SolidGridHam.Path.Cert
public import SolidGridHam.Path.Prelim.NotchPF
public import SolidGridHam.Cycle.Algorithm
public import SolidGridHam.Algorithm

@[expose] public section

/-!
# Sheffield's phase, decided

Bool checks on a state `(H, BS)` over `W ⊇ V` (connections decided by `connB W`):
* `cutB`: a cell is cut;
* `findMerge`: a merging cell that is not a pair square (`findMerge_none`: `MergeOK`);
* `critB`: a cell is critical in a frame with its back dark;
* `scan`: the run from a critical square, ending in a turn (a row of length `r`) or at a non-cell or
  cut square (stuck).
-/

namespace SolidGridHam

namespace HP

open Finset Classical

section salg

variable {V W : Finset Pt} {H : Finset Edge}

lemma cutB_iff (hVW : V ⊆ W) (hHW : Inside W H) {c : Pt} (hc : IsCell V c) :
    cutB W H c = true ↔ CutSq H c := by
  obtain ⟨h1, h2, h3, h4⟩ := hc
  unfold cutB CutSq
  rw [bool_not_iff]
  simp only [Bool.and_eq_true]
  rw [connB_iff hHW (hVW h1) (hVW h2), connB_iff hHW (hVW h1) (hVW h4),
    connB_iff hHW (hVW h1) (hVW h3), and_assoc]

lemma pairSqB_iff {BS : List Bridge} {c : Pt} :
    pairSqB BS c = true ↔ ∃ b ∈ BS, c = b.cell (b.r - 2) ∨ c = b.E := by
  unfold pairSqB; simp [List.any_eq_true]

def findMerge (V W : Finset Pt) (H : Finset Edge) (BS : List Bridge) : Option Pt :=
  (cellList V).find? fun c => decide (Alt H c) && cutB W H c && !pairSqB BS c

lemma findMerge_none (hVW : V ⊆ W) (hHW : Inside W H) {BS : List Bridge}
    (h : findMerge V W H BS = none) : MergeOK V H BS := by
  intro c hc ha hcut
  unfold findMerge at h
  have := List.find?_eq_none.1 h c (mem_cellList.2 ⟨hc.1, hc⟩)
  simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', not_and,
    Bool.not_eq_false] at this
  have h2 := this ⟨ha, (cutB_iff hVW hHW hc).2 hcut⟩
  exact pairSqB_iff.1 h2

lemma findMerge_some (hVW : V ⊆ W) (hHW : Inside W H) {BS : List Bridge} {c : Pt}
    (h : findMerge V W H BS = some c) :
    IsCell V c ∧ Alt H c ∧ CutSq H c ∧ ¬ ∃ b ∈ BS, c = b.cell (b.r - 2) ∨ c = b.E := by
  unfold findMerge at h
  have hm := List.mem_of_find?_eq_some h
  have hp := List.find?_some h
  have hc := (mem_cellList.1 hm).2
  simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at hp
  refine ⟨hc, hp.1.1, (cutB_iff hVW hHW hc).1 hp.1.2, fun hx => ?_⟩
  have := pairSqB_iff.2 hx
  rw [hp.2] at this; exact absurd this (by simp)

-- Critical in frame `a` with the back dark.
--
def critB (W : Finset Pt) (H : Finset Edge) (q : Pt) (a : Side) : Bool :=
  connB W H (back1 q a) (back2 q a) && connB W H (front1 q a) (front2 q a) &&
    !connB W H (back1 q a) (front1 q a) && decide (back q a ∈ H) && decide (front q a ∉ H)

lemma critB_iff (hVW : V ⊆ W) (hHW : Inside W H) {q : Pt} (hq : IsCell V q) {a : Side} :
    critB W H q a = true ↔ CriticalIn H q a ∧ back q a ∈ H := by
  obtain ⟨hb1, hb2, hf1, hf2⟩ := corners4 hq a
  unfold critB
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  rw [connB_iff hHW (hVW hb1) (hVW hb2), connB_iff hHW (hVW hf1) (hVW hf2),
    bool_not_iff (connB_iff hHW (hVW hb1) (hVW hf1))]
  unfold CriticalIn
  constructor
  · rintro ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩
    exact ⟨⟨h1, h2, h3, Or.inl ⟨h4, h5⟩⟩, h4⟩
  · rintro ⟨⟨h1, h2, h3, hx⟩, h4⟩
    refine ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, ?_⟩
    rcases hx with ⟨_, h⟩ | ⟨_, h⟩
    · exact h
    · exact absurd h4 h

-- A square of some bridge.
--
def bridgeSqB (BS : List Bridge) (q : Pt) : Bool :=
  BS.any fun b => (List.range b.r).any fun j => decide (q = b.cell j)

lemma bridgeSqB_iff {BS : List Bridge} {q : Pt} : bridgeSqB BS q = true ↔ BridgeSq BS q := by
  unfold bridgeSqB BridgeSq
  simp [List.any_eq_true]

def scanAux (V W : Finset Pt) (H : Finset Edge) (q : Pt) (a : Side) (o : Bool) :
    ℕ → ℕ → Option RunEnd
  | 0, _ => none
  | fuel + 1, j =>
    if outArc H (cellJ q a (j - 1)) a ≠ o then some (.row j)
    else if ¬ IsCell V (cellJ q a j) ∨ cutB W H (cellJ q a j) = true then some (.stuck j)
    else scanAux V W H q a o fuel (j + 1)

def scan (V W : Finset Pt) (H : Finset Edge) (q : Pt) (a : Side) : Option RunEnd :=
  scanAux V W H q a (outArc H q a) (V.card + 1) 1

-- What the scan has seen up to index `j`.
--
def ScanOK (V : Finset Pt) (H : Finset Edge) (q : Pt) (a : Side) (j : ℕ) : Prop :=
  1 ≤ j ∧ (∀ i, 1 ≤ i → i < j → IsCell V (cellJ q a i) ∧ ¬ CutSq H (cellJ q a i)) ∧
    (∀ i, i + 1 < j → outArc H (cellJ q a i) a = outArc H q a)

lemma scanAux_spec (hVW : V ⊆ W) (hHW : Inside W H) {q : Pt} {a : Side} :
    ∀ fuel j, ScanOK V H q a j → ∀ e, scanAux V W H q a (outArc H q a) fuel j = some e →
      (∃ r, e = .row r ∧ ScanOK V H q a r ∧ outArc H (cellJ q a (r - 1)) a ≠ outArc H q a) ∨
      (∃ k, e = .stuck k ∧ ScanOK V H q a k ∧ outArc H (cellJ q a (k - 1)) a = outArc H q a ∧
        (¬ IsCell V (cellJ q a k) ∨ CutSq H (cellJ q a k))) := by
  intro fuel
  induction fuel with
  | zero => intro j _ e h; simp [scanAux] at h
  | succ fuel ih =>
    intro j hj e h
    simp only [scanAux] at h
    by_cases h1 : outArc H (cellJ q a (j - 1)) a ≠ outArc H q a
    · rw [ite_eq_left h1] at h
      simp only [Option.some.injEq] at h
      exact Or.inl ⟨j, h.symm, hj, h1⟩
    · rw [ite_eq_right h1] at h
      push Not at h1
      by_cases h2 : ¬ IsCell V (cellJ q a j) ∨ cutB W H (cellJ q a j) = true
      · rw [ite_eq_left h2] at h
        simp only [Option.some.injEq] at h
        refine Or.inr ⟨j, h.symm, hj, h1, ?_⟩
        rcases h2 with h2 | h2
        · exact Or.inl h2
        · by_cases hc : IsCell V (cellJ q a j)
          · exact Or.inr ((cutB_iff hVW hHW hc).1 h2)
          · exact Or.inl hc
      · rw [ite_eq_right h2] at h
        push Not at h2
        apply ih (j + 1) _ e h
        refine ⟨by omega, fun i hi1 hi2 => ?_, fun i hi => ?_⟩
        · rcases Nat.lt_or_ge i j with hlt | hge
          · exact hj.2.1 i hi1 hlt
          · obtain rfl : i = j := by omega
            exact ⟨h2.1, fun hc => by
              have := (cutB_iff hVW hHW h2.1).2 hc; simp_all⟩
        · rcases Nat.lt_or_ge (i + 1) j with hlt | hge
          · exact hj.2.2 i hlt
          · obtain rfl : i = j - 1 := by omega
            exact h1

-- The scan from a critical square never runs out: the squares it passes are distinct cells.
--
lemma scan_some (_hVW : V ⊆ W) (_hHW : Inside W H) {q : Pt} {a : Side} (_hq : IsCell V q) :
    scan V W H q a ≠ none := by
  intro h
  have key : ∀ fuel j, 1 ≤ j → scanAux V W H q a (outArc H q a) fuel j = none →
      ∀ i, j ≤ i → i < j + fuel → IsCell V (cellJ q a i) := by
    intro fuel
    induction fuel with
    | zero => intro j _ _ i h1 h2; omega
    | succ fuel ih =>
      intro j hj h i h1 h2
      simp only [scanAux] at h
      by_cases c1 : outArc H (cellJ q a (j - 1)) a ≠ outArc H q a
      · rw [ite_eq_left c1] at h; simp at h
      · rw [ite_eq_right c1] at h
        by_cases c2 : ¬ IsCell V (cellJ q a j) ∨ cutB W H (cellJ q a j) = true
        · rw [ite_eq_left c2] at h; simp at h
        · rw [ite_eq_right c2] at h
          push Not at c2
          rcases Nat.lt_or_ge i (j + 1) with hlt | hge
          · obtain rfl : i = j := by omega
            exact c2.1
          · exact ih (j + 1) (by omega) h i hge (by omega)
  have hall := key (V.card + 1) 1 le_rfl h
  -- `V.card + 1` distinct cells `cellJ q a 1 … cellJ q a (V.card + 1)` in `V`.
  --
  have hinj : Set.InjOn (fun i => cellJ q a i) (Set.Icc 1 (V.card + 1)) :=
    fun i _ j _ hij => cellJ_inj hij
  have hsub : ((Finset.Icc 1 (V.card + 1)).image (fun i => cellJ q a i)) ⊆ V := by
    intro z hz
    simp only [Finset.mem_image, Finset.mem_Icc] at hz
    obtain ⟨i, ⟨h1, h2⟩, rfl⟩ := hz
    exact (hall i h1 (by omega)).1
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_image_of_injOn (by intro i hi j hj hij; exact cellJ_inj hij)] at hcard
  simp at hcard

end salg

section findmove

variable {V W : Finset Pt} {H : Finset Edge}

def moveOf (V W : Finset Pt) (H : Finset Edge) (BS : List Bridge) (x : Pt × Side) :
    Option Bridge :=
  if critB W H x.1 x.2 && !bridgeSqB BS x.1 then
    match scan V W H x.1 x.2 with
    | some (.row r) => some ⟨x.1, x.2, r⟩
    | _ => none
  else none

-- A critical non-bridge square whose run turns: a candidate row.
--
def findMove (V W : Finset Pt) (H : Finset Edge) (BS : List Bridge) : Option Bridge :=
  ((cellList V).flatMap fun q => sidesL.map fun a => (q, a)).findSome? (moveOf V W H BS)

lemma findMove_none (hVW : V ⊆ W) (hHW : Inside W H) {BS : List Bridge}
    (h : findMove V W H BS = none) : Stuck V H BS := by
  intro q a hq hcr hb
  by_cases hbs : BridgeSq BS q
  · exact Or.inl hbs
  right
  have hmem : (q, a) ∈ (cellList V).flatMap fun q => sidesL.map fun a => (q, a) := by
    simp only [List.mem_flatMap, List.mem_map]
    exact ⟨q, mem_cellList.2 ⟨hq.1, hq⟩, a, mem_sidesL a, rfl⟩
  have hnone := List.findSome?_eq_none_iff.1 h (q, a) hmem
  unfold moveOf at hnone
  have hc : (critB W H q a && !bridgeSqB BS q) = true := by
    simp only [Bool.and_eq_true, Bool.not_eq_true']
    refine ⟨(critB_iff hVW hHW hq).2 ⟨hcr, hb⟩, ?_⟩
    cases hx : bridgeSqB BS q
    · rfl
    · exact absurd (bridgeSqB_iff.1 hx) hbs
  simp only [hc, ↓reduceIte] at hnone
  have hs := scan_some hVW hHW hq (a := a)
  rcases he : scan V W H q a with _ | e
  · exact absurd he hs
  rw [he] at hnone
  have h0 : ScanOK V H q a 1 := ⟨le_rfl, fun i h1 h2 => by omega, fun i h => by omega⟩
  rcases scanAux_spec hVW hHW _ 1 h0 e he with ⟨r, rfl, _, _⟩ | ⟨k, rfl, hk, harc, hend⟩
  · simp at hnone
  · refine ⟨k, hk.1, hk.2.1, fun j hj => ?_, hend⟩
    rcases Nat.lt_or_ge (j + 1) k with hlt | hge
    · exact hk.2.2 j hlt
    · obtain rfl : j = k - 1 := by omega
      exact harc

lemma findMove_some (hVW : V ⊆ W) (hHW : Inside W H) {BS : List Bridge} {b : Bridge}
    (h : findMove V W H BS = some b) :
    IsCell V b.q ∧ CriticalIn H b.q b.a ∧ back b.q b.a ∈ H ∧ ¬ BridgeSq BS b.q ∧ 2 ≤ b.r ∧
      (∀ j < b.r, IsCell V (b.cell j)) ∧ (∀ j, 1 ≤ j → j < b.r → ¬ CutSq H (b.cell j)) ∧
      (∀ j, j + 1 < b.r → outArc H (b.cell j) b.a = outArc H b.q b.a) ∧
      outArc H b.E b.a ≠ outArc H b.q b.a := by
  obtain ⟨x, hx, hb⟩ := List.exists_of_findSome?_eq_some h
  simp only [List.mem_flatMap, List.mem_map] at hx
  obtain ⟨q, hq, a, _, rfl⟩ := hx
  have hq' := (mem_cellList.1 hq).2
  unfold moveOf at hb
  by_cases hc : (critB W H q a && !bridgeSqB BS q) = true
  swap
  · simp only [hc, Bool.false_eq_true, ↓reduceIte] at hb; simp at hb
  simp only [hc, ↓reduceIte] at hb
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hc
  obtain ⟨hcr, hb0⟩ := (critB_iff hVW hHW hq').1 hc.1
  rcases he : scan V W H q a with _ | e
  · rw [he] at hb; simp at hb
  rw [he] at hb
  have h0 : ScanOK V H q a 1 := ⟨le_rfl, fun i h1 h2 => by omega, fun i h => by omega⟩
  rcases scanAux_spec hVW hHW _ 1 h0 e he with ⟨r, rfl, hr, hlast⟩ | ⟨k, rfl, _, _, _⟩
  · simp only [Option.some.injEq] at hb
    subst hb
    have r2 : 2 ≤ r := by
      by_contra hlt
      have : r = 1 := by have := hr.1; omega
      subst this
      exact hlast (by simp [cellJ_zero])
    refine ⟨hq', hcr, hb0, fun hbs => ?_, r2, fun j hj => ?_, fun j h1 h2 => (hr.2.1 j h1 h2).2,
      fun j hj => hr.2.2 j hj, ?_⟩
    · have := bridgeSqB_iff.2 hbs; rw [hc.2] at this; exact absurd this (by simp)
    · rcases Nat.eq_zero_or_pos j with h0 | hpos
      · simp only [Bridge.cell]; rw [h0, cellJ_zero]; exact hq'
      · exact (hr.2.1 j hpos hj).1
    · exact hlast
  · simp at hb

end findmove

end HP

end SolidGridHam
