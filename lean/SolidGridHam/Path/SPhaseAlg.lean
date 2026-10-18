/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
module

public import SolidGridHam.Path.SAlg
public import SolidGridHam.Algorithm

@[expose] public section

/-!
# One phase, decided

`phase V W n H BS` runs bridge steps until one of:
* `.merge c`: a merging cell `c` that is not a pair square;
* `.odd b`: a critical non-bridge square whose run turns after an odd number of squares;
* `.twist b`: the same with an even number, whose last flip does not split;
* `.stuck`: every merging cell is a pair square and every critical square is a bridge square or
  stuck (`phase_no_hp` applies);
* `.fuel`: out of fuel, which does not happen with `W.card + 1` steps (`phase_fuel`).

`phase_spec`: the outcome holds of the state returned, which is reached by bridge steps.
-/

namespace SolidGridHam

namespace HP

open Finset Classical

def phase (V W : Finset Pt) : ℕ → Finset Edge → List Bridge → Finset Edge × List Bridge × POut
  | 0, H, BS => (H, BS, .fuel)
  | n + 1, H, BS =>
    match findMerge V W H BS with
    | some c => (H, BS, .merge c)
    | none =>
      match findMove V W H BS with
      | none => (H, BS, .stuck)
      | some b =>
        if b.r % 2 = 1 then (H, BS, .odd b)
        else if flipSplits W H b then phase V W n (flip H b.E) (b :: BS)
        else (H, BS, .twist b)

-- The facts of a candidate row.
--
def MoveFacts (V : Finset Pt) (H : Finset Edge) (BS : List Bridge) (b : Bridge) : Prop :=
  IsCell V b.q ∧ CriticalIn H b.q b.a ∧ back b.q b.a ∈ H ∧ ¬ BridgeSq BS b.q ∧ 2 ≤ b.r ∧
    (∀ j < b.r, IsCell V (b.cell j)) ∧ (∀ j, 1 ≤ j → j < b.r → ¬ CutSq H (b.cell j)) ∧
    (∀ j, j + 1 < b.r → outArc H (b.cell j) b.a = outArc H b.q b.a) ∧
    outArc H b.E b.a ≠ outArc H b.q b.a

def POK (V : Finset Pt) (H0 H : Finset Edge) (BS : List Bridge) : POut → Prop
  | .stuck => Reach V H0 H BS ∧ MergeOK V H BS ∧ Stuck V H BS
  | .merge c => Reach V H0 H BS ∧ IsCell V c ∧ Alt H c ∧ CutSq H c ∧
      ¬ ∃ b ∈ BS, c = b.cell (b.r - 2) ∨ c = b.E
  | .odd b => Reach V H0 H BS ∧ MergeOK V H BS ∧ MoveFacts V H BS b ∧ b.r % 2 = 1
  | .twist b => Reach V H0 H BS ∧ MergeOK V H BS ∧ MoveFacts V H BS b ∧ b.r % 2 = 0 ∧
      Conn (flip H b.E) (back1 b.E b.a) (front1 b.E b.a)
  | .fuel => True

section phaseAlg

variable {V W : Finset Pt} {d : Pt → ℕ} {t0 u0 : Pt}

theorem phase_spec (hVW : V ⊆ W) (hdc : ∀ q, IsCell V q → ∀ z, IsCorner z q → d z = 2)
    {H0 : Finset Edge} (h0 : IsFactor W d H0)
    (hout0 : ∀ e ∈ H0, (e.p ∉ V → e.q = t0 ∨ e.q = u0) ∧ (e.q ∉ V → e.p = t0 ∨ e.p = u0)) :
    ∀ n H BS, Reach V H0 H BS →
      POK V H0 (phase V W n H BS).1 (phase V W n H BS).2.1 (phase V W n H BS).2.2 := by
  intro n
  induction n with
  | zero => intro H BS _; simp [phase, POK]
  | succ n ih =>
    intro H BS hr
    have hinv := pinv_reach (t0 := t0) (u0 := u0) hVW hdc h0 hout0 hr
    have hHW := Inside.of_factor hinv.fac
    simp only [phase]
    rcases hm : findMerge V W H BS with _ | c
    · simp only
      have hmo := findMerge_none hVW hHW hm
      rcases hf : findMove V W H BS with _ | b
      · simp only [POK]
        exact ⟨hr, hmo, findMove_none hVW hHW hf⟩
      · simp only
        have mf := findMove_some hVW hHW hf
        by_cases ho : b.r % 2 = 1
        · simp only [ho, ↓reduceIte, POK]; exact ⟨hr, hmo, mf, trivial⟩
        · simp only [ho, ↓reduceIte]
          have hEc : IsCell V b.E := mf.2.2.2.2.2.1 _ (by have := mf.2.2.2.2.1; omega)
          have hin' := inside_flip hHW (isCell_mono hEc hVW)
          have corners := isCell_corners hEc b.a
          have hsp : flipSplits W H b = true ↔ ¬ Conn (flip H b.E) (back1 b.E b.a) (front1 b.E b.a) := by
            unfold flipSplits
            exact bool_not_iff (connB_iff hin' (hVW corners.1) (hVW corners.2.2.1))
          by_cases hs : flipSplits W H b = true
          · simp only [hs, ↓reduceIte]
            have hrs : RowStep V H b := ⟨mf.2.2.2.2.1, by omega, mf.2.2.2.2.2.1, mf.2.1, mf.2.2.1,
              mf.2.2.2.2.2.2.1, mf.2.2.2.2.2.2.2.1, mf.2.2.2.2.2.2.2.2, hsp.1 hs⟩
            exact ih _ _ (Reach.step hr hrs hmo mf.2.2.2.1)
          · have hs' : flipSplits W H b = false := by simpa using hs
            simp only [hs', Bool.false_eq_true, ↓reduceIte, POK]
            refine ⟨hr, hmo, mf, by omega, ?_⟩
            by_contra hc
            exact hs (hsp.2 hc)
    · simp only [POK]
      exact ⟨hr, findMerge_some hVW hHW hm⟩

lemma ncomp_le_card {X : Finset Pt} {F : Finset Edge} : ncomp X F ≤ X.card := by
  unfold ncomp; exact Finset.card_image_le

-- **Enough fuel.** Each bridge step adds a piece, and there are at most `W.card` pieces.
--
theorem phase_fuel (hVW : V ⊆ W) (hdc : ∀ q, IsCell V q → ∀ z, IsCorner z q → d z = 2)
    {H0 : Finset Edge} (h0 : IsFactor W d H0)
    (hout0 : ∀ e ∈ H0, (e.p ∉ V → e.q = t0 ∨ e.q = u0) ∧ (e.q ∉ V → e.p = t0 ∨ e.p = u0)) :
    ∀ n H BS, Reach V H0 H BS → W.card < n + ncomp W H →
      ∀ H' BS', phase V W n H BS ≠ (H', BS', .fuel) := by
  intro n
  induction n with
  | zero => intro H BS _ hlt; have := ncomp_le_card (X := W) (F := H); omega
  | succ n ih =>
    intro H BS hr hlt H' BS' heq
    have hinv := pinv_reach (t0 := t0) (u0 := u0) hVW hdc h0 hout0 hr
    have hHW := Inside.of_factor hinv.fac
    simp only [phase] at heq
    rcases hm : findMerge V W H BS with _ | c
    · rw [hm] at heq; simp only at heq
      have hmo := findMerge_none hVW hHW hm
      rcases hf : findMove V W H BS with _ | b
      · rw [hf] at heq; simp at heq
      · rw [hf] at heq; simp only at heq
        have mf := findMove_some hVW hHW hf
        by_cases ho : b.r % 2 = 1
        · simp [ho] at heq
        · simp only [ho, ↓reduceIte] at heq
          by_cases hs : flipSplits W H b = true
          · simp only [hs, ↓reduceIte] at heq
            have hEc : IsCell V b.E := mf.2.2.2.2.2.1 _ (by have := mf.2.2.2.2.1; omega)
            have hin' := inside_flip hHW (isCell_mono hEc hVW)
            have corners := isCell_corners hEc b.a
            have hsp : ¬ Conn (flip H b.E) (back1 b.E b.a) (front1 b.E b.a) := by
              have := hs; unfold flipSplits at this
              exact (bool_not_iff (connB_iff hin' (hVW corners.1) (hVW corners.2.2.1))).1 this
            have hrs : RowStep V H b := ⟨mf.2.2.2.2.1, by omega, mf.2.2.2.2.2.1, mf.2.1, mf.2.2.1,
              mf.2.2.2.2.2.2.1, mf.2.2.2.2.2.2.2.1, mf.2.2.2.2.2.2.2.2, hsp⟩
            have hc := step_count hVW hrs (degc_of hVW hdc hinv.fac)
            exact ih _ _ (Reach.step hr hrs hmo mf.2.2.2.1) (by omega) H' BS' heq
          · have hs' : flipSplits W H b = false := by simpa using hs
            simp [hs'] at heq
    · rw [hm] at heq; simp at heq

end phaseAlg

end HP

end SolidGridHam
