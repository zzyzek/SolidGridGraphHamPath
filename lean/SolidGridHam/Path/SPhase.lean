/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
import SolidGridHam.Path.PairOf

/-!
# Sheffield's phase

`Reach V H0 H BS`: from the bridge-free start `H0`, bridge steps (`RowStep`) build the bridges `BS`
(newest first). Each step is taken only when every merging cell is a pair square (`MergeOK`);
otherwise the phase ends in success.

`PInv` collects what holds along the phase: `H` is a factor whose only edge leaving `V` ends at
`t0`, every bridge region is frozen (`RegionOK`), and the pair squares of different bridges are
different (`pinv_step`).
-/

namespace SolidGridHam

namespace HP

open Finset Classical

-- The pair squares of two bridges are different.
--
def Disj (b1 b2 : Bridge) : Prop :=
  b1.cell (b1.r - 2) ≠ b2.cell (b2.r - 2) ∧ b1.cell (b1.r - 2) ≠ b2.E ∧
    b1.E ≠ b2.cell (b2.r - 2) ∧ b1.E ≠ b2.E

lemma Disj.symm {b1 b2 : Bridge} (h : Disj b1 b2) : Disj b2 b1 :=
  ⟨fun e => h.1 e.symm, fun e => h.2.2.1 e.symm, fun e => h.2.1 e.symm, fun e => h.2.2.2 e.symm⟩

-- The flipped square of `b1` is outside the region of `b2`.
--
def NotZ (b1 b2 : Bridge) : Prop :=
  (∀ j ≤ b2.r, b1.E ≠ b2.cell j) ∧ b1.E ≠ nb b2.q b2.a.opp ∧
    (∀ j, j + 1 ≤ b2.r → b1.E ≠ nb (b2.cell j) (latA b2.a) ∧ b1.E ≠ nb (b2.cell j) (latB b2.a))

-- Every merging cell is a pair square.
--
def MergeOK (V : Finset Pt) (H : Finset Edge) (BS : List Bridge) : Prop :=
  ∀ c, IsCell V c → Alt H c → CutSq H c → ∃ b ∈ BS, c = b.cell (b.r - 2) ∨ c = b.E

-- A square of some bridge (the start rule: a step never starts on one).
--
def BridgeSqL (BS : List Bridge) (q : Pt) : Prop := ∃ b ∈ BS, ∃ j < b.r, q = b.cell j

inductive Reach (V : Finset Pt) (H0 : Finset Edge) : Finset Edge → List Bridge → Prop
  | base : Reach V H0 H0 []
  | step {H : Finset Edge} {BS : List Bridge} {b : Bridge} :
      Reach V H0 H BS → RowStep V H b → MergeOK V H BS → ¬ BridgeSqL BS b.q →
        Reach V H0 (flip H b.E) (b :: BS)

structure PInv (V W : Finset Pt) (d : Pt → ℕ) (H : Finset Edge) (BS : List Bridge) (t0 u0 : Pt) :
    Prop where
  fac : IsFactor W d H
  out : ∀ e ∈ H, (e.p ∉ V → e.q = t0 ∨ e.q = u0) ∧ (e.q ∉ V → e.p = t0 ∨ e.p = u0)
  reg : ∀ b ∈ BS, RegionOK H b ∧ 2 ≤ b.r ∧ b.r % 2 = 0 ∧ (∀ j < b.r, IsCell V (b.cell j))
  disj : BS.Pairwise Disj
  sep : BS.Pairwise NotZ

section phase

variable {V W : Finset Pt} {d : Pt → ℕ} {H : Finset Edge} {t0 u0 : Pt}

lemma degc_of (hVW : V ⊆ W) (hdc : ∀ q, IsCell V q → ∀ z, IsCorner z q → d z = 2)
    (hH : IsFactor W d H) : ∀ f, IsCell V f → ∀ z, IsCorner z f → deg H z = 2 := by
  intro f hf z hz
  rw [hH.2 z (hVW (by
    obtain ⟨x, y⟩ := f
    rcases hz with rfl | rfl | rfl | rfl
    · exact hf.1
    · exact hf.2.1
    · exact hf.2.2.1
    · exact hf.2.2.2))]
  exact hdc f hf z hz

-- The pair squares of a frozen bridge are alternating.
--
lemma region_alt {b : Bridge} (hR : RegionOK H b) (htwo : 2 ≤ b.r) (hev : b.r % 2 = 0) :
    Alt H (b.cell (b.r - 2)) ∧ Alt H b.E := by
  obtain ⟨q, a, r⟩ := b
  obtain ⟨m, rfl⟩ : ∃ m, r = m + 2 := ⟨r - 2, by simp only at htwo; omega⟩
  obtain ⟨bk, lat, lat0, latE, fr, frA, frE, _, _, _, _⟩ := hR
  simp only [Bridge.cell, Bridge.E, show m + 2 - 1 = m + 1 by omega,
    show m + 2 - 2 = m by omega] at *
  have latA' : lat1 (cellJ q a m) a ∉ H ∧ lat2 (cellJ q a m) a ∉ H := by
    rcases Nat.eq_zero_or_pos m with h0 | hpos
    · subst h0; rw [cellJ_zero]; exact lat0
    · obtain ⟨a1, a2⟩ := lat m hpos (by omega)
      exact ⟨fun h => by have := a1.1 h; omega, fun h => by have := a2.1 h; omega⟩
  have bA : back (cellJ q a m) a ∈ H := by
    rcases Nat.eq_zero_or_pos m with h0 | hpos
    · subst h0; rw [cellJ_zero]; exact bk
    · obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
      rw [back_cellJ_succ]; exact (fr m' (by omega)).2 (by omega)
  have bE : back (cellJ q a (m + 1)) a ∈ H := by rw [back_cellJ_succ]; exact frA
  exact ⟨alt_of_bf bA frA latA'.1 latA'.2, alt_of_bf bE frE latE.1 latE.2⟩

-- The second-to-last square of a bridge step is not alternating before the flip.
--
lemma rowStep_A_notAlt {b : Bridge} (hrs : RowStep V H b)
    (hdegc : ∀ f, IsCell V f → ∀ z, IsCorner z f → deg H z = 2) :
    ¬ Alt H (b.cell (b.r - 2)) := by
  obtain ⟨q, a, r⟩ := b
  obtain ⟨two, even, cells, crit, bk, uncut, arcs, last, split⟩ := hrs
  obtain ⟨m, rfl⟩ : ∃ m, r = m + 2 := ⟨r - 2, by simp only at two; omega⟩
  simp only [Bridge.cell, Bridge.E, show m + 2 - 2 = m by omega] at *
  have hf0 : front q a ∉ H := fun h => by
    rcases crit.2.2.2 with ⟨_, h2⟩ | ⟨_, h1⟩
    · exact h2 h
    · exact h1 bk
  rcases Nat.eq_zero_or_pos m with h0 | hpos
  · subst h0
    rw [cellJ_zero]
    apply not_alt_of_ne (s' := a)
    unfold back at bk; unfold front at hf0; tauto
  · have dF1 : ∀ j < m + 2, deg H (front1 (cellJ q a j) a) = 2 := fun j hj =>
      hdegc _ (cells j hj) _ (isCorner_front1 _ _)
    have dF2 : ∀ j < m + 2, deg H (front2 (cellJ q a j) a) = 2 := fun j hj =>
      hdegc _ (cells j hj) _ (isCorner_front2 _ _)
    have rp := run_pat crit bk (n := m) (fun j hj => ⟨dF1 j (by omega), dF2 j (by omega)⟩)
      (fun j hj => arcs j (by omega))
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    have hb := (rp m' (by omega)).2.2
    have hf := (rp (m' + 1) le_rfl).2.2
    apply not_alt_of_ne (s' := a)
    have h1 : sideEdge (cellJ q a (m' + 1)) a ∉ H := fun h => by
      have := hf.1 h; omega
    have h2 : sideEdge (cellJ q a (m' + 1)) a.opp ∈ H := by
      have := back_cellJ_succ (c := q) (s := a) m'; unfold back at this; rw [this]
      exact hb.2 (by omega)
    tauto

-- **The phase invariant is kept by a bridge step.**
--
theorem pinv_step (hVW : V ⊆ W) (hdc : ∀ q, IsCell V q → ∀ z, IsCorner z q → d z = 2)
    {BS : List Bridge} {b : Bridge} (hinv : PInv V W d H BS t0 u0) (hrs : RowStep V H b) :
    PInv V W d (flip H b.E) (b :: BS) t0 u0 := by
  have hdegc := degc_of hVW hdc hinv.fac
  obtain ⟨Fl1, Fl2, Fbk, Ffr, _, _, _⟩ := rowStep_pre hrs hdegc
  have hEcell : IsCell V b.E := hrs.cells _ (by have := hrs.two; omega)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have hE := mkLat_cellE b.E b.a
    exact factor_flip hinv.fac (mkLat b.E b.a) (isCell_mono hEcell hVW) hE Fl1 Fl2 Fbk Ffr
  · intro e he
    unfold flip at he
    rcases Finset.mem_symmDiff.1 he with ⟨h1, _⟩ | ⟨h1, _⟩
    · exact hinv.out e h1
    · obtain ⟨cp, cq⟩ := corners_of_cellE h1
      have inV : ∀ z, IsCorner z b.E → z ∈ V := by
        intro z hz
        obtain ⟨x, y⟩ := b.E
        rcases hz with rfl | rfl | rfl | rfl
        · exact hEcell.1
        · exact hEcell.2.1
        · exact hEcell.2.2.1
        · exact hEcell.2.2.2
      exact ⟨fun h => absurd (inV _ cp) h, fun h => absurd (inV _ cq) h⟩
  · intro b' hb'
    rcases List.mem_cons.1 hb' with rfl | hb'
    · exact ⟨regionOK_new hrs hdegc, hrs.two, hrs.even, hrs.cells⟩
    · obtain ⟨hR, h2, he, hc⟩ := hinv.reg b' hb'
      exact ⟨regionOK_step hR h2 he hrs hdegc, h2, he, hc⟩
  · refine List.Pairwise.cons (fun b' hb' => ?_) hinv.disj
    obtain ⟨hR, h2, he, _⟩ := hinv.reg b' hb'
    obtain ⟨ncol, _, _⟩ := flip_not_region hR h2 he hrs hdegc
    obtain ⟨altA, altE⟩ := region_alt hR h2 he
    have nA := rowStep_A_notAlt hrs hdegc
    refine ⟨fun e => nA (e ▸ altA), fun e => nA (e ▸ altE), ncol _ (by omega), ?_⟩
    have := ncol (b'.r - 1) (by omega)
    exact this
  · refine List.Pairwise.cons (fun b' hb' => ?_) hinv.sep
    obtain ⟨hR, h2, he, _⟩ := hinv.reg b' hb'
    exact flip_not_region hR h2 he hrs hdegc

-- **Every reachable state satisfies the phase invariant.**
--
theorem pinv_reach (hVW : V ⊆ W) (hdc : ∀ q, IsCell V q → ∀ z, IsCorner z q → d z = 2)
    {H0 : Finset Edge} (h0 : IsFactor W d H0)
    (hout0 : ∀ e ∈ H0, (e.p ∉ V → e.q = t0 ∨ e.q = u0) ∧ (e.q ∉ V → e.p = t0 ∨ e.p = u0))
    {H : Finset Edge} {BS : List Bridge} (hr : Reach V H0 H BS) : PInv V W d H BS t0 u0 := by
  induction hr with
  | base => exact ⟨h0, hout0, fun _ h => absurd h (List.not_mem_nil), List.Pairwise.nil,
      List.Pairwise.nil⟩
  | step _ hrs _ _ ih => exact pinv_step hVW hdc ih hrs

end phase

end HP

end SolidGridHam
