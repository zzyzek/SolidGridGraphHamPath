/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
module

public import SolidGridHam.Path.E1

@[expose] public section

/-!
# Stuck ⇒ minimal (repaired §4.8): the induction

`Inv V H H' FP` collects what a stuck state (and every state after generalized moves toward `H'`)
satisfies (docs/STUCK_MINIMAL.md §20). The proof is by induction on `μ = Σ |D H H'|`:
* no movable square: the final count (`count_final`);
* a movable square: a generalized move (`move_step`) keeps `Inv`, the number of pieces and the
  number of fixed pairs, and lowers `μ`.
-/

namespace SolidGridHam

namespace HP

open Finset Classical

-- The column from `q` in direction `a` ends at a pair square of direction `o`: a top (climbing,
-- `o = true`, the bottom just beyond) or a bottom (descending, the top just beyond).
--
def ColEnds (V : Finset Pt) (H : Finset Edge) (FP : List FixedPr) (q : Pt) (a : Side) (o : Bool) :
    Prop :=
  ∃ n, (∀ j ≤ n + 1, IsCell V (cellJ q a j)) ∧ StripPat H q a (n + 1) ∧
    ∃ i ∈ FP, (o = true ∧ i.bot = cellJ q a (n + 1) ∧ i.s = a.opp) ∨
      (o = false ∧ i.bot = cellJ q a n ∧ i.s = a)

-- I5: strips starting beside the square just beyond a pair (docs/STUCK_MINIMAL.md §21).
--
def SideInv (V : Finset Pt) (H H' : Finset Edge) (FP : List FixedPr) : Prop :=
  ∀ p ∈ FP, ∀ ℓ, (ℓ = latA p.s ∨ ℓ = latB p.s) →
    (0 < D H H' p.top → IsCell V (nb p.bot ℓ) → back (nb p.bot ℓ) p.s.opp ∈ H →
      lat1 (nb p.bot ℓ) p.s.opp ∉ H → lat2 (nb p.bot ℓ) p.s.opp ∉ H →
      outArc H (nb p.bot ℓ) p.s = false → 0 < D H H' (nb p.bot ℓ) →
      ColEnds V H FP (nb p.bot ℓ) p.s.opp true) ∧
    (D H H' p.bot < 0 → IsCell V (nb p.top ℓ) → back (nb p.top ℓ) p.s ∈ H →
      lat1 (nb p.top ℓ) p.s ∉ H → lat2 (nb p.top ℓ) p.s ∉ H →
      outArc H (nb p.top ℓ) p.s.opp = true → D H H' (nb p.top ℓ) < 0 →
      ColEnds V H FP (nb p.top ℓ) p.s false)

-- The invariants. `col` is the column invariant for relevant critical squares (`D` of the sign of
-- the square's direction); `tri` is E1's shape for three-piece cells (docs/STUCK_MINIMAL.md §22).
--
structure Inv (V : Finset Pt) (H H' : Finset Edge) (FP : List FixedPr) (t0 u0 : Pt) : Prop where
  f2 : ∀ q, IsCell V q → Alt H q → CutSq H q → ∃ i ∈ FP, q = i.top ∨ q = i.bot
  f4 : ∀ i ∈ FP, PairOK H i
  tri : ∀ f, IsCell V f → Three H f → TriOK V H t0 u0 f
  out : ∀ e ∈ H, (e.p ∉ V → e.q = t0 ∨ e.q = u0) ∧ (e.q ∉ V → e.p = t0 ∨ e.p = u0)
  l4 : ∀ q s, IsCell V q → Conn H (back1 q s) (back2 q s) → Conn H (front1 q s) (front2 q s) →
    ¬ Conn H (back1 q s) (front1 q s) → back q s ∈ H ∨ front q s ∈ H
  palt : ∀ i ∈ FP, Alt H i.top ∧ Alt H i.bot
  pdark : ∀ i ∈ FP, sideEdge i.bot i.s ∈ H
  pcorn : ∀ i ∈ FP, IsCorner i.tx i.top ∧ IsCorner i.ty i.top ∧ IsCorner i.bx i.bot ∧
    IsCorner i.by' i.bot
  pdisj : ∀ i ∈ FP, ∀ j ∈ FP, (i.top = j.top ∨ i.top = j.bot ∨ i.bot = j.top ∨ i.bot = j.bot) →
    i = j
  col : ∀ q s, IsCell V q → CriticalIn H q s → back q s ∈ H →
    (∀ i ∈ FP, q ≠ i.top ∧ q ≠ i.bot) → 0 < sgnD (outArc H q s) (D H H' q) →
    ColEnds V H FP q s (outArc H q s)
  side : SideInv V H H' FP

section extract

variable {V : Finset Pt} {H H' : Finset Edge} {FP : List FixedPr} {t0 u0 : Pt}

-- A 2+2 square, same-piece pairs `back` and `front` in frame `s`, lateral sides not pointing `o`,
-- not alternating, with a dark same-piece side (L4): critical in frame `s` or `s.opp`, with its
-- dark side behind and its front arc pointing `o`.
--
lemma crit_of_twotwo {c : Pt} {s : Side} {o : Bool} (hl4 : back c s ∈ H ∨ front c s ∈ H)
    (hnalt : ¬ Alt H c) (hb : Conn H (back1 c s) (back2 c s)) (hf : Conn H (front1 c s) (front2 c s))
    (hn : ¬ Conn H (back1 c s) (front1 c s)) (hA : outArc H c (latA s) ≠ o)
    (hB : outArc H c (latB s) ≠ o) :
    ∃ s', (s' = s ∨ s' = s.opp) ∧ CriticalIn H c s' ∧ back c s' ∈ H ∧ outArc H c s' = o := by
  have l1 : lat1 c s ∉ H := fun h => hn ((ends_lat1 c s).conn h)
  have l2 : lat2 c s ∉ H := fun h => hn (hb.trans (((ends_lat2 c s).conn h).trans hf.symm))
  have hbf : ¬ (back c s ∈ H ∧ front c s ∈ H) := fun ⟨h1, h2⟩ => hnalt (alt_of_bf h1 h2 l1 l2)
  -- Arcs across light perpendicular sides are opposite.
  --
  have opp : ∀ s', (s' = s ∨ s' = s.opp) → sideEdge c s' ∉ H → outArc H c s' = o := by
    intro s' hs' hl
    have l1' : sideEdge c (latA s) ∉ H := by rw [← lat1_eq]; exact l1
    have hp : outArc H c s' = !outArc H c (latA s) := by
      cases s <;> cases s' <;> simp [Side.opp] at hs' <;> simp only [latA] at l1' ⊢ <;>
        rw [outArc_eq, outArc_eq] <;> simp only [Side.horiz, l1', hl, decide_false] <;>
        cases par c <;> rfl
    rw [hp]; cases o <;> cases h : outArc H c (latA s) <;> simp_all
  rcases hl4 with h | h
  · have hf' : front c s ∉ H := fun h' => hbf ⟨h, h'⟩
    refine ⟨s, Or.inl rfl, ⟨hb, hf, hn, Or.inl ⟨h, hf'⟩⟩, h, opp s (Or.inl rfl) hf'⟩
  · have hb' : back c s ∉ H := fun h' => hbf ⟨h', h⟩
    have e1 : back c s.opp = front c s := by cases s <;> rfl
    have e2 : front c s.opp = back c s := rfl
    have c1 : back1 c s.opp = front1 c s ∧ back2 c s.opp = front2 c s ∧
        front1 c s.opp = back1 c s ∧ front2 c s.opp = back2 c s := by
      obtain ⟨x, y⟩ := c; cases s <;> simp [back1, back2, front1, front2, Side.opp]
    refine ⟨s.opp, Or.inr rfl, ?_, by rw [e1]; exact h, opp s.opp (Or.inr rfl) (by
      show back c s ∉ H; exact hb')⟩
    rw [CriticalIn, c1.1, c1.2.1, c1.2.2.1, c1.2.2.2, e1, e2]
    exact ⟨hf, hb, fun h' => hn h'.symm, Or.inl ⟨h, hb'⟩⟩

lemma latA_opp (s : Side) : latA s.opp = latA s := by cases s <;> rfl

lemma nb_cellJ_opp (c : Pt) (s : Side) (j : ℕ) : nb (cellJ c s (j + 1)) s.opp = cellJ c s j := by
  obtain ⟨x, y⟩ := c
  cases s <;> simp [cellJ, nb, Side.opp] <;> ring_nf

-- A critical square (dark back, front arc `o`) is not a square of a pair: the top's light arcs
-- all point in, the bottom's all point out, but the square has light sides pointing both ways.
--
lemma not_pair_of_crit {c : Pt} {s : Side} {i : FixedPr} (hok : PairOK H i)
    (hc : CriticalIn H c s) (hb : back c s ∈ H) : c ≠ i.top ∧ c ≠ i.bot := by
  have hf : front c s ∉ H := by
    rcases hc.2.2.2 with ⟨_, h⟩ | ⟨_, h⟩
    · exact h
    · exact absurd hb h
  have hl : sideEdge c (latA s) ∉ H := by
    rw [← lat1_eq]; exact fun h => hc.2.2.1 ((ends_lat1 c s).conn h)
  have hp : outArc H c (latA s) = !outArc H c s := by
    have hf' : sideEdge c s ∉ H := hf
    cases s <;> simp only [latA] at hl ⊢ <;> rw [outArc_eq, outArc_eq] <;>
      simp only [Side.horiz, hl, hf', decide_false] <;> cases par c <;> rfl
  obtain ⟨htop, hbot, _⟩ := hok
  constructor
  · rintro rfl
    have a1 := htop s hf
    have a2 := htop (latA s) hl
    rw [hp, a1] at a2; exact absurd a2 (by simp)
  · rintro rfl
    have a1 := hbot s hf
    have a2 := hbot (latA s) hl
    rw [hp, a1] at a2; exact absurd a2 (by simp)

-- **A movable square, with its column ending at a fixed pair.**
--
theorem movable_column (hinv : Inv V H H' FP t0 u0) (hmove : ¬ NoMove V H H') :
    ∃ c s n i, IsCell V c ∧ CriticalIn H c s ∧ back c s ∈ H ∧ (∀ j ∈ FP, c ≠ j.top ∧ c ≠ j.bot) ∧
      0 < sgnD (outArc H c s) (D H H' c) ∧ (∀ j ≤ n + 1, IsCell V (cellJ c s j)) ∧
      StripPat H c s (n + 1) ∧ i ∈ FP ∧
      ((outArc H c s = true ∧ i.bot = cellJ c s (n + 1) ∧ i.s = s.opp) ∨
        (outArc H c s = false ∧ i.bot = cellJ c s n ∧ i.s = s)) ∧ n % 2 = 0 ∧ 2 ≤ n := by
  unfold NoMove at hmove
  push Not at hmove
  obtain ⟨o, c, hc, hnalt, hpos, hconf⟩ := hmove
  obtain ⟨s, -, hcrit, hb, harc⟩ : ∃ s, True ∧ CriticalIn H c s ∧ back c s ∈ H ∧ outArc H c s = o := by
    rcases hconf with ⟨h1, h2, h3, h4, h5⟩ | ⟨h1, h2, h3, h4, h5⟩
    · have hb' : Conn H (back1 c .t) (back2 c .t) := h1
      have hf' : Conn H (front1 c .t) (front2 c .t) := h2
      have hn' : ¬ Conn H (back1 c .t) (front1 c .t) := h3
      obtain ⟨s', -, h⟩ := crit_of_twotwo (hinv.l4 c .t hc hb' hf' hn') hnalt hb' hf' hn' h4 h5
      exact ⟨s', trivial, h⟩
    · have hb' : Conn H (back1 c .r) (back2 c .r) := h1
      have hf' : Conn H (front1 c .r) (front2 c .r) := h2
      have hn' : ¬ Conn H (back1 c .r) (front1 c .r) := h3
      obtain ⟨s', -, h⟩ := crit_of_twotwo (hinv.l4 c .r hc hb' hf' hn') hnalt hb' hf' hn' h4 h5
      exact ⟨s', trivial, h⟩
  have hnp : ∀ j ∈ FP, c ≠ j.top ∧ c ≠ j.bot := fun j hj =>
    not_pair_of_crit (hinv.f4 j hj) hcrit hb
  rw [← harc] at hpos
  obtain ⟨n, hcell, hpat, i, hi, hend⟩ := hinv.col c s hc hcrit hb hnp hpos
  have hfront : front (cellJ c s n) s ∈ H := by
    have hd := hinv.pdark i hi
    rcases hend with ⟨_, e1, e2⟩ | ⟨_, e1, e2⟩
    · rw [e1, e2] at hd
      have e3 : sideEdge (cellJ c s (n + 1)) s.opp = front (cellJ c s n) s :=
        back_cellJ_succ c s n
      rw [e3] at hd; exact hd
    · rw [e1, e2] at hd; exact hd
  have hev : n % 2 = 0 := by
    have := (hpat.2.2 n (by omega)).1 hfront; omega
  have hn0 : n ≠ 0 := by
    rintro rfl
    rcases hend with ⟨_, e1, e2⟩ | ⟨_, e1, _⟩
    · have : i.top = c := by
        unfold FixedPr.top; rw [e1, e2, nb_cellJ_opp, cellJ_zero]
      exact (hnp i hi).1 this.symm
    · rw [cellJ_zero] at e1; exact (hnp i hi).2 e1.symm
  exact ⟨c, s, n, i, hc, hcrit, hb, hnp, hpos, hcell, hpat, hi, hend, hev, by omega⟩

end extract

end HP

end SolidGridHam
