/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
import ULHC.HP.Sheffield.Height
import ULHC.HP.Sheffield.Shapes

/-!
# `FinalOK` from the shape of a final state

Across a light side, `H`'s arc depends only on the side's orientation and the cell's parity: out
of `c` across a horizontal side iff `par c` is false, across a vertical side iff it is true. So a
cell whose `x|y` sides include a horizontal and a vertical one is monotone along the cut, never
extremal. Hence a cell extremal along an `x|y` cut has its `x|y` sides opposite each other: it is a
2+2 square with the same-piece pairs adjacent (Sheffield's critical shape, or an alternating
merging square), or it touches three pieces.

**Final state** (hypotheses):
* (F2) every alternating cut square is a fixed square;
* (F3) at a square touching three pieces (E1 at `t`), the pair is paid through a third piece;
* (F4) each fixed pair: the top is a local maximum, the bottom a local minimum, and `(tx, ty)`,
  `(bx, by)` are the pieces of the top's and the bottom's cut;
* (F5) no movable square: no non-alternating 2+2 square, extremal along its cut, with `D` of the
  extremal sign.
-/

namespace ULHC

namespace HP

open Finset Classical

section finallocal

variable {V : Finset Pt} {H H' : Finset Edge}

/-! ## Pieces bookkeeping -/

lemma joins_peq {e : Edge} {x y u v : Pt} (h : PEq H x y u v) (hj : Joins H e u v) :
    Joins H e x y := by
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases hj with ⟨j1, j2⟩ | ⟨j1, j2⟩
  · exact Or.inl ⟨h1.trans j1, h2.trans j2⟩
  · exact Or.inr ⟨h1.trans j1, h2.trans j2⟩
  · exact Or.inr ⟨h1.trans j2, h2.trans j1⟩
  · exact Or.inl ⟨h1.trans j2, h2.trans j1⟩

lemma peq_trans {x y u v s t : Pt} (h1 : PEq H x y u v) (h2 : PEq H u v s t) : PEq H x y s t := by
  rcases h1 with ⟨a1, a2⟩ | ⟨a1, a2⟩ <;> rcases h2 with ⟨b1, b2⟩ | ⟨b1, b2⟩
  · exact Or.inl ⟨a1.trans b1, a2.trans b2⟩
  · exact Or.inr ⟨a1.trans b1, a2.trans b2⟩
  · exact Or.inr ⟨a1.trans b2, a2.trans b1⟩
  · exact Or.inl ⟨a1.trans b2, a2.trans b1⟩

lemma light_of_joins {e : Edge} {x y : Pt} (hj : Joins H e x y) (hn : ¬ Conn H x y) : e ∉ H := by
  intro he
  have hc : Conn H e.p e.q := Conn.of_edge he
  rcases hj with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact hn (h1.trans (hc.trans h2.symm))
  · exact hn (h1.trans (hc.symm.trans h2.symm))

lemma arc_light_h {c : Pt} {s : Side} (hs : s = .b ∨ s = .t) (he : sideEdge c s ∉ H) :
    outArc H c s = !par c := by
  rw [outArc_eq]
  rcases hs with rfl | rfl <;> simp only [Side.horiz, he, decide_false, ↓reduceIte] <;>
    cases par c <;> rfl

lemma arc_light_v {c : Pt} {s : Side} (hs : s = .l ∨ s = .r) (he : sideEdge c s ∉ H) :
    outArc H c s = par c := by
  rw [outArc_eq]
  rcases hs with rfl | rfl <;> simp only [Side.horiz, he, decide_false, Bool.false_eq_true,
    ↓reduceIte] <;> cases par c <;> rfl

-- A horizontal and a vertical `x|y` side: not extremal.
--
lemma not_ext_perp {c x y : Pt} {o : Bool} {s1 s2 : Side} (hs1 : s1 = .b ∨ s1 = .t)
    (hs2 : s2 = .l ∨ s2 = .r) (hn : ¬ Conn H x y) (h1 : Joins H (sideEdge c s1) x y)
    (h2 : Joins H (sideEdge c s2) x y) (hext : CutExt H o c x y) : False := by
  have a1 := arc_light_h hs1 (light_of_joins h1 hn)
  have a2 := arc_light_v hs2 (light_of_joins h2 hn)
  have e1 := hext s1 h1
  have e2 := hext s2 h2
  rw [a1] at e1; rw [a2] at e2
  revert e1 e2
  cases o <;> cases par c <;> simp

/-! ## The final state -/

-- Three corners of `c` on three different pieces.
--
def Three (H : Finset Edge) (c : Pt) : Prop :=
  ∃ u v w, IsCorner u c ∧ IsCorner v c ∧ IsCorner w c ∧ ¬ Conn H u v ∧ ¬ Conn H v w ∧ ¬ Conn H u w

-- (F4) for one fixed pair: across its light sides the top is higher than its neighbours and the
-- bottom lower; the top is higher than the bottom; `(tx, ty)`, `(bx, by)` are the cut pieces.
--
def PairOK (H : Finset Edge) (i : FixedPr) : Prop :=
  (∀ s, sideEdge i.top s ∉ H → outArc H i.top s = false) ∧
  (∀ s, sideEdge i.bot s ∉ H → outArc H i.bot s = true) ∧ outArc H i.bot i.s = true ∧
  (∀ u v, IsCorner u i.top → IsCorner v i.top → ¬ Conn H u v → PEq H u v i.tx i.ty) ∧
  (∀ u v, IsCorner u i.bot → IsCorner v i.bot → ¬ Conn H u v → PEq H u v i.bx i.by')

-- (F5): no movable square. Corners `a = c`, `b`, `C`, `d` (counterclockwise).
--
def NoMove (V : Finset Pt) (H H' : Finset Edge) : Prop :=
  ∀ (o : Bool) (c : Pt), IsCell V c → ¬ Alt H c → 0 < sgnD o (D H H' c) →
    ¬ ((Conn H c (c.1 + 1, c.2) ∧ Conn H (c.1, c.2 + 1) (c.1 + 1, c.2 + 1) ∧
          ¬ Conn H c (c.1, c.2 + 1) ∧ outArc H c .l ≠ o ∧ outArc H c .r ≠ o) ∨
       (Conn H c (c.1, c.2 + 1) ∧ Conn H (c.1 + 1, c.2) (c.1 + 1, c.2 + 1) ∧
          ¬ Conn H c (c.1 + 1, c.2) ∧ outArc H c .b ≠ o ∧ outArc H c .t ≠ o))

-- (F3): three pieces at an extremal cell (the E1 square at `t`) are paid through a third piece.
--
def ThreeOK (V : Finset Pt) (H H' : Finset Edge) (FP : List FixedPr) : Prop :=
  ∀ o x y c, ¬ Conn H x y → IsCell V c → 0 < sgnD o (D H H' c) →
    (∃ s, Joins H (sideEdge c s) x y) → CutExt H o c x y → Three H c →
      ∃ z c1 c2, IsCell V c1 ∧ 0 < sgnD o (D H H' c1) ∧
        (∃ s, Joins H (sideEdge c1 s) x z ∧ IsCell V (nb c1 s)) ∧
        IsCell V c2 ∧ 0 < sgnD o (D H H' c2) ∧ (∃ s, Joins H (sideEdge c2 s) z y ∧ IsCell V (nb c2 s)) ∧
        ExtFixed V H H' FP o x z ∧ ExtFixed V H H' FP o z y

-- The fixed-square case: an alternating 2+2 cell with pieces `(u, v)` on a side pair.
--
lemma fixed_case {FP : List FixedPr} (hF2 : ∀ c, IsCell V c → Alt H c → CutSq H c →
      ∃ i ∈ FP, c = i.top ∨ c = i.bot) (hF4 : ∀ i ∈ FP, PairOK H i)
    {o : Bool} {c x y u v : Pt} (hc : IsCell V c) (halt : Alt H c) (hcut : CutSq H c)
    (hu : IsCorner u c) (hv : IsCorner v c) (huv : ¬ Conn H u v) (hpq : PEq H x y u v)
    {s : Side} (hlight : sideEdge c s ∉ H) (harc : outArc H c s ≠ o) :
    ∃ i ∈ FP, c = i.ext o ∧ PEq H x y (i.px o) (i.py o) := by
  obtain ⟨i, hi, hci⟩ := hF2 c hc halt hcut
  obtain ⟨htop, hbot, _, hpt, hpb⟩ := hF4 i hi
  rcases hci with rfl | rfl
  · have : o = true := by have := htop s hlight; cases o <;> simp_all
    subst this
    exact ⟨i, hi, rfl, peq_trans hpq (hpt u v hu hv huv)⟩
  · have : o = false := by have := hbot s hlight; cases o <;> simp_all
    subst this
    exact ⟨i, hi, rfl, peq_trans hpq (hpb u v hu hv huv)⟩

-- **Extremal cells in a final state** are fixed squares, or touch three pieces.
--
theorem ext_cases {FP : List FixedPr}
    (hF2 : ∀ c, IsCell V c → Alt H c → CutSq H c → ∃ i ∈ FP, c = i.top ∨ c = i.bot)
    (hF4 : ∀ i ∈ FP, PairOK H i) (hF5 : NoMove V H H') {o : Bool} {x y c : Pt}
    (hn : ¬ Conn H x y) (hc : IsCell V c) (hpos : 0 < sgnD o (D H H' c))
    (hj : ∃ s, Joins H (sideEdge c s) x y) (hext : CutExt H o c x y) :
    (∃ i ∈ FP, c = i.ext o ∧ PEq H x y (i.px o) (i.py o)) ∨ Three H c := by
  obtain ⟨s0, hj0⟩ := hj
  obtain ⟨x0, y0⟩ := c
  set a : Pt := (x0, y0)
  set b : Pt := (x0 + 1, y0)
  set C : Pt := (x0 + 1, y0 + 1)
  set d : Pt := (x0, y0 + 1)
  have ca : IsCorner a (x0, y0) := Or.inl rfl
  have cb : IsCorner b (x0, y0) := Or.inr (Or.inl rfl)
  have cd : IsCorner d (x0, y0) := Or.inr (Or.inr (Or.inl rfl))
  have cC : IsCorner C (x0, y0) := Or.inr (Or.inr (Or.inr rfl))
  -- The four sides as `Joins` statements on corners.
  --
  have jb : ∀ u v, Joins H (sideEdge (x0, y0) .b) u v ↔ PEq H u v a b := fun u v => Iff.rfl
  have jt : ∀ u v, Joins H (sideEdge (x0, y0) .t) u v ↔ PEq H u v d C := fun u v => Iff.rfl
  have jl : ∀ u v, Joins H (sideEdge (x0, y0) .l) u v ↔ PEq H u v a d := fun u v => Iff.rfl
  have jr : ∀ u v, Joins H (sideEdge (x0, y0) .r) u v ↔ PEq H u v b C := fun u v => Iff.rfl
  have three : Three H (x0, y0) →
      (∃ i ∈ FP, (x0, y0) = i.ext o ∧ PEq H x y (i.px o) (i.py o)) ∨ Three H (x0, y0) :=
    fun h3 => Or.inr h3
  have nC : ∀ {u v}, PEq H x y u v → ¬ Conn H u v := by
    intro u v h huv
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact hn (h1.trans (huv.trans h2.symm))
    · exact hn (h1.trans (huv.symm.trans h2.symm))
  -- Vertical `x|y` sides: the `l`/`r` case; horizontal: the `b`/`t` case.
  --
  by_cases hv : Joins H (sideEdge (x0, y0) .l) x y ∨ Joins H (sideEdge (x0, y0) .r) x y
  · have nJb : ¬ Joins H (sideEdge (x0, y0) .b) x y := fun h => by
      rcases hv with hv | hv
      · exact not_ext_perp (Or.inl rfl) (Or.inl rfl) hn h hv hext
      · exact not_ext_perp (Or.inl rfl) (Or.inr rfl) hn h hv hext
    have nJt : ¬ Joins H (sideEdge (x0, y0) .t) x y := fun h => by
      rcases hv with hv | hv
      · exact not_ext_perp (Or.inr rfl) (Or.inl rfl) hn h hv hext
      · exact not_ext_perp (Or.inr rfl) (Or.inr rfl) hn h hv hext
    by_cases hl : Joins H (sideEdge (x0, y0) .l) x y
    · have pad : PEq H x y a d := hl
      have nad := nC pad
      have ndb : ¬ Conn H d b := fun h => nJb (joins_peq pad (Or.inl ⟨Conn.refl _ _, h⟩))
      have naC : ¬ Conn H a C := fun h => nJt (joins_peq pad (Or.inr ⟨h, Conn.refl _ _⟩))
      by_cases hab : Conn H a b
      · by_cases hdC : Conn H d C
        · have hr : Joins H (sideEdge (x0, y0) .r) x y :=
            joins_peq pad (Or.inl ⟨hab, hdC⟩)
          have al := hext .l hl
          have ar := hext .r hr
          have hcut : CutSq H (x0, y0) := fun ⟨_, _, h⟩ => nad h
          by_cases halt : Alt H (x0, y0)
          · exact Or.inl (fixed_case hF2 hF4 hc halt hcut ca cd nad pad (light_of_joins hl hn) al)
          · exact absurd (Or.inl ⟨hab, hdC, nad, al, ar⟩) (hF5 o _ hc halt hpos)
        · exact three ⟨a, d, C, ca, cd, cC, nad, fun h => hdC h, naC⟩
      · exact three ⟨a, b, d, ca, cb, cd, hab, fun h => ndb h.symm, nad⟩
    · have hr : Joins H (sideEdge (x0, y0) .r) x y := hv.resolve_left hl
      have pbC : PEq H x y b C := hr
      have nbC := nC pbC
      have nCa : ¬ Conn H C a := fun h => nJb (joins_peq pbC (Or.inr ⟨Conn.refl _ _, h⟩))
      have nbd : ¬ Conn H b d := fun h => nJt (joins_peq pbC (Or.inl ⟨h, Conn.refl _ _⟩))
      by_cases hba : Conn H b a
      · have nCd : ¬ Conn H C d := fun h => hl (joins_peq pbC (Or.inl ⟨hba, h⟩))
        exact three ⟨b, C, d, cb, cC, cd, nbC, nCd, nbd⟩
      · exact three ⟨a, b, C, ca, cb, cC, fun h => hba h.symm, nbC, fun h => nCa h.symm⟩
  · have hh : Joins H (sideEdge (x0, y0) .b) x y ∨ Joins H (sideEdge (x0, y0) .t) x y := by
      cases s0
      · exact Or.inl hj0
      · exact Or.inr hj0
      · exact absurd (Or.inl hj0) hv
      · exact absurd (Or.inr hj0) hv
    have nJl : ¬ Joins H (sideEdge (x0, y0) .l) x y := fun h => hv (Or.inl h)
    have nJr : ¬ Joins H (sideEdge (x0, y0) .r) x y := fun h => hv (Or.inr h)
    by_cases hb : Joins H (sideEdge (x0, y0) .b) x y
    · have pab : PEq H x y a b := hb
      have nab := nC pab
      have nbd : ¬ Conn H b d := fun h => nJl (joins_peq pab (Or.inl ⟨Conn.refl _ _, h⟩))
      have naC : ¬ Conn H a C := fun h => nJr (joins_peq pab (Or.inr ⟨h, Conn.refl _ _⟩))
      by_cases had : Conn H a d
      · by_cases hbC : Conn H b C
        · have ht : Joins H (sideEdge (x0, y0) .t) x y :=
            joins_peq pab (Or.inl ⟨had, hbC⟩)
          have ab := hext .b hb
          have at' := hext .t ht
          have hcut : CutSq H (x0, y0) := fun ⟨h, _, _⟩ => nab h
          by_cases halt : Alt H (x0, y0)
          · exact Or.inl (fixed_case hF2 hF4 hc halt hcut ca cb nab pab (light_of_joins hb hn) ab)
          · exact absurd (Or.inr ⟨had, hbC, nab, ab, at'⟩) (hF5 o _ hc halt hpos)
        · exact three ⟨a, b, C, ca, cb, cC, nab, hbC, naC⟩
      · exact three ⟨a, b, d, ca, cb, cd, nab, nbd, had⟩
    · have ht : Joins H (sideEdge (x0, y0) .t) x y := hh.resolve_left hb
      have pdC : PEq H x y d C := ht
      have ndC := nC pdC
      have nCa : ¬ Conn H C a := fun h => nJl (joins_peq pdC (Or.inr ⟨Conn.refl _ _, h⟩))
      have ndb : ¬ Conn H d b := fun h => nJr (joins_peq pdC (Or.inl ⟨h, Conn.refl _ _⟩))
      by_cases hda : Conn H d a
      · have nCb : ¬ Conn H C b := fun h => hb (joins_peq pdC (Or.inl ⟨hda, h⟩))
        exact three ⟨d, C, b, cd, cC, cb, ndC, nCb, ndb⟩
      · exact three ⟨a, d, C, ca, cd, cC, fun h => hda h.symm, ndC, fun h => nCa h.symm⟩

-- **`FinalOK` from the final-state shape.**
--
theorem finalOK_of {FP : List FixedPr}
    (hF2 : ∀ c, IsCell V c → Alt H c → CutSq H c → ∃ i ∈ FP, c = i.top ∨ c = i.bot)
    (hF3 : ThreeOK V H H' FP) (hF4 : ∀ i ∈ FP, PairOK H i) (hF5 : NoMove V H H') :
    FinalOK V H H' FP := by
  intro o x y c hn hc hpos ⟨s0, hj0⟩ hext
  obtain ⟨x0, y0⟩ := c
  set a : Pt := (x0, y0)
  set b : Pt := (x0 + 1, y0)
  set C : Pt := (x0 + 1, y0 + 1)
  set d : Pt := (x0, y0 + 1)
  have ca : IsCorner a (x0, y0) := Or.inl rfl
  have cb : IsCorner b (x0, y0) := Or.inr (Or.inl rfl)
  have cd : IsCorner d (x0, y0) := Or.inr (Or.inr (Or.inl rfl))
  have cC : IsCorner C (x0, y0) := Or.inr (Or.inr (Or.inr rfl))
  -- The four sides as `Joins` statements on corners.
  --
  have jb : ∀ u v, Joins H (sideEdge (x0, y0) .b) u v ↔ PEq H u v a b := fun u v => Iff.rfl
  have jt : ∀ u v, Joins H (sideEdge (x0, y0) .t) u v ↔ PEq H u v d C := fun u v => Iff.rfl
  have jl : ∀ u v, Joins H (sideEdge (x0, y0) .l) u v ↔ PEq H u v a d := fun u v => Iff.rfl
  have jr : ∀ u v, Joins H (sideEdge (x0, y0) .r) u v ↔ PEq H u v b C := fun u v => Iff.rfl
  have three : Three H (x0, y0) →
      (∃ i ∈ FP, (x0, y0) = i.ext o ∧ PEq H x y (i.px o) (i.py o)) ∨
      ∃ z c1 c2, IsCell V c1 ∧ 0 < sgnD o (D H H' c1) ∧
        (∃ s, Joins H (sideEdge c1 s) x z ∧ IsCell V (nb c1 s)) ∧
        IsCell V c2 ∧ 0 < sgnD o (D H H' c2) ∧ (∃ s, Joins H (sideEdge c2 s) z y ∧ IsCell V (nb c2 s)) ∧
        ExtFixed V H H' FP o x z ∧ ExtFixed V H H' FP o z y :=
    fun h3 => Or.inr (hF3 o x y _ hn hc hpos ⟨s0, hj0⟩ hext h3)
  have nC : ∀ {u v}, PEq H x y u v → ¬ Conn H u v := by
    intro u v h huv
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact hn (h1.trans (huv.trans h2.symm))
    · exact hn (h1.trans (huv.symm.trans h2.symm))
  -- Vertical `x|y` sides: the `l`/`r` case; horizontal: the `b`/`t` case.
  --
  by_cases hv : Joins H (sideEdge (x0, y0) .l) x y ∨ Joins H (sideEdge (x0, y0) .r) x y
  · have nJb : ¬ Joins H (sideEdge (x0, y0) .b) x y := fun h => by
      rcases hv with hv | hv
      · exact not_ext_perp (Or.inl rfl) (Or.inl rfl) hn h hv hext
      · exact not_ext_perp (Or.inl rfl) (Or.inr rfl) hn h hv hext
    have nJt : ¬ Joins H (sideEdge (x0, y0) .t) x y := fun h => by
      rcases hv with hv | hv
      · exact not_ext_perp (Or.inr rfl) (Or.inl rfl) hn h hv hext
      · exact not_ext_perp (Or.inr rfl) (Or.inr rfl) hn h hv hext
    by_cases hl : Joins H (sideEdge (x0, y0) .l) x y
    · have pad : PEq H x y a d := hl
      have nad := nC pad
      have ndb : ¬ Conn H d b := fun h => nJb (joins_peq pad (Or.inl ⟨Conn.refl _ _, h⟩))
      have naC : ¬ Conn H a C := fun h => nJt (joins_peq pad (Or.inr ⟨h, Conn.refl _ _⟩))
      by_cases hab : Conn H a b
      · by_cases hdC : Conn H d C
        · have hr : Joins H (sideEdge (x0, y0) .r) x y :=
            joins_peq pad (Or.inl ⟨hab, hdC⟩)
          have al := hext .l hl
          have ar := hext .r hr
          have hcut : CutSq H (x0, y0) := fun ⟨_, _, h⟩ => nad h
          by_cases halt : Alt H (x0, y0)
          · exact Or.inl (fixed_case hF2 hF4 hc halt hcut ca cd nad pad (light_of_joins hl hn) al)
          · exact absurd (Or.inl ⟨hab, hdC, nad, al, ar⟩) (hF5 o _ hc halt hpos)
        · exact three ⟨a, d, C, ca, cd, cC, nad, fun h => hdC h, naC⟩
      · exact three ⟨a, b, d, ca, cb, cd, hab, fun h => ndb h.symm, nad⟩
    · have hr : Joins H (sideEdge (x0, y0) .r) x y := hv.resolve_left hl
      have pbC : PEq H x y b C := hr
      have nbC := nC pbC
      have nCa : ¬ Conn H C a := fun h => nJb (joins_peq pbC (Or.inr ⟨Conn.refl _ _, h⟩))
      have nbd : ¬ Conn H b d := fun h => nJt (joins_peq pbC (Or.inl ⟨h, Conn.refl _ _⟩))
      by_cases hba : Conn H b a
      · have nCd : ¬ Conn H C d := fun h => hl (joins_peq pbC (Or.inl ⟨hba, h⟩))
        exact three ⟨b, C, d, cb, cC, cd, nbC, nCd, nbd⟩
      · exact three ⟨a, b, C, ca, cb, cC, fun h => hba h.symm, nbC, fun h => nCa h.symm⟩
  · have hh : Joins H (sideEdge (x0, y0) .b) x y ∨ Joins H (sideEdge (x0, y0) .t) x y := by
      cases s0
      · exact Or.inl hj0
      · exact Or.inr hj0
      · exact absurd (Or.inl hj0) hv
      · exact absurd (Or.inr hj0) hv
    have nJl : ¬ Joins H (sideEdge (x0, y0) .l) x y := fun h => hv (Or.inl h)
    have nJr : ¬ Joins H (sideEdge (x0, y0) .r) x y := fun h => hv (Or.inr h)
    by_cases hb : Joins H (sideEdge (x0, y0) .b) x y
    · have pab : PEq H x y a b := hb
      have nab := nC pab
      have nbd : ¬ Conn H b d := fun h => nJl (joins_peq pab (Or.inl ⟨Conn.refl _ _, h⟩))
      have naC : ¬ Conn H a C := fun h => nJr (joins_peq pab (Or.inr ⟨h, Conn.refl _ _⟩))
      by_cases had : Conn H a d
      · by_cases hbC : Conn H b C
        · have ht : Joins H (sideEdge (x0, y0) .t) x y :=
            joins_peq pab (Or.inl ⟨had, hbC⟩)
          have ab := hext .b hb
          have at' := hext .t ht
          have hcut : CutSq H (x0, y0) := fun ⟨h, _, _⟩ => nab h
          by_cases halt : Alt H (x0, y0)
          · exact Or.inl (fixed_case hF2 hF4 hc halt hcut ca cb nab pab (light_of_joins hb hn) ab)
          · exact absurd (Or.inr ⟨had, hbC, nab, ab, at'⟩) (hF5 o _ hc halt hpos)
        · exact three ⟨a, b, C, ca, cb, cC, nab, hbC, naC⟩
      · exact three ⟨a, b, d, ca, cb, cd, nab, nbd, had⟩
    · have ht : Joins H (sideEdge (x0, y0) .t) x y := hh.resolve_left hb
      have pdC : PEq H x y d C := ht
      have ndC := nC pdC
      have nCa : ¬ Conn H C a := fun h => nJl (joins_peq pdC (Or.inr ⟨Conn.refl _ _, h⟩))
      have ndb : ¬ Conn H d b := fun h => nJr (joins_peq pdC (Or.inl ⟨h, Conn.refl _ _⟩))
      by_cases hda : Conn H d a
      · have nCb : ¬ Conn H C b := fun h => hb (joins_peq pdC (Or.inl ⟨hda, h⟩))
        exact three ⟨d, C, b, cd, cC, cb, ndC, nCb, ndb⟩
      · exact three ⟨a, d, C, ca, cd, cC, fun h => hda h.symm, ndC, fun h => nCa h.symm⟩

-- **The count in a final state.**
--
theorem count_final {W : Finset Pt} {d : Pt → ℕ} {FP : List FixedPr}
    (hH : IsFactor W d H) (hH' : IsFactor W d H') (hac : ClimbAcyc V H) (hsol : SolidFor V H H')
    (hF2 : ∀ c, IsCell V c → Alt H c → CutSq H c → ∃ i ∈ FP, c = i.top ∨ c = i.bot)
    (hF3 : ThreeOK V H H' FP) (hF4 : ∀ i ∈ FP, PairOK H i) (hF5 : NoMove V H H') :
    ncomp W H ≤ ncomp W H' + FP.length :=
  final_count hH hH' hsol hac FP (fun i hi => (hF4 i hi).2.2.1)
    (finalOK_of hF2 hF3 hF4 hF5)

end finallocal

end HP

end ULHC
