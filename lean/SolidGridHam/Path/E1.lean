/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
module

public import SolidGridHam.Path.Move

@[expose] public section

/-!
# E1: the three-piece square at the notch endpoint

`TriShape V H t f` (E1's shape, NOTCH_SHEFFIELD §1): in some frame `sd`, the front corners of `f`
are alone (each on a piece of its own among `f`'s corners), `t` is one of them, the back corners
are joined, and the square across the front is not a cell.

From the shape:
* **uniqueness** (`tri_unique`): two such cells would have three or four light edges at `t`;
* **the triangle** (`threeOK_of_tri`): `f` is relevant-extremal only for the pair of its front
  corners, its lateral neighbours carry the cuts to the back pair with `D` of the same sign, and no
  other three-piece cell interferes, so `ThreeOK` holds in a final state.
-/

namespace SolidGridHam

namespace HP

open Finset Classical

def TriShape (V : Finset Pt) (H : Finset Edge) (t f : Pt) : Prop :=
  ∃ sd, (t = front1 f sd ∨ t = front2 f sd) ∧ ¬ IsCell V (nb f sd) ∧
    Conn H (back1 f sd) (back2 f sd) ∧ ¬ Conn H (front1 f sd) (front2 f sd) ∧
    ¬ Conn H (front1 f sd) (back1 f sd) ∧ ¬ Conn H (front2 f sd) (back2 f sd)

-- A cell whose diagonal corners share a piece and whose sides all join different pieces (the
-- 2+1+1 cell with diagonal lone corners). It is never cut-extremal (`diag_not_ext`).
--
def DiagShape (H : Finset Edge) (f : Pt) : Prop :=
  (∀ sd, ¬ Conn H (front1 f sd) (front2 f sd)) ∧
    (Conn H (f.1, f.2) (f.1 + 1, f.2 + 1) ∨ Conn H (f.1 + 1, f.2) (f.1, f.2 + 1))

-- The shape of a three-piece cell: E1's, or diagonal.
--
def TriOK (V : Finset Pt) (H : Finset Edge) (t u f : Pt) : Prop :=
  (TriShape V H t f ∨ TriShape V H u f) ∨ DiagShape H f

section e1

variable {V : Finset Pt} {H : Finset Edge}

lemma TriOK.ex {t u f : Pt} (h : TriOK V H t u f) :
    (∃ w, (w = t ∨ w = u) ∧ TriShape V H w f) ∨ DiagShape H f := by
  rcases h with (h | h) | h
  · exact Or.inl ⟨t, Or.inl rfl, h⟩
  · exact Or.inl ⟨u, Or.inr rfl, h⟩
  · exact Or.inr h

-- `t` is alone among the corners of an E1 cell.
--
lemma TriShape.alone {t f : Pt} (h : TriShape V H t f) :
    ∀ u, IsCorner u f → u ≠ t → ¬ Conn H t u := by
  obtain ⟨sd, ht, _, hbb, hff, h11, h22⟩ := h
  intro u hu hut hc
  rcases corner_cases f sd hu with rfl | rfl | rfl | rfl <;> rcases ht with rfl | rfl
  · exact h11 hc
  · exact h22 (hc.trans hbb)
  · exact h11 (hc.trans hbb.symm)
  · exact h22 hc
  · exact hut rfl
  · exact hff hc.symm
  · exact hff hc
  · exact hut rfl

-- The sides of a cell at one of its corners are light when that corner is alone.
--
lemma side_light_of_alone {t f : Pt} (halone : ∀ u, IsCorner u f → u ≠ t → ¬ Conn H t u)
    {e : Edge} (he : e ∈ cellE f) (ht : e.p = t ∨ e.q = t) : e ∉ H := by
  intro heH
  have hc : Conn H e.p e.q := Conn.of_edge heH
  have hcp : IsCorner e.p f ∧ IsCorner e.q f := by
    obtain ⟨x, y⟩ := f
    simp only [cellE, Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with rfl | rfl | rfl | rfl <;> simp [IsCorner, bot, top, lft, rgt, Edge.q]
  have hne := Edge.p_ne_q e
  rcases ht with h | h
  · exact halone e.q hcp.2 (by rw [← h]; exact fun h' => hne h'.symm) (by rw [← h]; exact hc)
  · exact halone e.p hcp.1 (by rw [← h]; exact hne) (by rw [← h]; exact hc.symm)

-- **At most one E1 cell**: two would leave at most one dark edge at `t`.
--
theorem tri_unique {t f g : Pt} (hf : TriShape V H t f) (hg : TriShape V H t g)
    (hdeg : deg H t = 2) : f = g := by
  have af := hf.alone
  have ag := hg.alone
  have cf : IsCorner t f := by
    obtain ⟨sd, ht, _⟩ := hf; rcases ht with rfl | rfl
    · exact isCorner_front1 f sd
    · exact isCorner_front2 f sd
  have cg : IsCorner t g := by
    obtain ⟨sd, ht, _⟩ := hg; rcases ht with rfl | rfl
    · exact isCorner_front1 g sd
    · exact isCorner_front2 g sd
  by_contra hne
  obtain ⟨tx, ty⟩ := t
  have pos : ∀ q : Pt, IsCorner (tx, ty) q →
      q = (tx, ty) ∨ q = (tx - 1, ty) ∨ q = (tx, ty - 1) ∨ q = (tx - 1, ty - 1) := by
    intro q hq
    obtain ⟨a, b⟩ := q
    rcases hq with h | h | h | h <;> simp only [Prod.mk.injEq] at h
    · left; rw [h.1, h.2]
    · right; left; ext <;> simp <;> omega
    · right; right; left; ext <;> simp <;> omega
    · right; right; right; ext <;> simp <;> omega
  -- The two sides at `t` of each possible cell are light.
  have lt : ∀ q : Pt, (∀ u, IsCorner u q → u ≠ (tx, ty) → ¬ Conn H (tx, ty) u) →
      (q = (tx, ty) → eR (tx, ty) ∉ H ∧ eU (tx, ty) ∉ H) ∧
      (q = (tx - 1, ty) → eL (tx, ty) ∉ H ∧ eU (tx, ty) ∉ H) ∧
      (q = (tx, ty - 1) → eR (tx, ty) ∉ H ∧ eD (tx, ty) ∉ H) ∧
      (q = (tx - 1, ty - 1) → eL (tx, ty) ∉ H ∧ eD (tx, ty) ∉ H) := by
    intro q hq
    refine ⟨fun h => ⟨?_, ?_⟩, fun h => ⟨?_, ?_⟩, fun h => ⟨?_, ?_⟩, fun h => ⟨?_, ?_⟩⟩ <;>
      subst h <;> apply side_light_of_alone hq <;>
      simp [cellE, eR, eL, eU, eD, bot, top, lft, rgt, Edge.q]
  have lf := lt f af
  have lg := lt g ag
  unfold deg ind at hdeg
  rcases pos f cf with rfl | rfl | rfl | rfl <;> rcases pos g cg with rfl | rfl | rfl | rfl
  · exact hne rfl
  · have A := lf.1 rfl; have B := lg.2.1 rfl
    simp only [A.1, A.2, B.1, ite_false] at hdeg
    (try split_ifs at hdeg) <;> omega
  · have A := lf.1 rfl; have B := lg.2.2.1 rfl
    simp only [A.1, A.2, B.2, ite_false] at hdeg
    (try split_ifs at hdeg) <;> omega
  · have A := lf.1 rfl; have B := lg.2.2.2 rfl
    simp only [A.1, A.2, B.1, B.2, ite_false] at hdeg
    omega
  · have A := lf.2.1 rfl; have B := lg.1 rfl
    simp only [A.1, A.2, B.1, ite_false] at hdeg
    (try split_ifs at hdeg) <;> omega
  · exact hne rfl
  · have A := lf.2.1 rfl; have B := lg.2.2.1 rfl
    simp only [A.1, A.2, B.1, B.2, ite_false] at hdeg
    omega
  · have A := lf.2.1 rfl; have B := lg.2.2.2 rfl
    simp only [A.1, A.2, B.2, ite_false] at hdeg
    (try split_ifs at hdeg) <;> omega
  · have A := lf.2.2.1 rfl; have B := lg.1 rfl
    simp only [A.1, A.2, B.2, ite_false] at hdeg
    (try split_ifs at hdeg) <;> omega
  · have A := lf.2.2.1 rfl; have B := lg.2.1 rfl
    simp only [A.1, A.2, B.1, B.2, ite_false] at hdeg
    omega
  · exact hne rfl
  · have A := lf.2.2.1 rfl; have B := lg.2.2.2 rfl
    simp only [A.1, A.2, B.1, ite_false] at hdeg
    (try split_ifs at hdeg) <;> omega
  · have A := lf.2.2.2 rfl; have B := lg.1 rfl
    simp only [A.1, A.2, B.1, B.2, ite_false] at hdeg
    omega
  · have A := lf.2.2.2 rfl; have B := lg.2.1 rfl
    simp only [A.1, A.2, B.2, ite_false] at hdeg
    (try split_ifs at hdeg) <;> omega
  · have A := lf.2.2.2 rfl; have B := lg.2.2.1 rfl
    simp only [A.1, A.2, B.1, ite_false] at hdeg
    (try split_ifs at hdeg) <;> omega
  · exact hne rfl

lemma arc_perpA {F : Finset Edge} {q : Pt} {sd : Side} (h1 : sideEdge q sd ∉ F)
    (h2 : sideEdge q (latA sd) ∉ F) : outArc F q (latA sd) = !outArc F q sd := by
  rw [outArc_eq, outArc_eq]
  cases sd <;> simp only [latA, Side.horiz] at h2 ⊢ <;>
    simp only [h1, h2, decide_false, ↓reduceIte, Bool.false_eq_true] <;> cases par q <;> rfl

lemma arc_perpB {F : Finset Edge} {q : Pt} {sd : Side} (h1 : sideEdge q sd ∉ F)
    (h2 : sideEdge q (latB sd) ∉ F) : outArc F q (latB sd) = !outArc F q sd := by
  rw [outArc_eq, outArc_eq]
  cases sd <;> simp only [latB, Side.horiz] at h2 ⊢ <;>
    simp only [h1, h2, decide_false, ↓reduceIte, Bool.false_eq_true] <;> cases par q <;> rfl

lemma joins_of_ends {F : Finset Edge} {e : Edge} {u v x y : Pt} (he : Ends e u v)
    (hx : Conn F x u) (hy : Conn F y v) : Joins F e x y := by
  rcases he with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · left; rw [h1, h2]; exact ⟨hx, hy⟩
  · right; rw [h1, h2]; exact ⟨hx, hy⟩

lemma conn_of_joins {F : Finset Edge} {e : Edge} {u v x y : Pt} (he : Ends e u v)
    (hj : Joins F e x y) : (Conn F x u ∧ Conn F y v) ∨ (Conn F x v ∧ Conn F y u) := by
  rcases he with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases hj with ⟨j1, j2⟩ | ⟨j1, j2⟩ <;>
    rw [h1, h2] at * <;> tauto

lemma ends_swap {e : Edge} {u v : Pt} (h : Ends e u v) : Ends e v u := by
  rcases h with h | h
  · exact Or.inr h
  · exact Or.inl h

lemma joins_congr {F : Finset Edge} {e e' : Edge} {u v u' v' x y : Pt} (he : Ends e u v)
    (he' : Ends e' u' v') (hu : Conn F u u') (hv : Conn F v v') (hj : Joins F e x y) :
    Joins F e' x y := by
  rcases conn_of_joins he hj with ⟨a, b⟩ | ⟨a, b⟩
  · exact joins_of_ends he' (a.trans hu) (b.trans hv)
  · exact joins_of_ends (ends_swap he') (a.trans hv) (b.trans hu)

-- **A diagonal cell is never cut-extremal**: a side joining the cut has a perpendicular partner
-- sharing its lone end, which joins the cut too, and the two arcs disagree.
--
lemma diag_not_ext {F : Finset Edge} {f x y : Pt} {o : Bool} {s0 : Side} (hD : DiagShape F f)
    (hn : ¬ Conn F x y) (hj : Joins F (sideEdge f s0) x y) (hext : CutExt F o f x y) : False := by
  have eb : Ends (sideEdge f .b) (f.1, f.2) (f.1 + 1, f.2) := ends_front f .b
  have et : Ends (sideEdge f .t) (f.1, f.2 + 1) (f.1 + 1, f.2 + 1) := ends_front f .t
  have el : Ends (sideEdge f .l) (f.1, f.2) (f.1, f.2 + 1) := ends_front f .l
  have er : Ends (sideEdge f .r) (f.1 + 1, f.2) (f.1 + 1, f.2 + 1) := ends_front f .r
  have hb : (Side.b = .b ∨ Side.b = .t) := Or.inl rfl
  have ht : (Side.t = .b ∨ Side.t = .t) := Or.inr rfl
  have hl : (Side.l = .l ∨ Side.l = .r) := Or.inl rfl
  have hr : (Side.r = .l ∨ Side.r = .r) := Or.inr rfl
  have R := Conn.refl F
  rcases hD.2 with d | d <;> cases s0
  · exact not_ext_perp hb hr hn hj (joins_congr eb (ends_swap er) d (R _) hj) hext
  · exact not_ext_perp ht hl hn hj (joins_congr et (ends_swap el) (R _) d.symm hj) hext
  · exact not_ext_perp ht hl hn (joins_congr el (ends_swap et) d (R _) hj) hj hext
  · exact not_ext_perp hb hr hn (joins_congr er (ends_swap eb) (R _) d.symm hj) hj hext
  · exact not_ext_perp hb hl hn hj (joins_congr eb el (R _) d hj) hext
  · exact not_ext_perp ht hr hn hj (joins_congr et er d.symm (R _) hj) hext
  · exact not_ext_perp hb hl hn (joins_congr el eb (R _) d.symm hj) hj hext
  · exact not_ext_perp ht hr hn (joins_congr er et d (R _) hj) hj hext

end e1

section tri

variable {V W : Finset Pt} {d : Pt → ℕ} {H H' : Finset Edge}
  (hH : IsFactor W d H) (hH' : IsFactor W d H')
include hH hH'

-- An E1-shaped cell (at any lone corner `w`) is never cut-extremal with `D` of the extremal
-- sign along a cut whose side has a cell across it: across the front lies a non-cell, the back
-- joins one piece, and along a lateral the arcs force `D` of the other sign.
--
lemma tri_not_ext (hsol : SolidFor V H H') {w g u v : Pt} {o : Bool} (hT : TriShape V H w g)
    (hpos : 0 < sgnD o (D H H' g)) (huv : ¬ Conn H u v) {s1 : Side}
    (hj : Joins H (sideEdge g s1) u v) (hc : IsCell V (nb g s1)) (hext : CutExt H o g u v) :
    False := by
  obtain ⟨sd, _, hout, hbb, hff, h11, h22⟩ := hT
  have lf : sideEdge g sd ∉ H := fun h => hff ((ends_front g sd).conn h)
  have l1 : sideEdge g (latA sd) ∉ H := by
    rw [← lat1_eq]; exact fun h => h11 ((ends_lat1 g sd).conn h).symm
  have l2 : sideEdge g (latB sd) ∉ H := by
    rw [← lat2_eq]; exact fun h => h22 ((ends_lat2 g sd).conn h).symm
  have aA := arc_perpA lf l1
  have aB := arc_perpB lf l2
  have hstep := sgnD_step hH hH' (c := g) (s := sd) (o := outArc H g sd) rfl
  rw [hsol _ hout] at hstep
  simp only [sgnD] at hstep
  rcases side_cases sd s1 with h | h | h | h <;> subst s1
  · exact hout hc
  · have hb : Ends (sideEdge g sd.opp) (back1 g sd) (back2 g sd) := ends_back g sd
    rcases conn_of_joins hb hj with ⟨hx, hy⟩ | ⟨hx, hy⟩
    · exact huv (hx.trans (hbb.trans hy.symm))
    · exact huv (hx.trans (hbb.symm.trans hy.symm))
  · have := hext _ hj; rw [aA] at this
    have ho : o = outArc H g sd := by cases o <;> cases h' : outArc H g sd <;> simp_all
    rw [ho] at hpos
    unfold sgnD at hpos; split_ifs at hstep hpos <;> omega
  · have := hext _ hj; rw [aB] at this
    have ho : o = outArc H g sd := by cases o <;> cases h' : outArc H g sd <;> simp_all
    rw [ho] at hpos
    unfold sgnD at hpos; split_ifs at hstep hpos <;> omega

-- **The triangle.** In a final state whose three-piece cells have E1's shape (at any lone corner)
-- or the diagonal shape, `ThreeOK` holds.
--
theorem threeOK_of_tri {FP : List FixedPr} (hsol : SolidFor V H H')
    (hF2 : ∀ c, IsCell V c → Alt H c → CutSq H c → ∃ i ∈ FP, c = i.top ∨ c = i.bot)
    (hF4 : ∀ i ∈ FP, PairOK H i) (hF5 : NoMove V H H')
    (htri : ∀ f, IsCell V f → Three H f → (∃ w, TriShape V H w f) ∨ DiagShape H f) :
    ThreeOK V H H' FP := by
  intro o x y f hn hf hpos ⟨s0, hj0⟩ hext h3
  rcases htri f hf h3 with ⟨t, hshape⟩ | hD
  swap
  · exact (diag_not_ext hD hn hj0 hext).elim
  obtain ⟨sd, _, hout, hbb, hff, h11, h22⟩ := id hshape
  have lf : sideEdge f sd ∉ H := fun h => hff ((ends_front f sd).conn h)
  have l1 : sideEdge f (latA sd) ∉ H := by
    rw [← lat1_eq]; exact fun h => h11 ((ends_lat1 f sd).conn h).symm
  have l2 : sideEdge f (latB sd) ∉ H := by
    rw [← lat2_eq]; exact fun h => h22 ((ends_lat2 f sd).conn h).symm
  have aA := arc_perpA lf l1
  have aB := arc_perpB lf l2
  rcases side_cases sd s0 with h | h | h | h <;> subst s0
  · -- The front: the pair of `f`'s lone corners.
    have ho : outArc H f sd = !o := by
      have := hext sd hj0; cases o <;> cases h' : outArc H f sd <;> simp_all
    rw [ho] at aA aB
    simp only [Bool.not_not] at aA aB
    have mA := sgnD_step hH hH' (c := f) (s := latA sd) aA
    have mB := sgnD_step hH hH' (c := f) (s := latB sd) aB
    have cellOf : ∀ q, 0 < sgnD o (D H H' q) → IsCell V q := fun q hq => by
      by_contra hc; rw [hsol q hc] at hq; simp [sgnD] at hq
    have cA := cellOf _ (lt_of_lt_of_le hpos mA)
    have cB := cellOf _ (lt_of_lt_of_le hpos mB)
    have eA : sideEdge (nb f (latA sd)) (latA sd).opp = lat1 f sd := by
      rw [sideEdge_nb_opp, lat1_eq]
    have eB : sideEdge (nb f (latB sd)) (latB sd).opp = lat2 f sd := by
      rw [sideEdge_nb_opp, lat2_eq]
    have bA : IsCell V (nb (nb f (latA sd)) (latA sd).opp) := by rw [nb_nb_opp]; exact hf
    have bB : IsCell V (nb (nb f (latB sd)) (latB sd).opp) := by rw [nb_nb_opp]; exact hf
    have extF : ∀ {u v : Pt}, ¬ Conn H u v → ExtFixed V H H' FP o u v := by
      intro u v huv g hg hposg ⟨s1, hj1, hc1⟩ hextg
      rcases ext_cases hF2 hF4 hF5 huv hg hposg ⟨s1, hj1⟩ hextg with hfix | hg3
      · exact hfix
      · rcases htri g hg hg3 with ⟨w, hgT⟩ | hgD
        · exact (tri_not_ext hH hH' hsol hgT hposg huv hj1 hc1 hextg).elim
        · exact (diag_not_ext hgD huv hj1 hextg).elim
    rcases conn_of_joins (ends_front f sd) hj0 with ⟨hx, hy⟩ | ⟨hx, hy⟩
    · -- `x` on `front1`, `y` on `front2`
      have nxz : ¬ Conn H x (back1 f sd) := fun h => h11 (hx.symm.trans h)
      have nzy : ¬ Conn H (back1 f sd) y := fun h => h22 (hy.symm.trans (h.symm.trans hbb))
      have jA : Joins H (sideEdge f (latA sd)) x (back1 f sd) := by
        rw [← lat1_eq]; exact joins_of_ends (ends_swap (ends_lat1 f sd)) hx (Conn.refl _ _)
      have jB : Joins H (sideEdge f (latB sd)) (back1 f sd) y := by
        rw [← lat2_eq]; exact joins_of_ends (ends_lat2 f sd) hbb hy
      refine ⟨back1 f sd, nb f (latA sd), nb f (latB sd), cA, lt_of_lt_of_le hpos mA,
        ⟨(latA sd).opp, by rw [eA, lat1_eq]; exact jA, bA⟩, cB,
        lt_of_lt_of_le hpos mB, ⟨(latB sd).opp, by rw [eB, lat2_eq]; exact jB, bB⟩,
        extF nxz, extF nzy⟩
    · -- `x` on `front2`, `y` on `front1`
      have nxz : ¬ Conn H x (back1 f sd) := fun h => h22 (hx.symm.trans (h.trans hbb))
      have nzy : ¬ Conn H (back1 f sd) y := fun h => h11 (hy.symm.trans h.symm)
      have jB : Joins H (sideEdge f (latB sd)) x (back1 f sd) := by
        rw [← lat2_eq]; exact joins_of_ends (ends_swap (ends_lat2 f sd)) hx hbb
      have jA : Joins H (sideEdge f (latA sd)) (back1 f sd) y := by
        rw [← lat1_eq]; exact joins_of_ends (ends_lat1 f sd) (Conn.refl _ _) hy
      refine ⟨back1 f sd, nb f (latB sd), nb f (latA sd), cB, lt_of_lt_of_le hpos mB,
        ⟨(latB sd).opp, by rw [eB, lat2_eq]; exact jB, bB⟩, cA,
        lt_of_lt_of_le hpos mA, ⟨(latA sd).opp, by rw [eA, lat1_eq]; exact jA, bA⟩,
        extF nxz, extF nzy⟩
  · -- The back: its corners are joined.
    exfalso
    have hb : Ends (sideEdge f sd.opp) (back1 f sd) (back2 f sd) := ends_back f sd
    rcases conn_of_joins hb hj0 with ⟨hx, hy⟩ | ⟨hx, hy⟩
    · exact hn (hx.trans (hbb.trans hy.symm))
    · exact hn (hx.trans (hbb.symm.trans hy.symm))
  · exfalso
    have hstep := sgnD_step hH hH' (c := f) (s := sd) (o := outArc H f sd) rfl
    rw [hsol _ hout] at hstep
    simp only [sgnD] at hstep
    have := hext _ hj0; rw [aA] at this
    have ho : o = outArc H f sd := by cases o <;> cases h' : outArc H f sd <;> simp_all
    rw [ho] at hpos
    unfold sgnD at hpos; split_ifs at hstep hpos <;> omega
  · exfalso
    have hstep := sgnD_step hH hH' (c := f) (s := sd) (o := outArc H f sd) rfl
    rw [hsol _ hout] at hstep
    simp only [sgnD] at hstep
    have := hext _ hj0; rw [aB] at this
    have ho : o = outArc H f sd := by cases o <;> cases h' : outArc H f sd <;> simp_all
    rw [ho] at hpos
    unfold sgnD at hpos; split_ifs at hstep hpos <;> omega

end tri

end HP

end SolidGridHam
