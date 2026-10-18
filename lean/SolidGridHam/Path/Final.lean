/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
module

public import SolidGridHam.Path.Rank
public import SolidGridHam.Path.Taut
public import SolidGridHam.Cycle.Chain
public import SolidGridHam.Cycle.Phase

@[expose] public section

/-!
# The final count (repaired §4.8, steps (2)–(3))

After the generalized moves, `H` has `r` fixed pairs and its cut squares that are extremal along
their cut, with `D = D H H'` of the extremal sign, are fixed squares (or the E1 square at `t`, whose
cut is paid by its two neighbouring cuts). Then `H'` has at least `pieces(H) − r` pieces.

**Climb.** An edge of `H'` joining two pieces `X ≠ Y` of `H` has a face with `D ≠ 0` beside it.
From there, walk across sides joining `X` to `Y` in the direction of `H`'s arcs (`D > 0`) or
against them (`D < 0`). `D` never moves back toward `0` (`D_mono_arc`), so the walk never reaches a
non-cell (`D = 0` there); a height function `τ` for `H` on the cells strictly increases, so the walk
stops at a cell that is extremal along the `X|Y` cut.

The height function is a hypothesis here (`HeightOn`); it exists on solid graphs.
-/

namespace SolidGridHam

namespace HP

open Finset Classical

-- `e` joins the pieces of `x` and `y` (either way round).
--
def Joins (H : Finset Edge) (e : Edge) (x y : Pt) : Prop :=
  (Conn H x e.p ∧ Conn H y e.q) ∨ (Conn H x e.q ∧ Conn H y e.p)

-- The pair of pieces `(x, y)` is the pair `(u, v)`.
--
def PEq (H : Finset Edge) (x y u v : Pt) : Prop :=
  (Conn H x u ∧ Conn H y v) ∨ (Conn H x v ∧ Conn H y u)

-- A height function for `H` on the cells of `V`: one step up across each arc of `H`.
--
def HeightOn (V : Finset Pt) (H : Finset Edge) (τ : Pt → ℤ) : Prop :=
  ∀ c s, IsCell V c → IsCell V (nb c s) → τ (nb c s) = τ c + (if outArc H c s then 1 else -1)

-- `c` is extremal along the `x|y` cut in direction `o`: no `x|y` side has its arc pointing `o`.
--
def CutExt (H : Finset Edge) (o : Bool) (c x y : Pt) : Prop :=
  ∀ s, Joins H (sideEdge c s) x y → outArc H c s ≠ o

-- `D` read with the sign of the direction.
--
def sgnD (o : Bool) (z : ℤ) : ℤ := if o then z else -z

section climb

variable {V W : Finset Pt} {d : Pt → ℕ} {H H' : Finset Edge}
  (hH : IsFactor W d H) (hH' : IsFactor W d H')
include hH hH'

-- One step in direction `o` does not move `D` back toward `0`.
--
lemma sgnD_step {c : Pt} {s : Side} {o : Bool} (ha : outArc H c s = o) :
    sgnD o (D H H' c) ≤ sgnD o (D H H' (nb c s)) := by
  have h := D_step hH hH' c s
  rw [ha] at h
  cases o <;> simp only [sgnD, Bool.false_eq_true, ↓reduceIte] at h ⊢ <;> split_ifs at h <;> omega

-- One climb step: across an `x|y` side whose arc points `o`, onto a cell.
--
def ClimbStep (V : Finset Pt) (H : Finset Edge) (o : Bool) (x y : Pt) (c c' : Pt) : Prop :=
  IsCell V c ∧ IsCell V c' ∧ ∃ s, Joins H (sideEdge c s) x y ∧ outArc H c s = o ∧ c' = nb c s

-- No closed chain of climb steps (on solid graphs: the height rises along each step).
--
def ClimbAcyc (V : Finset Pt) (H : Finset Edge) : Prop :=
  ∀ o x y c, ¬ Relation.TransGen (ClimbStep V H o x y) c c

omit hH hH' in
lemma acyc_of_height {τ : Pt → ℤ} (hτ : HeightOn V H τ) : ClimbAcyc V H := by
  intro o x y c hc
  have key : ∀ a b, Relation.TransGen (ClimbStep V H o x y) a b →
      sgnD o (τ a) < sgnD o (τ b) := by
    intro a b hab
    induction hab with
    | single h =>
      obtain ⟨ha, hb, s, _, has, rfl⟩ := h
      have := hτ _ s ha hb
      rw [has] at this
      rw [this]; cases o <;> simp [sgnD]
    | @tail m _ _ h ih =>
      obtain ⟨hm, hn, s, _, has, rfl⟩ := h
      have := hτ m s hm hn
      rw [has] at this
      have h2 : sgnD o (τ m) < sgnD o (τ (nb m s)) := by
        rw [this]; cases o <;> simp [sgnD]
      exact ih.trans h2
  exact lt_irrefl _ (key c c hc)

-- **The climb.** From a cell with `D` of sign `o` and an `x|y` side, walking in direction `o`
-- across `x|y` sides reaches a cell extremal along the `x|y` cut, with `D` at least as far from `0`.
--
theorem climb (hsol : SolidFor V H H') (hac : ClimbAcyc V H) (o : Bool) (x y : Pt) :
    ∀ c, IsCell V c → 0 < sgnD o (D H H' c) → (∃ s, Joins H (sideEdge c s) x y) →
      ∃ c', IsCell V c' ∧ sgnD o (D H H' c) ≤ sgnD o (D H H' c') ∧
        (∃ s, Joins H (sideEdge c' s) x y) ∧ CutExt H o c' x y ∧
        (c' = c ∨ ∃ s, Joins H (sideEdge c' s) x y ∧ IsCell V (nb c' s)) := by
  intro c
  -- Induction on the number of cells reachable from `c` by climb steps.
  --
  induction hn : (V.filter (fun q => Relation.ReflTransGen (ClimbStep V H o x y) c q)).card using
    Nat.strong_induction_on generalizing c with
  | _ n ih =>
  intro hc hpos hj
  by_cases hext : CutExt H o c x y
  · exact ⟨c, hc, le_rfl, hj, hext, Or.inl rfl⟩
  unfold CutExt at hext
  push Not at hext
  obtain ⟨s, hjs, has⟩ := hext
  have hmono := sgnD_step hH hH' (H' := H') has
  have hpos' : 0 < sgnD o (D H H' (nb c s)) := lt_of_lt_of_le hpos hmono
  have hc' : IsCell V (nb c s) := by
    by_contra hn'
    have := hsol _ hn'
    rw [this] at hpos'
    simp [sgnD] at hpos'
  have hstep : ClimbStep V H o x y c (nb c s) := ⟨hc, hc', s, hjs, has, rfl⟩
  have hlt : (V.filter (fun q => Relation.ReflTransGen (ClimbStep V H o x y) (nb c s) q)).card < n := by
    rw [← hn]
    apply Finset.card_lt_card
    rw [Finset.ssubset_iff_of_subset]
    · refine ⟨c, Finset.mem_filter.2 ⟨hc.1, Relation.ReflTransGen.refl⟩, ?_⟩
      intro hm
      have hr := (Finset.mem_filter.1 hm).2
      exact hac o x y c (Relation.TransGen.head' hstep hr)
    · intro q hq
      simp only [Finset.mem_filter] at hq ⊢
      exact ⟨hq.1, Relation.ReflTransGen.head hstep hq.2⟩
  -- The side just crossed is an `x|y` side of the new cell.
  --
  have hj' : ∃ s', Joins H (sideEdge (nb c s) s') x y :=
    ⟨s.opp, by rw [sideEdge_nb_opp]; exact hjs⟩
  obtain ⟨c', h1, h2, h3, h4, h5⟩ := ih _ hlt (nb c s) rfl hc' hpos' hj'
  refine ⟨c', h1, hmono.trans h2, h3, h4, Or.inr ?_⟩
  rcases h5 with rfl | h5
  · exact ⟨s.opp, by rw [sideEdge_nb_opp]; exact hjs, by rw [nb_nb_opp]; exact hc⟩
  · exact h5

end climb

/-! ## Fixed pairs and the count -/

-- A fixed pair: a bottom square `bot`, its top square `nb bot s` (higher: `H`'s arc goes up), the
-- pieces `(tx, ty)` of the top square's cut and `(bx, by)` of the bottom square's cut.
--
structure FixedPr where
  bot : Pt
  s : Side
  tx : Pt
  ty : Pt
  bx : Pt
  by' : Pt

def FixedPr.top (i : FixedPr) : Pt := nb i.bot i.s

-- The join a fixed pair pays for: its top cut if `D > 0` at the top, its bottom cut if `D < 0` at
-- the bottom.
--
noncomputable def FixedPr.pay (H H' : Finset Edge) (i : FixedPr) : Option (Pt × Pt) :=
  if 0 < D H H' i.top then some (i.tx, i.ty)
  else if D H H' i.bot < 0 then some (i.bx, i.by') else none

-- The extremal square of a climb in direction `o` is the fixed square of that direction.
--
def FixedPr.ext (i : FixedPr) (o : Bool) : Pt := if o then i.top else i.bot
def FixedPr.px (i : FixedPr) (o : Bool) : Pt := if o then i.tx else i.bx
def FixedPr.py (i : FixedPr) (o : Bool) : Pt := if o then i.ty else i.by'

section joins

variable {R : Pt → Pt → Prop}

lemma mergeL_of_rel (hR : IsEqv R) :
    ∀ (P : List (Pt × Pt)) {x y : Pt}, R x y → HP.mergeL R P x y
  | [], _, _, h => h
  | _ :: P, _, _, h => Or.inl (mergeL_of_rel hR P h)

lemma mergeL_of_mem (hR : IsEqv R) :
    ∀ (P : List (Pt × Pt)) {a b : Pt}, (a, b) ∈ P → HP.mergeL R P a b
  | [], _, _, h => absurd h (List.not_mem_nil)
  | q :: P, a, b, h => by
    rcases List.mem_cons.1 h with h | h
    · subst h
      exact Or.inr (Or.inl ⟨(hR.mergeL P).refl _, (hR.mergeL P).refl _⟩)
    · exact Or.inl (mergeL_of_mem hR P h)

-- An edge on which `H` and `H'` differ has a face with `D ≠ 0`, and that face has the edge as a
-- side.
--
lemma face_of_edge (e : Edge) : (∃ s, sideEdge e.hi s = e) ∧ (∃ s, sideEdge e.lo s = e) := by
  refine ⟨?_, ?_⟩
  · rcases (hi_eq_iff e e.hi).1 rfl with h | h
    · exact ⟨.b, h.symm⟩
    · exact ⟨.l, h.symm⟩
  · rcases (lo_eq_iff e e.lo).1 rfl with h | h
    · exact ⟨.t, h.symm⟩
    · exact ⟨.r, h.symm⟩

end joins

section count

variable {V W : Finset Pt} {d : Pt → ℕ} {H H' : Finset Edge}

-- Every cell extremal along the `x|y` cut in direction `o`, with `D` of sign `o`, is the fixed
-- square of that direction on the same cut.
--
def ExtFixed (V : Finset Pt) (H H' : Finset Edge) (FP : List FixedPr) (o : Bool) (x y : Pt) : Prop :=
  ∀ c, IsCell V c → 0 < sgnD o (D H H' c) → (∃ s, Joins H (sideEdge c s) x y ∧ IsCell V (nb c s)) →
    CutExt H o c x y → ∃ i ∈ FP, c = i.ext o ∧ PEq H x y (i.px o) (i.py o)

-- What the final state provides at a cut-extremal cell with `D` of the extremal sign: the fixed
-- square of that direction on the same cut, or (the E1 square at `t`) a third piece `z` such that
-- cells with `D` of sign `o` lie on the `x|z` and `z|y` cuts, and those two cuts are paid by
-- fixed squares.
--
def FinalOK (V : Finset Pt) (H H' : Finset Edge) (FP : List FixedPr) : Prop :=
  ∀ o x y c, ¬ Conn H x y → IsCell V c → 0 < sgnD o (D H H' c) →
    (∃ s, Joins H (sideEdge c s) x y) → CutExt H o c x y →
      (∃ i ∈ FP, c = i.ext o ∧ PEq H x y (i.px o) (i.py o)) ∨
      ∃ z c1 c2, IsCell V c1 ∧ 0 < sgnD o (D H H' c1) ∧
        (∃ s, Joins H (sideEdge c1 s) x z ∧ IsCell V (nb c1 s)) ∧
        IsCell V c2 ∧ 0 < sgnD o (D H H' c2) ∧ (∃ s, Joins H (sideEdge c2 s) z y ∧ IsCell V (nb c2 s)) ∧
        ExtFixed V H H' FP o x z ∧ ExtFixed V H H' FP o z y

variable (hH : IsFactor W d H) (hH' : IsFactor W d H')
include hH hH'

-- A fixed pair is paid in one direction only (`pair_one_side`).
--
lemma pay_of_ext (i : FixedPr) (hup : outArc H i.bot i.s = true) (o : Bool)
    (hpos : 0 < sgnD o (D H H' (i.ext o))) : i.pay H H' = some (i.px o, i.py o) := by
  cases o
  · simp only [FixedPr.ext, FixedPr.px, FixedPr.py, sgnD, Bool.false_eq_true, ↓reduceIte]
      at hpos ⊢
    unfold FixedPr.pay
    have : ¬ 0 < D H H' i.top := fun ht =>
      pair_one_side hH hH' hup ht (by omega)
    simp only [this, ↓reduceIte]
    rw [ite_eq_left (by omega)]
  · simp only [FixedPr.ext, FixedPr.px, FixedPr.py, sgnD, ↓reduceIte] at hpos ⊢
    unfold FixedPr.pay
    rw [ite_eq_left hpos]

-- From a cell with `D` of sign `o` and an `x|y` side, the pieces of `x` and `y` are joined by `H`
-- and the payments.
--
lemma joined_of_ext (hsol : SolidFor V H H') (hac : ClimbAcyc V H)
    (FP : List FixedPr) (hup : ∀ i ∈ FP, outArc H i.bot i.s = true) {o : Bool} {x y : Pt}
    (hok : ExtFixed V H H' FP o x y) {c : Pt} (hc : IsCell V c) (hpos : 0 < sgnD o (D H H' c))
    (hj : ∃ s, Joins H (sideEdge c s) x y ∧ IsCell V (nb c s)) :
    HP.mergeL (Conn H) (FP.filterMap (FixedPr.pay H H')) x y := by
  have hE := (isEqv_conn H).mergeL (FP.filterMap (FixedPr.pay H H'))
  obtain ⟨c', hc', hle, _, hext, hent⟩ :=
    climb hH hH' hsol hac o x y c hc hpos (let ⟨s, h, _⟩ := hj; ⟨s, h⟩)
  have hj' : ∃ s, Joins H (sideEdge c' s) x y ∧ IsCell V (nb c' s) := by
    rcases hent with rfl | h
    · exact hj
    · exact h
  obtain ⟨i, hi, rfl, hpq⟩ := hok c' hc' (lt_of_lt_of_le hpos hle) hj' hext
  have hpay := pay_of_ext hH hH' i (hup i hi) o (lt_of_lt_of_le hpos hle)
  have hmem : (i.px o, i.py o) ∈ FP.filterMap (FixedPr.pay H H') :=
    List.mem_filterMap.2 ⟨i, hi, hpay⟩
  have huv := mergeL_of_mem (isEqv_conn H) _ hmem
  have rel : ∀ {a b : Pt}, Conn H a b → HP.mergeL (Conn H) (FP.filterMap (FixedPr.pay H H')) a b :=
    fun h => mergeL_of_rel (isEqv_conn H) _ h
  rcases hpq with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact hE.trans (rel h1) (hE.trans huv (hE.symm (rel h2)))
  · exact hE.trans (rel h1) (hE.trans (hE.symm huv) (hE.symm (rel h2)))

-- **The final count.** In a final state, `H'` has at least `pieces(H) − r` pieces.
--
theorem final_count (hsol : SolidFor V H H') (hac : ClimbAcyc V H)
    (FP : List FixedPr) (hup : ∀ i ∈ FP, outArc H i.bot i.s = true) (hfin : FinalOK V H H' FP) :
    ncomp W H ≤ ncomp W H' + FP.length := by
  set P := FP.filterMap (FixedPr.pay H H')
  have hE := (isEqv_conn H).mergeL P
  have hlen : P.length ≤ FP.length := List.length_filterMap_le _ _
  suffices hin : ∀ e ∈ H', HP.mergeL (Conn H) P e.p e.q by
    have := ncomp_le_of_joins (V := W) P hin
    omega
  intro e he
  by_cases hc : Conn H e.p e.q
  · exact mergeL_of_rel (isEqv_conn H) P hc
  have hs : e ∈ symmDiff H H' := by
    rw [Finset.mem_symmDiff]
    exact Or.inr ⟨he, fun h => hc (Conn.of_edge h)⟩
  have hjoin : ∀ s c, sideEdge c s = e → Joins H (sideEdge c s) e.p e.q := by
    intro s c h; rw [h]; exact Or.inl ⟨Conn.refl _ _, Conn.refl _ _⟩
  -- A face beside `e` with `D ≠ 0`.
  --
  obtain ⟨f, hfs, hfD⟩ : ∃ f, (∃ s, sideEdge f s = e) ∧ D H H' f ≠ 0 := by
    obtain ⟨⟨s1, h1⟩, ⟨s2, h2⟩⟩ := face_of_edge e
    rcases disagree_beside hH hH' hs with h | h
    · exact ⟨e.hi, ⟨s1, h1⟩, h⟩
    · exact ⟨e.lo, ⟨s2, h2⟩, h⟩
  have hfc : IsCell V f := by
    by_contra hn; exact hfD (hsol f hn)
  obtain ⟨o, ho⟩ : ∃ o, 0 < sgnD o (D H H' f) := by
    rcases lt_or_gt_of_ne hfD with h | h
    · exact ⟨false, by simp [sgnD]; omega⟩
    · exact ⟨true, by simp [sgnD]; omega⟩
  have hj : ∃ s, Joins H (sideEdge f s) e.p e.q := by
    obtain ⟨s, h⟩ := hfs; exact ⟨s, hjoin s f h⟩
  -- Climb to a cut-extremal cell; it is paid directly, or (E1) through a third piece.
  --
  obtain ⟨c', hc', hle, hj', hext, -⟩ := climb hH hH' hsol hac o e.p e.q f hfc ho hj
  have rel : ∀ {a b : Pt}, Conn H a b → HP.mergeL (Conn H) P a b :=
    fun h => mergeL_of_rel (isEqv_conn H) _ h
  rcases hfin o e.p e.q c' hc hc' (lt_of_lt_of_le ho hle) hj' hext with
    ⟨i, hi, rfl, hpq⟩ | ⟨z, c1, c2, hc1, hp1, hj1, hc2, hp2, hj2, hok1, hok2⟩
  · have hpay := pay_of_ext hH hH' i (hup i hi) o (lt_of_lt_of_le ho hle)
    have huv := mergeL_of_mem (isEqv_conn H) P (List.mem_filterMap.2 ⟨i, hi, hpay⟩)
    rcases hpq with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact hE.trans (rel h1) (hE.trans huv (hE.symm (rel h2)))
    · exact hE.trans (rel h1) (hE.trans (hE.symm huv) (hE.symm (rel h2)))
  · exact hE.trans (joined_of_ext hH hH' hsol hac FP hup hok1 hc1 hp1 hj1)
      (joined_of_ext hH hH' hsol hac FP hup hok2 hc2 hp2 hj2)

end count

end HP

end SolidGridHam
