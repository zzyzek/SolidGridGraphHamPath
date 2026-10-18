/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
module

public import SolidGridHam.Path.TwoPhWalk

@[expose] public section

/-!
# A height with a slit, and climbs without cycles (interior endpoint, B-2)

An inner point `t = (a, b)` of degree 1 is a *vortex*: the arcs around it do not add up to `0`, so
no height function exists on the cells. Route its imbalance `δ = ±2` along the horizontal
*slit* `y = b`, `x < a`, to the far left: the potential `τ` then jumps across a cell side by the
arc (`±1`) plus `δ` on slit sides (`slit_height`).

`Φ = 2·sgnD o τ + μ·lab`, with `lab` the quadrant of a cell around `t` (0 south-west,
1 south-east, 2 north-east, 3 north-west; the slit separates 3 from 0) and `μ = ∓1`, rises
strictly along each climb step, so there is no closed climb (`acyc_vortex`).
-/

namespace SolidGridHam

namespace HP

open Finset Classical

section slit

variable {V : Finset Pt} {H : Finset Edge}

-- The imbalance of `wS` at a point of degree 1.
--
lemma wS_defect1 {p : Pt} (hdeg : deg H p = 1) : defect (wS H) p = 2 ∨ defect (wS H) p = -2 := by
  obtain ⟨x, y⟩ := p
  have p1 := par_sub_sub (x, y)
  have p2 := par_sub_snd (x, y)
  have p3 := par_sub_fst (x, y)
  simp only at p1 p2 p3
  unfold deg ind at hdeg
  unfold defect wS
  simp only [up, inE1, eD, eR, eL, eU, Edge.lo, p1, p2, p3] at hdeg ⊢
  cases par (x, y) <;>
  by_cases a1 : (⟨.v, (x, y - 1)⟩ : Edge) ∈ H <;>
  by_cases a2 : (⟨.h, (x, y)⟩ : Edge) ∈ H <;>
  by_cases a3 : (⟨.h, (x - 1, y)⟩ : Edge) ∈ H <;>
  by_cases a4 : (⟨.v, (x, y)⟩ : Edge) ∈ H <;>
  simp [a1, a2, a3, a4] at hdeg ⊢

-- The slit edges: horizontal, on row `b`, left of `a`.
--
def SlitE (a b : ℤ) (e : Edge) : Prop := e.d = .h ∧ e.p.2 = b ∧ e.p.1 < a

-- Unit flow from `(a, b)` straight left to `(L, b)`.
--
noncomputable def slitF (a b L : ℤ) (e : Edge) : ℤ :=
  if e.d = .h ∧ e.p.2 = b ∧ L ≤ e.p.1 ∧ e.p.1 < a then -1 else 0

lemma slitF_supp (a b L : ℤ) :
    Supp ((Finset.Ico L a).image (fun x => (⟨.h, (x, b)⟩ : Edge))) (slitF a b L) := by
  intro e he
  unfold slitF
  rw [ite_eq_right]
  rintro ⟨hd, hy, h1, h2⟩
  apply he
  rw [Finset.mem_image]
  refine ⟨e.p.1, Finset.mem_Ico.2 ⟨h1, h2⟩, ?_⟩
  obtain ⟨d, ⟨x, y⟩⟩ := e
  simp only at hd hy ⊢
  rw [hd, hy]

lemma slitF_defect {a b L : ℤ} (hL : L < a) (p : Pt) :
    defect (slitF a b L) p = (if p = (a, b) then 1 else 0) - (if p = (L, b) then 1 else 0) := by
  obtain ⟨x, y⟩ := p
  unfold defect slitF
  simp only [eD, eR, eL, eU, Prod.mk.injEq, reduceCtorEq, false_and, ite_false, true_and]
  by_cases hy : y = b
  · subst hy
    simp only [and_true, true_and]
    split_ifs <;> omega
  · simp only [hy, false_and, ite_false, and_false]
    simp

-- **The height with a slit.** On a solid graph whose inner points have degree 2 except the vortex
-- `(a, b)` (degree 1), a potential whose jump across an interior edge is the arc plus `δ` on
-- slit edges, with `δ = ±2`.
--
theorem slit_height (hs : Solid V) {a b : ℤ} (ht : Inner V (a, b)) (hdt : deg H (a, b) = 1)
    (hdeg : ∀ p, p ≠ (a, b) → Inner V p → deg H p = 2) :
    ∃ (τ : Pt → ℤ) (δ : ℤ), (δ = 2 ∨ δ = -2) ∧ ∀ e, Interior V e →
      τ e.hi - τ e.lo = (if up H e then 1 else -1) + (if SlitE a b e then δ else 0) := by
  set w := wC V H
  set S := V.biUnion cellE
  have hS : Supp S w := wC_supp
  set T : Finset Pt := S.biUnion (fun e => {e.p, e.q})
  have hT : ∀ e ∈ S, e.p ∈ T ∧ e.q ∈ T := fun e he =>
    ⟨Finset.mem_biUnion.2 ⟨e, he, by simp⟩, Finset.mem_biUnion.2 ⟨e, he, by simp⟩⟩
  obtain ⟨L, hL⟩ := exists_left_pt V
  set O : Pt := (L, 0)
  have hLa : L < a := hL _ ht.2.2.2.1
  -- The vortex's imbalance.
  --
  set δ := defect w (a, b) with hδdef
  have hδ : δ = 2 ∨ δ = -2 := by
    obtain ⟨i1, i2, i3, i4⟩ := inner_interior ht
    have := wS_defect1 (H := H) hdt
    rw [hδdef]; unfold defect at this ⊢
    simp only [w, wC]
    rw [ite_eq_left i1, ite_eq_left i2, ite_eq_left i3, ite_eq_left i4]
    exact this
  -- A flow from each point that is not inner to `O` (the zero flow at inner points).
  --
  have hflow : ∀ q : Pt, ∃ (Sq : Finset Edge) (f : Edge → ℤ), Supp Sq f ∧
      (∀ e, Interior V e → f e = 0) ∧
      (∀ p, defect f p = if Inner V q then 0 else
        (if p = q then 1 else 0) - (if p = O then 1 else 0)) := by
    intro q
    by_cases hq : Inner V q
    · exact ⟨∅, fun _ => 0, fun _ _ => rfl, fun _ _ => rfl, fun p => by simp [defect, hq]⟩
    · obtain ⟨Sq, f, h1, h2, h3⟩ := flow_of_reach (reach_far hs hL hq)
      exact ⟨Sq, f, h1, h2, fun p => by rw [ite_eq_right hq]; exact h3 p⟩
  choose SF F hSF hFI hFD using hflow
  -- The vortex's flow: straight left to `(L, b)`, then to `O` outside `V`.
  --
  obtain ⟨S2, f2, hS2, hI2, hD2⟩ := flow_of_reach (V := V) (O := O) (a := (L, b))
    (reach_left (fun q hq => hL q hq) (fun q hq => hL q hq))
  set Ft : Edge → ℤ := fun e => slitF a b L e + f2 e
  set SFt : Finset Edge := (Finset.Ico L a).image (fun x => (⟨.h, (x, b)⟩ : Edge)) ∪ S2
  have hSFt : Supp SFt Ft := by
    intro e he
    simp only [Ft]
    rw [slitF_supp a b L e (fun h => he (Finset.mem_union_left _ h)),
      hS2 e (fun h => he (Finset.mem_union_right _ h))]
    simp
  have hFtD : ∀ p, defect Ft p = (if p = (a, b) then 1 else 0) - (if p = O then 1 else 0) := by
    intro p
    have h1 := slitF_defect (b := b) hLa p
    have h2 := hD2 p
    unfold defect at h1 h2 ⊢
    simp only [Ft]
    linarith
  have hFtI : ∀ e, Interior V e → Ft e = if SlitE a b e then -1 else 0 := by
    intro e he
    simp only [Ft, hI2 e he, add_zero]
    unfold slitF SlitE
    by_cases h : e.d = .h ∧ e.p.2 = b ∧ e.p.1 < a
    · have hLe : L ≤ e.p.1 := le_of_lt (hL _ (by have := he.1.1; simpa [Edge.hi] using this))
      rw [ite_eq_left ⟨h.1, h.2.1, hLe, h.2.2⟩, ite_eq_left h]
    · rw [ite_eq_right (fun h' => h ⟨h'.1, h'.2.1, h'.2.2.2⟩), ite_eq_right h]
  -- Defects vanish at inner points other than the vortex, and off `T`.
  --
  have hδin : ∀ q, Inner V q → q ≠ (a, b) → defect w q = 0 := fun q hq hne =>
    wC_defect_inner hq (hdeg q hne hq)
  have hδT : ∀ p, p ∉ T → defect w p = 0 := by
    intro p hp
    have z : ∀ e, (e = eD p ∨ e = eR p ∨ e = eL p ∨ e = eU p) → w e = 0 := by
      intro e he
      apply hS
      intro heS
      apply hp
      have := hT e heS
      rcases he with rfl | rfl | rfl | rfl
      · simpa [eD, Edge.q] using this.2
      · simpa [eR] using this.1
      · simpa [eL, Edge.q] using this.2
      · simpa [eU] using this.1
    unfold defect
    rw [z _ (Or.inl rfl), z _ (Or.inr (Or.inl rfl)), z _ (Or.inr (Or.inr (Or.inl rfl))),
      z _ (Or.inr (Or.inr (Or.inr rfl)))]
    simp
  have hsum : ∑ q ∈ T, defect w q = 0 := sum_defect hS T hT
  have htT : (a, b) ∈ T := by
    by_contra h
    have := hδT _ h
    rw [← hδdef] at this
    rcases hδ with h' | h' <;> omega
  -- The correction and the corrected weight.
  --
  set β : Edge → ℤ := fun g => ∑ q ∈ T, defect w q * F q g
  set g : Edge → ℤ := fun e => w e - β e - δ * Ft e
  set Sg : Finset Edge := S ∪ T.biUnion SF ∪ SFt
  have hSg : Supp Sg g := by
    intro e he
    have h1 : e ∉ S := fun h => he (Finset.mem_union_left _ (Finset.mem_union_left _ h))
    have h2 : ∀ q ∈ T, e ∉ SF q := fun q hq h =>
      he (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨q, hq, h⟩)))
    have h3 : e ∉ SFt := fun h => he (Finset.mem_union_right _ h)
    simp only [g, β]
    rw [hS e h1, hSFt e h3, mul_zero, sub_zero, zero_sub, neg_eq_zero]
    apply Finset.sum_eq_zero
    intro q hq
    rw [hSF q e (h2 q hq), mul_zero]
  have hβI : ∀ e, Interior V e → β e = 0 := by
    intro e he
    simp only [β]
    apply Finset.sum_eq_zero
    intro q _
    rw [hFI q e he, mul_zero]
  have hdefβ : ∀ p, defect β p = ∑ q ∈ T, defect w q * defect (F q) p := by
    intro p
    simp only [defect, β, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro q _
    ring
  have hbal : Balanced g := by
    intro p
    have key : defect g p = 0 := by
      have hg : defect g p = defect w p - defect β p - δ * defect Ft p := by
        simp only [defect, g]; ring
      rw [hg, hdefβ, hFtD]
      set X : Pt → ℤ := fun q => (if p = q then 1 else 0) - (if p = O then 1 else 0) with hX
      have term : ∀ q ∈ T, defect w q * defect (F q) p =
          defect w q * X q - (if q = (a, b) then δ * X (a, b) else 0) := by
        intro q _
        rw [hFD q p]
        by_cases hq : Inner V q
        · rw [ite_eq_left hq]
          by_cases hqt : q = (a, b)
          · subst hqt; rw [ite_eq_left rfl, ← hδdef]; ring
          · rw [hδin q hq hqt, ite_eq_right hqt]; ring
        · have hqt : q ≠ (a, b) := fun h => hq (h ▸ ht)
          rw [ite_eq_right hq, ite_eq_right hqt]; simp only [hX]; ring
      rw [Finset.sum_congr rfl term, Finset.sum_sub_distrib, Finset.sum_ite_eq' T (a, b),
        ite_eq_left htT]
      have e1 : ∑ q ∈ T, defect w q * X q =
          (∑ q ∈ T, if p = q then defect w q else 0) - (∑ q ∈ T, defect w q) * (if p = O then 1 else 0) := by
        rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro q _
        simp only [hX]
        split_ifs <;> ring
      rw [e1, hsum, zero_mul, sub_zero, Finset.sum_ite_eq]
      by_cases hpT : p ∈ T
      · rw [ite_eq_left hpT]; simp only [hX]; ring
      · rw [ite_eq_right hpT, hδT p hpT]; simp only [hX]; ring
    unfold defect at key
    linarith
  refine ⟨pot Sg g, δ, hδ, fun e he => ?_⟩
  rw [pot_jump hSg hbal e]
  simp only [g, w, wC, ite_eq_left he, hβI e he, sub_zero, hFtI e he]
  unfold wS
  split_ifs <;> ring

-- The quadrant of a cell around `(a, b)`: 0 south-west, 1 south-east, 2 north-east, 3 north-west.
--
def lab (a b : ℤ) (c : Pt) : ℤ :=
  if c.2 ≤ b - 1 then (if c.1 ≤ a - 1 then 0 else 1) else (if a ≤ c.1 then 2 else 3)

lemma lab_step (a b x y : ℤ) (s : Side) :
    (s = .t ∧ x < a ∧ y + 1 = b ∧ lab a b (nb (x, y) s) = lab a b (x, y) + 3) ∨
    (s = .b ∧ x < a ∧ y = b ∧ lab a b (nb (x, y) s) = lab a b (x, y) - 3) ∨
    (¬ (s = .t ∧ x < a ∧ y + 1 = b) ∧ ¬ (s = .b ∧ x < a ∧ y = b) ∧
      lab a b (x, y) - 1 ≤ lab a b (nb (x, y) s) ∧ lab a b (nb (x, y) s) ≤ lab a b (x, y) + 1) := by
  cases s <;> simp only [nb, lab, reduceCtorEq, false_and, true_and, not_false_eq_true,
    not_and] <;> split_ifs <;> omega

-- A step across a side whose arc points `o`, between cells (a climb step without the cut).
--
def ArcStep (V : Finset Pt) (H : Finset Edge) (o : Bool) (c c' : Pt) : Prop :=
  IsCell V c ∧ IsCell V c' ∧ ∃ s, outArc H c s = o ∧ c' = nb c s

-- No closed walk of arc steps.
--
def ArcAcyc (V : Finset Pt) (H : Finset Edge) : Prop :=
  ∀ o c, ¬ Relation.TransGen (ArcStep V H o) c c

lemma climbAcyc_of_arc (h : ArcAcyc V H) : ClimbAcyc V H := by
  intro o x y c hc
  apply h o c
  have conv : ∀ a b, ClimbStep V H o x y a b → ArcStep V H o a b :=
    fun a b ⟨h1, h2, s, _, h3, h4⟩ => ⟨h1, h2, s, h3, h4⟩
  have key : ∀ a b, Relation.TransGen (ClimbStep V H o x y) a b →
      Relation.TransGen (ArcStep V H o) a b := by
    intro a b hab
    induction hab with
    | single h => exact .single (conv _ _ h)
    | tail _ h ih => exact ih.tail (conv _ _ h)
  exact key c c hc

-- **No closed climb around a vortex.**
--
theorem arc_vortex (hs : Solid V) {a b : ℤ} (ht : Inner V (a, b)) (hdt : deg H (a, b) = 1)
    (hdeg : ∀ p, p ≠ (a, b) → Inner V p → deg H p = 2) : ArcAcyc V H := by
  obtain ⟨τ, δ, hδ, hjump⟩ := slit_height hs ht hdt hdeg
  -- One step between cells.
  --
  have step : ∀ (x y : ℤ) (s : Side), IsCell V (x, y) → IsCell V (nb (x, y) s) →
      τ (nb (x, y) s) = τ (x, y) + (if outArc H (x, y) s then 1 else -1) +
        (match s with
          | .t => if x < a ∧ y + 1 = b then δ else 0
          | .b => if x < a ∧ y = b then -δ else 0
          | _ => 0) := by
    intro x y s hc hc'
    cases s
    · have he : Interior V (bot (x, y)) := ⟨hc, by simpa [bot, Edge.lo, nb] using hc'⟩
      have := hjump _ he
      have h1 : (bot (x, y)).hi = (x, y) := rfl
      have h2 : (bot (x, y)).lo = (x, y - 1) := rfl
      rw [h1, h2] at this
      show τ (x, y - 1) = τ (x, y) + (if (!up H (bot (x, y))) = true then 1 else -1) +
        (if x < a ∧ y = b then -δ else 0)
      have hsl : SlitE a b (bot (x, y)) ↔ x < a ∧ y = b := by
        simp only [SlitE, bot, true_and]; exact And.comm
      by_cases hc2 : x < a ∧ y = b
      · rw [ite_eq_left (hsl.2 hc2)] at this; rw [ite_eq_left hc2]
        cases hu : up H (bot (x, y)) <;> simp [hu] at this ⊢ <;> linarith
      · rw [ite_eq_right (fun h => hc2 (hsl.1 h))] at this; rw [ite_eq_right hc2]
        cases hu : up H (bot (x, y)) <;> simp [hu] at this ⊢ <;> linarith
    · have he : Interior V (top (x, y)) :=
        ⟨by simpa [top, nb] using hc', by simpa [top, Edge.lo] using hc⟩
      have := hjump _ he
      have h1 : (top (x, y)).hi = (x, y + 1) := rfl
      have h2 : (top (x, y)).lo = (x, y) := by simp [top, Edge.lo]
      rw [h1, h2] at this
      show τ (x, y + 1) = τ (x, y) + (if up H (top (x, y)) = true then 1 else -1) +
        (if x < a ∧ y + 1 = b then δ else 0)
      have hsl : SlitE a b (top (x, y)) ↔ x < a ∧ y + 1 = b := by
        simp only [SlitE, top, true_and]; exact And.comm
      by_cases hc2 : x < a ∧ y + 1 = b
      · rw [ite_eq_left (hsl.2 hc2)] at this; rw [ite_eq_left hc2]
        cases hu : up H (top (x, y)) <;> simp [hu] at this ⊢ <;> linarith
      · rw [ite_eq_right (fun h => hc2 (hsl.1 h))] at this; rw [ite_eq_right hc2]
        cases hu : up H (top (x, y)) <;> simp [hu] at this ⊢ <;> linarith
    · have he : Interior V (lft (x, y)) := ⟨hc, by simpa [lft, Edge.lo, nb] using hc'⟩
      have := hjump _ he
      have h1 : (lft (x, y)).hi = (x, y) := rfl
      have h2 : (lft (x, y)).lo = (x - 1, y) := rfl
      rw [h1, h2] at this
      have hsl : ¬ SlitE a b (lft (x, y)) := by simp [SlitE, lft]
      rw [ite_eq_right hsl] at this
      show τ (x - 1, y) = τ (x, y) + (if (!up H (lft (x, y))) = true then 1 else -1) + 0
      cases hu : up H (lft (x, y)) <;> simp [hu] at this ⊢ <;> linarith
    · have he : Interior V (rgt (x, y)) :=
        ⟨by simpa [rgt, nb] using hc', by simpa [rgt, Edge.lo] using hc⟩
      have := hjump _ he
      have h1 : (rgt (x, y)).hi = (x + 1, y) := rfl
      have h2 : (rgt (x, y)).lo = (x, y) := by simp [rgt, Edge.lo]
      rw [h1, h2] at this
      have hsl : ¬ SlitE a b (rgt (x, y)) := by simp [SlitE, rgt]
      rw [ite_eq_right hsl] at this
      show τ (x + 1, y) = τ (x, y) + (if up H (rgt (x, y)) = true then 1 else -1) + 0
      cases hu : up H (rgt (x, y)) <;> simp [hu] at this ⊢ <;> linarith
  intro o c hc
  -- the strict potential
  set g : ℤ := if o then 1 else -1 with hg
  have hsd : ∀ z, sgnD o z = g * z := by intro z; cases o <;> simp [sgnD, hg]
  have hgo : (if o = true then (1 : ℤ) else -1) = g := by cases o <;> simp [hg]
  have hg2 : g = 1 ∨ g = -1 := by cases o <;> simp [hg]
  set μ : ℤ := if g * δ = 2 then -1 else 1 with hμ
  set Φ : Pt → ℤ := fun c => 2 * sgnD o (τ c) + μ * lab a b c with hΦ
  have mono : ∀ c c', ArcStep V H o c c' → Φ c < Φ c' := by
    intro c c' h
    obtain ⟨hc1, hc2, s, has, rfl⟩ := h
    obtain ⟨u, v⟩ := c
    have hst := step u v s hc1 hc2
    rw [has, hgo] at hst
    simp only [hΦ, hsd]
    rw [hst]
    have hσ : g * δ = 2 ∨ g * δ = -2 := by
      rcases hg2 with h | h <;> rcases hδ with h' | h' <;> rw [h, h'] <;> norm_num
    have hgg : g * g = 1 := by rcases hg2 with h | h <;> rw [h] <;> norm_num
    rcases lab_step a b u v s with ⟨rfl, h1, h2, h3⟩ | ⟨rfl, h1, h2, h3⟩ | ⟨n1, n2, h3, h4⟩
    · simp only [ite_eq_left (And.intro h1 h2)]
      rw [h3]
      have e : g * (τ (u, v) + g + δ) = g * τ (u, v) + g * g + g * δ := by ring
      rw [e, hgg]
      rcases hσ with h | h
      · have hm : μ = -1 := by rw [hμ, ite_eq_left h]
        rw [hm, h]; linarith
      · have hm : μ = 1 := by rw [hμ, ite_eq_right (by rw [h]; norm_num)]
        rw [hm, h]; linarith
    · simp only [ite_eq_left (And.intro h1 h2)]
      rw [h3]
      have e : g * (τ (u, v) + g + -δ) = g * τ (u, v) + g * g - g * δ := by ring
      rw [e, hgg]
      rcases hσ with h | h
      · have hm : μ = -1 := by rw [hμ, ite_eq_left h]
        rw [hm, h]; linarith
      · have hm : μ = 1 := by rw [hμ, ite_eq_right (by rw [h]; norm_num)]
        rw [hm, h]; linarith
    · have hcorr : (match s with
          | .t => if u < a ∧ v + 1 = b then δ else 0
          | .b => if u < a ∧ v = b then -δ else 0
          | _ => 0) = 0 := by
        cases s
        · show (if u < a ∧ v = b then -δ else 0) = 0
          rw [ite_eq_right (fun h => n2 ⟨rfl, h.1, h.2⟩)]
        · show (if u < a ∧ v + 1 = b then δ else 0) = 0
          rw [ite_eq_right (fun h => n1 ⟨rfl, h.1, h.2⟩)]
        · rfl
        · rfl
      rw [hcorr]
      have e : g * (τ (u, v) + g + 0) = g * τ (u, v) + g * g := by ring
      rw [e, hgg]
      have hμ1 : μ = 1 ∨ μ = -1 := by simp only [hμ]; split_ifs <;> simp
      rcases hμ1 with h | h <;> rw [h] <;> linarith
  have key : ∀ c c', Relation.TransGen (ArcStep V H o) c c' → Φ c < Φ c' := by
    intro c c' h
    induction h with
    | single h => exact mono _ _ h
    | tail _ h ih => exact ih.trans (mono _ _ h)
  exact lt_irrefl _ (key c c hc)

theorem acyc_vortex (hs : Solid V) {a b : ℤ} (ht : Inner V (a, b)) (hdt : deg H (a, b) = 1)
    (hdeg : ∀ p, p ≠ (a, b) → Inner V p → deg H p = 2) : ClimbAcyc V H :=
  climbAcyc_of_arc (arc_vortex hs ht hdt hdeg)

-- Arc acyclicity passes to a smaller set of cells and to a factor that agrees on the sides
-- between those cells.
--
lemma arcAcyc_transfer {U : Finset Pt} {G : Finset Edge} (h : ArcAcyc V H) (hUV : U ⊆ V)
    (hag : ∀ c s, IsCell U c → IsCell U (nb c s) → outArc G c s = outArc H c s) :
    ArcAcyc U G := by
  intro o c hc
  apply h o c
  have conv : ∀ a b, ArcStep U G o a b → ArcStep V H o a b := by
    rintro a b ⟨h1, h2, s, h3, rfl⟩
    exact ⟨isCell_mono h1 hUV, isCell_mono h2 hUV, s, by rw [← hag a s h1 h2]; exact h3, rfl⟩
  have key : ∀ a b, Relation.TransGen (ArcStep U G o) a b →
      Relation.TransGen (ArcStep V H o) a b := by
    intro a b hab
    induction hab with
    | single h => exact .single (conv _ _ h)
    | tail _ h ih => exact ih.tail (conv _ _ h)
  exact key c c hc

end slit

end HP

end SolidGridHam
