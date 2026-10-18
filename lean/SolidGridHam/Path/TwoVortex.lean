/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
import SolidGridHam.Path.SlitHeight

/-!
# Two vortices: climbs without cycles (both endpoints inner)

Two inner points `v₁ ≠ v₂` of degree 1. Route each imbalance `δᵢ = ±2` along a slit: both slits
go left when the vortices lie on different rows; on a common row the left vortex's slit goes left
and the right vortex's goes down (`height2`). The potential `τ` jumps across a cell side by the
arc plus `δᵢ` on the sides of slit `i`.

Each vortex gets a three-sector label, jumping by `±2` across its slit and by `±1` across its two
other boundary rays:
* different rows: the lower vortex uses its row and its downward ray (`labD`), the upper its row
  and its upward ray (`labU`);
* a common row: the left vortex uses its column and its left ray (`labL`), the right its column and
  its right ray with the slit downward (`labR`).
No cell step crosses boundaries of both vortices, so `Φ = 3·sgnD o τ + 2μ₁·lab₁ + 2μ₂·lab₂`, with
`μᵢ = ∓1`, rises by at least 1 along each arc step (`arc_vortex2`).
-/

namespace SolidGridHam

namespace HP

open Finset Classical

section height2

variable {V : Finset Pt} {H : Finset Edge}

lemma wC_defect1 {v : Pt} (hv : Inner V v) (hd : deg H v = 1) :
    defect (wC V H) v = 2 ∨ defect (wC V H) v = -2 := by
  obtain ⟨i1, i2, i3, i4⟩ := inner_interior hv
  have := wS_defect1 (H := H) hd
  unfold defect at this ⊢
  simp only [wC]
  rw [ite_eq_left i1, ite_eq_left i2, ite_eq_left i3, ite_eq_left i4]
  exact this

-- **The height with two slits.** Given unit flows `F₁`, `F₂` from the two vortices to `O = (L, 0)`,
-- a potential whose jump across an interior edge is the arc minus `δᵢ Fᵢ`, with `δᵢ = ±2`.
--
theorem height2 (hs : Solid V) {L : ℤ} (hL : ∀ q ∈ V, L < q.1) {v1 v2 : Pt} (h12 : v1 ≠ v2)
    (hv1 : Inner V v1) (hv2 : Inner V v2) (hd1 : deg H v1 = 1) (hd2 : deg H v2 = 1)
    (hdeg : ∀ p, p ≠ v1 → p ≠ v2 → Inner V p → deg H p = 2)
    {S1 S2 : Finset Edge} {F1 F2 : Edge → ℤ} (hS1 : Supp S1 F1) (hS2 : Supp S2 F2)
    (hD1 : ∀ p, defect F1 p = (if p = v1 then 1 else 0) - (if p = (L, 0) then 1 else 0))
    (hD2 : ∀ p, defect F2 p = (if p = v2 then 1 else 0) - (if p = (L, 0) then 1 else 0)) :
    ∃ (τ : Pt → ℤ) (δ1 δ2 : ℤ), (δ1 = 2 ∨ δ1 = -2) ∧ (δ2 = 2 ∨ δ2 = -2) ∧ ∀ e, Interior V e →
      τ e.hi - τ e.lo = (if up H e then 1 else -1) - δ1 * F1 e - δ2 * F2 e := by
  set w := wC V H
  set S := V.biUnion cellE
  have hS : Supp S w := wC_supp
  set T : Finset Pt := S.biUnion (fun e => {e.p, e.q})
  have hT : ∀ e ∈ S, e.p ∈ T ∧ e.q ∈ T := fun e he =>
    ⟨Finset.mem_biUnion.2 ⟨e, he, by simp⟩, Finset.mem_biUnion.2 ⟨e, he, by simp⟩⟩
  set O : Pt := (L, 0)
  set δ1 := defect w v1 with hδ1def
  set δ2 := defect w v2 with hδ2def
  have hδ1 : δ1 = 2 ∨ δ1 = -2 := wC_defect1 hv1 hd1
  have hδ2 : δ2 = 2 ∨ δ2 = -2 := wC_defect1 hv2 hd2
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
  choose SF FF hSF hFI hFD using hflow
  -- Defects vanish at inner points other than the vortices, and off `T`.
  --
  have hδin : ∀ q, Inner V q → q ≠ v1 → q ≠ v2 → defect w q = 0 := fun q hq h1 h2 =>
    wC_defect_inner hq (hdeg q h1 h2 hq)
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
  have hv1T : v1 ∈ T := by
    by_contra h
    have := hδT _ h
    rw [← hδ1def] at this
    rcases hδ1 with h' | h' <;> omega
  have hv2T : v2 ∈ T := by
    by_contra h
    have := hδT _ h
    rw [← hδ2def] at this
    rcases hδ2 with h' | h' <;> omega
  -- The correction and the corrected weight.
  --
  set β : Edge → ℤ := fun g => ∑ q ∈ T, defect w q * FF q g
  set g : Edge → ℤ := fun e => w e - β e - δ1 * F1 e - δ2 * F2 e
  set Sg : Finset Edge := S ∪ T.biUnion SF ∪ S1 ∪ S2
  have hSg : Supp Sg g := by
    intro e he
    have h1 : e ∉ S := fun h => he (by simp [Sg, h])
    have h2 : ∀ q ∈ T, e ∉ SF q := fun q hq h =>
      he (by simp only [Sg, Finset.mem_union, Finset.mem_biUnion]; exact Or.inl (Or.inl
        (Or.inr ⟨q, hq, h⟩)))
    have h3 : e ∉ S1 := fun h => he (by simp [Sg, h])
    have h4 : e ∉ S2 := fun h => he (by simp [Sg, h])
    simp only [g, β]
    rw [hS e h1, hS1 e h3, hS2 e h4, mul_zero, mul_zero, sub_zero, sub_zero, zero_sub,
      neg_eq_zero]
    apply Finset.sum_eq_zero
    intro q hq
    rw [hSF q e (h2 q hq), mul_zero]
  have hβI : ∀ e, Interior V e → β e = 0 := by
    intro e he
    simp only [β]
    apply Finset.sum_eq_zero
    intro q _
    rw [hFI q e he, mul_zero]
  have hdefβ : ∀ p, defect β p = ∑ q ∈ T, defect w q * defect (FF q) p := by
    intro p
    simp only [defect, β, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro q _
    ring
  have hbal : Balanced g := by
    intro p
    have key : defect g p = 0 := by
      have hg : defect g p = defect w p - defect β p - δ1 * defect F1 p - δ2 * defect F2 p := by
        simp only [defect, g]; ring
      rw [hg, hdefβ, hD1, hD2]
      set X : Pt → ℤ := fun q => (if p = q then 1 else 0) - (if p = O then 1 else 0) with hX
      have term : ∀ q ∈ T, defect w q * defect (FF q) p =
          defect w q * X q - (if q = v1 then δ1 * X v1 else 0) -
            (if q = v2 then δ2 * X v2 else 0) := by
        intro q _
        rw [hFD q p]
        by_cases hq : Inner V q
        · rw [ite_eq_left hq]
          by_cases hq1 : q = v1
          · rw [hq1, ite_eq_left rfl, ite_eq_right h12, ← hδ1def]; ring
          · by_cases hq2 : q = v2
            · rw [hq2, ite_eq_right (Ne.symm h12), ite_eq_left rfl, ← hδ2def]; ring
            · rw [hδin q hq hq1 hq2, ite_eq_right hq1, ite_eq_right hq2]; ring
        · have hq1 : q ≠ v1 := fun h => hq (h ▸ hv1)
          have hq2 : q ≠ v2 := fun h => hq (h ▸ hv2)
          rw [ite_eq_right hq, ite_eq_right hq1, ite_eq_right hq2]; simp only [hX]; ring
      rw [Finset.sum_congr rfl term, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
        Finset.sum_ite_eq' T v1, Finset.sum_ite_eq' T v2, ite_eq_left hv1T, ite_eq_left hv2T]
      have e1 : ∑ q ∈ T, defect w q * X q =
          (∑ q ∈ T, if p = q then defect w q else 0) -
            (∑ q ∈ T, defect w q) * (if p = O then 1 else 0) := by
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
  refine ⟨pot Sg g, δ1, δ2, hδ1, hδ2, fun e he => ?_⟩
  rw [pot_jump hSg hbal e]
  simp only [g, w, wC, ite_eq_left he, hβI e he, sub_zero]
  unfold wS
  ring

end height2

/-! ## The two slit flows -/

section flows

variable {V : Finset Pt}

lemma exists_below_pt (V : Finset Pt) : ∃ M : ℤ, ∀ q ∈ V, M < q.2 := by
  refine ⟨-(∑ q ∈ V, |q.2|) - 1, fun q hq => ?_⟩
  have h1 : |q.2| ≤ ∑ q ∈ V, |q.2| :=
    Finset.single_le_sum (f := fun q : Pt => |q.2|) (fun _ _ => abs_nonneg _) hq
  have h2 := neg_abs_le q.2
  omega

lemma reach_row {y : ℤ} (hy : ∀ q ∈ V, y < q.2) (x : ℤ) :
    ∀ n : ℕ, Relation.ReflTransGen (NIAdj V) (x, y) (x + n, y) := by
  intro n
  induction n with
  | zero => simpa using Relation.ReflTransGen.refl
  | succ n ih =>
    have hm : (x + n, y) ∉ V := fun h => by have := hy _ h; simp at this
    have hs := niadj_of_edge (V := V) ⟨.h, (x + n, y)⟩
      (Or.inl (fun hc => hm hc.1))
    simp only [Edge.q] at hs
    push_cast
    rw [← add_assoc]
    exact ih.tail hs

-- The left slit: a unit flow from `(a, b)` to `(L, 0)`, equal to `-1` on the interior slit edges
-- and `0` on the other interior edges.
--
lemma flowL {L : ℤ} (hL : ∀ q ∈ V, L < q.1) {a b : ℤ} (hv : (a, b) ∈ V) :
    ∃ (S : Finset Edge) (F : Edge → ℤ), Supp S F ∧
      (∀ p, defect F p = (if p = (a, b) then 1 else 0) - (if p = (L, 0) then 1 else 0)) ∧
      ∀ e, Interior V e → F e = if SlitE a b e then -1 else 0 := by
  have hLa : L < a := hL _ hv
  obtain ⟨S2, f2, hS2, hI2, hD2⟩ := flow_of_reach (V := V) (O := (L, 0)) (a := (L, b))
    (reach_left (fun q hq => hL q hq) (fun q hq => hL q hq))
  refine ⟨(Finset.Ico L a).image (fun x => (⟨.h, (x, b)⟩ : Edge)) ∪ S2,
    fun e => slitF a b L e + f2 e, ?_, ?_, ?_⟩
  · intro e he
    simp only
    rw [slitF_supp a b L e (fun h => he (Finset.mem_union_left _ h)),
      hS2 e (fun h => he (Finset.mem_union_right _ h))]
    simp
  · intro p
    have h1 := slitF_defect (b := b) hLa p
    have h2 := hD2 p
    unfold defect at h1 h2 ⊢
    linarith
  · intro e he
    simp only [hI2 e he, add_zero]
    unfold slitF SlitE
    by_cases h : e.d = .h ∧ e.p.2 = b ∧ e.p.1 < a
    · have hLe : L ≤ e.p.1 := le_of_lt (hL _ (by have := he.1.1; simpa [Edge.hi] using this))
      rw [ite_eq_left ⟨h.1, h.2.1, hLe, h.2.2⟩, ite_eq_left h]
    · rw [ite_eq_right (fun h' => h ⟨h'.1, h'.2.1, h'.2.2.2⟩), ite_eq_right h]

-- The downward slit edges: vertical, on column `a`, below `b`.
--
def SlitD (a b : ℤ) (e : Edge) : Prop := e.d = .v ∧ e.p.1 = a ∧ e.p.2 < b

-- Unit flow from `(a, b)` straight down to `(a, M)`.
--
noncomputable def slitFD (a b M : ℤ) (e : Edge) : ℤ :=
  if e.d = .v ∧ e.p.1 = a ∧ M ≤ e.p.2 ∧ e.p.2 < b then 1 else 0

lemma slitFD_supp (a b M : ℤ) :
    Supp ((Finset.Ico M b).image (fun y => (⟨.v, (a, y)⟩ : Edge))) (slitFD a b M) := by
  intro e he
  unfold slitFD
  rw [ite_eq_right]
  rintro ⟨hd, hx, h1, h2⟩
  apply he
  rw [Finset.mem_image]
  refine ⟨e.p.2, Finset.mem_Ico.2 ⟨h1, h2⟩, ?_⟩
  obtain ⟨d, ⟨x, y⟩⟩ := e
  simp only at hd hx ⊢
  rw [hd, hx]

lemma slitFD_defect {a b M : ℤ} (hM : M < b) (p : Pt) :
    defect (slitFD a b M) p = (if p = (a, b) then 1 else 0) - (if p = (a, M) then 1 else 0) := by
  obtain ⟨x, y⟩ := p
  unfold defect slitFD
  simp only [eD, eR, eL, eU, Prod.mk.injEq, reduceCtorEq, false_and, ite_false, true_and]
  by_cases hx : x = a
  · subst hx
    simp only [true_and]
    split_ifs <;> omega
  · simp only [hx, false_and, ite_false]
    simp

-- The downward slit: a unit flow from `(a, b)` to `(L, 0)`, equal to `1` on the interior slit
-- edges and `0` on the other interior edges.
--
lemma flowD {L : ℤ} (hL : ∀ q ∈ V, L < q.1) {a b : ℤ} (hv : (a, b) ∈ V) :
    ∃ (S : Finset Edge) (F : Edge → ℤ), Supp S F ∧
      (∀ p, defect F p = (if p = (a, b) then 1 else 0) - (if p = (L, 0) then 1 else 0)) ∧
      ∀ e, Interior V e → F e = if SlitD a b e then 1 else 0 := by
  obtain ⟨M, hM⟩ := exists_below_pt V
  have hMb : M < b := hM _ hv
  have hLa : L < a := hL _ hv
  have hrow : Relation.ReflTransGen (NIAdj V) (a, M) (L, M) := by
    obtain ⟨n, hn⟩ : ∃ n : ℕ, a = L + n := ⟨(a - L).toNat, by omega⟩
    rw [hn]
    exact reach_symm (reach_row hM L n)
  obtain ⟨S2, f2, hS2, hI2, hD2⟩ := flow_of_reach (V := V) (O := (L, 0)) (a := (a, M))
    (hrow.trans (reach_left (fun q hq => hL q hq) (fun q hq => hL q hq)))
  refine ⟨(Finset.Ico M b).image (fun y => (⟨.v, (a, y)⟩ : Edge)) ∪ S2,
    fun e => slitFD a b M e + f2 e, ?_, ?_, ?_⟩
  · intro e he
    simp only
    rw [slitFD_supp a b M e (fun h => he (Finset.mem_union_left _ h)),
      hS2 e (fun h => he (Finset.mem_union_right _ h))]
    simp
  · intro p
    have h1 := slitFD_defect (a := a) hMb p
    have h2 := hD2 p
    unfold defect at h1 h2 ⊢
    linarith
  · intro e he
    simp only [hI2 e he, add_zero]
    unfold slitFD SlitD
    by_cases h : e.d = .v ∧ e.p.1 = a ∧ e.p.2 < b
    · have hMe : M ≤ e.p.2 := le_of_lt (hM _ (by have := he.1.1; simpa [Edge.hi] using this))
      rw [ite_eq_left ⟨h.1, h.2.1, hMe, h.2.2⟩, ite_eq_left h]
    · rw [ite_eq_right (fun h' => h ⟨h'.1, h'.2.1, h'.2.2.2⟩), ite_eq_right h]

end flows

/-! ## Steps between cells -/

-- The sign of a side: `+1` for the top and right sides, `-1` for the bottom and left sides.
--
def sgnS : Side → ℤ
  | .t => 1
  | .r => 1
  | .b => -1
  | .l => -1

section step

variable {V : Finset Pt} {H : Finset Edge}

lemma tau_step {τ : Pt → ℤ} {K : Edge → ℤ}
    (hj : ∀ e, Interior V e → τ e.hi - τ e.lo = (if up H e then 1 else -1) + K e)
    (c : Pt) (s : Side) (hc : IsCell V c) (hc' : IsCell V (nb c s)) :
    τ (nb c s) - τ c = (if outArc H c s then 1 else -1) + sgnS s * K (sideEdge c s) := by
  obtain ⟨x, y⟩ := c
  cases s
  · have he : Interior V (bot (x, y)) := ⟨hc, by simpa [bot, Edge.lo, nb] using hc'⟩
    have := hj _ he
    have h1 : (bot (x, y)).hi = (x, y) := rfl
    have h2 : (bot (x, y)).lo = (x, y - 1) := rfl
    rw [h1, h2] at this
    show τ (x, y - 1) - τ (x, y) = (if (!up H (bot (x, y))) = true then 1 else -1) +
      -1 * K (bot (x, y))
    cases hu : up H (bot (x, y)) <;> simp [hu] at this ⊢ <;> linarith
  · have he : Interior V (top (x, y)) :=
      ⟨by simpa [top, nb] using hc', by simpa [top, Edge.lo] using hc⟩
    have := hj _ he
    have h1 : (top (x, y)).hi = (x, y + 1) := rfl
    have h2 : (top (x, y)).lo = (x, y) := by simp [top, Edge.lo]
    rw [h1, h2] at this
    show τ (x, y + 1) - τ (x, y) = (if up H (top (x, y)) = true then 1 else -1) +
      1 * K (top (x, y))
    cases hu : up H (top (x, y)) <;> simp [hu] at this ⊢ <;> linarith
  · have he : Interior V (lft (x, y)) := ⟨hc, by simpa [lft, Edge.lo, nb] using hc'⟩
    have := hj _ he
    have h1 : (lft (x, y)).hi = (x, y) := rfl
    have h2 : (lft (x, y)).lo = (x - 1, y) := rfl
    rw [h1, h2] at this
    show τ (x - 1, y) - τ (x, y) = (if (!up H (lft (x, y))) = true then 1 else -1) +
      -1 * K (lft (x, y))
    cases hu : up H (lft (x, y)) <;> simp [hu] at this ⊢ <;> linarith
  · have he : Interior V (rgt (x, y)) :=
      ⟨by simpa [rgt, nb] using hc', by simpa [rgt, Edge.lo] using hc⟩
    have := hj _ he
    have h1 : (rgt (x, y)).hi = (x + 1, y) := rfl
    have h2 : (rgt (x, y)).lo = (x, y) := by simp [rgt, Edge.lo]
    rw [h1, h2] at this
    show τ (x + 1, y) - τ (x, y) = (if up H (rgt (x, y)) = true then 1 else -1) +
      1 * K (rgt (x, y))
    cases hu : up H (rgt (x, y)) <;> simp [hu] at this ⊢ <;> linarith

end step

-- Crossing the left slit of `(a, b)` from cell `c` across side `s`: `+1` going up, `-1` going down.
--
def kL (a b : ℤ) (c : Pt) : Side → ℤ
  | .t => if c.1 < a ∧ c.2 + 1 = b then 1 else 0
  | .b => if c.1 < a ∧ c.2 = b then -1 else 0
  | _ => 0

-- Crossing the downward slit of `(a, b)`: `+1` going left, `-1` going right.
--
def kD (a b : ℤ) (c : Pt) : Side → ℤ
  | .l => if c.1 = a ∧ c.2 < b then 1 else 0
  | .r => if c.1 + 1 = a ∧ c.2 < b then -1 else 0
  | _ => 0

lemma kL_eq (a b : ℤ) (c : Pt) (s : Side) :
    sgnS s * (if SlitE a b (sideEdge c s) then 1 else 0) = kL a b c s := by
  obtain ⟨x, y⟩ := c
  cases s <;> simp only [sgnS, kL, sideEdge, SlitE, bot, top, lft, rgt, reduceCtorEq,
    false_and, ite_false, mul_zero, true_and] <;> split_ifs <;> omega

lemma kD_eq (a b : ℤ) (c : Pt) (s : Side) :
    sgnS s * (if SlitD a b (sideEdge c s) then -1 else 0) = kD a b c s := by
  obtain ⟨x, y⟩ := c
  cases s <;> simp only [sgnS, kD, sideEdge, SlitD, bot, top, lft, rgt, reduceCtorEq,
    false_and, ite_false, mul_zero, true_and] <;> split_ifs <;> omega

/-! ## The labels -/

-- Lower vortex (row and downward ray, slit left): 1 lower left, 2 lower right, 3 upper.
--
def labD (a b : ℤ) (c : Pt) : ℤ := if b ≤ c.2 then 3 else if c.1 ≤ a - 1 then 1 else 2

-- Upper vortex (row and upward ray, slit left): 1 lower, 2 upper right, 3 upper left.
--
def labU (a b : ℤ) (c : Pt) : ℤ := if c.2 ≤ b - 1 then 1 else if a ≤ c.1 then 2 else 3

-- Left vortex on a common row (column and left ray, slit left): 0 lower left, 1 right,
-- 2 upper left.
--
def labL (a b : ℤ) (c : Pt) : ℤ := if a ≤ c.1 then 1 else if b ≤ c.2 then 2 else 0

-- Right vortex on a common row (column and right ray, slit down): 0 lower right, 1 upper right,
-- 2 left.
--
def labR (a b : ℤ) (c : Pt) : ℤ := if c.1 ≤ a - 1 then 2 else if c.2 ≤ b - 1 then 0 else 1

lemma geo_rows (a1 b1 a2 b2 x y μ1 μ2 : ℤ) (hb : b1 < b2) (hμ1 : μ1 = 1 ∨ μ1 = -1)
    (hμ2 : μ2 = 1 ∨ μ2 = -1) (s : Side) :
    1 ≤ 3 * (1 - 2 * μ1 * kL a1 b1 (x, y) s - 2 * μ2 * kL a2 b2 (x, y) s) +
      2 * μ1 * (labD a1 b1 (nb (x, y) s) - labD a1 b1 (x, y)) +
      2 * μ2 * (labU a2 b2 (nb (x, y) s) - labU a2 b2 (x, y)) := by
  rcases hμ1 with rfl | rfl <;> rcases hμ2 with rfl | rfl <;> cases s <;>
    simp only [kL, labD, labU, nb] <;> split_ifs <;> omega

lemma geo_same (a1 a2 b x y μ1 μ2 : ℤ) (ha : a1 < a2) (hμ1 : μ1 = 1 ∨ μ1 = -1)
    (hμ2 : μ2 = 1 ∨ μ2 = -1) (s : Side) :
    1 ≤ 3 * (1 - 2 * μ1 * kL a1 b (x, y) s - 2 * μ2 * kD a2 b (x, y) s) +
      2 * μ1 * (labL a1 b (nb (x, y) s) - labL a1 b (x, y)) +
      2 * μ2 * (labR a2 b (nb (x, y) s) - labR a2 b (x, y)) := by
  rcases hμ1 with rfl | rfl <;> rcases hμ2 with rfl | rfl <;> cases s <;>
    simp only [kL, kD, labL, labR, nb] <;> split_ifs <;> omega

/-! ## No closed arc walk -/

section arc

variable {V : Finset Pt} {H : Finset Edge}

-- The potential argument, for any step data `k₁, k₂` and labels satisfying the per-step bound.
--
lemma arc_of_pot {τ : Pt → ℤ} {δ1 δ2 : ℤ} (hδ1 : δ1 = 2 ∨ δ1 = -2) (hδ2 : δ2 = 2 ∨ δ2 = -2)
    (k1 k2 : Pt → Side → ℤ) (l1 l2 : Pt → ℤ)
    (hstep : ∀ c s, IsCell V c → IsCell V (nb c s) →
      τ (nb c s) - τ c = (if outArc H c s then 1 else -1) + δ1 * k1 c s + δ2 * k2 c s)
    (hgeo : ∀ c s μ1 μ2, (μ1 = 1 ∨ μ1 = -1) → (μ2 = 1 ∨ μ2 = -1) →
      1 ≤ 3 * (1 - 2 * μ1 * k1 c s - 2 * μ2 * k2 c s) + 2 * μ1 * (l1 (nb c s) - l1 c) +
        2 * μ2 * (l2 (nb c s) - l2 c)) : ArcAcyc V H := by
  intro o c hc
  set g : ℤ := if o then 1 else -1 with hg
  have hgo : (if o = true then (1 : ℤ) else -1) = g := by cases o <;> simp [hg]
  have hg2 : g = 1 ∨ g = -1 := by cases o <;> simp [hg]
  have hgg : g * g = 1 := by rcases hg2 with h | h <;> rw [h] <;> norm_num
  set μ1 : ℤ := if g * δ1 = 2 then -1 else 1 with hμ1
  set μ2 : ℤ := if g * δ2 = 2 then -1 else 1 with hμ2
  have e1 : g * δ1 = -2 * μ1 := by
    rcases hg2 with h | h <;> rcases hδ1 with h' | h' <;> simp [hμ1, h, h']
  have e2 : g * δ2 = -2 * μ2 := by
    rcases hg2 with h | h <;> rcases hδ2 with h' | h' <;> simp [hμ2, h, h']
  have m1 : μ1 = 1 ∨ μ1 = -1 := by simp only [hμ1]; split_ifs <;> simp
  have m2 : μ2 = 1 ∨ μ2 = -1 := by simp only [hμ2]; split_ifs <;> simp
  set Φ : Pt → ℤ := fun c => 3 * (g * τ c) + 2 * μ1 * l1 c + 2 * μ2 * l2 c with hΦ
  have mono : ∀ c c', ArcStep V H o c c' → Φ c < Φ c' := by
    intro c c' h
    obtain ⟨hc1, hc2, s, has, rfl⟩ := h
    have hst := hstep c s hc1 hc2
    rw [has, hgo] at hst
    have hgτ : g * τ (nb c s) - g * τ c = 1 - 2 * μ1 * k1 c s - 2 * μ2 * k2 c s := by
      have : g * τ (nb c s) - g * τ c = g * (τ (nb c s) - τ c) := by ring
      rw [this, hst]
      have : g * (g + δ1 * k1 c s + δ2 * k2 c s) =
          g * g + (g * δ1) * k1 c s + (g * δ2) * k2 c s := by ring
      rw [this, hgg, e1, e2]; ring
    have := hgeo c s μ1 μ2 m1 m2
    simp only [hΦ]
    nlinarith
  have key : ∀ c c', Relation.TransGen (ArcStep V H o) c c' → Φ c < Φ c' := by
    intro c c' h
    induction h with
    | single h => exact mono _ _ h
    | tail _ h ih => exact ih.trans (mono _ _ h)
  exact lt_irrefl _ (key c c hc)

-- **Two vortices on different rows.**
--
theorem arc_rows (hs : Solid V) {a1 b1 a2 b2 : ℤ} (hb : b1 < b2) (hv1 : Inner V (a1, b1))
    (hv2 : Inner V (a2, b2)) (hd1 : deg H (a1, b1) = 1) (hd2 : deg H (a2, b2) = 1)
    (hdeg : ∀ p, p ≠ (a1, b1) → p ≠ (a2, b2) → Inner V p → deg H p = 2) : ArcAcyc V H := by
  obtain ⟨L, hL⟩ := exists_left_pt V
  obtain ⟨S1, F1, hS1, hD1, hI1⟩ := flowL hL hv1.2.2.2.1
  obtain ⟨S2, F2, hS2, hD2, hI2⟩ := flowL hL hv2.2.2.2.1
  have h12 : (a1, b1) ≠ (a2, b2) := fun h => by simp at h; omega
  obtain ⟨τ, δ1, δ2, hδ1, hδ2, hj⟩ :=
    height2 hs hL h12 hv1 hv2 hd1 hd2 hdeg hS1 hS2 hD1 hD2
  have hj' : ∀ e, Interior V e → τ e.hi - τ e.lo = (if up H e then 1 else -1) +
      (δ1 * (if SlitE a1 b1 e then 1 else 0) + δ2 * (if SlitE a2 b2 e then 1 else 0)) := by
    intro e he
    rw [hj e he, hI1 e he, hI2 e he]
    split_ifs <;> ring
  refine arc_of_pot (τ := τ) hδ1 hδ2 (kL a1 b1) (kL a2 b2) (labD a1 b1) (labU a2 b2) (fun c s hc hc' => ?_)
    (fun c s μ1 μ2 m1 m2 => geo_rows a1 b1 a2 b2 c.1 c.2 μ1 μ2 hb m1 m2 s)
  rw [tau_step hj' c s hc hc', ← kL_eq a1 b1 c s, ← kL_eq a2 b2 c s]
  ring

-- **Two vortices on a common row.**
--
theorem arc_same (hs : Solid V) {a1 a2 b : ℤ} (ha : a1 < a2) (hv1 : Inner V (a1, b))
    (hv2 : Inner V (a2, b)) (hd1 : deg H (a1, b) = 1) (hd2 : deg H (a2, b) = 1)
    (hdeg : ∀ p, p ≠ (a1, b) → p ≠ (a2, b) → Inner V p → deg H p = 2) : ArcAcyc V H := by
  obtain ⟨L, hL⟩ := exists_left_pt V
  obtain ⟨S1, F1, hS1, hD1, hI1⟩ := flowL hL hv1.2.2.2.1
  obtain ⟨S2, F2, hS2, hD2, hI2⟩ := flowD hL hv2.2.2.2.1
  have h12 : (a1, b) ≠ (a2, b) := fun h => by simp at h; omega
  obtain ⟨τ, δ1, δ2, hδ1, hδ2, hj⟩ :=
    height2 hs hL h12 hv1 hv2 hd1 hd2 hdeg hS1 hS2 hD1 hD2
  have hj' : ∀ e, Interior V e → τ e.hi - τ e.lo = (if up H e then 1 else -1) +
      (δ1 * (if SlitE a1 b e then 1 else 0) + δ2 * (if SlitD a2 b e then -1 else 0)) := by
    intro e he
    rw [hj e he, hI1 e he, hI2 e he]
    split_ifs <;> ring
  refine arc_of_pot (τ := τ) hδ1 hδ2 (kL a1 b) (kD a2 b) (labL a1 b) (labR a2 b) (fun c s hc hc' => ?_)
    (fun c s μ1 μ2 m1 m2 => geo_same a1 a2 b c.1 c.2 μ1 μ2 ha m1 m2 s)
  rw [tau_step hj' c s hc hc', ← kL_eq a1 b c s, ← kD_eq a2 b c s]
  ring

-- **No closed climb with two vortices.** On a solid graph whose inner points have degree 2
-- except two distinct vortices of degree 1, there is no closed arc walk.
--
theorem arc_vortex2 (hs : Solid V) {v1 v2 : Pt} (h12 : v1 ≠ v2) (hv1 : Inner V v1)
    (hv2 : Inner V v2) (hd1 : deg H v1 = 1) (hd2 : deg H v2 = 1)
    (hdeg : ∀ p, p ≠ v1 → p ≠ v2 → Inner V p → deg H p = 2) : ArcAcyc V H := by
  obtain ⟨a1, b1⟩ := v1
  obtain ⟨a2, b2⟩ := v2
  rcases lt_trichotomy b1 b2 with hb | hb | hb
  · exact arc_rows hs hb hv1 hv2 hd1 hd2 hdeg
  · subst hb
    have ha : a1 ≠ a2 := fun h => h12 (by rw [h])
    rcases lt_or_gt_of_ne ha with ha | ha
    · exact arc_same hs ha hv1 hv2 hd1 hd2 hdeg
    · exact arc_same hs ha hv2 hv1 hd2 hd1 (fun p h2 h1 hp => hdeg p h1 h2 hp)
  · exact arc_rows hs hb hv2 hv1 hd2 hd1 (fun p h2 h1 hp => hdeg p h1 h2 hp)

end arc

end HP

end SolidGridHam
