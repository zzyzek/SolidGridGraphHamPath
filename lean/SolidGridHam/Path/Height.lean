/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
module

public import SolidGridHam.Path.Final

@[expose] public section

/-!
# Sheffield's height function exists on solid graphs

`HeightOn V H τ`: crossing a side between two cells raises `τ` by 1 along `H`'s arc and lowers it
by 1 against it. It exists when every *inner* point (all four faces around it are cells) has
degree 2 in `H`, and `V` is solid.

**Construction.** Put weight `±1` (by `H`'s arc) on every *interior* edge (both faces cells) and
`0` elsewhere: `wC`. It is balanced at inner points (degree 2), but not at boundary points. Route
each boundary point's imbalance (`defect`) to one far-left point `O` along a path of non-interior
edges, which exists because `V` is solid (missing points escape to the left by king moves). The
imbalances add up to `0`, so the corrected weight is balanced everywhere; its potential (`pot`)
is the height. The correction lives on non-interior edges, so steps between cells are untouched.
-/

namespace SolidGridHam

namespace HP

open Finset Classical

-- Both faces of `e` are cells.
--
def Interior (V : Finset Pt) (e : Edge) : Prop := IsCell V e.hi ∧ IsCell V e.lo

-- All four faces around `p` are cells.
--
def Inner (V : Finset Pt) (p : Pt) : Prop :=
  IsCell V (p.1 - 1, p.2 - 1) ∧ IsCell V (p.1, p.2 - 1) ∧ IsCell V (p.1 - 1, p.2) ∧ IsCell V p

-- Imbalance of a weight at a point (`Balanced` is `defect = 0` everywhere).
--
def defect (f : Edge → ℤ) (p : Pt) : ℤ := f (eD p) + f (eR p) - f (eL p) - f (eU p)

-- One step along `H`'s arc: `+1`, against it: `−1`.
--
def wS (H : Finset Edge) (e : Edge) : ℤ := if up H e then 1 else -1

noncomputable def wC (V : Finset Pt) (H : Finset Edge) (e : Edge) : ℤ := if Interior V e then wS H e else 0

-- Unit flow along `e` from `e.p` to `e.q`.
--
noncomputable def uf (e : Edge) (g : Edge) : ℤ := if g = e then (if e.d = .h then 1 else -1) else 0

-- Joined by a non-interior edge.
--
def NIAdj (V : Finset Pt) (a b : Pt) : Prop :=
  ∃ e : Edge, ¬ Interior V e ∧ ((e.p = a ∧ e.q = b) ∨ (e.p = b ∧ e.q = a))

section height

variable {V : Finset Pt} {H : Finset Edge}

/-! ## Local balance -/

lemma wS_defect {p : Pt} (hdeg : deg H p = 2) : defect (wS H) p = 0 := by
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

lemma inner_interior {p : Pt} (h : Inner V p) :
    Interior V (eD p) ∧ Interior V (eR p) ∧ Interior V (eL p) ∧ Interior V (eU p) := by
  obtain ⟨x, y⟩ := p
  obtain ⟨h1, h2, h3, h4⟩ := h
  simp only [Interior, eD, eR, eL, eU, Edge.hi, Edge.lo]
  exact ⟨⟨h2, h1⟩, ⟨h4, h2⟩, ⟨h3, h1⟩, ⟨h4, h3⟩⟩

lemma wC_defect_inner {p : Pt} (h : Inner V p) (hdeg : deg H p = 2) : defect (wC V H) p = 0 := by
  obtain ⟨i1, i2, i3, i4⟩ := inner_interior h
  have := wS_defect hdeg
  unfold defect wC at *
  rw [ite_eq_left i1, ite_eq_left i2, ite_eq_left i3, ite_eq_left i4]
  exact this

lemma wC_supp : Supp (V.biUnion cellE) (wC V H) := by
  intro e he
  unfold wC
  rw [ite_eq_right]
  rintro ⟨hc, _⟩
  apply he
  rw [Finset.mem_biUnion]
  exact ⟨e.hi, hc.1, (mem_cellE_iff e e.hi).2 (Or.inl rfl)⟩

/-! ## Defects: coefficients, linearity, total -/

lemma coef_formula (e : Edge) (p : Pt) :
    (if eD p = e then (1 : ℤ) else 0) + (if eR p = e then 1 else 0) - (if eL p = e then 1 else 0) -
      (if eU p = e then 1 else 0) =
    (if e.d = .h then 1 else -1) * ((if p = e.p then 1 else 0) - (if p = e.q then 1 else 0)) := by
  obtain ⟨d, x, y⟩ := e
  obtain ⟨a, b⟩ := p
  cases d <;> simp only [eD, eR, eL, eU, Edge.q, Edge.mk.injEq, Prod.mk.injEq, reduceCtorEq,
    false_and, true_and, ite_false, ite_true] <;> split_ifs <;> omega

lemma defect_eq_sum {S : Finset Edge} {f : Edge → ℤ} (hS : Supp S f) (p : Pt) :
    defect f p = ∑ e ∈ S, f e * ((if eD p = e then (1 : ℤ) else 0) + (if eR p = e then 1 else 0) -
      (if eL p = e then 1 else 0) - (if eU p = e then 1 else 0)) := by
  have one : ∀ g : Edge, f g = ∑ e ∈ S, f e * (if g = e then 1 else 0) := by
    intro g
    simp only [mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq]
    split_ifs with hg
    · rfl
    · exact hS g hg
  unfold defect
  rw [one (eD p), one (eR p), one (eL p), one (eU p), ← Finset.sum_add_distrib,
    ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro e _
  ring

-- **The imbalances of a finitely supported weight add up to `0`.**
--
lemma sum_defect {S : Finset Edge} {f : Edge → ℤ} (hS : Supp S f) (T : Finset Pt)
    (hT : ∀ e ∈ S, e.p ∈ T ∧ e.q ∈ T) : ∑ p ∈ T, defect f p = 0 := by
  simp only [defect_eq_sum hS, coef_formula]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro e he
  rw [← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_sub_distrib]
  simp only [Finset.sum_ite_eq', (hT e he).1, (hT e he).2, ite_true, sub_self, mul_zero]

lemma defect_uf (e : Edge) (p : Pt) :
    defect (uf e) p = (if p = e.p then 1 else 0) - (if p = e.q then 1 else 0) := by
  have h := coef_formula e p
  have hs : (if e.d = .h then (1 : ℤ) else -1) * (if e.d = .h then 1 else -1) = 1 := by
    split_ifs <;> norm_num
  unfold defect uf
  have e1 : ∀ g : Edge, (if g = e then (if e.d = .h then (1 : ℤ) else -1) else 0) =
      (if e.d = .h then 1 else -1) * (if g = e then 1 else 0) := by
    intro g; split_ifs <;> simp
  rw [e1, e1, e1, e1]
  have : (if eD p = e then (1 : ℤ) else 0) + (if eR p = e then 1 else 0) -
      (if eL p = e then 1 else 0) - (if eU p = e then 1 else 0) =
      (if e.d = .h then 1 else -1) * ((if p = e.p then 1 else 0) - (if p = e.q then 1 else 0)) := h
  calc _ = (if e.d = .h then (1 : ℤ) else -1) * ((if eD p = e then (1 : ℤ) else 0) +
        (if eR p = e then 1 else 0) - (if eL p = e then 1 else 0) -
        (if eU p = e then 1 else 0)) := by ring
    _ = _ := by rw [this, ← mul_assoc, hs, one_mul]

/-! ## Flows along non-interior paths -/

lemma flow_of_reach {O a : Pt} (h : Relation.ReflTransGen (NIAdj V) a O) :
    ∃ (S : Finset Edge) (f : Edge → ℤ), Supp S f ∧ (∀ e, Interior V e → f e = 0) ∧
      ∀ p, defect f p = (if p = a then 1 else 0) - (if p = O then 1 else 0) := by
  induction h with
  | refl => exact ⟨∅, fun _ => 0, fun _ _ => rfl, fun _ _ => rfl, fun p => by simp [defect]⟩
  | @tail b c _ hbc ih =>
    obtain ⟨S, f, hS, hI, hD⟩ := ih
    obtain ⟨e, he, hends⟩ := hbc
    have hue : ∀ g, g ≠ e → uf e g = 0 := fun g hg => by simp [uf, hg]
    have hueI : ∀ g, Interior V g → uf e g = 0 := fun g hg =>
      hue g (fun h => he (h ▸ hg))
    rcases hends with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · refine ⟨insert e S, fun g => f g + uf e g, ?_, ?_, ?_⟩
      · intro g hg
        rw [Finset.mem_insert, not_or] at hg
        simp [hS g hg.2, hue g hg.1]
      · intro g hg; simp [hI g hg, hueI g hg]
      · intro p
        have := defect_uf e p
        rw [h1, h2] at this
        have hd := hD p
        unfold defect at this hd ⊢
        linarith
    · refine ⟨insert e S, fun g => f g - uf e g, ?_, ?_, ?_⟩
      · intro g hg
        rw [Finset.mem_insert, not_or] at hg
        simp [hS g hg.2, hue g hg.1]
      · intro g hg; simp [hI g hg, hueI g hg]
      · intro p
        have := defect_uf e p
        rw [h1, h2] at this
        have hd := hD p
        unfold defect at this hd ⊢
        linarith

/-! ## Reaching the far left through non-interior edges -/

lemma niadj_symm {a b : Pt} (h : NIAdj V a b) : NIAdj V b a := by
  obtain ⟨e, he, h'⟩ := h; exact ⟨e, he, h'.symm⟩

lemma reach_symm {a b : Pt} (h : Relation.ReflTransGen (NIAdj V) a b) :
    Relation.ReflTransGen (NIAdj V) b a := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih => exact Relation.ReflTransGen.head (niadj_symm hbc) ih

lemma niadj_of_edge (e : Edge) (he : ¬ IsCell V e.hi ∨ ¬ IsCell V e.lo) : NIAdj V e.p e.q :=
  ⟨e, fun ⟨h1, h2⟩ => he.elim (· h1) (· h2), Or.inl ⟨rfl, rfl⟩⟩

lemma one_step {a b : Pt} (h : NIAdj V a b) : Relation.ReflTransGen (NIAdj V) a b :=
  Relation.ReflTransGen.single h

-- The corners of a face that is not a cell reach each other.
--
lemma corners_reach {f : Pt} (hf : ¬ IsCell V f) :
    Relation.ReflTransGen (NIAdj V) f (f.1 + 1, f.2) ∧
    Relation.ReflTransGen (NIAdj V) f (f.1, f.2 + 1) ∧
    Relation.ReflTransGen (NIAdj V) f (f.1 + 1, f.2 + 1) := by
  obtain ⟨x, y⟩ := f
  have hb : NIAdj V (x, y) (x + 1, y) := niadj_of_edge ⟨.h, (x, y)⟩ (Or.inl hf)
  have hl : NIAdj V (x, y) (x, y + 1) := niadj_of_edge ⟨.v, (x, y)⟩ (Or.inl hf)
  have hr : NIAdj V (x + 1, y) (x + 1, y + 1) :=
    niadj_of_edge ⟨.v, (x + 1, y)⟩ (Or.inr (by simpa [Edge.lo] using hf))
  exact ⟨one_step hb, one_step hl, (one_step hb).tail hr⟩

-- Any two corners of a non-cell face reach each other.
--
lemma corner_reach {f u v : Pt} (hf : ¬ IsCell V f) (hu : IsCorner u f) (hv : IsCorner v f) :
    Relation.ReflTransGen (NIAdj V) u v := by
  obtain ⟨c1, c2, c3⟩ := corners_reach hf
  have toF : ∀ w, IsCorner w f → Relation.ReflTransGen (NIAdj V) w f := by
    intro w hw
    rcases hw with rfl | rfl | rfl | rfl
    · exact Relation.ReflTransGen.refl
    · exact reach_symm c1
    · exact reach_symm c2
    · exact reach_symm c3
  exact (toF u hu).trans (reach_symm (toF v hv))

lemma not_cell_of_corner {f a : Pt} (ha : a ∉ V) (h : IsCorner a f) : ¬ IsCell V f := by
  intro hc
  obtain ⟨h1, h2, h3, h4⟩ := hc
  rcases h with rfl | rfl | rfl | rfl <;> contradiction

lemma corner_of_near {a b : Pt} (h1 : |a.1 - b.1| ≤ 1) (h2 : |a.2 - b.2| ≤ 1) :
    IsCorner a (min a.1 b.1, min a.2 b.2) := by
  obtain ⟨x, y⟩ := a
  obtain ⟨u, v⟩ := b
  simp only at h1 h2 ⊢
  rw [abs_le] at h1 h2
  unfold IsCorner
  rcases (by omega : min x u = x ∨ min x u + 1 = x) with hx | hx <;>
  rcases (by omega : min y v = y ∨ min y v + 1 = y) with hy | hy
  · left; rw [Prod.ext_iff]; exact ⟨hx.symm, hy.symm⟩
  · right; right; left; rw [Prod.ext_iff]; exact ⟨hx.symm, hy.symm⟩
  · right; left; rw [Prod.ext_iff]; exact ⟨hx.symm, hy.symm⟩
  · right; right; right; rw [Prod.ext_iff]; exact ⟨hx.symm, hy.symm⟩

-- King moves between missing points are non-interior paths.
--
lemma reach_of_miss {a b : Pt} (h : Relation.ReflTransGen (MissAdj V) a b) :
    Relation.ReflTransGen (NIAdj V) a b := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | @tail b' c' _ hbc ih =>
    obtain ⟨hb', _, h1, h2⟩ := hbc
    have cb := corner_of_near h1 h2
    have cc := corner_of_near (a := c') (b := b') (by rw [abs_sub_comm]; exact h1)
      (by rw [abs_sub_comm]; exact h2)
    rw [min_comm c'.1, min_comm c'.2] at cc
    exact ih.trans (corner_reach (not_cell_of_corner hb' cb) cb cc)

-- Straight lines through missing points.
--
lemma reach_vert {x : ℤ} (hx : ∀ q ∈ V, x < q.1) (y : ℤ) :
    ∀ n : ℕ, Relation.ReflTransGen (NIAdj V) (x, y) (x, y + n) := by
  intro n
  induction n with
  | zero => simpa using Relation.ReflTransGen.refl
  | succ n ih =>
    have hm : (x, y + n) ∉ V := fun h => by have := hx _ h; simp at this
    have hs := niadj_of_edge (V := V) ⟨.v, (x, y + n)⟩
      (Or.inl (fun hc => hm hc.1))
    simp only [Edge.q] at hs
    push_cast
    rw [← add_assoc]
    exact ih.tail hs

lemma reach_horiz {y : ℤ} (x : ℤ) (n : ℕ) (hx : ∀ q ∈ V, x + n < q.1) :
    Relation.ReflTransGen (NIAdj V) (x, y) (x + n, y) := by
  induction n with
  | zero => simpa using Relation.ReflTransGen.refl
  | succ n ih =>
    have ih' := ih (fun q hq => by have := hx q hq; push_cast at this; omega)
    have hm : (x + n, y) ∉ V := fun h => by have := hx _ h; push_cast at this; omega
    have hs := niadj_of_edge (V := V) ⟨.h, (x + n, y)⟩
      (Or.inl (fun hc => hm hc.1))
    simp only [Edge.q] at hs
    push_cast
    rw [← add_assoc]
    exact ih'.tail hs

-- Two points left of all of `V` reach each other.
--
lemma reach_left {u v : Pt} (hu : ∀ q ∈ V, u.1 < q.1) (hv : ∀ q ∈ V, v.1 < q.1) :
    Relation.ReflTransGen (NIAdj V) u v := by
  -- Both reach `(m, ·)` with `m = min u.1 v.1`, and the column `x = m` is connected.
  --
  set m := min u.1 v.1
  have hm : ∀ q ∈ V, m < q.1 := fun q hq => lt_of_le_of_lt (min_le_left _ _) (hu q hq)
  have toCol : ∀ w : Pt, (∀ q ∈ V, w.1 < q.1) → m ≤ w.1 →
      Relation.ReflTransGen (NIAdj V) (m, w.2) w := by
    intro w hw hmw
    obtain ⟨n, hn⟩ : ∃ n : ℕ, w.1 = m + n := ⟨(w.1 - m).toNat, by omega⟩
    have := reach_horiz (V := V) (y := w.2) m n (by rw [← hn]; exact hw)
    rw [← hn] at this
    exact this
  have col : ∀ a b : ℤ, Relation.ReflTransGen (NIAdj V) (m, a) (m, b) := by
    intro a b
    rcases le_total a b with h | h
    · obtain ⟨n, hn⟩ : ∃ n : ℕ, b = a + n := ⟨(b - a).toNat, by omega⟩
      rw [hn]; exact reach_vert hm a n
    · obtain ⟨n, hn⟩ : ∃ n : ℕ, a = b + n := ⟨(a - b).toNat, by omega⟩
      rw [hn]; exact reach_symm (reach_vert hm b n)
  exact (reach_symm (toCol u hu (min_le_left _ _))).trans
    ((col u.2 v.2).trans (toCol v hv (min_le_right _ _)))

lemma exists_left_pt (V : Finset Pt) : ∃ L : ℤ, ∀ q ∈ V, L < q.1 := by
  refine ⟨-(∑ q ∈ V, |q.1|) - 1, fun q hq => ?_⟩
  have h1 : |q.1| ≤ ∑ q ∈ V, |q.1| :=
    Finset.single_le_sum (f := fun q : Pt => |q.1|) (fun _ _ => abs_nonneg _) hq
  have h2 := neg_abs_le q.1
  omega

-- **Every point that is not inner reaches the far left.**
--
lemma reach_far (hs : Solid V) {L : ℤ} (hL : ∀ q ∈ V, L < q.1) {p : Pt} (hp : ¬ Inner V p) :
    Relation.ReflTransGen (NIAdj V) p (L, 0) := by
  -- A face around `p` that is not a cell, and a missing corner `a` of it.
  --
  obtain ⟨f, hf, hpf⟩ : ∃ f, ¬ IsCell V f ∧ IsCorner p f := by
    obtain ⟨x, y⟩ := p
    unfold Inner at hp
    by_cases h1 : IsCell V (x - 1, y - 1)
    · by_cases h2 : IsCell V (x, y - 1)
      · by_cases h3 : IsCell V (x - 1, y)
        · exact ⟨(x, y), fun h4 => hp ⟨h1, h2, h3, h4⟩, Or.inl rfl⟩
        · exact ⟨(x - 1, y), h3, Or.inr (Or.inl (by simp))⟩
      · exact ⟨(x, y - 1), h2, Or.inr (Or.inr (Or.inl (by simp)))⟩
    · exact ⟨(x - 1, y - 1), h1, Or.inr (Or.inr (Or.inr (by simp)))⟩
  obtain ⟨a, ha, haf⟩ : ∃ a, a ∉ V ∧ IsCorner a f := by
    obtain ⟨x, y⟩ := f
    unfold IsCell at hf
    by_cases h1 : (x, y) ∈ V
    · by_cases h2 : (x + 1, y) ∈ V
      · by_cases h3 : (x, y + 1) ∈ V
        · exact ⟨(x + 1, y + 1), fun h4 => hf ⟨h1, h2, h3, h4⟩, Or.inr (Or.inr (Or.inr rfl))⟩
        · exact ⟨(x, y + 1), h3, Or.inr (Or.inr (Or.inl rfl))⟩
      · exact ⟨(x + 1, y), h2, Or.inr (Or.inl rfl)⟩
    · exact ⟨(x, y), h1, Or.inl rfl⟩
  obtain ⟨b, hab, hb⟩ := hs a ha
  exact (corner_reach hf hpf haf).trans ((reach_of_miss hab).trans
    (reach_left hb (fun q hq => hL q hq)))

/-! ## The height function -/

-- **Sheffield's height function exists** on a solid graph whose inner points have degree 2.
--
theorem height_exists (hs : Solid V) (hdeg : ∀ p, Inner V p → deg H p = 2) :
    ∃ τ : Pt → ℤ, HeightOn V H τ := by
  set w := wC V H
  set S := V.biUnion cellE
  have hS : Supp S w := wC_supp
  set T : Finset Pt := S.biUnion (fun e => {e.p, e.q})
  have hT : ∀ e ∈ S, e.p ∈ T ∧ e.q ∈ T := fun e he =>
    ⟨Finset.mem_biUnion.2 ⟨e, he, by simp⟩, Finset.mem_biUnion.2 ⟨e, he, by simp⟩⟩
  obtain ⟨L, hL⟩ := exists_left_pt V
  set O : Pt := (L, 0)
  -- A flow from each point that is not inner to `O`.
  --
  have hflow : ∀ q : Pt, ∃ (Sq : Finset Edge) (f : Edge → ℤ), Supp Sq f ∧
      (∀ e, Interior V e → f e = 0) ∧
      (¬ Inner V q → ∀ p, defect f p = (if p = q then 1 else 0) - (if p = O then 1 else 0)) := by
    intro q
    by_cases hq : Inner V q
    · exact ⟨∅, fun _ => 0, fun _ _ => rfl, fun _ _ => rfl, fun h => absurd hq h⟩
    · obtain ⟨Sq, f, h1, h2, h3⟩ := flow_of_reach (reach_far hs hL hq)
      exact ⟨Sq, f, h1, h2, fun _ => h3⟩
  choose SF F hSF hFI hFD using hflow
  -- Defects vanish at inner points and off `T`.
  --
  have hδin : ∀ q, Inner V q → defect w q = 0 := fun q hq => wC_defect_inner hq (hdeg q hq)
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
  -- The correction and the corrected weight.
  --
  set β : Edge → ℤ := fun g => ∑ q ∈ T, defect w q * F q g
  set g : Edge → ℤ := fun e => w e - β e
  set Sg : Finset Edge := S ∪ T.biUnion SF
  have hSg : Supp Sg g := by
    intro e he
    have h1 : e ∉ S := fun h => he (Finset.mem_union_left _ h)
    have h2 : ∀ q ∈ T, e ∉ SF q := fun q hq h =>
      he (Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨q, hq, h⟩))
    simp only [g, β]
    rw [hS e h1, zero_sub, neg_eq_zero]
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
      have hg : defect g p = defect w p - defect β p := by
        simp only [defect, g]; ring
      rw [hg, hdefβ]
      have term : ∀ q ∈ T, defect w q * defect (F q) p =
          defect w q * ((if p = q then 1 else 0) - (if p = O then 1 else 0)) := by
        intro q _
        by_cases hq : Inner V q
        · rw [hδin q hq]; ring
        · rw [hFD q hq p]
      rw [Finset.sum_congr rfl term]
      have e1 : ∑ q ∈ T, defect w q * ((if p = q then (1 : ℤ) else 0) - (if p = O then 1 else 0)) =
          (∑ q ∈ T, if p = q then defect w q else 0) -
            (∑ q ∈ T, defect w q) * (if p = O then 1 else 0) := by
        rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro q _
        split_ifs <;> ring
      rw [e1, hsum, zero_mul, sub_zero, Finset.sum_ite_eq]
      by_cases hpT : p ∈ T
      · rw [ite_eq_left hpT, sub_self]
      · rw [ite_eq_right hpT, hδT p hpT, sub_zero]
    unfold defect at key
    linarith
  refine ⟨pot Sg g, ?_⟩
  intro c s hc hc'
  have hwI : ∀ e, Interior V e → g e = wS H e := by
    intro e he
    simp only [g, w, wC, ite_eq_left he, hβI e he, sub_zero]
  have key : ∀ e, Interior V e →
      pot Sg g e.hi - pot Sg g e.lo = (if up H e then 1 else -1) := fun e he => by
    rw [pot_jump hSg hbal e, hwI e he]; rfl
  obtain ⟨x, y⟩ := c
  cases s
  · have he : Interior V (bot (x, y)) := ⟨hc, by simpa [bot, Edge.lo, nb] using hc'⟩
    have := key _ he
    have h1 : (bot (x, y)).hi = (x, y) := rfl
    have h2 : (bot (x, y)).lo = (x, y - 1) := rfl
    rw [h1, h2] at this
    show pot Sg g (x, y - 1) = pot Sg g (x, y) + (if (!up H (bot (x, y))) = true then 1 else -1)
    cases hu : up H (bot (x, y)) <;> simp [hu] at this ⊢ <;> linarith
  · have he : Interior V (top (x, y)) :=
      ⟨by simpa [top, nb] using hc', by simpa [top, Edge.lo] using hc⟩
    have := key _ he
    have h1 : (top (x, y)).hi = (x, y + 1) := rfl
    have h2 : (top (x, y)).lo = (x, y) := by simp [top, Edge.lo]
    rw [h1, h2] at this
    show pot Sg g (x, y + 1) = pot Sg g (x, y) + (if up H (top (x, y)) = true then 1 else -1)
    cases hu : up H (top (x, y)) <;> simp [hu] at this ⊢ <;> linarith
  · have he : Interior V (lft (x, y)) := ⟨hc, by simpa [lft, Edge.lo, nb] using hc'⟩
    have := key _ he
    have h1 : (lft (x, y)).hi = (x, y) := rfl
    have h2 : (lft (x, y)).lo = (x - 1, y) := rfl
    rw [h1, h2] at this
    show pot Sg g (x - 1, y) = pot Sg g (x, y) + (if (!up H (lft (x, y))) = true then 1 else -1)
    cases hu : up H (lft (x, y)) <;> simp [hu] at this ⊢ <;> linarith
  · have he : Interior V (rgt (x, y)) :=
      ⟨by simpa [rgt, nb] using hc', by simpa [rgt, Edge.lo] using hc⟩
    have := key _ he
    have h1 : (rgt (x, y)).hi = (x + 1, y) := rfl
    have h2 : (rgt (x, y)).lo = (x, y) := by simp [rgt, Edge.lo]
    rw [h1, h2] at this
    show pot Sg g (x + 1, y) = pot Sg g (x, y) + (if up H (rgt (x, y)) = true then 1 else -1)
    cases hu : up H (rgt (x, y)) <;> simp [hu] at this ⊢ <;> linarith

end height

end HP

end SolidGridHam

namespace SolidGridHam

namespace HP

-- **The final count on a solid graph**, with the height function supplied by `height_exists`.
--
theorem final_count_solid {V W : Finset Pt} {d : Pt → ℕ} {H H' : Finset Edge}
    (hH : IsFactor W d H) (hH' : IsFactor W d H') (hs : Solid V)
    (hdeg : ∀ p, Inner V p → deg H p = 2) (hsol : SolidFor V H H') (FP : List FixedPr)
    (hup : ∀ i ∈ FP, outArc H i.bot i.s = true) (hfin : FinalOK V H H' FP) :
    ncomp W H ≤ ncomp W H' + FP.length := by
  obtain ⟨τ, hτ⟩ := height_exists hs hdeg
  exact final_count hH hH' hsol (acyc_of_height hτ) FP hup hfin

end HP

end SolidGridHam
