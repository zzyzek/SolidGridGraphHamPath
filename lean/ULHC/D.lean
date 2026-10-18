/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
import ULHC.Arcs

/-!
# The potential `D` of a pair of factors

For two edge sets `F`, `H` with the same degree at every lattice point (two 2-factors, or
two path-factors with the same ends), put weight `±2` on each edge of `F ⊕ H`: `+2` when
`F`'s arc across it points from its low cell to its high cell, `−2` otherwise. The weights
are balanced at every point (checked over all local patterns), so the row-sum potential
`D` jumps by exactly the weight across every edge.

`D` plays the role of `h_F − h_H` from the height-function notes, without needing the
height functions themselves: it exists whenever the degrees agree, holes or not.
-/

namespace ULHC

open Finset

-- Weight for the pair: `±2` on `F ⊕ H`, sign from the direction of `F`'s arc.
--
def wb (inS u : Bool) : ℤ := if inS then (if u then 2 else -2) else 0

def wD (F H : Finset Edge) (e : Edge) : ℤ :=
  wb (decide (e ∈ F) ^^ decide (e ∈ H)) (up F e)

def D (F H : Finset Edge) (c : Pt) : ℤ := pot (symmDiff F H) (wD F H) c

lemma wD_supp (F H : Finset Edge) : Supp (symmDiff F H) (wD F H) := by
  intro e he
  rw [Finset.mem_symmDiff] at he
  unfold wD wb
  by_cases h1 : e ∈ F <;> by_cases h2 : e ∈ H <;> simp_all

/-! ## Balance -/

lemma wD_balanced_at (F H : Finset Edge) (p : Pt) (hdeg : deg F p = deg H p) :
    wD F H (eD p) + wD F H (eR p) = wD F H (eL p) + wD F H (eU p) := by
  obtain ⟨x, y⟩ := p
  have p1 := par_sub_sub (x, y)
  have p2 := par_sub_snd (x, y)
  have p3 := par_sub_fst (x, y)
  simp only at p1 p2 p3
  unfold deg ind at hdeg
  unfold wD
  simp only [up, inE1, eD, eR, eL, eU, Edge.lo, p1, p2, p3] at hdeg ⊢
  cases par (x, y) <;>
  by_cases a1 : (⟨.v, (x, y - 1)⟩ : Edge) ∈ F <;>
  by_cases a2 : (⟨.h, (x, y)⟩ : Edge) ∈ F <;>
  by_cases a3 : (⟨.h, (x - 1, y)⟩ : Edge) ∈ F <;>
  by_cases a4 : (⟨.v, (x, y)⟩ : Edge) ∈ F <;>
  by_cases b1 : (⟨.v, (x, y - 1)⟩ : Edge) ∈ H <;>
  by_cases b2 : (⟨.h, (x, y)⟩ : Edge) ∈ H <;>
  by_cases b3 : (⟨.h, (x - 1, y)⟩ : Edge) ∈ H <;>
  by_cases b4 : (⟨.v, (x, y)⟩ : Edge) ∈ H <;>
  simp [a1, a2, a3, a4, b1, b2, b3, b4, wb] at hdeg ⊢

-- Two factors with the same degree function have equal degrees everywhere: off `V`
-- both degrees are 0, since every edge at such a point leaves `V`.
--
lemma deg_zero_of_not_mem {V : Finset Pt} {d : Pt → ℕ} {F : Finset Edge}
    (hF : IsFactor V d F) {p : Pt} (hp : p ∉ V) : deg F p = 0 := by
  obtain ⟨x, y⟩ := p
  have h : ∀ e ∈ F, e.p ∈ V ∧ e.q ∈ V := fun e he => hF.1 e he
  have n1 : eR (x, y) ∉ F := fun he => hp (h _ he).1
  have n2 : eL (x, y) ∉ F := fun he => by
    have := (h _ he).2; simp [eL] at this; exact hp this
  have n3 : eU (x, y) ∉ F := fun he => hp (h _ he).1
  have n4 : eD (x, y) ∉ F := fun he => by
    have := (h _ he).2; simp [eD] at this; exact hp this
  simp [deg, ind, n1, n2, n3, n4]

lemma deg_eq_of_factors {V : Finset Pt} {d : Pt → ℕ} {F H : Finset Edge}
    (hF : IsFactor V d F) (hH : IsFactor V d H) (p : Pt) : deg F p = deg H p := by
  by_cases hp : p ∈ V
  · rw [hF.2 p hp, hH.2 p hp]
  · rw [deg_zero_of_not_mem hF hp, deg_zero_of_not_mem hH hp]

lemma wD_balanced {V : Finset Pt} {d : Pt → ℕ} {F H : Finset Edge}
    (hF : IsFactor V d F) (hH : IsFactor V d H) : Balanced (wD F H) :=
  fun p => wD_balanced_at F H p (deg_eq_of_factors hF hH p)

/-! ## Jumps of `D` -/

lemma wb_not (s u : Bool) : wb s (!u) = - wb s u := by
  cases s <;> cases u <;> simp [wb]

lemma step_aux (a b : ℤ) (u s : Bool) (h : b - a = wb s u) :
    (if u then b - a else a - b) = if s then 2 else 0 := by
  cases u <;> cases s <;> simp [wb] at h ⊢ <;> linarith

section jumps

variable {V : Finset Pt} {d : Pt → ℕ} {F H : Finset Edge}
  (hF : IsFactor V d F) (hH : IsFactor V d H)
include hF hH

lemma D_jump (e : Edge) : D F H e.hi - D F H e.lo = wD F H e :=
  pot_jump (wD_supp F H) (wD_balanced hF hH) e

-- **D1.** Stepping across side `s` of cell `c` along `F`'s arc raises `D` by 2 if the
-- side is in `F ⊕ H` and leaves it unchanged otherwise.
--
lemma D_step (c : Pt) (s : Side) :
    (if outArc F c s then D F H (nb c s) - D F H c else D F H c - D F H (nb c s)) =
      if (decide (sideEdge c s ∈ F) ^^ decide (sideEdge c s ∈ H)) then 2 else 0 := by
  obtain ⟨x, y⟩ := c
  cases s
  · have j := D_jump hF hH (bot (x, y))
    simp only [bot, Edge.hi_mk, Edge.lo_h] at j
    simp only [outArc, nb, sideEdge, bot]
    apply step_aux; rw [wb_not]; unfold wD at j
    exact (neg_sub _ _).symm.trans (congrArg Neg.neg j)
  · have j := D_jump hF hH (top (x, y))
    simp only [top, Edge.hi_mk, Edge.lo_h, add_sub_cancel_right] at j
    simp only [outArc, nb, sideEdge, top]
    apply step_aux; unfold wD at j; exact j
  · have j := D_jump hF hH (lft (x, y))
    simp only [lft, Edge.hi_mk, Edge.lo_v] at j
    simp only [outArc, nb, sideEdge, lft]
    apply step_aux; rw [wb_not]; unfold wD at j
    exact (neg_sub _ _).symm.trans (congrArg Neg.neg j)
  · have j := D_jump hF hH (rgt (x, y))
    simp only [rgt, Edge.hi_mk, Edge.lo_v, add_sub_cancel_right] at j
    simp only [outArc, nb, sideEdge, rgt]
    apply step_aux; unfold wD at j; exact j

end jumps

/-! ## D2: in a solid graph, `D = 0` off the graph's cells -/

section solid

variable {V : Finset Pt} {d : Pt → ℕ} {F H : Finset Edge}

lemma wD_zero_of_not_mem {e : Edge} (h1 : e ∉ F) (h2 : e ∉ H) : wD F H e = 0 := by
  simp [wD, wb, h1, h2]

-- The four cells having lattice point `a` as a corner.
--
def Around (a c : Pt) : Prop :=
  (c.1 = a.1 - 1 ∨ c.1 = a.1) ∧ (c.2 = a.2 - 1 ∨ c.2 = a.2)

lemma not_mem_of_endpoint {G : Finset Edge} {d' : Pt → ℕ} (hG : IsFactor V d' G)
    {e : Edge} {a : Pt} (ha : a ∉ V) (h : e.p = a ∨ e.q = a) : e ∉ G := by
  intro he
  obtain ⟨h1, h2⟩ := hG.1 e he
  rcases h with h | h <;> simp_all

variable (hF : IsFactor V d F) (hH : IsFactor V d H)
include hF hH

-- All four cells at a missing point have the same `D`.
--
lemma D_around {a c : Pt} (ha : a ∉ V) (hc : Around a c) : D F H c = D F H a := by
  obtain ⟨x, y⟩ := a
  have z : ∀ e : Edge, (e.p = (x, y) ∨ e.q = (x, y)) → wD F H e = 0 := fun e h =>
    wD_zero_of_not_mem (not_mem_of_endpoint hF ha h) (not_mem_of_endpoint hH ha h)
  have jR := D_jump hF hH (eR (x, y))
  have jU := D_jump hF hH (eU (x, y))
  have jL := D_jump hF hH (eL (x, y))
  rw [z _ (by simp [eR])] at jR
  rw [z _ (by simp [eU])] at jU
  rw [z _ (by simp [eL, Edge.q])] at jL
  simp only [eR, eU, eL, Edge.hi_mk, Edge.lo_h, Edge.lo_v] at jR jU jL
  obtain ⟨c1, c2⟩ := c
  obtain ⟨h1 | h1, h2 | h2⟩ := hc <;> simp only at h1 h2 <;> subst h1 h2 <;> linarith

-- `D` is constant along king-move chains of missing points.
--
lemma D_chain {a b : Pt} (h : Relation.ReflTransGen (MissAdj V) a b) :
    D F H a = D F H b := by
  induction h with
  | refl => rfl
  | @tail b' c' _ hbc ih =>
    obtain ⟨hb, hc, h1, h2⟩ := hbc
    let m : Pt := (max b'.1 c'.1 - 1, max b'.2 c'.2 - 1)
    have mb : Around b' m := by
      constructor <;> simp only [m] <;> rw [abs_le] at * <;> omega
    have mc : Around c' m := by
      constructor <;> simp only [m] <;> rw [abs_le] at * <;> omega
    rw [ih, ← D_around hF hH hb mb, D_around hF hH hc mc]

-- **D2.**
--
theorem D_eq_zero_of_not_cell (hs : Solid V) {c : Pt} (hc : ¬ IsCell V c) :
    D F H c = 0 := by
  obtain ⟨x, y⟩ := c
  have corner : ∃ a, a ∉ V ∧ Around a (x, y) := by
    unfold IsCell at hc
    by_cases h1 : (x, y) ∈ V
    · by_cases h2 : (x + 1, y) ∈ V
      · by_cases h3 : (x, y + 1) ∈ V
        · refine ⟨(x + 1, y + 1), fun h4 => hc ⟨h1, h2, h3, h4⟩, ?_⟩
          simp [Around]
        · exact ⟨(x, y + 1), h3, by simp [Around]⟩
      · exact ⟨(x + 1, y), h2, by simp [Around]⟩
    · exact ⟨(x, y), h1, by simp [Around]⟩
  obtain ⟨a, ha, hac⟩ := corner
  obtain ⟨b, hab, hb⟩ := hs a ha
  rw [D_around hF hH ha hac, D_chain hF hH hab]
  apply pot_eq_zero_of_left (B := b.1) _ b le_rfl
  intro e he
  rw [Finset.mem_symmDiff] at he
  rcases he with ⟨he, _⟩ | ⟨he, _⟩
  · exact hb _ (hF.1 e he).1
  · exact hb _ (hH.1 e he).1

end solid

/-! ## D2 for factors on a larger set agreeing off `V` -/

section solidW

variable {V W : Finset Pt} {d : Pt → ℕ} {F H : Finset Edge}
  (hF : IsFactor W d F) (hH : IsFactor W d H) (hFH : ∀ e ∈ symmDiff F H, e.p ∈ V ∧ e.q ∈ V)
include hF hH hFH

lemma D_aroundW {a c : Pt} (ha : a ∉ V) (hc : Around a c) : D F H c = D F H a := by
  obtain ⟨x, y⟩ := a
  have z : ∀ e : Edge, (e.p = (x, y) ∨ e.q = (x, y)) → wD F H e = 0 := fun e h => by
    have hn : e ∉ symmDiff F H := fun he => by
      obtain ⟨h1, h2⟩ := hFH e he
      rcases h with h | h <;> simp_all
    rw [Finset.mem_symmDiff] at hn
    push Not at hn
    by_cases h1 : e ∈ F
    · simp [wD, wb, h1, hn.1 h1]
    · by_cases h2 : e ∈ H
      · exact absurd (hn.2 h2) h1
      · exact wD_zero_of_not_mem h1 h2
  have jR := D_jump hF hH (eR (x, y))
  have jU := D_jump hF hH (eU (x, y))
  have jL := D_jump hF hH (eL (x, y))
  rw [z _ (by simp [eR])] at jR
  rw [z _ (by simp [eU])] at jU
  rw [z _ (by simp [eL, Edge.q])] at jL
  simp only [eR, eU, eL, Edge.hi_mk, Edge.lo_h, Edge.lo_v] at jR jU jL
  obtain ⟨c1, c2⟩ := c
  obtain ⟨h1 | h1, h2 | h2⟩ := hc <;> simp only at h1 h2 <;> subst h1 h2 <;> linarith

lemma D_chainW {a b : Pt} (h : Relation.ReflTransGen (MissAdj V) a b) :
    D F H a = D F H b := by
  induction h with
  | refl => rfl
  | @tail b' c' _ hbc ih =>
    obtain ⟨hb, hc, h1, h2⟩ := hbc
    let m : Pt := (max b'.1 c'.1 - 1, max b'.2 c'.2 - 1)
    have mb : Around b' m := by
      constructor <;> simp only [m] <;> rw [abs_le] at * <;> omega
    have mc : Around c' m := by
      constructor <;> simp only [m] <;> rw [abs_le] at * <;> omega
    rw [ih, ← D_aroundW hF hH hFH hb mb, D_aroundW hF hH hFH hc mc]

-- **D2 on `W ⊇ V`**: when `F` and `H` differ only on edges inside the solid `V`, `D` vanishes
-- off the cells of `V`.
--
theorem D_eq_zero_of_not_cellW (hs : Solid V) {c : Pt} (hc : ¬ IsCell V c) : D F H c = 0 := by
  obtain ⟨x, y⟩ := c
  have corner : ∃ a, a ∉ V ∧ Around a (x, y) := by
    unfold IsCell at hc
    by_cases h1 : (x, y) ∈ V
    · by_cases h2 : (x + 1, y) ∈ V
      · by_cases h3 : (x, y + 1) ∈ V
        · refine ⟨(x + 1, y + 1), fun h4 => hc ⟨h1, h2, h3, h4⟩, ?_⟩
          simp [Around]
        · exact ⟨(x, y + 1), h3, by simp [Around]⟩
      · exact ⟨(x + 1, y), h2, by simp [Around]⟩
    · exact ⟨(x, y), h1, by simp [Around]⟩
  obtain ⟨a, ha, hac⟩ := corner
  obtain ⟨b, hab, hb⟩ := hs a ha
  rw [D_aroundW hF hH hFH ha hac, D_chainW hF hH hFH hab]
  exact pot_eq_zero_of_left (B := b.1) (fun e he => hb _ (hFH e he).1) b le_rfl

end solidW

/-! ## `D = 0` off the cells, as a hypothesis -/

-- `D F H` vanishes off the cells of `V`. Solid graphs give it (`D_eq_zero_of_not_cell`); it also
-- holds for factors on `V` plus a pendant-edge point when `F` and `H` share that edge.
--
def SolidFor (V : Finset Pt) (F H : Finset Edge) : Prop := ∀ c, ¬ IsCell V c → D F H c = 0

lemma SolidFor.of_solid {V : Finset Pt} {d : Pt → ℕ} {F H : Finset Edge} (hF : IsFactor V d F)
    (hH : IsFactor V d H) (hs : Solid V) : SolidFor V F H :=
  fun _ hc => D_eq_zero_of_not_cell hF hH hs hc

-- A move that changes `D` only at cells keeps `SolidFor`.
--
-- `SolidFor` on `W ⊇ V` from `V` solid, when `F` and `H` differ only on edges inside `V`.
--
lemma SolidFor.of_solidW {V W : Finset Pt} {d : Pt → ℕ} {F H : Finset Edge} (hF : IsFactor W d F)
    (hH : IsFactor W d H) (hFH : ∀ e ∈ symmDiff F H, e.p ∈ V ∧ e.q ∈ V) (hs : Solid V)
    (hVW : V ⊆ W) : SolidFor W F H := fun _ hc =>
  D_eq_zero_of_not_cellW hF hH hFH hs fun h => hc ⟨hVW h.1, hVW h.2.1, hVW h.2.2.1, hVW h.2.2.2⟩

lemma SolidFor.of_off {V : Finset Pt} {F F' H : Finset Edge} (hs : SolidFor V F H)
    (h : ∀ w, ¬ IsCell V w → D F' H w = D F H w) : SolidFor V F' H :=
  fun w hw => by rw [h w hw]; exact hs w hw

/-! ## D3: flipping a cell -/

-- The four sides of cell `c`, and the edge set obtained by flipping them.
--
def cellE (c : Pt) : Finset Edge := {bot c, top c, lft c, rgt c}

def flip (F : Finset Edge) (c : Pt) : Finset Edge := symmDiff F (cellE c)

lemma up_congr {F F' : Finset Edge} {e : Edge} (h : e ∈ F ↔ e ∈ F') : up F e = up F' e := by
  unfold up inE1; simp [h]

lemma wD_flip_off {F H : Finset Edge} {c : Pt} {e : Edge} (he : e ∉ cellE c) :
    wD (flip F c) H e = wD F H e := by
  have hm : e ∈ flip F c ↔ e ∈ F := by
    simp [flip, Finset.mem_symmDiff, he]
  unfold wD; rw [up_congr hm]; simp [hm]

lemma wD_flip_on {F H : Finset Edge} {c : Pt} {e : Edge} (he : e ∈ cellE c) :
    wD (flip F c) H e - wD F H e = - (if up F e then 2 else -2) := by
  have hm : e ∈ flip F c ↔ e ∉ F := by
    simp [flip, Finset.mem_symmDiff, he]
  have hu : up (flip F c) e = ! up F e := by
    unfold up inE1
    cases e.d <;> cases par e.lo <;> by_cases h : e ∈ F <;> simp [hm, h]
  unfold wD; rw [hu]
  by_cases h1 : e ∈ F <;> by_cases h2 : e ∈ H <;> cases up F e <;> simp [hm, h1, h2, wb]

lemma pot_cellE (c x : Pt) (f : Edge → ℤ) :
    pot (cellE c) f x =
      (if c.2 = x.2 ∧ c.1 ≤ x.1 then f (lft c) else 0) +
      (if c.2 = x.2 ∧ c.1 < x.1 then f (rgt c) else 0) := by
  obtain ⟨c1, c2⟩ := c
  rw [pot_eq_sum_ite]
  unfold cellE
  rw [Finset.sum_insert (by simp [bot, top, lft, rgt]),
    Finset.sum_insert (by simp [top, lft, rgt]),
    Finset.sum_insert (by simp [lft, rgt]), Finset.sum_singleton]
  simp [RowSel, bot, top, lft, rgt]

-- Flipping cell `c` changes `D` only in `c`'s row, from `c` rightward.
--
theorem D_flip_formula (F H : Finset Edge) (c x : Pt) :
    D (flip F c) H x - D F H x =
      (if c.2 = x.2 ∧ c.1 ≤ x.1 then - (if up F (lft c) then 2 else -2) else 0) +
      (if c.2 = x.2 ∧ c.1 < x.1 then - (if up F (rgt c) then 2 else -2) else 0) := by
  let E := symmDiff F H ∪ symmDiff (flip F c) H ∪ cellE c
  have s1 : symmDiff (flip F c) H ⊆ E := by
    intro e he; simp only [E, Finset.mem_union]; tauto
  have s2 : symmDiff F H ⊆ E := by
    intro e he; simp only [E, Finset.mem_union]; tauto
  have s3 : cellE c ⊆ E := by
    intro e he; simp only [E, Finset.mem_union]; tauto
  unfold D
  rw [pot_mono_supp s1 (wD_supp _ _), pot_mono_supp s2 (wD_supp _ _), ← pot_sub]
  have hsupp : Supp (cellE c) (fun e => wD (flip F c) H e - wD F H e) := by
    intro e he; simp [wD_flip_off he]
  rw [← pot_mono_supp s3 hsupp, pot_cellE]
  have hl : lft c ∈ cellE c := by simp [cellE]
  have hr : rgt c ∈ cellE c := by simp [cellE]
  rw [wD_flip_on hl, wD_flip_on hr]

-- **D3** for a sink: flipping lowers `D` by 2 at `c` and nowhere else.
--
theorem D_flip_sink {F H : Finset Edge} {c : Pt} (h : Sink F c) (x : Pt) :
    D (flip F c) H x = D F H x - (if x = c then 2 else 0) := by
  have hl := h .l
  have hr := h .r
  simp only [outArc, Bool.not_eq_false'] at hl hr
  have := D_flip_formula F H c x
  rw [hl, hr] at this
  obtain ⟨x1, x2⟩ := x
  obtain ⟨c1, c2⟩ := c
  simp only [Prod.mk.injEq, ite_true, Bool.false_eq_true, ite_false] at this ⊢
  split_ifs at this ⊢ <;> omega

-- **D3** for a source: flipping raises `D` by 2 at `c` and nowhere else.
--
theorem D_flip_source {F H : Finset Edge} {c : Pt} (h : Source F c) (x : Pt) :
    D (flip F c) H x = D F H x + (if x = c then 2 else 0) := by
  have hl := h .l
  have hr := h .r
  simp only [outArc, Bool.not_eq_true'] at hl hr
  have := D_flip_formula F H c x
  rw [hl, hr] at this
  obtain ⟨x1, x2⟩ := x
  obtain ⟨c1, c2⟩ := c
  simp only [Prod.mk.injEq, ite_true, Bool.false_eq_true, ite_false] at this ⊢
  split_ifs at this ⊢ <;> omega

/-! ## D4, D5: the progress measure `μ` -/

-- The cells of the grid graph.
--
def cells (V : Finset Pt) : Finset Pt := V.filter (IsCell V)

lemma mem_cells {V : Finset Pt} {c : Pt} : c ∈ cells V ↔ IsCell V c := by
  unfold cells; rw [Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨h.1, h⟩⟩

-- `μ = Σ |D|` over the cells of the graph (twice the thesis-style count of flips).
--
def mu (V : Finset Pt) (F H : Finset Edge) : ℕ := ∑ c ∈ cells V, (D F H c).natAbs

lemma D_even (F H : Finset Edge) (c : Pt) : 2 ∣ D F H c := by
  unfold D pot
  apply Finset.dvd_sum
  intro e _
  unfold wD wb
  split_ifs <;> simp

-- **D5** for a sink: flipping a sink with `D > 0` lowers `μ` by 2.
--
theorem mu_flip_sink {V : Finset Pt} {F H : Finset Edge} {c : Pt} (hc : IsCell V c)
    (h : Sink F c) (hD : 0 < D F H c) : mu V (flip F c) H + 2 = mu V F H := by
  unfold mu
  have hcm : c ∈ cells V := mem_cells.2 hc
  rw [← Finset.add_sum_erase _ _ hcm, ← Finset.add_sum_erase _ _ hcm]
  have rest : ∑ x ∈ (cells V).erase c, (D (flip F c) H x).natAbs =
      ∑ x ∈ (cells V).erase c, (D F H x).natAbs := by
    apply Finset.sum_congr rfl
    intro x hx
    rw [D_flip_sink h x]; simp [Finset.ne_of_mem_erase hx]
  rw [rest, D_flip_sink h c]; simp only [ite_true]
  obtain ⟨k, hk⟩ := D_even F H c
  rw [hk] at hD ⊢
  omega

-- **D5** for a source: flipping a source with `D < 0` lowers `μ` by 2.
--
theorem mu_flip_source {V : Finset Pt} {F H : Finset Edge} {c : Pt} (hc : IsCell V c)
    (h : Source F c) (hD : D F H c < 0) : mu V (flip F c) H + 2 = mu V F H := by
  unfold mu
  have hcm : c ∈ cells V := mem_cells.2 hc
  rw [← Finset.add_sum_erase _ _ hcm, ← Finset.add_sum_erase _ _ hcm]
  have rest : ∑ x ∈ (cells V).erase c, (D (flip F c) H x).natAbs =
      ∑ x ∈ (cells V).erase c, (D F H x).natAbs := by
    apply Finset.sum_congr rfl
    intro x hx
    rw [D_flip_source h x]; simp [Finset.ne_of_mem_erase hx]
  rw [rest, D_flip_source h c]; simp only [ite_true]
  obtain ⟨k, hk⟩ := D_even F H c
  rw [hk] at hD ⊢
  omega

-- **D4.** In a solid graph, `μ = 0` forces `F = H`.
--
theorem eq_of_mu_eq_zero {V : Finset Pt} {d : Pt → ℕ} {F H : Finset Edge}
    (hF : IsFactor V d F) (hH : IsFactor V d H) (hs : Solid V) (h0 : mu V F H = 0) :
    F = H := by
  have zero : ∀ c, D F H c = 0 := by
    intro c
    by_cases hc : IsCell V c
    · have := (Finset.sum_eq_zero_iff.1 h0) c (mem_cells.2 hc)
      simpa using this
    · exact D_eq_zero_of_not_cell hF hH hs hc
  by_contra hne
  have : (symmDiff F H).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro he
    exact hne (symmDiff_eq_bot.1 he)
  obtain ⟨e, he⟩ := this
  have j := D_jump hF hH e
  rw [zero, zero] at j
  rw [Finset.mem_symmDiff] at he
  unfold wD wb at j
  rcases he with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> split_ifs at j <;> simp_all

end ULHC
