/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
module

public import SolidGridHam.Cycle.L57

@[expose] public section

/-!
# Dual walks

A dual walk moves from cell to cell across light sides (sides not in `F`), or leaves the graph
across a light side on its outer boundary and comes back in across another. The set of sides
crossed an odd number of times is accumulated by symmetric difference.

**Main fact (`DWalk.sep`).** A closed dual walk separates the two ends of every side it
crosses an odd number of times: they lie in different classes of `F`. This is the discrete
Jordan curve argument, via `separation`.
-/

namespace SolidGridHam

open Finset Classical

/-! ## Parity of sides -/

lemma ind_symmDiff (A B : Finset Edge) (e : Edge) :
    ind (symmDiff A B) e % 2 = (ind A e + ind B e) % 2 := by
  simp only [ind, Finset.mem_symmDiff]
  by_cases ha : e ∈ A <;> by_cases hb : e ∈ B <;> simp [ha, hb]

lemma sidesIn_symmDiff (A B : Finset Edge) (c : Pt) :
    sidesIn (symmDiff A B) c % 2 = (sidesIn A c + sidesIn B c) % 2 := by
  unfold sidesIn
  have h1 := ind_symmDiff A B (bot c)
  have h2 := ind_symmDiff A B (top c)
  have h3 := ind_symmDiff A B (lft c)
  have h4 := ind_symmDiff A B (rgt c)
  omega

lemma sidesIn_empty (c : Pt) : sidesIn ∅ c = 0 := by
  simp [sidesIn, ind]

lemma sidesIn_single (e : Edge) (x : Pt) :
    sidesIn {e} x = if e ∈ cellE x then 1 else 0 := by
  obtain ⟨d, p⟩ := e
  obtain ⟨a, b⟩ := x
  unfold sidesIn ind cellE
  cases d <;>
    simp only [bot, top, lft, rgt, Finset.mem_singleton, Finset.mem_insert, Edge.mk.injEq,
      reduceCtorEq, false_and, or_false, false_or, true_and] <;>
    split_ifs <;> simp_all [Prod.ext_iff] <;> grind

lemma side_mem_cellE_iff (c : Pt) (tf : Side) (x : Pt) :
    sideEdge c tf ∈ cellE x ↔ x = c ∨ x = nb c tf :=
  ⟨fun h => cell_of_side c h, fun h => by
    rcases h with rfl | rfl
    · exact side_mem_cellE _ tf
    · exact side_mem_cellE_nb _ tf⟩

lemma nb_ne (c : Pt) (tf : Side) : c ≠ nb c tf := by
  obtain ⟨p, q⟩ := c; cases tf <;> simp [nb] <;> omega

lemma isEdge_side {V : Finset Pt} {c : Pt} (hc : IsCell V c) (tf : Side) : IsEdge V (sideEdge c tf) := by
  obtain ⟨x, y⟩ := c
  obtain ⟨h1, h2, h3, h4⟩ := hc
  cases tf <;> simp [IsEdge, sideEdge, bot, top, lft, rgt, Edge.q] <;>
    exact ⟨by assumption, by assumption⟩

/-! ## Dual steps and walks -/

-- One step of a dual walk from cell `c` to cell `c'`, with the sides it crosses.
--
inductive DStep (V : Finset Pt) (F : Finset Edge) : Pt → Pt → Finset Edge → Prop
  | inner (c : Pt) (tf : Side) : IsCell V c → IsCell V (nb c tf) → sideEdge c tf ∉ F →
      DStep V F c (nb c tf) {sideEdge c tf}
  | outer (c c' : Pt) (tf t' : Side) : IsCell V c → IsCell V c' → ¬ IsCell V (nb c tf) →
      ¬ IsCell V (nb c' t') → sideEdge c tf ∉ F → sideEdge c' t' ∉ F →
      DStep V F c c' (symmDiff {sideEdge c tf} {sideEdge c' t'})

-- A dual walk from `a` to `b`; `B` holds the sides crossed an odd number of times.
--
inductive DWalk (V : Finset Pt) (F : Finset Edge) : Pt → Pt → Finset Edge → Prop
  | nil (a : Pt) : DWalk V F a a ∅
  | cons {a d b : Pt} {E B : Finset Edge} : DStep V F a d E → DWalk V F d b B →
      DWalk V F a b (symmDiff E B)

section dual

variable {V : Finset Pt} {F : Finset Edge}

lemma DStep.parity {a d : Pt} {E : Finset Edge} (h : DStep V F a d E) (x : Pt) (hx : IsCell V x) :
    sidesIn E x % 2 = ((if x = a then 1 else 0) + (if x = d then 1 else 0)) % 2 := by
  cases h with
  | inner tf _ _ _ =>
    simp only [sidesIn_single, side_mem_cellE_iff]
    have := nb_ne a tf
    by_cases h1 : x = a <;> by_cases h2 : x = nb a tf <;> simp [h1, h2] <;> simp_all
  | outer _ tf t' _ _ n1 n2 _ _ =>
    rw [sidesIn_symmDiff]
    simp only [sidesIn_single, side_mem_cellE_iff]
    have e1 : x ≠ nb a tf := fun h => n1 (h ▸ hx)
    have e2 : x ≠ nb d t' := fun h => n2 (h ▸ hx)
    by_cases h1 : x = a <;> by_cases h2 : x = d <;> subst_vars <;> simp_all

lemma DStep.light {a d : Pt} {E : Finset Edge} (h : DStep V F a d E) : ∀ e ∈ E, e ∉ F := by
  cases h with
  | inner tf _ _ hl => intro e he; rw [Finset.mem_singleton.1 he]; exact hl
  | outer c' tf t' _ _ _ _ hl hl' =>
    intro e he
    rcases Finset.mem_symmDiff.1 he with ⟨h, _⟩ | ⟨h, _⟩
    · rw [Finset.mem_singleton.1 h]; exact hl
    · rw [Finset.mem_singleton.1 h]; exact hl'

lemma DWalk.parity {a b : Pt} {B : Finset Edge} (h : DWalk V F a b B) (x : Pt)
    (hx : IsCell V x) :
    sidesIn B x % 2 = ((if x = a then 1 else 0) + (if x = b then 1 else 0)) % 2 := by
  induction h with
  | nil a => rw [sidesIn_empty]; split_ifs <;> rfl
  | cons hs _ ih =>
    rw [sidesIn_symmDiff]
    have := hs.parity x hx
    split_ifs at this ih ⊢ <;> omega

lemma DWalk.light {a b : Pt} {B : Finset Edge} (h : DWalk V F a b B) : ∀ e ∈ B, e ∉ F := by
  induction h with
  | nil a => intro e he; simp at he
  | cons hs _ ih =>
    intro e he
    rcases Finset.mem_symmDiff.1 he with ⟨h, _⟩ | ⟨h, _⟩
    · exact hs.light e h
    · exact ih e h

lemma DWalk.trans {a b c : Pt} {B B' : Finset Edge} (h : DWalk V F a b B) (h' : DWalk V F b c B') :
    DWalk V F a c (symmDiff B B') := by
  induction h with
  | nil a => rw [show symmDiff (∅ : Finset Edge) B' = B' from bot_symmDiff B']; exact h'
  | cons hs _ ih =>
    rw [symmDiff_assoc]
    exact DWalk.cons hs (ih h')

-- **A closed dual walk separates.** The two ends of a side crossed an odd number of times
-- lie in different classes.
--
theorem DWalk.sep (hs : Solid V) (hFV : Inside V F) (x0 : Pt)
    (hconn : ∀ z ∈ V, Conn (GE V) x0 z) {a : Pt} {B : Finset Edge} (h : DWalk V F a a B)
    {e : Edge} (he : e ∈ B) (hE : IsEdge V e) : ¬ Conn F e.p e.q := by
  have heven : ∀ c, IsCell V c → sidesIn B c % 2 = 0 := by
    intro c hc
    rw [h.parity c hc]
    split_ifs <;> rfl
  obtain ⟨P, hB, hcut⟩ := separation B hs heven hFV h.light x0 hconn
  intro hc
  have := (hcut e hE).2 he
  unfold Cut at this
  have := hB.same_side hc
  tauto

theorem DWalk.sep_ends (hs : Solid V) (hFV : Inside V F) (x0 : Pt)
    (hconn : ∀ z ∈ V, Conn (GE V) x0 z) {a : Pt} {B : Finset Edge} (h : DWalk V F a a B)
    {e : Edge} {u v : Pt} (hE : Ends e u v) (he : e ∈ B) (hu : u ∈ V) (hv : v ∈ V) :
    ¬ Conn F u v := by
  rw [← hE.conn_iff]
  exact h.sep hs hFV x0 hconn he (hE.isEdge hu hv)

/-! ## Inter sides are exactly the sides lying in an even light set -/

-- The cut of any vertex set meets every cell in an even number of sides.
--
lemma cut_sides_even (P : Finset Pt) (B : Finset Edge) (hB : ∀ e, e ∈ B ↔ IsEdge V e ∧ Cut P e)
    (c : Pt) (hc : IsCell V c) : sidesIn B c % 2 = 0 := by
  obtain ⟨x, y⟩ := c
  obtain ⟨h1, h2, h3, h4⟩ := hc
  unfold sidesIn ind
  simp only [hB, IsEdge, Cut, bot, top, lft, rgt, Edge.q]
  by_cases a : (x, y) ∈ P <;> by_cases b : (x + 1, y) ∈ P <;> by_cases c : (x, y + 1) ∈ P <;>
    by_cases d : (x + 1, y + 1) ∈ P <;> simp_all

-- **Inter sides.** A light side of the graph joins two classes exactly when some even set of
-- light sides contains it.
--
theorem inter_iff_even (hs : Solid V) (hFV : Inside V F) (x0 : Pt)
    (hconn : ∀ z ∈ V, Conn (GE V) x0 z) {e : Edge} (hE : IsEdge V e) :
    ¬ Conn F e.p e.q ↔ ∃ B : Finset Edge, (∀ c, IsCell V c → sidesIn B c % 2 = 0) ∧
      (∀ f ∈ B, f ∉ F) ∧ e ∈ B := by
  constructor
  · intro hn
    set P := cls V F e.p
    have hB : Border V F P := ⟨Finset.filter_subset _ _, fun u hu w hw => closed_cls hFV _ u hu w hw⟩
    refine ⟨(GE V).filter (Cut P), cut_sides_even P _ (fun f => by
      rw [Finset.mem_filter, mem_GE]) , fun f hf hfF => ?_, ?_⟩
    · rw [Finset.mem_filter] at hf
      exact hB.not_cut hfF hf.2
    · rw [Finset.mem_filter, mem_GE]
      refine ⟨hE, ?_⟩
      have hp : e.p ∈ P := mem_cls_self hE.1
      have hq : e.q ∉ P := by
        simp only [P, cls, Finset.mem_filter, not_and]; exact fun _ => hn
      unfold Cut; tauto
  · rintro ⟨B, heven, hlight, he⟩ hc
    obtain ⟨P, hB, hcut⟩ := separation B hs heven hFV hlight x0 hconn
    have := (hcut e hE).2 he
    unfold Cut at this
    have := hB.same_side hc
    tauto

end dual

end SolidGridHam
