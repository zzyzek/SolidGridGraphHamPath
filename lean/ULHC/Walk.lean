/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
import ULHC.StripCount

/-!
# The boundary walk (thesis Lemmas 6.3, 6.4; paper Claims 1, 2)

A *border* is a set `P ⊆ V` closed under `F`-adjacency (a union of classes). An edge is
*cut* when exactly one end is in `P`. The walk crosses cut sides of cells, always along
`F`'s dependency arcs (orientation `o = true`) or always against them (`o = false`).

## The local step

At a cell entered through a cut side, with no Type III cells around:
* either the cell is *pass-through*: another cut side leads out along the walk's
  orientation, and the entry side is its only cut side with an incoming arc
  (these are the Type II cells);
* or the cell *stops* the walk: one dark side (`back`), the walk entered through a
  lateral side, the front side is not cut, and its arc points out (a Type I cell; Phase II
  starts here).

This is checked over all local configurations by `decide`. Its three hypotheses:
dark sides are never cut (closure of `P`); a cut side never has both of its neighbouring
sides light (from no Type III cells, by forcing); an alternating cell has no cut side
(no Type III cells).
-/

namespace ULHC

open Finset Classical

instance : Fintype Side := ⟨{.b, .t, .l, .r}, by intro x; cases x <;> simp⟩

/-! ## The local model -/

def mS (mb mt ml mr : Bool) : Side → Bool
  | .b => mb
  | .t => mt
  | .l => ml
  | .r => mr

def isCutCell (pbl pbr ptl ptr : Bool) : Side → Bool
  | .b => pbl != pbr
  | .t => ptl != ptr
  | .l => pbl != ptl
  | .r => pbr != ptr

def outS (q : Bool) (m : Side → Bool) : Side → Bool
  | .b => q == m .b
  | .t => q == m .t
  | .l => !(q == m .l)
  | .r => !(q == m .r)

-- The two sides next to a side.
--
def latA : Side → Side
  | .b => .l
  | .t => .l
  | .l => .b
  | .r => .b

def latB : Side → Side
  | .b => .r
  | .t => .r
  | .l => .t
  | .r => .t

theorem walk_local : ∀ (mb mt ml mr pbl pbr ptl ptr q o : Bool) (si : Side),
    (∀ s, mS mb mt ml mr s = true → isCutCell pbl pbr ptl ptr s = false) →
    (∀ s, isCutCell pbl pbr ptl ptr s = true →
        (mS mb mt ml mr (latA s) || mS mb mt ml mr (latB s)) = true) →
    ((mb == mt) && (ml == mr) && (mb != ml) = true → ∀ s, isCutCell pbl pbr ptl ptr s = false) →
    isCutCell pbl pbr ptl ptr si = true → outS q (mS mb mt ml mr) si = !o →
    (∃ so, so ≠ si ∧ isCutCell pbl pbr ptl ptr so = true ∧ outS q (mS mb mt ml mr) so = o ∧
        ∀ s', isCutCell pbl pbr ptl ptr s' = true → outS q (mS mb mt ml mr) s' = !o → s' = si) ∨
    (∃ d, mS mb mt ml mr d = true ∧ mS mb mt ml mr d.opp = false ∧
        mS mb mt ml mr (latA d) = false ∧ mS mb mt ml mr (latB d) = false ∧
        (si = latA d ∨ si = latB d) ∧ isCutCell pbl pbr ptl ptr d.opp = false ∧
        outS q (mS mb mt ml mr) d.opp = o ∧
        ∀ s, isCutCell pbl pbr ptl ptr s = true → outS q (mS mb mt ml mr) s = !o) := by
  decide

/-! ## Borders and cut edges -/

-- A union of classes of `F` inside `V`.
--
def Border (V : Finset Pt) (F : Finset Edge) (P : Finset Pt) : Prop :=
  P ⊆ V ∧ ∀ x ∈ P, ∀ y, Adj F x y → y ∈ P

-- Exactly one end of `e` is in `P`.
--
def Cut (P : Finset Pt) (e : Edge) : Prop := (e.p ∈ P ↔ e.q ∉ P)

instance (P : Finset Pt) (e : Edge) : Decidable (Cut P e) := by unfold Cut; infer_instance

lemma Border.mem_of_conn {V : Finset Pt} {F : Finset Edge} {P : Finset Pt} (hB : Border V F P)
    {x y : Pt} (hx : x ∈ P) (h : Conn F x y) : y ∈ P := by
  induction h with
  | refl => exact hx
  | tail _ hyz ih => exact hB.2 _ ih _ hyz

lemma Border.not_cut {V : Finset Pt} {F : Finset Edge} {P : Finset Pt} (hB : Border V F P)
    {e : Edge} (he : e ∈ F) : ¬ Cut P e := by
  unfold Cut
  have h1 : e.p ∈ P → e.q ∈ P := fun h => hB.2 _ h _ ⟨e, he, Or.inl ⟨rfl, rfl⟩⟩
  have h2 : e.q ∈ P → e.p ∈ P := fun h => hB.2 _ h _ ⟨e, he, Or.inr ⟨rfl, rfl⟩⟩
  tauto

lemma Border.same_side {V : Finset Pt} {F : Finset Edge} {P : Finset Pt} (hB : Border V F P)
    {x y : Pt} (h : Conn F x y) : (x ∈ P ↔ y ∈ P) :=
  ⟨fun hx => hB.mem_of_conn hx h, fun hy => hB.mem_of_conn hy h.symm⟩

/-! ## Bridging the local model -/

def corner (w : Pt) : Side → Side → Pt
  | _, _ => w

lemma latA_opp (s : Side) : latA s.opp = latA s := by cases s <;> rfl
lemma latB_opp (s : Side) : latB s.opp = latB s := by cases s <;> rfl
lemma opp_opp (s : Side) : s.opp.opp = s := by cases s <;> rfl

lemma lat1_eq (c : Pt) (s : Side) : lat1 c s = sideEdge c (latA s) := by cases s <;> rfl
lemma lat2_eq (c : Pt) (s : Side) : lat2 c s = sideEdge c (latB s) := by cases s <;> rfl

-- The step at one cell, for actual `F` and `P`.
--
theorem step_cell {V : Finset Pt} {F : Finset Edge} {P : Finset Pt} (hB : Border V F P)
    (w : Pt) (o : Bool)
    (hlat : ∀ s, Cut P (sideEdge w s) → sideEdge w (latA s) ∈ F ∨ sideEdge w (latB s) ∈ F)
    (halt : Alt F w → ∀ s, ¬ Cut P (sideEdge w s))
    (si : Side) (hcut : Cut P (sideEdge w si)) (hin : outArc F w si = !o) :
    (∃ so, so ≠ si ∧ Cut P (sideEdge w so) ∧ outArc F w so = o ∧
        ∀ s', Cut P (sideEdge w s') → outArc F w s' = !o → s' = si) ∨
    (∃ d, sideEdge w d ∈ F ∧ sideEdge w d.opp ∉ F ∧ sideEdge w (latA d) ∉ F ∧
        sideEdge w (latB d) ∉ F ∧ (si = latA d ∨ si = latB d) ∧ ¬ Cut P (sideEdge w d.opp) ∧
        outArc F w d.opp = o ∧ ∀ s, Cut P (sideEdge w s) → outArc F w s = !o) := by
  obtain ⟨x, y⟩ := w
  set mb := decide (bot (x, y) ∈ F)
  set mt := decide (top (x, y) ∈ F)
  set ml := decide (lft (x, y) ∈ F)
  set mr := decide (rgt (x, y) ∈ F)
  set pbl := decide ((x, y) ∈ P)
  set pbr := decide ((x + 1, y) ∈ P)
  set ptl := decide ((x, y + 1) ∈ P)
  set ptr := decide ((x + 1, y + 1) ∈ P)
  have hm : ∀ s, mS mb mt ml mr s = true ↔ sideEdge (x, y) s ∈ F := by
    intro s; cases s <;> simp [mS, mb, mt, ml, mr, sideEdge]
  have hc : ∀ s, isCutCell pbl pbr ptl ptr s = true ↔ Cut P (sideEdge (x, y) s) := by
    intro s
    cases s <;> simp only [isCutCell, Cut, sideEdge, bot, top, lft, rgt, Edge.q, pbl, pbr, ptl, ptr]
    · by_cases h1 : (x, y) ∈ P <;> by_cases h2 : (x + 1, y) ∈ P <;> simp [h1, h2]
    · by_cases h1 : (x, y + 1) ∈ P <;> by_cases h2 : (x + 1, y + 1) ∈ P <;> simp [h1, h2]
    · by_cases h1 : (x, y) ∈ P <;> by_cases h2 : (x, y + 1) ∈ P <;> simp [h1, h2]
    · by_cases h1 : (x + 1, y) ∈ P <;> by_cases h2 : (x + 1, y + 1) ∈ P <;> simp [h1, h2]
  have hmf : ∀ s, mS mb mt ml mr s = false ↔ sideEdge (x, y) s ∉ F := by
    intro s; rw [← hm s]; simp
  have hcf : ∀ s, isCutCell pbl pbr ptl ptr s = false ↔ ¬ Cut P (sideEdge (x, y) s) := by
    intro s; rw [← hc s]; simp
  have ho : ∀ s, outS (par (x, y)) (mS mb mt ml mr) s = outArc F (x, y) s := by
    intro s
    rw [outArc_eq]
    cases s <;> rfl
  have key := walk_local mb mt ml mr pbl pbr ptl ptr (par (x, y)) o si
    (fun s hs => (hcf s).2 (hB.not_cut ((hm s).1 hs)))
    (by
      intro s hs
      rcases hlat s ((hc s).1 hs) with h | h
      · rw [(hm _).2 h]; rfl
      · rw [(hm _).2 h]; simp)
    (by
      intro h s
      apply (hcf s).2
      apply halt _ s
      simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at h
      obtain ⟨⟨h1, h2⟩, h3⟩ := h
      unfold Alt
      simp only [mb, mt, ml, mr] at h1 h2 h3
      by_cases hb : bot (x, y) ∈ F <;> by_cases hl : lft (x, y) ∈ F <;> simp_all)
    ((hc si).2 hcut)
    (by rw [ho]; exact hin)
  rcases key with ⟨so, h1, h2, h3, h4⟩ | ⟨d, h1, h2, h3, h4, h5, h6, h7, h8⟩
  · left
    refine ⟨so, h1, (hc so).1 h2, by rw [← ho]; exact h3, ?_⟩
    intro s' hs' ho'
    exact h4 s' ((hc s').2 hs') (by rw [ho]; exact ho')
  · right
    exact ⟨d, (hm d).1 h1, (hmf _).1 h2, (hmf _).1 h3, (hmf _).1 h4, h5, (hcf _).1 h6,
      by rw [← ho]; exact h7, fun s hs => by rw [← ho]; exact h8 s ((hc s).2 hs)⟩

/-! ## No Type III cells -/

-- Every alternating cell of the graph has its two dark sides in one class.
--
def NoTypeIII (V : Finset Pt) (F : Finset Edge) : Prop :=
  ∀ c, IsCell V c → ∀ s, back c s ∈ F → front c s ∈ F → lat1 c s ∉ F → lat2 c s ∉ F →
    Conn F (back1 c s) (front1 c s)

-- Cell `c` is not a Type III cell.
--
def NotTypeIII (_V : Finset Pt) (F : Finset Edge) (c : Pt) : Prop :=
  ∀ s, back c s ∈ F → front c s ∈ F → lat1 c s ∉ F → lat2 c s ∉ F →
    Conn F (back1 c s) (front1 c s)

lemma NoTypeIII.at {V : Finset Pt} {F : Finset Edge} (hT : NoTypeIII V F) {c : Pt}
    (hc : IsCell V c) : NotTypeIII V F c := hT c hc

-- In an alternating cell that is not Type III, all four corners are in one class.
--
lemma alt_corners_conn' {V : Finset Pt} {F : Finset Edge} {r : Pt} (hT : NotTypeIII V F r)
    (ha : Alt F r) :
    Conn F r (r.1 + 1, r.2) ∧ Conn F r (r.1, r.2 + 1) ∧ Conn F r (r.1 + 1, r.2 + 1) := by
  obtain ⟨x, y⟩ := r
  rcases ha with ⟨hb, ht, hl, hr'⟩ | ⟨hb, ht, hl, hr'⟩
  · have h := hT .t hb ht hl hr'
    simp only [back1, front1] at h
    have e1 : Conn F (x, y) (x + 1, y) := Conn.of_edge hb
    have e2 : Conn F (x, y + 1) (x + 1, y + 1) := Conn.of_edge ht
    exact ⟨e1, h, h.trans e2⟩
  · have h := hT .r hl hr' hb ht
    simp only [back1, front1] at h
    have e1 : Conn F (x, y) (x, y + 1) := Conn.of_edge hl
    have e2 : Conn F (x + 1, y) (x + 1, y + 1) := Conn.of_edge hr'
    exact ⟨h, e1, h.trans e2⟩

lemma alt_corners_conn {V : Finset Pt} {F : Finset Edge} (hT : NoTypeIII V F) {r : Pt}
    (hr : IsCell V r) (ha : Alt F r) :
    Conn F r (r.1 + 1, r.2) ∧ Conn F r (r.1, r.2 + 1) ∧ Conn F r (r.1 + 1, r.2 + 1) :=
  alt_corners_conn' (hT.at hr) ha

lemma corners_of_side (c : Pt) (s : Side) (P : Finset Pt)
    (h : (c ∈ P ↔ (c.1 + 1, c.2) ∈ P) ∧ (c ∈ P ↔ (c.1, c.2 + 1) ∈ P) ∧
      (c ∈ P ↔ (c.1 + 1, c.2 + 1) ∈ P)) : ¬ Cut P (sideEdge c s) := by
  obtain ⟨x, y⟩ := c
  obtain ⟨h1, h2, h3⟩ := h
  unfold Cut
  cases s <;> simp only [sideEdge, bot, top, lft, rgt, Edge.q] <;> tauto

lemma isCell_of_corners {V : Finset Pt} (c : Pt) (s : Side)
    (h1 : back1 c s ∈ V) (h2 : back2 c s ∈ V) (h3 : front1 c s ∈ V) (h4 : front2 c s ∈ V) :
    IsCell V c := by
  obtain ⟨x, y⟩ := c
  cases s <;> simp only [back1, back2, front1, front2] at h1 h2 h3 h4 <;>
    exact ⟨by assumption, by assumption, by assumption, by assumption⟩

section hypsLocal

variable {V : Finset Pt} {F : Finset Edge} {P : Finset Pt}
  (hF : Deg2 V F) (hB : Border V F P)
include hF hB

omit hF in
lemma alt_no_cut_l {w : Pt} (hTw : NotTypeIII V F w) (ha : Alt F w) (s : Side) :
    ¬ Cut P (sideEdge w s) := by
  obtain ⟨h1, h2, h3⟩ := alt_corners_conn' hTw ha
  exact corners_of_side w s P ⟨hB.same_side h1, hB.same_side h2, hB.same_side h3⟩

-- A cut side always has a dark neighbouring side.
--
lemma cut_has_dark_lat_l {w : Pt} (hw : IsCell V w) (s : Side) (hcut : Cut P (sideEdge w s))
    (hTr : IsCell V (nb w s) → NotTypeIII V F (nb w s)) :
    sideEdge w (latA s) ∈ F ∨ sideEdge w (latB s) ∈ F := by
  by_contra hn
  push Not at hn
  obtain ⟨n1, n2⟩ := hn
  rw [← lat1_eq] at n1
  rw [← lat2_eq] at n2
  have hfr : front w s ∉ F := fun h => hB.not_cut h hcut
  -- Forcing at the two front corners.
  obtain ⟨wb1, wb2, wf1, wf2⟩ := isCell_corners hw s
  have d1 := deg_front1 w s F
  have d2 := deg_front2 w s F
  rw [hF.2 _ wf1] at d1
  rw [hF.2 _ wf2] at d2
  have i1 : ind F (lat1 w s) = 0 := by simp [ind, n1]
  have i2 : ind F (lat2 w s) = 0 := by simp [ind, n2]
  have i3 : ind F (front w s) = 0 := by simp [ind, hfr]
  have mem1 : ∀ e, ind F e = 1 → e ∈ F := by
    intro e h; unfold ind at h; split_ifs at h with h'; exact h'
  rw [i1, i3] at d1
  rw [i2, i3] at d2
  have l1 : lat1 (nb w s) s ∈ F := by
    have := ind_le_one F (lat1 (nb w s) s)
    have := ind_le_one F (outer1 w s)
    exact mem1 _ (by omega)
  have l2 : lat2 (nb w s) s ∈ F := by
    have := ind_le_one F (lat2 (nb w s) s)
    have := ind_le_one F (outer2 w s)
    exact mem1 _ (by omega)
  set r := nb w s
  have c1 : Conn F (back1 r s) (front1 r s) := (ends_lat1 r s).conn l1
  have c2 : Conn F (back2 r s) (front2 r s) := (ends_lat2 r s).conn l2
  have rf1 : front1 r s ∈ V := conn_mem hF.1 (by rw [back1_nb]; exact wf1) c1
  have rf2 : front2 r s ∈ V := conn_mem hF.1 (by rw [back2_nb]; exact wf2) c2
  have hr : IsCell V r := isCell_of_corners r s (by rw [back1_nb]; exact wf1)
    (by rw [back2_nb]; exact wf2) rf1 rf2
  -- The two front corners of `w` are joined, so the front is not cut.
  have hjoin : Conn F (back1 r s) (back2 r s) := by
    by_cases hf : front r s ∈ F
    · exact (c1.trans ((ends_front r s).conn hf)).trans c2.symm
    · have hbk : back r s ∉ F := by rw [back_nb]; exact hfr
      have ha : Alt F r := by
        rw [lat1_eq] at l1
        rw [lat2_eq] at l2
        simp only [back, front, sideEdge] at hbk hf
        obtain ⟨x, y⟩ := r
        cases s <;> simp only [latA, latB, sideEdge, Side.opp] at l1 l2 hbk hf <;> unfold Alt <;>
          tauto
      obtain ⟨k1, k2, k3⟩ := alt_corners_conn' (hTr hr) ha
      obtain ⟨x, y⟩ := r
      cases s <;> simp only [back1, back2] at * <;>
        first
        | exact k1
        | exact k2.symm.trans k3
        | exact k1.symm.trans k3
        | exact k2
  rw [back1_nb, back2_nb] at hjoin
  apply hcut |> fun h => ?_
  have := hB.same_side hjoin
  have hends := ends_front w s
  unfold Cut at hcut
  rcases hends with ⟨q1, q2⟩ | ⟨q1, q2⟩ <;> simp only [front] at q1 q2 <;> rw [q1, q2] at hcut <;>
    tauto


end hypsLocal

section hyps

variable {V : Finset Pt} {F : Finset Edge} {P : Finset Pt}
  (hF : Deg2 V F) (hB : Border V F P) (hT : NoTypeIII V F)
include hF hB hT

-- An alternating cell has no cut side.
--
omit hF in
lemma alt_no_cut {w : Pt} (hw : IsCell V w) (ha : Alt F w) (s : Side) :
    ¬ Cut P (sideEdge w s) := by
  obtain ⟨h1, h2, h3⟩ := alt_corners_conn hT hw ha
  exact corners_of_side w s P ⟨hB.same_side h1, hB.same_side h2, hB.same_side h3⟩

-- A cut side always has a dark neighbouring side.
--
lemma cut_has_dark_lat {w : Pt} (hw : IsCell V w) (s : Side) (hcut : Cut P (sideEdge w s)) :
    sideEdge w (latA s) ∈ F ∨ sideEdge w (latB s) ∈ F := by
  by_contra hn
  push Not at hn
  obtain ⟨n1, n2⟩ := hn
  rw [← lat1_eq] at n1
  rw [← lat2_eq] at n2
  have hfr : front w s ∉ F := fun h => hB.not_cut h hcut
  -- Forcing at the two front corners.
  obtain ⟨wb1, wb2, wf1, wf2⟩ := isCell_corners hw s
  have d1 := deg_front1 w s F
  have d2 := deg_front2 w s F
  rw [hF.2 _ wf1] at d1
  rw [hF.2 _ wf2] at d2
  have i1 : ind F (lat1 w s) = 0 := by simp [ind, n1]
  have i2 : ind F (lat2 w s) = 0 := by simp [ind, n2]
  have i3 : ind F (front w s) = 0 := by simp [ind, hfr]
  have mem1 : ∀ e, ind F e = 1 → e ∈ F := by
    intro e h; unfold ind at h; split_ifs at h with h'; exact h'
  rw [i1, i3] at d1
  rw [i2, i3] at d2
  have l1 : lat1 (nb w s) s ∈ F := by
    have := ind_le_one F (lat1 (nb w s) s)
    have := ind_le_one F (outer1 w s)
    exact mem1 _ (by omega)
  have l2 : lat2 (nb w s) s ∈ F := by
    have := ind_le_one F (lat2 (nb w s) s)
    have := ind_le_one F (outer2 w s)
    exact mem1 _ (by omega)
  set r := nb w s
  have c1 : Conn F (back1 r s) (front1 r s) := (ends_lat1 r s).conn l1
  have c2 : Conn F (back2 r s) (front2 r s) := (ends_lat2 r s).conn l2
  have rf1 : front1 r s ∈ V := conn_mem hF.1 (by rw [back1_nb]; exact wf1) c1
  have rf2 : front2 r s ∈ V := conn_mem hF.1 (by rw [back2_nb]; exact wf2) c2
  have hr : IsCell V r := isCell_of_corners r s (by rw [back1_nb]; exact wf1)
    (by rw [back2_nb]; exact wf2) rf1 rf2
  -- The two front corners of `w` are joined, so the front is not cut.
  have hjoin : Conn F (back1 r s) (back2 r s) := by
    by_cases hf : front r s ∈ F
    · exact (c1.trans ((ends_front r s).conn hf)).trans c2.symm
    · have hbk : back r s ∉ F := by rw [back_nb]; exact hfr
      have ha : Alt F r := by
        rw [lat1_eq] at l1
        rw [lat2_eq] at l2
        simp only [back, front, sideEdge] at hbk hf
        obtain ⟨x, y⟩ := r
        cases s <;> simp only [latA, latB, sideEdge, Side.opp] at l1 l2 hbk hf <;> unfold Alt <;>
          tauto
      obtain ⟨k1, k2, k3⟩ := alt_corners_conn hT hr ha
      obtain ⟨x, y⟩ := r
      cases s <;> simp only [back1, back2] at * <;>
        first
        | exact k1
        | exact k2.symm.trans k3
        | exact k1.symm.trans k3
        | exact k2
  rw [back1_nb, back2_nb] at hjoin
  apply hcut |> fun h => ?_
  have := hB.same_side hjoin
  have hends := ends_front w s
  unfold Cut at hcut
  rcases hends with ⟨q1, q2⟩ | ⟨q1, q2⟩ <;> simp only [front] at q1 q2 <;> rw [q1, q2] at hcut <;>
    tauto

end hyps

end ULHC
