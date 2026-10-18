/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
module

public import SolidGridHam.Cycle.V2

@[expose] public section

/-!
# Boundary chains and their separation property

An *inter edge* is an edge of the graph, not in `F`, whose ends are in different classes.
A boundary chain is a set of cells linked through inter sides.

With no Type III cells, every cell has an even number (0 or 2) of inter sides. Hence any
closed walk in the graph crosses the inter sides of a chain an even number of times, and
the chain's inter sides are exactly the cut edges of a union of classes (the paper's
border). This is what lets the walk of Theorem A stay on the boundary created by the
previous strip.
-/

namespace SolidGridHam

open Finset Classical

def Inter (V : Finset Pt) (F : Finset Edge) (e : Edge) : Prop :=
  IsEdge V e ∧ e ∉ F ∧ ¬ Conn F e.p e.q

/-! ## Local count -/

-- Corner pairs: `ab ad ak bd bk dk` say whether the corners are in one class.
--
def triOK (ab ad ak bd bk dk : Bool) : Bool :=
  -- every triangle of corners is transitive
  ((ab && bd) <= ad) && ((ad && bd) <= ab) && ((ab && ad) <= bd) &&
  ((ab && bk) <= ak) && ((ak && bk) <= ab) && ((ab && ak) <= bk) &&
  ((ad && dk) <= ak) && ((ak && dk) <= ad) && ((ad && ak) <= dk) &&
  ((bd && dk) <= bk) && ((bk && dk) <= bd) && ((bd && bk) <= dk)

def bI (b : Bool) : ℕ := if b then 1 else 0

theorem inter_local : ∀ (mb mt ml mr ab ad ak bd bk dk : Bool),
    triOK ab ad ak bd bk dk = true →
    -- dark sides join corners of one class
    (mb ≤ ab) → (mt ≤ dk) → (ml ≤ ad) → (mr ≤ bk) →
    -- no Type III cell
    ((mb && mt && !ml && !mr) ≤ ad) → ((ml && mr && !mb && !mt) ≤ ab) →
    -- an inter side has a dark neighbouring side
    ((!mb && !ab) ≤ (ml || mr)) → ((!mt && !dk) ≤ (ml || mr)) →
    ((!ml && !ad) ≤ (mb || mt)) → ((!mr && !bk) ≤ (mb || mt)) →
    (bI (!mb && !ab) + bI (!mt && !dk) + bI (!ml && !ad) + bI (!mr && !bk)) % 2 = 0 := by
  decide

lemma bI_dec (p : Prop) [Decidable p] : bI (decide p) = if p then 1 else 0 := by
  by_cases h : p <;> simp [bI, h]

-- Number of inter sides of a cell.
--
noncomputable def interCount (V : Finset Pt) (F : Finset Edge) (w : Pt) : ℕ :=
  (if Inter V F (bot w) then 1 else 0) + (if Inter V F (top w) then 1 else 0) +
    (if Inter V F (lft w) then 1 else 0) + (if Inter V F (rgt w) then 1 else 0)

section count

variable {V : Finset Pt} {F : Finset Edge} (hF : Deg2 V F) (hT : NoTypeIII V F)
include hF hT

-- An inter side has a dark neighbouring side (via the border of one end's class).
--
lemma inter_dark_lat {w : Pt} (hw : IsCell V w) (s : Side) (h : Inter V F (sideEdge w s)) :
    sideEdge w (latA s) ∈ F ∨ sideEdge w (latB s) ∈ F := by
  set e := sideEdge w s
  have hB : Border V F (cls V F e.p) :=
    ⟨Finset.filter_subset _ _, fun u hu v hv => closed_cls hF.1 e.p u hu v hv⟩
  apply cut_has_dark_lat hF hB hT hw s
  unfold Cut
  have hp : e.p ∈ cls V F e.p := mem_cls_self h.1.1
  have hq : e.q ∉ cls V F e.p := by
    simp only [cls, Finset.mem_filter, not_and]; exact fun _ => h.2.2
  tauto

theorem interCount_even {w : Pt} (hw : IsCell V w) : interCount V F w % 2 = 0 := by
  obtain ⟨x, y⟩ := w
  have hw' := hw
  obtain ⟨va, vb, vd, vk⟩ := hw
  set a : Pt := (x, y)
  set b : Pt := (x + 1, y)
  set d : Pt := (x, y + 1)
  set k : Pt := (x + 1, y + 1)
  have key := inter_local (decide (bot (x, y) ∈ F)) (decide (top (x, y) ∈ F))
    (decide (lft (x, y) ∈ F)) (decide (rgt (x, y) ∈ F))
    (decide (Conn F a b)) (decide (Conn F a d)) (decide (Conn F a k)) (decide (Conn F b d))
    (decide (Conn F b k)) (decide (Conn F d k))
  -- Transitivity of the corner relation.
  have tri : triOK (decide (Conn F a b)) (decide (Conn F a d)) (decide (Conn F a k))
      (decide (Conn F b d)) (decide (Conn F b k)) (decide (Conn F d k)) = true := by
    unfold triOK
    simp only [Bool.and_eq_true, Bool.le_iff_imp, decide_eq_true_eq]
    refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩ <;>
      intro h <;> obtain ⟨h1, h2⟩ := h
    all_goals first
      | exact h1.trans h2 | exact h1.trans h2.symm | exact h1.symm.trans h2
  have dk1 : ∀ (e : Edge) (u v : Pt), Ends e u v → (decide (e ∈ F) ≤ decide (Conn F u v)) := by
    intro e u v he
    simp only [Bool.le_iff_imp, decide_eq_true_eq]
    exact fun h => he.conn h
  have eb : Ends (bot (x, y)) a b := Or.inl ⟨rfl, rfl⟩
  have et : Ends (top (x, y)) d k := Or.inl ⟨rfl, rfl⟩
  have el : Ends (lft (x, y)) a d := Or.inl ⟨rfl, rfl⟩
  have er : Ends (rgt (x, y)) b k := Or.inl ⟨rfl, rfl⟩
  -- No Type III cell.
  have t1 : (decide (bot (x, y) ∈ F) && decide (top (x, y) ∈ F) && !decide (lft (x, y) ∈ F) &&
      !decide (rgt (x, y) ∈ F)) ≤ decide (Conn F a d) := by
    simp only [Bool.le_iff_imp, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq,
      decide_eq_false_iff_not]
    rintro ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩
    have := hT (x, y) hw' .t h1 h2 h3 h4
    simpa [back1, front1] using this
  have t2 : (decide (lft (x, y) ∈ F) && decide (rgt (x, y) ∈ F) && !decide (bot (x, y) ∈ F) &&
      !decide (top (x, y) ∈ F)) ≤ decide (Conn F a b) := by
    simp only [Bool.le_iff_imp, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq,
      decide_eq_false_iff_not]
    rintro ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩
    have := hT (x, y) hw' .r h1 h2 h3 h4
    simpa [back1, front1] using this
  -- Inter sides have a dark neighbour.
  have iE : ∀ s : Side, IsEdge V (sideEdge (x, y) s) := by
    intro s; cases s <;> simp [IsEdge, sideEdge, bot, top, lft, rgt, Edge.q] <;>
      exact ⟨by assumption, by assumption⟩
  have nl : ∀ (s : Side) (u v : Pt), Ends (sideEdge (x, y) s) u v →
      ((!decide (sideEdge (x, y) s ∈ F) && !decide (Conn F u v)) ≤
        (decide (sideEdge (x, y) (latA s) ∈ F) || decide (sideEdge (x, y) (latB s) ∈ F))) := by
    intro s u v he
    simp only [Bool.le_iff_imp, Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not,
      Bool.or_eq_true, decide_eq_true_eq]
    rintro ⟨h1, h2⟩
    exact inter_dark_lat hF hT hw' s ⟨iE s, h1, fun h => h2 ((he.conn_iff F).1 h)⟩
  have hcount := key tri (dk1 _ _ _ eb) (dk1 _ _ _ et) (dk1 _ _ _ el) (dk1 _ _ _ er) t1 t2
    (nl .b a b eb) (nl .t d k et) (nl .l a d el) (nl .r b k er)
  -- Translate back.
  have tr : ∀ (e : Edge) (u v : Pt), Ends e u v → IsEdge V e →
      bI (!decide (e ∈ F) && !decide (Conn F u v)) = if Inter V F e then 1 else 0 := by
    intro e u v he hE
    unfold Inter
    rw [he.conn_iff]
    by_cases h1 : e ∈ F <;> by_cases h2 : Conn F u v <;> simp [bI, h1, h2, hE]
  unfold interCount
  rw [← tr _ _ _ eb (iE .b), ← tr _ _ _ et (iE .t), ← tr _ _ _ el (iE .l), ← tr _ _ _ er (iE .r)]
  exact hcount

end count

section countLocal

variable {V : Finset Pt} {F : Finset Edge} (hF : Deg2 V F)
include hF

-- An inter side has a dark neighbouring side (via the border of one end's class).
--
lemma inter_dark_lat_l {w : Pt} (hw : IsCell V w) (s : Side) (h : Inter V F (sideEdge w s))
    (hTr : IsCell V (nb w s) → NotTypeIII V F (nb w s)) :
    sideEdge w (latA s) ∈ F ∨ sideEdge w (latB s) ∈ F := by
  set e := sideEdge w s
  have hB : Border V F (cls V F e.p) :=
    ⟨Finset.filter_subset _ _, fun u hu v hv => closed_cls hF.1 e.p u hu v hv⟩
  apply cut_has_dark_lat_l hF hB hw s _ hTr
  unfold Cut
  have hp : e.p ∈ cls V F e.p := mem_cls_self h.1.1
  have hq : e.q ∉ cls V F e.p := by
    simp only [cls, Finset.mem_filter, not_and]; exact fun _ => h.2.2
  tauto

theorem interCount_even_l {w : Pt} (hw : IsCell V w) (hTw : NotTypeIII V F w)
    (hTn : ∀ s, Inter V F (sideEdge w s) → IsCell V (nb w s) → NotTypeIII V F (nb w s)) :
    interCount V F w % 2 = 0 := by
  obtain ⟨x, y⟩ := w
  have hw' := hw
  obtain ⟨va, vb, vd, vk⟩ := hw
  set a : Pt := (x, y)
  set b : Pt := (x + 1, y)
  set d : Pt := (x, y + 1)
  set k : Pt := (x + 1, y + 1)
  have key := inter_local (decide (bot (x, y) ∈ F)) (decide (top (x, y) ∈ F))
    (decide (lft (x, y) ∈ F)) (decide (rgt (x, y) ∈ F))
    (decide (Conn F a b)) (decide (Conn F a d)) (decide (Conn F a k)) (decide (Conn F b d))
    (decide (Conn F b k)) (decide (Conn F d k))
  -- Transitivity of the corner relation.
  have tri : triOK (decide (Conn F a b)) (decide (Conn F a d)) (decide (Conn F a k))
      (decide (Conn F b d)) (decide (Conn F b k)) (decide (Conn F d k)) = true := by
    unfold triOK
    simp only [Bool.and_eq_true, Bool.le_iff_imp, decide_eq_true_eq]
    refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩ <;>
      intro h <;> obtain ⟨h1, h2⟩ := h
    all_goals first
      | exact h1.trans h2 | exact h1.trans h2.symm | exact h1.symm.trans h2
  have dk1 : ∀ (e : Edge) (u v : Pt), Ends e u v → (decide (e ∈ F) ≤ decide (Conn F u v)) := by
    intro e u v he
    simp only [Bool.le_iff_imp, decide_eq_true_eq]
    exact fun h => he.conn h
  have eb : Ends (bot (x, y)) a b := Or.inl ⟨rfl, rfl⟩
  have et : Ends (top (x, y)) d k := Or.inl ⟨rfl, rfl⟩
  have el : Ends (lft (x, y)) a d := Or.inl ⟨rfl, rfl⟩
  have er : Ends (rgt (x, y)) b k := Or.inl ⟨rfl, rfl⟩
  -- No Type III cell.
  have t1 : (decide (bot (x, y) ∈ F) && decide (top (x, y) ∈ F) && !decide (lft (x, y) ∈ F) &&
      !decide (rgt (x, y) ∈ F)) ≤ decide (Conn F a d) := by
    simp only [Bool.le_iff_imp, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq,
      decide_eq_false_iff_not]
    rintro ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩
    have := hTw .t h1 h2 h3 h4
    simpa [back1, front1] using this
  have t2 : (decide (lft (x, y) ∈ F) && decide (rgt (x, y) ∈ F) && !decide (bot (x, y) ∈ F) &&
      !decide (top (x, y) ∈ F)) ≤ decide (Conn F a b) := by
    simp only [Bool.le_iff_imp, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq,
      decide_eq_false_iff_not]
    rintro ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩
    have := hTw .r h1 h2 h3 h4
    simpa [back1, front1] using this
  -- Inter sides have a dark neighbour.
  have iE : ∀ s : Side, IsEdge V (sideEdge (x, y) s) := by
    intro s; cases s <;> simp [IsEdge, sideEdge, bot, top, lft, rgt, Edge.q] <;>
      exact ⟨by assumption, by assumption⟩
  have nl : ∀ (s : Side) (u v : Pt), Ends (sideEdge (x, y) s) u v →
      ((!decide (sideEdge (x, y) s ∈ F) && !decide (Conn F u v)) ≤
        (decide (sideEdge (x, y) (latA s) ∈ F) || decide (sideEdge (x, y) (latB s) ∈ F))) := by
    intro s u v he
    simp only [Bool.le_iff_imp, Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not,
      Bool.or_eq_true, decide_eq_true_eq]
    rintro ⟨h1, h2⟩
    have hI : Inter V F (sideEdge (x, y) s) := ⟨iE s, h1, fun h => h2 ((he.conn_iff F).1 h)⟩
    exact inter_dark_lat_l hF hw' s hI (hTn s hI)
  have hcount := key tri (dk1 _ _ _ eb) (dk1 _ _ _ et) (dk1 _ _ _ el) (dk1 _ _ _ er) t1 t2
    (nl .b a b eb) (nl .t d k et) (nl .l a d el) (nl .r b k er)
  -- Translate back.
  have tr : ∀ (e : Edge) (u v : Pt), Ends e u v → IsEdge V e →
      bI (!decide (e ∈ F) && !decide (Conn F u v)) = if Inter V F e then 1 else 0 := by
    intro e u v he hE
    unfold Inter
    rw [he.conn_iff]
    by_cases h1 : e ∈ F <;> by_cases h2 : Conn F u v <;> simp [bI, h1, h2, hE]
  unfold interCount
  rw [← tr _ _ _ eb (iE .b), ← tr _ _ _ et (iE .t), ← tr _ _ _ el (iE .l), ← tr _ _ _ er (iE .r)]
  exact hcount

end countLocal

/-! ## Potentials of weights on graph edges vanish off the graph's cells -/

section potzero

variable {V : Finset Pt} {E : Finset Edge} {w : Edge → ℤ}
  (hS : Supp E w) (hb : Balanced w) (hE : ∀ e ∈ E, e.p ∈ V ∧ e.q ∈ V)
include hS hb hE

omit hb in
lemma w_zero_at_missing {a : Pt} (ha : a ∉ V) {e : Edge} (h : e.p = a ∨ e.q = a) : w e = 0 := by
  apply hS
  intro he
  rcases h with h | h
  · exact ha (h ▸ (hE e he).1)
  · exact ha (h ▸ (hE e he).2)

lemma pot_around_missing {a c : Pt} (ha : a ∉ V) (hc : Around a c) : pot E w c = pot E w a := by
  apply pot_around hS hb _ hc
  obtain ⟨x, y⟩ := a
  refine ⟨w_zero_at_missing hS hE ha (Or.inl rfl), w_zero_at_missing hS hE ha (Or.inl rfl),
    w_zero_at_missing hS hE ha (Or.inr ?_), w_zero_at_missing hS hE ha (Or.inr ?_)⟩ <;>
    simp [eL, eD, Edge.q]

lemma pot_missing_chain {a b : Pt} (h : Relation.ReflTransGen (MissAdj V) a b) :
    pot E w a = pot E w b := by
  induction h with
  | refl => rfl
  | @tail b' c' _ hbc ih =>
    obtain ⟨hb', hc', h1, h2⟩ := hbc
    let m : Pt := (max b'.1 c'.1 - 1, max b'.2 c'.2 - 1)
    have mb : Around b' m := by
      constructor <;> simp only [m] <;> rw [abs_le] at * <;> omega
    have mc : Around c' m := by
      constructor <;> simp only [m] <;> rw [abs_le] at * <;> omega
    rw [ih, ← pot_around_missing hS hb hE hb' mb, pot_around_missing hS hb hE hc' mc]

theorem pot_zero_off_cells (hs : Solid V) {c : Pt} (hc : ¬ IsCell V c) : pot E w c = 0 := by
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
  obtain ⟨b, hab, hb'⟩ := hs a ha
  rw [pot_around_missing hS hb hE ha hac, pot_missing_chain hS hb hE hab]
  exact pot_eq_zero_of_left (B := b.1) (fun e he => hb' _ (hE e he).1) b le_rfl

end potzero

/-! ## Edges are determined by their ends -/

lemma Edge.q_sum (e : Edge) : e.q.1 + e.q.2 = e.p.1 + e.p.2 + 1 := by
  obtain ⟨d, p1, p2⟩ := e; cases d <;> simp [Edge.q] <;> ring

lemma Edge.ext_pq {e e' : Edge} (h1 : e.p = e'.p) (h2 : e.q = e'.q) : e = e' := by
  obtain ⟨d, p⟩ := e
  obtain ⟨d', p'⟩ := e'
  simp only at h1
  subst h1
  cases d <;> cases d' <;> simp_all [Edge.q]

lemma Edge.eq_of_ends {e e' : Edge} {u v : Pt} (h : Ends e u v) (h' : Ends e' u v) : e = e' := by
  have s1 := Edge.q_sum e
  have s2 := Edge.q_sum e'
  rcases h with ⟨a1, a2⟩ | ⟨a1, a2⟩ <;> rcases h' with ⟨b1, b2⟩ | ⟨b1, b2⟩
  · exact Edge.ext_pq (a1.trans b1.symm) (a2.trans b2.symm)
  · rw [a1, a2] at s1; rw [b1, b2] at s2; omega
  · rw [a1, a2] at s1; rw [b1, b2] at s2; omega
  · exact Edge.ext_pq (a1.trans b1.symm) (a2.trans b2.symm)

lemma Adj.ends {G : Finset Edge} {u v : Pt} (h : Adj G u v) : ∃ e ∈ G, Ends e u v := by
  obtain ⟨e, he, h⟩ := h
  exact ⟨e, he, h⟩

/-! ## Closed chains cross an even-cornered edge set an even number of times -/

-- Number of sides of cell `c` in `B`.
--
def sidesIn (B : Finset Edge) (c : Pt) : ℕ := ind B (bot c) + ind B (top c) + ind B (lft c) + ind B (rgt c)

-- Number of steps of the chain `u, l` along edges of `B`.
--
noncomputable def crossL (B : Finset Edge) : Pt → List Pt → ℕ
  | _, [] => 0
  | u, v :: l => (if ∃ e ∈ B, Ends e u v then 1 else 0) + crossL B v l

lemma hi_eq_iff (e : Edge) (c : Pt) : e.hi = c ↔ (e = bot c ∨ e = lft c) := by
  obtain ⟨d, p⟩ := e
  cases d <;> simp [Edge.hi, bot, lft]

lemma lo_eq_iff (e : Edge) (c : Pt) : e.lo = c ↔ (e = top c ∨ e = rgt c) := by
  obtain ⟨d, p1, p2⟩ := e
  obtain ⟨x, y⟩ := c
  cases d <;> simp [Edge.lo, top, rgt] <;> omega

lemma bot_ne_lft (c : Pt) : bot c ≠ lft c := by simp [bot, lft]
lemma top_ne_rgt (c : Pt) : top c ≠ rgt c := by simp [top, rgt]

lemma sum_hi_lo (B : Finset Edge) (W : Pt → ℤ) (T : Finset Pt)
    (hT : ∀ e ∈ B, e.hi ∈ T ∧ e.lo ∈ T) :
    ∑ e ∈ B, (W e.hi + W e.lo) = ∑ c ∈ T, W c * (sidesIn B c : ℤ) := by
  have h1 : ∀ e ∈ B, W e.hi + W e.lo =
      ∑ c ∈ T, W c * ((if e.hi = c then 1 else 0) + (if e.lo = c then 1 else 0)) := by
    intro e he
    simp only [mul_add, mul_ite, mul_one, mul_zero, Finset.sum_add_distrib]
    rw [Finset.sum_ite_eq, Finset.sum_ite_eq, ite_eq_left (hT e he).1, ite_eq_left (hT e he).2]
  rw [Finset.sum_congr rfl h1, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro c _
  rw [← Finset.mul_sum]
  congr 1
  rw [Finset.sum_add_distrib]
  simp only [hi_eq_iff, lo_eq_iff]
  unfold sidesIn ind
  have e1 : ∑ e ∈ B, (if e = bot c ∨ e = lft c then (1 : ℤ) else 0) =
      (if bot c ∈ B then 1 else 0) + (if lft c ∈ B then 1 else 0) := by
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
    have : B.filter (fun e => e = bot c ∨ e = lft c) =
        (B.filter (· = bot c)) ∪ (B.filter (· = lft c)) := by
      ext e; simp [Finset.mem_filter]; tauto
    rw [this, Finset.card_union_of_disjoint]
    · rw [Finset.filter_eq', Finset.filter_eq']
      split_ifs <;> simp
    · rw [Finset.disjoint_filter]; intro e _ h1 h2; exact bot_ne_lft c (h1 ▸ h2)
  have e2 : ∑ e ∈ B, (if e = top c ∨ e = rgt c then (1 : ℤ) else 0) =
      (if top c ∈ B then 1 else 0) + (if rgt c ∈ B then 1 else 0) := by
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
    have : B.filter (fun e => e = top c ∨ e = rgt c) =
        (B.filter (· = top c)) ∪ (B.filter (· = rgt c)) := by
      ext e; simp [Finset.mem_filter]; tauto
    rw [this, Finset.card_union_of_disjoint]
    · rw [Finset.filter_eq', Finset.filter_eq']
      split_ifs <;> simp
    · rw [Finset.disjoint_filter]; intro e _ h1 h2; exact top_ne_rgt c (h1 ▸ h2)
  rw [e1, e2]
  push_cast
  split_ifs <;> simp

/-! ## Chains of graph edges -/

section chains

variable {G : Finset Edge}

lemma flowL_mem {u : Pt} {l : List Pt} (hc : List.IsChain (Adj G) (u :: l)) {e : Edge}
    (h : flowL u l e ≠ 0) : e ∈ G := by
  induction l generalizing u with
  | nil => simp [flowL] at h
  | cons v l ih =>
    rw [List.isChain_cons_cons] at hc
    simp only [flowL] at h
    by_cases h1 : stepFlow u v e = 0
    · rw [h1, zero_add] at h; exact ih hc.2 h
    · obtain ⟨e0, he0, h0⟩ := hc.1.ends
      have : e = e0 := Edge.eq_of_ends (stepFlow_ne_zero h1) h0
      rw [this]; exact he0

lemma stepFlow_sum {u v : Pt} (h : Adj G u v) (B : Finset Edge) :
    ∃ tf : ℤ, ∑ e ∈ B, stepFlow u v e = (if ∃ e ∈ B, Ends e u v then 1 else 0) + 2 * tf := by
  obtain ⟨e0, _, h0⟩ := h.ends
  have hz : ∀ e, e ≠ e0 → stepFlow u v e = 0 := by
    intro e he
    by_contra hne
    exact he (Edge.eq_of_ends (stepFlow_ne_zero hne) h0)
  have huv : u ≠ v := by
    intro he; have := h.unit; rw [he] at this; simp [Unit] at this
  have hv : stepFlow u v e0 = 1 ∨ stepFlow u v e0 = -1 := by
    unfold stepFlow
    rcases h0 with ⟨a1, a2⟩ | ⟨a1, a2⟩
    · left
      rw [ite_eq_left ⟨a1, a2⟩, ite_eq_right (fun h' => huv (a1.symm.trans h'.1))]; ring
    · right
      rw [ite_eq_right (fun h' => huv (h'.1.symm.trans a1)), ite_eq_left ⟨a1, a2⟩]; ring
  have hsum : ∑ e ∈ B, stepFlow u v e = if e0 ∈ B then stepFlow u v e0 else 0 := by
    rw [← Finset.sum_ite_eq' B e0 (fun e => stepFlow u v e)]
    apply Finset.sum_congr rfl
    intro e _
    by_cases he : e = e0
    · simp [he]
    · simp [he, hz e he]
  have hex : (∃ e ∈ B, Ends e u v) ↔ e0 ∈ B := by
    constructor
    · rintro ⟨e, he, h1⟩; rwa [Edge.eq_of_ends h1 h0] at he
    · exact fun h => ⟨e0, h, h0⟩
  rw [hsum]
  by_cases hB : e0 ∈ B
  · rw [ite_eq_left hB, ite_eq_left (hex.2 hB)]
    rcases hv with hv | hv
    · exact ⟨0, by rw [hv]; ring⟩
    · exact ⟨-1, by rw [hv]; ring⟩
  · rw [ite_eq_right hB, ite_eq_right (fun h => hB (hex.1 h))]; exact ⟨0, by ring⟩

lemma flow_cross_parity (B : Finset Edge) {u : Pt} {l : List Pt}
    (hc : List.IsChain (Adj G) (u :: l)) :
    ∃ tf : ℤ, ∑ e ∈ B, flowL u l e = (crossL B u l : ℤ) + 2 * tf := by
  induction l generalizing u with
  | nil => exact ⟨0, by simp [flowL, crossL]⟩
  | cons v l ih =>
    rw [List.isChain_cons_cons] at hc
    obtain ⟨t1, h1⟩ := stepFlow_sum hc.1 B
    obtain ⟨t2, h2⟩ := ih hc.2
    refine ⟨t1 + t2, ?_⟩
    simp only [flowL, Finset.sum_add_distrib, crossL, h1, h2]
    push_cast
    split_ifs <;> ring

-- **Closed chains cross evenly.** If every cell of the graph has an even number of sides in
-- `B`, a closed chain along graph edges uses edges of `B` an even number of times.
--
theorem closed_chain_even {V : Finset Pt} (hs : Solid V) (hG : ∀ e ∈ G, e.p ∈ V ∧ e.q ∈ V)
    (B : Finset Edge) (heven : ∀ c, IsCell V c → sidesIn B c % 2 = 0)
    {u : Pt} {l : List Pt} (hc : List.IsChain (Adj G) (u :: l))
    (hl : (u :: l).getLast (by simp) = u) : crossL B u l % 2 = 0 := by
  set f := flowL u l
  have hunit : List.IsChain Unit (u :: l) := hc.imp (fun _ _ h => h.unit)
  have hout : ∀ x, outflow f x = 0 := by
    intro x; rw [outflow_flowL u l hunit x, hl]; ring
  have hS : Supp G (rot f) := by
    intro e he
    have : f e = 0 := by by_contra h; exact he (flowL_mem hc h)
    unfold rot; cases e.d <;> simp [this]
  have hb := rot_balanced hout
  set W := pot G (rot f)
  have hj : ∀ e, W e.hi - W e.lo = rot f e := pot_jump hS hb
  have hz : ∀ c, ¬ IsCell V c → W c = 0 := fun c hc' => pot_zero_off_cells hS hb hG hs hc'
  -- `Σ_B (W hi + W lo)` is even.
  set T := B.image Edge.hi ∪ B.image Edge.lo
  have hT : ∀ e ∈ B, e.hi ∈ T ∧ e.lo ∈ T := fun e he =>
    ⟨Finset.mem_union_left _ (Finset.mem_image_of_mem _ he),
      Finset.mem_union_right _ (Finset.mem_image_of_mem _ he)⟩
  have hev : Even (∑ e ∈ B, (W e.hi + W e.lo)) := by
    rw [sum_hi_lo B W T hT]
    apply Finset.even_sum
    intro c _
    by_cases hcell : IsCell V c
    · have := heven c hcell
      obtain ⟨r, hr⟩ : ∃ r, sidesIn B c = 2 * r := ⟨sidesIn B c / 2, by omega⟩
      rw [hr]; push_cast; exact ⟨W c * r, by ring⟩
    · rw [hz c hcell]; simp
  -- Hence `Σ_B rot f` and `Σ_B f` are even.
  have hrot : Even (∑ e ∈ B, rot f e) := by
    have e1 : ∑ e ∈ B, rot f e = ∑ e ∈ B, (W e.hi + W e.lo) - 2 * ∑ e ∈ B, W e.lo := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl; intro e _; rw [← hj]; ring
    rw [e1]; obtain ⟨r, hr⟩ := hev; exact ⟨r - ∑ e ∈ B, W e.lo, by rw [hr]; ring⟩
  have hf : Even (∑ e ∈ B, f e) := by
    have e2 : ∑ e ∈ B, f e = ∑ e ∈ B, rot f e + 2 * ∑ e ∈ B.filter (fun e => e.d = .v), f e := by
      rw [Finset.sum_filter, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl; intro e _
      unfold rot; cases e.d <;> simp; ring
    rw [e2]; obtain ⟨r, hr⟩ := hrot; exact ⟨r + ∑ e ∈ B.filter (fun e => e.d = .v), f e, by rw [hr]; ring⟩
  obtain ⟨tf, ht⟩ := flow_cross_parity B hc
  obtain ⟨r, hr⟩ := hf
  have : (crossL B u l : ℤ) = 2 * (r - tf) := by rw [hr] at ht; linarith
  omega

end chains

/-! ## The graph's edges, and the separation theorem -/

-- All edges of the grid graph on `V`.
--
noncomputable def GE (V : Finset Pt) : Finset Edge :=
  (V.biUnion (fun v => ({eR v, eU v} : Finset Edge))).filter (IsEdge V)

lemma mem_GE {V : Finset Pt} {e : Edge} : e ∈ GE V ↔ IsEdge V e := by
  unfold GE
  rw [Finset.mem_filter]
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨Finset.mem_biUnion.2 ⟨e.p, h.1, ?_⟩, h⟩
    obtain ⟨d, p⟩ := e
    cases d <;> simp [eR, eU]

lemma GE_inside (V : Finset Pt) : ∀ e ∈ GE V, e.p ∈ V ∧ e.q ∈ V := fun _ he => mem_GE.1 he

lemma crossL_append (B : Finset Edge) (u : Pt) (l : List Pt) (d : Pt) :
    crossL B u (l ++ [d]) =
      crossL B u l + (if ∃ e ∈ B, Ends e ((u :: l).getLast (by simp)) d then 1 else 0) := by
  induction l generalizing u with
  | nil =>
    simp only [List.nil_append, crossL, List.getLast_singleton]
    by_cases h : ∃ e ∈ B, Ends e u d <;> simp only [h, ite_true, ite_false]
  | cons v l ih =>
    simp only [List.cons_append, crossL, ih v, List.getLast_cons_cons]
    by_cases h : ∃ e ∈ B, Ends e u v <;>
      by_cases h' : ∃ e ∈ B, Ends e ((v :: l).getLast (by simp)) d <;>
      simp only [h, h', ite_true, ite_false] <;> ring

lemma isChain_append {R : Pt → Pt → Prop} {u : Pt} {l : List Pt} {d : Pt}
    (h : List.IsChain R (u :: l)) (hd : R ((u :: l).getLast (by simp)) d) :
    List.IsChain R (u :: (l ++ [d])) := by
  induction l generalizing u with
  | nil => simpa using hd
  | cons v l ih =>
    rw [List.isChain_cons_cons] at h
    rw [List.cons_append, List.isChain_cons_cons]
    exact ⟨h.1, ih h.2 (by simpa using hd)⟩

section sep

variable {V : Finset Pt} (B : Finset Edge)

-- Steps on (vertex, parity) pairs.
--
def PStep (V : Finset Pt) (B : Finset Edge) (x y : Pt × Bool) : Prop :=
  Adj (GE V) x.1 y.1 ∧ y.2 = (x.2 ^^ decide (∃ e ∈ B, Ends e x.1 y.1))

lemma ends_swap_iff {u v : Pt} : (∃ e ∈ B, Ends e u v) ↔ (∃ e ∈ B, Ends e v u) :=
  ⟨fun ⟨e, he, h⟩ => ⟨e, he, h.swap⟩, fun ⟨e, he, h⟩ => ⟨e, he, h.swap⟩⟩

lemma PStep.symm {x y : Pt × Bool} (h : PStep V B x y) : PStep V B y x := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨h1.symm, ?_⟩
  rw [h2, show decide (∃ e ∈ B, Ends e y.1 x.1) = decide (∃ e ∈ B, Ends e x.1 y.1) from
    by simp only [ends_swap_iff B]]
  cases x.2 <;> cases decide (∃ e ∈ B, Ends e x.1 y.1) <;> rfl

lemma PStep.neg {x y : Pt × Bool} (h : PStep V B x y) : PStep V B (x.1, !x.2) (y.1, !y.2) := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨h1, ?_⟩
  simp only [h2]
  cases x.2 <;> cases decide (∃ e ∈ B, Ends e x.1 y.1) <;> rfl

lemma preach_symm {x y : Pt × Bool} (h : Relation.ReflTransGen (PStep V B) x y) :
    Relation.ReflTransGen (PStep V B) y x := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih => exact Relation.ReflTransGen.head (hbc.symm B) ih

lemma preach_neg {x y : Pt × Bool} (h : Relation.ReflTransGen (PStep V B) x y) :
    Relation.ReflTransGen (PStep V B) (x.1, !x.2) (y.1, !y.2) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih => exact ih.tail (hbc.neg B)

lemma preach_chain {a c : Pt} {b b' : Bool}
    (h : Relation.ReflTransGen (PStep V B) (a, b) (c, b')) :
    ∃ l, List.IsChain (Adj (GE V)) (a :: l) ∧ (a :: l).getLast (by simp) = c ∧
      (crossL B a l % 2 = if b = b' then 0 else 1) := by
  generalize hx : ((a, b) : Pt × Bool) = x at h
  generalize hy : ((c, b') : Pt × Bool) = y at h
  induction h generalizing c b' with
  | refl =>
    subst hx; simp only [Prod.mk.injEq] at hy; obtain ⟨rfl, rfl⟩ := hy
    exact ⟨[], List.IsChain.singleton _, rfl, by simp [crossL]⟩
  | @tail y' z _ hyz ih =>
    subst hx hy
    obtain ⟨l, hl, hlast, hpar⟩ := ih rfl
    obtain ⟨h1, h2⟩ := hyz
    refine ⟨l ++ [c], isChain_append hl (by rw [hlast]; exact h1), by simp, ?_⟩
    rw [crossL_append, hlast]
    simp only at h2
    rw [h2]
    have key : ∀ (X : ℕ) (b c tf : Bool), X % 2 = (if b = c then 0 else 1) →
        (X + (if tf = true then 1 else 0)) % 2 = (if b = (c ^^ tf) then 0 else 1) := by
      intro X b c tf h
      cases b <;> cases c <;> cases tf <;> simp at h ⊢ <;> omega
    have := key (crossL B a l) b y'.2 (decide (∃ e ∈ B, Ends e y'.1 c)) hpar
    simpa only [decide_eq_true_eq] using this

lemma lift_conn {a z : Pt} (h : Conn (GE V) a z) (b : Bool) :
    ∃ b', Relation.ReflTransGen (PStep V B) (a, b) (z, b') := by
  induction h with
  | refl => exact ⟨b, Relation.ReflTransGen.refl⟩
  | @tail y w _ hyw ih =>
    obtain ⟨b1, h1⟩ := ih
    exact ⟨b1 ^^ decide (∃ e ∈ B, Ends e y w), h1.tail ⟨hyw, rfl⟩⟩

variable (hs : Solid V) (heven : ∀ c, IsCell V c → sidesIn B c % 2 = 0)
include hs heven

lemma no_odd_return {a : Pt} {b : Bool} :
    ¬ Relation.ReflTransGen (PStep V B) (a, b) (a, !b) := by
  intro h
  obtain ⟨l, hl, hlast, hpar⟩ := preach_chain B h
  have := closed_chain_even hs (GE_inside V) B heven hl hlast
  cases b <;> simp at hpar <;> omega

lemma bit_unique {x0 z : Pt} {b1 b2 : Bool}
    (h1 : Relation.ReflTransGen (PStep V B) (x0, false) (z, b1))
    (h2 : Relation.ReflTransGen (PStep V B) (x0, false) (z, b2)) : b1 = b2 := by
  by_contra hne
  have hb : b2 = !b1 := by cases b1 <;> cases b2 <;> simp_all
  have h3 := preach_neg B (preach_symm B h2)
  simp only [hb, Bool.not_not] at h3
  exact no_odd_return B hs heven (h1.trans h3)

-- **Separation.** If every cell of the graph has an even number of sides in `B`, the graph is
-- connected, and `B` avoids `F`, then some border of `F` has exactly `B` as its cut edges.
--
theorem separation {F : Finset Edge} (hFV : Inside V F) (hBF : ∀ e ∈ B, e ∉ F)
    (x0 : Pt) (hconn : ∀ z ∈ V, Conn (GE V) x0 z) :
    ∃ P : Finset Pt, Border V F P ∧ ∀ e, IsEdge V e → (Cut P e ↔ e ∈ B) := by
  let P := V.filter (fun z => Relation.ReflTransGen (PStep V B) (x0, false) (z, false))
  have bitOf : ∀ z ∈ V, ∃ b, Relation.ReflTransGen (PStep V B) (x0, false) (z, b) :=
    fun z hz => lift_conn B (hconn z hz) false
  have memP : ∀ z ∈ V, ∀ b, Relation.ReflTransGen (PStep V B) (x0, false) (z, b) →
      (z ∈ P ↔ b = false) := by
    intro z hz b hb
    simp only [P, Finset.mem_filter]
    constructor
    · rintro ⟨_, h⟩; exact bit_unique B hs heven hb h
    · rintro rfl; exact ⟨hz, hb⟩
  have step : ∀ e, IsEdge V e → ∀ b, Relation.ReflTransGen (PStep V B) (x0, false) (e.p, b) →
      Relation.ReflTransGen (PStep V B) (x0, false) (e.q, b ^^ decide (e ∈ B)) := by
    intro e he b hb
    have hadj : Adj (GE V) e.p e.q := ⟨e, mem_GE.2 he, Or.inl ⟨rfl, rfl⟩⟩
    have hiff : (∃ e' ∈ B, Ends e' e.p e.q) ↔ e ∈ B :=
      ⟨fun ⟨e', he', h⟩ => by rwa [Edge.eq_of_ends h (Or.inl ⟨rfl, rfl⟩)] at he',
        fun h => ⟨e, h, Or.inl ⟨rfl, rfl⟩⟩⟩
    have := hb.tail (show PStep V B (e.p, b) (e.q, b ^^ decide (∃ e' ∈ B, Ends e' e.p e.q)) from
      ⟨hadj, rfl⟩)
    simpa only [hiff] using this
  refine ⟨P, ⟨Finset.filter_subset _ _, ?_⟩, ?_⟩
  · intro x hx y hxy
    obtain ⟨f, hf, hfe⟩ := hxy
    have hxV : x ∈ V := Finset.mem_of_mem_filter _ hx
    obtain ⟨b, hb⟩ := bitOf x hxV
    have hb0 : b = false := (memP x hxV b hb).1 hx
    have hfB : f ∉ B := hBF f |> fun h hf' => h hf' hf
    rcases hfe with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have hfp : Relation.ReflTransGen (PStep V B) (x0, false) (f.p, b) := by rw [h1]; exact hb
      have := step f (hFV f hf) b hfp
      rw [h2] at this
      simp only [hfB, decide_false, Bool.xor_false] at this
      exact (memP y (by rw [← h2]; exact (hFV f hf).2) b this).2 hb0
    · have hfq : Relation.ReflTransGen (PStep V B) (x0, false) (f.q, b) := by rw [h2]; exact hb
      obtain ⟨b', hb'⟩ := bitOf f.p (hFV f hf).1
      have := step f (hFV f hf) b' hb'
      simp only [hfB, decide_false, Bool.xor_false] at this
      have : b' = b := bit_unique B hs heven this hfq
      rw [h1] at hb'
      exact (memP y (by rw [← h1]; exact (hFV f hf).1) b' hb').2 (this.trans hb0)
  · intro e he
    obtain ⟨b, hb⟩ := bitOf e.p he.1
    have hq := step e he b hb
    unfold Cut
    rw [memP e.p he.1 b hb, memP e.q he.2 _ hq]
    by_cases heB : e ∈ B <;> cases b <;> simp [heB]

end sep

/-! ## Which edges a strip flip changes -/

-- Number of the first `n` strip cells having `e` as a side.
--
noncomputable def nOn (c : Pt) (s : Side) (n : ℕ) (e : Edge) : ℕ :=
  ((Finset.range n).filter (fun j => e ∈ cellE (cellJ c s j))).card

lemma mem_flipCol (F : Finset Edge) (c : Pt) (s : Side) :
    ∀ n e, e ∈ flipCol F c s n ↔ (e ∈ F ↔ nOn c s n e % 2 = 0) := by
  intro n
  induction n generalizing F with
  | zero => intro e; simp [flipCol, nOn]
  | succ n ih =>
    intro e
    rw [flipCol_succ, ih, mem_flip_iff]
    unfold nOn
    rw [Finset.range_add_one, Finset.filter_insert]
    split_ifs with h
    · rw [Finset.card_insert_of_notMem (by simp)]
      set X := ((Finset.range n).filter (fun j => e ∈ cellE (cellJ c s j))).card
      have hx : ((X + 1) % 2 = 0) ↔ ¬ (X % 2 = 0) := by omega
      rw [hx]; tauto
    · tauto

lemma nOn_eq (c : Pt) (s : Side) (n : ℕ) (e : Edge) (J : Finset ℕ)
    (hJ : ∀ j, j < n → (e ∈ cellE (cellJ c s j) ↔ j ∈ J)) (hJn : ∀ j ∈ J, j < n) :
    nOn c s n e = J.card := by
  unfold nOn
  congr 1
  ext j
  simp only [Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨h1, h2⟩; exact (hJ j h1).1 h2
  · intro h; exact ⟨hJn j h, (hJ j (hJn j h)).2 h⟩

section flipfacts

variable (c : Pt) (s : Side)

lemma nOn_lat1 {n j : ℕ} (hj : j < n) : nOn c s n (lat1 (cellJ c s j) s) = 1 := by
  rw [nOn_eq c s n _ {j}]
  · simp
  · intro m _
    simp only [Finset.mem_singleton]
    constructor
    · intro h; by_contra hne; exact lat1_not_mem c s (j := j) (m := m) (Ne.symm hne) h
    · intro h; subst h; exact lat1_mem_self c s _
  · simpa using hj

lemma nOn_lat2 {n j : ℕ} (hj : j < n) : nOn c s n (lat2 (cellJ c s j) s) = 1 := by
  rw [nOn_eq c s n _ {j}]
  · simp
  · intro m _
    simp only [Finset.mem_singleton]
    constructor
    · intro h; by_contra hne; exact lat2_not_mem c s (j := j) (m := m) (Ne.symm hne) h
    · intro h; subst h; exact lat2_mem_self c s _
  · simpa using hj

lemma back_mem_zero : back c s ∈ cellE (cellJ c s 0) := by
  rw [cellJ_zero, cellE_frame c s]; simp

lemma nOn_back {n : ℕ} (hn : 1 ≤ n) : nOn c s n (back c s) = 1 := by
  rw [nOn_eq c s n _ {0}]
  · simp
  · intro m _
    simp only [Finset.mem_singleton]
    constructor
    · intro h; by_contra hne; exact back_not_mem c s hne h
    · rintro rfl; exact back_mem_zero c s
  · simp; omega

lemma nOn_front_last (m : ℕ) : nOn c s (m + 1) (front (cellJ c s m) s) = 1 := by
  rw [nOn_eq c s (m + 1) _ {m}]
  · simp
  · intro j hj
    simp only [Finset.mem_singleton]
    constructor
    · intro h; by_contra hne
      exact front_not_mem c s (j := m) (m := j) (Ne.symm hne) (by omega) h
    · rintro rfl; exact front_mem_self c s j
  · simp

lemma nOn_front_mid {n j : ℕ} (hj : j + 1 < n) : nOn c s n (front (cellJ c s j) s) = 2 := by
  rw [nOn_eq c s n _ {j, j + 1}]
  · rw [Finset.card_insert_of_notMem (by simp)]; simp
  · intro m _
    simp only [Finset.mem_insert, Finset.mem_singleton]
    constructor
    · intro h; by_contra hne; push Not at hne
      exact front_not_mem c s (j := j) (m := m) (Ne.symm hne.1) hne.2 h
    · rintro (rfl | rfl)
      · exact front_mem_self c s m
      · exact front_mem_next c s j
  · intro m hm; simp only [Finset.mem_insert, Finset.mem_singleton] at hm; omega

lemma nOn_zero {n : ℕ} {e : Edge} (h : ∀ j < n, e ∉ cellE (cellJ c s j)) : nOn c s n e = 0 := by
  rw [nOn_eq c s n _ ∅]
  · simp
  · intro j hj; simp [h j hj]
  · simp

end flipfacts

/-! ## Boundary chains -/

lemma mem_cellE_iff (e : Edge) (c : Pt) : e ∈ cellE c ↔ (e.hi = c ∨ e.lo = c) := by
  rw [hi_eq_iff, lo_eq_iff]; simp [cellE]; tauto

-- Two cells of the graph sharing an inter side.
--
def CAdj (V : Finset Pt) (F : Finset Edge) (c c' : Pt) : Prop :=
  IsCell V c ∧ IsCell V c' ∧ ∃ e, Inter V F e ∧ e ∈ cellE c ∧ e ∈ cellE c'

-- The chain of cells through `c0`, and its inter sides.
--
noncomputable def chainCells (V : Finset Pt) (F : Finset Edge) (c0 : Pt) : Finset Pt :=
  (cells V).filter (fun c => Relation.ReflTransGen (CAdj V F) c0 c)

noncomputable def EB (V : Finset Pt) (F : Finset Edge) (c0 : Pt) : Finset Edge :=
  (GE V).filter (fun e => Inter V F e ∧ ∃ c ∈ chainCells V F c0, e ∈ cellE c)

section chainsep

variable {V : Finset Pt} {F : Finset Edge}

lemma side_mem_cellE (c : Pt) (s : Side) : sideEdge c s ∈ cellE c := by
  cases s <;> simp [sideEdge, cellE]

-- A cell of the graph with an `EB` side is on the chain.
--
lemma on_chain_of_side {c0 w : Pt} {e : Edge} (hw : IsCell V w) (he : e ∈ cellE w)
    (hB : e ∈ EB V F c0) : w ∈ chainCells V F c0 := by
  simp only [EB, Finset.mem_filter] at hB
  obtain ⟨_, hI, c', hc', hec'⟩ := hB
  simp only [chainCells, Finset.mem_filter] at hc' ⊢
  refine ⟨mem_cells.2 hw, hc'.2.tail ⟨mem_cells.1 hc'.1, hw, e, hI, hec', he⟩⟩

lemma sidesIn_EB_even (hF : Deg2 V F) (hT : NoTypeIII V F) (c0 : Pt) :
    ∀ c, IsCell V c → sidesIn (EB V F c0) c % 2 = 0 := by
  intro c hc
  have hGE : ∀ s : Side, sideEdge c s ∈ GE V := by
    intro s; rw [mem_GE]
    obtain ⟨x, y⟩ := c
    obtain ⟨h1, h2, h3, h4⟩ := hc
    cases s <;> simp [IsEdge, sideEdge, bot, top, lft, rgt, Edge.q] <;>
      exact ⟨by assumption, by assumption⟩
  by_cases hin : c ∈ chainCells V F c0
  · -- On the chain: the `EB` sides are the inter sides.
    have hiff : ∀ s : Side, sideEdge c s ∈ EB V F c0 ↔ Inter V F (sideEdge c s) := by
      intro s
      simp only [EB, Finset.mem_filter]
      constructor
      · exact fun h => h.2.1
      · exact fun h => ⟨hGE s, h, c, hin, side_mem_cellE c s⟩
    have := interCount_even hF hT hc
    unfold sidesIn interCount ind at *
    have hb := hiff .b; have ht := hiff .t; have hl := hiff .l; have hr := hiff .r
    simp only [sideEdge] at hb ht hl hr
    simp only [hb, ht, hl, hr]
    exact this
  · -- Off the chain: no side is in `EB`.
    have hno : ∀ s : Side, sideEdge c s ∉ EB V F c0 := fun s h =>
      hin (on_chain_of_side hc (side_mem_cellE c s) h)
    unfold sidesIn ind
    have hb := hno .b; have ht := hno .t; have hl := hno .l; have hr := hno .r
    simp only [sideEdge] at hb ht hl hr
    simp [hb, ht, hl, hr]

-- **The created boundary is a border.** For a factor with no Type III cells on a solid
-- connected graph, the inter sides of the chain through `c0` are exactly the cut edges of a
-- border.
--
theorem chain_border (hs : Solid V) (hF : Deg2 V F) (hT : NoTypeIII V F) (x0 : Pt)
    (hconn : ∀ z ∈ V, Conn (GE V) x0 z) (c0 : Pt) :
    ∃ P : Finset Pt, Border V F P ∧ ∀ e, IsEdge V e → (Cut P e ↔ e ∈ EB V F c0) := by
  apply separation (EB V F c0) hs (sidesIn_EB_even hF hT c0) hF.1
  · intro e he
    simp only [EB, Finset.mem_filter] at he
    exact he.2.1.2.1
  · exact hconn

lemma side_mem_cellE_nb (c : Pt) (s : Side) : sideEdge c s ∈ cellE (nb c s) := by
  obtain ⟨x, y⟩ := c
  cases s <;> simp [sideEdge, cellE, nb, bot, top, lft, rgt]

lemma sidesIn_EB_even_l (hF : Deg2 V F) (c0 : Pt)
    (hC : ∀ c ∈ chainCells V F c0, NotTypeIII V F c) :
    ∀ c, IsCell V c → sidesIn (EB V F c0) c % 2 = 0 := by
  intro c hc
  have hGE : ∀ s : Side, sideEdge c s ∈ GE V := by
    intro s; rw [mem_GE]
    obtain ⟨x, y⟩ := c
    obtain ⟨h1, h2, h3, h4⟩ := hc
    cases s <;> simp [IsEdge, sideEdge, bot, top, lft, rgt, Edge.q] <;>
      exact ⟨by assumption, by assumption⟩
  by_cases hin : c ∈ chainCells V F c0
  · have hiff : ∀ s : Side, sideEdge c s ∈ EB V F c0 ↔ Inter V F (sideEdge c s) := by
      intro s
      simp only [EB, Finset.mem_filter]
      constructor
      · exact fun h => h.2.1
      · exact fun h => ⟨hGE s, h, c, hin, side_mem_cellE c s⟩
    have hTn : ∀ s, Inter V F (sideEdge c s) → IsCell V (nb c s) → NotTypeIII V F (nb c s) := by
      intro s hI hcell
      apply hC
      simp only [chainCells, Finset.mem_filter] at hin ⊢
      exact ⟨mem_cells.2 hcell, hin.2.tail ⟨hc, hcell, _, hI, side_mem_cellE c s,
        side_mem_cellE_nb c s⟩⟩
    have := interCount_even_l hF hc (hC c hin) hTn
    unfold sidesIn interCount ind at *
    have hb := hiff .b; have ht := hiff .t; have hl := hiff .l; have hr := hiff .r
    simp only [sideEdge] at hb ht hl hr
    simp only [hb, ht, hl, hr]
    exact this
  · have hno : ∀ s : Side, sideEdge c s ∉ EB V F c0 := fun s h =>
      hin (on_chain_of_side hc (side_mem_cellE c s) h)
    unfold sidesIn ind
    have hb := hno .b; have ht := hno .t; have hl := hno .l; have hr := hno .r
    simp only [sideEdge] at hb ht hl hr
    simp [hb, ht, hl, hr]

-- **The chain is a border** when no cell of the chain is Type III (other cells may be).
--
theorem chain_border_l (hs : Solid V) (hF : Deg2 V F) (x0 : Pt)
    (hconn : ∀ z ∈ V, Conn (GE V) x0 z) (c0 : Pt)
    (hC : ∀ c ∈ chainCells V F c0, NotTypeIII V F c) :
    ∃ P : Finset Pt, Border V F P ∧ ∀ e, IsEdge V e → (Cut P e ↔ e ∈ EB V F c0) := by
  apply separation (EB V F c0) hs (sidesIn_EB_even_l hF c0 hC) hF.1
  · intro e he
    simp only [EB, Finset.mem_filter] at he
    exact he.2.1.2.1
  · exact hconn

end chainsep

end SolidGridHam
