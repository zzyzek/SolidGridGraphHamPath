/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
import SolidGridHam.Basic.Planar

/-!
# Counting components

`ncomp V F` counts the connected components of `(V, F)`: the number of distinct classes
`{y ∈ V | Conn F x y}` for `x ∈ V`.

Every change of a factor in this development is a sequence of single-edge insertions and
deletions, so the only counting facts needed are:
* inserting an edge inside a class changes nothing;
* inserting an edge between two classes merges them (count − 1);
* deleting an edge reverses one of the above.

Plus two degree facts: the handshake lemma per class (so an edge whose class has only
even degrees is not a bridge), and at most two vertices of degree 1 per class when all
degrees are at most 2.
-/

namespace SolidGridHam

open Finset Classical

/-! ## Inserting one edge -/

lemma adj_insert {F : Finset Edge} {e : Edge} {a b : Pt} :
    Adj (insert e F) a b ↔ Adj F a b ∨ (a = e.p ∧ b = e.q) ∨ (a = e.q ∧ b = e.p) := by
  constructor
  · rintro ⟨f, hf, h⟩
    rcases Finset.mem_insert.1 hf with hf | hf
    · subst hf; rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inr (Or.inl ⟨h1.symm, h2.symm⟩)
      · exact Or.inr (Or.inr ⟨h2.symm, h1.symm⟩)
    · exact Or.inl ⟨f, hf, h⟩
  · rintro (h | ⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact h.mono (Finset.subset_insert _ _)
    · exact ⟨e, Finset.mem_insert_self _ _, Or.inl ⟨h1.symm, h2.symm⟩⟩
    · exact ⟨e, Finset.mem_insert_self _ _, Or.inr ⟨h2.symm, h1.symm⟩⟩

lemma conn_insert {F : Finset Edge} {e : Edge} {x y : Pt} :
    Conn (insert e F) x y ↔
      Conn F x y ∨ (Conn F x e.p ∧ Conn F e.q y) ∨ (Conn F x e.q ∧ Conn F e.p y) := by
  constructor
  · intro h
    induction h with
    | refl => exact Or.inl (Conn.refl _ _)
    | tail _ hyz ih =>
      rename_i y z
      rcases adj_insert.1 hyz with hyz | ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rcases ih with h | ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact Or.inl (h.trans (Conn.of_adj hyz))
        · exact Or.inr (Or.inl ⟨h1, h2.trans (Conn.of_adj hyz)⟩)
        · exact Or.inr (Or.inr ⟨h1, h2.trans (Conn.of_adj hyz)⟩)
      · subst h1 h2
        rcases ih with h | ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact Or.inr (Or.inl ⟨h, Conn.refl _ _⟩)
        · exact Or.inl (h1.trans h2.symm)
        · exact Or.inl h1
      · subst h1 h2
        rcases ih with h | ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact Or.inr (Or.inr ⟨h, Conn.refl _ _⟩)
        · exact Or.inl h1
        · exact Or.inl (h1.trans h2.symm)
  · have hs : F ⊆ insert e F := Finset.subset_insert _ _
    have he : Conn (insert e F) e.p e.q := Conn.of_edge (Finset.mem_insert_self _ _)
    rintro (h | ⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact h.mono hs
    · exact ((h1.mono hs).trans he).trans (h2.mono hs)
    · exact ((h1.mono hs).trans he.symm).trans (h2.mono hs)

-- Inserting an edge whose ends are already joined changes no connection.
--
lemma conn_insert_of_conn {F : Finset Edge} {e : Edge} (h : Conn F e.p e.q) (x y : Pt) :
    Conn (insert e F) x y ↔ Conn F x y := by
  rw [conn_insert]
  constructor
  · rintro (h' | ⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact h'
    · exact (h1.trans h).trans h2
    · exact (h1.trans h.symm).trans h2
  · exact fun h' => Or.inl h'

/-! ## Classes and the count -/

noncomputable def cls (V : Finset Pt) (F : Finset Edge) (x : Pt) : Finset Pt := V.filter (Conn F x)

noncomputable def ncomp (V : Finset Pt) (F : Finset Edge) : ℕ := (V.image (cls V F)).card

lemma ncomp_congr {V : Finset Pt} {F F' : Finset Edge}
    (h : ∀ x ∈ V, ∀ y ∈ V, Conn F x y ↔ Conn F' x y) : ncomp V F = ncomp V F' := by
  unfold ncomp
  congr 1
  apply Finset.image_congr
  intro x hx
  unfold cls
  apply Finset.filter_congr
  intro y hy
  exact h x hx y hy

lemma cls_eq_of_conn {V : Finset Pt} {F : Finset Edge} {x y : Pt} (h : Conn F x y) :
    cls V F x = cls V F y := by
  unfold cls; ext z
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hz, h'⟩; exact ⟨hz, h.symm.trans h'⟩
  · rintro ⟨hz, h'⟩; exact ⟨hz, h.trans h'⟩

lemma mem_cls_self {V : Finset Pt} {F : Finset Edge} {x : Pt} (hx : x ∈ V) : x ∈ cls V F x := by
  unfold cls; simp [hx, Conn.refl]

-- **Merge.** Inserting an edge between two classes lowers the count by one.
--
theorem ncomp_insert_merge {V : Finset Pt} {F : Finset Edge} {e : Edge}
    (hu : e.p ∈ V) (hv : e.q ∈ V) (hn : ¬ Conn F e.p e.q) :
    ncomp V (insert e F) + 1 = ncomp V F := by
  set A := cls V F e.p
  set B := cls V F e.q
  set W := V.filter (fun w => ¬ Conn F e.p w ∧ ¬ Conn F e.q w)
  set Rest := W.image (cls V F)
  -- New classes.
  have cls' : ∀ x ∈ V, cls V (insert e F) x =
      if Conn F e.p x ∨ Conn F e.q x then A ∪ B else cls V F x := by
    intro x hx
    split_ifs with hc
    · ext y
      simp only [cls, A, B, Finset.mem_filter, Finset.mem_union, conn_insert]
      rcases hc with hc | hc
      · constructor
        · rintro ⟨hy, h | ⟨h1, h2⟩ | ⟨h1, h2⟩⟩
          · exact Or.inl ⟨hy, hc.trans h⟩
          · exact Or.inr ⟨hy, h2⟩
          · exact Or.inl ⟨hy, h2⟩
        · rintro (⟨hy, h⟩ | ⟨hy, h⟩)
          · exact ⟨hy, Or.inl (hc.symm.trans h)⟩
          · exact ⟨hy, Or.inr (Or.inl ⟨hc.symm, h⟩)⟩
      · constructor
        · rintro ⟨hy, h | ⟨h1, h2⟩ | ⟨h1, h2⟩⟩
          · exact Or.inr ⟨hy, hc.trans h⟩
          · exact Or.inr ⟨hy, h2⟩
          · exact Or.inl ⟨hy, h2⟩
        · rintro (⟨hy, h⟩ | ⟨hy, h⟩)
          · exact ⟨hy, Or.inr (Or.inr ⟨hc.symm, h⟩)⟩
          · exact ⟨hy, Or.inl (hc.symm.trans h)⟩
    · simp only [not_or] at hc
      ext y
      simp only [cls, Finset.mem_filter, conn_insert]
      constructor
      · rintro ⟨hy, h | ⟨h1, h2⟩ | ⟨h1, h2⟩⟩
        · exact ⟨hy, h⟩
        · exact absurd h1.symm hc.1
        · exact absurd h1.symm hc.2
      · rintro ⟨hy, h⟩; exact ⟨hy, Or.inl h⟩
  -- Old image and new image in terms of `Rest`.
  have uA : e.p ∈ A := mem_cls_self hu
  have vB : e.q ∈ B := mem_cls_self hv
  have notin : ∀ S ∈ Rest, e.p ∉ S ∧ e.q ∉ S := by
    intro S hS
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.1 hS
    simp only [W, Finset.mem_filter] at hw
    unfold cls; simp only [Finset.mem_filter, not_and]
    exact ⟨fun _ h => hw.2.1 h.symm, fun _ h => hw.2.2 h.symm⟩
  have hAB : A ≠ B := by
    intro h; apply hn
    have : e.p ∈ B := h ▸ uA
    simp only [B, cls, Finset.mem_filter] at this
    exact this.2.symm
  have old : V.image (cls V F) = insert A (insert B Rest) := by
    ext S
    simp only [Finset.mem_image, Finset.mem_insert, Rest, W, Finset.mem_filter]
    constructor
    · rintro ⟨x, hx, rfl⟩
      by_cases h1 : Conn F e.p x
      · exact Or.inl (cls_eq_of_conn h1).symm
      · by_cases h2 : Conn F e.q x
        · exact Or.inr (Or.inl (cls_eq_of_conn h2).symm)
        · exact Or.inr (Or.inr ⟨x, ⟨hx, h1, h2⟩, rfl⟩)
    · rintro (rfl | rfl | ⟨x, ⟨hx, _⟩, rfl⟩)
      · exact ⟨e.p, hu, rfl⟩
      · exact ⟨e.q, hv, rfl⟩
      · exact ⟨x, hx, rfl⟩
  have new : V.image (cls V (insert e F)) = insert (A ∪ B) Rest := by
    ext S
    simp only [Finset.mem_image, Finset.mem_insert, Rest, W, Finset.mem_filter]
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [cls' x hx]
      split_ifs with h
      · exact Or.inl rfl
      · simp only [not_or] at h; exact Or.inr ⟨x, ⟨hx, h.1, h.2⟩, rfl⟩
    · rintro (rfl | ⟨x, ⟨hx, h1, h2⟩, rfl⟩)
      · refine ⟨e.p, hu, ?_⟩
        rw [cls' _ hu, ite_eq_left (Or.inl (Conn.refl _ _))]
      · refine ⟨x, hx, ?_⟩
        rw [cls' _ hx, ite_eq_right (by simp only [not_or]; exact ⟨h1, h2⟩)]
  unfold ncomp
  rw [old, new]
  have hA : A ∉ insert B Rest := by
    simp only [Finset.mem_insert, not_or]
    exact ⟨hAB, fun h => (notin A h).1 uA⟩
  have hB : B ∉ Rest := fun h => (notin B h).2 vB
  have hAB' : A ∪ B ∉ Rest := fun h => (notin _ h).1 (Finset.mem_union_left _ uA)
  rw [Finset.card_insert_of_notMem hA, Finset.card_insert_of_notMem hB,
    Finset.card_insert_of_notMem hAB']

/-! ## Incidence and degree -/

-- The four edges at `y`.
--
def inc (y : Pt) : Finset Edge := {eR y, eU y, eL y, eD y}

lemma mem_inc {y : Pt} {e : Edge} : e ∈ inc y ↔ e.p = y ∨ e.q = y := by
  obtain ⟨d, p1, p2⟩ := e
  obtain ⟨y1, y2⟩ := y
  cases d <;> simp [inc, eR, eU, eL, eD, Edge.q] <;> omega

lemma ind_erase {F : Finset Edge} {e : Edge} (he : e ∈ F) (g : Edge) :
    ind (F.erase e) g + (if g = e then 1 else 0) = ind F g := by
  unfold ind
  by_cases h : g = e
  · subst h; simp [he]
  · simp [h, Finset.mem_erase]

lemma inc_count (e : Edge) (y : Pt) :
    (if eR y = e then 1 else 0) + (if eU y = e then 1 else 0) + (if eL y = e then 1 else 0) +
      (if eD y = e then 1 else 0) = (if e.p = y ∨ e.q = y then 1 else 0 : ℕ) := by
  obtain ⟨d, p1, p2⟩ := e
  obtain ⟨y1, y2⟩ := y
  cases d <;> simp only [eR, eU, eL, eD, Edge.q, Edge.mk.injEq, Prod.mk.injEq,
    reduceCtorEq, false_and, true_and, ite_false] <;> split_ifs <;> omega

-- Erasing an edge lowers the degrees of its two ends by one.
--
lemma deg_erase {F : Finset Edge} {e : Edge} (he : e ∈ F) (y : Pt) :
    deg (F.erase e) y + (if e.p = y ∨ e.q = y then 1 else 0) = deg F y := by
  rw [← inc_count e y]
  unfold deg
  have h1 := ind_erase he (eR y)
  have h2 := ind_erase he (eU y)
  have h3 := ind_erase he (eL y)
  have h4 := ind_erase he (eD y)
  omega

lemma adj_iff_inc {F : Finset Edge} {x y : Pt} :
    Adj F x y ↔ ∃ e ∈ F, (e.p = x ∧ e.q = y) ∨ (e.p = y ∧ e.q = x) := Iff.rfl

/-! ## Handshake per class -/

-- A set of points closed under `F`-adjacency.
--
def Closed (F : Finset Edge) (K : Finset Pt) : Prop := ∀ x ∈ K, ∀ y, Adj F x y → y ∈ K

lemma sum_shift_eq {F : Finset Edge} {K : Finset Pt} (hK : Closed F K)
    (s : Pt → Pt) (tf : Pt → Pt) (hst : ∀ x, tf (s x) = x) (hts : ∀ x, s (tf x) = x)
    (g g' : Pt → Edge) (hg : ∀ x, g' (s x) = g x)
    (hadj : ∀ x, g x ∈ F → Adj F x (s x)) (hadj' : ∀ x, g' x ∈ F → Adj F x (tf x)) :
    ((K.filter (fun x => g x ∈ F)).card) = ((K.filter (fun x => g' x ∈ F)).card) := by
  apply Finset.card_bij' (fun x _ => s x) (fun x _ => tf x)
  · intro x hx
    simp only [Finset.mem_filter] at hx ⊢
    exact ⟨hK x hx.1 _ (hadj x hx.2), by rw [hg]; exact hx.2⟩
  · intro x hx
    simp only [Finset.mem_filter] at hx ⊢
    refine ⟨hK x hx.1 _ (hadj' x hx.2), ?_⟩
    rw [← hg, hts]; exact hx.2
  · intro x _; exact hst x
  · intro x _; exact hts x

theorem handshake {F : Finset Edge} {K : Finset Pt} (hK : Closed F K) :
    Even (∑ x ∈ K, deg F x) := by
  have e1 : ∀ x, deg F x = ind F (eR x) + ind F (eU x) + ind F (eL x) + ind F (eD x) := by
    intro x; unfold deg; ring
  simp only [e1, Finset.sum_add_distrib]
  have c : ∀ g : Pt → Edge, ∑ x ∈ K, ind F (g x) = (K.filter (fun x => g x ∈ F)).card := by
    intro g; unfold ind; simp [Finset.sum_boole]
  rw [c, c, c, c]
  have hL : (K.filter (fun x => eL x ∈ F)).card = (K.filter (fun x => eR x ∈ F)).card := by
    apply sum_shift_eq hK (fun x => (x.1 - 1, x.2)) (fun x => (x.1 + 1, x.2))
    · intro x; simp
    · intro x; simp
    · intro x; simp [eL, eR]
    · intro x hx; exact ⟨_, hx, Or.inr ⟨by simp [eL], by simp [eL, Edge.q]⟩⟩
    · intro x hx; exact ⟨_, hx, Or.inl ⟨by simp [eR], by simp [eR, Edge.q]⟩⟩
  have hD : (K.filter (fun x => eD x ∈ F)).card = (K.filter (fun x => eU x ∈ F)).card := by
    apply sum_shift_eq hK (fun x => (x.1, x.2 - 1)) (fun x => (x.1, x.2 + 1))
    · intro x; simp
    · intro x; simp
    · intro x; simp [eD, eU]
    · intro x hx; exact ⟨_, hx, Or.inr ⟨by simp [eD], by simp [eD, Edge.q]⟩⟩
    · intro x hx; exact ⟨_, hx, Or.inl ⟨by simp [eU], by simp [eU, Edge.q]⟩⟩
  rw [hL, hD]
  exact ⟨(K.filter (fun x => eR x ∈ F)).card + (K.filter (fun x => eU x ∈ F)).card, by ring⟩

-- Edges of `F` stay inside `V`.
--
def Inside (V : Finset Pt) (F : Finset Edge) : Prop := ∀ e ∈ F, e.p ∈ V ∧ e.q ∈ V

lemma Inside.of_factor {V : Finset Pt} {d : Pt → ℕ} {F : Finset Edge} (h : IsFactor V d F) :
    Inside V F := fun e he => h.1 e he

lemma Inside.mono {V : Finset Pt} {F F' : Finset Edge} (h : Inside V F) (hs : F' ⊆ F) :
    Inside V F' := fun e he => h e (hs he)

lemma closed_cls {V : Finset Pt} {F : Finset Edge} (hV : Inside V F) (x : Pt) :
    Closed F (cls V F x) := by
  intro y hy z hz
  unfold cls at hy ⊢
  simp only [Finset.mem_filter] at hy ⊢
  obtain ⟨f, hf, h⟩ := hz
  refine ⟨?_, hy.2.trans (Conn.of_adj ⟨f, hf, h⟩)⟩
  rcases h with ⟨_, h⟩ | ⟨h, _⟩
  · rw [← h]; exact (hV f hf).2
  · rw [← h]; exact (hV f hf).1

-- **No bridges.** If every vertex in `e`'s class has even degree, removing `e` keeps its
-- ends joined.
--
theorem conn_erase_of_even {V : Finset Pt} {F : Finset Edge} (hV : Inside V F) {e : Edge}
    (he : e ∈ F) (heven : ∀ z ∈ V, Conn F e.p z → Even (deg F z)) :
    Conn (F.erase e) e.p e.q := by
  by_contra hn
  have hV' : Inside V (F.erase e) := hV.mono (Finset.erase_subset _ _)
  set K := cls V (F.erase e) e.p
  have hs := handshake (closed_cls hV' e.p)
  have hp : e.p ∈ K := mem_cls_self (hV e he).1
  have hq : e.q ∉ K := by
    unfold K cls; simp only [Finset.mem_filter, not_and]; exact fun _ h => hn h
  have hsum : ∑ x ∈ K, deg F x =
      ∑ x ∈ K, deg (F.erase e) x + ∑ x ∈ K, (if e.p = x ∨ e.q = x then 1 else 0) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro x _; exact (deg_erase he x).symm
  have hone : ∑ x ∈ K, (if e.p = x ∨ e.q = x then 1 else 0) = 1 := by
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, smul_eq_mul,
      mul_one]
    rw [Finset.card_eq_one]
    refine ⟨e.p, ?_⟩
    ext x
    simp only [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨hx, h | h⟩
      · exact h.symm
      · subst h; exact absurd hx hq
    · rintro rfl; exact ⟨hp, Or.inl rfl⟩
  have hev : Even (∑ x ∈ K, deg F x) := by
    apply Finset.even_sum
    intro x hx
    unfold K cls at hx
    simp only [Finset.mem_filter] at hx
    exact heven x hx.1 (hx.2.mono (Finset.erase_subset _ _))
  rw [hsum, hone] at hev
  rw [Nat.even_add_one] at hev
  exact hev hs

/-! ## At most two degree-1 vertices per class when degrees are at most 2 -/

lemma conn_map {F F' : Finset Edge} (f : Pt → Pt)
    (h : ∀ u v, Adj F u v → Conn F' (f u) (f v)) {x y : Pt} (hxy : Conn F x y) :
    Conn F' (f x) (f y) := by
  induction hxy with
  | refl => exact Conn.refl _ _
  | tail _ hyz ih => exact ih.trans (h _ _ hyz)

lemma one_le_deg {F : Finset Edge} {e : Edge} (he : e ∈ F) {y : Pt} (hy : e.p = y ∨ e.q = y) :
    1 ≤ deg F y := by
  have := deg_erase he y
  rw [ite_eq_left hy] at this
  omega

lemma exists_inc_of_deg {F : Finset Edge} {y : Pt} (h : 1 ≤ deg F y) :
    ∃ e ∈ F, e.p = y ∨ e.q = y := by
  unfold deg ind at h
  by_cases h1 : eR y ∈ F
  · exact ⟨_, h1, Or.inl (by simp [eR])⟩
  by_cases h2 : eL y ∈ F
  · exact ⟨_, h2, Or.inr (by simp [eL, Edge.q])⟩
  by_cases h3 : eU y ∈ F
  · exact ⟨_, h3, Or.inl (by simp [eU])⟩
  by_cases h4 : eD y ∈ F
  · exact ⟨_, h4, Or.inr (by simp [eD, Edge.q])⟩
  simp [h1, h2, h3, h4] at h

-- With degree 1, the incident edge is unique.
--
lemma inc_unique {F : Finset Edge} {y : Pt} (hd : deg F y = 1) {e e' : Edge} (he : e ∈ F)
    (hy : e.p = y ∨ e.q = y) (he' : e' ∈ F) (hy' : e'.p = y ∨ e'.q = y) : e' = e := by
  by_contra hne
  have h1 := deg_erase he y
  rw [ite_eq_left hy] at h1
  have h2 := one_le_deg (Finset.mem_erase.2 ⟨hne, he'⟩) hy'
  omega

lemma Edge.p_ne_q (e : Edge) : e.p ≠ e.q := by
  obtain ⟨d, p1, p2⟩ := e
  cases d <;> simp [Edge.q]

-- The other end of `e` from `y`.
--
def other (e : Edge) (y : Pt) : Pt := if e.p = y then e.q else e.p

lemma adj_other {F : Finset Edge} {e : Edge} (he : e ∈ F) {y : Pt} (hy : e.p = y ∨ e.q = y) :
    Adj F y (other e y) := by
  unfold other
  split_ifs with h
  · exact ⟨e, he, Or.inl ⟨h, rfl⟩⟩
  · rcases hy with hy | hy
    · exact absurd hy h
    · exact ⟨e, he, Or.inr ⟨rfl, hy⟩⟩

lemma other_inc {e : Edge} {y : Pt} : e.p = other e y ∨ e.q = other e y := by
  unfold other; split_ifs <;> simp

lemma other_ne {e : Edge} {y : Pt} (hy : e.p = y ∨ e.q = y) : other e y ≠ y := by
  unfold other
  split_ifs with h
  · subst h; exact (Edge.p_ne_q e).symm
  · rcases hy with hy | hy
    · exact absurd hy h
    · subst hy; exact Edge.p_ne_q e

lemma adj_inc {F : Finset Edge} {u v : Pt} (h : Adj F u v) :
    ∃ e ∈ F, (e.p = u ∨ e.q = u) ∧ (e.p = v ∨ e.q = v) ∧ v = other e u := by
  obtain ⟨e, he, h⟩ := h
  refine ⟨e, he, ?_, ?_, ?_⟩
  · rcases h with ⟨h1, _⟩ | ⟨_, h2⟩
    · exact Or.inl h1
    · exact Or.inr h2
  · rcases h with ⟨_, h2⟩ | ⟨h1, _⟩
    · exact Or.inr h2
    · exact Or.inl h1
  · unfold other
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [ite_eq_left h1, h2]
    · have : e.p ≠ u := fun h => Edge.p_ne_q e (h.trans h2.symm)
      rw [ite_eq_right this, h1]

-- An edge has exactly two ends.
--
lemma inc_two {e : Edge} {y z u : Pt} (hy : e.p = y ∨ e.q = y) (hz : e.p = z ∨ e.q = z)
    (hne : y ≠ z) (hu : e.p = u ∨ e.q = u) : u = y ∨ u = z := by
  have hpq := Edge.p_ne_q e
  rcases hy with hy | hy <;> rcases hz with hz | hz <;> rcases hu with hu | hu <;>
    subst hy <;> first
    | exact absurd hz.symm hne
    | exact absurd hz hne
    | exact Or.inl hu.symm
    | exact Or.inr (hu.symm.trans hz)

theorem leaves_le_two {V : Finset Pt} :
    ∀ (n : ℕ) (F : Finset Edge), F.card = n → Inside V F → (∀ y, deg F y ≤ 2) →
      ∀ x, (V.filter (fun y => Conn F x y ∧ deg F y = 1)).card ≤ 2 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro F hn hV hdeg x
  by_contra hlt
  push Not at hlt
  set L := V.filter (fun y => Conn F x y ∧ deg F y = 1)
  obtain ⟨y0, hy0⟩ : L.Nonempty := Finset.card_pos.1 (by omega)
  simp only [L, Finset.mem_filter] at hy0
  obtain ⟨hy0V, hxy0, hd0⟩ := hy0
  obtain ⟨e0, he0, hi0⟩ := exists_inc_of_deg (F := F) (y := y0) (by omega)
  set z := other e0 y0
  have hzi : e0.p = z ∨ e0.q = z := other_inc
  have hzne : z ≠ y0 := other_ne hi0
  have uniq0 : ∀ e ∈ F, (e.p = y0 ∨ e.q = y0) → e = e0 := fun e he hy =>
    inc_unique hd0 he0 hi0 he hy
  have hz1 : 1 ≤ deg F z := one_le_deg he0 hzi
  rcases (show deg F z = 1 ∨ deg F z = 2 by have := hdeg z; omega) with hdz | hdz
  · -- The class of `y0` is `{y0, z}`.
    have uniqz : ∀ e ∈ F, (e.p = z ∨ e.q = z) → e = e0 := fun e he hy =>
      inc_unique hdz he0 hzi he hy
    have small : ∀ w, Conn F y0 w → w = y0 ∨ w = z := by
      intro w hw
      induction hw with
      | refl => exact Or.inl rfl
      | tail _ huv ihw =>
        rename_i u v
        obtain ⟨e, he, hu, hv, _⟩ := adj_inc huv
        have hee : e = e0 := by
          rcases ihw with rfl | rfl
          · exact uniq0 e he hu
          · exact uniqz e he hu
        subst hee
        exact inc_two hi0 hzi hzne.symm hv
    have : L ⊆ {y0, z} := by
      intro y hy
      simp only [L, Finset.mem_filter] at hy
      have := small y (hxy0.symm.trans hy.2.1)
      simp only [Finset.mem_insert, Finset.mem_singleton]; exact this
    have h1 := Finset.card_le_card this
    have h2 : ({y0, z} : Finset Pt).card ≤ 2 :=
      (Finset.card_insert_le _ _).trans (by simp)
    omega
  · -- Remove the pendant edge and use the induction hypothesis at `z`.
    set F0 := F.erase e0 with hF0
    have hcard : F0.card < n := by
      have h1 : F0.card = F.card - 1 := Finset.card_erase_of_mem he0
      have h2 : 0 < F.card := Finset.card_pos.2 ⟨e0, he0⟩
      omega
    have hV0 : Inside V F0 := hV.mono (Finset.erase_subset _ _)
    have hdeg0 : ∀ y, deg F0 y ≤ 2 := by
      intro y; have h1 := deg_erase he0 y; rw [← hF0] at h1; have := hdeg y; omega
    have IH := ih _ hcard F0 rfl hV0 hdeg0 z
    set L0 := V.filter (fun y => Conn F0 z y ∧ deg F0 y = 1)
    have hzL0 : z ∈ L0 := by
      simp only [L0, Finset.mem_filter]
      refine ⟨?_, Conn.refl _ _, ?_⟩
      · rcases hzi with h | h <;> rw [← h]
        · exact (hV e0 he0).1
        · exact (hV e0 he0).2
      · have h1 := deg_erase he0 z; rw [← hF0, ite_eq_left hzi] at h1; omega
    let f : Pt → Pt := fun w => if w = y0 then z else w
    have hf : ∀ u v, Adj F u v → Conn F0 (f u) (f v) := by
      intro u v huv
      obtain ⟨e, he, h'⟩ := huv
      have hu : e.p = u ∨ e.q = u := by
        rcases h' with ⟨h1, _⟩ | ⟨_, h2⟩
        · exact Or.inl h1
        · exact Or.inr h2
      have hv : e.p = v ∨ e.q = v := by
        rcases h' with ⟨_, h2⟩ | ⟨h1, _⟩
        · exact Or.inr h2
        · exact Or.inl h1
      by_cases hee : e = e0
      · subst hee
        have fz : ∀ w, (e.p = w ∨ e.q = w) → f w = z := by
          intro w hw
          rcases inc_two hi0 hzi hzne.symm hw with h | h
          · simp only [f, ite_eq_left h]
          · subst h; simp only [f, ite_eq_right hzne]
        rw [fz u hu, fz v hv]; exact Conn.refl _ _
      · have hu0 : u ≠ y0 := fun h => hee (uniq0 e he (h ▸ hu))
        have hv0 : v ≠ y0 := fun h => hee (uniq0 e he (h ▸ hv))
        simp only [f, ite_eq_right hu0, ite_eq_right hv0]
        exact Conn.of_adj ⟨e, Finset.mem_erase.2 ⟨hee, he⟩, h'⟩
    have sub : L.erase y0 ⊆ L0.erase z := by
      intro y hy
      simp only [Finset.mem_erase, L, Finset.mem_filter] at hy
      obtain ⟨hyy0, hyV, hxy, hdy⟩ := hy
      have hyz : y ≠ z := by intro h; subst h; omega
      have hni : ¬ (e0.p = y ∨ e0.q = y) := by
        rintro (h | h)
        · rcases hi0 with h0 | h0
          · exact hyy0 (h.symm.trans h0)
          · rcases hzi with h1 | h1
            · exact hyz (h.symm.trans h1)
            · exact hzne (h1.symm.trans h0)
        · rcases hi0 with h0 | h0
          · rcases hzi with h1 | h1
            · exact hzne (h1.symm.trans h0)
            · exact hyz (h.symm.trans h1)
          · exact hyy0 (h.symm.trans h0)
      simp only [Finset.mem_erase, L0, Finset.mem_filter]
      refine ⟨hyz, hyV, ?_, ?_⟩
      · have := conn_map f hf (hxy0.symm.trans hxy)
        simp only [f, ite_eq_left rfl, ite_eq_right hyy0] at this
        exact this
      · have h1 := deg_erase he0 y; rw [← hF0, ite_eq_right hni] at h1; omega
    have c1 := Finset.card_le_card sub
    have hy0L : y0 ∈ L := by
      simp only [L, Finset.mem_filter]; exact ⟨hy0V, hxy0, hd0⟩
    rw [Finset.card_erase_of_mem hy0L, Finset.card_erase_of_mem hzL0] at c1
    omega

end SolidGridHam
