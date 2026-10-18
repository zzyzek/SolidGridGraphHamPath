/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
import ULHC.HP.StartPF

/-!
# Moving an endpoint onto a pendant vertex

Let `t ∈ V` and `p ∉ V` a lattice point whose only neighbour in `V` is `t` (the edge `e0`).
Adding `p` to `V` gives `V' = insert p V`. Hamiltonian `s`–`t` paths of `V` and Hamiltonian
`s`–`p` paths of `V'` correspond (add or remove `e0`), and `p` is a corner of no cell of `V'`,
so the cells of `V'` are those of `V`. With `s` also a corner of no cell, `hpPF_correct_dang`
applies to `V'`, `s`, `p`: the algorithm run on `V'` decides the Hamiltonian `s`–`t` path
problem on `V`.
-/

namespace ULHC

namespace HP

open Finset Classical

/-! ## One component -/

lemma conn_of_ncomp_one {V : Finset Pt} {F : Finset Edge} (h : ncomp V F = 1) {x y : Pt}
    (hx : x ∈ V) (hy : y ∈ V) : Conn F x y := by
  unfold ncomp at h
  obtain ⟨K, hK⟩ := Finset.card_eq_one.1 h
  have hxK : cls V F x = K := by
    have : cls V F x ∈ V.image (cls V F) := Finset.mem_image_of_mem _ hx
    rw [hK] at this; simpa using this
  have hyK : cls V F y = K := by
    have : cls V F y ∈ V.image (cls V F) := Finset.mem_image_of_mem _ hy
    rw [hK] at this; simpa using this
  have hy' : y ∈ cls V F x := by rw [hxK, ← hyK]; exact mem_cls_self hy
  unfold cls at hy'
  exact (Finset.mem_filter.1 hy').2

lemma ncomp_one_of_conn {V : Finset Pt} {F : Finset Edge} {x0 : Pt} (h0 : x0 ∈ V)
    (h : ∀ x ∈ V, ∀ y ∈ V, Conn F x y) : ncomp V F = 1 := by
  unfold ncomp
  rw [Finset.card_eq_one]
  refine ⟨cls V F x0, ?_⟩
  ext K
  simp only [Finset.mem_image, Finset.mem_singleton]
  constructor
  · rintro ⟨x, hx, rfl⟩
    unfold cls
    apply Finset.filter_congr
    intro z hz
    exact ⟨fun hxz => (h x0 h0 x hx).trans hxz, fun h0z => (h x hx x0 h0).trans h0z⟩
  · rintro rfl; exact ⟨x0, h0, rfl⟩

section pendant

variable {V : Finset Pt} {s t p : Pt} {e0 : Edge}
  (hpV : p ∉ V) (htV : t ∈ V) (he0 : (e0.p = t ∧ e0.q = p) ∨ (e0.p = p ∧ e0.q = t))
  (hpe : ∀ e : Edge, (e.p = p ∨ e.q = p) → e.p ∈ insert p V → e.q ∈ insert p V → e = e0)
include hpV htV he0 hpe

omit hpV htV hpe in
lemma e0_ends : (e0.p = p ∨ e0.q = p) ∧ (e0.p = t ∨ e0.q = t) := by
  rcases he0 with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨Or.inr h2, Or.inl h1⟩
  · exact ⟨Or.inl h1, Or.inr h2⟩

omit htV hpe in
lemma e0_not_inside {F : Finset Edge} (hF : Inside V F) : e0 ∉ F := by
  intro h
  have := hF e0 h
  rcases he0 with ⟨_, h2⟩ | ⟨h1, _⟩
  · exact hpV (h2 ▸ this.2)
  · exact hpV (h1 ▸ this.1)

omit he0 hpe in
lemma t_ne_p : t ≠ p := fun h => hpV (h ▸ htV)

omit hpV htV he0 in
-- `p` is a corner of no cell of `V'`: a cell with corner `p` has two sides at `p`, both inside
-- `V'`, and they are different edges.
--
lemma pendant_not_corner {c : Pt} (hc : IsCell (insert p V) c) : ¬ IsCorner p c := by
  obtain ⟨c1, c2, c3, c4⟩ := hc
  obtain ⟨x, y⟩ := c
  simp only at c1 c2 c3 c4
  rintro (h | h | h | h)
  · have a := hpe ⟨.h, (x, y)⟩ (Or.inl h.symm) c1 c2
    have b := hpe ⟨.v, (x, y)⟩ (Or.inl h.symm) c1 c3
    rw [← b] at a; simp at a
  · have a := hpe ⟨.h, (x, y)⟩ (Or.inr (by simp [h])) c1 c2
    have b := hpe ⟨.v, (x + 1, y)⟩ (Or.inl h.symm) c2 c4
    rw [← b] at a; simp at a
  · have a := hpe ⟨.h, (x, y + 1)⟩ (Or.inl h.symm) c3 c4
    have b := hpe ⟨.v, (x, y)⟩ (Or.inr (by simp [h])) c1 c3
    rw [← b] at a; simp at a
  · have a := hpe ⟨.h, (x, y + 1)⟩ (Or.inr (by simp [h])) c3 c4
    have b := hpe ⟨.v, (x + 1, y)⟩ (Or.inr (by simp [h])) c2 c4
    rw [← b] at a; simp at a

omit hpV htV he0 in
lemma pendant_cell {c : Pt} (hc : IsCell (insert p V) c) : IsCell V c := by
  have hnp := pendant_not_corner hpe hc
  obtain ⟨c1, c2, c3, c4⟩ := hc
  unfold IsCorner at hnp
  push Not at hnp
  obtain ⟨n1, n2, n3, n4⟩ := hnp
  exact ⟨(Finset.mem_insert.1 c1).resolve_left (Ne.symm n1),
    (Finset.mem_insert.1 c2).resolve_left (Ne.symm n2),
    (Finset.mem_insert.1 c3).resolve_left (Ne.symm n3),
    (Finset.mem_insert.1 c4).resolve_left (Ne.symm n4)⟩

-- `t` is one of the four orthogonal neighbours of `p`.
--
omit hpV htV hpe in
lemma t_adj : t = (p.1 + 1, p.2) ∨ t = (p.1 - 1, p.2) ∨ t = (p.1, p.2 + 1) ∨ t = (p.1, p.2 - 1) := by
  obtain ⟨dir, ⟨wx, wy⟩⟩ := e0
  obtain ⟨px, py⟩ := p
  obtain ⟨tx, ty⟩ := t
  cases dir <;> simp only [Edge.q, Prod.mk.injEq] at he0 <;>
    rcases he0 with ⟨⟨h1, h2⟩, h3, h4⟩ | ⟨⟨h1, h2⟩, h3, h4⟩ <;>
    simp only [Prod.mk.injEq] <;> omega

-- The other orthogonal neighbours of `p` are outside `V'`.
--
lemma orth_free {q : Pt}
    (hq : q = (p.1 + 1, p.2) ∨ q = (p.1 - 1, p.2) ∨ q = (p.1, p.2 + 1) ∨ q = (p.1, p.2 - 1))
    (hqt : q ≠ t) : q ∉ insert p V := by
  intro hm
  have hqp : q ≠ p := by
    obtain ⟨a, b⟩ := p
    rcases hq with rfl | rfl | rfl | rfl <;> simp
  have hqV : q ∈ V := (Finset.mem_insert.1 hm).resolve_left hqp
  have hpm : p ∈ insert p V := Finset.mem_insert_self _ _
  have key : ∀ E : Edge, ((E.p = p ∧ E.q = q) ∨ (E.p = q ∧ E.q = p)) → False := by
    intro E hE
    have hE0 : E = e0 := by
      rcases hE with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact hpe E (Or.inl h1) (h1 ▸ hpm) (h2 ▸ hm)
      · exact hpe E (Or.inr h2) (h1 ▸ hm) (h2 ▸ hpm)
    subst hE0
    rcases hE with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases he0 with ⟨g1, g2⟩ | ⟨g1, g2⟩
    · exact hpV ((g1.symm.trans h1) ▸ htV)
    · exact hqt (h2.symm.trans g2)
    · exact hqt (h1.symm.trans g1)
    · exact hpV ((g2.symm.trans h2) ▸ htV)
  obtain ⟨a, b⟩ := p
  rcases hq with rfl | rfl | rfl | rfl
  · exact key ⟨.h, (a, b)⟩ (Or.inl ⟨rfl, rfl⟩)
  · exact key ⟨.h, (a - 1, b)⟩ (Or.inr ⟨rfl, by simp⟩)
  · exact key ⟨.v, (a, b)⟩ (Or.inl ⟨rfl, rfl⟩)
  · exact key ⟨.v, (a, b - 1)⟩ (Or.inr ⟨rfl, by simp⟩)

-- Every missing king neighbour of `p` reaches the free neighbour opposite `t` by at most two king
-- moves outside `V'`.
--
lemma ring_chain {z : Pt} (hz : z ∉ insert p V) (hzx : |z.1 - p.1| ≤ 1) (hzy : |z.2 - p.2| ≤ 1) :
    Relation.ReflTransGen (MissAdj (insert p V)) z (2 * p.1 - t.1, 2 * p.2 - t.2) := by
  have fr := fun q hq hqt => orth_free hpV htV he0 hpe (q := q) hq hqt
  obtain ⟨a, b⟩ := p
  obtain ⟨x, y⟩ := z
  simp only at hzx hzy fr ⊢
  have hzp : (x, y) ≠ (a, b) := fun h => hz (h ▸ Finset.mem_insert_self _ _)
  have one : ∀ u v : Pt, u ∉ insert (a, b) V → v ∉ insert (a, b) V → |u.1 - v.1| ≤ 1 →
      |u.2 - v.2| ≤ 1 → Relation.ReflTransGen (MissAdj (insert (a, b) V)) u v :=
    fun u v hu hv h1 h2 => Relation.ReflTransGen.single ⟨hu, hv, h1, h2⟩
  have hx : x = a - 1 ∨ x = a ∨ x = a + 1 := by rw [abs_le] at hzx; omega
  have hy : y = b - 1 ∨ y = b ∨ y = b + 1 := by rw [abs_le] at hzy; omega
  rcases t_adj he0 with rfl | rfl | rfl | rfl <;> simp only at fr ⊢
  -- t to the right: the target is (a - 1, b).
  · have oL := fr (a - 1, b) (by simp) (by simp only [ne_eq, Prod.mk.injEq]; omega)
    have oU := fr (a, b + 1) (by simp) (by simp only [ne_eq, Prod.mk.injEq]; omega)
    have oD := fr (a, b - 1) (by simp) (by simp only [ne_eq, Prod.mk.injEq]; omega)
    have tgt : (2 * a - (a + 1), 2 * b - b) = (a - 1, b) := by simp only [Prod.mk.injEq]; constructor <;> ring
    rw [tgt]
    rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl
    · exact one _ _ hz oL (by simp) (by simp)
    · exact Relation.ReflTransGen.refl
    · exact one _ _ hz oL (by simp) (by simp)
    · exact one _ _ hz oL (by simp) (by simp)
    · exact absurd rfl hzp
    · exact one _ _ hz oL (by simp) (by simp)
    · exact (one _ _ hz oD (by simp) (by simp)).trans (one _ _ oD oL (by simp) (by simp))
    · exact absurd (Finset.mem_insert_of_mem htV) hz
    · exact (one _ _ hz oU (by simp) (by simp)).trans (one _ _ oU oL (by simp) (by simp))
  -- t to the left: the target is (a + 1, b).
  · have oR := fr (a + 1, b) (by simp) (by simp only [ne_eq, Prod.mk.injEq]; omega)
    have oU := fr (a, b + 1) (by simp) (by simp only [ne_eq, Prod.mk.injEq]; omega)
    have oD := fr (a, b - 1) (by simp) (by simp only [ne_eq, Prod.mk.injEq]; omega)
    have tgt : (2 * a - (a - 1), 2 * b - b) = (a + 1, b) := by simp only [Prod.mk.injEq]; constructor <;> ring
    rw [tgt]
    rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl
    · exact (one _ _ hz oD (by simp) (by simp)).trans (one _ _ oD oR (by simp) (by simp))
    · exact absurd (Finset.mem_insert_of_mem htV) hz
    · exact (one _ _ hz oU (by simp) (by simp)).trans (one _ _ oU oR (by simp) (by simp))
    · exact one _ _ hz oR (by simp) (by simp)
    · exact absurd rfl hzp
    · exact one _ _ hz oR (by simp) (by simp)
    · exact one _ _ hz oR (by simp) (by simp)
    · exact Relation.ReflTransGen.refl
    · exact one _ _ hz oR (by simp) (by simp)
  -- t above: the target is (a, b - 1).
  · have oR := fr (a + 1, b) (by simp) (by simp only [ne_eq, Prod.mk.injEq]; omega)
    have oL := fr (a - 1, b) (by simp) (by simp only [ne_eq, Prod.mk.injEq]; omega)
    have oD := fr (a, b - 1) (by simp) (by simp only [ne_eq, Prod.mk.injEq]; omega)
    have tgt : (2 * a - a, 2 * b - (b + 1)) = (a, b - 1) := by simp only [Prod.mk.injEq]; constructor <;> ring
    rw [tgt]
    rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl
    · exact one _ _ hz oD (by simp) (by simp)
    · exact one _ _ hz oD (by simp) (by simp)
    · exact (one _ _ hz oL (by simp) (by simp)).trans (one _ _ oL oD (by simp) (by simp))
    · exact Relation.ReflTransGen.refl
    · exact absurd rfl hzp
    · exact absurd (Finset.mem_insert_of_mem htV) hz
    · exact one _ _ hz oD (by simp) (by simp)
    · exact one _ _ hz oD (by simp) (by simp)
    · exact (one _ _ hz oR (by simp) (by simp)).trans (one _ _ oR oD (by simp) (by simp))
  -- t below: the target is (a, b + 1).
  · have oR := fr (a + 1, b) (by simp) (by simp only [ne_eq, Prod.mk.injEq]; omega)
    have oL := fr (a - 1, b) (by simp) (by simp only [ne_eq, Prod.mk.injEq]; omega)
    have oU := fr (a, b + 1) (by simp) (by simp only [ne_eq, Prod.mk.injEq]; omega)
    have tgt : (2 * a - a, 2 * b - (b - 1)) = (a, b + 1) := by simp only [Prod.mk.injEq]; constructor <;> ring
    rw [tgt]
    rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl
    · exact (one _ _ hz oL (by simp) (by simp)).trans (one _ _ oL oU (by simp) (by simp))
    · exact one _ _ hz oU (by simp) (by simp)
    · exact one _ _ hz oU (by simp) (by simp)
    · exact absurd (Finset.mem_insert_of_mem htV) hz
    · exact absurd rfl hzp
    · exact Relation.ReflTransGen.refl
    · exact (one _ _ hz oR (by simp) (by simp)).trans (one _ _ oR oU (by simp) (by simp))
    · exact one _ _ hz oU (by simp) (by simp)
    · exact one _ _ hz oU (by simp) (by simp)

-- **`V'` is solid**: an escape path of missing points through `p` is rerouted around `p` through
-- the free neighbour opposite `t` (`ring_chain`).
--
theorem pendant_solid (hs : Solid V) : Solid (insert p V) := by
  set V' := insert p V with hV'
  set o : Pt := (2 * p.1 - t.1, 2 * p.2 - t.2) with ho
  have hta := t_adj he0
  have hot : o ≠ t := by
    intro h; rw [ho] at h
    rcases hta with h' | h' | h' | h' <;> rw [h'] at h <;> dsimp only at h <;>
      simp only [Prod.mk.injEq] at h <;> omega
  have hoF : o ∉ V' := orth_free hpV htV he0 hpe (by
    rw [ho]
    rcases hta with h' | h' | h' | h' <;> rw [h'] <;> dsimp only <;>
      simp only [Prod.mk.injEq] <;> omega) hot
  have rev : ∀ {x y : Pt}, Relation.ReflTransGen (MissAdj V') x y →
      Relation.ReflTransGen (MissAdj V') y x := by
    intro x y hxy
    induction hxy with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ hbc ih =>
      obtain ⟨h1, h2, h3, h4⟩ := hbc
      exact (Relation.ReflTransGen.single ⟨h2, h1, by rw [abs_sub_comm]; exact h3,
        by rw [abs_sub_comm]; exact h4⟩).trans ih
  let Q : Pt → Prop := fun y => ∃ b, Relation.ReflTransGen (MissAdj V') y b ∧ ∀ q ∈ V', b.1 < q.1
  have back : ∀ y z, Relation.ReflTransGen (MissAdj V') y z → Q z → Q y :=
    fun y z hyz ⟨b, hzb, hb⟩ => ⟨b, hyz.trans hzb, hb⟩
  intro a ha
  have haV : a ∉ V := fun h => ha (Finset.mem_insert_of_mem h)
  have hap : a ≠ p := fun h => ha (h ▸ Finset.mem_insert_self _ _)
  obtain ⟨b0, hch, hleft⟩ := hs a haV
  have key : (a ≠ p → a ∉ V → Q a) ∧ (a = p → Q o) := by
    refine Relation.ReflTransGen.head_induction_on (motive := fun y _ =>
      (y ≠ p → y ∉ V → Q y) ∧ (y = p → Q o)) hch ?_ ?_
    · -- The end of the escape path lies left of all of `V`.
      --
      have hb0V : b0 ∉ V := fun h => lt_irrefl _ (hleft b0 h)
      have htl := hleft t htV
      refine ⟨fun hb0p _ => ?_, fun hb0p => ?_⟩
      · refine ⟨(b0.1 - 1, b0.2), Relation.ReflTransGen.single ⟨?_, ?_, ?_, ?_⟩, ?_⟩
        · exact fun h => (Finset.mem_insert.1 h).elim hb0p hb0V
        · intro h
          rcases Finset.mem_insert.1 h with h | h
          · have : p.1 = b0.1 - 1 := by rw [← h]
            rcases hta with h' | h' | h' | h' <;> rw [h'] at htl <;> simp only at htl <;> omega
          · have := hleft _ h; simp only at this; omega
        · simp
        · simp
        · intro q hq
          rcases Finset.mem_insert.1 hq with rfl | hq
          · rcases hta with h' | h' | h' | h' <;> rw [h'] at htl <;> simp only at htl ⊢ <;> omega
          · have := hleft q hq; simp only; omega
      · subst hb0p
        refine ⟨o, Relation.ReflTransGen.refl, fun q hq => ?_⟩
        have hpx : t.1 = b0.1 + 1 := by
          rcases hta with h' | h' | h' | h' <;> rw [h'] at htl ⊢ <;> simp only at htl ⊢ <;> omega
        rw [ho]; simp only
        rcases Finset.mem_insert.1 hq with rfl | hq
        · omega
        · have := hleft q hq; omega
    · intro y y' hyy' _ ih
      obtain ⟨hyV, hy'V, hx1, hx2⟩ := hyy'
      refine ⟨fun hyp _ => ?_, fun hyp => ?_⟩
      · have hyF : y ∉ V' := fun h => (Finset.mem_insert.1 h).elim hyp hyV
        by_cases hy'p : y' = p
        · rw [hy'p] at hx1 hx2
          exact back _ _ (ring_chain hpV htV he0 hpe hyF hx1 hx2) (ih.2 hy'p)
        · have hy'F : y' ∉ V' := fun h => (Finset.mem_insert.1 h).elim hy'p hy'V
          exact back _ _ (Relation.ReflTransGen.single ⟨hyF, hy'F, hx1, hx2⟩) (ih.1 hy'p hy'V)
      · rw [hyp] at hx1 hx2
        by_cases hy'p : y' = p
        · exact ih.2 hy'p
        · have hy'F : y' ∉ V' := fun h => (Finset.mem_insert.1 h).elim hy'p hy'V
          have hx1' : |y'.1 - p.1| ≤ 1 := by rw [abs_sub_comm]; exact hx1
          have hx2' : |y'.2 - p.2| ≤ 1 := by rw [abs_sub_comm]; exact hx2
          have hc := ring_chain hpV htV he0 hpe hy'F hx1' hx2'
          exact back _ _ (rev hc) (ih.1 hy'p hy'V)
  exact key.1 hap haV

-- **Hamiltonian paths of `V` give Hamiltonian paths of `V'`.**
--
lemma pendant_up (hst : s ≠ t) {H : Finset Edge} (hH : IsFactor V (dST s t) H)
    (hHam : ncomp V H = 1) :
    IsFactor (insert p V) (dST s p) (insert e0 H) ∧ ncomp (insert p V) (insert e0 H) = 1 := by
  have hin : Inside V H := fun e he => hH.1 e he
  have hnot := e0_not_inside hpV he0 hin
  obtain ⟨hep, het⟩ := e0_ends he0
  have htp : t ≠ p := fun h => hpV (h ▸ htV)
  refine ⟨⟨fun e he => ?_, fun z hz => ?_⟩, ?_⟩
  · rcases Finset.mem_insert.1 he with rfl | he
    · rcases he0 with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact ⟨by rw [h1]; exact Finset.mem_insert_of_mem htV, by rw [h2]; exact Finset.mem_insert_self _ _⟩
      · exact ⟨by rw [h1]; exact Finset.mem_insert_self _ _, by rw [h2]; exact Finset.mem_insert_of_mem htV⟩
    · obtain ⟨a, b⟩ := hH.1 e he
      exact ⟨Finset.mem_insert_of_mem a, Finset.mem_insert_of_mem b⟩
  · rcases Finset.mem_insert.1 hz with rfl | hz
    · rw [DF.deg_insert_end hnot hep]
      have : deg H z = 0 := by
        unfold deg ind
        have h1 : eR z ∉ H := fun h => hpV (hin _ h).1
        have h2 : eL z ∉ H := fun h => hpV (by have := (hin _ h).2; simpa [eL] using this)
        have h3 : eU z ∉ H := fun h => hpV (hin _ h).1
        have h4 : eD z ∉ H := fun h => hpV (by have := (hin _ h).2; simpa [eD] using this)
        simp [h1, h2, h3, h4]
      rw [this]; unfold dST; simp
    · by_cases hzt : z = t
      · subst hzt
        rw [DF.deg_insert_end hnot het, hH.2 z hz]
        unfold dST; simp [Ne.symm hst, htp]
      · have hoff : ¬ (e0.p = z ∨ e0.q = z) := by
          rcases he0 with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · rw [h1, h2]; rintro (h | h)
            · exact hzt h.symm
            · exact hpV (h ▸ hz)
          · rw [h1, h2]; rintro (h | h)
            · exact hpV (h ▸ hz)
            · exact hzt h.symm
        rw [DF.deg_insert_off hnot hoff, hH.2 z hz]
        have hzp : z ≠ p := fun h => hpV (h ▸ hz)
        unfold dST; simp [hzt, hzp]
  · refine ncomp_one_of_conn (Finset.mem_insert_self p V) (fun x hx y hy => ?_)
    have hpt : Conn (insert e0 H) p t := by
      refine Relation.ReflTransGen.single ⟨e0, Finset.mem_insert_self _ _, ?_⟩
      rcases he0 with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inr ⟨h1, h2⟩
      · exact Or.inl ⟨h1, h2⟩
    have hsub : H ⊆ insert e0 H := Finset.subset_insert _ _
    have toT : ∀ z ∈ insert p V, Conn (insert e0 H) z t := by
      intro z hz
      rcases Finset.mem_insert.1 hz with rfl | hz
      · exact hpt
      · exact (conn_of_ncomp_one hHam hz htV).mono hsub
    exact (toT x hx).trans (toT y hy).symm

-- **Hamiltonian paths of `V'` give Hamiltonian paths of `V`**: `p` has degree 1, its only
-- possible edge is `e0`, and removing it leaves an `s`–`t` path on `V` (`p` is a dead end, so
-- connections inside `V` never need it).
--
lemma pendant_down (hst : s ≠ t) {H' : Finset Edge} (hH : IsFactor (insert p V) (dST s p) H')
    (hHam : ncomp (insert p V) H' = 1) :
    IsFactor V (dST s t) (H'.erase e0) ∧ ncomp V (H'.erase e0) = 1 := by
  have htp : t ≠ p := fun h => hpV (h ▸ htV)
  obtain ⟨hep, het⟩ := e0_ends he0
  have touch : ∀ e ∈ H', (e.p = p ∨ e.q = p) → e = e0 := fun e he hp =>
    hpe e hp (hH.1 e he).1 (hH.1 e he).2
  have hdp : deg H' p = 1 := by
    rw [hH.2 p (Finset.mem_insert_self _ _)]; unfold dST; simp
  have he0H : e0 ∈ H' := by
    by_contra hn
    have h1 : eR p ∉ H' := fun h => hn (touch _ h (Or.inl rfl) ▸ h)
    have h2 : eL p ∉ H' := fun h => hn (touch _ h (Or.inr (by simp [eL])) ▸ h)
    have h3 : eU p ∉ H' := fun h => hn (touch _ h (Or.inl rfl) ▸ h)
    have h4 : eD p ∉ H' := fun h => hn (touch _ h (Or.inr (by simp [eD])) ▸ h)
    unfold deg ind at hdp
    simp [h1, h2, h3, h4] at hdp
  set H := H'.erase e0 with hHdef
  have offp : ∀ e ∈ H, ¬ (e.p = p ∨ e.q = p) := by
    intro e he hp
    obtain ⟨hne, heH⟩ := Finset.mem_erase.1 he
    exact hne (touch e heH hp)
  refine ⟨⟨fun e he => ?_, fun z hz => ?_⟩, ?_⟩
  · obtain ⟨a, b⟩ := hH.1 e (Finset.mem_erase.1 he).2
    have hn := offp e he
    push Not at hn
    exact ⟨(Finset.mem_insert.1 a).resolve_left hn.1, (Finset.mem_insert.1 b).resolve_left hn.2⟩
  · have hzp : z ≠ p := fun h => hpV (h ▸ hz)
    by_cases hzt : z = t
    · subst hzt
      have := DF.deg_erase_end he0H het
      rw [hH.2 z (Finset.mem_insert_of_mem hz)] at this
      unfold dST at this ⊢
      simp [Ne.symm hst, htp] at this ⊢
      omega
    · have hoff : ¬ (e0.p = z ∨ e0.q = z) := by
        rcases he0 with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · rw [h1, h2]; rintro (h | h)
          · exact hzt h.symm
          · exact hzp h.symm
        · rw [h1, h2]; rintro (h | h)
          · exact hzp h.symm
          · exact hzt h.symm
      rw [DF.deg_erase_off he0H hoff, hH.2 z (Finset.mem_insert_of_mem hz)]
      unfold dST; simp [hzt, hzp]
  · -- A walk of `H'` from a vertex of `V` reaches every vertex of `V` it reaches without `p`.
    --
    have walk : ∀ x ∈ V, ∀ y, Conn H' x y → (y ≠ p → Conn H x y) ∧ (y = p → Conn H x t) := by
      intro x hx y hxy
      induction hxy with
      | refl => exact ⟨fun _ => Conn.refl _ _, fun h => absurd (h ▸ hx) hpV⟩
      | @tail y z _ hyz ih =>
        obtain ⟨e, he, hends⟩ := hyz
        by_cases hee : e = e0
        · subst hee
          rcases he0 with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · rcases hends with ⟨a, b⟩ | ⟨a, b⟩
            · rw [h1] at a; rw [h2] at b; subst a; subst b
              exact ⟨fun h => absurd rfl h, fun _ => ih.1 htp⟩
            · rw [h1] at a; rw [h2] at b; subst a; subst b
              exact ⟨fun _ => ih.2 rfl, fun h => absurd h htp⟩
          · rcases hends with ⟨a, b⟩ | ⟨a, b⟩
            · rw [h1] at a; rw [h2] at b; subst a; subst b
              exact ⟨fun _ => ih.2 rfl, fun h => absurd h htp⟩
            · rw [h1] at a; rw [h2] at b; subst a; subst b
              exact ⟨fun h => absurd rfl h, fun _ => ih.1 htp⟩
        · have heH : e ∈ H := Finset.mem_erase.2 ⟨hee, he⟩
          have hn := offp e heH
          push Not at hn
          have hyp : y ≠ p := by rcases hends with ⟨a, _⟩ | ⟨_, b⟩; exacts [a ▸ hn.1, b ▸ hn.2]
          have hzp : z ≠ p := by rcases hends with ⟨_, b⟩ | ⟨a, _⟩; exacts [b ▸ hn.2, a ▸ hn.1]
          exact ⟨fun _ => (ih.1 hyp).trans (Relation.ReflTransGen.single ⟨e, heH, hends⟩),
            fun h => absurd h hzp⟩
    refine ncomp_one_of_conn htV (fun x hx y hy => ?_)
    have hy' : y ≠ p := fun h => hpV (h ▸ hy)
    exact (walk x hx y (conn_of_ncomp_one hHam (Finset.mem_insert_of_mem hx)
      (Finset.mem_insert_of_mem hy))).1 hy'

-- **The reduction.** With `s` a corner of no cell and `V'` solid, the algorithm run on `V'` with
-- endpoints `s`, `p` decides whether `V` has a Hamiltonian `s`–`t` path; no open lemma is used.
--
theorem hpPF_correct_pendant (hs' : Solid (insert p V)) (hst : s ≠ t) (hsV : s ∈ V)
    (hsD : ∀ c, IsCell V c → ¬ IsCorner s c) :
    hpPF (insert p V) s p = true ↔ ∃ H, IsFactor V (dST s t) H ∧ ncomp V H = 1 := by
  have hsp : s ≠ p := fun h => hpV (h ▸ hsV)
  have hD : Dang (insert p V) s p := fun c hc =>
    ⟨hsD c (pendant_cell hpe hc), pendant_not_corner hpe hc⟩
  rw [hpPF_correct_dang hs' hsp (Finset.mem_insert_of_mem hsV) (Finset.mem_insert_self _ _) hD]
  constructor
  · rintro ⟨H', hH', hHam⟩
    exact ⟨_, pendant_down hpV htV he0 hpe hst hH' hHam⟩
  · rintro ⟨H, hH, hHam⟩
    exact ⟨_, pendant_up hpV htV he0 hpe hst hH hHam⟩

-- With `V` solid, `V'` is solid, so solidity of `V'` need not be assumed.
--
theorem hpPF_correct_pendant' (hs : Solid V) (hst : s ≠ t) (hsV : s ∈ V)
    (hsD : ∀ c, IsCell V c → ¬ IsCorner s c) :
    hpPF (insert p V) s p = true ↔ ∃ H, IsFactor V (dST s t) H ∧ ncomp V H = 1 :=
  hpPF_correct_pendant hpV htV he0 hpe (pendant_solid hpV htV he0 hpe hs) hst hsV hsD

end pendant

end HP

end ULHC

namespace ULHC

namespace HP

lemma dST_comm (s t : Pt) : dST s t = dST t s := by
  funext z; unfold dST; simp only [or_comm]

-- **Both endpoints moved onto pendant vertices.** `p` hangs off `t` (only neighbour `t` in `V`),
-- `q` hangs off `s` (only neighbour `s` in `V ∪ {p}`). Then the algorithm run on `V ∪ {p, q}`
-- with endpoints `q`, `p` decides whether `V` has a Hamiltonian `s`–`t` path. No open lemma is
-- used.
--
theorem hpPF_correct_pendant2 {V : Finset Pt} {s t p q : Pt} {e0 e1 : Edge} (hs : Solid V)
    (hst : s ≠ t) (hsV : s ∈ V) (htV : t ∈ V)
    (hpV : p ∉ V) (he0 : (e0.p = t ∧ e0.q = p) ∨ (e0.p = p ∧ e0.q = t))
    (hpe : ∀ e : Edge, (e.p = p ∨ e.q = p) → e.p ∈ insert p V → e.q ∈ insert p V → e = e0)
    (hqV : q ∉ insert p V) (he1 : (e1.p = s ∧ e1.q = q) ∨ (e1.p = q ∧ e1.q = s))
    (hqe : ∀ e : Edge, (e.p = q ∨ e.q = q) → e.p ∈ insert q (insert p V) →
      e.q ∈ insert q (insert p V) → e = e1) :
    hpPF (insert q (insert p V)) q p = true ↔ ∃ H, IsFactor V (dST s t) H ∧ ncomp V H = 1 := by
  have hsV' : s ∈ insert p V := Finset.mem_insert_of_mem hsV
  have hps : p ≠ s := fun h => hpV (h ▸ hsV)
  have hqp : q ≠ p := fun h => hqV (h ▸ Finset.mem_insert_self _ _)
  have hs' := pendant_solid hpV htV he0 hpe hs
  have hs'' := pendant_solid hqV hsV' he1 hqe hs'
  have hD : Dang (insert q (insert p V)) q p := fun c hc =>
    ⟨pendant_not_corner hqe hc,
      pendant_not_corner hpe (pendant_cell hqe hc)⟩
  rw [hpPF_correct_dang hs'' hqp (Finset.mem_insert_self _ _)
    (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)) hD]
  constructor
  · rintro ⟨H'', hH'', hHam''⟩
    rw [dST_comm] at hH''
    obtain ⟨hH', hHam'⟩ := pendant_down hqV hsV' he1 hqe hps hH'' hHam''
    rw [dST_comm] at hH'
    exact ⟨_, pendant_down hpV htV he0 hpe hst hH' hHam'⟩
  · rintro ⟨H, hH, hHam⟩
    obtain ⟨hH', hHam'⟩ := pendant_up hpV htV he0 hpe hst hH hHam
    rw [dST_comm] at hH'
    obtain ⟨hH'', hHam''⟩ := pendant_up hqV hsV' he1 hqe hps hH' hHam'
    rw [dST_comm] at hH''
    exact ⟨_, hH'', hHam''⟩

end HP

end ULHC

/-! ## Deleting an endpoint whose last edge is fixed

If `H`'s edge at `t` is `ew` (to `w`), removing `t` leaves a Hamiltonian `s`–`w` path of
`V.erase t`, and conversely. With a missing king neighbour of `t`, `V.erase t` stays solid. For a
concave corner (`t` on three squares) the new endpoint `w` then has a missing orthogonal neighbour
(the spot of `t`).
-/

namespace ULHC

namespace HP

open Finset Classical

section delete

variable {V : Finset Pt} {s t w : Pt} {ew : Edge}
  (htV : t ∈ V) (hwV : w ∈ V) (hew : (ew.p = t ∧ ew.q = w) ∨ (ew.p = w ∧ ew.q = t))
include htV hwV hew

omit hwV hew in
-- Removing a vertex with a missing king neighbour keeps a solid set solid.
--
theorem solid_erase (hs : Solid V) {q : Pt} (hq : q ∉ V) (hqx : |q.1 - t.1| ≤ 1)
    (hqy : |q.2 - t.2| ≤ 1) : Solid (V.erase t) := by
  have mono : ∀ {x y}, Relation.ReflTransGen (MissAdj V) x y →
      Relation.ReflTransGen (MissAdj (V.erase t)) x y := by
    intro x y h
    induction h with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ hab ih =>
      obtain ⟨h1, h2, h3, h4⟩ := hab
      exact ih.tail ⟨fun h => h1 (Finset.mem_of_mem_erase h), fun h => h2 (Finset.mem_of_mem_erase h),
        h3, h4⟩
  intro a ha
  by_cases hat : a = t
  · subst hat
    obtain ⟨b, hch, hb⟩ := hs q hq
    refine ⟨b, (Relation.ReflTransGen.single ⟨ha, fun h => hq (Finset.mem_of_mem_erase h),
      by rw [abs_sub_comm]; exact hqx, by rw [abs_sub_comm]; exact hqy⟩).trans (mono hch),
      fun p hp => hb p (Finset.mem_of_mem_erase hp)⟩
  · have haV : a ∉ V := fun h => ha (Finset.mem_erase.2 ⟨hat, h⟩)
    obtain ⟨b, hch, hb⟩ := hs a haV
    exact ⟨b, mono hch, fun p hp => hb p (Finset.mem_of_mem_erase hp)⟩

-- **Hamiltonian `s`–`t` paths ending with `ew` give Hamiltonian `s`–`w` paths of `V.erase t`.**
--
lemma delete_down (_hst : s ≠ t) (hsw : s ≠ w) {H : Finset Edge} (hH : IsFactor V (dST s t) H)
    (hHam : ncomp V H = 1) (hewH : ew ∈ H) :
    IsFactor (V.erase t) (dST s w) (H.erase ew) ∧ ncomp (V.erase t) (H.erase ew) = 1 := by
  have htw : t ≠ w := by
    have hpq : ew.p ≠ ew.q := by
      obtain ⟨dir, ⟨x, y⟩⟩ := ew; cases dir <;> simp [Edge.q]
    rcases hew with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [← h1, ← h2]; exact hpq
    · rw [← h1, ← h2]; exact Ne.symm hpq
  have hendT : ew.p = t ∨ ew.q = t := by rcases hew with ⟨h, _⟩ | ⟨_, h⟩; exacts [Or.inl h, Or.inr h]
  have hendW : ew.p = w ∨ ew.q = w := by rcases hew with ⟨_, h⟩ | ⟨h, _⟩; exacts [Or.inr h, Or.inl h]
  have hdt : deg H t = 1 := by rw [hH.2 t htV]; unfold dST; simp
  -- `ew` is the only edge of `H` at `t`.
  --
  have only : ∀ e ∈ H, (e.p = t ∨ e.q = t) → e = ew := by
    intro e he ht
    by_contra hne
    have h1 := DF.deg_erase_end hewH hendT
    have h2 := DF.deg_erase_end (Finset.mem_erase.2 ⟨hne, he⟩) ht
    omega
  set H' := H.erase ew
  have offt : ∀ e ∈ H', ¬ (e.p = t ∨ e.q = t) := fun e he ht =>
    (Finset.mem_erase.1 he).1 (only e (Finset.mem_erase.1 he).2 ht)
  refine ⟨⟨fun e he => ?_, fun z hz => ?_⟩, ?_⟩
  · obtain ⟨a, b⟩ := hH.1 e (Finset.mem_erase.1 he).2
    have hn := offt e he
    push Not at hn
    exact ⟨Finset.mem_erase.2 ⟨hn.1, a⟩, Finset.mem_erase.2 ⟨hn.2, b⟩⟩
  · obtain ⟨hzt, hzV⟩ := Finset.mem_erase.1 hz
    by_cases hzw : z = w
    · subst hzw
      have := DF.deg_erase_end hewH hendW
      rw [hH.2 z hzV] at this
      unfold dST at this ⊢
      simp [Ne.symm hsw, hzt] at this ⊢
      omega
    · have hoff : ¬ (ew.p = z ∨ ew.q = z) := by
        rcases hew with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2] <;> rintro (h | h) <;>
          first | exact hzt h.symm | exact hzw h.symm
      rw [DF.deg_erase_off hewH hoff, hH.2 z hzV]
      unfold dST; simp [hzt, hzw]
  · have walk : ∀ x ∈ V.erase t, ∀ y, Conn H x y → (y ≠ t → Conn H' x y) ∧ (y = t → Conn H' x w) := by
      intro x hx y hxy
      have hxt : x ≠ t := (Finset.mem_erase.1 hx).1
      induction hxy with
      | refl => exact ⟨fun _ => Conn.refl _ _, fun h => absurd h hxt⟩
      | @tail y z _ hyz ih =>
        obtain ⟨e, he, hends⟩ := hyz
        by_cases hee : e = ew
        · subst hee
          rcases hew with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases hends with ⟨a, b⟩ | ⟨a, b⟩ <;>
            rw [h1] at a <;> rw [h2] at b <;> subst a <;> subst b
          all_goals first
            | exact ⟨fun _ => ih.2 rfl, fun h => absurd h htw⟩
            | exact ⟨fun _ => ih.2 rfl, fun h => absurd h.symm htw⟩
            | exact ⟨fun h => absurd rfl h, fun _ => ih.1 htw⟩
            | exact ⟨fun h => absurd rfl h, fun _ => ih.1 (Ne.symm htw)⟩
        · have heH : e ∈ H' := Finset.mem_erase.2 ⟨hee, he⟩
          have hn := offt e heH
          push Not at hn
          have hyt : y ≠ t := by rcases hends with ⟨a, _⟩ | ⟨_, b⟩; exacts [a ▸ hn.1, b ▸ hn.2]
          have hzt : z ≠ t := by rcases hends with ⟨_, b⟩ | ⟨a, _⟩; exacts [b ▸ hn.2, a ▸ hn.1]
          exact ⟨fun _ => (ih.1 hyt).trans (Relation.ReflTransGen.single ⟨e, heH, hends⟩),
            fun h => absurd h hzt⟩
    have hw' : w ∈ V.erase t := Finset.mem_erase.2 ⟨Ne.symm htw, hwV⟩
    refine ncomp_one_of_conn hw' (fun x hx y hy => ?_)
    have hyt : y ≠ t := (Finset.mem_erase.1 hy).1
    exact (walk x hx y (conn_of_ncomp_one hHam (Finset.mem_of_mem_erase hx)
      (Finset.mem_of_mem_erase hy))).1 hyt

-- **And conversely**: adding `t` back with the edge `ew`.
--
lemma delete_up (hst : s ≠ t) (hsw : s ≠ w) {H' : Finset Edge}
    (hH : IsFactor (V.erase t) (dST s w) H') (hHam : ncomp (V.erase t) H' = 1) :
    IsFactor V (dST s t) (insert ew H') ∧ ncomp V (insert ew H') = 1 ∧ ew ∈ insert ew H' := by
  have htw : t ≠ w := by
    have hpq : ew.p ≠ ew.q := by
      obtain ⟨dir, ⟨x, y⟩⟩ := ew; cases dir <;> simp [Edge.q]
    rcases hew with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [← h1, ← h2]; exact hpq
    · rw [← h1, ← h2]; exact Ne.symm hpq
  have hendT : ew.p = t ∨ ew.q = t := by rcases hew with ⟨h, _⟩ | ⟨_, h⟩; exacts [Or.inl h, Or.inr h]
  have hendW : ew.p = w ∨ ew.q = w := by rcases hew with ⟨_, h⟩ | ⟨h, _⟩; exacts [Or.inr h, Or.inl h]
  have hin : Inside (V.erase t) H' := fun e he => hH.1 e he
  have hnot : ew ∉ H' := fun h => by
    have := hin ew h
    rcases hendT with h' | h'
    · exact (Finset.mem_erase.1 (h' ▸ this.1)).1 rfl
    · exact (Finset.mem_erase.1 (h' ▸ this.2)).1 rfl
  refine ⟨⟨fun e he => ?_, fun z hz => ?_⟩, ?_, Finset.mem_insert_self _ _⟩
  · rcases Finset.mem_insert.1 he with rfl | he
    · rcases hew with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact ⟨h1 ▸ htV, h2 ▸ hwV⟩
      · exact ⟨h1 ▸ hwV, h2 ▸ htV⟩
    · obtain ⟨a, b⟩ := hH.1 e he
      exact ⟨Finset.mem_of_mem_erase a, Finset.mem_of_mem_erase b⟩
  · by_cases hzt : z = t
    · subst hzt
      rw [DF.deg_insert_end hnot hendT]
      have : deg H' z = 0 := by
        unfold deg ind
        have h1 : eR z ∉ H' := fun h => (Finset.mem_erase.1 (hin _ h).1).1 rfl
        have h2 : eL z ∉ H' := fun h => by
          have h' : z ∈ V.erase z := by have := (hin _ h).2; simp [eL] at this
          exact (Finset.mem_erase.1 h').1 rfl
        have h3 : eU z ∉ H' := fun h => (Finset.mem_erase.1 (hin _ h).1).1 rfl
        have h4 : eD z ∉ H' := fun h => by
          have h' : z ∈ V.erase z := by have := (hin _ h).2; simp [eD] at this
          exact (Finset.mem_erase.1 h').1 rfl
        simp [h1, h2, h3, h4]
      rw [this]; unfold dST; simp
    · have hz' : z ∈ V.erase t := Finset.mem_erase.2 ⟨hzt, hz⟩
      by_cases hzw : z = w
      · subst hzw
        rw [DF.deg_insert_end hnot hendW, hH.2 z hz']
        unfold dST; simp [Ne.symm hsw, hzt]
      · have hoff : ¬ (ew.p = z ∨ ew.q = z) := by
          rcases hew with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2] <;> rintro (h | h) <;>
            first | exact hzt h.symm | exact hzw h.symm
        rw [DF.deg_insert_off hnot hoff, hH.2 z hz']
        unfold dST; simp [hzt, hzw]
  · refine ncomp_one_of_conn htV (fun x hx y hy => ?_)
    have hwt : Conn (insert ew H') t w := by
      refine Relation.ReflTransGen.single ⟨ew, Finset.mem_insert_self _ _, ?_⟩
      rcases hew with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl ⟨h1, h2⟩
      · exact Or.inr ⟨h1, h2⟩
    have hsub : H' ⊆ insert ew H' := Finset.subset_insert _ _
    have hw' : w ∈ V.erase t := Finset.mem_erase.2 ⟨Ne.symm htw, hwV⟩
    have toW : ∀ z ∈ V, Conn (insert ew H') z w := by
      intro z hz
      by_cases hzt : z = t
      · subst hzt; exact hwt
      · exact (conn_of_ncomp_one hHam (Finset.mem_erase.2 ⟨hzt, hz⟩) hw').mono hsub
    exact (toW x hx).trans (toW y hy).symm

end delete

end HP

end ULHC
