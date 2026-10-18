/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
import ULHC.HP.Sheffield.SPhaseAlg

/-!
# S4: undoing the bridges (docs/S4_UNDO.md, Part I)

* `step_rel`: before a bridge step, a connection is one after it with the flipped square's
  `β = back1 E`, `φ = front1 E` merged (`merge`, Rank.lean).
* Joiners: odd strips `(c, a, n)`, applied by `flipCol`. An edge that is a side of an even number
  of the strip's cells keeps its status (`joinKeep`).
* `join_count`: a joiner whose pattern holds and whose end pairs are apart lowers the count by one
  and merges the two classes (from `strip_odd_pf`).
-/

namespace ULHC

namespace HP

open Finset Classical

section undo

variable {V W : Finset Pt} {d : Pt → ℕ} {H : Finset Edge}

-- **The step relation.**
--
theorem step_rel {b : Bridge} (hrs : RowStep V H b)
    (hdegc : ∀ f, IsCell V f → ∀ z, IsCorner z f → deg H z = 2) (x y : Pt) :
    Conn H x y ↔ merge (Conn (flip H b.E)) (back1 b.E b.a) (front1 b.E b.a) x y := by
  obtain ⟨Fl1, Fl2, Fbk, Ffr, _, _, Fun⟩ := rowStep_pre hrs hdegc
  have hres : flip H b.E = (mkLat b.E b.a).res H :=
    (mkLat b.E b.a).flip_eq (mkLat_cellE b.E b.a) Fl1 Fl2 Fbk Ffr
  have hsame : Conn H (mkLat b.E b.a).a (mkLat b.E b.a).d :=
    conn_of_uncut Fun (isCorner_back1 _ _) (isCorner_back2 _ _)
  rw [split_rel_pf (mkLat b.E b.a) Fl1 Fl2 hsame x y, hres]
  rfl

structure Join where
  c : Pt
  a : Side
  n : ℕ

def Join.apply (G : Finset Edge) (o : Join) : Finset Edge := flipCol G o.c o.a o.n

-- An edge toggled by a joiner: a side of an odd number of its cells.
--
def Join.tog (o : Join) (e : Edge) : Prop := nOn o.c o.a o.n e % 2 = 1

lemma joinKeep {G : Finset Edge} {o : Join} {e : Edge} (h : ¬ o.tog e) :
    e ∈ o.apply G ↔ e ∈ G := by
  unfold Join.apply; rw [mem_flipCol]
  unfold Join.tog at h
  constructor
  · intro h'; exact h'.2 (by omega)
  · intro h'; exact ⟨fun _ => by omega, fun _ => h'⟩

end undo

section mergeAlg

variable {R : Pt → Pt → Prop}

lemma merge_le {S : Pt → Pt → Prop} (hS : IsEqv S) (hRS : ∀ x y, R x y → S x y) {a b : Pt}
    (hab : S a b) {x y : Pt} (h : merge R a b x y) : S x y := by
  rcases h with h | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact hRS _ _ h
  · exact hS.trans (hS.trans (hRS _ _ h1) hab) (hRS _ _ h2)
  · exact hS.trans (hS.trans (hRS _ _ h1) (hS.symm hab)) (hRS _ _ h2)

lemma merge_self (hR : IsEqv R) (a b : Pt) : merge R a b a b :=
  Or.inr (Or.inl ⟨hR.refl a, hR.refl b⟩)

lemma merge_comm2 (hR : IsEqv R) (a b c d x y : Pt) :
    merge (merge R a b) c d x y ↔ merge (merge R c d) a b x y := by
  have key : ∀ a b c d x y, merge (merge R a b) c d x y → merge (merge R c d) a b x y := by
    intro a b c d x y h
    have hN := (hR.merge c d).merge a b
    exact merge_le hN (fun x y h' => merge_le hN (fun x y h'' => Or.inl (Or.inl h''))
      (merge_self (hR.merge c d) a b) h') (Or.inl (merge_self hR c d)) h
  exact ⟨key a b c d x y, key c d a b x y⟩

lemma merge_congr (hR : IsEqv R) {a b a' b' : Pt} (ha : R a a') (hb : R b b') (x y : Pt) :
    merge R a b x y ↔ merge R a' b' x y := by
  constructor
  · intro h
    have hS := hR.merge a' b'
    exact merge_le hS (fun x y h => Or.inl h)
      (hS.trans (Or.inl ha) (hS.trans (merge_self hR a' b') (Or.inl (hR.symm hb)))) h
  · intro h
    have hS := hR.merge a b
    exact merge_le hS (fun x y h => Or.inl h)
      (hS.trans (Or.inl (hR.symm ha)) (hS.trans (merge_self hR a b) (Or.inl hb))) h

lemma merge_of_rel (hR : IsEqv R) {a b : Pt} (hab : R a b) (x y : Pt) : merge R a b x y ↔ R x y :=
  ⟨fun h => merge_le hR (fun _ _ h => h) hab h, fun h => Or.inl h⟩

lemma merge_on {S : Pt → Pt → Prop} {P : Pt → Prop}
    (h : ∀ x y, P x → P y → (R x y ↔ S x y)) {a b x y : Pt} (ha : P a) (hb : P b) (hx : P x)
    (hy : P y) : merge R a b x y ↔ merge S a b x y := by
  unfold merge
  rw [h x y hx hy, h x a hx ha, h b y hb hy, h x b hx hb, h a y ha hy]

end mergeAlg

lemma flip_flip (G : Finset Edge) (c : Pt) : flip (flip G c) c = G := by
  unfold flip; rw [symmDiff_symmDiff_cancel_right]

end HP

end ULHC
