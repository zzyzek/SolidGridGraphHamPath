/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
import SolidGridHam.Path.Agree

/-!
# Lemma 2 with a budget: pieces lost to a list of joins

Sheffield's final count (§4.8, repaired in docs/STUCK_MINIMAL.md §16): if every edge of `H'` stays
inside a piece of `H`, or joins two pieces that a list `P` of `r` extra joins already connects,
then `H'` has at least `pieces(H) − r` pieces.

The extra joins are pairs of points, not grid edges, so the count works with relations: `nclass V R`
counts the classes `{y ∈ V | R x y}`, `x ∈ V`, of an equivalence `R`; `ncomp V H = nclass V (Conn H)`.
One extra join `a ~ b` (`merge R a b`) lowers the count by at most one.
-/

namespace SolidGridHam

namespace HP

open Finset Classical

noncomputable def nclass (V : Finset Pt) (R : Pt → Pt → Prop) : ℕ :=
  (V.image (fun x => V.filter (R x))).card

-- `R` with one extra join `a ~ b`.
--
def merge (R : Pt → Pt → Prop) (a b : Pt) (x y : Pt) : Prop :=
  R x y ∨ (R x a ∧ R b y) ∨ (R x b ∧ R a y)

-- `R` with every join of a list.
--
def mergeL (R : Pt → Pt → Prop) : List (Pt × Pt) → Pt → Pt → Prop
  | [] => R
  | q :: P => merge (mergeL R P) q.1 q.2

structure IsEqv (R : Pt → Pt → Prop) : Prop where
  refl : ∀ x, R x x
  symm : ∀ {x y}, R x y → R y x
  trans : ∀ {x y z}, R x y → R y z → R x z

section rank

variable {V : Finset Pt}

lemma IsEqv.merge {R : Pt → Pt → Prop} (h : IsEqv R) (a b : Pt) : IsEqv (merge R a b) where
  refl x := Or.inl (h.refl x)
  symm := by
    rintro x y (hxy | ⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact Or.inl (h.symm hxy)
    · exact Or.inr (Or.inr ⟨h.symm h2, h.symm h1⟩)
    · exact Or.inr (Or.inl ⟨h.symm h2, h.symm h1⟩)
  trans := by
    rintro x y z (hxy | ⟨h1, h2⟩ | ⟨h1, h2⟩) (hyz | ⟨h3, h4⟩ | ⟨h3, h4⟩)
    · exact Or.inl (h.trans hxy hyz)
    · exact Or.inr (Or.inl ⟨h.trans hxy h3, h4⟩)
    · exact Or.inr (Or.inr ⟨h.trans hxy h3, h4⟩)
    · exact Or.inr (Or.inl ⟨h1, h.trans h2 hyz⟩)
    · exact Or.inr (Or.inl ⟨h1, h4⟩)
    · exact Or.inl (h.trans h1 h4)
    · exact Or.inr (Or.inr ⟨h1, h.trans h2 hyz⟩)
    · exact Or.inl (h.trans h1 h4)
    · exact Or.inr (Or.inr ⟨h1, h4⟩)

lemma IsEqv.mergeL {R : Pt → Pt → Prop} (h : IsEqv R) : ∀ P, IsEqv (HP.mergeL R P)
  | [] => h
  | q :: P => (IsEqv.mergeL h P).merge q.1 q.2

lemma ncomp_eq_nclass (F : Finset Edge) : ncomp V F = nclass V (Conn F) := rfl

lemma isEqv_conn (F : Finset Edge) : IsEqv (Conn F) :=
  ⟨Conn.refl _, fun h => h.symm, fun h1 h2 => h1.trans h2⟩

-- One extra join lowers the count by at most one.
--
lemma nclass_merge {R : Pt → Pt → Prop} (hR : IsEqv R) (a b : Pt) :
    nclass V R ≤ nclass V (merge R a b) + 1 := by
  unfold nclass
  set R' := merge R a b
  set A := V.filter (R a)
  set g : Finset Pt → Finset Pt := fun C => V.filter (fun y => ∃ x ∈ C, R' x y)
  have hg : ∀ x ∈ V, g (V.filter (R x)) = V.filter (R' x) := by
    intro x hx
    ext y
    simp only [g, Finset.mem_filter]
    constructor
    · rintro ⟨hy, z, ⟨_, hxz⟩, hzy⟩
      exact ⟨hy, (hR.merge a b).trans (Or.inl hxz) hzy⟩
    · rintro ⟨hy, hxy⟩
      exact ⟨hy, x, ⟨hx, hR.refl x⟩, hxy⟩
  have hinj : Set.InjOn g ((V.image (fun x => V.filter (R x))).erase A) := by
    intro C1 h1 C2 h2 heq
    simp only [Finset.coe_erase, Set.mem_sdiff, Finset.mem_coe, Finset.mem_image,
      Set.mem_singleton_iff] at h1 h2
    obtain ⟨⟨x1, hx1, rfl⟩, hA1⟩ := h1
    obtain ⟨⟨x2, hx2, rfl⟩, hA2⟩ := h2
    rw [hg x1 hx1, hg x2 hx2] at heq
    have h12 : R' x1 x2 := by
      have : x2 ∈ V.filter (R' x1) := by
        rw [heq]; exact Finset.mem_filter.2 ⟨hx2, (hR.merge a b).refl x2⟩
      exact (Finset.mem_filter.1 this).2
    have clsEq : ∀ {u v : Pt}, R u v → V.filter (R u) = V.filter (R v) := by
      intro u v huv; ext z; simp only [Finset.mem_filter]
      exact ⟨fun ⟨hz, h⟩ => ⟨hz, hR.trans (hR.symm huv) h⟩,
        fun ⟨hz, h⟩ => ⟨hz, hR.trans huv h⟩⟩
    rcases h12 with h | ⟨ha, _⟩ | ⟨_, ha⟩
    · exact clsEq h
    · exact absurd (clsEq ha) hA1
    · exact absurd (clsEq (hR.symm ha)) hA2
  have hmaps : Set.MapsTo g ((V.image (fun x => V.filter (R x))).erase A)
      (V.image (fun x => V.filter (R' x))) := by
    intro C hC
    simp only [Finset.coe_erase, Set.mem_sdiff, Finset.mem_coe, Finset.mem_image] at hC
    obtain ⟨⟨x, hx, rfl⟩, _⟩ := hC
    simp only [Finset.mem_coe, Finset.mem_image]
    exact ⟨x, hx, (hg x hx).symm⟩
  have := Finset.card_le_card_of_injOn g hmaps hinj
  have h2 := Finset.pred_card_le_card_erase (s := V.image (fun x => V.filter (R x))) (a := A)
  omega

lemma nclass_mergeL {R : Pt → Pt → Prop} (hR : IsEqv R) :
    ∀ P : List (Pt × Pt), nclass V R ≤ nclass V (HP.mergeL R P) + P.length
  | [] => by simp [HP.mergeL]
  | q :: P => by
    have h1 := nclass_mergeL hR P
    have h2 := nclass_merge (V := V) (hR.mergeL P) q.1 q.2
    simp only [HP.mergeL, List.length_cons]
    omega

-- A finer equivalence has more classes.
--
lemma nclass_le_of_imp {R S : Pt → Pt → Prop} (hS : IsEqv S) (hRS : ∀ x y, R x y → S x y)
    (hR : IsEqv R) : nclass V S ≤ nclass V R := by
  unfold nclass
  have hsurj : V.image (fun x => V.filter (S x)) = (V.image (fun x => V.filter (R x))).image
      (fun C => V.filter (fun z => ∃ x ∈ C, S x z)) := by
    rw [Finset.image_image]
    apply Finset.image_congr
    intro x hx
    ext z
    simp only [Function.comp, Finset.mem_filter]
    constructor
    · rintro ⟨hz, hc⟩; exact ⟨hz, x, ⟨hx, hR.refl x⟩, hc⟩
    · rintro ⟨hz, w, ⟨_, hxw⟩, hwz⟩; exact ⟨hz, hS.trans (hRS _ _ hxw) hwz⟩
  rw [hsurj]
  exact Finset.card_image_le

-- **Lemma 2 with a budget.** If every edge of `H'` joins points already joined by `H` and the
-- extra joins `P`, then `H'` has at least `pieces(H) − |P|` pieces.
--
theorem ncomp_le_of_joins {H H' : Finset Edge} (P : List (Pt × Pt))
    (hin : ∀ e ∈ H', HP.mergeL (Conn H) P e.p e.q) :
    ncomp V H ≤ ncomp V H' + P.length := by
  have hE := (isEqv_conn H).mergeL P
  have himp : ∀ x y, Conn H' x y → HP.mergeL (Conn H) P x y := by
    intro x y h
    induction h with
    | refl => exact hE.refl _
    | tail _ hab ih =>
      obtain ⟨e, he, hends⟩ := hab
      have hc := hin e he
      rcases hends with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [h1, h2] at hc; exact hE.trans ih hc
      · rw [h1, h2] at hc; exact hE.trans ih (hE.symm hc)
  have h1 := nclass_mergeL (V := V) (isEqv_conn H) P
  have h2 := nclass_le_of_imp (V := V) hE himp (isEqv_conn H')
  rw [ncomp_eq_nclass, ncomp_eq_nclass]
  omega

end rank

end HP

end SolidGridHam
