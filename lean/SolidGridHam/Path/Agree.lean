/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
module

public import SolidGridHam.Path.Prelim.NotchPF

@[expose] public section

/-!
# Sheffield's Lemma 2: agreement on the cut faces keeps pieces apart

For two factors `H`, `H'` with the same degrees, `D H' H` is the difference of their heights
(`D.lean`). Across an edge where they differ, `D H' H` jumps by `±2` (`D_jump`), so one of the two
faces beside that edge is a face where the heights disagree.

**Lemma 2** (Sheffield, arXiv math/0008231, §4.4): if `H'` agrees with `H` on both faces beside
every edge of `H'` that joins two pieces of `H`, then no edge of `H'` joins two pieces of `H`, so
the pieces of `H'` refine those of `H` and `H'` has at least as many pieces.
-/

namespace SolidGridHam

namespace HP

open Finset Classical

section agree

variable {V : Finset Pt} {d : Pt → ℕ} {H H' : Finset Edge}

-- The weight of an edge on which the two factors differ is nonzero.
--
lemma wD_ne_zero_of_symmDiff {e : Edge} (he : e ∈ symmDiff H' H) : wD H' H e ≠ 0 := by
  rw [Finset.mem_symmDiff] at he
  unfold wD wb
  rcases he with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp [h1, h2] <;> split_ifs <;> simp

-- **The faces beside an edge where two factors differ carry different height differences.**
--
lemma D_ne_of_symmDiff (hH' : IsFactor V d H') (hH : IsFactor V d H) {e : Edge}
    (he : e ∈ symmDiff H' H) : D H' H e.hi ≠ D H' H e.lo := by
  have j := D_jump hH' hH e
  intro h
  rw [h, sub_self] at j
  exact wD_ne_zero_of_symmDiff he j.symm

-- Hence at least one of the two faces is a face where `H'` and `H` disagree (`D ≠ 0`).
--
lemma disagree_beside (hH' : IsFactor V d H') (hH : IsFactor V d H) {e : Edge}
    (he : e ∈ symmDiff H' H) : D H' H e.hi ≠ 0 ∨ D H' H e.lo ≠ 0 := by
  by_contra hn
  push Not at hn
  exact D_ne_of_symmDiff hH' hH he (hn.1.trans hn.2.symm)

-- Pieces of `H'` refine pieces of `H` when every edge of `H'` stays inside a piece of `H`.
--
lemma conn_of_edges_inside {x y : Pt} (hin : ∀ e ∈ H', Conn H e.p e.q) (h : Conn H' x y) :
    Conn H x y := by
  induction h with
  | refl => exact Conn.refl _ _
  | tail _ hab ih =>
    obtain ⟨e, he, hends⟩ := hab
    have hc := hin e he
    rcases hends with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2] at hc; exact ih.trans hc
    · rw [h1, h2] at hc; exact ih.trans hc.symm

-- Finer pieces: more of them.
--
lemma ncomp_le_of_refine {F F' : Finset Edge} (h : ∀ x ∈ V, ∀ y ∈ V, Conn F' x y → Conn F x y) :
    ncomp V F ≤ ncomp V F' := by
  unfold ncomp
  have hsurj : V.image (cls V F) = (V.image (cls V F')).image (fun S => V.filter (fun z =>
      ∃ x ∈ S, Conn F x z)) := by
    rw [Finset.image_image]
    apply Finset.image_congr
    intro x hx
    ext z
    simp only [cls, Function.comp, Finset.mem_filter]
    constructor
    · rintro ⟨hz, hc⟩; exact ⟨hz, x, ⟨hx, Conn.refl _ _⟩, hc⟩
    · rintro ⟨hz, w, ⟨hw, hxw⟩, hwz⟩; exact ⟨hz, (h x hx w hw hxw).trans hwz⟩
  rw [hsurj]
  exact Finset.card_image_le

-- **Sheffield's Lemma 2.** If `H'` agrees with `H` on the two faces beside every edge of `H'`
-- that joins two pieces of `H`, then `H'` has at least as many pieces as `H`.
--
theorem ncomp_le_of_agree (hH' : IsFactor V d H') (hH : IsFactor V d H)
    (hag : ∀ e ∈ H', ¬ Conn H e.p e.q → D H' H e.hi = 0 ∧ D H' H e.lo = 0) :
    ncomp V H ≤ ncomp V H' := by
  have hin : ∀ e ∈ H', Conn H e.p e.q := by
    intro e he
    by_contra hn
    have hs : e ∈ symmDiff H' H := by
      rw [Finset.mem_symmDiff]
      exact Or.inl ⟨he, fun h => hn (Conn.of_edge h)⟩
    obtain ⟨h1, h2⟩ := hag e he hn
    rcases disagree_beside hH' hH hs with h | h
    · exact h h1
    · exact h h2
  exact ncomp_le_of_refine (fun x _ y _ hxy => conn_of_edges_inside hin hxy)

end agree

end HP

end SolidGridHam
