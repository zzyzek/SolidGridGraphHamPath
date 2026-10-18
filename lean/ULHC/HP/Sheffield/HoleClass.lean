/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
import ULHC.HP.Sheffield.SlitHeight

/-!
# One hole: `D` vanishes off the cells within a class (B-1, docs/HOLE_CLASSES.md §2)

`V' = V.erase t` for a solid `V`: every missing point of `V'` is `t` or escapes to the far left
(`hole_escape`). For two factors on `W ⊇ V'` that agree off `V'`, `D` is constant on each king
cluster of missing points, so it vanishes on every non-cell of `V'` as soon as it vanishes at
`t` (`solidFor_hole`).
-/

namespace ULHC

namespace HP

open Finset Classical

section hole

variable {V W : Finset Pt} {d : Pt → ℕ} {F H : Finset Edge} {t : Pt}

lemma hole_escape (hs : Solid V) :
    ∀ b, b ∉ V.erase t → b = t ∨
      ∃ b', Relation.ReflTransGen (MissAdj (V.erase t)) b b' ∧ ∀ p ∈ V.erase t, b'.1 < p.1 := by
  intro b hb
  by_cases hbt : b = t
  · exact Or.inl hbt
  right
  have hbV : b ∉ V := fun h => hb (Finset.mem_erase.2 ⟨hbt, h⟩)
  obtain ⟨b', hch, hleft⟩ := hs b hbV
  refine ⟨b', ?_, fun p hp => hleft p (Finset.mem_of_mem_erase hp)⟩
  have mono : ∀ {x y}, Relation.ReflTransGen (MissAdj V) x y →
      Relation.ReflTransGen (MissAdj (V.erase t)) x y := by
    intro x y h
    induction h with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ hab ih =>
      obtain ⟨h1, h2, h3, h4⟩ := hab
      exact ih.tail ⟨fun h => h1 (Finset.mem_of_mem_erase h),
        fun h => h2 (Finset.mem_of_mem_erase h), h3, h4⟩
  exact mono hch

-- **B-1.** Two factors agreeing off `V.erase t` with `D = 0` at the square `t` have `D = 0` on
-- every non-cell of `V.erase t`.
--
theorem solidFor_hole (hF : IsFactor W d F) (hH : IsFactor W d H)
    (hFH : ∀ e ∈ symmDiff F H, e.p ∈ V.erase t ∧ e.q ∈ V.erase t) (hs : Solid V)
    (h0 : D F H t = 0) : SolidFor (V.erase t) F H := by
  intro c hc
  obtain ⟨x, y⟩ := c
  have corner : ∃ a, a ∉ V.erase t ∧ Around a (x, y) := by
    unfold IsCell at hc
    by_cases h1 : (x, y) ∈ V.erase t
    · by_cases h2 : (x + 1, y) ∈ V.erase t
      · by_cases h3 : (x, y + 1) ∈ V.erase t
        · refine ⟨(x + 1, y + 1), fun h4 => hc ⟨h1, h2, h3, h4⟩, ?_⟩
          simp [Around]
        · exact ⟨(x, y + 1), h3, by simp [Around]⟩
      · exact ⟨(x + 1, y), h2, by simp [Around]⟩
    · exact ⟨(x, y), h1, by simp [Around]⟩
  obtain ⟨a, ha, hac⟩ := corner
  rw [D_aroundW hF hH hFH ha hac]
  rcases hole_escape hs a ha with rfl | ⟨b, hab, hb⟩
  · exact h0
  · rw [D_chainW hF hH hFH hab]
    exact pot_eq_zero_of_left (B := b.1) (fun e he => hb _ (hFH e he).1) b le_rfl


-- **B-1 for a hole cluster.** If every missing point of `U` chains to `t` through missing points
-- or escapes to the far left, then `D = 0` at `t` gives `D = 0` on every non-cell of `U`.
--
theorem solidFor_cluster {U : Finset Pt} (hF : IsFactor W d F) (hH : IsFactor W d H)
    (hFH : ∀ e ∈ symmDiff F H, e.p ∈ U ∧ e.q ∈ U)
    (hesc : ∀ b, b ∉ U → Relation.ReflTransGen (MissAdj U) b t ∨
      ∃ b', Relation.ReflTransGen (MissAdj U) b b' ∧ ∀ p ∈ U, b'.1 < p.1)
    (h0 : D F H t = 0) : SolidFor U F H := by
  intro c hc
  obtain ⟨x, y⟩ := c
  have corner : ∃ a, a ∉ U ∧ Around a (x, y) := by
    unfold IsCell at hc
    by_cases h1 : (x, y) ∈ U
    · by_cases h2 : (x + 1, y) ∈ U
      · by_cases h3 : (x, y + 1) ∈ U
        · refine ⟨(x + 1, y + 1), fun h4 => hc ⟨h1, h2, h3, h4⟩, ?_⟩
          simp [Around]
        · exact ⟨(x, y + 1), h3, by simp [Around]⟩
      · exact ⟨(x + 1, y), h2, by simp [Around]⟩
    · exact ⟨(x, y), h1, by simp [Around]⟩
  obtain ⟨a, ha, hac⟩ := corner
  rw [D_aroundW hF hH hFH ha hac]
  rcases hesc a ha with hat | ⟨b, hab, hb⟩
  · rw [D_chainW hF hH hFH hat]; exact h0
  · rw [D_chainW hF hH hFH hab]
    exact pot_eq_zero_of_left (B := b.1) (fun e he => hb _ (hFH e he).1) b le_rfl

end hole

end HP

end ULHC
