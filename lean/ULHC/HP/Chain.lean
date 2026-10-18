/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
import ULHC.HP.Signed

/-!
# Fence chains at `t` (notes O37, P22)

A *fence step* at `t` flips the cells with an arc path to one of `t`'s four cells `b`, when all of
them are cells of the graph. It does not depend on any Hamiltonian path.

`fence_chain`: if `D F H ≤ 0` on `t`'s four cells, a chain of fence steps reaches a factor with
`D = 0` on them, and then `theoremA_pf` finishes. The fence at `b` with `D b ≤ -2` raises `D` by 2
exactly on the ancestors of `b`, and every ancestor has `D ≤ D b ≤ -2`, so no cell of `t` rises
above 0 and the sum of `-D` over `t`'s cells drops by at least 2 per step. No special `H` and no
knowledge of which of `t`'s cells each fence covers is needed.
-/

namespace ULHC

open Finset Classical

namespace HP

-- One fence step at `t`.
--
def FenceStep (V : Finset Pt) (t : Pt) (F F' : Finset Edge) : Prop :=
  ∃ b, IsCorner t b ∧ (∀ c, AncP F b c → IsCell V c) ∧
    F' = rflip F ((cells V).filter (AncP F b))

lemma isCorner_four (t : Pt) :
    IsCorner t t ∧ IsCorner t (t.1 - 1, t.2) ∧ IsCorner t (t.1, t.2 - 1) ∧
      IsCorner t (t.1 - 1, t.2 - 1) := by
  obtain ⟨x, y⟩ := t
  unfold IsCorner
  simp

-- The sum of `-D` over `t`'s four cells.
--
def negSumAt (F H : Finset Edge) (t : Pt) : ℤ :=
  -(D F H t + D F H (t.1 - 1, t.2) + D F H (t.1, t.2 - 1) + D F H (t.1 - 1, t.2 - 1))

theorem fence_chain {V : Finset Pt} {d : Pt → ℕ} {H : Finset Edge} (hs : Solid V)
    (hH : IsFactor V d H) (hHam : ncomp V H = 1) {s t : Pt}
    (hd : ∀ z, z ≠ s → z ≠ t → d z = 2) (hds : d s = 1) (hsV : s ∈ V)
    (hsfree : ∀ w, IsCorner s w → ¬ IsCell V w) :
    ∀ F, IsFactor V d F → (∀ w, IsCorner t w → D F H w ≤ 0) →
      ∃ F1, Relation.ReflTransGen (FenceStep V t) F F1 ∧ IsFactor V d F1 ∧
        ∃ F', Relation.ReflTransGen (MovePF V s t) F1 F' ∧ IsFactor V d F' ∧
          (ncomp V F' = 1 ∨
            ∃ c, IsCell V c ∧ (IsCorner s c ∨ IsCorner t c) ∧ ¬ NotTypeIII V F' c) := by
  obtain ⟨k0, k1, k2, k3⟩ := isCorner_four t
  suffices key : ∀ n : ℕ, ∀ F, IsFactor V d F → (∀ w, IsCorner t w → D F H w ≤ 0) →
      negSumAt F H t ≤ n →
      ∃ F1, Relation.ReflTransGen (FenceStep V t) F F1 ∧ IsFactor V d F1 ∧
        ∃ F', Relation.ReflTransGen (MovePF V s t) F1 F' ∧ IsFactor V d F' ∧
          (ncomp V F' = 1 ∨
            ∃ c, IsCell V c ∧ (IsCorner s c ∨ IsCorner t c) ∧ ¬ NotTypeIII V F' c) by
    intro F hF hle
    exact key (negSumAt F H t).toNat F hF hle (Int.self_le_toNat _)
  intro n
  induction n with
  | zero =>
    intro F hF hle hn
    have z0 := hle _ k0; have z1 := hle _ k1; have z2 := hle _ k2; have z3 := hle _ k3
    unfold negSumAt at hn
    have hz : ∀ w, IsCorner s w ∨ IsCorner t w → D F H w = 0 := by
      intro w hw
      rcases hw with hw | hw
      · exact D_eq_zero_of_not_cell hF hH hs (hsfree w hw)
      · rcases isCorner_cases hw with rfl | rfl | rfl | rfl <;> push_cast at hn <;> omega
    exact ⟨F, Relation.ReflTransGen.refl, hF, theoremA_pf hs hH hHam hd hds hsV F hF hz⟩
  | succ n ih =>
    intro F hF hle hn
    -- If `D` already vanishes on `t`'s cells, the bound `0` case applies.
    --
    by_cases hall0 : ∀ w, IsCorner t w → D F H w = 0
    · have z0 := hall0 _ k0; have z1 := hall0 _ k1; have z2 := hall0 _ k2
      have z3 := hall0 _ k3
      exact ih F hF hle (by unfold negSumAt; rw [z0, z1, z2, z3]; push_cast; omega)
    push Not at hall0
    obtain ⟨b, hbt, hbne⟩ := hall0
    have hb2 : D F H b ≤ -2 := by
      have := hle b hbt
      obtain ⟨m, hm⟩ := D_even F H b
      omega
    -- Every ancestor of `b` has `D ≤ -2`, hence is a cell of the graph.
    --
    have hall : ∀ c, AncP F b c → IsCell V c := by
      intro c hc
      by_contra hnc
      have h1 := D_eq_zero_of_not_cell hF hH hs hnc
      have h2 := D_le_anc hF hH hc
      omega
    set R := (cells V).filter (AncP F b) with hRdef
    obtain ⟨hF', hbR, hcl, _, _⟩ := smallest_fence hF hall
    have hO := outR_of_closed hcl
    have memR : ∀ c, c ∈ R ↔ AncP F b c := by
      intro c; simp only [R, Finset.mem_filter, mem_cells]
      exact ⟨fun h => h.2, fun h => ⟨hall c h, h⟩⟩
    -- After the flip, each of `t`'s cells keeps `D ≤ 0`, and `b` rises by 2.
    --
    have hnew : ∀ w, D (rflip F R) H w = D F H w + 2 * rin R w := fun w => D_rflip hO w
    have hle' : ∀ w, IsCorner t w → D (rflip F R) H w ≤ 0 := by
      intro w hw
      rw [hnew w]; unfold rin
      split_ifs with hwR
      · have := D_le_anc hF hH ((memR w).1 hwR); omega
      · have := hle w hw; omega
    have hge : ∀ w, D F H w ≤ D (rflip F R) H w := by
      intro w; rw [hnew w]; unfold rin; split_ifs <;> omega
    have hbup : D (rflip F R) H b = D F H b + 2 := by
      have hbR' : b ∈ R := by rw [hRdef]; exact hbR
      rw [hnew b]; unfold rin; simp only [hbR', ↓reduceIte]; ring
    have hdrop : negSumAt (rflip F R) H t ≤ n := by
      have g0 := hge t; have g1 := hge (t.1 - 1, t.2); have g2 := hge (t.1, t.2 - 1)
      have g3 := hge (t.1 - 1, t.2 - 1)
      unfold negSumAt at hn ⊢
      push_cast at hn
      rcases isCorner_cases hbt with rfl | rfl | rfl | rfl <;> omega
    obtain ⟨F1, hch, rest⟩ := ih (rflip F R) hF' hle' hdrop
    exact ⟨F1, Relation.ReflTransGen.head ⟨b, hbt, hall, rfl⟩ hch, rest⟩

end HP

end ULHC
