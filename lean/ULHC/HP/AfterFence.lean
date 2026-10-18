/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
import ULHC.HP.Fence

/-!
# After the fence flip (notes P19)

`D_const_at`: if `F` and `H` use the same edges at `t`, then `D F H` is the same on the four
cells around `t` (moving between them crosses only `t`'s edges).

`after_fence_strip`: let `b` be a cell around `t`, `R` the smallest fence at `b` (cells with an
arc path to `b`), and `F'` the factor after flipping `R`. If `D F H b = -2` (in the notes'
terms, `H` one step lower than `F` at `b`), `F'` and `H` use the same edges at `t`, and `s` is a
corner of no cell (`s` on a tail one vertex wide), then `D F' H` vanishes on every cell with an
endpoint as a corner, and Lemma B gives a strip of `F'` avoiding `s` and `t` that lowers `μ`
and keeps or lowers the count (provided `F'` has no Type III cell and two or more components).
-/

namespace ULHC

open Finset Classical

namespace HP

lemma wD_zero_of_agree {F H : Finset Edge} {e : Edge} (h : e ∈ F ↔ e ∈ H) : wD F H e = 0 := by
  unfold wD wb
  by_cases h1 : e ∈ F
  · have h2 := h.1 h1; simp [h1, h2]
  · have h2 : e ∉ H := fun h' => h1 (h.2 h'); simp [h1, h2]

-- `D` is the same on the four cells around `t` when `F` and `H` agree on `t`'s edges.
--
theorem D_const_at {V : Finset Pt} {d : Pt → ℕ} {F H : Finset Edge}
    (hF : IsFactor V d F) (hH : IsFactor V d H) {t : Pt}
    (hag : ∀ e, (e = eR t ∨ e = eL t ∨ e = eU t ∨ e = eD t) → (e ∈ F ↔ e ∈ H)) :
    D F H (t.1 - 1, t.2) = D F H t ∧ D F H (t.1, t.2 - 1) = D F H t ∧
      D F H (t.1 - 1, t.2 - 1) = D F H t := by
  obtain ⟨x, y⟩ := t
  have jU := D_jump hF hH (eU (x, y))
  have jR := D_jump hF hH (eR (x, y))
  have jL := D_jump hF hH (eL (x, y))
  have zU := wD_zero_of_agree (F := F) (H := H) (hag _ (Or.inr (Or.inr (Or.inl rfl))))
  have zR := wD_zero_of_agree (F := F) (H := H) (hag _ (Or.inl rfl))
  have zL := wD_zero_of_agree (F := F) (H := H) (hag _ (Or.inr (Or.inl rfl)))
  simp only [eU, eR, eL, Edge.hi, Edge.lo] at jU jR jL zU zR zL
  rw [zU] at jU; rw [zR] at jR; rw [zL] at jL
  show D F H (x - 1, y) = D F H (x, y) ∧ D F H (x, y - 1) = D F H (x, y) ∧
    D F H (x - 1, y - 1) = D F H (x, y)
  refine ⟨by omega, by omega, by omega⟩

lemma isCorner_cases {t w : Pt} (h : IsCorner t w) :
    w = t ∨ w = (t.1 - 1, t.2) ∨ w = (t.1, t.2 - 1) ∨ w = (t.1 - 1, t.2 - 1) := by
  obtain ⟨x, y⟩ := t
  obtain ⟨a, c⟩ := w
  unfold IsCorner at h
  simp only [Prod.mk.injEq] at h ⊢
  omega

-- **After the fence flip (P19).**
--
theorem after_fence_strip {V : Finset Pt} {d : Pt → ℕ} {F H : Finset Edge} (hs : Solid V)
    (hF : IsFactor V d F) (hH : IsFactor V d H) (hHam : ncomp V H = 1) {s t b : Pt}
    (hd : ∀ z, z ≠ s → z ≠ t → d z = 2) (hds : d s = 1) (hsV : s ∈ V)
    (hsfree : ∀ w, IsCorner s w → ¬ IsCell V w)
    (hall : ∀ c, AncP F b c → IsCell V c) (hbt : IsCorner t b) (hDb : D F H b = -2)
    (hag : ∀ e, (e = eR t ∨ e = eL t ∨ e = eU t ∨ e = eD t) →
      (e ∈ rflip F ((cells V).filter (AncP F b)) ↔ e ∈ H))
    (hT : NoTypeIII V (rflip F ((cells V).filter (AncP F b))))
    (h2 : 2 ≤ ncomp V (rflip F ((cells V).filter (AncP F b)))) :
    ∃ σ : StripSpec, ValidStrip V (rflip F ((cells V).filter (AncP F b))) σ ∧ 2 ≤ σ.n ∧
      (∀ j < σ.n, ¬ IsCorner s (cellJ σ.c σ.s j) ∧ ¬ IsCorner t (cellJ σ.c σ.s j)) ∧
      ncomp V (applyS (rflip F ((cells V).filter (AncP F b))) σ) ≤
        ncomp V (rflip F ((cells V).filter (AncP F b))) := by
  set R := (cells V).filter (AncP F b) with hRdef
  obtain ⟨hF', hbR, hcl, _, _⟩ := smallest_fence hF hall
  have hO := outR_of_closed hcl
  -- `D F' H` vanishes at `b`, hence on the four cells around `t`.
  have hb0 : D (rflip F R) H b = 0 := by
    rw [D_rflip hO b]; unfold rin; simp [hbR, hDb]
  obtain ⟨c1, c2, c3⟩ := D_const_at hF' hH hag
  have ht0 : D (rflip F R) H t = 0 := by
    rcases isCorner_cases hbt with rfl | rfl | rfl | rfl
    · exact hb0
    · rw [← c1]; exact hb0
    · rw [← c2]; exact hb0
    · rw [← c3]; exact hb0
  have hz : ∀ w, IsCorner s w ∨ IsCorner t w → D (rflip F R) H w = 0 := by
    intro w hw
    rcases hw with hw | hw
    · exact D_eq_zero_of_not_cell hF' hH hs (hsfree w hw)
    · rcases isCorner_cases hw with rfl | rfl | rfl | rfl
      · exact ht0
      · rw [c1]; exact ht0
      · rw [c2]; exact ht0
      · rw [c3]; exact ht0
  obtain ⟨σ, hv, hn, _, hcor, hle, _, _, _⟩ := lemmaB hs hF' hH hHam hd hds hsV hz hT h2
  exact ⟨σ, hv, hn, hcor, hle⟩

end HP

end ULHC
