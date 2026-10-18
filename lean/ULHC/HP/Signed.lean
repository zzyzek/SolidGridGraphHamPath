/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
import ULHC.HP.TheoremAPF

/-!
# The sign of `D` after the fence flip (notes O32)

`fence_signed`: let `R` be the cells with an arc path to `b`, all cells of the graph, and
`D F H b ≤ -2` (`H` lower than `F` at `b`). After flipping `R`, `D ≤ 0` on every cell of `R` and
on every cell outside `R` that shares a side with a cell of `R`. Unlike `after_fence_strip`, no
special `H` is needed: this holds for every `H` lower than `F` at `b`.
-/

namespace ULHC

open Finset Classical

namespace HP

theorem fence_signed {V : Finset Pt} {d : Pt → ℕ} {F H : Finset Edge}
    (hF : IsFactor V d F) (hH : IsFactor V d H) {b : Pt}
    (hall : ∀ c, AncP F b c → IsCell V c) (hDb : D F H b ≤ -2) :
    let R := (cells V).filter (AncP F b)
    (∀ c ∈ R, D (rflip F R) H c ≤ 0) ∧
      (∀ c, c ∉ R → ∀ c'' ∈ R, ∀ sd : Side, nb c'' sd = c → D (rflip F R) H c ≤ 0) := by
  intro R
  obtain ⟨_, _, hcl, _, _⟩ := smallest_fence hF hall
  have hO := outR_of_closed hcl
  have memR : ∀ c, c ∈ R ↔ AncP F b c := by
    intro c; simp only [R, Finset.mem_filter, mem_cells]
    exact ⟨fun h => h.2, fun h => ⟨hall c h, h⟩⟩
  refine ⟨fun c hc => ?_, fun c hc c'' hc'' sd hnb => ?_⟩
  · rw [D_rflip hO c]; unfold rin
    have := D_le_anc hF hH ((memR c).1 hc)
    split_ifs <;> omega
  · rw [D_rflip hO c]; unfold rin
    rw [ite_eq_right_iff.2 (fun h => absurd h hc), mul_zero, add_zero]
    -- The arc between `c''` and `c` points out of `R`, so `D` rises from `c''` to `c` by 0 or 2.
    have hout : outArc F c'' sd = true := by
      by_contra h
      simp only [Bool.not_eq_true] at h
      exact hc (hcl c'' hc'' c ⟨sd, hnb, h⟩)
    have hstep := D_step hF hH c'' sd
    rw [hout] at hstep
    simp only [ite_true] at hstep
    rw [hnb] at hstep
    have hle := D_le_anc hF hH ((memR c'').1 hc'')
    split_ifs at hstep <;> omega

end HP

end ULHC
