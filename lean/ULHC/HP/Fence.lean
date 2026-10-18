/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
import ULHC.HP.RegionFlip
import ULHC.Dual

/-!
# The smallest fence (notes P15)

`ArcTo F q c`: `F`'s arc between neighbouring cells `q` and `c` points from `q` into `c`.
`AncP F b c`: an arc path leads from `c` to `b`. `R` = the cells with an arc path to `b`.

`smallest_fence`: if every cell with an arc path to `b` is a cell of the graph, then flipping
`R` gives a factor with the same degrees; for every `H` with `D F H b ≤ -2` (in the notes'
terms, `H` lower than `F` at `b`), `μ` drops by `2 |R|`; and `R` lies inside every set of
cells containing `b` that no arc enters from outside. The proof uses only that `D` never
decreases along an arc (so every cell of `R` has `D ≤ D b`) and `D_rflip`.
-/

namespace ULHC

open Finset Classical

namespace HP

def ArcTo (F : Finset Edge) (q c : Pt) : Prop := ∃ s, nb c s = q ∧ outArc F c s = false

def AncP (F : Finset Edge) (b c : Pt) : Prop := Relation.ReflTransGen (ArcTo F) c b

def InClosed (F : Finset Edge) (R : Finset Pt) : Prop := ∀ c ∈ R, ∀ q, ArcTo F q c → q ∈ R

-- `D` never decreases along an arc.
--
lemma D_arc {V : Finset Pt} {d : Pt → ℕ} {F H : Finset Edge} (hF : IsFactor V d F)
    (hH : IsFactor V d H) {q c : Pt} (h : ArcTo F q c) : D F H q ≤ D F H c := by
  obtain ⟨s, rfl, ho⟩ := h
  have := D_step hF hH c s
  rw [ho] at this
  simp only [Bool.false_eq_true, ite_false] at this
  split_ifs at this <;> omega

lemma D_le_anc {V : Finset Pt} {d : Pt → ℕ} {F H : Finset Edge} (hF : IsFactor V d F)
    (hH : IsFactor V d H) {b c : Pt} (h : AncP F b c) : D F H c ≤ D F H b := by
  induction h with
  | refl => exact le_rfl
  | tail _ hyz ih => exact ih.trans (D_arc hF hH hyz)

-- No arc entering from outside means every boundary arc points out.
--
lemma outR_of_closed {F : Finset Edge} {R : Finset Pt} (hcl : InClosed F R) : OutR F R := by
  intro e he
  have hx := mem_bnd.1 he
  obtain ⟨dd, p⟩ := e
  cases dd
  · -- horizontal: low cell below, high cell `p` above; `e = bot p = top lo`.
    have hlo : (⟨.h, p⟩ : Edge).lo = (p.1, p.2 - 1) := rfl
    have htop : top (p.1, p.2 - 1) = ⟨.h, p⟩ := by simp [top]
    have a1 : outArc F p .b = ! up F ⟨.h, p⟩ := rfl
    have a2 : outArc F (p.1, p.2 - 1) .t = up F ⟨.h, p⟩ := by
      show up F (top (p.1, p.2 - 1)) = _; rw [htop]
    rw [hlo] at hx ⊢
    by_cases hl : (p.1, p.2 - 1) ∈ R
    · have hh : p ∉ R := by intro h; simp [hl, h, Edge.hi] at hx
      simp only [hl, decide_true]
      by_contra hu
      simp only [Bool.not_eq_true] at hu
      exact hh (hcl _ hl p ⟨.t, by simp [nb], by rw [a2, hu]⟩)
    · have hh : p ∈ R := by by_contra h; simp [hl, h, Edge.hi] at hx
      simp only [hl, decide_false]
      by_contra hu
      simp only [Bool.not_eq_false] at hu
      exact hl (hcl _ hh _ ⟨.b, rfl, by rw [a1, hu]; rfl⟩)
  · -- vertical: low cell to the left, high cell `p` to the right; `e = lft p = rgt lo`.
    have hlo : (⟨.v, p⟩ : Edge).lo = (p.1 - 1, p.2) := rfl
    have hrgt : rgt (p.1 - 1, p.2) = ⟨.v, p⟩ := by simp [rgt]
    have a1 : outArc F p .l = ! up F ⟨.v, p⟩ := rfl
    have a2 : outArc F (p.1 - 1, p.2) .r = up F ⟨.v, p⟩ := by
      show up F (rgt (p.1 - 1, p.2)) = _; rw [hrgt]
    rw [hlo] at hx ⊢
    by_cases hl : (p.1 - 1, p.2) ∈ R
    · have hh : p ∉ R := by intro h; simp [hl, h, Edge.hi] at hx
      simp only [hl, decide_true]
      by_contra hu
      simp only [Bool.not_eq_true] at hu
      exact hh (hcl _ hl p ⟨.r, by simp [nb], by rw [a2, hu]⟩)
    · have hh : p ∈ R := by by_contra h; simp [hl, h, Edge.hi] at hx
      simp only [hl, decide_false]
      by_contra hu
      simp only [Bool.not_eq_false] at hu
      exact hl (hcl _ hh _ ⟨.l, rfl, by rw [a1, hu]; rfl⟩)

lemma isEdge_of_cellE {V : Finset Pt} {c : Pt} (hc : IsCell V c) {e : Edge} (he : e ∈ cellE c) :
    IsEdge V e := by
  simp only [cellE, Finset.mem_insert, Finset.mem_singleton] at he
  rcases he with rfl | rfl | rfl | rfl
  · exact isEdge_side hc .b
  · exact isEdge_side hc .t
  · exact isEdge_side hc .l
  · exact isEdge_side hc .r

-- **The smallest fence (P15).**
--
theorem smallest_fence {V : Finset Pt} {d : Pt → ℕ} {F : Finset Edge} (hF : IsFactor V d F)
    {b : Pt} (hall : ∀ c, AncP F b c → IsCell V c) :
    let R := (cells V).filter (AncP F b)
    IsFactor V d (rflip F R) ∧ b ∈ R ∧ InClosed F R ∧
      (∀ R' : Finset Pt, InClosed F R' → b ∈ R' → R ⊆ R') ∧
      ∀ H, IsFactor V d H → D F H b ≤ -2 → mu V (rflip F R) H + 2 * R.card = mu V F H := by
  intro R
  have memR : ∀ c, c ∈ R ↔ AncP F b c := by
    intro c; simp only [R, Finset.mem_filter, mem_cells]
    exact ⟨fun h => h.2, fun h => ⟨hall c h, h⟩⟩
  have hcl : InClosed F R := by
    intro c hc q hq
    rw [memR] at hc ⊢
    exact Relation.ReflTransGen.head hq hc
  have hO := outR_of_closed hcl
  have hbR : b ∈ R := (memR b).2 Relation.ReflTransGen.refl
  refine ⟨⟨fun e he => ?_, fun p hp => by rw [deg_rflip hO]; exact hF.2 p hp⟩, hbR, hcl, ?_, ?_⟩
  · -- edges of the flipped set are graph edges
    unfold rflip at he
    rcases Finset.mem_symmDiff.1 he with ⟨h, _⟩ | ⟨h, _⟩
    · exact hF.1 e h
    · unfold bnd at h
      obtain ⟨c, hc, hce⟩ := Finset.mem_biUnion.1 (Finset.mem_filter.1 h).1
      exact isEdge_of_cellE (hall c ((memR c).1 hc)) hce
  · -- minimality
    intro R' hcl' hb' c hc
    have hp := (memR c).1 hc
    unfold AncP at hp
    induction hp using Relation.ReflTransGen.head_induction_on with
    | refl => exact hb'
    | head hxy _ ih => exact hcl' _ (ih ((memR _).2 (by assumption))) _ hxy
  · -- `μ` drops by `2 |R|`
    intro H hH hb
    have hsub : R ⊆ cells V := Finset.filter_subset _ _
    have key : ∀ c ∈ cells V, (D (rflip F R) H c).natAbs + 2 * (if c ∈ R then 1 else 0) =
        (D F H c).natAbs := by
      intro c _
      rw [D_rflip hO c]
      unfold rin
      by_cases hc : c ∈ R
      · have := D_le_anc hF hH ((memR c).1 hc)
        simp only [hc, ite_true]; omega
      · simp only [hc, ite_false]; omega
    unfold mu
    rw [← Finset.sum_congr rfl key, Finset.sum_add_distrib, ← Finset.mul_sum,
      Finset.sum_boole, Finset.filter_mem_eq_inter, Finset.inter_eq_right.2 hsub]
    simp

end HP

end ULHC
