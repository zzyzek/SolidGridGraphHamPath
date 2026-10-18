/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
import ULHC.HP.Chain

/-!
# Descendant fences and fence chains for every `H` (notes P22)

The mirror of `smallest_fence`: let `R` be the cells reachable from `b` along arcs (the
descendants of `b`). No arc leaves `R`, so every boundary arc points into `R`. The flip reverses
every boundary arc, so for `rflip F R` every boundary arc points out, and `deg_rflip`/`D_rflip`
applied to `rflip F R` (an involution) give: degrees are kept and `D` drops by 2 on `R`.

`fence_chain_any`: from any factor `F` and any Hamiltonian path `H`, a chain of ancestor and
descendant fences at `t`'s cells reaches `D = 0` on `t`'s cells, and then `theoremA_pf` finishes.
An ancestor fence at a cell with `D < 0` never touches a cell with `D ≥ 0` (ancestors have
smaller `D`), and a descendant fence at a cell with `D > 0` never touches a cell with `D ≤ 0`, so
the sum of `|D|` over `t`'s four cells drops by at least 2 per step.
-/

namespace ULHC

open Finset Classical

namespace HP

def DesP (F : Finset Edge) (b c : Pt) : Prop := Relation.ReflTransGen (ArcTo F) b c

def OutClosed (F : Finset Edge) (R : Finset Pt) : Prop := ∀ c ∈ R, ∀ q, ArcTo F c q → q ∈ R

lemma D_ge_desc {V : Finset Pt} {d : Pt → ℕ} {F H : Finset Edge} (hF : IsFactor V d F)
    (hH : IsFactor V d H) {b c : Pt} (h : DesP F b c) : D F H b ≤ D F H c := by
  induction h with
  | refl => exact le_rfl
  | tail _ hyz ih => exact ih.trans (D_arc hF hH hyz)

-- Every boundary arc of a descendant-closed region points into it.
--
lemma inR_of_outClosed {F : Finset Edge} {R : Finset Pt} (hcl : OutClosed F R) :
    ∀ e ∈ bnd R, up F e = decide (e.hi ∈ R) := by
  intro e he
  have hx := mem_bnd.1 he
  obtain ⟨dd, p⟩ := e
  cases dd
  · have hlo : (⟨.h, p⟩ : Edge).lo = (p.1, p.2 - 1) := rfl
    have hhi : (⟨.h, p⟩ : Edge).hi = p := rfl
    have htop : top (p.1, p.2 - 1) = ⟨.h, p⟩ := by simp [top]
    have a1 : outArc F p .b = ! up F ⟨.h, p⟩ := rfl
    have a2 : outArc F (p.1, p.2 - 1) .t = up F ⟨.h, p⟩ := by
      show up F (top (p.1, p.2 - 1)) = _; rw [htop]
    rw [hlo, hhi] at hx; rw [hhi]
    by_cases hl : (p.1, p.2 - 1) ∈ R
    · have hh : p ∉ R := by intro h; simp [hl, h] at hx
      simp only [hh, decide_false]
      by_contra hu
      simp only [Bool.not_eq_false] at hu
      exact hh (hcl _ hl p ⟨.b, rfl, by rw [a1, hu]; rfl⟩)
    · have hh : p ∈ R := by by_contra h; simp [hl, h] at hx
      simp only [hh, decide_true]
      by_contra hu
      simp only [Bool.not_eq_true] at hu
      exact hl (hcl _ hh _ ⟨.t, by simp [nb], by rw [a2, hu]⟩)
  · have hlo : (⟨.v, p⟩ : Edge).lo = (p.1 - 1, p.2) := rfl
    have hhi : (⟨.v, p⟩ : Edge).hi = p := rfl
    have hrgt : rgt (p.1 - 1, p.2) = ⟨.v, p⟩ := by simp [rgt]
    have a1 : outArc F p .l = ! up F ⟨.v, p⟩ := rfl
    have a2 : outArc F (p.1 - 1, p.2) .r = up F ⟨.v, p⟩ := by
      show up F (rgt (p.1 - 1, p.2)) = _; rw [hrgt]
    rw [hlo, hhi] at hx; rw [hhi]
    by_cases hl : (p.1 - 1, p.2) ∈ R
    · have hh : p ∉ R := by intro h; simp [hl, h] at hx
      simp only [hh, decide_false]
      by_contra hu
      simp only [Bool.not_eq_false] at hu
      exact hh (hcl _ hl p ⟨.l, rfl, by rw [a1, hu]; rfl⟩)
    · have hh : p ∈ R := by by_contra h; simp [hl, h] at hx
      simp only [hh, decide_true]
      by_contra hu
      simp only [Bool.not_eq_true] at hu
      exact hl (hcl _ hh _ ⟨.r, by simp [nb], by rw [a2, hu]⟩)

lemma up_rflip_bnd {F : Finset Edge} {R : Finset Pt} {e : Edge} (hb : e ∈ bnd R) :
    up (rflip F R) e = ! up F e := by
  have hm : e ∈ rflip F R ↔ e ∉ F := by simp [rflip, Finset.mem_symmDiff, hb]
  unfold up inE1
  cases e.d <;> cases par e.lo <;> by_cases h : e ∈ F <;> simp [hm, h]

lemma rflip_rflip (F : Finset Edge) (R : Finset Pt) : rflip (rflip F R) R = F := by
  unfold rflip; exact symmDiff_symmDiff_cancel_right _ _

lemma outR_rflip {F : Finset Edge} {R : Finset Pt} (hcl : OutClosed F R) :
    OutR (rflip F R) R := by
  intro e he
  rw [up_rflip_bnd he, inR_of_outClosed hcl e he]
  have hx := mem_bnd.1 he
  by_cases hl : e.lo ∈ R <;> by_cases hh : e.hi ∈ R <;> simp [hl, hh] at hx ⊢

theorem deg_rflip_desc {F : Finset Edge} {R : Finset Pt} (hcl : OutClosed F R) (v : Pt) :
    deg (rflip F R) v = deg F v := by
  have := deg_rflip (outR_rflip hcl) v
  rw [rflip_rflip] at this
  exact this.symm

theorem D_rflip_desc {F H : Finset Edge} {R : Finset Pt} (hcl : OutClosed F R) (x : Pt) :
    D (rflip F R) H x = D F H x - 2 * rin R x := by
  have := D_rflip (H := H) (outR_rflip hcl) x
  rw [rflip_rflip] at this
  omega

-- **The descendant fence**: flipping the descendants of `b` gives a factor.
--
theorem desc_fence {V : Finset Pt} {d : Pt → ℕ} {F : Finset Edge} (hF : IsFactor V d F)
    {b : Pt} (hall : ∀ c, DesP F b c → IsCell V c) :
    let R := (cells V).filter (DesP F b)
    IsFactor V d (rflip F R) ∧ b ∈ R ∧ OutClosed F R := by
  intro R
  have memR : ∀ c, c ∈ R ↔ DesP F b c := by
    intro c; simp only [R, Finset.mem_filter, mem_cells]
    exact ⟨fun h => h.2, fun h => ⟨hall c h, h⟩⟩
  have hcl : OutClosed F R := by
    intro c hc q hq
    rw [memR] at hc ⊢
    exact Relation.ReflTransGen.tail hc hq
  have hbR : b ∈ R := (memR b).2 Relation.ReflTransGen.refl
  refine ⟨⟨fun e he => ?_, fun p hp => by rw [deg_rflip_desc hcl]; exact hF.2 p hp⟩, hbR, hcl⟩
  unfold rflip at he
  rcases Finset.mem_symmDiff.1 he with ⟨h, _⟩ | ⟨h, _⟩
  · exact hF.1 e h
  · unfold bnd at h
    obtain ⟨c, hc, hce⟩ := Finset.mem_biUnion.1 (Finset.mem_filter.1 h).1
    exact isEdge_of_cellE (hall c ((memR c).1 hc)) hce

-- One fence step at `t` of either kind.
--
def FenceStepAny (V : Finset Pt) (t : Pt) (F F' : Finset Edge) : Prop :=
  FenceStep V t F F' ∨
    ∃ b, IsCorner t b ∧ (∀ c, DesP F b c → IsCell V c) ∧
      F' = rflip F ((cells V).filter (DesP F b))

-- The sum of `|D|` over `t`'s four cells.
--
def absSumAt (F H : Finset Edge) (t : Pt) : ℕ :=
  (D F H t).natAbs + (D F H (t.1 - 1, t.2)).natAbs + (D F H (t.1, t.2 - 1)).natAbs +
    (D F H (t.1 - 1, t.2 - 1)).natAbs

theorem fence_chain_any {V : Finset Pt} {d : Pt → ℕ} {H : Finset Edge} (hs : Solid V)
    (hH : IsFactor V d H) (hHam : ncomp V H = 1) {s t : Pt}
    (hd : ∀ z, z ≠ s → z ≠ t → d z = 2) (hds : d s = 1) (hsV : s ∈ V)
    (hsfree : ∀ w, IsCorner s w → ¬ IsCell V w) :
    ∀ F, IsFactor V d F →
      ∃ F1, Relation.ReflTransGen (FenceStepAny V t) F F1 ∧ IsFactor V d F1 ∧
        ∃ F', Relation.ReflTransGen (MovePF V s t) F1 F' ∧ IsFactor V d F' ∧
          (ncomp V F' = 1 ∨
            ∃ c, IsCell V c ∧ (IsCorner s c ∨ IsCorner t c) ∧ ¬ NotTypeIII V F' c) := by
  obtain ⟨k0, k1, k2, k3⟩ := isCorner_four t
  suffices key : ∀ n : ℕ, ∀ F, IsFactor V d F → absSumAt F H t ≤ n →
      ∃ F1, Relation.ReflTransGen (FenceStepAny V t) F F1 ∧ IsFactor V d F1 ∧
        ∃ F', Relation.ReflTransGen (MovePF V s t) F1 F' ∧ IsFactor V d F' ∧
          (ncomp V F' = 1 ∨
            ∃ c, IsCell V c ∧ (IsCorner s c ∨ IsCorner t c) ∧ ¬ NotTypeIII V F' c) by
    intro F hF
    exact key _ F hF le_rfl
  intro n
  induction n with
  | zero =>
    intro F hF hn
    unfold absSumAt at hn
    have hz : ∀ w, IsCorner s w ∨ IsCorner t w → D F H w = 0 := by
      intro w hw
      rcases hw with hw | hw
      · exact D_eq_zero_of_not_cell hF hH hs (hsfree w hw)
      · rcases isCorner_cases hw with rfl | rfl | rfl | rfl <;> omega
    exact ⟨F, Relation.ReflTransGen.refl, hF, theoremA_pf hs hH hHam hd hds hsV F hF hz⟩
  | succ n ih =>
    intro F hF hn
    by_cases hall0 : ∀ w, IsCorner t w → D F H w = 0
    · have z0 := hall0 _ k0; have z1 := hall0 _ k1; have z2 := hall0 _ k2
      have z3 := hall0 _ k3
      exact ih F hF (by unfold absSumAt; rw [z0, z1, z2, z3]; simp)
    push Not at hall0
    obtain ⟨b, hbt, hbne⟩ := hall0
    obtain ⟨m, hm⟩ := D_even F H b
    rcases lt_or_gt_of_ne hbne with hneg | hpos
    · -- `D b ≤ -2`: the ancestor fence at `b`.
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
      have hle : ∀ w, (D (rflip F R) H w).natAbs ≤ (D F H w).natAbs := by
        intro w
        rw [D_rflip hO w]; unfold rin
        split_ifs with hwR
        · have := D_le_anc hF hH ((memR w).1 hwR); omega
        · simp
      have hbR' : b ∈ R := by rw [hRdef]; exact hbR
      have hblt : (D (rflip F R) H b).natAbs + 2 = (D F H b).natAbs := by
        rw [D_rflip hO b]; unfold rin
        split_ifs
        omega
      have hdrop : absSumAt (rflip F R) H t ≤ n := by
        have g0 := hle t; have g1 := hle (t.1 - 1, t.2); have g2 := hle (t.1, t.2 - 1)
        have g3 := hle (t.1 - 1, t.2 - 1)
        unfold absSumAt at hn ⊢
        rcases isCorner_cases hbt with rfl | rfl | rfl | rfl <;> omega
      obtain ⟨F1, hch, rest⟩ := ih (rflip F R) hF' hdrop
      exact ⟨F1, Relation.ReflTransGen.head (Or.inl ⟨b, hbt, hall, rfl⟩) hch, rest⟩
    · -- `D b ≥ 2`: the descendant fence at `b`.
      --
      have hall : ∀ c, DesP F b c → IsCell V c := by
        intro c hc
        by_contra hnc
        have h1 := D_eq_zero_of_not_cell hF hH hs hnc
        have h2 := D_ge_desc hF hH hc
        omega
      set R := (cells V).filter (DesP F b) with hRdef
      obtain ⟨hF', hbR, hcl⟩ := desc_fence hF hall
      have memR : ∀ c, c ∈ R ↔ DesP F b c := by
        intro c; simp only [R, Finset.mem_filter, mem_cells]
        exact ⟨fun h => h.2, fun h => ⟨hall c h, h⟩⟩
      have hle : ∀ w, (D (rflip F R) H w).natAbs ≤ (D F H w).natAbs := by
        intro w
        rw [D_rflip_desc hcl w]; unfold rin
        split_ifs with hwR
        · have := D_ge_desc hF hH ((memR w).1 hwR); omega
        · simp
      have hbR' : b ∈ R := by rw [hRdef]; exact hbR
      have hblt : (D (rflip F R) H b).natAbs + 2 = (D F H b).natAbs := by
        rw [D_rflip_desc hcl b]; unfold rin
        split_ifs
        omega
      have hdrop : absSumAt (rflip F R) H t ≤ n := by
        have g0 := hle t; have g1 := hle (t.1 - 1, t.2); have g2 := hle (t.1, t.2 - 1)
        have g3 := hle (t.1 - 1, t.2 - 1)
        unfold absSumAt at hn ⊢
        rcases isCorner_cases hbt with rfl | rfl | rfl | rfl <;> omega
      obtain ⟨F1, hch, rest⟩ := ih (rflip F R) hF' hdrop
      exact ⟨F1, Relation.ReflTransGen.head (Or.inr ⟨b, hbt, hall, rfl⟩) hch, rest⟩

end HP

end ULHC
