/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
import ULHC.HP.TheoremAT2

/-!
# Guessing the endpoint heights (algorithm plan, step 1–2)

`D` is additive: `D F H = D F R - D H R` for any reference factor `R` (edge weights are linear
in edge membership). So "`D F H = 0` on the endpoints' cells" says that `F` and `H` have the
same `D · R` there, and an algorithm that guesses those values `τ` can run the fence chain of
P22/P24 without knowing `H`: fence at an endpoint cell `b` where `D F R b ≠ τ b`, an ancestor
fence when `D F R b < τ b` and a descendant fence when it is larger.

`guided_chain`: when `τ` is `H`'s values, every such guided chain (any choice of cells) reaches
`D F H = 0` on the endpoints' cells.
-/

namespace ULHC

open Finset Classical

namespace HP

lemma wD_add (F H K : Finset Edge) (e : Edge) : wD F H e + wD H K e = wD F K e := by
  unfold wD wb up inE1
  cases e.d <;> cases par e.lo <;> by_cases a : e ∈ F <;> by_cases b : e ∈ H <;>
    by_cases c : e ∈ K <;> simp [a, b, c]

theorem D_add (F H K : Finset Edge) (x : Pt) : D F H x + D H K x = D F K x := by
  let E := symmDiff F H ∪ symmDiff H K ∪ symmDiff F K
  have s1 : symmDiff F H ⊆ E := by intro e he; simp only [E, Finset.mem_union]; tauto
  have s2 : symmDiff H K ⊆ E := by intro e he; simp only [E, Finset.mem_union]; tauto
  have s3 : symmDiff F K ⊆ E := by intro e he; simp only [E, Finset.mem_union]; tauto
  unfold D
  rw [pot_mono_supp s1 (wD_supp _ _), pot_mono_supp s2 (wD_supp _ _),
    pot_mono_supp s3 (wD_supp _ _), ← pot_add]
  congr 1
  funext e
  exact wD_add F H K e

-- A fence step at an endpoint cell guided by guessed values `τ` of `D · R`.
--
def GuidedStep (V : Finset Pt) (s t : Pt) (R : Finset Edge) (τ : Pt → ℤ)
    (F F' : Finset Edge) : Prop :=
  ∃ z b, (z = s ∨ z = t) ∧ IsCorner z b ∧ D F R b ≠ τ b ∧
    ((D F R b < τ b ∧ (∀ c, AncP F b c → IsCell V c) ∧
        F' = rflip F ((cells V).filter (AncP F b))) ∨
      (τ b < D F R b ∧ (∀ c, DesP F b c → IsCell V c) ∧
        F' = rflip F ((cells V).filter (DesP F b))))

-- Guided steps exist while some endpoint cell is off target, and every guided step for `H`'s
-- values lowers `Σ |D · H|` over the endpoints' cells by at least 2.
--
theorem guided_step_exists {V : Finset Pt} {d : Pt → ℕ} {F H R : Finset Edge} (hs : Solid V)
    (hF : IsFactor V d F) (hH : IsFactor V d H) {s t z b : Pt} (hz : z = s ∨ z = t)
    (hb : IsCorner z b) (hne : D F R b ≠ D H R b) :
    ∃ F', GuidedStep V s t R (D H R) F F' := by
  have hD : D F H b = D F R b - D H R b := by have := D_add F H R b; omega
  obtain ⟨m, hm⟩ := D_even F H b
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hall : ∀ c, AncP F b c → IsCell V c := by
      intro c hc; by_contra hnc
      have h1 := D_eq_zero_of_not_cell hF hH hs hnc
      have h2 := D_le_anc hF hH hc
      omega
    exact ⟨_, z, b, hz, hb, hne, Or.inl ⟨hlt, hall, rfl⟩⟩
  · have hall : ∀ c, DesP F b c → IsCell V c := by
      intro c hc; by_contra hnc
      have h1 := D_eq_zero_of_not_cell hF hH hs hnc
      have h2 := D_ge_desc hF hH hc
      omega
    exact ⟨_, z, b, hz, hb, hne, Or.inr ⟨hgt, hall, rfl⟩⟩

theorem guided_step_spec {V : Finset Pt} {d : Pt → ℕ} {F F' H R : Finset Edge}
    (hF : IsFactor V d F) (hH : IsFactor V d H) {s t : Pt}
    (hst : GuidedStep V s t R (D H R) F F') :
    IsFactor V d F' ∧ (∀ w, (D F' H w).natAbs ≤ (D F H w).natAbs) ∧
      absSumAt F' H s + absSumAt F' H t + 2 ≤ absSumAt F H s + absSumAt F H t := by
  obtain ⟨z, b, hz, hb, hne, h⟩ := hst
  have hD : ∀ G x, D G H x = D G R x - D H R x := fun G x => by have := D_add G H R x; omega
  obtain ⟨m, hm⟩ := D_even F H b
  have key : IsFactor V d F' ∧ (∀ w, (D F' H w).natAbs ≤ (D F H w).natAbs) ∧
      (D F' H b).natAbs + 2 = (D F H b).natAbs := by
    rcases h with ⟨hlt, hall, rfl⟩ | ⟨hgt, hall, rfl⟩
    · have hneg : D F H b < 0 := by rw [hD]; omega
      obtain ⟨hF', hbR, hcl, _, _⟩ := smallest_fence hF hall
      have hO := outR_of_closed hcl
      have memR : ∀ c, c ∈ (cells V).filter (AncP F b) ↔ AncP F b c := by
        intro c; simp only [Finset.mem_filter, mem_cells]
        exact ⟨fun h => h.2, fun h => ⟨hall c h, h⟩⟩
      refine ⟨hF', fun w => ?_, ?_⟩
      · rw [D_rflip hO w]; unfold rin
        split_ifs with hwR
        · have := D_le_anc hF hH ((memR w).1 hwR); omega
        · omega
      · rw [D_rflip hO b]; unfold rin
        split_ifs
        omega
    · have hpos : 0 < D F H b := by rw [hD]; omega
      obtain ⟨hF', hbR, hcl⟩ := desc_fence hF hall
      have memR : ∀ c, c ∈ (cells V).filter (DesP F b) ↔ DesP F b c := by
        intro c; simp only [Finset.mem_filter, mem_cells]
        exact ⟨fun h => h.2, fun h => ⟨hall c h, h⟩⟩
      refine ⟨hF', fun w => ?_, ?_⟩
      · rw [D_rflip_desc hcl w]; unfold rin
        split_ifs with hwR
        · have := D_ge_desc hF hH ((memR w).1 hwR); omega
        · omega
      · rw [D_rflip_desc hcl b]; unfold rin
        split_ifs
        omega
  obtain ⟨hF', hle, hblt⟩ := key
  refine ⟨hF', hle, ?_⟩
  have a1 := absSum_le hle s
  have a2 := absSum_le hle t
  rcases hz with rfl | rfl
  · have := absSum_lt hle hb hblt; omega
  · have := absSum_lt hle hb hblt; omega

-- **Guided chains reach the target.** For `H`'s values, a maximal chain of guided steps ends
-- at a factor with `D · H = 0` on the endpoints' cells, after at most `Σ |D F H| / 2` steps.
--
theorem guided_chain {V : Finset Pt} {d : Pt → ℕ} {H R : Finset Edge} (hs : Solid V)
    (hH : IsFactor V d H) {s t : Pt} :
    ∀ F, IsFactor V d F →
      ∃ F1, Relation.ReflTransGen (GuidedStep V s t R (D H R)) F F1 ∧ IsFactor V d F1 ∧
        ∀ w, IsCorner s w ∨ IsCorner t w → D F1 H w = 0 := by
  suffices key : ∀ n : ℕ, ∀ F, IsFactor V d F → absSumAt F H s + absSumAt F H t ≤ n →
      ∃ F1, Relation.ReflTransGen (GuidedStep V s t R (D H R)) F F1 ∧ IsFactor V d F1 ∧
        ∀ w, IsCorner s w ∨ IsCorner t w → D F1 H w = 0 by
    intro F hF; exact key _ F hF le_rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro F hF hn
  by_cases hall0 : ∀ w, IsCorner s w ∨ IsCorner t w → D F H w = 0
  · exact ⟨F, Relation.ReflTransGen.refl, hF, hall0⟩
  push Not at hall0
  obtain ⟨b, hbz, hbne⟩ := hall0
  have hne : D F R b ≠ D H R b := by
    intro h; apply hbne; have := D_add F H R b; omega
  obtain ⟨z, hz, hb⟩ : ∃ z, (z = s ∨ z = t) ∧ IsCorner z b := by
    rcases hbz with h | h
    · exact ⟨s, Or.inl rfl, h⟩
    · exact ⟨t, Or.inr rfl, h⟩
  obtain ⟨F2, hst⟩ := guided_step_exists hs hF hH hz hb hne
  obtain ⟨hF2, _, hdrop⟩ := guided_step_spec hF hH hst
  obtain ⟨F1, hch, rest⟩ := ih (absSumAt F2 H s + absSumAt F2 H t) (by omega) F2 hF2 le_rfl
  exact ⟨F1, Relation.ReflTransGen.head hst hch, rest⟩

end HP

end ULHC
