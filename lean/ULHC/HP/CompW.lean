/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
import ULHC.Comp
import ULHC.Enum
import ULHC.HP.StripCountPF

/-!
# Computed component counts for factors on `V` plus one point

With a phantom endpoint, a factor lives on `W ⊇ V` with at most one point more than `V`. The
bounded reach of `cncomp V` (|V| rounds) still reaches every component, so the computed count
over `V` is the true count (`cncomp_eqW`).
-/

namespace ULHC

namespace HP

open Finset

section compW

variable {V W : Finset Pt} {F : Finset Edge}

lemma creach_fixW (hFW : Inside W F) (hW : W.card ≤ V.card + 1) {x : Pt} (hx : x ∈ W) :
    ∃ k ≤ V.card, creach F x (k + 1) = creach F x k := by
  by_contra hn
  push Not at hn
  have hgrow : ∀ n, n ≤ V.card + 1 → n + 1 ≤ (creach F x n).card := by
    intro n
    induction n with
    | zero => intro _; simp [creach]
    | succ n ih =>
      intro hn1
      have hss : creach F x n ⊂ creach F x (n + 1) :=
        ssubset_of_subset_of_ne creach_sub_succ (hn n (by omega)).symm
      have := card_lt_card hss
      have := ih (by omega)
      omega
  have h1 := hgrow (V.card + 1) le_rfl
  have h2 := card_le_card (creach_sub hFW hx (V.card + 1))
  omega

lemma ccls_eqW (hFW : Inside W F) (hW : W.card ≤ V.card + 1) (hVW : V ⊆ W) {x : Pt}
    (hx : x ∈ V) : ccls V F x = cls W F x := by
  classical
  obtain ⟨k, hk, hfix⟩ := creach_fixW hFW hW (hVW hx)
  have hst : creach F x V.card = creach F x k := creach_stable hfix _ hk
  have closed : ∀ u ∈ creach F x k, ∀ v, Adj F u v → v ∈ creach F x k := by
    intro u hu v huv
    obtain ⟨e, he, hi, _, rfl⟩ := adj_inc huv
    rw [← hfix, creach_succ, mem_union, mem_biUnion]
    exact Or.inr ⟨u, hu, mem_fnbr.2 ⟨e, he, hi, rfl⟩⟩
  ext z
  unfold ccls cls
  rw [mem_filter, hst]
  constructor
  · intro hz
    exact ⟨creach_sub hFW (hVW hx) k hz, creach_conn k z hz⟩
  · rintro ⟨-, hc⟩
    induction hc with
    | refl => exact creach_mono (Nat.zero_le k) (by simp [creach])
    | tail _ hbc ih => exact closed _ ih _ hbc

-- **The computed count is the count**, for a factor on `W` with at most one point more than `V`.
--
theorem cncomp_eqW (hFW : Inside W F) (hW : W.card ≤ V.card + 1) (hVW : V ⊆ W) :
    cncomp V F = ncomp V F := by
  classical
  unfold cncomp ncomp
  have h1 : V.image (ccls V F) = V.image (cls W F) :=
    image_congr (fun x hx => ccls_eqW hFW hW hVW hx)
  have h2 : V.image (cls V F) = (V.image (cls W F)).image (fun S => S.filter (· ∈ V)) := by
    rw [image_image]
    apply image_congr
    intro x _
    ext z
    simp only [cls, Function.comp, mem_filter]
    constructor
    · rintro ⟨hz, hc⟩; exact ⟨⟨hVW hz, hc⟩, hz⟩
    · rintro ⟨⟨_, hc⟩, hz⟩; exact ⟨hz, hc⟩
  rw [h1, h2]
  symm
  apply card_image_of_injOn
  intro A hA B hB hAB
  obtain ⟨x, hx, rfl⟩ := mem_image.1 (mem_coe.1 hA)
  obtain ⟨y, hy, rfl⟩ := mem_image.1 (mem_coe.1 hB)
  have hxy : x ∈ (cls W F y).filter (· ∈ V) := by
    have h := hAB; simp only at h; rw [← h]; simp only [cls, mem_filter]
    exact ⟨⟨hVW hx, Conn.refl F x⟩, hx⟩
  simp only [cls, mem_filter] at hxy
  have hc : Conn F y x := hxy.1.2
  ext z
  simp only [cls, mem_filter]
  exact ⟨fun ⟨hz, h⟩ => ⟨hz, hc.trans h⟩, fun ⟨hz, h⟩ => ⟨hz, hc.symm.trans h⟩⟩

end compW

section decideW

variable {V W : Finset Pt} {F G : Finset Edge}

-- With one phantom point, a set `W = insert s (insert t V)` with `s ∈ V` has at most one point
-- more than `V`.
--
lemma card_insST {s t : Pt} (hs : s ∈ V) : (insert s (insert t V)).card ≤ V.card + 1 := by
  rw [Finset.insert_eq_of_mem (Finset.mem_insert_of_mem hs)]
  exact Finset.card_insert_le t V

lemma connB_iffW (hFW : Inside W F) (hW : W.card ≤ V.card + 1) (hVW : V ⊆ W) {x y : Pt}
    (hx : x ∈ V) (hy : y ∈ V) : connB V F x y = true ↔ Conn F x y := by
  simp only [connB, decide_eq_true_eq, ccls_eqW hFW hW hVW hx, cls, Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨hVW hy, h⟩⟩

theorem validB_iffW (hFW : Inside W F) (hW : W.card ≤ V.card + 1) (hVW : V ⊆ W)
    {σ : StripSpec} : validB V F σ = true ↔ ValidStrip V F σ := by
  unfold validB ValidStrip
  rw [Bool.and_eq_true, decide_eq_true_eq, mem_allStrips, Bool.not_eq_true']
  constructor
  · rintro ⟨⟨h1, hp, hc⟩, hn⟩
    have hc0 : IsCell V σ.c := by have := hc 0 (by omega); rwa [cellJ_zero] at this
    obtain ⟨hb, hf⟩ := corners_mem hc0 σ.s
    refine ⟨h1, hp, hc, fun h => ?_⟩
    rw [← connB_iffW hFW hW hVW hb hf] at h
    rw [h] at hn; cases hn
  · rintro ⟨h1, hp, hc, hn⟩
    have hc0 : IsCell V σ.c := by have := hc 0 (by omega); rwa [cellJ_zero] at this
    obtain ⟨hb, hf⟩ := corners_mem hc0 σ.s
    refine ⟨⟨h1, hp, hc⟩, ?_⟩
    cases h : connB V F (back1 σ.c σ.s) (front1 σ.c σ.s)
    · rfl
    · exact absurd ((connB_iffW hFW hW hVW hb hf).1 h) hn

theorem cr2B_iffW (hGW : Inside W G) (hW : W.card ≤ V.card + 1) (hVW : V ⊆ W)
    {b c : StripSpec} (hu : IsCell V (endCell b)) : cr2B V G b c = true ↔ CR2 V G b c := by
  have hFu : Inside W (flip G (endCell b)) := inside_flip hGW (isCell_mono hu hVW)
  unfold cr2B CR2
  simp only [Bool.and_eq_true, decide_eq_true_eq, mem_allStrips, sideOffB_iff,
    bool_not_iff midB_iff]
  have hne : notEndB b c = true ↔ ∀ j < c.n, cellJ c.c c.s j ≠ endCell b := by
    simp [notEndB, List.all_eq_true, List.mem_range]
  have hend : endOffB b c = true ↔
      (c.n % 2 = 0 → ∀ e ∈ cellE (endCell c), e ∉ cellE (endCell b)) := by
    simp only [endOffB, decide_eq_true_eq]
  rw [hne, hend]
  constructor
  · rintro ⟨⟨⟨⟨⟨⟨⟨⟨⟨h2, he⟩, h1, hp, hc⟩, hso⟩, hne'⟩, hen⟩, hm1⟩, hm2⟩, hcg⟩, hcu⟩
    have hc0 : IsCell V c.c := by have := hc 0 (by omega); rwa [cellJ_zero] at this
    obtain ⟨hb, hf⟩ := corners_mem hc0 c.s
    refine ⟨h2, he, h1, hp, hc, hso, hne', hen, hm1, hm2,
      (connB_iffW hGW hW hVW hb hf).1 hcg, ?_⟩
    exact (bool_not_iff (connB_iffW hFu hW hVW hb hf)).1 hcu
  · rintro ⟨h2, he, h1, hp, hc, hso, hne', hen, hm1, hm2, hcg, hcu⟩
    have hc0 : IsCell V c.c := by have := hc 0 (by omega); rwa [cellJ_zero] at this
    obtain ⟨hb, hf⟩ := corners_mem hc0 c.s
    exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨h2, he⟩, h1, hp, hc⟩, hso⟩, hne'⟩, hen⟩, hm1⟩, hm2⟩,
      (connB_iffW hGW hW hVW hb hf).2 hcg⟩, (bool_not_iff (connB_iffW hFu hW hVW hb hf)).2 hcu⟩

end decideW

end HP

end ULHC
