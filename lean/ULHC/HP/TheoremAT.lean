/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
import ULHC.HP.StartEdge
import ULHC.HP.DescFence

/-!
# Lemma B and Theorem A for path-factors without the residual case (notes P23)

`theoremA_pf` stopped at a Type III cell with an endpoint as a corner, because Lemma B assumed
no Type III cell anywhere. The walk needs "not Type III" only at cells where `D` has the walk's
sign (`WalkT.lean`) and at the start, which `good_start` supplies. With `s` on a tail (no cell
has `s` as a corner) and `d t = 1`, Type III merges away from the endpoints and Lemma B's strips
reach a Hamiltonian path. `hp_moves`: from any factor, if a Hamiltonian path exists, fence steps
at `t` (P22) and then these moves reach a Hamiltonian path.
-/

namespace ULHC

open Finset Classical

namespace HP

theorem endpoint_criterion_t {V : Finset Pt} {d : Pt → ℕ} {F H : Finset Edge} (hs : Solid V)
    (hF : IsFactor V d F) (hH : IsFactor V d H) (hHam : ncomp V H = 1) {s t : Pt}
    (hd : ∀ z, z ≠ s → z ≠ t → d z = 2)
    (hz : ∀ w, IsCorner s w ∨ IsCorner t w → D F H w = 0)
    (hdt : d t = 1) (htV : t ∈ V) (hsfree : ∀ w, IsCorner s w → ¬ IsCell V w)
    (hfar : ∀ c, IsCell V c → ¬ IsCorner s c → ¬ IsCorner t c → NotTypeIII V F c)
    (h2 : 2 ≤ ncomp V F) :
    ∃ σ : StripSpec, ValidStrip V F σ ∧ 2 ≤ σ.n ∧ mu V (applyS F σ) H + 2 * σ.n = mu V F H ∧
      (∀ j < σ.n, ¬ IsCorner s (cellJ σ.c σ.s j) ∧ ¬ IsCorner t (cellJ σ.c σ.s j)) ∧
      ∃ o, ParOK σ.c σ.s o ∧ ∀ j < σ.n, Good o (D F H (cellJ σ.c σ.s j)) := by
  have hloc := deg2Cell_of_zero hF hH (SolidFor.of_solid hF hH hs) hd hz
  obtain ⟨o, v, s0, hc0, hi0, hj0, hg0, hL0⟩ :=
    good_start hs hF hH hHam hd hdt htV hsfree hfar hz h2
  set P := cls V F t
  have hB : Border V F P :=
    ⟨Finset.filter_subset _ _, fun u hu w hw => closed_cls (Inside.of_factor hF) t u hu w hw⟩
  have hTg : ∀ c, Good o (D F H c) → NotTypeIII V F c := by
    intro c hg
    have h0 := good_ne_zero hg
    exact hfar c (Good.isCell_f (SolidFor.of_solid hF hH hs) hg) (fun h => h0 (hz _ (Or.inl h)))
      (fun h => h0 (hz _ (Or.inr h)))
  obtain ⟨w, _, hgw, hst⟩ := phase1_t hF hH (SolidFor.of_solid hF hH hs) hB o hTg (hloc o) v s0 hc0 hi0 hj0 hg0 hL0
  obtain ⟨s', n, hn, hpat, hcell, hgood, hp, hsep⟩ := phase2_loc hF hH (SolidFor.of_solid hF hH hs) hB (hloc o) hgw hst
  refine ⟨⟨w, s', n⟩, ⟨show 1 ≤ n by omega, hpat, hcell, hsep⟩, hn,
    strip_mu hp n hpat hcell hgood, fun j hj => ?_, o, hp, hgood⟩
  have h0 := good_ne_zero (hgood j hj)
  exact ⟨fun h => h0 (hz _ (Or.inl h)), fun h => h0 (hz _ (Or.inr h))⟩

theorem lemmaB_t {V : Finset Pt} {d : Pt → ℕ} {F H : Finset Edge} (hs : Solid V)
    (hF : IsFactor V d F) (hH : IsFactor V d H) (hHam : ncomp V H = 1) {s t : Pt}
    (hd : ∀ z, z ≠ s → z ≠ t → d z = 2) (hds : d s = 1) (hsV : s ∈ V)
    (hz : ∀ w, IsCorner s w ∨ IsCorner t w → D F H w = 0)
    (hdt : d t = 1) (htV : t ∈ V) (hsfree : ∀ w, IsCorner s w → ¬ IsCell V w)
    (hfar : ∀ c, IsCell V c → ¬ IsCorner s c → ¬ IsCorner t c → NotTypeIII V F c)
    (h2 : 2 ≤ ncomp V F) :
    ∃ σ : StripSpec, ValidStrip V F σ ∧ 2 ≤ σ.n ∧ mu V (applyS F σ) H + 2 * σ.n = mu V F H ∧
      (∀ j < σ.n, ¬ IsCorner s (cellJ σ.c σ.s j) ∧ ¬ IsCorner t (cellJ σ.c σ.s j)) ∧
      ncomp V (applyS F σ) ≤ ncomp V F ∧ ncomp V F ≤ ncomp V (applyS F σ) + 1 ∧
      (σ.n % 2 = 1 → ncomp V (applyS F σ) + 1 = ncomp V F) ∧
      ∃ o, ParOK σ.c σ.s o ∧ ∀ j < σ.n, Good o (D F H (cellJ σ.c σ.s j)) := by
  obtain ⟨σ, hv, hn, hmu, hcor, o, hpo, hgo⟩ := endpoint_criterion_t hs hF hH hHam hd hz hdt htV hsfree hfar h2
  have hD : Deg2Off V F s t :=
    ⟨InsideST.of_inside (Inside.of_factor hF), fun z hz hzs hzt => by rw [hF.2 z hz]; exact hd z hzs hzt⟩
  have hdsF : deg F s = 1 := by rw [hF.2 s hsV]; exact hds
  have hst := conn_st hD hsV hdsF
  suffices hcnt : ncomp V (applyS F σ) ≤ ncomp V F ∧ ncomp V F ≤ ncomp V (applyS F σ) + 1 ∧
      (σ.n % 2 = 1 → ncomp V (applyS F σ) + 1 = ncomp V F) from
    ⟨σ, hv, hn, hmu, hcor, hcnt.1, hcnt.2.1, hcnt.2.2, o, hpo, hgo⟩
  obtain ⟨_, hpat, hcell, hsep⟩ := hv
  unfold applyS
  rcases Nat.mod_two_eq_zero_or_one σ.n with hev | hodd
  · obtain ⟨k, hk⟩ : ∃ k, σ.n = k + 2 := ⟨σ.n - 2, by omega⟩
    have hk2 : k % 2 = 0 := by omega
    rw [hk] at hpat hcell hcor ⊢
    have hsame : Conn F (back1 (cellJ σ.c σ.s (k + 1)) σ.s) (back2 (cellJ σ.c σ.s (k + 1)) σ.s) := by
      have hce := hcell (k + 1) (by omega)
      obtain ⟨_, hl, hf⟩ := hpat
      have ha : Alt F (cellJ σ.c σ.s (k + 1)) := by
        have l1 := (hl (k + 1) (by omega)).1.2 (by omega)
        have l2 := (hl (k + 1) (by omega)).2.2 (by omega)
        have fF : front (cellJ σ.c σ.s (k + 1)) σ.s ∉ F := by
          intro h; have := (hf (k + 1) (by omega)).1 h; omega
        have bF : back (cellJ σ.c σ.s (k + 1)) σ.s ∉ F := by
          rw [back_cellJ_succ]; intro h; have := (hf k (by omega)).1 h; omega
        rw [lat1_eq] at l1
        rw [lat2_eq] at l2
        simp only [back, front] at fF bF
        generalize cellJ σ.c σ.s (k + 1) = r at *
        obtain ⟨x, y⟩ := r
        cases hs' : σ.s <;> rw [hs'] at l1 l2 fF bF <;>
          simp only [latA, latB, sideEdge, Side.opp] at l1 l2 fF bF <;> unfold Alt <;> tauto
      obtain ⟨k1, k2, k3⟩ := alt_corners_conn' (hfar _ hce (hcor (k + 1) (by omega)).1
        (hcor (k + 1) (by omega)).2) ha
      generalize cellJ σ.c σ.s (k + 1) = r at *
      obtain ⟨x, y⟩ := r
      cases σ.s <;> simp only [back1, back2] at * <;>
        first
        | exact k1
        | exact k2.symm.trans k3
        | exact k1.symm.trans k3
        | exact k2
    obtain ⟨b1, b2⟩ := strip_even_count_pf k hk2 F hD hsV hdsF (fun j hj => hcell j (by omega))
      (fun j hj => hcor j (by omega)) hpat hsep hsame
    exact ⟨b1, b2, fun h => by omega⟩
  · obtain ⟨k, hk⟩ : ∃ k, σ.n = k + 1 := ⟨σ.n - 1, by omega⟩
    have hk2 : k % 2 = 0 := by omega
    rw [hk] at hpat hcell hcor ⊢
    have := strip_odd_count_pf k hk2 F hD hst (fun j hj => hcell j (by omega))
      (fun j hj => hcor j (by omega)) hpat hsep
    exact ⟨by omega, by omega, fun _ => this⟩


theorem theoremA_t {V : Finset Pt} {d : Pt → ℕ} {H : Finset Edge} (hs : Solid V)
    (hH : IsFactor V d H) (hHam : ncomp V H = 1) {s t : Pt}
    (hd : ∀ z, z ≠ s → z ≠ t → d z = 2) (hds : d s = 1) (hsV : s ∈ V) (hdt : d t = 1)
    (htV : t ∈ V) (hsfree : ∀ w, IsCorner s w → ¬ IsCell V w) :
    ∀ F, IsFactor V d F → (∀ w, IsCorner s w ∨ IsCorner t w → D F H w = 0) →
      ∃ F', Relation.ReflTransGen (MovePF V s t) F F' ∧ IsFactor V d F' ∧ ncomp V F' = 1 := by
  suffices key : ∀ n m (F : Finset Edge), ncomp V F = n → mu V F H = m → IsFactor V d F →
      (∀ w, IsCorner s w ∨ IsCorner t w → D F H w = 0) →
      ∃ F', Relation.ReflTransGen (MovePF V s t) F F' ∧ IsFactor V d F' ∧ ncomp V F' = 1 from
    fun F hF hz => key _ _ F rfl rfl hF hz
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ihn =>
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ihm =>
  intro F hn hm hF hz
  by_cases h1 : ncomp V F ≤ 1
  · exact ⟨F, Relation.ReflTransGen.refl, hF, by have := ncomp_pos (F := F) hsV; omega⟩
  by_cases hA : ∃ c, IsCell V c ∧ ¬ IsCorner s c ∧ ¬ IsCorner t c ∧ ¬ NotTypeIII V F c
  · obtain ⟨c, hc, hcs, hct, hc3⟩ := hA
    obtain ⟨hF', hcnt, hDoff⟩ := typeIII_flip (H := H) hF hd hds hsV hc hc3
    have hz' : ∀ w, IsCorner s w ∨ IsCorner t w → D (ULHC.flip F c) H w = 0 := by
      intro w hw
      have hwc : w ≠ c := by
        rintro rfl; rcases hw with h | h
        · exact hcs h
        · exact hct h
      rw [hDoff w hwc]; exact hz w hw
    obtain ⟨F', hr, hF'', hfin⟩ :=
      ihn (ncomp V (ULHC.flip F c)) (by omega) _ _ rfl rfl hF' hz'
    exact ⟨F', Relation.ReflTransGen.head (Or.inr ⟨c, hc, hcs, hct, hc3, rfl⟩) hr, hF'', hfin⟩
  have hfar : ∀ c, IsCell V c → ¬ IsCorner s c → ¬ IsCorner t c → NotTypeIII V F c := by
    intro c hc h1 h2
    by_contra h
    exact hA ⟨c, hc, h1, h2, h⟩
  obtain ⟨σ, hv, hn2, hmu, hcor, hle, _, _, o, hp, hg⟩ :=
    lemmaB_t hs hF hH hHam hd hds hsV hz hdt htV hsfree hfar (by omega)
  have hF' : IsFactor V d (applyS F σ) := factor_flipCol σ.n F hF hv.2.1 hv.2.2.1
  have hz' : ∀ w, IsCorner s w ∨ IsCorner t w → D (applyS F σ) H w = 0 := by
    intro w hw
    unfold applyS
    rw [strip_D_off hp σ.n hv.2.1 hg w (fun j hj heq => by
      rcases hw with h | h
      · exact (hcor j hj).1 (heq ▸ h)
      · exact (hcor j hj).2 (heq ▸ h))]
    exact hz w hw
  have hmove : MovePF V s t F (applyS F σ) := Or.inl ⟨σ, hv, hcor, rfl, hle⟩
  by_cases hlt : ncomp V (applyS F σ) < ncomp V F
  · obtain ⟨F', hr, hF'', hfin⟩ := ihn _ (by omega) _ _ rfl rfl hF' hz'
    exact ⟨F', Relation.ReflTransGen.head hmove hr, hF'', hfin⟩
  · obtain ⟨F', hr, hF'', hfin⟩ := ihm (mu V (applyS F σ) H) (by omega) _ (by omega) rfl hF' hz'
    exact ⟨F', Relation.ReflTransGen.head hmove hr, hF'', hfin⟩

-- **Existence of a move sequence (P22 + P23).** Let `s` be on a tail (no cell has `s` as a
-- corner) and `H` a Hamiltonian s–t path. From any path-factor `F`, fence steps at `t`'s cells
-- and then strips and Type III merges away from the endpoints reach a Hamiltonian path.
--
theorem hp_moves {V : Finset Pt} {d : Pt → ℕ} {H : Finset Edge} (hs : Solid V)
    (hH : IsFactor V d H) (hHam : ncomp V H = 1) {s t : Pt}
    (hd : ∀ z, z ≠ s → z ≠ t → d z = 2) (hds : d s = 1) (hsV : s ∈ V)
    (hsfree : ∀ w, IsCorner s w → ¬ IsCell V w) (hdt : d t = 1) (htV : t ∈ V) :
    ∀ F, IsFactor V d F →
      ∃ F1, Relation.ReflTransGen (FenceStepAny V t) F F1 ∧ IsFactor V d F1 ∧
        ∃ F', Relation.ReflTransGen (MovePF V s t) F1 F' ∧ IsFactor V d F' ∧ ncomp V F' = 1 := by
  obtain ⟨k0, k1, k2, k3⟩ := isCorner_four t
  suffices key : ∀ n : ℕ, ∀ F, IsFactor V d F → absSumAt F H t ≤ n →
      ∃ F1, Relation.ReflTransGen (FenceStepAny V t) F F1 ∧ IsFactor V d F1 ∧
        ∃ F', Relation.ReflTransGen (MovePF V s t) F1 F' ∧ IsFactor V d F' ∧ ncomp V F' = 1 by
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
    exact ⟨F, Relation.ReflTransGen.refl, hF, theoremA_t hs hH hHam hd hds hsV hdt htV hsfree F hF hz⟩
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
