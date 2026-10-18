/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
import ULHC.HP.StartEdge2
import ULHC.HP.TheoremAT

/-!
# Both endpoints in the grid (notes P24)

No tail at `s`. Fence steps now run at the cells of both endpoints (a fence at a cell with
`D < 0` touches only cells with smaller `D`, so `D` on the other endpoint's cells never moves
away from 0). Lemma B either gives a strip or, by `good_start2`, `F` has exactly two components
and a Type III cell, whose flip is a Hamiltonian path.
-/

namespace ULHC

open Finset Classical

namespace HP

theorem endpoint_criterion_t2 {V : Finset Pt} {d : Pt → ℕ} {F H : Finset Edge} (hs : SolidFor V F H)
    (hF : IsFactor V d F) (hH : IsFactor V d H) (hHam : ncomp V H = 1) {s t : Pt}
    (hd : ∀ z, z ≠ s → z ≠ t → d z = 2)
    (hz : ∀ w, IsCorner s w ∨ IsCorner t w → D F H w = 0)
    (hds : d s = 1) (hdt : d t = 1) (hsV : s ∈ V) (htV : t ∈ V)
    (hfar : ∀ c, IsCell V c → ¬ IsCorner s c → ¬ IsCorner t c → NotTypeIII V F c)
    (h2 : 2 ≤ ncomp V F) :
    (∃ σ : StripSpec, ValidStrip V F σ ∧ 2 ≤ σ.n ∧ mu V (applyS F σ) H + 2 * σ.n = mu V F H ∧
      (∀ j < σ.n, ¬ IsCorner s (cellJ σ.c σ.s j) ∧ ¬ IsCorner t (cellJ σ.c σ.s j)) ∧
      ∃ o, ParOK σ.c σ.s o ∧ ∀ j < σ.n, Good o (D F H (cellJ σ.c σ.s j))) ∨
    (ncomp V F = 2 ∧ ∃ c, IsCell V c ∧ ¬ NotTypeIII V F c) := by
  have hloc := deg2Cell_of_zero hF hH hs hd hz
  rcases good_start2 hs hF hH hHam hd hds hdt hsV htV hfar hz h2 with
    ⟨P, hB, o, v, s0, hc0, hi0, hj0, hg0, hL0⟩ | hr
  swap
  · exact Or.inr hr
  left
  have hTg : ∀ c, Good o (D F H c) → NotTypeIII V F c := by
    intro c hg
    have h0 := good_ne_zero hg
    exact hfar c (Good.isCell_f hs hg) (fun h => h0 (hz _ (Or.inl h)))
      (fun h => h0 (hz _ (Or.inr h)))
  obtain ⟨w, _, hgw, hst⟩ := phase1_t hF hH hs hB o hTg (hloc o) v s0 hc0 hi0 hj0 hg0 hL0
  obtain ⟨s', n, hn, hpat, hcell, hgood, hp, hsep⟩ := phase2_loc hF hH hs hB (hloc o) hgw hst
  refine ⟨⟨w, s', n⟩, ⟨show 1 ≤ n by omega, hpat, hcell, hsep⟩, hn,
    strip_mu hp n hpat hcell hgood, fun j hj => ?_, o, hp, hgood⟩
  have h0 := good_ne_zero (hgood j hj)
  exact ⟨fun h => h0 (hz _ (Or.inl h)), fun h => h0 (hz _ (Or.inr h))⟩

theorem lemmaB_t2 {V : Finset Pt} {d : Pt → ℕ} {F H : Finset Edge} (hs : SolidFor V F H)
    (hF : IsFactor V d F) (hH : IsFactor V d H) (hHam : ncomp V H = 1) {s t : Pt}
    (hd : ∀ z, z ≠ s → z ≠ t → d z = 2) (hds : d s = 1) (hsV : s ∈ V)
    (hz : ∀ w, IsCorner s w ∨ IsCorner t w → D F H w = 0)
    (hdt : d t = 1) (htV : t ∈ V)
    (hfar : ∀ c, IsCell V c → ¬ IsCorner s c → ¬ IsCorner t c → NotTypeIII V F c)
    (h2 : 2 ≤ ncomp V F) :
    (∃ σ : StripSpec, ValidStrip V F σ ∧ 2 ≤ σ.n ∧ mu V (applyS F σ) H + 2 * σ.n = mu V F H ∧
      (∀ j < σ.n, ¬ IsCorner s (cellJ σ.c σ.s j) ∧ ¬ IsCorner t (cellJ σ.c σ.s j)) ∧
      ncomp V (applyS F σ) ≤ ncomp V F ∧ ncomp V F ≤ ncomp V (applyS F σ) + 1 ∧
      (σ.n % 2 = 1 → ncomp V (applyS F σ) + 1 = ncomp V F) ∧
      ∃ o, ParOK σ.c σ.s o ∧ ∀ j < σ.n, Good o (D F H (cellJ σ.c σ.s j))) ∨
    (ncomp V F = 2 ∧ ∃ c, IsCell V c ∧ ¬ NotTypeIII V F c) := by
  rcases endpoint_criterion_t2 hs hF hH hHam hd hz hds hdt hsV htV hfar h2 with
    ⟨σ, hv, hn, hmu, hcor, o, hpo, hgo⟩ | hr
  swap
  · exact Or.inr hr
  left
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


theorem theoremA_t2 {V : Finset Pt} {d : Pt → ℕ} {H : Finset Edge}
    (hH : IsFactor V d H) (hHam : ncomp V H = 1) {s t : Pt}
    (hd : ∀ z, z ≠ s → z ≠ t → d z = 2) (hds : d s = 1) (hsV : s ∈ V) (hdt : d t = 1)
    (htV : t ∈ V) :
    ∀ F, IsFactor V d F → SolidFor V F H → (∀ w, IsCorner s w ∨ IsCorner t w → D F H w = 0) →
      ∃ F', Relation.ReflTransGen (MovePF V s t) F F' ∧ IsFactor V d F' ∧
        (ncomp V F' = 1 ∨ ∃ c, IsCell V c ∧ ¬ NotTypeIII V F' c ∧
          IsFactor V d (ULHC.flip F' c) ∧ ncomp V (ULHC.flip F' c) = 1) := by
  suffices key : ∀ n m (F : Finset Edge), ncomp V F = n → mu V F H = m → IsFactor V d F →
      SolidFor V F H → (∀ w, IsCorner s w ∨ IsCorner t w → D F H w = 0) →
      ∃ F', Relation.ReflTransGen (MovePF V s t) F F' ∧ IsFactor V d F' ∧
        (ncomp V F' = 1 ∨ ∃ c, IsCell V c ∧ ¬ NotTypeIII V F' c ∧
          IsFactor V d (ULHC.flip F' c) ∧ ncomp V (ULHC.flip F' c) = 1) from
    fun F hF hs hz => key _ _ F rfl rfl hF hs hz
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ihn =>
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ihm =>
  intro F hn hm hF hs hz
  by_cases h1 : ncomp V F ≤ 1
  · exact ⟨F, Relation.ReflTransGen.refl, hF, Or.inl (by have := ncomp_pos (F := F) hsV; omega)⟩
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
    have hs' : SolidFor V (ULHC.flip F c) H :=
      hs.of_off fun w hw => hDoff w (fun h => hw (h ▸ hc))
    obtain ⟨F', hr, hF'', hfin⟩ :=
      ihn (ncomp V (ULHC.flip F c)) (by omega) _ _ rfl rfl hF' hs' hz'
    exact ⟨F', Relation.ReflTransGen.head (Or.inr ⟨c, hc, hcs, hct, hc3, rfl⟩) hr, hF'', hfin⟩
  have hfar : ∀ c, IsCell V c → ¬ IsCorner s c → ¬ IsCorner t c → NotTypeIII V F c := by
    intro c hc h1 h2
    by_contra h
    exact hA ⟨c, hc, h1, h2, h⟩
  rcases lemmaB_t2 hs hF hH hHam hd hds hsV hz hdt htV hfar (by omega) with
    ⟨σ, hv, hn2, hmu, hcor, hle, _, _, o, hp, hg⟩ | ⟨h2c, c, hc, hc3⟩
  swap
  · obtain ⟨hF', hcnt, _⟩ := typeIII_flip (H := H) hF hd hds hsV hc hc3
    exact ⟨F, Relation.ReflTransGen.refl, hF, Or.inr ⟨c, hc, hc3, hF', by omega⟩⟩
  have hF' : IsFactor V d (applyS F σ) := factor_flipCol σ.n F hF hv.2.1 hv.2.2.1
  have hz' : ∀ w, IsCorner s w ∨ IsCorner t w → D (applyS F σ) H w = 0 := by
    intro w hw
    unfold applyS
    rw [strip_D_off hp σ.n hv.2.1 hg w (fun j hj heq => by
      rcases hw with h | h
      · exact (hcor j hj).1 (heq ▸ h)
      · exact (hcor j hj).2 (heq ▸ h))]
    exact hz w hw
  have hs' : SolidFor V (applyS F σ) H := hs.of_off fun w hw => by
    unfold applyS
    exact strip_D_off hp σ.n hv.2.1 hg w (fun j hj heq => hw (by rw [heq]; exact hv.2.2.1 j hj))
  have hmove : MovePF V s t F (applyS F σ) := Or.inl ⟨σ, hv, hcor, rfl, hle⟩
  by_cases hlt : ncomp V (applyS F σ) < ncomp V F
  · obtain ⟨F', hr, hF'', hfin⟩ := ihn _ (by omega) _ _ rfl rfl hF' hs' hz'
    exact ⟨F', Relation.ReflTransGen.head hmove hr, hF'', hfin⟩
  · obtain ⟨F', hr, hF'', hfin⟩ := ihm (mu V (applyS F σ) H) (by omega) _ (by omega) rfl hF' hs' hz'
    exact ⟨F', Relation.ReflTransGen.head hmove hr, hF'', hfin⟩


-- One fence step at a cell `b` with `D b ≠ 0`: no `|D|` grows, and `|D b|` drops by 2.
--
lemma fence_step_at {V : Finset Pt} {d : Pt → ℕ} {F H : Finset Edge} (hs : SolidFor V F H)
    (hF : IsFactor V d F) (hH : IsFactor V d H) {z b : Pt} (hbz : IsCorner z b)
    (hbne : D F H b ≠ 0) :
    ∃ F2, FenceStepAny V z F F2 ∧ IsFactor V d F2 ∧
      (∀ w, (D F2 H w).natAbs ≤ (D F H w).natAbs) ∧ (D F2 H b).natAbs + 2 = (D F H b).natAbs := by
  obtain ⟨m, hm⟩ := D_even F H b
  rcases lt_or_gt_of_ne hbne with hneg | hpos
  · have hall : ∀ c, AncP F b c → IsCell V c := by
      intro c hc
      by_contra hnc
      have h1 := hs c hnc
      have h2 := D_le_anc hF hH hc
      omega
    set R := (cells V).filter (AncP F b) with hRdef
    obtain ⟨hF', hbR, hcl, _, _⟩ := smallest_fence hF hall
    have hO := outR_of_closed hcl
    have memR : ∀ c, c ∈ R ↔ AncP F b c := by
      intro c; simp only [R, Finset.mem_filter, mem_cells]
      exact ⟨fun h => h.2, fun h => ⟨hall c h, h⟩⟩
    refine ⟨rflip F R, Or.inl ⟨b, hbz, hall, rfl⟩, hF', fun w => ?_, ?_⟩
    · rw [D_rflip hO w]; unfold rin
      split_ifs with hwR
      · have := D_le_anc hF hH ((memR w).1 hwR); omega
      · omega
    · rw [D_rflip hO b]; unfold rin
      split_ifs
      omega
  · have hall : ∀ c, DesP F b c → IsCell V c := by
      intro c hc
      by_contra hnc
      have h1 := hs c hnc
      have h2 := D_ge_desc hF hH hc
      omega
    set R := (cells V).filter (DesP F b) with hRdef
    obtain ⟨hF', hbR, hcl⟩ := desc_fence hF hall
    have memR : ∀ c, c ∈ R ↔ DesP F b c := by
      intro c; simp only [R, Finset.mem_filter, mem_cells]
      exact ⟨fun h => h.2, fun h => ⟨hall c h, h⟩⟩
    refine ⟨rflip F R, Or.inr ⟨b, hbz, hall, rfl⟩, hF', fun w => ?_, ?_⟩
    · rw [D_rflip_desc hcl w]; unfold rin
      split_ifs with hwR
      · have := D_ge_desc hF hH ((memR w).1 hwR); omega
      · omega
    · rw [D_rflip_desc hcl b]; unfold rin
      split_ifs
      omega

lemma absSum_le {F F2 H : Finset Edge} (hle : ∀ w, (D F2 H w).natAbs ≤ (D F H w).natAbs)
    (z : Pt) : absSumAt F2 H z ≤ absSumAt F H z := by
  have g0 := hle z; have g1 := hle (z.1 - 1, z.2); have g2 := hle (z.1, z.2 - 1)
  have g3 := hle (z.1 - 1, z.2 - 1)
  unfold absSumAt; omega

lemma absSum_lt {F F2 H : Finset Edge} (hle : ∀ w, (D F2 H w).natAbs ≤ (D F H w).natAbs)
    {z b : Pt} (hb : IsCorner z b) (hblt : (D F2 H b).natAbs + 2 = (D F H b).natAbs) :
    absSumAt F2 H z + 2 ≤ absSumAt F H z := by
  have g0 := hle z; have g1 := hle (z.1 - 1, z.2); have g2 := hle (z.1, z.2 - 1)
  have g3 := hle (z.1 - 1, z.2 - 1)
  unfold absSumAt
  rcases isCorner_cases hb with rfl | rfl | rfl | rfl <;> omega

lemma zero_of_absSum {F H : Finset Edge} {z : Pt} (h : absSumAt F H z = 0) :
    ∀ w, IsCorner z w → D F H w = 0 := by
  intro w hw
  unfold absSumAt at h
  rcases isCorner_cases hw with rfl | rfl | rfl | rfl <;> omega

def FenceStep2 (V : Finset Pt) (s t : Pt) (F F' : Finset Edge) : Prop :=
  FenceStepAny V s F F' ∨ FenceStepAny V t F F'

-- **Existence with both endpoints in the grid (P22 + P24).** If a Hamiltonian s–t path exists,
-- then from any path-factor, fence steps at the endpoints' cells, then strips and Type III
-- merges away from the endpoints, reach a Hamiltonian path, possibly after one last Type III
-- flip.
--
theorem hp_moves2 {V : Finset Pt} {d : Pt → ℕ} {H : Finset Edge}
    (hH : IsFactor V d H) (hHam : ncomp V H = 1) {s t : Pt}
    (hd : ∀ z, z ≠ s → z ≠ t → d z = 2) (hds : d s = 1) (hsV : s ∈ V) (hdt : d t = 1)
    (htV : t ∈ V) :
    ∀ F, IsFactor V d F → SolidFor V F H →
      ∃ F1, Relation.ReflTransGen (FenceStep2 V s t) F F1 ∧ IsFactor V d F1 ∧
        ∃ F', Relation.ReflTransGen (MovePF V s t) F1 F' ∧ IsFactor V d F' ∧
          (ncomp V F' = 1 ∨ ∃ c, IsCell V c ∧ ¬ NotTypeIII V F' c ∧
            IsFactor V d (ULHC.flip F' c) ∧ ncomp V (ULHC.flip F' c) = 1) := by
  obtain ⟨s0, s1, s2, s3⟩ := isCorner_four s
  obtain ⟨k0, k1, k2, k3⟩ := isCorner_four t
  suffices key : ∀ n : ℕ, ∀ F, IsFactor V d F → SolidFor V F H → absSumAt F H s + absSumAt F H t ≤ n →
      ∃ F1, Relation.ReflTransGen (FenceStep2 V s t) F F1 ∧ IsFactor V d F1 ∧
        ∃ F', Relation.ReflTransGen (MovePF V s t) F1 F' ∧ IsFactor V d F' ∧
          (ncomp V F' = 1 ∨ ∃ c, IsCell V c ∧ ¬ NotTypeIII V F' c ∧
            IsFactor V d (ULHC.flip F' c) ∧ ncomp V (ULHC.flip F' c) = 1) by
    intro F hF hs
    exact key _ F hF hs le_rfl
  intro n
  induction n with
  | zero =>
    intro F hF hs hn
    have hz : ∀ w, IsCorner s w ∨ IsCorner t w → D F H w = 0 := by
      intro w hw
      rcases hw with hw | hw
      · exact zero_of_absSum (by omega) w hw
      · exact zero_of_absSum (by omega) w hw
    exact ⟨F, Relation.ReflTransGen.refl, hF, theoremA_t2 hH hHam hd hds hsV hdt htV F hF hs hz⟩
  | succ n ih =>
    intro F hF hs hn
    by_cases hall0 : ∀ w, IsCorner s w ∨ IsCorner t w → D F H w = 0
    · refine ih F hF hs ?_
      have z0 := hall0 _ (Or.inl s0); have z1 := hall0 _ (Or.inl s1)
      have z2 := hall0 _ (Or.inl s2); have z3 := hall0 _ (Or.inl s3)
      have z4 := hall0 _ (Or.inr k0); have z5 := hall0 _ (Or.inr k1)
      have z6 := hall0 _ (Or.inr k2); have z7 := hall0 _ (Or.inr k3)
      have e1 : absSumAt F H s = 0 := by unfold absSumAt; rw [z0, z1, z2, z3]; simp
      have e2 : absSumAt F H t = 0 := by unfold absSumAt; rw [z4, z5, z6, z7]; simp
      omega
    push Not at hall0
    obtain ⟨b, hbz, hbne⟩ := hall0
    have hstep : ∃ F2, FenceStep2 V s t F F2 ∧ IsFactor V d F2 ∧
        (∀ w, (D F2 H w).natAbs ≤ (D F H w).natAbs) ∧
        (D F2 H b).natAbs + 2 = (D F H b).natAbs := by
      rcases hbz with hb | hb
      · obtain ⟨F2, h1, h2, h3, h4⟩ := fence_step_at hs hF hH hb hbne
        exact ⟨F2, Or.inl h1, h2, h3, h4⟩
      · obtain ⟨F2, h1, h2, h3, h4⟩ := fence_step_at hs hF hH hb hbne
        exact ⟨F2, Or.inr h1, h2, h3, h4⟩
    obtain ⟨F2, hst, hF2, hle, hblt⟩ := hstep
    have hdrop : absSumAt F2 H s + absSumAt F2 H t ≤ n := by
      have a1 := absSum_le hle s
      have a2 := absSum_le hle t
      rcases hbz with hb | hb
      · have := absSum_lt hle hb hblt; omega
      · have := absSum_lt hle hb hblt; omega
    have hs2 : SolidFor V F2 H := fun w hw => by
      have := hle w; rw [hs w hw] at this; omega
    obtain ⟨F1, hch, rest⟩ := ih F2 hF2 hs2 hdrop
    exact ⟨F1, Relation.ReflTransGen.head hst hch, rest⟩

end HP

end ULHC
