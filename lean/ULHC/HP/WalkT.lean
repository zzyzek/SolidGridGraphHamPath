/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
import ULHC.HP.LocalWalk

/-!
# The walk with "not Type III" only where `D` has the walk's sign (notes P23)

UL's walk step (`walk_local`) asks every cut side of the walk cell for a dark neighbouring side,
and `cut_has_dark_lat` gets it from "the cell across that side is not Type III". The step
needs it only on cut sides whose arc has the walk's orientation and on the side the walk came
in through (`walk_local_o`, by `decide`). Across a side of the walk's orientation `D` keeps the
walk's sign (D never decreases along an arc), and the side the walk came in through faces the
previous walk cell. So, apart from the start, "not Type III" is needed only at cells with
`Good o D`, which are never cells at an endpoint when `D` vanishes there.
-/

namespace ULHC

open Finset Classical

namespace HP

theorem walk_local_o : ∀ (mb mt ml mr pbl pbr ptl ptr q o : Bool) (si : Side),
    (∀ s, mS mb mt ml mr s = true → isCutCell pbl pbr ptl ptr s = false) →
    (∀ s, (isCutCell pbl pbr ptl ptr s && ((outS q (mS mb mt ml mr) s == o) || decide (s = si))) =
        true → (mS mb mt ml mr (latA s) || mS mb mt ml mr (latB s)) = true) →
    ((mb == mt) && (ml == mr) && (mb != ml) = true → ∀ s, isCutCell pbl pbr ptl ptr s = false) →
    isCutCell pbl pbr ptl ptr si = true → outS q (mS mb mt ml mr) si = !o →
    (∃ so, so ≠ si ∧ isCutCell pbl pbr ptl ptr so = true ∧ outS q (mS mb mt ml mr) so = o ∧
        ∀ s', isCutCell pbl pbr ptl ptr s' = true → outS q (mS mb mt ml mr) s' = !o → s' = si) ∨
    (∃ d, mS mb mt ml mr d = true ∧ mS mb mt ml mr d.opp = false ∧
        mS mb mt ml mr (latA d) = false ∧ mS mb mt ml mr (latB d) = false ∧
        (si = latA d ∨ si = latB d) ∧ isCutCell pbl pbr ptl ptr d.opp = false ∧
        outS q (mS mb mt ml mr) d.opp = o ∧
        ∀ s, isCutCell pbl pbr ptl ptr s = true → outS q (mS mb mt ml mr) s = !o) := by
  decide

theorem step_cell_o {V : Finset Pt} {F : Finset Edge} {P : Finset Pt} (hB : Border V F P)
    (w : Pt) (o : Bool) (si : Side) (hcut : Cut P (sideEdge w si)) (hin : outArc F w si = !o)
    (hlat : ∀ s, Cut P (sideEdge w s) → (outArc F w s = o ∨ s = si) →
      sideEdge w (latA s) ∈ F ∨ sideEdge w (latB s) ∈ F)
    (halt : Alt F w → ∀ s, ¬ Cut P (sideEdge w s)) :
    (∃ so, so ≠ si ∧ Cut P (sideEdge w so) ∧ outArc F w so = o ∧
        ∀ s', Cut P (sideEdge w s') → outArc F w s' = !o → s' = si) ∨
    (∃ d, sideEdge w d ∈ F ∧ sideEdge w d.opp ∉ F ∧ sideEdge w (latA d) ∉ F ∧
        sideEdge w (latB d) ∉ F ∧ (si = latA d ∨ si = latB d) ∧ ¬ Cut P (sideEdge w d.opp) ∧
        outArc F w d.opp = o ∧ ∀ s, Cut P (sideEdge w s) → outArc F w s = !o) := by
  obtain ⟨x, y⟩ := w
  set mb := decide (bot (x, y) ∈ F)
  set mt := decide (top (x, y) ∈ F)
  set ml := decide (lft (x, y) ∈ F)
  set mr := decide (rgt (x, y) ∈ F)
  set pbl := decide ((x, y) ∈ P)
  set pbr := decide ((x + 1, y) ∈ P)
  set ptl := decide ((x, y + 1) ∈ P)
  set ptr := decide ((x + 1, y + 1) ∈ P)
  have hm : ∀ s, mS mb mt ml mr s = true ↔ sideEdge (x, y) s ∈ F := by
    intro s; cases s <;> simp [mS, mb, mt, ml, mr, sideEdge]
  have hc : ∀ s, isCutCell pbl pbr ptl ptr s = true ↔ Cut P (sideEdge (x, y) s) := by
    intro s
    cases s <;> simp only [isCutCell, Cut, sideEdge, bot, top, lft, rgt, Edge.q, pbl, pbr, ptl, ptr]
    · by_cases h1 : (x, y) ∈ P <;> by_cases h2 : (x + 1, y) ∈ P <;> simp [h1, h2]
    · by_cases h1 : (x, y + 1) ∈ P <;> by_cases h2 : (x + 1, y + 1) ∈ P <;> simp [h1, h2]
    · by_cases h1 : (x, y) ∈ P <;> by_cases h2 : (x, y + 1) ∈ P <;> simp [h1, h2]
    · by_cases h1 : (x + 1, y) ∈ P <;> by_cases h2 : (x + 1, y + 1) ∈ P <;> simp [h1, h2]
  have hmf : ∀ s, mS mb mt ml mr s = false ↔ sideEdge (x, y) s ∉ F := by
    intro s; rw [← hm s]; simp
  have hcf : ∀ s, isCutCell pbl pbr ptl ptr s = false ↔ ¬ Cut P (sideEdge (x, y) s) := by
    intro s; rw [← hc s]; simp
  have ho : ∀ s, outS (par (x, y)) (mS mb mt ml mr) s = outArc F (x, y) s := by
    intro s
    rw [outArc_eq]
    cases s <;> rfl
  have key := walk_local_o mb mt ml mr pbl pbr ptl ptr (par (x, y)) o si
    (fun s hs => (hcf s).2 (hB.not_cut ((hm s).1 hs)))
    (by
      intro s hs
      simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at hs
      obtain ⟨hs1, hs2⟩ := hs
      rw [ho] at hs2
      rcases hlat s ((hc s).1 hs1) hs2 with h | h
      · rw [(hm _).2 h]; rfl
      · rw [(hm _).2 h]; simp)
    (by
      intro h s
      apply (hcf s).2
      apply halt _ s
      simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at h
      obtain ⟨⟨h1, h2⟩, h3⟩ := h
      unfold Alt
      simp only [mb, mt, ml, mr] at h1 h2 h3
      by_cases hb : bot (x, y) ∈ F <;> by_cases hl : lft (x, y) ∈ F <;> simp_all)
    ((hc si).2 hcut)
    (by rw [ho]; exact hin)
  rcases key with ⟨so, h1, h2, h3, h4⟩ | ⟨d, h1, h2, h3, h4, h5, h6, h7, h8⟩
  · left
    refine ⟨so, h1, (hc so).1 h2, by rw [← ho]; exact h3, ?_⟩
    intro s' hs' ho'
    exact h4 s' ((hc s').2 hs') (by rw [ho]; exact ho')
  · right
    exact ⟨d, (hm d).1 h1, (hmf _).1 h2, (hmf _).1 h3, (hmf _).1 h4, h5, (hcf _).1 h6,
      by rw [← ho]; exact h7, fun s hs => by rw [← ho]; exact h8 s ((hc s).2 hs)⟩

-- A cut side has a dark neighbouring side when the cell across it is not Type III.
--
lemma cut_has_dark_lat_r {V : Finset Pt} {F : Finset Edge} {P : Finset Pt}
    (_hIn : Inside V F) (hB : Border V F P)
    {w : Pt} (hw : IsCell V w) (hw2 : Deg2Cell F w) (s : Side)
    (hT : NotTypeIII V F (nb w s)) (hcut : Cut P (sideEdge w s)) :
    sideEdge w (latA s) ∈ F ∨ sideEdge w (latB s) ∈ F := by
  by_contra hn
  push Not at hn
  obtain ⟨n1, n2⟩ := hn
  rw [← lat1_eq] at n1
  rw [← lat2_eq] at n2
  have hfr : front w s ∉ F := fun h => hB.not_cut h hcut
  obtain ⟨wb1, wb2, wf1, wf2⟩ := isCell_corners hw s
  have d1 := deg_front1 w s F
  have d2 := deg_front2 w s F
  rw [deg2_front1 hw2 s] at d1
  rw [deg2_front2 hw2 s] at d2
  have i1 : ind F (lat1 w s) = 0 := by simp [ind, n1]
  have i2 : ind F (lat2 w s) = 0 := by simp [ind, n2]
  have i3 : ind F (front w s) = 0 := by simp [ind, hfr]
  have mem1 : ∀ e, ind F e = 1 → e ∈ F := by
    intro e h; unfold ind at h; split_ifs at h with h'; exact h'
  rw [i1, i3] at d1
  rw [i2, i3] at d2
  have l1 : lat1 (nb w s) s ∈ F := by
    have := ind_le_one F (lat1 (nb w s) s)
    have := ind_le_one F (outer1 w s)
    exact mem1 _ (by omega)
  have l2 : lat2 (nb w s) s ∈ F := by
    have := ind_le_one F (lat2 (nb w s) s)
    have := ind_le_one F (outer2 w s)
    exact mem1 _ (by omega)
  set r := nb w s
  have c1 : Conn F (back1 r s) (front1 r s) := (ends_lat1 r s).conn l1
  have c2 : Conn F (back2 r s) (front2 r s) := (ends_lat2 r s).conn l2
  have hjoin : Conn F (back1 r s) (back2 r s) := by
    by_cases hf : front r s ∈ F
    · exact (c1.trans ((ends_front r s).conn hf)).trans c2.symm
    · have hbk : back r s ∉ F := by rw [back_nb]; exact hfr
      have ha : Alt F r := by
        rw [lat1_eq] at l1
        rw [lat2_eq] at l2
        simp only [back, front, sideEdge] at hbk hf
        obtain ⟨x, y⟩ := r
        cases s <;> simp only [latA, latB, sideEdge, Side.opp] at l1 l2 hbk hf <;> unfold Alt <;>
          tauto
      obtain ⟨k1, k2, k3⟩ := alt_corners_conn' hT ha
      obtain ⟨x, y⟩ := r
      cases s <;> simp only [back1, back2] at * <;>
        first
        | exact k1
        | exact k2.symm.trans k3
        | exact k1.symm.trans k3
        | exact k2
  rw [back1_nb, back2_nb] at hjoin
  apply hcut |> fun h => ?_
  have := hB.same_side hjoin
  have hends := ends_front w s
  unfold Cut at hcut
  rcases hends with ⟨q1, q2⟩ | ⟨q1, q2⟩ <;> simp only [front] at q1 q2 <;> rw [q1, q2] at hcut <;>
    tauto

section boundaryEndpointsWalk

variable {V : Finset Pt} {d : Pt → ℕ} {F H : Finset Edge} (hF : IsFactor V d F)
  (hH : IsFactor V d H)
include hF hH

-- The step at a walk cell, from "not Type III" at cells of the walk's sign and across the
-- entry side.
--
lemma step_t {P : Finset Pt} (hB : Border V F P) {o : Bool}
    (hTg : ∀ c, Good o (D F H c) → NotTypeIII V F c)
    {w : Pt} (hw : IsCell V w) (hw2 : Deg2Cell F w) (hg : Good o (D F H w))
    (si : Side) (hcut : Cut P (sideEdge w si)) (hin : outArc F w si = !o)
    (hLi : sideEdge w (latA si) ∈ F ∨ sideEdge w (latB si) ∈ F) :
    (∃ so, so ≠ si ∧ Cut P (sideEdge w so) ∧ outArc F w so = o ∧
        ∀ s', Cut P (sideEdge w s') → outArc F w s' = !o → s' = si) ∨
    (∃ d, sideEdge w d ∈ F ∧ sideEdge w d.opp ∉ F ∧ sideEdge w (latA d) ∉ F ∧
        sideEdge w (latB d) ∉ F ∧ (si = latA d ∨ si = latB d) ∧ ¬ Cut P (sideEdge w d.opp) ∧
        outArc F w d.opp = o ∧ ∀ s, Cut P (sideEdge w s) → outArc F w s = !o) :=
  step_cell_o hB w o si hcut hin
    (fun s hc h => h.elim
      (fun ho => cut_has_dark_lat_r (Inside.of_factor hF) hB hw hw2 s
        (hTg _ (Good.step_f hF hH ho hg)) hc)
      (fun he => he ▸ hLi))
    (fun ha s => alt_no_cut_l hB (hTg w hg) ha s)

lemma uniq_t {P : Finset Pt} (hB : Border V F P) {o : Bool}
    (hTg : ∀ c, Good o (D F H c) → NotTypeIII V F c)
    {w : Pt} (hw : IsCell V w) (hw2 : Deg2Cell F w) (hg : Good o (D F H w))
    (si : Side) (hcut : Cut P (sideEdge w si)) (hin : outArc F w si = !o)
    (hLi : sideEdge w (latA si) ∈ F ∨ sideEdge w (latB si) ∈ F) (hout : Out F P o w) :
    ∀ s1 s2, Cut P (sideEdge w s1) → outArc F w s1 = !o →
      Cut P (sideEdge w s2) → outArc F w s2 = !o → s1 = s2 := by
  rcases step_t hF hH hB hTg hw hw2 hg si hcut hin hLi with
    ⟨so, _, _, _, h4⟩ | ⟨_, _, _, _, _, _, _, _, hall'⟩
  · exact fun s1 s2 c1 o1 c2 o2 => (h4 s1 c1 o1).trans (h4 s2 c2 o2).symm
  · obtain ⟨so', hc', ho'⟩ := hout
    have := hall' so' hc'
    rw [ho'] at this
    cases o <;> simp at this

lemma stop_t {P : Finset Pt} (hB : Border V F P) {o : Bool}
    (hTg : ∀ c, Good o (D F H c) → NotTypeIII V F c)
    {w : Pt} (hw : IsCell V w) (hw2 : Deg2Cell F w) (hg : Good o (D F H w))
    (si : Side) (hcut : Cut P (sideEdge w si)) (hin : outArc F w si = !o)
    (hLi : sideEdge w (latA si) ∈ F ∨ sideEdge w (latB si) ∈ F) (hno : ¬ Out F P o w) : Stop F P o w := by
  rcases step_t hF hH hB hTg hw hw2 hg si hcut hin hLi with
    ⟨so, _, h2, h3, _⟩ | ⟨d, h1, h2, h3, h4, h5, h6, h7, _⟩
  · exact absurd ⟨so, h2, h3⟩ hno
  · exact ⟨d, h1, h2, h3, h4, ⟨si, h5, hcut, hin⟩, h6, h7⟩

end boundaryEndpointsWalk

theorem phase1_t {V : Finset Pt} {d : Pt → ℕ} {F H : Finset Edge} {P : Finset Pt}
    (hF : IsFactor V d F) (hH : IsFactor V d H) (hs : SolidFor V F H) (hB : Border V F P)
    (o : Bool) (hTg : ∀ c, Good o (D F H c) → NotTypeIII V F c) (hloc : ∀ w, Good o (D F H w) → Deg2Cell F w)
    (v : Pt) (s0 : Side) (hcut : Cut P (sideEdge v s0)) (hin : outArc F v s0 = !o)
    (hjump : if o then D F H v = D F H (nb v s0) + 2 else D F H v = D F H (nb v s0) - 2)
    (hgood : Good o (D F H v))
    (hL0 : sideEdge v (latA s0) ∈ F ∨ sideEdge v (latB s0) ∈ F) :
    ∃ w, IsCell V w ∧ Good o (D F H w) ∧ Stop F P o w := by
  set u := nb v s0
  let wk : ℕ → Pt := fun k => (sig F P o)^[k] v
  have wk0 : wk 0 = v := rfl
  have wks : ∀ k, wk (k + 1) = sig F P o (wk k) := fun k => Function.iterate_succ_apply' _ _ _
  -- Invariant along the walk.
  have inv : ∀ k, (∀ i < k, Out F P o (wk i)) →
      (∃ si, Cut P (sideEdge (wk k) si) ∧ outArc F (wk k) si = !o ∧
        (sideEdge (wk k) (latA si) ∈ F ∨ sideEdge (wk k) (latB si) ∈ F)) ∧
        Good o (D F H (wk k)) ∧
        (if o then D F H v ≤ D F H (wk k) else D F H (wk k) ≤ D F H v) := by
    intro k
    induction k with
    | zero =>
      intro _
      refine ⟨⟨s0, hcut, hin, hL0⟩, hgood, ?_⟩
      rw [wk0]; cases o <;> simp
    | succ k ih =>
      intro hall
      obtain ⟨_, hg, hm⟩ := ih (fun i hi => hall i (by omega))
      obtain ⟨so, hsig, hc, ho⟩ := sig_spec o (hall k (by omega))
      rw [wks, hsig]
      have hg' := Good.step_f hF hH ho hg
      refine ⟨⟨so.opp, by rw [sideEdge_nb_opp]; exact hc, by rw [outArc_nb_opp, ho],
          cut_has_dark_lat_r (Inside.of_factor hF) hB (Good.isCell_f hs hg') (hloc _ hg')
            so.opp (by rw [nb_nb_opp]; exact hTg _ hg) (by rw [sideEdge_nb_opp]; exact hc)⟩,
        Good.step_f hF hH ho hg, ?_⟩
      have := D_mono_f hF hH o (wk k) so ho
      cases o <;> simp only [Bool.false_eq_true, ite_false, ite_true] at hm this ⊢ <;> omega
  set N := (cells V).card
  by_cases hall : ∀ k ≤ N, Out F P o (wk k)
  · exfalso
    -- No cell repeats.
    have inj : ∀ i j, i < j → j ≤ N → wk i ≠ wk j := by
      intro i
      induction i with
      | zero =>
        intro j hj hjN heq
        obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
        obtain ⟨so, hsig, hc, ho⟩ := sig_spec o (hall j' (by omega))
        rw [wk0, wks, hsig] at heq
        -- `v` is entered from `wk j'` through `so.opp`, and from `u` through `s0`.
        have uniq := uniq_t hF hH hB hTg (Good.isCell_f hs hgood) (hloc _ hgood) hgood s0 hcut hin hL0
          (by have := hall 0 (by omega); rwa [wk0] at this)
        have e := uniq s0 so.opp hcut hin
          (by rw [heq, sideEdge_nb_opp]; exact hc) (by rw [heq, outArc_nb_opp, ho])
        have hwu : wk j' = u := by
          rw [show u = nb v s0 from rfl, e, heq, nb_nb_opp]
        obtain ⟨_, _, hm⟩ := inv j' (fun i hi => hall i (by omega))
        rw [hwu] at hm
        cases o <;> simp only [Bool.false_eq_true, ite_false, ite_true] at hm hjump <;> omega
      | succ i ih =>
        intro j hij hjN heq
        obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
        obtain ⟨so1, hs1, hc1, ho1⟩ := sig_spec o (hall i (by omega))
        obtain ⟨so2, hs2, hc2, ho2⟩ := sig_spec o (hall j' (by omega))
        rw [wks, wks, hs1, hs2] at heq
        set z := nb (wk i) so1
        have hzc := (inv (i + 1) (fun k hk => hall k (by omega))).2.1
        rw [wks, hs1] at hzc
        have uniq := uniq_t hF hH hB hTg (Good.isCell_f hs hzc) (hloc _ hzc) hzc so1.opp
          (by rw [sideEdge_nb_opp]; exact hc1) (by rw [outArc_nb_opp, ho1])
          (cut_has_dark_lat_r (Inside.of_factor hF) hB (Good.isCell_f hs hzc) (hloc _ hzc)
            so1.opp (by rw [nb_nb_opp]; exact hTg _ (inv i (fun k hk => hall k (by omega))).2.1)
            (by rw [sideEdge_nb_opp]; exact hc1))
          (by have := hall (i + 1) (by omega); rwa [wks, hs1] at this)
        have e := uniq so1.opp so2.opp (by rw [sideEdge_nb_opp]; exact hc1)
          (by rw [outArc_nb_opp, ho1]) (by rw [heq, sideEdge_nb_opp]; exact hc2)
          (by rw [heq, outArc_nb_opp, ho2])
        apply ih j' (by omega) (by omega)
        have h1 : nb z so1.opp = wk i := nb_nb_opp _ _
        have h2 : nb z so2.opp = wk j' := by rw [heq, nb_nb_opp]
        rw [← h1, ← h2, e]
    -- Pigeonhole.
    have hmaps : ∀ k ∈ Finset.range (N + 1), wk k ∈ cells V := by
      intro k hk
      rw [Finset.mem_range] at hk
      exact mem_cells.2 (Good.isCell_f hs
        (inv k (fun i hi => hall i (by omega))).2.1)
    have hinj : Set.InjOn wk (Finset.range (N + 1)) := by
      intro i hi j hj heq
      simp only [Finset.coe_range, Set.mem_Iio] at hi hj
      by_contra hne
      rcases Nat.lt_or_gt_of_ne hne with h | h
      · exact inj i j h (by omega) heq
      · exact inj j i h (by omega) heq.symm
    have := Finset.card_le_card_of_injOn wk hmaps hinj
    simp only [Finset.card_range] at this
    omega
  · push Not at hall
    obtain ⟨k, hkN, hk⟩ := hall
    -- The first cell with no way out.
    have ex : ∃ k, ¬ Out F P o (wk k) := ⟨k, hk⟩
    let k0 := Nat.find ex
    have hk0 : ¬ Out F P o (wk k0) := Nat.find_spec ex
    have hbefore : ∀ i < k0, Out F P o (wk i) := fun i hi => by
      have := Nat.find_min ex hi; push Not at this; exact this
    obtain ⟨⟨si, hsc, hsi, hsT⟩, hg, _⟩ := inv k0 hbefore
    have hc := Good.isCell_f hs hg
    exact ⟨wk k0, hc, hg, stop_t hF hH hB hTg hc (hloc _ hg) hg si hsc hsi hsT hk0⟩


end HP

end ULHC
