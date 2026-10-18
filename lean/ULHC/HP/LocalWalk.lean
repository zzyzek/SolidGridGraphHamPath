/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
import ULHC.Phase2

/-!
# The walk and Phase II with local degree hypotheses (s–t path extension)

The ULHC walk lemmas assume degree 2 at every vertex (`Deg2 V F`). Their proofs use it only
by degree forcing at corners of the cells the walk and its strip visit, and those cells all
have a potential `D` of the walk's sign (`Good`). Here `F` and `H` are factors for the same
degree function `d` (path-factors with the same endpoints, for instance), and the only extra
hypothesis is `hloc`: every cell with `Good o (D F H w)` has degree 2 at its four corners.
For a path-factor this holds when `D` vanishes on the cells with s or t as a corner.

The proofs are those of `Walk.lean`, `Phase.lean`, `Phase2.lean` with the degree uses
replaced (generated from them); `strip_mu` needs no change.
-/

namespace ULHC

open Finset Classical

namespace HP

-- Degree 2 at the four corners of cell `w`.
--
def Deg2Cell (F : Finset Edge) (w : Pt) : Prop :=
  deg F w = 2 ∧ deg F (w.1 + 1, w.2) = 2 ∧ deg F (w.1, w.2 + 1) = 2 ∧ deg F (w.1 + 1, w.2 + 1) = 2

lemma deg2_front1 {F : Finset Edge} {w : Pt} (h : Deg2Cell F w) (s : Side) :
    deg F (front1 w s) = 2 := by
  obtain ⟨x, y⟩ := w
  obtain ⟨h1, h2, h3, h4⟩ := h
  cases s <;> simp only [front1] <;> assumption

lemma deg2_front2 {F : Finset Edge} {w : Pt} (h : Deg2Cell F w) (s : Side) :
    deg F (front2 w s) = 2 := by
  obtain ⟨x, y⟩ := w
  obtain ⟨h1, h2, h3, h4⟩ := h
  cases s <;> simp only [front2] <;> assumption

section dmono

variable {V : Finset Pt} {d : Pt → ℕ} {F H : Finset Edge} (hF : IsFactor V d F) (hH : IsFactor V d H)
include hF hH

lemma D_mono_f (o : Bool) (c : Pt) (s : Side) (h : outArc F c s = o) :
    if o then D F H c ≤ D F H (nb c s) else D F H (nb c s) ≤ D F H c := by
  have := D_step hF hH c s
  rw [h] at this
  cases o <;> simp only [Bool.false_eq_true, ite_false, ite_true] at this ⊢ <;>
    split_ifs at this <;> omega

lemma Good.step_f {o : Bool} {c : Pt} {s : Side} (h : outArc F c s = o)
    (hg : Good o (D F H c)) : Good o (D F H (nb c s)) := by
  have := D_mono_f hF hH o c s h
  unfold Good at *
  cases o <;> simp only [Bool.false_eq_true, ite_false, ite_true] at this hg ⊢ <;> omega

omit hF hH in
lemma Good.isCell_f (hs : SolidFor V F H) {o : Bool} {c : Pt} (hg : Good o (D F H c)) : IsCell V c := by
  by_contra h
  have := hs c h
  unfold Good at hg; rw [this] at hg
  cases o <;> simp at hg

end dmono

-- A cut side always has a dark neighbouring side (degree 2 needed at the cell's corners only).
--
lemma cut_has_dark_lat_loc {V : Finset Pt} {F : Finset Edge} {P : Finset Pt}
    (hIn : Inside V F) (hB : Border V F P) (hT : NoTypeIII V F)
    {w : Pt} (hw : IsCell V w) (hw2 : Deg2Cell F w) (s : Side) (hcut : Cut P (sideEdge w s)) :
    sideEdge w (latA s) ∈ F ∨ sideEdge w (latB s) ∈ F := by
  by_contra hn
  push Not at hn
  obtain ⟨n1, n2⟩ := hn
  rw [← lat1_eq] at n1
  rw [← lat2_eq] at n2
  have hfr : front w s ∉ F := fun h => hB.not_cut h hcut
  -- Forcing at the two front corners.
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
  have rf1 : front1 r s ∈ V := conn_mem hIn (by rw [back1_nb]; exact wf1) c1
  have rf2 : front2 r s ∈ V := conn_mem hIn (by rw [back2_nb]; exact wf2) c2
  have hr : IsCell V r := isCell_of_corners r s (by rw [back1_nb]; exact wf1)
    (by rw [back2_nb]; exact wf2) rf1 rf2
  -- The two front corners of `w` are joined, so the front is not cut.
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
      obtain ⟨k1, k2, k3⟩ := alt_corners_conn hT hr ha
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

lemma uniq_of_out_loc {V : Finset Pt} {F : Finset Edge} {P : Finset Pt}
    (hIn : Inside V F) (hB : Border V F P) (hT : NoTypeIII V F) (o : Bool)
    {w : Pt} (hw : IsCell V w) (hw2 : Deg2Cell F w) (si : Side) (hcut : Cut P (sideEdge w si))
    (hin : outArc F w si = !o) (hout : Out F P o w) :
    ∀ s1 s2, Cut P (sideEdge w s1) → outArc F w s1 = !o →
      Cut P (sideEdge w s2) → outArc F w s2 = !o → s1 = s2 := by
  rcases step_cell hB w o (fun s h => cut_has_dark_lat_loc hIn hB hT hw hw2 s h)
      (fun ha => alt_no_cut hB hT hw ha) si hcut hin with
    ⟨so, _, _, _, h4⟩ | ⟨_, _, _, _, _, _, _, _, hall'⟩
  · exact fun s1 s2 c1 o1 c2 o2 => (h4 s1 c1 o1).trans (h4 s2 c2 o2).symm
  · obtain ⟨so', hc', ho'⟩ := hout
    have := hall' so' hc'
    rw [ho'] at this
    cases o <;> simp at this

lemma stop_of_not_out_loc {V : Finset Pt} {F : Finset Edge} {P : Finset Pt}
    (hIn : Inside V F) (hB : Border V F P) (hT : NoTypeIII V F) (o : Bool)
    {w : Pt} (hw : IsCell V w) (hw2 : Deg2Cell F w) (he : Entered F P o w)
    (hno : ¬ Out F P o w) : Stop F P o w := by
  obtain ⟨si, hcut, hin⟩ := he
  rcases step_cell hB w o (fun s h => cut_has_dark_lat_loc hIn hB hT hw hw2 s h)
      (fun ha => alt_no_cut hB hT hw ha) si hcut hin with
    ⟨so, _, h2, h3, _⟩ | ⟨d, h1, h2, h3, h4, h5, h6, h7, _⟩
  · exact absurd ⟨so, h2, h3⟩ hno
  · exact ⟨d, h1, h2, h3, h4, ⟨si, h5, hcut, hin⟩, h6, h7⟩

-- **Phase I** for factors with a common degree function, with degree 2 needed only at the
-- corners of cells where `D` has the walk's sign.
--
theorem phase1_loc {V : Finset Pt} {d : Pt → ℕ} {F H : Finset Edge} {P : Finset Pt}
    (hF : IsFactor V d F) (hH : IsFactor V d H) (hs : SolidFor V F H) (hB : Border V F P)
    (hT : NoTypeIII V F) (o : Bool) (hloc : ∀ w, Good o (D F H w) → Deg2Cell F w)
    (v : Pt) (s0 : Side) (hcut : Cut P (sideEdge v s0)) (hin : outArc F v s0 = !o)
    (hjump : if o then D F H v = D F H (nb v s0) + 2 else D F H v = D F H (nb v s0) - 2)
    (hgood : Good o (D F H v)) :
    ∃ w, IsCell V w ∧ Good o (D F H w) ∧ Stop F P o w := by
  set u := nb v s0
  let wk : ℕ → Pt := fun k => (sig F P o)^[k] v
  have wk0 : wk 0 = v := rfl
  have wks : ∀ k, wk (k + 1) = sig F P o (wk k) := fun k => Function.iterate_succ_apply' _ _ _
  -- Invariant along the walk.
  have inv : ∀ k, (∀ i < k, Out F P o (wk i)) →
      Entered F P o (wk k) ∧ Good o (D F H (wk k)) ∧
        (if o then D F H v ≤ D F H (wk k) else D F H (wk k) ≤ D F H v) := by
    intro k
    induction k with
    | zero =>
      intro _
      refine ⟨⟨s0, hcut, hin⟩, hgood, ?_⟩
      rw [wk0]; cases o <;> simp
    | succ k ih =>
      intro hall
      obtain ⟨_, hg, hm⟩ := ih (fun i hi => hall i (by omega))
      obtain ⟨so, hsig, hc, ho⟩ := sig_spec o (hall k (by omega))
      rw [wks, hsig]
      refine ⟨⟨so.opp, by rw [sideEdge_nb_opp]; exact hc, by rw [outArc_nb_opp, ho]⟩,
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
        have uniq := uniq_of_out_loc (Inside.of_factor hF) hB hT o (Good.isCell_f hs hgood) (hloc _ hgood) s0 hcut hin
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
        have uniq := uniq_of_out_loc (Inside.of_factor hF) hB hT o (Good.isCell_f hs hzc) (hloc _ hzc) so1.opp
          (by rw [sideEdge_nb_opp]; exact hc1) (by rw [outArc_nb_opp, ho1])
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
    obtain ⟨he, hg, _⟩ := inv k0 hbefore
    have hc := Good.isCell_f hs hg
    exact ⟨wk k0, hc, hg, stop_of_not_out_loc (Inside.of_factor hF) hB hT o hc (hloc _ hg) he hk0⟩

lemma column_loc {V : Finset Pt} {d : Pt → ℕ} {F H : Finset Edge}
    (hF : IsFactor V d F) (hH : IsFactor V d H) (hs : SolidFor V F H)
    {w : Pt} {s : Side} {o : Bool} (hp : ParOK w s o)
    (_hb : back w s ∈ F) (hl1 : lat1 w s ∉ F) (hl2 : lat2 w s ∉ F) (hg : Good o (D F H w))
    (hloc : ∀ w, Good o (D F H w) → Deg2Cell F w) :
    ∀ J, (∀ j < J, front (cellJ w s j) s ∈ F ↔ j % 2 = 1) →
      (∀ j ≤ J, (lat1 (cellJ w s j) s ∈ F ↔ j % 2 = 1) ∧
        (lat2 (cellJ w s j) s ∈ F ↔ j % 2 = 1)) ∧
      ∀ j ≤ J, Good o (D F H (cellJ w s j)) := by
  intro J
  induction J with
  | zero =>
    intro _
    refine ⟨fun j hj => ?_, fun j hj => ?_⟩
    · obtain rfl : j = 0 := by omega
      rw [cellJ_zero]; simp [hl1, hl2]
    · obtain rfl : j = 0 := by omega
      rw [cellJ_zero]; exact hg
  | succ J ih =>
    intro hc
    obtain ⟨hlat, hgood⟩ := ih (fun j hj => hc j (by omega))
    have hfJ := hc J (by omega)
    have hgJ := hgood J le_rfl
    have hcJ : IsCell V (cellJ w s J) := Good.isCell_f hs hgJ
    obtain ⟨_, _, f1V, f2V⟩ := isCell_corners hcJ s
    have d1 := deg_front1 (cellJ w s J) s F
    have d2 := deg_front2 (cellJ w s J) s F
    rw [deg2_front1 (hloc _ hgJ) s] at d1
    rw [deg2_front2 (hloc _ hgJ) s] at d2
    rw [nb_cellJ] at d1 d2
    have mem1 : ∀ e, ind F e = 1 → e ∈ F := by
      intro e h; unfold ind at h; split_ifs at h with h'; exact h'
    have nmem : ∀ e, ind F e = 0 → e ∉ F := by
      intro e h he; simp [ind, he] at h
    have i_of : ∀ e, ∀ p : Prop, (e ∈ F ↔ p) → p → ind F e = 1 := by
      intro e p h hp; unfold ind; rw [ite_eq_left (h.2 hp)]
    have i_of' : ∀ e, ∀ p : Prop, (e ∈ F ↔ p) → ¬ p → ind F e = 0 := by
      intro e p h hp; unfold ind; rw [ite_eq_right (fun h' => hp (h.1 h'))]
    have b1 := ind_le_one F (lat1 (cellJ w s (J + 1)) s)
    have b2 := ind_le_one F (lat2 (cellJ w s (J + 1)) s)
    have b3 := ind_le_one F (outer1 (cellJ w s J) s)
    have b4 := ind_le_one F (outer2 (cellJ w s J) s)
    have newlat : (lat1 (cellJ w s (J + 1)) s ∈ F ↔ (J + 1) % 2 = 1) ∧
        (lat2 (cellJ w s (J + 1)) s ∈ F ↔ (J + 1) % 2 = 1) := by
      rcases Nat.mod_two_eq_zero_or_one J with h | h
      · have a1 := i_of' _ _ (hlat J le_rfl).1 (by omega)
        have a2 := i_of' _ _ (hlat J le_rfl).2 (by omega)
        have a3 := i_of' _ _ hfJ (by omega)
        rw [a1, a3] at d1
        rw [a2, a3] at d2
        have q : (J + 1) % 2 = 1 := by omega
        exact ⟨⟨fun _ => q, fun _ => mem1 _ (by omega)⟩, ⟨fun _ => q, fun _ => mem1 _ (by omega)⟩⟩
      · have a1 := i_of _ _ (hlat J le_rfl).1 (by omega)
        have a2 := i_of _ _ (hlat J le_rfl).2 (by omega)
        have a3 := i_of _ _ hfJ (by omega)
        rw [a1, a3] at d1
        rw [a2, a3] at d2
        have q : ¬ (J + 1) % 2 = 1 := by omega
        exact ⟨⟨fun h' => absurd h' (nmem _ (by omega)), fun h' => absurd h' q⟩,
          ⟨fun h' => absurd h' (nmem _ (by omega)), fun h' => absurd h' q⟩⟩
    refine ⟨fun j hj => ?_, fun j hj => ?_⟩
    · rcases (show j ≤ J ∨ j = J + 1 by omega) with h | rfl
      · exact hlat j h
      · exact newlat
    · rcases (show j ≤ J ∨ j = J + 1 by omega) with h | rfl
      · exact hgood j h
      · rw [← nb_cellJ]
        exact Good.step_f hF hH (front_out hp J hfJ) hgJ

-- **Phase II** for factors with a common degree function.
--
theorem phase2_loc {V : Finset Pt} {d : Pt → ℕ} {F H : Finset Edge} {P : Finset Pt}
    (hF : IsFactor V d F) (hH : IsFactor V d H) (hs : SolidFor V F H) (hB : Border V F P)
    {w : Pt} {o : Bool} (hloc : ∀ w, Good o (D F H w) → Deg2Cell F w)
    (hg : Good o (D F H w)) (hst : Stop F P o w) :
    ∃ s n, 2 ≤ n ∧ StripPat F w s n ∧ (∀ j < n, IsCell V (cellJ w s j)) ∧
      (∀ j < n, Good o (D F H (cellJ w s j))) ∧ ParOK w s o ∧
      ¬ Conn F (back1 w s) (front1 w s) := by
  obtain ⟨d, hd, hdo, hla, hlb, ⟨si, hsi, hcut, hin⟩, hnc, hout⟩ := hst
  set s := d.opp
  have hb : back w s ∈ F := by simp only [back, s, opp_opp]; exact hd
  have hf0 : front w s ∉ F := hdo
  have hl1 : lat1 w s ∉ F := by rw [lat1_eq, latA_opp]; exact hla
  have hl2 : lat2 w s ∉ F := by rw [lat2_eq, latB_opp]; exact hlb
  -- Parity from the entry side.
  have hp : ParOK w s o := by
    unfold ParOK
    rw [outArc_eq] at hin
    have hsiF : sideEdge w si ∉ F := by rcases hsi with rfl | rfl <;> assumption
    have hh : si.horiz = !s.horiz := by
      rcases hsi with rfl | rfl
      · rw [← horiz_latA, latA_opp]
      · rw [← horiz_latB, latB_opp]
    rw [hh] at hin
    simp only [hsiF, decide_false] at hin
    cases hs' : s.horiz <;> cases o <;> cases hq : par w <;> simp_all
  -- Opposite sides of the border.
  have hsep : ¬ Conn F (back1 w s) (front1 w s) := by
    intro hc
    have e1 := hB.same_side hc
    have e2 := hB.same_side ((ends_back w s).conn hb)
    have hfc : ¬ Cut P (front w s) := hnc
    have ef := ends_front w s
    unfold Cut at hfc
    have e3 : front1 w s ∈ P ↔ front2 w s ∈ P := by
      rcases ef with ⟨q1, q2⟩ | ⟨q1, q2⟩ <;> rw [q1, q2] at hfc <;> tauto
    rcases hsi with rfl | rfl
    · have := ends_lat1 w s
      rw [lat1_eq, latA_opp] at this
      unfold Cut at hcut
      rcases this with ⟨q1, q2⟩ | ⟨q1, q2⟩ <;> rw [q1, q2] at hcut <;> tauto
    · have := ends_lat2 w s
      rw [lat2_eq, latB_opp] at this
      unfold Cut at hcut
      rcases this with ⟨q1, q2⟩ | ⟨q1, q2⟩ <;> rw [q1, q2] at hcut <;> tauto
  -- The first cell where the pattern stops continuing.
  obtain ⟨J0, hJ0⟩ := exists_not_cell V w s
  have hex : ∃ J, ¬ (front (cellJ w s J) s ∈ F ↔ J % 2 = 1) := by
    by_contra hall
    push Not at hall
    obtain ⟨_, hgd⟩ := column_loc hF hH hs hp hb hl1 hl2 hg hloc (J0 + 1) (fun j _ => hall j)
    exact hJ0 (Good.isCell_f hs (hgd J0 (by omega)))
  set J := Nat.find hex
  have hJ : ¬ (front (cellJ w s J) s ∈ F ↔ J % 2 = 1) := Nat.find_spec hex
  have hbefore : ∀ j < J, front (cellJ w s j) s ∈ F ↔ j % 2 = 1 := fun j hj => by
    have := Nat.find_min hex hj; push Not at this; exact this
  have hJpos : J ≠ 0 := by
    intro h0
    apply hJ; rw [h0, cellJ_zero]; simp [hf0]
  obtain ⟨hlat, hgd⟩ := column_loc hF hH hs hp hb hl1 hl2 hg hloc J hbefore
  refine ⟨s, J + 1, by omega, ⟨hb, fun j hj => hlat j (by omega), fun j hj => ?_⟩,
    fun j hj => Good.isCell_f hs (hgd j (by omega)), fun j hj => hgd j (by omega), hp, hsep⟩
  rcases (show j < J ∨ j = J by omega) with h | rfl
  · have q : j + 1 < J + 1 := by omega
    simp only [q, iff_true]; exact hbefore j h
  · simp only [lt_self_iff_false, iff_false]
    tauto

end HP

end ULHC
