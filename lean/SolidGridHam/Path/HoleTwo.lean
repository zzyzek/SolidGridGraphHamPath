/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
import SolidGridHam.Path.HoleRun

/-!
# One hole, two phantoms

An inner point `z` of the solid `Vo` is the hole: the path's edge `e0 = w–z` is fixed, and the inner
set is `U = Vo.erase z`. The other endpoint `s` has its own phantom `q ∉ Vo` (edge `e1`). States are
two-phantom states of `U` (`NotchF2 U z q e0 e1`); the out-vertices `w` and `s` are far apart.
`s4C2` and `runSC2` need no solidity; the run keeps its class (`sf_reduceOutC2`), a stuck phase is
certified within the class (`phase_no_hp2_hole`), and the loop is complete within a class
(`runSC2_complete_hole`).
-/

namespace SolidGridHam

namespace HP

open Finset Classical

section sf2

variable {V : Finset Pt} {s t p q : Pt} {e0 e1 : Edge}

-- **The two-phantom reduction keeps `SolidFor`.**
--
theorem sf_reduceOutC2 (hsV : s ∈ V) (htV : t ∈ V) (hpV : p ∉ V) (hqV : q ∉ V)
    (he0 : Ends e0 t p) (he1 : Ends e1 s q) (hfr : FarN t p s q) {H0 H X : Finset Edge}
    {BS : List Bridge} {out : POut} (hN : NotchF2 V p q e0 e1 H0) (hpok : POK V H0 H BS out)
    (hs : out ≠ .stuck) (hf : out ≠ .fuel) (hz : SolidFor V H X) :
    SolidFor V (reduceOutC V (insert q (insert p V)) H BS out) X := by
  have hdc := two_dc hpV hqV
  have hout0 := two_out htV hsV he0 he1 hN
  cases out with
  | stuck => exact absurd rfl hs
  | fuel => exact absurd rfl hf
  | odd g =>
    obtain ⟨hr, hmerge, mf, ho⟩ := hpok
    obtain ⟨hHW, hb⟩ := brW2 hsV htV hpV hqV he0 he1 hN hr
    have hc := corners_mem (isCell_mono mf.1 (vw2 (p := p) (q := q))) g.a
    have hinv := pinv_reach (t0 := t) (u0 := s) vw2 hdc hN.fac hout0 hr
    obtain ⟨pat, _⟩ := oddRow_pat mf ho (degc_of vw2 hdc hinv.fac)
    obtain ⟨ops, _⟩ := opsOK_rows (t0 := t) (u0 := s) (s0 := q) (p0 := p) vw2 hdc hN.fac hout0 hfr.1
      (fun c hc => notCorner_out hqV hc) hpV hr hmerge mf
    simp only [reduceOutC]
    rw [planB_eq hHW hc.1 hc.2 hb]
    exact sf_applyAll _ _ ops (plan_cells2 hsV htV hpV hqV he0 he1 hN hr)
      (sf_flipCol g.r H pat mf.2.2.2.2.2.1 hz)
  | twist g =>
    obtain ⟨hr, hmerge, mf, he, _⟩ := hpok
    obtain ⟨hHW, hb⟩ := brW2 hsV htV hpV hqV he0 he1 hN hr
    have hc := corners_mem (isCell_mono mf.1 (vw2 (p := p) (q := q))) g.a
    have hinv := pinv_reach (t0 := t) (u0 := s) vw2 hdc hN.fac hout0 hr
    obtain ⟨pat, _⟩ := evenRow_pat mf he (degc_of vw2 hdc hinv.fac)
    obtain ⟨ops, _⟩ := opsOK_rows (t0 := t) (u0 := s) (s0 := q) (p0 := p) vw2 hdc hN.fac hout0 hfr.1
      (fun c hc => notCorner_out hqV hc) hpV hr hmerge mf
    simp only [reduceOutC]
    rw [planB_eq hHW hc.1 hc.2 hb]
    exact sf_applyAll _ _ ops (plan_cells2 hsV htV hpV hqV he0 he1 hN hr)
      (sf_flipCol g.r H pat mf.2.2.2.2.2.1 hz)
  | merge c =>
    obtain ⟨hr, hc, ha, hcut, hnp⟩ := hpok
    obtain ⟨hHW, hb⟩ := brW2 hsV htV hpV hqV he0 he1 hN hr
    simp only [reduceOutC]
    refine getD_spec (cellList V) _ c (fun Y => SolidFor V (applyAll
        (flipCol H Y (altFrame H Y) 1) (planB (insert q (insert p V)) H BS (mergePair H Y))) X) ?_ ?_
    · intro Y hYl hg
      have hY := (mem_cellList.1 hYl).2
      obtain ⟨haY, hcY, hnpY, hgY⟩ := (goodB_iff vw2 hHW hb hY).1 hg
      have hcc := corners_mem (isCell_mono hY (vw2 (p := p) (q := q))) (altFrame H Y)
      rw [planB_eq hHW hcc.1 hcc.2 hb]
      obtain ⟨pat, _⟩ := merge_join_alt haY hcY
      obtain ⟨ops, _⟩ := opsOK_merge (t0 := t) (u0 := s) (s0 := q) (p0 := p) vw2 hdc hN.fac hout0 hfr.1
        (fun c hc => notCorner_out hqV hc) hpV hr (mcell_of hY haY hcY) haY hnpY hgY
      refine sf_applyAll _ _ ops (plan_cells2 hsV htV hpV hqV he0 he1 hN hr)
        (sf_flipCol 1 H pat ?_ hz)
      intro j hj
      obtain rfl : j = 0 := by omega
      rw [cellJ_zero]; exact hY
    · obtain ⟨Y, hY, haY, hcY, hnpY, hgY⟩ :=
        theoremR (t0 := t) (u0 := s) vw2 hdc hN.fac hout0 hfr.1
          (two_noOpp hsV htV hpV hqV he0 he1 hN hfr.2) hr hc ha hcut hnp
      exact ⟨Y, mem_cellList.2 ⟨by obtain ⟨x, y⟩ := Y; exact hY.1, hY⟩,
        (goodB_iff vw2 hHW hb hY).2 ⟨haY, hcY, hnpY, hgY⟩⟩

end sf2

section hole2

variable {Vo : Finset Pt} {s z w q : Pt} {e0 e1 : Edge}

-- No closed climb for the factors of the two-phantom hole setting.
--
lemma acyc_hole2 (hs : Solid Vo) (hz : Inner Vo z) (hqV : q ∉ Vo) :
    ∀ G, IsFactor (insert q (insert z (Vo.erase z))) (dST z q) G → ClimbAcyc (Vo.erase z) G := by
  intro G hG
  have hzV : z ∈ Vo := hz.2.2.2.1
  rw [Finset.insert_erase hzV] at hG
  apply climbAcyc_of_arc
  refine arcAcyc_transfer (H := G)
    (arc_vortex hs hz (by rw [hG.2 z (Finset.mem_insert_of_mem hzV)]; exact dST_s z q)
      (fun p hpz hp => ?_)) (Finset.erase_subset _ _) (fun _ _ _ _ => rfl)
  have hpq : p ≠ q := fun h => hqV (h ▸ hp.2.2.2.1)
  rw [hG.2 p (Finset.mem_insert_of_mem hp.2.2.2.1)]
  exact dST_off hpz hpq

end hole2

section holeU

variable {U : Finset Pt} {s z w q : Pt} {e0 e1 : Edge}
  (hac : ∀ G, IsFactor (insert q (insert z U)) (dST z q) G → ClimbAcyc U G)
  (hzU : z ∉ U) (hqU : q ∉ U) (hzq : z ≠ q) (hst : s ≠ w) (hsV : s ∈ U)
  (hwV : w ∈ U) (he0 : Ends e0 w z) (he1 : Ends e1 s q) (hfr : FarN w z s q)
include hac hzU hqU hzq hst hsV hwV he0 he1 hfr

-- **The "no" answer within a class, two phantoms.**
--
theorem phase_no_hp2_hole {H0 : Finset Edge} (h0 : NotchF2 (U) z q e0 e1 H0)
    (hm : 2 ≤ ncomp (U) H0) {H : Finset Edge} {BS : List Bridge}
    (hr : Reach (U) H0 H BS) (hmerge : MergeOK (U) H BS)
    (hstuck : Stuck (U) H BS) {Hs : Finset Edge}
    (hHs : IsFactor (U) (dST s w) Hs) (hHam : ncomp (U) Hs = 1)
    (hcl : SolidFor (U) H0 (insert e1 (insert e0 Hs))) : False := by
  have hdc := two_dc hzU hqU
  have hout0 := two_out hwV hsV he0 he1 h0
  have hinv := pinv_reach (t0 := w) (u0 := s) vw2 hdc h0.fac hout0 hr
  have hG : NotchF2 (U) z q e0 e1 H := two_reach hzU hqU hr h0 hinv.fac
  have hc := cert_of_stuck vw2 hdc h0.fac hout0 hr hmerge hstuck hfr.1
  have hcnt := reach_count vw2 hdc h0.fac hout0 hr
  rw [h0.ncomp hsV hwV he0 he1, hG.ncomp hsV hwV he0 he1] at hcnt
  have hHN := two_up hst hsV hwV hzU hqU hzq he0 he1 hHs
  have hHam' : ncomp (U) (insert e1 (insert e0 Hs)) = 1 :=
    ncomp_one_of_conn hwV (fun x hx y hy => (conn_of_ncomp_one hHam hx hy).mono
      ((Finset.subset_insert _ _).trans (Finset.subset_insert _ _)))
  have hsol := sf_reach vw2 hdc h0.fac hout0 hr hcl
  have hcount := cert_count_gen hG.fac hHN.fac hac vw2 hdc (two_symm hG hHN)
    hsol hc
  rw [hG.ncomp hsV hwV he0 he1, hHN.ncomp hsV hwV he0 he1, hHam'] at hcount
  simp only [List.length_map] at hcount
  omega

-- **Completeness within a class, two phantoms.**
--
theorem runSC2_complete_hole {Hs : Finset Edge} (hHs : IsFactor (U) (dST s w) Hs)
    (hHam : ncomp (U) Hs = 1) :
    ∀ n G, NotchF2 (U) z q e0 e1 G → SolidFor (U) G (insert e1 (insert e0 Hs)) →
      ncomp (U) G ≤ n + 1 → runSC2 (U) z q n G = true := by
  intro n
  induction n with
  | zero =>
    intro G hG _ hle
    have := ncomp_pos (F := G) hwV
    simp only [runSC2, beq_iff_eq, cncomp_two hsV hwV he0 he1 hG]; omega
  | succ n ih =>
    intro G hG hcl hle
    by_cases h1 : ncomp (U) G = 1
    · simp only [runSC2, cncomp_two hsV hwV he0 he1 hG, h1, beq_self_eq_true,
        ↓reduceIte]
    have h2 : 2 ≤ ncomp (U) G := by have := ncomp_pos (F := G) hwV; omega
    have h1' : (cncomp (insert q (insert z (U))) G == 1) = false := by
      rw [cncomp_two hsV hwV he0 he1 hG]; simpa using h1
    simp only [runSC2, h1', Bool.false_eq_true, ↓reduceIte]
    have hpok := two_pok hsV hwV hzU hqU he0 he1 hG
      ((insert q (insert z (U))).card + 1)
    have hfuel := phase_fuel (t0 := w) (u0 := s) vw2 (two_dc hzU hqU) hG.fac
      (two_out hwV hsV he0 he1 hG) ((insert q (insert z (U))).card + 1) G [] Reach.base
      (by omega)
    rcases hph : phase (U) (insert q (insert z (U)))
      ((insert q (insert z (U))).card + 1) G [] with ⟨H, BS, out⟩
    rw [hph] at hpok
    dsimp only at hpok
    have hfuel' := fun H' BS' => hfuel H' BS'
    rw [hph] at hfuel'
    have hclH : ∀ (hr : Reach (U) G H BS),
        SolidFor (U) H (insert e1 (insert e0 Hs)) :=
      fun hr => sf_reach vw2 (two_dc hzU hqU) hG.fac (two_out hwV hsV he0 he1 hG) hr hcl
    cases out with
    | stuck =>
      obtain ⟨hr, hm, hk'⟩ := hpok
      exact (phase_no_hp2_hole hac hzU hqU hzq hst hsV hwV he0 he1 hfr hG h2 hr hm hk' hHs hHam
        hcl).elim
    | fuel => exact absurd rfl (hfuel' H BS)
    | merge c =>
      obtain ⟨hN, hc⟩ := s4C2 hsV hwV hzU hqU he0 he1 hfr hG hpok (by simp) (by simp)
      rw [hN.ncomp hsV hwV he0 he1, hG.ncomp hsV hwV he0 he1] at hc
      exact ih _ hN (sf_reduceOutC2 hsV hwV hzU hqU he0 he1 hfr hG hpok (by simp) (by simp)
        (hclH hpok.1)) (by show ncomp _ (reduceOutC _ _ H BS (POut.merge c)) ≤ n + 1; omega)
    | odd b =>
      obtain ⟨hN, hc⟩ := s4C2 hsV hwV hzU hqU he0 he1 hfr hG hpok (by simp) (by simp)
      rw [hN.ncomp hsV hwV he0 he1, hG.ncomp hsV hwV he0 he1] at hc
      exact ih _ hN (sf_reduceOutC2 hsV hwV hzU hqU he0 he1 hfr hG hpok (by simp) (by simp)
        (hclH hpok.1)) (by show ncomp _ (reduceOutC _ _ H BS (POut.odd b)) ≤ n + 1; omega)
    | twist b =>
      obtain ⟨hN, hc⟩ := s4C2 hsV hwV hzU hqU he0 he1 hfr hG hpok (by simp) (by simp)
      rw [hN.ncomp hsV hwV he0 he1, hG.ncomp hsV hwV he0 he1] at hc
      exact ih _ hN (sf_reduceOutC2 hsV hwV hzU hqU he0 he1 hfr hG hpok (by simp) (by simp)
        (hclH hpok.1)) (by show ncomp _ (reduceOutC _ _ H BS (POut.twist b)) ≤ n + 1; omega)

end holeU

section ext

lemma corner_memU {U : Finset Pt} {c z : Pt} (hc : IsCell U c) (hz : IsCorner z c) : z ∈ U := by
  obtain ⟨x, y⟩ := c
  rcases hz with rfl | rfl | rfl | rfl
  · exact hc.1
  · exact hc.2.1
  · exact hc.2.2.1
  · exact hc.2.2.2

-- **No closed climb by extension.** If adding a fixed edge set `P`, touching no point of `U`, gives
-- every factor degree 1 at the inner point `z` of the solid `Vo` and degree 2 at its other inner
-- points, the factors have no closed climb on the cells of `U ⊆ Vo`.
--
theorem acyc_ext {Vo U W : Finset Pt} {d : Pt → ℕ} {z : Pt} (hs : Solid Vo) (hz : Inner Vo z)
    (hUV : U ⊆ Vo) (P : Finset Edge) (hPU : ∀ e ∈ P, e.p ∉ U ∧ e.q ∉ U)
    (hdeg : ∀ G, IsFactor W d G → deg (G ∪ P) z = 1 ∧
      ∀ v, v ≠ z → Inner Vo v → deg (G ∪ P) v = 2) :
    ∀ G, IsFactor W d G → ClimbAcyc U G := by
  intro G hG
  obtain ⟨h1, h2⟩ := hdeg G hG
  apply climbAcyc_of_arc
  refine arcAcyc_transfer (arc_vortex hs hz h1 h2) hUV (fun c s hc _ => outArc_congr ?_)
  have hm := (sideEdge_mem_cellE c c s).2 (Or.inl rfl)
  obtain ⟨cp, cq⟩ := corners_of_cellE hm
  have hp := corner_memU hc cp
  constructor
  · intro h; exact Finset.mem_union_left _ h
  · intro h
    rcases Finset.mem_union.1 h with h | h
    · exact h
    · exact absurd hp (hPU _ h).1

end ext

end HP

end SolidGridHam
