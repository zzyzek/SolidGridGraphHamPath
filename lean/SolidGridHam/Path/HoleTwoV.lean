/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
module

public import SolidGridHam.Path.HoleWalkCost
public import SolidGridHam.Path.TwoVortex
public import SolidGridHam.Algorithm

@[expose] public section

/-!
# Both endpoints inner

The walk of `HoleWalk` with a different final test. After deleting `t` and `s`, both are holes:
`t` is the phantom of `w`, and `s` (the other endpoint `r` of the invariant `WS`) is the end of the
deleted path. A factor of the two-phantom setting, with the deleted path added, has degree 1 at the
two inner points `t` and `s` and degree 2 at every other inner point, so it has no closed climb
(`arc_vortex2`). The classes are pairs `(h₁, h₂)`, the values of `D/2` at the two holes, found by
`classSearch` (`twoHoleFinalTest`).
-/

namespace SolidGridHam

namespace HP

open Finset Classical

-- **No closed climb by extension, two vortices.**
--
theorem acyc_ext2 {Vo U W : Finset Pt} {d : Pt → ℕ} {z r : Pt} (hs : Solid Vo) (hz : Inner Vo z)
    (hr : Inner Vo r) (hzr : z ≠ r) (hUV : U ⊆ Vo) (P : Finset Edge)
    (hPU : ∀ e ∈ P, e.p ∉ U ∧ e.q ∉ U)
    (hdeg : ∀ G, IsFactor W d G → deg (G ∪ P) z = 1 ∧ deg (G ∪ P) r = 1 ∧
      ∀ v, v ≠ z → v ≠ r → Inner Vo v → deg (G ∪ P) v = 2) :
    ∀ G, IsFactor W d G → ClimbAcyc U G := by
  intro G hG
  obtain ⟨h1, h2, h3⟩ := hdeg G hG
  apply climbAcyc_of_arc
  refine arcAcyc_transfer (arc_vortex2 hs hzr hz hr h1 h2 h3) hUV
    (fun c s hc _ => outArc_congr ?_)
  have hm := (sideEdge_mem_cellE c c s).2 (Or.inl rfl)
  obtain ⟨cp, cq⟩ := corners_of_cellE hm
  have hp := corner_memU hc cp
  constructor
  · intro h; exact Finset.mem_union_left _ h
  · intro h
    rcases Finset.mem_union.1 h with h | h
    · exact h
    · exact absurd hp (hPU _ h).1

section ws2

variable {Vo : Finset Pt} {t r w : Pt} {e0 : Edge} {U : Finset Pt} {s q : Pt} {e1 : Edge}

-- **No closed climb, two vortices** (both endpoints inner).
--
theorem ws_acyc2 (hI : WS Vo t r w e0 U s q e1) (hrI : Inner Vo r) :
    ∀ G, IsFactor (insert q (insert t U)) (dST t q) G → ClimbAcyc U G := by
  obtain ⟨P, hPU, hPt, hPd⟩ := hI.ext
  refine acyc_ext2 hI.solid hI.inner hrI hI.rt.symm hI.sub P hPU (fun G hG => ?_)
  obtain ⟨h1, h2⟩ := ws_deg hI hPU hPt hPd hG
  refine ⟨h1, by rw [h2 r hI.rt hrI, ite_eq_left rfl], fun v hvt hvr hv => ?_⟩
  rw [h2 v hvt hv, ite_eq_right hvr]

lemma ws_kholes (hI : WS Vo t r w e0 U s q e1) : KHoles U [t, r] := by
  refine ⟨by simp [hI.tU, hI.rU], fun b hb => ?_⟩
  rcases hI.esc b hb with h | h | h
  · exact Or.inl ⟨t, by simp, h⟩
  · exact Or.inl ⟨r, by simp, h⟩
  · exact Or.inr h

end ws2

/-! ## Two holes: the classes -/

section k2

variable {V W : Finset Pt} {d : Pt → ℕ} {F G : Finset Edge} {t r : Pt} {h1 h2 : ℤ}

theorem kFind2_sound (hVW : V ⊆ W) (hF : IsFactor W d F)
    (hT : classSearch V F [t, r] [h1, h2] = some G) :
    IsFactor W d G ∧ (∀ e ∈ symmDiff F G, e.p ∈ V ∧ e.q ∈ V) ∧ D F G t = 2 * h1 ∧
      D F G r = 2 * h2 := by
  obtain ⟨hG, hFG, hD⟩ := classSearch_sound hVW hF hT
  exact ⟨hG, hFG, hD (t, h1) (by simp), hD (r, h2) (by simp)⟩

theorem kFind2_complete (hF : IsFactor W d F) (hG : IsFactor W d G)
    (hFG : ∀ e ∈ symmDiff F G, e.p ∈ V ∧ e.q ∈ V) (hD1 : D F G t = 2 * h1)
    (hD2 : D F G r = 2 * h2) : classSearch V F [t, r] [h1, h2] ≠ none := by
  apply classSearch_complete hF hG hFG
  intro ah hm
  simp only [List.zip_cons_cons, List.zip_nil_right, List.mem_cons, List.not_mem_nil,
    or_false] at hm
  rcases hm with rfl | rfl
  · exact hD1
  · exact hD2

-- **B-3 with B-1, two holes.**
--
theorem kFind2_solidFor (hVW : V ⊆ W) (hF : IsFactor W d F) (hk : KHoles V [t, r])
    {G' : Finset Edge} (hT : classSearch V F [t, r] [h1, h2] = some G') (hG : IsFactor W d G)
    (hFG : ∀ e ∈ symmDiff F G, e.p ∈ V ∧ e.q ∈ V) (hD1 : D F G t = 2 * h1)
    (hD2 : D F G r = 2 * h2) : SolidFor V G' G := by
  obtain ⟨hG', hFG', hT1, hT2⟩ := kFind2_sound hVW hF hT
  have hsd : ∀ e ∈ symmDiff G' G, e.p ∈ V ∧ e.q ∈ V := by
    intro e he
    have : symmDiff G' G = symmDiff (symmDiff F G') (symmDiff F G) := by
      rw [symmDiff_symmDiff_symmDiff_comm, symmDiff_self, bot_symmDiff]
    rw [this, Finset.mem_symmDiff] at he
    rcases he with ⟨he, _⟩ | ⟨he, _⟩
    · exact hFG' e he
    · exact hFG e he
  refine solidFor_of_holes hG' hG hsd hk (fun a ha => ?_)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl
  · rw [D_sub hF.1 hG'.1 hG.1, hD1, hT1]; ring
  · rw [D_sub hF.1 hG'.1 hG.1, hD2, hT2]; ring

end k2

/-! ## The final test -/

section twoHoleFinalTest

variable {Vo : Finset Pt} {t r w : Pt} {e0 : Edge} {U : Finset Pt} {s q : Pt} {e1 : Edge}

theorem twoHoleFinalTest_correct (hI : WS Vo t r w e0 U s q e1) (hrI : Inner Vo r) (hfr : FarN w t s q) :
    twoHoleFinalTest U s w t r q e0 e1 = true ↔ ∃ H, IsFactor U (dST s w) H ∧ ncomp U H = 1 := by
  have hVW : U ⊆ insert q (insert t U) :=
    (Finset.subset_insert _ _).trans (Finset.subset_insert _ _)
  unfold twoHoleFinalTest
  rw [Bool.and_eq_true]
  constructor
  · rintro ⟨_, hb⟩
    rcases hR : findFactor U (dST s w) with _ | R
    · rw [hR] at hb; simp at hb
    rw [hR] at hb
    simp only [List.any_eq_true] at hb
    obtain ⟨h1, _, h2, _, hb⟩ := hb
    rcases hT : classSearch U (insert e1 (insert e0 R)) [t, r] [h1, h2] with _ | G
    · rw [hT] at hb; simp at hb
    rw [hT] at hb
    simp only at hb
    have hF := two_up hI.sw hI.sU hI.wU hI.tU hI.qU hI.qt.symm hI.he0 hI.he1
      (findFactor_some (dST_le s w) hR)
    obtain ⟨hGf, hFG, _⟩ := kFind2_sound hVW hF.fac hT
    have hG := notch2_of_symm hI.tU hI.qU hF hGf hFG
    rw [twoPhantomLoop_eq hI.sU hI.wU hI.tU hI.qU hI.he0 hI.he1 hfr _ _ hG] at hb
    obtain ⟨G', hG', h1⟩ := runSC2_sound hI.sU hI.wU hI.tU hI.qU hI.he0 hI.he1 hfr _ _ hG hb
    exact two_down hI.sw hI.sU hI.wU hI.tU hI.qU hI.qt.symm hI.he0 hI.he1 hG' h1
  · rintro ⟨Hs, hHs, hHam⟩
    refine ⟨by
      simp only [isNarrow, Bool.and_eq_true, decide_eq_true_eq]
      exact narrow_of_ncomp (Inside.of_factor hHs) hHam, ?_⟩
    rcases hR : findFactor U (dST s w) with _ | R
    · exact absurd ⟨Hs, hHs⟩ (findFactor_none (dST_le s w) hR)
    simp only [List.any_eq_true]
    have hF := two_up hI.sw hI.sU hI.wU hI.tU hI.qU hI.qt.symm hI.he0 hI.he1
      (findFactor_some (dST_le s w) hR)
    have hHN := two_up hI.sw hI.sU hI.wU hI.tU hI.qU hI.qt.symm hI.he0 hI.he1 hHs
    have hFH := two_symm hF hHN
    obtain ⟨hmem1, hev1⟩ := class_mem_hRange (t := t) hFH
    obtain ⟨hmem2, hev2⟩ := class_mem_hRange (t := r) hFH
    refine ⟨_, hmem1, _, hmem2, ?_⟩
    have hne := kFind2_complete hF.fac hHN.fac hFH hev1 hev2
    rcases hT : classSearch U (insert e1 (insert e0 R)) [t, r]
      [D (insert e1 (insert e0 R)) (insert e1 (insert e0 Hs)) t / 2,
        D (insert e1 (insert e0 R)) (insert e1 (insert e0 Hs)) r / 2] with _ | G
    · exact absurd hT hne
    simp only
    obtain ⟨hGf, hFG, _⟩ := kFind2_sound hVW hF.fac hT
    have hG := notch2_of_symm hI.tU hI.qU hF hGf hFG
    have hsol := kFind2_solidFor hVW hF.fac (ws_kholes hI) hT hHN.fac hFH hev1 hev2
    have hle := ncomp_le_card (X := U) (F := G)
    rw [twoPhantomLoop_eq hI.sU hI.wU hI.tU hI.qU hI.he0 hI.he1 hfr _ _ hG]
    exact runSC2_complete_hole (ws_acyc2 hI hrI) hI.tU hI.qU hI.qt.symm hI.sw hI.sU hI.wU hI.he0
      hI.he1 hfr hHs hHam _ G hG hsol (by omega)

end twoHoleFinalTest

/-! ## Both endpoints inner -/

section twoHoleCase

variable {V : Finset Pt} {s t : Pt}

-- **Both endpoints inner.** For solid `V` and distinct inner `s`, `t`, `twoHoleCase` decides the
-- Hamiltonian `s`–`t` path problem.
--
theorem twoHoleCase_correct (hs : Solid V) (ht : Inner V t) (hsI : Inner V s) (hst : s ≠ t) :
    twoHoleCase V s t = true ↔ ∃ H, IsFactor V (dST s t) H ∧ ncomp V H = 1 :=
  holeCase_correct hs ht hst hsI.2.2.2.1 (fun _ _ _ _ _ _ hI hfr => twoHoleFinalTest_correct hI hsI hfr)

end twoHoleCase

end HP

end SolidGridHam
