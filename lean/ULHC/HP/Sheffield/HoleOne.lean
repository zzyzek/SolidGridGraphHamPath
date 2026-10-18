/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
import ULHC.HP.Sheffield.HoleTwo
import ULHC.HP.Sheffield.HoleTryCost

/-!
# An inner endpoint, the other dangling: decided

`hpI1 V s t`: over the path's last edge `w–t` (each neighbour `w ≠ s` of `t`), take a reference
factor of `V.erase t` through `w–t`, and in each class (`classRange`) the factor `classSearchOne` returns, and run
the loop on `V.erase t` with phantom `t`. Correct when `t` is inner in the solid `V` and `s` is a
corner of no cell of `V.erase t` (`hpI1_correct`).
-/

namespace ULHC

namespace HP

open Finset Classical

-- The box of a set connected by a Hamiltonian path is narrow (`narrow_of_ncomp`).
--
def isNarrow (U : Finset Pt) : Bool :=
  decide (bx1 U - bx0 U < U.card) && decide (by1 U - by0 U < U.card)

def hpI1 (V : Finset Pt) (s t : Pt) : Bool :=
  (nbrsL t).any fun x => decide (x.1 ∈ V) && decide (x.1 ≠ s) && isNarrow (V.erase t) &&
    match findFactor (V.erase t) (dST s x.1) with
    | none => false
    | some R => (classRange (V.erase t)).any fun h =>
        match classSearchOne (V.erase t) (insert x.2 R) t h with
        | some G => runSC (V.erase t) t ((V.erase t).card + 2) G
        | none => false

section holeOne

variable {V : Finset Pt} {s t : Pt}

-- A factor agreeing with a notch state off the inner edges is a notch state.
--
lemma notch_of_symm {U : Finset Pt} {p : Pt} {e0 : Edge} {F G : Finset Edge} (hpU : p ∉ U)
    (hF : NotchF U s p e0 F) (hG : IsFactor (insert p U) (dST s p) G)
    (hFG : ∀ e ∈ symmDiff F G, e.p ∈ U ∧ e.q ∈ U) : NotchF U s p e0 G := by
  refine ⟨hG, fun e he => ?_⟩
  rw [← hF.pat e he]
  constructor
  · intro h
    by_contra hn
    have := hFG e (Finset.mem_symmDiff.2 (Or.inr ⟨h, hn⟩))
    rcases he with h' | h'
    · exact hpU (h' ▸ this.1)
    · exact hpU (h' ▸ this.2)
  · intro h
    by_contra hn
    have := hFG e (Finset.mem_symmDiff.2 (Or.inl ⟨h, hn⟩))
    rcases he with h' | h'
    · exact hpU (h' ▸ this.1)
    · exact hpU (h' ▸ this.2)

-- **One branch** (the path's last edge `w–t`).
--
theorem hpI1_branch (hs : Solid V) (ht : Inner V t) (hst : s ≠ t)
    (hsD : ∀ c, IsCell (V.erase t) c → ¬ IsCorner s c) {x : Pt × Edge} (hx : x ∈ nbrsL t)
    (hxV : x.1 ∈ V) (hxs : x.1 ≠ s) :
    (match findFactor (V.erase t) (dST s x.1) with
      | none => false
      | some R => (classRange (V.erase t)).any fun h =>
          match classSearchOne (V.erase t) (insert x.2 R) t h with
          | some G => runSC (V.erase t) t ((V.erase t).card + 2) G
          | none => false) = true ↔
      ∃ H, IsFactor (V.erase t) (dST s x.1) H ∧ ncomp (V.erase t) H = 1 := by
  have htV' : t ∉ V.erase t := Finset.notMem_erase t V
  have hends := nbrsL_ends hx
  have he0 : Ends x.2 x.1 t := by rcases hends with h | h; exacts [Or.inr h, Or.inl h]
  have hwV' : x.1 ∈ V.erase t := Finset.mem_erase.2 ⟨(edge_ne hends).symm, hxV⟩
  have hsw : s ≠ x.1 := Ne.symm hxs
  have hVW : V.erase t ⊆ insert t (V.erase t) := Finset.subset_insert _ _
  have hesc : ∀ b, b ∉ V.erase t → Relation.ReflTransGen (MissAdj (V.erase t)) b t ∨
      ∃ b', Relation.ReflTransGen (MissAdj (V.erase t)) b b' ∧ ∀ p ∈ V.erase t, b'.1 < p.1 := by
    intro b hb
    rcases hole_escape hs b hb with rfl | h
    · exact Or.inl Relation.ReflTransGen.refl
    · exact Or.inr h
  rcases hR : findFactor (V.erase t) (dST s x.1) with _ | R
  · simp only
    constructor
    · intro h; exact absurd h (by simp)
    · rintro ⟨H, hH, _⟩
      exact absurd ⟨H, hH⟩ (findFactor_none (dST_le s x.1) hR)
  · simp only
    have hRf := findFactor_some (dST_le s x.1) hR
    have hF := notch_up hsw hwV' htV' he0 hRf
    rw [List.any_eq_true]
    constructor
    · rintro ⟨h, _, hb⟩
      rcases hT : classSearchOne (V.erase t) (insert x.2 R) t h with _ | G
      · rw [hT] at hb; simp at hb
      rw [hT] at hb
      simp only at hb
      obtain ⟨hGf, hFG, _⟩ := classSearchOne_sound hVW hF.fac hT
      have hG := notch_of_symm htV' hF hGf hFG
      obtain ⟨G', hG', h1⟩ := runSC_sound hwV' htV' he0 hsD _ _ hG hb
      exact ⟨_, notch_down hsw hwV' htV' he0 hG' h1⟩
    · rintro ⟨Hs, hHs, hHam⟩
      have hHN := notch_up hsw hwV' htV' he0 hHs
      have hFH := symmDiff_inside_of_PAt (Inside.of_factor hF.fac) (Inside.of_factor hHN.fac)
        hF.pat hHN.pat
      obtain ⟨hmem, hev⟩ := class_mem_hRange (t := t) hFH
      refine ⟨_, hmem, ?_⟩
      have hne := classSearchOne_complete hF.fac hHN.fac hFH hev
      rcases hT : classSearchOne (V.erase t) (insert x.2 R) t (D (insert x.2 R) (insert x.2 Hs) t / 2) with
        _ | G
      · exact absurd hT hne
      simp only
      obtain ⟨hGf, hFG, _⟩ := classSearchOne_sound hVW hF.fac hT
      have hG := notch_of_symm htV' hF hGf hFG
      have hsol := classSearchOne_solidFor hVW hF.fac htV' hesc hT hHN.fac hFH hev
      have hle := ncomp_le_card (X := V.erase t) (F := G)
      exact runSC_complete_hole hs ht hsw hst hwV' he0 hsD hHs hHam _ G hG hsol (by omega)

-- **An inner endpoint, the other dangling.** For solid `V` with at least three points, `t` inner,
-- and `s` a corner of no cell of `V.erase t`, `hpI1` decides the Hamiltonian `s`–`t` path problem.
--
theorem hpI1_correct (hs : Solid V) (ht : Inner V t) (hst : s ≠ t)
    (hsD : ∀ c, IsCell (V.erase t) c → ¬ IsCorner s c) (h3 : 3 ≤ V.card) :
    hpI1 V s t = true ↔ ∃ H, IsFactor V (dST s t) H ∧ ncomp V H = 1 := by
  rw [del_iff hst ht.2.2.2.1 h3]
  unfold hpI1
  rw [List.any_eq_true]
  constructor
  · rintro ⟨x, hx, hb⟩
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hb
    obtain ⟨⟨⟨hxV, hxs⟩, _⟩, hb⟩ := hb
    exact ⟨x, hx, hxV, hxs, (hpI1_branch hs ht hst hsD hx hxV hxs).1 hb⟩
  · rintro ⟨x, hx, hxV, hxs, hH⟩
    refine ⟨x, hx, ?_⟩
    obtain ⟨Hs, hHs, hHam⟩ := hH
    have hn := narrow_of_ncomp (Inside.of_factor hHs) hHam
    simp only [Bool.and_eq_true, decide_eq_true_eq, isNarrow]
    exact ⟨⟨⟨hxV, hxs⟩, hn⟩, (hpI1_branch hs ht hst hsD hx hxV hxs).2 ⟨Hs, hHs, hHam⟩⟩

end holeOne

end HP

end ULHC
