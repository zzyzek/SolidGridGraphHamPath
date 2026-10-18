/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
import ULHC.HP.Sheffield.S4TheoremR

/-!
# The Sheffield loop is correct

Theorem R and Theorem II give a good merging cell at every merging-cell outcome
(`MergeGoodSpec`), so S4 holds, and `hpSheff` decides the Hamiltonian `s`–`t` path problem on a
solid grid graph (with `t` at the notch `p`, `s` not a cell corner).
-/

namespace ULHC

namespace HP

open Finset Classical

section main

variable {V : Finset Pt} {s t p : Pt} {e0 : Edge}

-- **Theorem R, packaged.** At a merging-cell outcome some cell of `V` is good.
--
theorem mergeGood (htV : t ∈ V) (hpV : p ∉ V) (he0 : Ends e0 t p)
    (hsD : ∀ c, IsCell V c → ¬ IsCorner s c) : MergeGoodSpec V s p e0 := by
  intro H0 H BS c hN _ hpok
  obtain ⟨hr, hc, ha, hcut, hnp⟩ := hpok
  have hVW : V ⊆ insert p V := Finset.subset_insert _ _
  have hdc := notch_dc (s := s) hpV hsD
  have hout0 := notch_out htV he0 hN
  obtain ⟨X, hX, haX, hcutX, hnpX, hgood⟩ :=
    theoremR (t0 := t) (u0 := t) hVW hdc hN.fac hout0 (Or.inl rfl) (noOpp_same _ _ _) hr hc ha hcut hnp
  refine ⟨X, hX, by obtain ⟨x, y⟩ := X; exact hX.1, ?_⟩
  exact goodCell_of hVW hdc hN.fac hout0 (Or.inl rfl) hsD hpV hr hX haX hcutX hnpX hgood

-- **S4.**
--
theorem s4Spec (htV : t ∈ V) (hpV : p ∉ V) (he0 : Ends e0 t p)
    (hsD : ∀ c, IsCell V c → ¬ IsCorner s c) : S4Spec V s p e0 :=
  s4Spec_of htV hpV he0 hsD (mergeGood htV hpV he0 hsD)

-- **Correctness of the Sheffield loop.**
--
theorem hpSheff_correct' (hs : Solid V) (hst : s ≠ t) (htV : t ∈ V) (hpV : p ∉ V)
    (he0 : Ends e0 t p) (hsD : ∀ c, IsCell V c → ¬ IsCorner s c) :
    hpSheff V s t p e0 = true ↔ ∃ H, IsFactor V (dST s t) H ∧ ncomp V H = 1 :=
  hpSheff_correct hs hst htV hpV he0 hsD (s4Spec htV hpV he0 hsD)

-- **Deleting `t`.** With a missing king neighbour of `t`, `V` has a Hamiltonian `s`–`t` path iff
-- for some neighbour `w ≠ s` of `t`, the Sheffield loop on `V.erase t` with endpoint `w` and
-- phantom `t` answers `true`.
--
theorem hp_delete (hs : Solid V) (hst : s ≠ t) (htV : t ∈ V)
    (hsD : ∀ c, IsCell V c → ¬ IsCorner s c) {q : Pt} (hq : q ∉ V) (hqx : |q.1 - t.1| ≤ 1)
    (hqy : |q.2 - t.2| ≤ 1) (h3 : ∃ z ∈ V, z ≠ s ∧ z ≠ t) :
    (∃ H, IsFactor V (dST s t) H ∧ ncomp V H = 1) ↔
      ∃ w ew, ((ew.p = t ∧ ew.q = w) ∨ (ew.p = w ∧ ew.q = t)) ∧ w ∈ V ∧ w ≠ s ∧
        hpSheff (V.erase t) s w t ew = true := by
  have hs' : Solid (V.erase t) := solid_erase htV hs hq hqx hqy
  have hsD' : ∀ c, IsCell (V.erase t) c → ¬ IsCorner s c :=
    fun c hc => hsD c (isCell_mono hc (Finset.erase_subset _ _))
  have htV' : t ∉ V.erase t := Finset.notMem_erase t V
  have hpq : ∀ e : Edge, e.p ≠ e.q := by
    intro e; obtain ⟨dir, ⟨x, y⟩⟩ := e; cases dir <;> simp [Edge.q]
  have htw : ∀ {w : Pt} {ew : Edge}, ((ew.p = t ∧ ew.q = w) ∨ (ew.p = w ∧ ew.q = t)) → t ≠ w := by
    intro w ew hew
    rcases hew with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [← h1, ← h2]; exact hpq ew
    · rw [← h1, ← h2]; exact Ne.symm (hpq ew)
  have hends : ∀ {w : Pt} {ew : Edge}, ((ew.p = t ∧ ew.q = w) ∨ (ew.p = w ∧ ew.q = t)) →
      Ends ew w t := by
    intro w ew hew
    rcases hew with h | h
    · exact Or.inr h
    · exact Or.inl h
  constructor
  · rintro ⟨H, hH, hHam⟩
    have hdt : deg H t = 1 := by rw [hH.2 t htV]; unfold dST; simp
    rw [DF.deg_eq_card] at hdt
    obtain ⟨e, he⟩ := Finset.card_eq_one.1 hdt
    have hem : e ∈ H.filter (fun e => e.p = t ∨ e.q = t) := by
      rw [he]; exact Finset.mem_singleton_self e
    obtain ⟨heH, het⟩ := Finset.mem_filter.1 hem
    obtain ⟨w, hew⟩ : ∃ w, (e.p = t ∧ e.q = w) ∨ (e.p = w ∧ e.q = t) := by
      rcases het with h | h
      · exact ⟨e.q, Or.inl ⟨h, rfl⟩⟩
      · exact ⟨e.p, Or.inr ⟨rfl, h⟩⟩
    have hwV : w ∈ V := by
      have := Inside.of_factor hH e heH
      rcases hew with ⟨_, h⟩ | ⟨h, _⟩
      · rw [← h]; exact this.2
      · rw [← h]; exact this.1
    have hsw : s ≠ w := by
      intro hsw
      subst hsw
      obtain ⟨z, hz, hzs, hzt⟩ := h3
      have endS : e.p = s ∨ e.q = s := by
        rcases hew with ⟨_, h⟩ | ⟨h, _⟩
        · exact Or.inr h
        · exact Or.inl h
      have endT : e.p = t ∨ e.q = t := het
      have d0 : ∀ x, (x = s ∨ x = t) → deg (H.erase e) x = 0 := by
        intro x hx
        rcases hx with rfl | rfl
        · have h1 := DF.deg_erase_end heH endS
          rw [hH.2 x hwV] at h1; unfold dST at h1; simp at h1; omega
        · have h1 := DF.deg_erase_end heH endT
          rw [hH.2 x htV] at h1; unfold dST at h1; simp at h1; omega
      have reach : ∀ y, Conn H s y → y = s ∨ y = t := by
        intro y hy
        induction hy with
        | refl => exact Or.inl rfl
        | @tail a b _ hab ih =>
          obtain ⟨f, hf, hfe⟩ := hab
          by_cases hff : f = e
          · subst hff
            rcases hfe with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases hew with ⟨h3, h4⟩ | ⟨h3, h4⟩
            · exact Or.inl (h2.symm.trans h4)
            · exact Or.inr (h2.symm.trans h4)
            · exact Or.inr (h1.symm.trans h3)
            · exact Or.inl (h1.symm.trans h3)
          · have hf' : f ∈ H.erase e := Finset.mem_erase.2 ⟨hff, hf⟩
            have ha : f.p = a ∨ f.q = a := by
              rcases hfe with ⟨h1, _⟩ | ⟨_, h2⟩
              · exact Or.inl h1
              · exact Or.inr h2
            have := one_le_deg hf' ha
            rw [d0 a ih] at this; omega
      rcases reach z (conn_of_ncomp_one hHam hwV hz) with h | h
      · exact hzs h
      · exact hzt h
    obtain ⟨hH', hHam'⟩ := delete_down htV hwV hew hst hsw hH hHam heH
    refine ⟨w, e, hew, hwV, Ne.symm hsw, ?_⟩
    exact (hpSheff_correct' hs' hsw (Finset.mem_erase.2 ⟨(htw hew).symm, hwV⟩) htV' (hends hew)
      hsD').2 ⟨_, hH', hHam'⟩
  · rintro ⟨w, ew, hew, hwV, hws, hrun⟩
    obtain ⟨H', hH', hHam'⟩ := (hpSheff_correct' hs' (Ne.symm hws)
      (Finset.mem_erase.2 ⟨(htw hew).symm, hwV⟩) htV' (hends hew) hsD').1 hrun
    obtain ⟨hH, hHam, _⟩ := delete_up htV hwV hew hst (Ne.symm hws) hH' hHam'
    exact ⟨_, hH, hHam⟩

end main

end HP

end ULHC
