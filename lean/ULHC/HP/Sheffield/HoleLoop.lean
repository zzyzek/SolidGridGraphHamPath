/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
import ULHC.HP.Sheffield.HoleRun

/-!
# One hole: the loop within a class

An endpoint `t` inner in the solid `V`: the path's last edge `e0 = w–t` is fixed, and the run works
on `V' = V.erase t` with endpoint `w` and phantom `t` (inside the hole). The single-phantom
results (`s4C`, `runSC_sound`) need no solidity. Completeness holds within a class: if a
Hamiltonian `s`–`w` path of `V'` agrees with the start in `D` at `t` (`SolidFor V'`), the loop
finds one piece. A stuck phase is certified (`cert_count_gen`): `D = 0` off the cells by the class
(`sf_reach`), and no closed climb by the vortex at `t` (`acyc_hole`).
-/

namespace ULHC

namespace HP

open Finset Classical

section holeLoop

variable {V : Finset Pt} {s t w : Pt} {e0 : Edge}

lemma cell_erase {c : Pt} (hc : IsCell V c) (ht : ¬ IsCorner t c) : IsCell (V.erase t) c := by
  obtain ⟨x, y⟩ := c
  obtain ⟨h1, h2, h3, h4⟩ := hc
  unfold IsCorner at ht
  push Not at ht
  exact ⟨Finset.mem_erase.2 ⟨ht.1.symm, h1⟩, Finset.mem_erase.2 ⟨ht.2.1.symm, h2⟩,
    Finset.mem_erase.2 ⟨ht.2.2.1.symm, h3⟩, Finset.mem_erase.2 ⟨ht.2.2.2.symm, h4⟩⟩

-- A corner of no cell of `V.erase t` is not inner in `V`.
--
lemma s_not_inner (hst : s ≠ t) (hsD : ∀ c, IsCell (V.erase t) c → ¬ IsCorner s c) :
    ¬ Inner V s := by
  intro hin
  obtain ⟨x, y⟩ := s
  obtain ⟨i1, _, _, i4⟩ := hin
  by_cases h4 : IsCorner t (x, y)
  · apply hsD _ (cell_erase i1 ?_) (Or.inr (Or.inr (Or.inr (by simp))))
    intro h1
    obtain ⟨a, b⟩ := t
    unfold IsCorner at h1 h4
    rcases h1 with h | h | h | h <;> rcases h4 with h' | h' | h' | h' <;>
      (try simp [Prod.ext_iff] at h h' hst) <;> omega
  · exact hsD _ (cell_erase i4 h4) (Or.inl rfl)

lemma acyc_mono {H : Finset Edge} (hac : ClimbAcyc V H) : ClimbAcyc (V.erase t) H := by
  intro o x y c hc
  apply hac o x y c
  have conv : ∀ a b, ClimbStep (V.erase t) H o x y a b → ClimbStep V H o x y a b := by
    intro a b h
    obtain ⟨h1, h2, h3⟩ := h
    exact ⟨isCell_mono h1 (Finset.erase_subset _ _), isCell_mono h2 (Finset.erase_subset _ _), h3⟩
  have key : ∀ a b, Relation.TransGen (ClimbStep (V.erase t) H o x y) a b →
      Relation.TransGen (ClimbStep V H o x y) a b := by
    intro a b h
    induction h with
    | single h => exact .single (conv _ _ h)
    | tail _ h ih => exact ih.tail (conv _ _ h)
  exact key c c hc

-- **No closed climb** for the factors of the hole setting.
--
lemma acyc_hole (hs : Solid V) (ht : Inner V t) (hst : s ≠ t)
    (hsD : ∀ c, IsCell (V.erase t) c → ¬ IsCorner s c) :
    ∀ G, IsFactor (insert t (V.erase t)) (dST s t) G → ClimbAcyc (V.erase t) G := by
  intro G hG
  have htV : t ∈ V := ht.2.2.2.1
  rw [Finset.insert_erase htV] at hG
  apply acyc_mono
  refine acyc_vortex hs ht (by rw [hG.2 t htV]; exact dST_t s t) (fun p hpt hp => ?_)
  have hps : p ≠ s := fun h => s_not_inner hst hsD (h ▸ hp)
  rw [hG.2 p hp.2.2.2.1]
  exact dST_off hps hpt

-- **The "no" answer, within a class.**
--
theorem phase_no_hp_hole (hs : Solid V) (ht : Inner V t) (hsw : s ≠ w) (hst : s ≠ t)
    (hwV : w ∈ V.erase t) (he0 : Ends e0 w t) (hsD : ∀ c, IsCell (V.erase t) c → ¬ IsCorner s c)
    {H0 : Finset Edge} (h0 : NotchF (V.erase t) s t e0 H0) (hm : 2 ≤ ncomp (V.erase t) H0)
    {H : Finset Edge} {BS : List Bridge} (hr : Reach (V.erase t) H0 H BS)
    (hmerge : MergeOK (V.erase t) H BS) (hstuck : Stuck (V.erase t) H BS) {Hs : Finset Edge}
    (hHs : IsFactor (V.erase t) (dST s w) Hs) (hHam : ncomp (V.erase t) Hs = 1)
    (hcl : SolidFor (V.erase t) H0 (insert e0 Hs)) : False := by
  have hpV : t ∉ V.erase t := Finset.notMem_erase t V
  have hVW : V.erase t ⊆ insert t (V.erase t) := Finset.subset_insert _ _
  have hdc := notch_dc (s := s) hpV hsD
  have hout0 := notch_out hwV he0 h0
  have hinv := pinv_reach (t0 := w) (u0 := w) hVW hdc h0.fac hout0 hr
  have hG : NotchF (V.erase t) s t e0 H := ⟨hinv.fac, pat_reach hpV h0.pat hr⟩
  have hc := cert_of_stuck hVW hdc h0.fac hout0 hr hmerge hstuck (Or.inl rfl)
  have hcnt := reach_count hVW hdc h0.fac hout0 hr
  rw [h0.ncomp hwV he0, hG.ncomp hwV he0] at hcnt
  have hHN := notch_up hsw hwV hpV he0 hHs
  have hHam' : ncomp (V.erase t) (insert e0 Hs) = 1 := ncomp_one_of_conn hwV (fun x hx y hy =>
    (conn_of_ncomp_one hHam hx hy).mono (Finset.subset_insert _ _))
  have hsol := sf_reach hVW hdc h0.fac hout0 hr hcl
  have hcount := cert_count_gen hG.fac hHN.fac (acyc_hole hs ht hst hsD) hVW hdc
    (symmDiff_inside_of_PAt (Inside.of_factor hG.fac) (Inside.of_factor hHN.fac) hG.pat hHN.pat)
    hsol hc
  rw [hG.ncomp hwV he0, hHN.ncomp hwV he0, hHam'] at hcount
  simp only [List.length_map] at hcount
  omega

-- **Completeness within a class.**
--
theorem runSC_complete_hole (hs : Solid V) (ht : Inner V t) (hsw : s ≠ w) (hst : s ≠ t)
    (hwV : w ∈ V.erase t) (he0 : Ends e0 w t) (hsD : ∀ c, IsCell (V.erase t) c → ¬ IsCorner s c)
    {Hs : Finset Edge} (hHs : IsFactor (V.erase t) (dST s w) Hs) (hHam : ncomp (V.erase t) Hs = 1) :
    ∀ n G, NotchF (V.erase t) s t e0 G → SolidFor (V.erase t) G (insert e0 Hs) →
      ncomp (V.erase t) G ≤ n + 1 → runSC (V.erase t) t n G = true := by
  have hpV : t ∉ V.erase t := Finset.notMem_erase t V
  have hVW : V.erase t ⊆ insert t (V.erase t) := Finset.subset_insert _ _
  intro n
  induction n with
  | zero =>
    intro G hG _ hle
    have := ncomp_pos (F := G) hwV
    simp only [runSC, beq_iff_eq, cncomp_notch hwV he0 hG]; omega
  | succ n ih =>
    intro G hG hcl hle
    by_cases h1 : ncomp (V.erase t) G = 1
    · simp only [runSC, cncomp_notch hwV he0 hG, h1, beq_self_eq_true, ↓reduceIte]
    have h2 : 2 ≤ ncomp (V.erase t) G := by have := ncomp_pos (F := G) hwV; omega
    have h1' : (cncomp (insert t (V.erase t)) G == 1) = false := by
      rw [cncomp_notch hwV he0 hG]; simpa using h1
    simp only [runSC, h1', Bool.false_eq_true, ↓reduceIte]
    have hpok := notch_pok hwV hpV he0 hsD hG ((insert t (V.erase t)).card + 1)
    have hfuel := phase_fuel (t0 := w) (u0 := w) hVW (notch_dc hpV hsD) hG.fac
      (notch_out hwV he0 hG) ((insert t (V.erase t)).card + 1) G [] Reach.base (by omega)
    have h2' : 2 ≤ ncomp (insert t (V.erase t)) G := by rw [hG.ncomp hwV he0]; exact h2
    rcases hph : phase (V.erase t) (insert t (V.erase t)) ((insert t (V.erase t)).card + 1) G [] with
      ⟨H, BS, out⟩
    rw [hph] at hpok
    dsimp only at hpok
    have hfuel' := fun H' BS' => hfuel H' BS'
    rw [hph] at hfuel'
    have hdc := notch_dc (s := s) hpV hsD
    have hout0 := notch_out hwV he0 hG
    -- the phase keeps the class
    have hclH : ∀ (hr : Reach (V.erase t) G H BS), SolidFor (V.erase t) H (insert e0 Hs) :=
      fun hr => sf_reach hVW hdc hG.fac hout0 hr hcl
    cases out with
    | stuck =>
      obtain ⟨hr, hm, hk'⟩ := hpok
      exact (phase_no_hp_hole hs ht hsw hst hwV he0 hsD hG h2 hr hm hk' hHs hHam hcl).elim
    | fuel => exact absurd rfl (hfuel' H BS)
    | merge c =>
      obtain ⟨hN, hc⟩ := s4C hwV hpV he0 hsD hG h2' hpok (by simp) (by simp)
      rw [hN.ncomp hwV he0, hG.ncomp hwV he0] at hc
      exact ih _ hN (sf_reduceOutC hwV hpV he0 hsD hG hpok (by simp) (by simp) (hclH hpok.1))
        (by show ncomp _ (reduceOutC _ _ H BS (POut.merge c)) ≤ n + 1; omega)
    | odd b =>
      obtain ⟨hN, hc⟩ := s4C hwV hpV he0 hsD hG h2' hpok (by simp) (by simp)
      rw [hN.ncomp hwV he0, hG.ncomp hwV he0] at hc
      exact ih _ hN (sf_reduceOutC hwV hpV he0 hsD hG hpok (by simp) (by simp) (hclH hpok.1))
        (by show ncomp _ (reduceOutC _ _ H BS (POut.odd b)) ≤ n + 1; omega)
    | twist b =>
      obtain ⟨hN, hc⟩ := s4C hwV hpV he0 hsD hG h2' hpok (by simp) (by simp)
      rw [hN.ncomp hwV he0, hG.ncomp hwV he0] at hc
      exact ih _ hN (sf_reduceOutC hwV hpV he0 hsD hG hpok (by simp) (by simp) (hclH hpok.1))
        (by show ncomp _ (reduceOutC _ _ H BS (POut.twist b)) ≤ n + 1; omega)

end holeLoop

end HP

end ULHC
