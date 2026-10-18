/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
import ULHC.HP.Sheffield.PhaseCount
import ULHC.HP.Sheffield.CertHP

/-!
# A stuck phase rules out Hamiltonian s–t paths

Start a phase from a notch state `H0` (`t` in a notch with phantom `p`, `s` dangling) with at least
two pieces. If bridge steps reach a state where every merging cell is a pair square and every
critical square is a bridge square or stuck, there is no Hamiltonian `s–t` path (`phase_no_hp`).
-/

namespace ULHC

namespace HP

open Finset Classical

section phaseNo

variable {V : Finset Pt} {s t p : Pt} {e0 : Edge}

-- Bridge steps flip cells of `V`, so the edges at `p` do not change.
--
lemma pat_reach (hpV : p ∉ V) {H0 : Finset Edge} (h0 : PAt p e0 H0) {H : Finset Edge}
    {BS : List Bridge} (hr : Reach V H0 H BS) : PAt p e0 H := by
  induction hr with
  | base => exact h0
  | @step H' BS' b _ hrs _ _ ih =>
    intro e he
    rw [mem_flip_iff]
    have hE : IsCell V b.E := hrs.cells _ (by have := hrs.two; omega)
    have hn : e ∉ cellE b.E := by
      intro hc
      obtain ⟨cp, cq⟩ := corners_of_cellE hc
      have inV : ∀ z, IsCorner z b.E → z ∈ V := by
        intro z hz
        rcases hz with rfl | rfl | rfl | rfl
        · exact hE.1
        · exact hE.2.1
        · exact hE.2.2.1
        · exact hE.2.2.2
      rcases he with h | h
      · exact hpV (h ▸ inV _ cp)
      · exact hpV (h ▸ inV _ cq)
    rw [← ih e he]; tauto

theorem phase_no_hp (hs : Solid V) (hst : s ≠ t) (htV : t ∈ V) (hpV : p ∉ V)
    (he0 : Ends e0 t p) (hsD : ∀ c, IsCell V c → ¬ IsCorner s c)
    {H0 : Finset Edge} (h0 : NotchF V s p e0 H0) (hm : 2 ≤ ncomp V H0)
    {H : Finset Edge} {BS : List Bridge} (hr : Reach V H0 H BS) (hmerge : MergeOK V H BS)
    (hstuck : Stuck V H BS) :
    ¬ ∃ H', IsFactor V (dST s t) H' ∧ ncomp V H' = 1 := by
  have hVW : V ⊆ insert p V := Finset.subset_insert _ _
  have hdc : ∀ q, IsCell V q → ∀ z, IsCorner z q → dST s p z = 2 := by
    intro q hq z hz
    have hzV : z ∈ V := by
      obtain ⟨x, y⟩ := q
      rcases hz with rfl | rfl | rfl | rfl
      · exact hq.1
      · exact hq.2.1
      · exact hq.2.2.1
      · exact hq.2.2.2
    have hzs : z ≠ s := fun h => hsD q hq (h ▸ hz)
    have hzp : z ≠ p := fun h => hpV (h ▸ hzV)
    unfold dST; simp [hzs, hzp]
  have hout : ∀ (G : Finset Edge), PAt p e0 G → Inside (insert p V) G →
      ∀ e ∈ G, (e.p ∉ V → e.q = t) ∧ (e.q ∉ V → e.p = t) := by
    intro G hG hin e he
    have hev := hin e he
    constructor
    · intro hx
      have : e.p = p := by
        rcases Finset.mem_insert.1 hev.1 with h | h
        · exact h
        · exact absurd h hx
      have := (hG e (Or.inl this)).1 he
      subst this
      rcases he0 with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact absurd (h1 ▸ htV) hx
      · exact h2
    · intro hx
      have : e.q = p := by
        rcases Finset.mem_insert.1 hev.2 with h | h
        · exact h
        · exact absurd h hx
      have := (hG e (Or.inr this)).1 he
      subst this
      rcases he0 with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact h1
      · exact absurd (h2 ▸ htV) hx
  have hout0 := out_dup (hout H0 h0.pat (Inside.of_factor h0.fac))
  have hinv := pinv_reach (t0 := t) (u0 := t) hVW hdc h0.fac hout0 hr
  have hG : NotchF V s p e0 H := ⟨hinv.fac, pat_reach hpV h0.pat hr⟩
  have hc := cert_of_stuck hVW hdc h0.fac hout0 hr hmerge hstuck (Or.inl rfl)
  have hcnt := reach_count hVW hdc h0.fac hout0 hr
  rw [h0.ncomp htV he0, hG.ncomp htV he0] at hcnt
  exact cert_no_hp hs hst htV hpV he0 hsD hG hc (by simp; omega)

end phaseNo

end HP

end ULHC
