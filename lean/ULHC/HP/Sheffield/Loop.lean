/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
import ULHC.HP.Sheffield.Reduce
import ULHC.HP.Sheffield.PhaseNo

/-!
# The Sheffield route at a notch

`runS` repeats phases from a notch state: one piece answers `true`; a phase ending `.stuck` (or
`.fuel`) answers `false`; a success outcome is reduced (`reduceOut`) and the loop goes on.
`hpSheff` starts from an s–t path-factor of `V` plus the edge `e0` from `t` to `p`.

`hpSheff_correct`: assuming the S4 statement (`S4Spec`), `hpSheff` answers `true` exactly when `V`
has a Hamiltonian s–t path. A `true` comes with a one-piece notch state (`notch_down`). Given a path,
`.stuck` contradicts `phase_no_hp`, `.fuel` contradicts `phase_fuel`, and each reduction removes one
piece, so `V.card + 2` rounds suffice.
-/

namespace ULHC

namespace HP

open Finset Classical

-- Phases from `G` until one piece; `.stuck` and `.fuel` answer `false`.
--
noncomputable def runS (V : Finset Pt) (s p : Pt) : ℕ → Finset Edge → Bool
  | 0, G => decide (ncomp V G = 1)
  | n + 1, G =>
    if ncomp V G = 1 then true
    else
      let r := phase V (insert p V) ((insert p V).card + 1) G []
      if r.2.2 = .stuck ∨ r.2.2 = .fuel then false
      else runS V s p n (reduceOut V (insert p V) s p r.1 r.2.1 r.2.2)

-- **The Sheffield route at a notch.** An s–t path-factor `R` of `V`, plus the edge `e0` from `t`
-- to its missing neighbour `p`, then phases and reductions.
--
noncomputable def hpSheff (V : Finset Pt) (s t p : Pt) (e0 : Edge) : Bool :=
  match findFactor V (dST s t) with
  | none => false
  | some R => runS V s p (V.card + 2) (insert e0 R)

section loop

variable {V : Finset Pt} {s t p : Pt} {e0 : Edge}

-- Every corner of a cell of `V` has degree 2 in `dST s p`.
--
lemma notch_dc (hpV : p ∉ V) (hsD : ∀ c, IsCell V c → ¬ IsCorner s c) :
    ∀ q, IsCell V q → ∀ z, IsCorner z q → dST s p z = 2 := by
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

-- The only edge of a notch state leaving `V` ends at `t`.
--
lemma notch_out1 (htV : t ∈ V) (he0 : Ends e0 t p) {G : Finset Edge} (hG : NotchF V s p e0 G) :
    ∀ e ∈ G, (e.p ∉ V → e.q = t) ∧ (e.q ∉ V → e.p = t) := by
  intro e he
  have hev := Inside.of_factor hG.fac e he
  constructor
  · intro hx
    have : e.p = p := by
      rcases Finset.mem_insert.1 hev.1 with h | h
      · exact h
      · exact absurd h hx
    have := (hG.pat e (Or.inl this)).1 he
    subst this
    rcases he0 with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact absurd (h1 ▸ htV) hx
    · exact h2
  · intro hx
    have : e.q = p := by
      rcases Finset.mem_insert.1 hev.2 with h | h
      · exact h
      · exact absurd h hx
    have := (hG.pat e (Or.inr this)).1 he
    subst this
    rcases he0 with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact h1
    · exact absurd (h2 ▸ htV) hx

-- The same, in the form with two out-vertices (both `t`).
--
lemma notch_out (htV : t ∈ V) (he0 : Ends e0 t p) {G : Finset Edge} (hG : NotchF V s p e0 G) :
    ∀ e ∈ G, (e.p ∉ V → e.q = t ∨ e.q = t) ∧ (e.q ∉ V → e.p = t ∨ e.p = t) :=
  out_dup (notch_out1 htV he0 hG)

-- A phase from a notch state, with no bridges yet, ends in a state its outcome describes.
--
lemma notch_pok (htV : t ∈ V) (hpV : p ∉ V) (he0 : Ends e0 t p)
    (hsD : ∀ c, IsCell V c → ¬ IsCorner s c) {G : Finset Edge} (hG : NotchF V s p e0 G) (n : ℕ) :
    POK V G (phase V (insert p V) n G []).1 (phase V (insert p V) n G []).2.1
      (phase V (insert p V) n G []).2.2 :=
  phase_spec (t0 := t) (u0 := t) (Finset.subset_insert _ _) (notch_dc hpV hsD) hG.fac
    (notch_out htV he0 hG) n G [] Reach.base

-- **Soundness.** A `true` comes with a one-piece notch state.
--
theorem runS_sound (htV : t ∈ V) (hpV : p ∉ V) (he0 : Ends e0 t p)
    (hsD : ∀ c, IsCell V c → ¬ IsCorner s c) (hS4 : S4Spec V s p e0) :
    ∀ n G, NotchF V s p e0 G → runS V s p n G = true →
      ∃ G', NotchF V s p e0 G' ∧ ncomp V G' = 1 := by
  intro n
  induction n with
  | zero => intro G hG h; exact ⟨G, hG, by simpa [runS] using h⟩
  | succ n ih =>
    intro G hG h
    by_cases h1 : ncomp V G = 1
    · exact ⟨G, hG, h1⟩
    rw [runS, ite_eq_right h1] at h
    dsimp only at h
    by_cases hso : (phase V (insert p V) ((insert p V).card + 1) G []).2.2 = .stuck ∨
        (phase V (insert p V) ((insert p V).card + 1) G []).2.2 = .fuel
    · rw [ite_eq_left hso] at h; exact absurd h Bool.false_ne_true
    rw [ite_eq_right hso] at h
    push Not at hso
    have h2 : 2 ≤ ncomp (insert p V) G := by
      have := ncomp_pos (F := G) htV; rw [hG.ncomp htV he0]; omega
    exact ih _ (hS4 _ _ _ _ hG h2 (notch_pok htV hpV he0 hsD hG _) hso.1 hso.2).1 h

-- **Completeness.** With a Hamiltonian s–t path, a notch state with at most `n + 1` pieces
-- answers `true` within `n` rounds.
--
theorem runS_complete (hs : Solid V) (hst : s ≠ t) (htV : t ∈ V) (hpV : p ∉ V)
    (he0 : Ends e0 t p) (hsD : ∀ c, IsCell V c → ¬ IsCorner s c) (hS4 : S4Spec V s p e0)
    (hHP : ∃ H, IsFactor V (dST s t) H ∧ ncomp V H = 1) :
    ∀ n G, NotchF V s p e0 G → ncomp V G ≤ n + 1 → runS V s p n G = true := by
  intro n
  induction n with
  | zero =>
    intro G _ hle
    have := ncomp_pos (F := G) htV
    simp only [runS, decide_eq_true_eq]; omega
  | succ n ih =>
    intro G hG hle
    by_cases h1 : ncomp V G = 1
    · rw [runS, ite_eq_left h1]
    have h2 : 2 ≤ ncomp V G := by have := ncomp_pos (F := G) htV; omega
    rw [runS, ite_eq_right h1]
    dsimp only
    have hpok := notch_pok htV hpV he0 hsD hG ((insert p V).card + 1)
    have hso : ¬ ((phase V (insert p V) ((insert p V).card + 1) G []).2.2 = .stuck ∨
        (phase V (insert p V) ((insert p V).card + 1) G []).2.2 = .fuel) := by
      rintro (hk | hf)
      · rw [hk] at hpok
        obtain ⟨hr, hm, hk'⟩ := hpok
        exact phase_no_hp hs hst htV hpV he0 hsD hG h2 hr hm hk' hHP
      · exact phase_fuel (t0 := t) (u0 := t) (Finset.subset_insert _ _) (notch_dc hpV hsD) hG.fac
          (notch_out htV he0 hG) ((insert p V).card + 1) G [] Reach.base (by omega) _ _
          (Prod.ext rfl (Prod.ext rfl hf))
    rw [ite_eq_right hso]
    push Not at hso
    have h2' : 2 ≤ ncomp (insert p V) G := by rw [hG.ncomp htV he0]; exact h2
    obtain ⟨hN, hc⟩ := hS4 _ _ _ _ hG h2' hpok hso.1 hso.2
    rw [hN.ncomp htV he0, hG.ncomp htV he0] at hc
    exact ih _ hN (by omega)

-- **Correctness of the Sheffield route at a notch**, assuming the S4 statement: with `s` a corner
-- of no cell and `p ∉ V` a neighbour of `t`, `hpSheff` answers `true` exactly when `V` has a
-- Hamiltonian s–t path.
--
theorem hpSheff_correct (hs : Solid V) (hst : s ≠ t) (htV : t ∈ V) (hpV : p ∉ V)
    (he0 : Ends e0 t p) (hsD : ∀ c, IsCell V c → ¬ IsCorner s c) (hS4 : S4Spec V s p e0) :
    hpSheff V s t p e0 = true ↔ ∃ H, IsFactor V (dST s t) H ∧ ncomp V H = 1 := by
  constructor
  · intro h
    unfold hpSheff at h
    rcases hR : findFactor V (dST s t) with _ | R
    · rw [hR] at h; simp at h
    rw [hR] at h
    obtain ⟨G, hG, h1⟩ := runS_sound htV hpV he0 hsD hS4 _ _
      (notch_up hst htV hpV he0 (findFactor_some (dST_le s t) hR)) h
    exact ⟨_, notch_down hst htV hpV he0 hG h1⟩
  · intro hHP
    unfold hpSheff
    rcases hR : findFactor V (dST s t) with _ | R
    · obtain ⟨H, hH, _⟩ := hHP
      exact absurd ⟨H, hH⟩ (findFactor_none (dST_le s t) hR)
    have := ncomp_le_card (X := V) (F := insert e0 R)
    exact runS_complete hs hst htV hpV he0 hsD hS4 hHP _ _
      (notch_up hst htV hpV he0 (findFactor_some (dST_le s t) hR)) (by omega)

end loop

end HP

end ULHC
