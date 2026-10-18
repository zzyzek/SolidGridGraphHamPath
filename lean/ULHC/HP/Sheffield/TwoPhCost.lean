/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
import ULHC.HP.Sheffield.TwoPhS4

/-!
# Two phantoms: running time

Costs of `runSC2` and `hpSheffC2` in the style of `SheffCost`, with `N = |V| + 3`
(`|W₂| = |V| + 2`): each round at most `4000 N⁵`, the whole algorithm at most `10⁴ N⁶`.
-/

namespace ULHC

namespace HP

open Finset Classical

def runSC2Cost (V : Finset Pt) (p q : Pt) : ℕ → Finset Edge → ℕ
  | 0, G => cncompCost (insert q (insert p V)) G + 2
  | n + 1, G =>
    cncompCost (insert q (insert p V)) G + 2 +
      if cncomp (insert q (insert p V)) G == 1 then 0
      else
        (insert q (insert p V)).card + 3 +
          phaseCost V (insert q (insert p V)) ((insert q (insert p V)).card + 1) G [] +
          match phase V (insert q (insert p V)) ((insert q (insert p V)).card + 1) G [] with
          | (_, _, .stuck) => 0
          | (_, _, .fuel) => 0
          | (H, BS, out) => reduceOutCCost V (insert q (insert p V)) H BS out +
              runSC2Cost V p q n (reduceOutC V (insert q (insert p V)) H BS out)

def hpSheffC2Cost (V : Finset Pt) (s t p q : Pt) (e0 e1 : Edge) : ℕ :=
  DFC.findFactorCost V (dST s t) + 1 +
    match findFactor V (dST s t) with
    | none => 0
    | some R => runSC2Cost V p q (V.card + 2) (insert e1 (insert e0 R))

section twoCost

variable {V : Finset Pt} {s t p q : Pt} {e0 e1 : Edge}
  (hst : s ≠ t) (hsV : s ∈ V) (htV : t ∈ V) (hpV : p ∉ V) (hqV : q ∉ V) (hpq : p ≠ q)
  (he0 : Ends e0 t p) (he1 : Ends e1 s q) (hfr : FarN t p s q)
include hsV htV hpV hqV hpq he0 he1 hfr

omit hsV htV he0 he1 hfr in
lemma card_w2 : (insert q (insert p V)).card = V.card + 2 := by
  have hqV' : q ∉ insert p V := by
    rw [Finset.mem_insert]; rintro (h | h)
    · exact hpq h.symm
    · exact hqV h
  rw [Finset.card_insert_of_notMem hqV', Finset.card_insert_of_notMem hpV]

theorem runSC2Cost_le :
    ∀ n G, NotchF2 V p q e0 e1 G → runSC2Cost V p q n G ≤ (n + 1) * (4000 * (V.card + 3) ^ 5) := by
  have hW := card_w2 hpV hqV hpq
  have a3 : (V.card + 3) ^ 3 ≤ (V.card + 3) ^ 5 := Nat.pow_le_pow_right (by omega) (by omega)
  have a0 : 1 ≤ (V.card + 3) ^ 5 := Nat.one_le_pow _ _ (by omega)
  intro n
  induction n with
  | zero =>
    intro G hG
    have := cncompCost_le (Inside.of_factor hG.fac)
    rw [hW, show V.card + 2 + 1 = V.card + 3 by omega] at this
    simp only [runSC2Cost]
    omega
  | succ n ih =>
    intro G hG
    have hc := cncompCost_le (Inside.of_factor hG.fac)
    rw [hW, show V.card + 2 + 1 = V.card + 3 by omega] at hc
    have e : (n + 1 + 1) * (4000 * (V.card + 3) ^ 5) =
        (n + 1) * (4000 * (V.card + 3) ^ 5) + 4000 * (V.card + 3) ^ 5 := Nat.succ_mul _ _
    have hX : 4000 * (V.card + 3) ^ 5 ≤ (n + 1) * (4000 * (V.card + 3) ^ 5) :=
      Nat.le_mul_of_pos_left _ (by omega)
    rw [e]
    simp only [runSC2Cost]
    split
    · omega
    · rename_i h1
      have hI0 : PhI V (insert q (insert p V)) G [] := ⟨Inside.of_factor hG.fac, by simp⟩
      have hph := phaseCost_le vw2 ((insert q (insert p V)).card + 1) G [] hI0 (by simp)
      have hle5 : V.card + 3 ≤ (V.card + 3) ^ 5 := Nat.le_self_pow (by omega) _
      have hph' : phaseCost V (insert q (insert p V)) ((insert q (insert p V)).card + 1) G [] ≤
          3000 * (V.card + 3) ^ 5 := by
        refine hph.trans ?_
        rw [hW, show V.card + 2 + 1 = V.card + 3 by omega]
        have e5 : (V.card + 3) * (V.card + 3) ^ 4 = (V.card + 3) ^ 5 := by ring
        nlinarith
      obtain ⟨hI, hlen, hgr⟩ := phase_inv vw2 ((insert q (insert p V)).card + 1) G [] hI0
      have hpok := two_pok hsV htV hpV hqV he0 he1 hG ((insert q (insert p V)).card + 1)
      rcases hp : phase V (insert q (insert p V)) ((insert q (insert p V)).card + 1) G [] with
        ⟨H, BS, out⟩
      rw [hp] at hI hlen hgr hpok
      dsimp only at hI hlen hgr hpok
      simp only [List.length_nil, zero_add] at hlen
      have hro := reduceOutCCost_le vw2 hI (by omega) (out := out)
        (fun g hg' => (hgr g hg').1)
      rw [hW, show V.card + 2 + 1 = V.card + 3 by omega] at hro
      cases out with
      | stuck => simp only; omega
      | fuel => simp only; omega
      | merge c =>
        simp only
        have := ih _ (s4C2 hsV htV hpV hqV he0 he1 hfr hG hpok (by simp) (by simp)).1
        omega
      | odd b =>
        simp only
        have := ih _ (s4C2 hsV htV hpV hqV he0 he1 hfr hG hpok (by simp) (by simp)).1
        omega
      | twist b =>
        simp only
        have := ih _ (s4C2 hsV htV hpV hqV he0 he1 hfr hG hpok (by simp) (by simp)).1
        omega

include hst

theorem hpSheffC2Cost_le : hpSheffC2Cost V s t p q e0 e1 ≤ 10000 * (V.card + 3) ^ 6 := by
  unfold hpSheffC2Cost
  have hd := DFC.findFactorCost_le V (dST s t)
  have a3 : (V.card + 1) ^ 3 ≤ (V.card + 3) ^ 6 :=
    (Nat.pow_le_pow_left (by omega) 3).trans (Nat.pow_le_pow_right (by omega) (by omega))
  have e6 : (V.card + 3) * (V.card + 3) ^ 5 = (V.card + 3) ^ 6 := by ring
  have a1 : 1 ≤ (V.card + 1) ^ 3 := Nat.one_le_pow _ _ (by omega)
  rcases hR : findFactor V (dST s t) with _ | R
  · simp only; omega
  · simp only
    have := runSC2Cost_le hsV htV hpV hqV hpq he0 he1 hfr (V.card + 2) _
      (two_up hst hsV htV hpV hqV hpq he0 he1 (findFactor_some (dST_le s t) hR))
    have h1 : (V.card + 2 + 1) * (4000 * (V.card + 3) ^ 5) = (V.card + 3) * (4000 * (V.card + 3) ^ 5) :=
      by ring
    nlinarith

-- **Two phantoms, decided in polynomial time.**
--
theorem hpSheffC2_main (hs : Solid V) :
    (hpSheffC2 V s t p q e0 e1 = true ↔ ∃ H, IsFactor V (dST s t) H ∧ ncomp V H = 1) ∧
      hpSheffC2Cost V s t p q e0 e1 ≤ 10000 * (V.card + 3) ^ 6 :=
  ⟨hpSheffC2_correct hst hsV htV hpV hqV hpq he0 he1 hfr hs,
    hpSheffC2Cost_le hst hsV htV hpV hqV hpq he0 he1 hfr⟩

end twoCost

end HP

end ULHC
