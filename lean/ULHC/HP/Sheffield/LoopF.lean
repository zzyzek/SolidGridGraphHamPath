/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
import ULHC.HP.Sheffield.PhaseSCost

/-!
# The fast two-phantom loop: `O(N³)` per round, `O(N⁴)` in all

`twoPhantomLoopCost_le`: with `N = |V| + 3`, `twoPhantomLoop` with fuel `n` costs at most `(n + 1) · 3000 N³`.
`twoPhantomTest` (the reference factor, then `twoPhantomLoop`) decides what `hpSheffC2` decides
(`twoPhantomTest_eq`) within `5000 N⁴` steps (`twoPhantomTestCost_le`).
-/

namespace ULHC

namespace HP

open Finset Classical

def twoPhantomLoopCost (V : Finset Pt) (p q : Pt) : ℕ → Finset Edge → ℕ
  | 0, G => cncompCost (insert q (insert p V)) G + 2
  | n + 1, G =>
    cncompCost (insert q (insert p V)) G + 2 +
      if cncomp (insert q (insert p V)) G == 1 then 0
      else
        (insert q (insert p V)).card + 3 +
          runPhaseCost V (insert q (insert p V)) ((insert q (insert p V)).card + 1) G [] +
          match runPhase V (insert q (insert p V)) ((insert q (insert p V)).card + 1) G [] with
          | (_, _, .stuck) => 0
          | (_, _, .fuel) => 0
          | (H, BS, out) => reducePiecesCost V (insert q (insert p V)) H BS out +
              twoPhantomLoopCost V p q n (reducePieces V (insert q (insert p V)) H BS out)

def twoPhantomTest (V : Finset Pt) (s t p q : Pt) (e0 e1 : Edge) : Bool :=
  match findFactor V (dST s t) with
  | none => false
  | some R => twoPhantomLoop V p q (V.card + 2) (insert e1 (insert e0 R))

def twoPhantomTestCost (V : Finset Pt) (s t p q : Pt) (e0 e1 : Edge) : ℕ :=
  DFC.findFactorCost V (dST s t) + 1 +
    match findFactor V (dST s t) with
    | none => 0
    | some R => twoPhantomLoopCost V p q (V.card + 2) (insert e1 (insert e0 R))

section loopFCost

variable {V : Finset Pt} {s t p q : Pt} {e0 e1 : Edge}
  (hst : s ≠ t) (hsV : s ∈ V) (htV : t ∈ V) (hpV : p ∉ V) (hqV : q ∉ V) (hpq : p ≠ q)
  (he0 : Ends e0 t p) (he1 : Ends e1 s q) (hfr : FarN t p s q)
include hsV htV hpV hqV hpq he0 he1 hfr

theorem twoPhantomLoopCost_le :
    ∀ n G, NotchF2 V p q e0 e1 G → twoPhantomLoopCost V p q n G ≤ (n + 1) * (3000 * (V.card + 3) ^ 3) := by
  have hW := card_w2 hpV hqV hpq
  have a0 : 1 ≤ (V.card + 3) ^ 3 := Nat.one_le_pow _ _ (by omega)
  have a2 : (V.card + 3) ^ 2 ≤ (V.card + 3) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
  have a1 : V.card + 3 ≤ (V.card + 3) ^ 3 := Nat.le_self_pow (by omega) _
  intro n
  induction n with
  | zero =>
    intro G hG
    have := cncompCost_le (Inside.of_factor hG.fac)
    rw [hW, show V.card + 2 + 1 = V.card + 3 by omega] at this
    simp only [twoPhantomLoopCost]
    omega
  | succ n ih =>
    intro G hG
    have hc := cncompCost_le (Inside.of_factor hG.fac)
    rw [hW, show V.card + 2 + 1 = V.card + 3 by omega] at hc
    have e : (n + 1 + 1) * (3000 * (V.card + 3) ^ 3) =
        (n + 1) * (3000 * (V.card + 3) ^ 3) + 3000 * (V.card + 3) ^ 3 := Nat.succ_mul _ _
    have hX : 3000 * (V.card + 3) ^ 3 ≤ (n + 1) * (3000 * (V.card + 3) ^ 3) :=
      Nat.le_mul_of_pos_left _ (by omega)
    rw [e]
    simp only [twoPhantomLoopCost]
    split
    · omega
    · rename_i h1
      have hI0 : PhI V (insert q (insert p V)) G [] := ⟨Inside.of_factor hG.fac, by simp⟩
      have hph := runPhaseCost_le vw2 ((insert q (insert p V)).card + 1) G [] hI0 (by simp)
      have hph' : runPhaseCost V (insert q (insert p V)) ((insert q (insert p V)).card + 1) G [] ≤
          1600 * (V.card + 3) ^ 3 := by
        refine hph.trans ?_
        rw [hW, show V.card + 2 + 1 = V.card + 3 by omega]
        have e3 : (V.card + 3) * (V.card + 3) ^ 2 = (V.card + 3) ^ 3 := by ring
        nlinarith
      rw [runPhase_eq vw2 _ G [] hI0]
      obtain ⟨hI, hlen, hgr⟩ := phase_inv vw2 ((insert q (insert p V)).card + 1) G [] hI0
      have hpok := two_pok hsV htV hpV hqV he0 he1 hG ((insert q (insert p V)).card + 1)
      rcases hp : phase V (insert q (insert p V)) ((insert q (insert p V)).card + 1) G [] with
        ⟨H, BS, out⟩
      rw [hp] at hI hlen hgr hpok
      dsimp only at hI hlen hgr hpok
      simp only [List.length_nil, zero_add] at hlen
      have hro := reducePiecesCost_le vw2 hI (by omega) (out := out)
        (fun g hg' => (hgr g hg').1)
      rw [hW, show V.card + 2 + 1 = V.card + 3 by omega] at hro
      cases out with
      | stuck => simp only; omega
      | fuel => simp only; omega
      | merge c =>
        obtain ⟨hHW, hb⟩ := brW2 hsV htV hpV hqV he0 he1 hG hpok.1
        simp only
        rw [reducePieces_eq vw2 hHW hb (fun c' h => by cases h; exact hpok.2.1)
          (fun g h => by rcases h with h | h <;> cases h)]
        have := ih _ (s4C2 hsV htV hpV hqV he0 he1 hfr hG hpok (by simp) (by simp)).1
        omega
      | odd g =>
        obtain ⟨hHW, hb⟩ := brW2 hsV htV hpV hqV he0 he1 hG hpok.1
        simp only
        rw [reducePieces_eq vw2 hHW hb (fun c' h => by cases h)
          (fun g' h => by rcases h with h | h <;> cases h; exact hpok.2.2.1.1)]
        have := ih _ (s4C2 hsV htV hpV hqV he0 he1 hfr hG hpok (by simp) (by simp)).1
        omega
      | twist g =>
        obtain ⟨hHW, hb⟩ := brW2 hsV htV hpV hqV he0 he1 hG hpok.1
        simp only
        rw [reducePieces_eq vw2 hHW hb (fun c' h => by cases h)
          (fun g' h => by rcases h with h | h <;> cases h; exact hpok.2.2.1.1)]
        have := ih _ (s4C2 hsV htV hpV hqV he0 he1 hfr hG hpok (by simp) (by simp)).1
        omega

include hst

theorem twoPhantomTest_eq : twoPhantomTest V s t p q e0 e1 = hpSheffC2 V s t p q e0 e1 := by
  unfold twoPhantomTest hpSheffC2
  rcases hR : findFactor V (dST s t) with _ | R
  · rfl
  · exact twoPhantomLoop_eq hsV htV hpV hqV he0 he1 hfr _ _
      (two_up hst hsV htV hpV hqV hpq he0 he1 (findFactor_some (dST_le s t) hR))

theorem twoPhantomTestCost_le : twoPhantomTestCost V s t p q e0 e1 ≤ 5000 * (V.card + 3) ^ 4 := by
  unfold twoPhantomTestCost
  have hd := DFC.findFactorCost_le V (dST s t)
  have a3 : (V.card + 1) ^ 3 ≤ (V.card + 3) ^ 4 :=
    (Nat.pow_le_pow_left (by omega) 3).trans (Nat.pow_le_pow_right (by omega) (by omega))
  have e4 : (V.card + 3) * (V.card + 3) ^ 3 = (V.card + 3) ^ 4 := by ring
  have a1 : 1 ≤ (V.card + 1) ^ 3 := Nat.one_le_pow _ _ (by omega)
  rcases hR : findFactor V (dST s t) with _ | R
  · simp only; omega
  · simp only
    have := twoPhantomLoopCost_le hsV htV hpV hqV hpq he0 he1 hfr (V.card + 2) _
      (two_up hst hsV htV hpV hqV hpq he0 he1 (findFactor_some (dST_le s t) hR))
    have h1 : (V.card + 2 + 1) * (3000 * (V.card + 3) ^ 3) =
        (V.card + 3) * (3000 * (V.card + 3) ^ 3) := by ring
    nlinarith

end loopFCost

end HP

end ULHC
