/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
import ULHC.HP.Sheffield.HoleTwoV

/-!
# Both endpoints inner: running time

`twoHoleFinalTest`: the box test, a reference factor, and per pair of classes (at most `(2|U| + 1)²`) one
`classSearch` and one two-phantom loop, at most `2.5·10⁴ (|U| + 3)⁶` steps; `twoHoleCase` takes at most
`5 217 000 (|V| + 3)⁶` steps (`twoHoleCase_main`).
-/

namespace ULHC

namespace HP

open Finset Classical

noncomputable def twoHoleFinalTestCost (U : Finset Pt) (s w t r q : Pt) (e0 e1 : Edge) : ℕ :=
  10 + 8 * U.card +
    if isNarrow U = true then
      DFC.findFactorCost U (dST s w) + 1 +
        (match findFactor U (dST s w) with
          | none => 0
          | some R => ((classRange U).map fun h1 => ((classRange U).map fun h2 =>
              2 + classSearchCost U (insert e1 (insert e0 R)) [t, r] [h1, h2] +
                (match classSearch U (insert e1 (insert e0 R)) [t, r] [h1, h2] with
                  | some G => twoPhantomLoopCost U t q (U.card + 2) G
                  | none => 0)).sum).sum)
    else 0

section twoHoleFinalTestCost

variable {Vo : Finset Pt} {t r w : Pt} {e0 : Edge} {U : Finset Pt} {s q : Pt} {e1 : Edge}

theorem twoHoleFinalTestCost_le (hI : WS Vo t r w e0 U s q e1) (hfr : FarN w t s q) :
    twoHoleFinalTestCost U s w t r q e0 e1 ≤ 25000 * (U.card + 3) ^ 6 := by
  have hVW : U ⊆ insert q (insert t U) :=
    (Finset.subset_insert _ _).trans (Finset.subset_insert _ _)
  have hW := card_w2 hI.tU hI.qU hI.qt.symm
  set N := U.card + 3 with hN
  have a1 : 1 ≤ N := by omega
  have p3 : N ^ 3 ≤ N ^ 6 := Nat.pow_le_pow_right a1 (by omega)
  have p1 : N ≤ N ^ 6 := Nat.le_self_pow (by omega) _
  have p0 : 1 ≤ N ^ 4 := Nat.one_le_pow _ _ a1
  unfold twoHoleFinalTestCost
  split_ifs with hnar
  · simp only [isNarrow, Bool.and_eq_true, decide_eq_true_eq] at hnar
    have hd := DFC.findFactorCost_le U (dST s w)
    have hd' : 200 * (U.card + 1) ^ 3 ≤ 200 * N ^ 3 :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 3)
    rcases hR : findFactor U (dST s w) with _ | R
    · simp only; omega
    · simp only
      have hF := two_up hI.sw hI.sU hI.wU hI.tU hI.qU hI.qt.symm hI.he0 hI.he1
        (findFactor_some (dST_le s w) hR)
      have hin : ∀ h1 : ℤ, ((classRange U).map fun h2 =>
          2 + classSearchCost U (insert e1 (insert e0 R)) [t, r] [h1, h2] +
            (match classSearch U (insert e1 (insert e0 R)) [t, r] [h1, h2] with
              | some G => twoPhantomLoopCost U t q (U.card + 2) G
              | none => 0)).sum ≤ 10000 * N ^ 5 := by
        intro h1
        have hs := lsum_le (classRange U) (fun h2 =>
            2 + classSearchCost U (insert e1 (insert e0 R)) [t, r] [h1, h2] +
              (match classSearch U (insert e1 (insert e0 R)) [t, r] [h1, h2] with
                | some G => twoPhantomLoopCost U t q (U.card + 2) G
                | none => 0)) (5000 * N ^ 4) (fun h2 _ => by
          have hT := classSearchCost_le hVW (Inside.of_factor hF.fac) hnar.1 hnar.2 [t, r] [h1, h2]
            (F := insert e1 (insert e0 R))
          rw [hW] at hT
          simp only [List.length_cons, List.length_nil] at hT
          have hT' : 500 * (0 + 1 + 1 + 1) * (U.card + 2 + 1) ^ 4 ≤ 1500 * N ^ 4 := by
            rw [show U.card + 2 + 1 = N by omega]
          rcases hG : classSearch U (insert e1 (insert e0 R)) [t, r] [h1, h2] with _ | G
          · simp only; omega
          · simp only
            obtain ⟨hGf, hFG, _⟩ := kFind2_sound hVW hF.fac hG
            have hGN := notch2_of_symm hI.tU hI.qU hF hGf hFG
            have hr := twoPhantomLoopCost_le hI.sU hI.wU hI.tU hI.qU hI.qt.symm hI.he0 hI.he1 hfr
              (U.card + 2) G hGN
            rw [← hN] at hr
            have h5 : (U.card + 2 + 1) * (3000 * N ^ 3) = 3000 * N ^ 4 := by
              rw [show U.card + 2 + 1 = N by omega]; ring
            have hr' := hr.trans h5.le
            omega)
        rw [length_hRange] at hs
        have h2 : (2 * U.card + 1) * (5000 * N ^ 4) ≤ 2 * N * (5000 * N ^ 4) :=
          Nat.mul_le_mul_right _ (by omega)
        have e8 : 2 * N * (5000 * N ^ 4) = 10000 * N ^ 5 := by ring
        omega
      have hs := lsum_le (classRange U) _ (10000 * N ^ 5) (fun h1 _ => hin h1)
      rw [length_hRange] at hs
      have h2 : (2 * U.card + 1) * (10000 * N ^ 5) ≤ 2 * N * (10000 * N ^ 5) :=
        Nat.mul_le_mul_right _ (by omega)
      have e9 : 2 * N * (10000 * N ^ 5) = 20000 * N ^ 6 := by ring
      omega
  · omega

end twoHoleFinalTestCost

noncomputable def twoHoleCaseCost (V : Finset Pt) (s t : Pt) : ℕ :=
  holeCaseCost (fun w e0 U s' q e1 => twoHoleFinalTestCost U s' w t s q e0 e1) V s t

section twoHoleCaseCost

variable {V : Finset Pt} {s t : Pt}

-- **Both endpoints inner: decided in polynomial time.** For solid `V` and distinct inner `s`, `t`,
-- `twoHoleCase` answers `true` exactly when `V` has a Hamiltonian `s`–`t` path, within
-- `5 217 000 (|V| + 3)⁶` steps.
--
theorem twoHoleCase_main (hs : Solid V) (ht : Inner V t) (hsI : Inner V s) (hst : s ≠ t) :
    (twoHoleCase V s t = true ↔ ∃ H, IsFactor V (dST s t) H ∧ ncomp V H = 1) ∧
      twoHoleCaseCost V s t ≤ (208 * 25000 + 17000) * (V.card + 3) ^ 6 :=
  ⟨twoHoleCase_correct hs ht hsI hst,
    holeCaseCost_le hs ht hst (fun _ _ _ _ _ _ hI hfr => twoHoleFinalTestCost_le hI hfr) (by norm_num)⟩

end twoHoleCaseCost

end HP

end ULHC
