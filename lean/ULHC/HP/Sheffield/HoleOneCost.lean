/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
import ULHC.HP.Sheffield.HoleOne

/-!
# An inner endpoint, the other dangling: running time

Per branch: the box test, a reference factor, and per class (at most `2|V| + 1`) one `classSearchOne` and
one loop. With `N = |V| + 3`, at most `5·10⁴ N⁸` steps (`hpI1_main`).
-/

namespace ULHC

namespace HP

open Finset Classical

noncomputable def hpI1Cost (V : Finset Pt) (s t : Pt) : ℕ :=
  10 + ((nbrsL t).map fun x => 10 + 8 * V.card +
    if x.1 ∈ V ∧ x.1 ≠ s ∧ isNarrow (V.erase t) = true then
      DFC.findFactorCost (V.erase t) (dST s x.1) + 1 +
        (match findFactor (V.erase t) (dST s x.1) with
          | none => 0
          | some R => ((classRange (V.erase t)).map fun h =>
              2 + classSearchOneCost (V.erase t) (insert x.2 R) t h +
                (match classSearchOne (V.erase t) (insert x.2 R) t h with
                  | some G => runSCCost (V.erase t) t ((V.erase t).card + 2) G
                  | none => 0)).sum)
    else 0).sum

section cost

variable {V : Finset Pt} {s t : Pt}

lemma length_hRange (U : Finset Pt) : (classRange U).length = 2 * U.card + 1 := by
  simp [classRange]

theorem hpI1Cost_le (ht : Inner V t) (hsD : ∀ c, IsCell (V.erase t) c → ¬ IsCorner s c) :
    hpI1Cost V s t ≤ 50000 * (V.card + 3) ^ 8 := by
  have htV : t ∈ V := ht.2.2.2.1
  have htV' : t ∉ V.erase t := Finset.notMem_erase t V
  have hcard : (V.erase t).card + 1 = V.card := Finset.card_erase_add_one htV
  have hW : (insert t (V.erase t)).card = V.card := by
    rw [Finset.card_insert_of_notMem htV', hcard]
  have hVW : V.erase t ⊆ insert t (V.erase t) := Finset.subset_insert _ _
  set N := V.card + 3 with hN
  have a1 : 1 ≤ N := by omega
  have p3 : N ^ 3 ≤ N ^ 8 := Nat.pow_le_pow_right a1 (by omega)
  have p7 : N ^ 7 ≤ N ^ 8 := Nat.pow_le_pow_right a1 (by omega)
  have p1 : N ≤ N ^ 8 := Nat.le_self_pow (by omega) _
  have p0 : 1 ≤ N ^ 7 := Nat.one_le_pow _ _ a1
  have hbr : ∀ x ∈ nbrsL t, (10 + 8 * V.card +
      if x.1 ∈ V ∧ x.1 ≠ s ∧ isNarrow (V.erase t) = true then
        DFC.findFactorCost (V.erase t) (dST s x.1) + 1 +
          (match findFactor (V.erase t) (dST s x.1) with
            | none => 0
            | some R => ((classRange (V.erase t)).map fun h =>
                2 + classSearchOneCost (V.erase t) (insert x.2 R) t h +
                  (match classSearchOne (V.erase t) (insert x.2 R) t h with
                    | some G => runSCCost (V.erase t) t ((V.erase t).card + 2) G
                    | none => 0)).sum)
      else 0) ≤ 12000 * N ^ 8 := by
    intro x hx
    split_ifs with hc
    · obtain ⟨hxV, hxs, hnar⟩ := hc
      simp only [isNarrow, Bool.and_eq_true, decide_eq_true_eq] at hnar
      have hends := nbrsL_ends hx
      have he0 : Ends x.2 x.1 t := by rcases hends with h | h; exacts [Or.inr h, Or.inl h]
      have hwV' : x.1 ∈ V.erase t := Finset.mem_erase.2 ⟨(edge_ne hends).symm, hxV⟩
      have hd := DFC.findFactorCost_le (V.erase t) (dST s x.1)
      have hd' : 200 * ((V.erase t).card + 1) ^ 3 ≤ 200 * N ^ 3 :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 3)
      rcases hR : findFactor (V.erase t) (dST s x.1) with _ | R
      · simp only; omega
      · simp only
        have hF := notch_up (Ne.symm hxs) hwV' htV' he0 (findFactor_some (dST_le s x.1) hR)
        have hs := lsum_le (classRange (V.erase t)) (fun h =>
            2 + classSearchOneCost (V.erase t) (insert x.2 R) t h +
              (match classSearchOne (V.erase t) (insert x.2 R) t h with
                | some G => runSCCost (V.erase t) t ((V.erase t).card + 2) G
                | none => 0)) (5000 * N ^ 7) (fun h _ => by
          have hT := classSearchOneCost_le hVW (Inside.of_factor hF.fac) hnar.1 hnar.2 t h (F := insert x.2 R)
          rw [hW] at hT
          have hT' : 1000 * (V.card + 1) ^ 4 ≤ 1000 * N ^ 4 :=
            Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 4)
          have p57 : 2 + N ^ 4 ≤ N ^ 7 := by
            have e : N ^ 7 = N ^ 4 * N ^ 3 := by ring
            have h9 : 9 ≤ N ^ 3 := by
              have := Nat.pow_le_pow_left (show 3 ≤ N by omega) 3
              norm_num at this; omega
            have h1 : 1 ≤ N ^ 4 := Nat.one_le_pow _ _ a1
            nlinarith
          rcases hG : classSearchOne (V.erase t) (insert x.2 R) t h with _ | G
          · simp only; omega
          · simp only
            obtain ⟨hGf, hFG, _⟩ := classSearchOne_sound hVW hF.fac hG
            have hGN := notch_of_symm htV' hF hGf hFG
            have hr := runSCCost_le hwV' htV' he0 hsD ((V.erase t).card + 2) G hGN
            have h5 : ((V.erase t).card + 2 + 1) * (4000 * ((V.erase t).card + 2) ^ 5) ≤
                N * (4000 * N ^ 5) := Nat.mul_le_mul (by omega)
                  (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 5))
            have e6 : N * (4000 * N ^ 5) = 4000 * N ^ 6 := by ring
            have p6 : N ^ 6 ≤ N ^ 7 := Nat.pow_le_pow_right a1 (by omega)
            omega)
        rw [length_hRange] at hs
        have h2 : (2 * (V.erase t).card + 1) * (5000 * N ^ 7) ≤ 2 * N * (5000 * N ^ 7) :=
          Nat.mul_le_mul_right _ (by omega)
        have e8 : 2 * N * (5000 * N ^ 7) = 10000 * N ^ 8 := by ring
        omega
    · omega
  have hs := lsum_le (nbrsL t) _ (12000 * N ^ 8) hbr
  have hl : (nbrsL t).length = 4 := rfl
  rw [hl] at hs
  unfold hpI1Cost
  omega

-- **An inner endpoint, the other dangling: decided in polynomial time.**
--
theorem hpI1_main (hs : Solid V) (ht : Inner V t) (hst : s ≠ t)
    (hsD : ∀ c, IsCell (V.erase t) c → ¬ IsCorner s c) (h3 : 3 ≤ V.card) :
    (hpI1 V s t = true ↔ ∃ H, IsFactor V (dST s t) H ∧ ncomp V H = 1) ∧
      hpI1Cost V s t ≤ 50000 * (V.card + 3) ^ 8 :=
  ⟨hpI1_correct hs ht hst hsD h3, hpI1Cost_le ht hsD⟩

end cost

end HP

end ULHC
