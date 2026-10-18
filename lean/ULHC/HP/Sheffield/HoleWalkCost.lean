/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
import ULHC.HP.Sheffield.WalkCount

/-!
# An inner endpoint, the other on the boundary: running time

`oneHoleFinalTest`: the box test, a reference factor, and per class (at most `2|U| + 1`) one `classSearchOne` and one
two-phantom loop, at most `1.2·10⁴ (|U| + 3)⁵` steps. Each walk
reaches at most 13 final tests and 21 nodes (`holeCaseWalkCost_pot`, by the ring potentials `Lp`, `Mp`);
with the 16 walk starts, `oneHoleCase` takes at most `2 513 000 (|V| + 3)⁵` steps (`oneHoleCase_main`). The
walk's bound holds for any final test (`holeCaseCost_le`).
-/

namespace ULHC

namespace HP

open Finset Classical

noncomputable def oneHoleFinalTestCost (U : Finset Pt) (s w t q : Pt) (e0 e1 : Edge) : ℕ :=
  10 + 8 * U.card +
    if isNarrow U = true then
      DFC.findFactorCost U (dST s w) + 1 +
        (match findFactor U (dST s w) with
          | none => 0
          | some R => ((classRange U).map fun h =>
              2 + classSearchOneCost U (insert e1 (insert e0 R)) t h +
                (match classSearchOne U (insert e1 (insert e0 R)) t h with
                  | some G => twoPhantomLoopCost U t q (U.card + 2) G
                  | none => 0)).sum)
    else 0

section oneHoleFinalTestCost

variable {Vo : Finset Pt} {t r w : Pt} {e0 : Edge} {U : Finset Pt} {s q : Pt} {e1 : Edge}

theorem oneHoleFinalTestCost_le (hI : WS Vo t r w e0 U s q e1) (hfr : FarN w t s q) :
    oneHoleFinalTestCost U s w t q e0 e1 ≤ 12000 * (U.card + 3) ^ 5 := by
  have hVW : U ⊆ insert q (insert t U) :=
    (Finset.subset_insert _ _).trans (Finset.subset_insert _ _)
  have hW := card_w2 hI.tU hI.qU hI.qt.symm
  set N := U.card + 3 with hN
  have a1 : 1 ≤ N := by omega
  have p3 : N ^ 3 ≤ N ^ 5 := Nat.pow_le_pow_right a1 (by omega)
  have p1 : N ≤ N ^ 5 := Nat.le_self_pow (by omega) _
  have p0 : 1 ≤ N ^ 4 := Nat.one_le_pow _ _ a1
  unfold oneHoleFinalTestCost
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
      have hs := lsum_le (classRange U) (fun h =>
          2 + classSearchOneCost U (insert e1 (insert e0 R)) t h +
            (match classSearchOne U (insert e1 (insert e0 R)) t h with
              | some G => twoPhantomLoopCost U t q (U.card + 2) G
              | none => 0)) (5000 * N ^ 4) (fun h _ => by
        have hT := classSearchOneCost_le hVW (Inside.of_factor hF.fac) hnar.1 hnar.2 t h
          (F := insert e1 (insert e0 R))
        rw [hW] at hT
        have hT' : 1000 * (U.card + 2 + 1) ^ 4 ≤ 1000 * N ^ 4 :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 4)
        rcases hG : classSearchOne U (insert e1 (insert e0 R)) t h with _ | G
        · simp only; omega
        · simp only
          obtain ⟨hGf, hFG, _⟩ := classSearchOne_sound hVW hF.fac hG
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
  · omega

end oneHoleFinalTestCost

noncomputable def holeCaseWalkCost (finC : Finset Pt → Pt → Pt → Edge → ℕ) (w pw : Pt) :
    ℕ → Finset Pt → Pt → Pt → Edge → ℕ
  | 0, _, _, _, _ => 1
  | n + 1, U, s, q, e1 =>
    U.card + 30 +
      if U.card ≤ 2 then 0
      else if isFar w s && !phantomsOpposed w pw s q then finC U s q e1
      else ((nbrsL s).map fun x =>
          3 + if x.1 ∈ U ∧ x.1 ≠ w then holeCaseWalkCost finC w pw n (U.erase s) x.1 s x.2 else 0).sum

section walkCost

variable {Vo : Finset Pt} {t r w : Pt} {e0 : Edge} {finC : Finset Pt → Pt → Pt → Edge → ℕ}
  {B m : ℕ}

lemma lsum_split {α : Type*} (l : List α) (f a b : α → ℕ) (X Y : ℕ)
    (h : ∀ x ∈ l, f x ≤ 3 + a x * X + b x * Y) :
    (l.map f).sum ≤ 3 * l.length + (l.map a).sum * X + (l.map b).sum * Y := by
  induction l with
  | nil => simp
  | cons c l ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    have h1 := h c List.mem_cons_self
    have h2 := ih (fun x hx => h x (List.mem_cons_of_mem _ hx))
    rw [Nat.add_mul, Nat.add_mul, Nat.mul_succ]; omega

lemma rel_unit {e0 : Edge} {w t : Pt} (h : Ends e0 w t) : rel w t ∈ units4 := by
  have hc := ends_close1 h
  have hne := edge_ne h
  obtain ⟨d, ⟨x, y⟩⟩ := e0
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> cases d <;> simp only [Edge.q] at h1 h2 <;>
    subst h1 <;> subst h2 <;> simp [rel, units4]

-- **The walk's cost by its potentials**: `Lp` final tests and `Mp` nodes.
--
theorem holeCaseWalkCost_pot
    (hfc : ∀ U s q e1, WS Vo t r w e0 U s q e1 → FarN w t s q → finC U s q e1 ≤ B * (U.card + 3) ^ m)
    (hm : 1 ≤ m) :
    ∀ n U s q e1, WS Vo t r w e0 U s q e1 →
      holeCaseWalkCost finC w t n U s q e1 ≤
        Lp w t U s q * (B * (U.card + 3) ^ m) + Mp w t U s q * (50 * (U.card + 3) ^ m) := by
  intro n
  induction n with
  | zero =>
    intro U s q e1 _
    simp only [holeCaseWalkCost]
    have h1 := Mp_pos (w := w) (t := t) U s q
    have h2 : 1 ≤ 50 * (U.card + 3) ^ m := by
      have : 1 ≤ (U.card + 3) ^ m := Nat.one_le_pow _ _ (by omega)
      omega
    have := Nat.mul_le_mul h1 h2
    omega
  | succ n ih =>
    intro U s q e1 hI
    have ha := rel_unit hI.he0
    set X := B * (U.card + 3) ^ m with hX
    set Y := 50 * (U.card + 3) ^ m with hY
    have am : U.card + 3 ≤ (U.card + 3) ^ m := Nat.le_self_pow (by omega) _
    have hY1 : U.card + 42 ≤ Y := by omega
    simp only [holeCaseWalkCost]
    by_cases h2 : U.card ≤ 2
    · rw [ite_eq_left h2]
      have : Mp w t U s q = 1 := by unfold Mp; rw [ite_eq_left h2]
      rw [this]; omega
    rw [ite_eq_right h2]
    by_cases hst : (isFar w s && !phantomsOpposed w t s q) = true
    · rw [ite_eq_left hst]
      have hL : Lp w t U s q = 1 := by unfold Lp stopB; rw [ite_eq_right h2, ite_eq_left hst]
      have hM : Mp w t U s q = 1 := by unfold Mp stopB; rw [ite_eq_right h2, ite_eq_left hst]
      have hf := hst
      simp only [Bool.and_eq_true, Bool.not_eq_true', phantomsOpposed, decide_eq_false_iff_not] at hf
      have := hfc U s q e1 hI ⟨isFar_iff.1 hf.1, hf.2⟩
      rw [hL, hM]; omega
    rw [ite_eq_right hst]
    -- children
    have hchild : ∀ x ∈ nbrsL s, (3 +
        if x.1 ∈ U ∧ x.1 ≠ w then holeCaseWalkCost finC w t n (U.erase s) x.1 s x.2 else 0) ≤
        3 + (if x.1 ∈ U ∧ x.1 ≠ w then Lp w t (U.erase s) x.1 s else 0) * X +
          (if x.1 ∈ U ∧ x.1 ≠ w then Mp w t (U.erase s) x.1 s else 0) * Y := by
      intro x hx
      split_ifs with hc
      · have := ih _ _ _ _ (ws_step hI hx hc.1 hc.2)
        have hcard : (U.erase s).card + 3 ≤ U.card + 3 := by
          have := Finset.card_erase_le (s := U) (a := s); omega
        have hpm : ((U.erase s).card + 3) ^ m ≤ (U.card + 3) ^ m := Nat.pow_le_pow_left hcard m
        have h1 : Lp w t (U.erase s) x.1 s * (B * ((U.erase s).card + 3) ^ m) ≤
            Lp w t (U.erase s) x.1 s * X := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hpm)
        have h2 : Mp w t (U.erase s) x.1 s * (50 * ((U.erase s).card + 3) ^ m) ≤
            Mp w t (U.erase s) x.1 s * Y := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hpm)
        omega
      · omega
    -- the potentials of the children
    have hpot : ((nbrsL s).map fun x =>
        if x.1 ∈ U ∧ x.1 ≠ w then Lp w t (U.erase s) x.1 s else 0).sum ≤ Lp w t U s q ∧
        1 + ((nbrsL s).map fun x =>
          if x.1 ∈ U ∧ x.1 ≠ w then Mp w t (U.erase s) x.1 s else 0).sum ≤ Mp w t U s q := by
      by_cases hr : pidx w t s < 7
      · have hse := ptAt_pidx ha hr
        have hL : Lp w t U s q = ringL w t U (pidx w t s) := by
          unfold Lp stopB; rw [ite_eq_right h2, ite_eq_right hst, ite_eq_left hr]
        have hM : Mp w t U s q = ringM w t U (pidx w t s) := by
          unfold Mp stopB; rw [ite_eq_right h2, ite_eq_right hst, ite_eq_left hr]
        rw [hL, hM]
        have := ring_step (U := U) ha hI.tU hr
        rw [hse] at this
        exact this
      · have hop : Opp w t s q := by
          by_contra hno
          apply hst
          have hfar : isFar w s = true := by
            by_contra hf
            have hnf : ¬ Far w s := fun h => hf (isFar_iff.2 h)
            unfold Far at hnf; push Not at hnf
            exact hr (close1_ring ha hnf.2 hI.sw (fun h => hI.tU (h ▸ hI.sU)))
          simp [hfar, phantomsOpposed, hno]
        have hL : Lp w t U s q = 13 := by
          unfold Lp stopB; rw [ite_eq_right h2, ite_eq_right hst, ite_eq_right hr]
        have hM : Mp w t U s q = 21 := by
          unfold Mp stopB; rw [ite_eq_right h2, ite_eq_right hst, ite_eq_right hr]
        rw [hL, hM]
        exact opp_step ha hI.tU hI.qU hop
    obtain ⟨hpL, hpM⟩ := hpot
    have hs := lsum_split (nbrsL s) _ _ _ X Y hchild
    have hl : (nbrsL s).length = 4 := rfl
    rw [hl] at hs
    have hL' := Nat.mul_le_mul_right X hpL
    have hM' := Nat.mul_le_mul_right Y hpM
    rw [Nat.add_mul, one_mul] at hM'
    omega

end walkCost

noncomputable def holeCaseCost (finC : Pt → Edge → Finset Pt → Pt → Pt → Edge → ℕ) (V : Finset Pt)
    (s t : Pt) : ℕ :=
  V.card + 30 +
    if V.card ≤ 2 then 0
    else ((nbrsL t).map fun y => 3 +
      if y.1 ∈ V ∧ y.1 ≠ s then
        V.card + 30 +
          if (V.erase t).card ≤ 2 then 0
          else ((nbrsL s).map fun x => 3 +
            if x.1 ∈ V.erase t ∧ x.1 ≠ y.1 then
              holeCaseWalkCost (finC y.1 y.2) y.1 t 10 ((V.erase t).erase s) x.1 s x.2
            else 0).sum
      else 0).sum

section holeCaseCost

variable {V : Finset Pt} {s t : Pt} {finC : Pt → Edge → Finset Pt → Pt → Pt → Edge → ℕ} {B m : ℕ}

-- **At most 16 walks, each at most 13 final tests and 21 nodes.**
--
theorem holeCaseCost_le (hs : Solid V) (ht : Inner V t) (hst : s ≠ t)
    (hfc : ∀ w e0 U s' q e1, WS V t s w e0 U s' q e1 → FarN w t s' q →
      finC w e0 U s' q e1 ≤ B * (U.card + 3) ^ m) (hm : 1 ≤ m) :
    holeCaseCost finC V s t ≤ (208 * B + 17000) * (V.card + 3) ^ m := by
  set P := (V.card + 3) ^ m with hP
  have am : V.card + 3 ≤ P := Nat.le_self_pow (by omega) _
  have hwalk : ∀ y ∈ nbrsL t, y.1 ∈ V ∧ y.1 ≠ s → ¬ (V.erase t).card ≤ 2 → ∀ x ∈ nbrsL s,
      (3 + if x.1 ∈ V.erase t ∧ x.1 ≠ y.1 then
        holeCaseWalkCost (finC y.1 y.2) y.1 t 10 ((V.erase t).erase s) x.1 s x.2 else 0) ≤
        3 + 13 * (B * P) + 21 * (50 * P) := by
    intro y hy hc _ x hx
    split_ifs with hc'
    · have hI := ws_init hs ht hst hy hc.1 hc.2 hx hc'.1 hc'.2
      have := holeCaseWalkCost_pot (finC := finC y.1 y.2)
        (fun U s' q e1 hI hfr => hfc _ _ U s' q e1 hI hfr) hm 10 _ _ _ _ hI
      have hcard : ((V.erase t).erase s).card + 3 ≤ V.card + 3 := by
        have h1 := Finset.card_erase_le (s := V.erase t) (a := s)
        have h2 := Finset.card_erase_le (s := V) (a := t)
        omega
      have hpm : (((V.erase t).erase s).card + 3) ^ m ≤ P := Nat.pow_le_pow_left hcard m
      have l1 := Lp_le13 (w := y.1) (t := t) ((V.erase t).erase s) x.1 s
      have l2 := Mp_le21 (w := y.1) (t := t) ((V.erase t).erase s) x.1 s
      have k1 : Lp y.1 t ((V.erase t).erase s) x.1 s * (B * (((V.erase t).erase s).card + 3) ^ m) ≤
          13 * (B * P) := Nat.mul_le_mul l1 (Nat.mul_le_mul_left _ hpm)
      have k2 : Mp y.1 t ((V.erase t).erase s) x.1 s * (50 * (((V.erase t).erase s).card + 3) ^ m) ≤
          21 * (50 * P) := Nat.mul_le_mul l2 (Nat.mul_le_mul_left _ hpm)
      omega
    · omega
  have hy : ∀ y ∈ nbrsL t, (3 +
      if y.1 ∈ V ∧ y.1 ≠ s then
        V.card + 30 +
          if (V.erase t).card ≤ 2 then 0
          else ((nbrsL s).map fun x => 3 +
            if x.1 ∈ V.erase t ∧ x.1 ≠ y.1 then
              holeCaseWalkCost (finC y.1 y.2) y.1 t 10 ((V.erase t).erase s) x.1 s x.2
            else 0).sum
      else 0) ≤ V.card + 33 + 4 * (3 + 13 * (B * P) + 21 * (50 * P)) := by
    intro y hy
    split_ifs with hc h2
    · omega
    · have hs := lsum_le (nbrsL s) _ (3 + 13 * (B * P) + 21 * (50 * P)) (hwalk y hy hc h2)
      have hl : (nbrsL s).length = 4 := rfl
      rw [hl] at hs
      omega
    · omega
  have hsum := lsum_le (nbrsL t) _ _ hy
  have hl : (nbrsL t).length = 4 := rfl
  rw [hl] at hsum
  have e : (208 * B + 17000) * P = 208 * (B * P) + 17000 * P := by ring
  unfold holeCaseCost
  rw [e]
  by_cases h2 : V.card ≤ 2
  · rw [ite_eq_left h2]; omega
  · rw [ite_eq_right h2]; omega

end holeCaseCost

noncomputable def oneHoleCaseCost (V : Finset Pt) (s t : Pt) : ℕ :=
  holeCaseCost (fun w e0 U s' q e1 => oneHoleFinalTestCost U s' w t q e0 e1) V s t

section oneHoleCaseCost

variable {V : Finset Pt} {s t : Pt}

-- **An inner endpoint, the other with a missing king neighbour: decided in polynomial time.**
-- For solid `V`, `t` inner and `s ≠ t` in `V` with a missing king neighbour, `oneHoleCase` answers
-- `true` exactly when `V` has a Hamiltonian `s`–`t` path, within `2 513 000 (|V| + 3)⁵` steps.
--
theorem oneHoleCase_main (hs : Solid V) (ht : Inner V t) (hst : s ≠ t) (hsV : s ∈ V)
    (hms : ∃ m, m ∉ V ∧ |m.1 - s.1| ≤ 1 ∧ |m.2 - s.2| ≤ 1) :
    (oneHoleCase V s t = true ↔ ∃ H, IsFactor V (dST s t) H ∧ ncomp V H = 1) ∧
      oneHoleCaseCost V s t ≤ (208 * 12000 + 17000) * (V.card + 3) ^ 5 :=
  ⟨oneHoleCase_correct hs ht hst hsV hms,
    holeCaseCost_le hs ht hst (fun _ _ _ _ _ _ hI hfr => oneHoleFinalTestCost_le hI hfr) (by norm_num)⟩

end oneHoleCaseCost

end HP

end ULHC
