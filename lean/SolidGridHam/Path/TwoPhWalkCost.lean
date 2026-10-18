/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
module

public import SolidGridHam.Path.HoleWalkCost

@[expose] public section

/-!
# Two boundary endpoints: running time

The walk `boundaryEndpointsWalk` moves `t` around the fixed `s`, whose phantom `q` is a lattice neighbour. Once `t`
has a deleted lattice neighbour `p`, the walk is a hole walk around `s` with hole `q`, walker `t`
and phantom `p`, except that it may also stop when `p` is opposed but another phantom of `t` is
usable. So the ring potentials `Lp`, `Mp` bound it again: at most 13 final tests and 21 nodes
(`boundaryEndpointsWalkCost_pot`). The first step has no deleted neighbour yet and at most 4 children, so a walk
from the start reaches at most 52 final tests (`boundaryEndpointsWalkCost_start`), and `boundaryEndpoints` takes at most
`1 060 000 (|V| + 3)⁴` steps (`boundaryEndpoints_main`).
-/

namespace SolidGridHam

namespace HP

open Finset Classical

lemma isFar_comm (a b : Pt) : isFar a b = isFar b a := by
  apply Bool.eq_iff_iff.2
  rw [isFar_iff, isFar_iff]; unfold Far Close1
  rw [abs_sub_comm b.1, abs_sub_comm b.2, eq_comm]

noncomputable def boundaryEndpointsWalkCost (s q : Pt) (e1 : Edge) : ℕ → Finset Pt → Pt → ℕ
  | 0, _, _ => 1
  | n + 1, V, t =>
    V.card + 30 +
      if V.card ≤ 2 then 0
      else
        match (nbrsL t).find? (isUsablePhantom V s q t) with
        | some x =>
          if isFar t s then twoPhantomTestCost V s t x.1 q x.2 e1
          else ((nbrsL t).map fun x =>
            3 + if x.1 ∈ V ∧ x.1 ≠ s then boundaryEndpointsWalkCost s q e1 n (V.erase t) x.1 else 0).sum
        | none => ((nbrsL t).map fun x =>
            3 + if x.1 ∈ V ∧ x.1 ≠ s then boundaryEndpointsWalkCost s q e1 n (V.erase t) x.1 else 0).sum

noncomputable def boundaryEndpointsCost (V : Finset Pt) (s t : Pt) : ℕ :=
  V.card + 30 +
    if V.card ≤ 2 then 0
    else
      match (nbrsL s).find? (fun x => decide (x.1 ∉ V)) with
      | some x => boundaryEndpointsWalkCost s x.1 x.2 12 V t
      | none => ((nbrsL s).map fun x =>
          3 + if x.1 ∈ V ∧ x.1 ≠ t then boundaryEndpointsWalkCost x.1 s x.2 12 (V.erase s) t else 0).sum

section cost

variable {s q : Pt} {e1 : Edge}

lemma back_mem {t : Pt} {x : Pt × Edge} (hx : x ∈ nbrsL t) : (t, x.2) ∈ nbrsL x.1 :=
  mem_nbrsL (by rcases nbrsL_ends hx with h | h; exacts [Or.inr h, Or.inl h])

lemma q_ne {V : Finset Pt} {t : Pt} (hI : WI V s q e1 t) : t ≠ q := fun h => hI.qV (h ▸ hI.tV)

-- The final test, when the walk stops.
--
lemma fin_le {V : Finset Pt} {t : Pt} (hI : WI V s q e1 t) {x : Pt × Edge}
    (hf : (nbrsL t).find? (isUsablePhantom V s q t) = some x) (hfar : isFar t s = true) :
    twoPhantomTestCost V s t x.1 q x.2 e1 ≤ 5000 * (V.card + 3) ^ 4 := by
  have hm := List.mem_of_find?_eq_some hf
  have hp := List.find?_some hf
  simp only [isUsablePhantom, phantomsOpposed, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true',
    decide_eq_false_iff_not] at hp
  obtain ⟨⟨hpV, hpq⟩, hno⟩ := hp
  exact twoPhantomTestCost_le hI.st hI.sV hI.tV hpV hI.qV hpq (nbrsL_ends hm) hI.e1
    ⟨isFar_iff.1 hfar, hno⟩

-- **The walk's cost by its potentials**, once `t` has a deleted lattice neighbour `p`.
--
theorem boundaryEndpointsWalkCost_pot :
    ∀ n V t p, WI V s q e1 t → p ∉ V → p ≠ q → (∃ e, (p, e) ∈ nbrsL t) →
      boundaryEndpointsWalkCost s q e1 n V t ≤
        Lp s q V t p * (5000 * (V.card + 3) ^ 4) + Mp s q V t p * (50 * (V.card + 3) ^ 4) := by
  intro n
  induction n with
  | zero =>
    intro V t p _ _ _ _
    simp only [boundaryEndpointsWalkCost]
    have h1 := Mp_pos (w := s) (t := q) V t p
    have h2 : 1 ≤ 50 * (V.card + 3) ^ 4 := by
      have : 1 ≤ (V.card + 3) ^ 4 := Nat.one_le_pow _ _ (by omega)
      omega
    have := Nat.mul_le_mul h1 h2
    omega
  | succ n ih =>
    intro V t p hI hpV hpq hpn
    have ha := rel_unit hI.e1
    set X := 5000 * (V.card + 3) ^ 4 with hX
    set Y := 50 * (V.card + 3) ^ 4 with hY
    have am : V.card + 3 ≤ (V.card + 3) ^ 4 := Nat.le_self_pow (by omega) _
    have hY1 : V.card + 42 ≤ Y := by omega
    simp only [boundaryEndpointsWalkCost]
    by_cases h2 : V.card ≤ 2
    · rw [ite_eq_left h2]
      have : Mp s q V t p = 1 := by unfold Mp; rw [ite_eq_left h2]
      rw [this]; omega
    rw [ite_eq_right h2]
    -- the children, when the walk goes on
    have hkids : ¬ (isFar t s = true ∧ ∃ x, (nbrsL t).find? (isUsablePhantom V s q t) = some x) →
        ((nbrsL t).map fun x =>
          3 + if x.1 ∈ V ∧ x.1 ≠ s then boundaryEndpointsWalkCost s q e1 n (V.erase t) x.1 else 0).sum +
          (V.card + 30) ≤ Lp s q V t p * X + Mp s q V t p * Y := by
      intro hns
      have hst : ¬ stopB s q t p = true := by
        intro hb
        apply hns
        simp only [stopB, Bool.and_eq_true, Bool.not_eq_true', phantomsOpposed,
          decide_eq_false_iff_not] at hb
        obtain ⟨e, he⟩ := hpn
        refine ⟨by rw [isFar_comm]; exact hb.1, ?_⟩
        rcases hf : (nbrsL t).find? (isUsablePhantom V s q t) with _ | x
        · exfalso
          have h0 := List.find?_eq_none.1 hf _ he
          simp only [isUsablePhantom, phantomsOpposed, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true',
            decide_eq_false_iff_not, not_and, not_not] at h0
          exact hb.2 (opp_symm (h0 ⟨hpV, hpq⟩))
        · exact ⟨x, rfl⟩
      have hchild : ∀ x ∈ nbrsL t, (3 +
          if x.1 ∈ V ∧ x.1 ≠ s then boundaryEndpointsWalkCost s q e1 n (V.erase t) x.1 else 0) ≤
          3 + (if x.1 ∈ V ∧ x.1 ≠ s then Lp s q (V.erase t) x.1 t else 0) * X +
            (if x.1 ∈ V ∧ x.1 ≠ s then Mp s q (V.erase t) x.1 t else 0) * Y := by
        intro x hx
        split_ifs with hc
        · have := ih _ _ _ (wi_step hI hx hc.1 hc.2) (by simp) (q_ne hI) ⟨x.2, back_mem hx⟩
          have hcard : (V.erase t).card + 3 ≤ V.card + 3 := by
            have := Finset.card_erase_le (s := V) (a := t); omega
          have hpm : ((V.erase t).card + 3) ^ 4 ≤ (V.card + 3) ^ 4 := Nat.pow_le_pow_left hcard 4
          have h1 : Lp s q (V.erase t) x.1 t * (5000 * ((V.erase t).card + 3) ^ 4) ≤
              Lp s q (V.erase t) x.1 t * X := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hpm)
          have h2 : Mp s q (V.erase t) x.1 t * (50 * ((V.erase t).card + 3) ^ 4) ≤
              Mp s q (V.erase t) x.1 t * Y := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hpm)
          omega
        · omega
      have hpot : ((nbrsL t).map fun x =>
          if x.1 ∈ V ∧ x.1 ≠ s then Lp s q (V.erase t) x.1 t else 0).sum ≤ Lp s q V t p ∧
          1 + ((nbrsL t).map fun x =>
            if x.1 ∈ V ∧ x.1 ≠ s then Mp s q (V.erase t) x.1 t else 0).sum ≤ Mp s q V t p := by
        by_cases hr : pidx s q t < 7
        · have hse := ptAt_pidx ha hr
          have hL : Lp s q V t p = ringL s q V (pidx s q t) := by
            unfold Lp; rw [ite_eq_right h2, ite_eq_right hst, ite_eq_left hr]
          have hM : Mp s q V t p = ringM s q V (pidx s q t) := by
            unfold Mp; rw [ite_eq_right h2, ite_eq_right hst, ite_eq_left hr]
          rw [hL, hM]
          have := ring_step (U := V) ha hI.qV hr
          rw [hse] at this
          exact this
        · have hop : Opp s q t p := by
            by_contra hno
            apply hst
            have hfar : isFar s t = true := by
              by_contra hf
              have hnf : ¬ Far s t := fun h => hf (isFar_iff.2 h)
              unfold Far at hnf; push Not at hnf
              exact hr (close1_ring ha hnf.2 hI.st.symm (q_ne hI))
            simp [stopB, hfar, phantomsOpposed, hno]
          have hL : Lp s q V t p = 13 := by
            unfold Lp; rw [ite_eq_right h2, ite_eq_right hst, ite_eq_right hr]
          have hM : Mp s q V t p = 21 := by
            unfold Mp; rw [ite_eq_right h2, ite_eq_right hst, ite_eq_right hr]
          rw [hL, hM]
          exact opp_step ha hI.qV hpV hop
      obtain ⟨hpL, hpM⟩ := hpot
      have hs := lsum_split (nbrsL t) _ _ _ X Y hchild
      have hl : (nbrsL t).length = 4 := rfl
      rw [hl] at hs
      have hL' := Nat.mul_le_mul_right X hpL
      have hM' := Nat.mul_le_mul_right Y hpM
      rw [Nat.add_mul, one_mul] at hM'
      omega
    rcases hf : (nbrsL t).find? (isUsablePhantom V s q t) with _ | x
    · have := hkids (fun h => by obtain ⟨_, x, hx⟩ := h; rw [hf] at hx; cases hx)
      simp only
      omega
    · simp only
      by_cases hfar : isFar t s = true
      · rw [ite_eq_left hfar]
        have hfin := fin_le hI hf hfar
        have hL1 : 1 ≤ Lp s q V t p := by
          unfold Lp; rw [ite_eq_right h2]
          split_ifs with h3 h4
          · omega
          · exfalso
            have hc := ring_close1 ha h4
            rcases isFar_iff.1 hfar with h | h
            · exact hI.st h.symm
            · exact h ⟨by rw [abs_sub_comm]; exact hc.1, by rw [abs_sub_comm]; exact hc.2⟩
          · omega
        have hM1 := Mp_pos (w := s) (t := q) V t p
        have k1 := Nat.mul_le_mul_right X hL1
        have k2 := Nat.mul_le_mul_right Y hM1
        omega
      · rw [ite_eq_right hfar]
        have := hkids (fun h => hfar h.1)
        omega

-- **From the start**: the first step has no deleted neighbour, so up to 4 children of
-- potential at most 13.
--
theorem boundaryEndpointsWalkCost_start {V : Finset Pt} {t : Pt} (hI : WI V s q e1 t) (n : ℕ) :
    boundaryEndpointsWalkCost s q e1 n V t ≤ 264250 * (V.card + 3) ^ 4 := by
  set P := (V.card + 3) ^ 4 with hP
  have am : V.card + 3 ≤ P := Nat.le_self_pow (by omega) _
  cases n with
  | zero => simp only [boundaryEndpointsWalkCost]; omega
  | succ n =>
    have hkids : ((nbrsL t).map fun x =>
        3 + if x.1 ∈ V ∧ x.1 ≠ s then boundaryEndpointsWalkCost s q e1 n (V.erase t) x.1 else 0).sum ≤
        4 * (3 + 13 * (5000 * P) + 21 * (50 * P)) := by
      have := lsum_le (nbrsL t) (fun x =>
        3 + if x.1 ∈ V ∧ x.1 ≠ s then boundaryEndpointsWalkCost s q e1 n (V.erase t) x.1 else 0)
        (3 + 13 * (5000 * P) + 21 * (50 * P)) (by
          intro x hx
          split_ifs with hc
          · have h := boundaryEndpointsWalkCost_pot n _ _ _ (wi_step hI hx hc.1 hc.2) (by simp) (q_ne hI)
              ⟨x.2, back_mem hx⟩
            have hcard : (V.erase t).card + 3 ≤ V.card + 3 := by
              have := Finset.card_erase_le (s := V) (a := t); omega
            have hpm : ((V.erase t).card + 3) ^ 4 ≤ P := Nat.pow_le_pow_left hcard 4
            have l1 := Lp_le13 (w := s) (t := q) (V.erase t) x.1 t
            have l2 := Mp_le21 (w := s) (t := q) (V.erase t) x.1 t
            have k1 : Lp s q (V.erase t) x.1 t * (5000 * ((V.erase t).card + 3) ^ 4) ≤
                13 * (5000 * P) := Nat.mul_le_mul l1 (Nat.mul_le_mul_left _ hpm)
            have k2 : Mp s q (V.erase t) x.1 t * (50 * ((V.erase t).card + 3) ^ 4) ≤
                21 * (50 * P) := Nat.mul_le_mul l2 (Nat.mul_le_mul_left _ hpm)
            omega
          · omega)
      have hl : (nbrsL t).length = 4 := rfl
      rw [hl] at this
      exact this
    simp only [boundaryEndpointsWalkCost]
    by_cases h2 : V.card ≤ 2
    · rw [ite_eq_left h2]; omega
    rw [ite_eq_right h2]
    rcases hf : (nbrsL t).find? (isUsablePhantom V s q t) with _ | x
    · simp only; omega
    · simp only
      by_cases hfar : isFar t s = true
      · rw [ite_eq_left hfar]; have := fin_le hI hf hfar; omega
      · rw [ite_eq_right hfar]; omega

end cost

section costA

variable {V : Finset Pt} {s t : Pt}

theorem boundaryEndpointsCost_le (hs : Solid V) (hst : s ≠ t) (hsV : s ∈ V) (htV : t ∈ V)
    (hms : ∃ m, m ∉ V ∧ |m.1 - s.1| ≤ 1 ∧ |m.2 - s.2| ≤ 1)
    (hmt : ∃ m, m ∉ V ∧ |m.1 - t.1| ≤ 1 ∧ |m.2 - t.2| ≤ 1) :
    boundaryEndpointsCost V s t ≤ 1060000 * (V.card + 3) ^ 4 := by
  set P := (V.card + 3) ^ 4 with hP
  have am : V.card + 3 ≤ P := Nat.le_self_pow (by omega) _
  unfold boundaryEndpointsCost
  split_ifs with h2
  · omega
  rcases hf : (nbrsL s).find? (fun x => decide (x.1 ∉ V)) with _ | x
  · try simp only [hf]
    obtain ⟨m, hm, hm1, hm2⟩ := hms
    have hsol := solid_erase hsV hs hm hm1 hm2
    have hrec : ∀ x ∈ nbrsL s,
        3 + (if x.1 ∈ V ∧ x.1 ≠ t then boundaryEndpointsWalkCost x.1 s x.2 12 (V.erase s) t else 0) ≤
          3 + 264250 * P := by
      intro x hx
      split_ifs with hc
      · have hends := nbrsL_ends hx
        have hI : WI (V.erase s) x.1 s x.2 t :=
          ⟨hsol, Finset.mem_erase.2 ⟨(edge_ne hends).symm, hc.1⟩,
            Finset.mem_erase.2 ⟨Ne.symm hst, htV⟩, hc.2, by simp,
            by rcases hends with h | h; exacts [Or.inr h, Or.inl h],
            let ⟨m', hm', h1, h2⟩ := hmt; ⟨m', fun h => hm' (Finset.mem_of_mem_erase h), h1, h2⟩⟩
        have := boundaryEndpointsWalkCost_start hI 12
        have hcard : (V.erase s).card + 3 ≤ V.card + 3 := by
          have := Finset.card_erase_le (s := V) (a := s); omega
        have hp4 : ((V.erase s).card + 3) ^ 4 ≤ P := Nat.pow_le_pow_left hcard 4
        omega
      · omega
    have hs := lsum_le (nbrsL s)
      (fun x => 3 + if x.1 ∈ V ∧ x.1 ≠ t then boundaryEndpointsWalkCost x.1 s x.2 12 (V.erase s) t else 0)
      (3 + 264250 * P) hrec
    have hl : (nbrsL s).length = 4 := rfl
    rw [hl] at hs
    omega
  · try simp only [hf]
    have hm := List.mem_of_find?_eq_some hf
    have hp := List.find?_some hf
    simp only [decide_eq_true_eq] at hp
    have hI : WI V s x.1 x.2 t := ⟨hs, hsV, htV, hst, hp, nbrsL_ends hm, hmt⟩
    have := boundaryEndpointsWalkCost_start hI 12
    omega

-- **Two boundary endpoints, decided in polynomial time.** For solid `V` and `s ≠ t` in `V`, each
-- with a missing king neighbour, `boundaryEndpoints` answers `true` exactly when `V` has a Hamiltonian
-- `s`–`t` path, within `1 060 000 (|V| + 3)⁴` steps.
--
theorem boundaryEndpoints_main (hs : Solid V) (hst : s ≠ t) (hsV : s ∈ V) (htV : t ∈ V)
    (hms : ∃ m, m ∉ V ∧ |m.1 - s.1| ≤ 1 ∧ |m.2 - s.2| ≤ 1)
    (hmt : ∃ m, m ∉ V ∧ |m.1 - t.1| ≤ 1 ∧ |m.2 - t.2| ≤ 1) :
    (boundaryEndpoints V s t = true ↔ ∃ H, IsFactor V (dST s t) H ∧ ncomp V H = 1) ∧
      boundaryEndpointsCost V s t ≤ 1060000 * (V.card + 3) ^ 4 :=
  ⟨boundaryEndpoints_correct hs hst hsV htV hms hmt, boundaryEndpointsCost_le hs hst hsV htV hms hmt⟩

end costA

end HP

end SolidGridHam
