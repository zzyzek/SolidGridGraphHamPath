/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
import ULHC.HP.Sheffield.SheffCost

/-!
# Dangling `s`, `t` on the boundary

`hpB V s t`: if a lattice neighbour of `t` is missing, run `hpSheffC` with it as the phantom;
otherwise try deleting `t` towards each neighbour `w ≠ s` (`hp_delete`), with `t` as the phantom of
`V.erase t`. Correct when `t` has a missing king neighbour, and polynomial.
-/

namespace ULHC

namespace HP

open Finset Classical

def nbrsL (t : Pt) : List (Pt × Edge) :=
  [((t.1 + 1, t.2), eR t), ((t.1 - 1, t.2), eL t), ((t.1, t.2 + 1), eU t), ((t.1, t.2 - 1), eD t)]

lemma nbrsL_ends {t : Pt} {x : Pt × Edge} (hx : x ∈ nbrsL t) :
    (x.2.p = t ∧ x.2.q = x.1) ∨ (x.2.p = x.1 ∧ x.2.q = t) := by
  obtain ⟨a, b⟩ := t
  simp only [nbrsL, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl <;> simp [eR, eL, eU, eD, Edge.q]

lemma mem_nbrsL {t w : Pt} {ew : Edge} (h : (ew.p = t ∧ ew.q = w) ∨ (ew.p = w ∧ ew.q = t)) :
    (w, ew) ∈ nbrsL t := by
  obtain ⟨d, ⟨z1, z2⟩⟩ := ew
  obtain ⟨a, b⟩ := t
  obtain ⟨u, v⟩ := w
  cases d <;> simp only [Edge.q, Prod.mk.injEq] at h <;>
    simp only [nbrsL, eR, eL, eU, eD, List.mem_cons, Prod.mk.injEq, Edge.mk.injEq,
      List.not_mem_nil, or_false, reduceCtorEq, false_and, true_and, and_false] <;> omega

def hpB (V : Finset Pt) (s t : Pt) : Bool :=
  match (nbrsL t).find? (fun x => decide (x.1 ∉ V)) with
  | some x => hpSheffC V s t x.1 x.2
  | none => (nbrsL t).any fun x => decide (x.1 ≠ s) && hpSheffC (V.erase t) s x.1 t x.2

def hpBCost (V : Finset Pt) (s t : Pt) : ℕ :=
  8 +
    match (nbrsL t).find? (fun x => decide (x.1 ∉ V)) with
    | some x => hpSheffCCost V s t x.1 x.2
    | none => ((nbrsL t).map fun x =>
        2 + if x.1 ≠ s then hpSheffCCost (V.erase t) s x.1 t x.2 else 0).sum

section boundary

variable {V : Finset Pt} {s t : Pt}

lemma edge_ne {t w : Pt} {ew : Edge} (h : (ew.p = t ∧ ew.q = w) ∨ (ew.p = w ∧ ew.q = t)) :
    t ≠ w := by
  have hpq : ew.p ≠ ew.q := by obtain ⟨dir, ⟨x, y⟩⟩ := ew; cases dir <;> simp [Edge.q]
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [← h1, ← h2]; exact hpq
  · rw [← h1, ← h2]; exact Ne.symm hpq

theorem hpB_correct (hs : Solid V) (hst : s ≠ t) (htV : t ∈ V)
    (hsD : ∀ c, IsCell V c → ¬ IsCorner s c) {q : Pt} (hq : q ∉ V) (hqx : |q.1 - t.1| ≤ 1)
    (hqy : |q.2 - t.2| ≤ 1) (h3 : ∃ z ∈ V, z ≠ s ∧ z ≠ t) :
    hpB V s t = true ↔ ∃ H, IsFactor V (dST s t) H ∧ ncomp V H = 1 := by
  have hs' : Solid (V.erase t) := solid_erase htV hs hq hqx hqy
  have hsD' : ∀ c, IsCell (V.erase t) c → ¬ IsCorner s c :=
    fun c hc => hsD c (isCell_mono hc (Finset.erase_subset _ _))
  have htV' : t ∉ V.erase t := Finset.notMem_erase t V
  have swapE : ∀ {w : Pt} {ew : Edge}, ((ew.p = t ∧ ew.q = w) ∨ (ew.p = w ∧ ew.q = t)) →
      Ends ew w t := by
    intro w ew hew
    rcases hew with h | h
    · exact Or.inr h
    · exact Or.inl h
  -- On `V.erase t`, the classical and the decided loops agree.
  have agree : ∀ {w : Pt} {ew : Edge}, ((ew.p = t ∧ ew.q = w) ∨ (ew.p = w ∧ ew.q = t)) →
      w ∈ V → s ≠ w → (hpSheffC (V.erase t) s w t ew = true ↔ hpSheff (V.erase t) s w t ew = true) := by
    intro w ew hew hwV hsw
    have hwV' : w ∈ V.erase t := Finset.mem_erase.2 ⟨(edge_ne hew).symm, hwV⟩
    rw [hpSheffC_correct hs' hsw hwV' htV' (swapE hew) hsD',
      hpSheff_correct' hs' hsw hwV' htV' (swapE hew) hsD']
  unfold hpB
  rcases hf : (nbrsL t).find? (fun x => decide (x.1 ∉ V)) with _ | x
  · simp only [hf]
    have hall : ∀ x ∈ nbrsL t, x.1 ∈ V := by
      intro x hx
      have := List.find?_eq_none.1 hf x hx
      simpa using this
    rw [hp_delete hs hst htV hsD hq hqx hqy h3]
    constructor
    · intro h
      obtain ⟨x, hx, hb⟩ := List.any_eq_true.1 h
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hb
      exact ⟨x.1, x.2, nbrsL_ends hx, hall x hx, hb.1,
        (agree (nbrsL_ends hx) (hall x hx) (Ne.symm hb.1)).1 hb.2⟩
    · rintro ⟨w, ew, hew, hwV, hws, hrun⟩
      apply List.any_eq_true.2
      refine ⟨(w, ew), mem_nbrsL hew, ?_⟩
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨hws, (agree hew hwV (Ne.symm hws)).2 hrun⟩
  · simp only [hf]
    have hm := List.mem_of_find?_eq_some hf
    have hp := List.find?_some hf
    simp only [decide_eq_true_eq] at hp
    exact hpSheffC_correct hs hst htV hp (nbrsL_ends hm) hsD

theorem hpBCost_le (hst : s ≠ t) (htV : t ∈ V) (hsD : ∀ c, IsCell V c → ¬ IsCorner s c) :
    hpBCost V s t ≤ 50000 * (V.card + 2) ^ 6 := by
  have a0 : 1 ≤ (V.card + 2) ^ 6 := Nat.one_le_pow _ _ (by omega)
  unfold hpBCost
  rcases hf : (nbrsL t).find? (fun x => decide (x.1 ∉ V)) with _ | x
  · simp only [hf]
    have hall : ∀ x ∈ nbrsL t, x.1 ∈ V := by
      intro x hx
      have := List.find?_eq_none.1 hf x hx
      simpa using this
    have hsD' : ∀ c, IsCell (V.erase t) c → ¬ IsCorner s c :=
      fun c hc => hsD c (isCell_mono hc (Finset.erase_subset _ _))
    have hcard : (V.erase t).card + 2 ≤ V.card + 2 := by
      have := Finset.card_erase_le (s := V) (a := t); omega
    have hpow : ((V.erase t).card + 2) ^ 6 ≤ (V.card + 2) ^ 6 := Nat.pow_le_pow_left hcard 6
    have hs := lsum_le (nbrsL t)
      (fun x => 2 + if x.1 ≠ s then hpSheffCCost (V.erase t) s x.1 t x.2 else 0)
      (2 + 10000 * (V.card + 2) ^ 6) (fun x hx => by
        split_ifs with hxs
        · have hew := nbrsL_ends hx
          have hwV' : x.1 ∈ V.erase t := Finset.mem_erase.2 ⟨(edge_ne hew).symm, hall x hx⟩
          have := hpSheffCCost_le (Ne.symm hxs) hwV' (Finset.notMem_erase t V)
            (by rcases hew with h | h; exacts [Or.inr h, Or.inl h]) hsD'
          omega
        · omega)
    have hl : (nbrsL t).length = 4 := rfl
    rw [hl] at hs
    omega
  · simp only [hf]
    have hm := List.mem_of_find?_eq_some hf
    have hp := List.find?_some hf
    simp only [decide_eq_true_eq] at hp
    have := hpSheffCCost_le hst htV hp (nbrsL_ends hm) hsD
    omega

-- **Dangling `s`, `t` with a missing king neighbour: decided in polynomial time.**
--
theorem hpB_main (hs : Solid V) (hst : s ≠ t) (htV : t ∈ V)
    (hsD : ∀ c, IsCell V c → ¬ IsCorner s c) {q : Pt} (hq : q ∉ V) (hqx : |q.1 - t.1| ≤ 1)
    (hqy : |q.2 - t.2| ≤ 1) (h3 : ∃ z ∈ V, z ≠ s ∧ z ≠ t) :
    (hpB V s t = true ↔ ∃ H, IsFactor V (dST s t) H ∧ ncomp V H = 1) ∧
      hpBCost V s t ≤ 50000 * (V.card + 2) ^ 6 :=
  ⟨hpB_correct hs hst htV hsD hq hqx hqy h3, hpBCost_le hst htV hsD⟩

end boundary

end HP

end ULHC
