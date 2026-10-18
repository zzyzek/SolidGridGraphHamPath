/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
import ULHC.HP.Sheffield.SheffEndpoints

/-!
# Exposed endpoints (docs/ENDPOINTS_GENERAL.md, route A0)

An endpoint `s` is *exposed* when it has a missing neighbour `q` whose other three neighbours
are missing too. Adding `q` as a pendant vertex keeps the set solid, makes `q` a corner of no cell,
and a Hamiltonian `s`–`t` path of `V` is a Hamiltonian `q`–`t` path of `V ∪ {q}` with its first
edge removed. So `hpD` on `V ∪ {q}` decides the problem whenever its coverage test passes there.

`hpX` tries, in order: `hpD` on `V`; an exposed `s`; an exposed `t`. `hpX_main`: when the
coverage test `covX` passes, `hpX` is correct and polynomial.
-/

namespace ULHC

namespace HP

open Finset Classical

lemma nbrsL_uniq {q w : Pt} {e e' : Edge} (h1 : (w, e) ∈ nbrsL q) (h2 : (w, e') ∈ nbrsL q) :
    e = e' := by
  obtain ⟨a, b⟩ := q
  simp only [nbrsL, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at h1 h2
  rcases h1 with ⟨h, rfl⟩ | ⟨h, rfl⟩ | ⟨h, rfl⟩ | ⟨h, rfl⟩ <;>
    rcases h2 with ⟨h', rfl⟩ | ⟨h', rfl⟩ | ⟨h', rfl⟩ | ⟨h', rfl⟩ <;>
    first | rfl | (rw [h] at h'; simp [Prod.ext_iff] at h'; omega) | (rw [h] at h'; simp [Prod.ext_iff] at h')

-- An exposed neighbour of `s`: missing, with all its other neighbours missing.
--
def exposedB (V : Finset Pt) (s : Pt) : Option (Pt × Edge) :=
  (nbrsL s).find? fun x =>
    decide (x.1 ∉ V) && (nbrsL x.1).all fun y => decide (y.1 = s) || decide (y.1 ∉ V)

lemma exposedB_some {V : Finset Pt} {s : Pt} {x : Pt × Edge} (h : exposedB V s = some x) :
    x.1 ∉ V ∧ ((x.2.p = s ∧ x.2.q = x.1) ∨ (x.2.p = x.1 ∧ x.2.q = s)) ∧
      ∀ e : Edge, (e.p = x.1 ∨ e.q = x.1) → e.p ∈ insert x.1 V → e.q ∈ insert x.1 V →
        e = x.2 := by
  have hm := List.mem_of_find?_eq_some h
  have hp := List.find?_some h
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, Bool.or_eq_true] at hp
  obtain ⟨hq, hall⟩ := hp
  have hends := nbrsL_ends hm
  refine ⟨hq, hends, fun e he h1 h2 => ?_⟩
  -- the other end `w` of `e`
  obtain ⟨w, hew⟩ : ∃ w, (e.p = x.1 ∧ e.q = w) ∨ (e.p = w ∧ e.q = x.1) := by
    rcases he with h | h
    · exact ⟨e.q, Or.inl ⟨h, rfl⟩⟩
    · exact ⟨e.p, Or.inr ⟨rfl, h⟩⟩
  have hwq : w ≠ x.1 := (edge_ne hew).symm
  have hwV : w ∈ V := by
    rcases hew with ⟨_, h⟩ | ⟨h, _⟩
    · rw [h] at h2; exact (Finset.mem_insert.1 h2).resolve_left hwq
    · rw [h] at h1; exact (Finset.mem_insert.1 h1).resolve_left hwq
  have hmw := mem_nbrsL hew
  have hws : w = s := by
    rcases hall _ hmw with h | h
    · exact h
    · exact absurd hwV h
  subst hws
  have hms : (w, x.2) ∈ nbrsL x.1 := by
    apply mem_nbrsL
    rcases hends with h | h
    · exact Or.inr h
    · exact Or.inl h
  exact nbrsL_uniq hmw hms

-- `hpD`'s coverage test.
--
def covB (V : Finset Pt) (s t : Pt) : Bool :=
  (danglingB V s && bdB V t) || (danglingB V t && bdB V s)

def sBr (V : Finset Pt) (s t : Pt) : Option Bool :=
  match exposedB V s with
  | some x => if covB (insert x.1 V) x.1 t then some (hpD (insert x.1 V) x.1 t) else none
  | none => none

def tBr (V : Finset Pt) (s t : Pt) : Option Bool :=
  match exposedB V t with
  | some x => if covB (insert x.1 V) s x.1 then some (hpD (insert x.1 V) s x.1) else none
  | none => none

def covX (V : Finset Pt) (s t : Pt) : Bool :=
  covB V s t || (sBr V s t).isSome || (tBr V s t).isSome

def hpX (V : Finset Pt) (s t : Pt) : Bool :=
  if covB V s t then hpD V s t else (sBr V s t).getD ((tBr V s t).getD false)

def hpXCost (V : Finset Pt) (s t : Pt) : ℕ :=
  400 +
    if covB V s t then hpDCost V s t
    else
      (match exposedB V s with
        | some x => if covB (insert x.1 V) x.1 t then hpDCost (insert x.1 V) x.1 t else 0
        | none => 0) +
      (match exposedB V t with
        | some x => if covB (insert x.1 V) s x.1 then hpDCost (insert x.1 V) s x.1 else 0
        | none => 0)

section exposed

variable {V : Finset Pt} {s t : Pt}

lemma covB_iff : covB V s t = true ↔
    (danglingB V s = true ∧ bdB V t = true) ∨ (danglingB V t = true ∧ bdB V s = true) := by
  unfold covB; simp

-- **The pendant reduction at `s`.**
--
lemma hp_pendS (hst : s ≠ t) (hsV : s ∈ V) (_htV : t ∈ V) {x : Pt × Edge}
    (hx : exposedB V s = some x) :
    (∃ H, IsFactor V (dST s t) H ∧ ncomp V H = 1) ↔
      ∃ H, IsFactor (insert x.1 V) (dST x.1 t) H ∧ ncomp (insert x.1 V) H = 1 := by
  obtain ⟨hq, hends, hpe⟩ := exposedB_some hx
  have he0 : (x.2.p = s ∧ x.2.q = x.1) ∨ (x.2.p = x.1 ∧ x.2.q = s) := hends
  rw [dST_comm, dST_comm x.1 t]
  constructor
  · rintro ⟨H, hH, hHam⟩
    exact ⟨_, (pendant_up hq hsV he0 hpe (Ne.symm hst) hH hHam).1,
      (pendant_up hq hsV he0 hpe (Ne.symm hst) hH hHam).2⟩
  · rintro ⟨H, hH, hHam⟩
    exact ⟨_, (pendant_down hq hsV he0 hpe (Ne.symm hst) hH hHam).1,
      (pendant_down hq hsV he0 hpe (Ne.symm hst) hH hHam).2⟩

-- **The pendant reduction at `t`.**
--
lemma hp_pendT (hst : s ≠ t) (htV : t ∈ V) {x : Pt × Edge} (hx : exposedB V t = some x) :
    (∃ H, IsFactor V (dST s t) H ∧ ncomp V H = 1) ↔
      ∃ H, IsFactor (insert x.1 V) (dST s x.1) H ∧ ncomp (insert x.1 V) H = 1 := by
  obtain ⟨hq, hends, hpe⟩ := exposedB_some hx
  constructor
  · rintro ⟨H, hH, hHam⟩
    exact ⟨_, (pendant_up hq htV hends hpe hst hH hHam).1, (pendant_up hq htV hends hpe hst hH hHam).2⟩
  · rintro ⟨H, hH, hHam⟩
    exact ⟨_, (pendant_down hq htV hends hpe hst hH hHam).1,
      (pendant_down hq htV hends hpe hst hH hHam).2⟩

lemma card_insert_ge {q : Pt} (hq : q ∉ V) (h2 : 2 ≤ V.card) : 3 ≤ (insert q V).card := by
  rw [Finset.card_insert_of_notMem hq]; omega

lemma sBr_spec (hs : Solid V) (hst : s ≠ t) (hsV : s ∈ V) (htV : t ∈ V) (h2 : 2 ≤ V.card)
    {b : Bool} (hb : sBr V s t = some b) :
    (b = true ↔ ∃ H, IsFactor V (dST s t) H ∧ ncomp V H = 1) ∧
      (match exposedB V s with
        | some x => if covB (insert x.1 V) x.1 t then hpDCost (insert x.1 V) x.1 t else 0
        | none => 0) ≤ 60000 * (V.card + 3) ^ 6 := by
  unfold sBr at hb
  rcases hx : exposedB V s with _ | x
  · rw [hx] at hb; simp at hb
  rw [hx] at hb
  simp only at hb ⊢
  split_ifs at hb ⊢ with hc
  simp only [Option.some.injEq] at hb
  subst hb
  obtain ⟨hq, hends, hpe⟩ := exposedB_some hx
  have hs' := pendant_solid hq hsV hends hpe hs
  have hqt : x.1 ≠ t := fun h => hq (h ▸ htV)
  obtain ⟨c1, c2⟩ := hpD_main hs' hqt (Finset.mem_insert_self _ _) (Finset.mem_insert_of_mem htV)
    (card_insert_ge hq h2) (covB_iff.1 hc)
  rw [Finset.card_insert_of_notMem hq] at c2
  refine ⟨c1.trans (hp_pendS hst hsV htV hx).symm, ?_⟩
  rw [show V.card + 1 + 2 = V.card + 3 by omega] at c2
  exact c2

lemma tBr_spec (hs : Solid V) (hst : s ≠ t) (hsV : s ∈ V) (htV : t ∈ V) (h2 : 2 ≤ V.card)
    {b : Bool} (hb : tBr V s t = some b) :
    (b = true ↔ ∃ H, IsFactor V (dST s t) H ∧ ncomp V H = 1) ∧
      (match exposedB V t with
        | some x => if covB (insert x.1 V) s x.1 then hpDCost (insert x.1 V) s x.1 else 0
        | none => 0) ≤ 60000 * (V.card + 3) ^ 6 := by
  unfold tBr at hb
  rcases hx : exposedB V t with _ | x
  · rw [hx] at hb; simp at hb
  rw [hx] at hb
  simp only at hb ⊢
  split_ifs at hb ⊢ with hc
  simp only [Option.some.injEq] at hb
  subst hb
  obtain ⟨hq, hends, hpe⟩ := exposedB_some hx
  have hs' := pendant_solid hq htV hends hpe hs
  have hsq : s ≠ x.1 := fun h => hq (h ▸ hsV)
  obtain ⟨c1, c2⟩ := hpD_main hs' hsq (Finset.mem_insert_of_mem hsV) (Finset.mem_insert_self _ _)
    (card_insert_ge hq h2) (covB_iff.1 hc)
  rw [Finset.card_insert_of_notMem hq] at c2
  refine ⟨c1.trans (hp_pendT hst htV hx).symm, ?_⟩
  rw [show V.card + 1 + 2 = V.card + 3 by omega] at c2
  exact c2

lemma branch_cost_s (hs : Solid V) (hst : s ≠ t) (hsV : s ∈ V) (htV : t ∈ V) (h2 : 2 ≤ V.card) :
    (match exposedB V s with
      | some x => if covB (insert x.1 V) x.1 t then hpDCost (insert x.1 V) x.1 t else 0
      | none => 0) ≤ 60000 * (V.card + 3) ^ 6 := by
  cases hb : sBr V s t with
  | some b => exact (sBr_spec hs hst hsV htV h2 hb).2
  | none =>
    unfold sBr at hb
    rcases hx : exposedB V s with _ | x
    · simp
    · rw [hx] at hb
      simp only at hb ⊢
      split_ifs at hb ⊢; simp_all

lemma branch_cost_t (hs : Solid V) (hst : s ≠ t) (hsV : s ∈ V) (htV : t ∈ V) (h2 : 2 ≤ V.card) :
    (match exposedB V t with
      | some x => if covB (insert x.1 V) s x.1 then hpDCost (insert x.1 V) s x.1 else 0
      | none => 0) ≤ 60000 * (V.card + 3) ^ 6 := by
  cases hb : tBr V s t with
  | some b => exact (tBr_spec hs hst hsV htV h2 hb).2
  | none =>
    unfold tBr at hb
    rcases hx : exposedB V t with _ | x
    · simp
    · rw [hx] at hb
      simp only at hb ⊢
      split_ifs at hb ⊢; simp_all

-- **Exposed endpoints and the dangling/boundary case, decided in polynomial time.**
--
theorem hpX_main (hs : Solid V) (hst : s ≠ t) (hsV : s ∈ V) (htV : t ∈ V) (h3 : 3 ≤ V.card)
    (hcov : covX V s t = true) :
    (hpX V s t = true ↔ ∃ H, IsFactor V (dST s t) H ∧ ncomp V H = 1) ∧
      hpXCost V s t ≤ 200000 * (V.card + 3) ^ 6 := by
  have h2 : 2 ≤ V.card := by omega
  have hp6 : (V.card + 2) ^ 6 ≤ (V.card + 3) ^ 6 := Nat.pow_le_pow_left (by omega) 6
  have a0 : 1 ≤ (V.card + 3) ^ 6 := Nat.one_le_pow _ _ (by omega)
  unfold hpX hpXCost
  by_cases hc : covB V s t = true
  · obtain ⟨c1, c2⟩ := hpD_main hs hst hsV htV h3 (covB_iff.1 hc)
    simp only [hc, ↓reduceIte]
    exact ⟨c1, by omega⟩
  · simp only [hc, Bool.false_eq_true, ↓reduceIte]
    have cs := branch_cost_s hs hst hsV htV h2
    have ct := branch_cost_t hs hst hsV htV h2
    refine ⟨?_, by omega⟩
    unfold covX at hcov
    simp only [hc, Bool.false_or, Bool.or_eq_true, Option.isSome_iff_exists] at hcov
    rcases hsb : sBr V s t with _ | b
    · simp only [hsb, reduceCtorEq, exists_false, false_or] at hcov
      obtain ⟨b, hb⟩ := hcov
      rw [hb]
      exact (tBr_spec hs hst hsV htV h2 hb).1
    · exact (sBr_spec hs hst hsV htV h2 hsb).1

end exposed

end HP

end ULHC
