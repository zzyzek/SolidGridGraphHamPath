/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
module

public import SolidGridHam.Cycle.TwoFactor
public import SolidGridHam.Algorithm

@[expose] public section

/-!
# Computable classes

`ccls V F x` computes the class of `x` by `|V|` rounds of breadth-first search along `F`;
it equals `cls V F x` (`ccls_eq`). `cncomp` computes the number of components.

Cost: `|V|` rounds, each scanning four edges at every point found so far.
-/

namespace SolidGridHam

open Finset

section comp

variable {V : Finset Pt} {F : Finset Edge}

lemma mem_fnbr {u v : Pt} : v ∈ fnbr F u ↔ ∃ e ∈ F, (e.p = u ∨ e.q = u) ∧ other e u = v := by
  simp [fnbr, TF.mem_inc4]
  constructor
  · rintro ⟨e, ⟨h1, h2⟩, h3⟩; exact ⟨e, h2, h1, h3⟩
  · rintro ⟨e, h2, h1, h3⟩; exact ⟨e, ⟨h1, h2⟩, h3⟩

lemma creach_succ (x : Pt) (k : ℕ) :
    creach F x (k + 1) = creach F x k ∪ (creach F x k).biUnion (fnbr F) := rfl

lemma creach_sub_succ {x : Pt} {k : ℕ} : creach F x k ⊆ creach F x (k + 1) := by
  rw [creach_succ]; exact subset_union_left

lemma creach_mono {x : Pt} {j k : ℕ} (h : j ≤ k) : creach F x j ⊆ creach F x k := by
  induction h with
  | refl => exact Subset.refl _
  | step _ ih => exact ih.trans creach_sub_succ

lemma creach_conn {x : Pt} : ∀ k, ∀ z ∈ creach F x k, Conn F x z := by
  intro k
  induction k with
  | zero => intro z hz; rw [creach, mem_singleton] at hz; rw [hz]; exact Conn.refl F x
  | succ k ih =>
    intro z hz
    rw [creach_succ, mem_union, mem_biUnion] at hz
    rcases hz with hz | ⟨u, hu, hz⟩
    · exact ih z hz
    · obtain ⟨e, he, hi, rfl⟩ := mem_fnbr.1 hz
      exact (ih u hu).trans (Conn.of_adj (adj_other he hi))

lemma creach_sub (hFV : Inside V F) {x : Pt} (hx : x ∈ V) : ∀ k, creach F x k ⊆ V := by
  intro k z hz
  exact conn_mem hFV hx (creach_conn k z hz)

lemma creach_stable {x : Pt} {k : ℕ} (h : creach F x (k + 1) = creach F x k) :
    ∀ j, k ≤ j → creach F x j = creach F x k := by
  intro j hj
  induction hj with
  | refl => rfl
  | step _ ih => rw [creach_succ, ih, ← creach_succ, h]

lemma creach_fix (hFV : Inside V F) {x : Pt} (hx : x ∈ V) :
    ∃ k ≤ V.card, creach F x (k + 1) = creach F x k := by
  by_contra hn
  push Not at hn
  have hgrow : ∀ n, n ≤ V.card + 1 → n + 1 ≤ (creach F x n).card := by
    intro n
    induction n with
    | zero => intro _; simp [creach]
    | succ n ih =>
      intro hn1
      have hss : creach F x n ⊂ creach F x (n + 1) :=
        ssubset_of_subset_of_ne creach_sub_succ (hn n (by omega)).symm
      have := card_lt_card hss
      have := ih (by omega)
      omega
  have h1 := hgrow (V.card + 1) le_rfl
  have h2 := card_le_card (creach_sub hFV hx (V.card + 1))
  omega

-- **Computed classes are classes.**
--
theorem ccls_eq (hFV : Inside V F) {x : Pt} (hx : x ∈ V) : ccls V F x = cls V F x := by
  classical
  obtain ⟨k, hk, hfix⟩ := creach_fix hFV hx
  have hst : creach F x V.card = creach F x k := creach_stable hfix _ hk
  have closed : ∀ u ∈ creach F x k, ∀ v, Adj F u v → v ∈ creach F x k := by
    intro u hu v huv
    obtain ⟨e, he, hi, _, rfl⟩ := adj_inc huv
    rw [← hfix, creach_succ, mem_union, mem_biUnion]
    exact Or.inr ⟨u, hu, mem_fnbr.2 ⟨e, he, hi, rfl⟩⟩
  ext z
  unfold ccls cls
  rw [mem_filter, hst]
  constructor
  · intro hz
    exact ⟨creach_sub hFV hx k hz, creach_conn k z hz⟩
  · rintro ⟨-, hc⟩
    induction hc with
    | refl => exact creach_mono (Nat.zero_le k) (by simp [creach])
    | tail _ hbc ih => exact closed _ ih _ hbc

theorem cncomp_eq (hFV : Inside V F) : cncomp V F = ncomp V F := by
  classical
  unfold cncomp ncomp
  congr 1
  exact image_congr (fun x hx => ccls_eq hFV hx)

end comp

end SolidGridHam
