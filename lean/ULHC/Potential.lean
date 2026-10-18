/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
import ULHC.Grid

/-!
# Potentials from edge weights

Given integer weights `w` on edges, supported on a finite set `E`, the *row-sum
potential* of a cell `c` is the sum of `w` over the vertical edges in `c`'s row that lie
at or left of `c`'s left side. Crossing a vertical edge rightward changes the potential by
its weight, by construction.

If the weights are *balanced* at every lattice point (the two ways around the point from
its lower-left cell to its upper-right cell agree), then crossing a horizontal edge upward
also changes the potential by its weight. This is the discrete fact behind both the
region parity `R(S)` and the factor-pair potential `D`.
-/

namespace ULHC

open Finset

-- Vertical edges in the row of cell `c`, at or left of `c`'s left side.
--
def RowSel (c : Pt) (e : Edge) : Prop := e.d = .v ∧ e.p.2 = c.2 ∧ e.p.1 ≤ c.1

instance (c : Pt) : DecidablePred (RowSel c) := by
  intro e; unfold RowSel; infer_instance

def pot (E : Finset Edge) (w : Edge → ℤ) (c : Pt) : ℤ :=
  ∑ e ∈ E.filter (RowSel c), w e

-- `w` vanishes off `E`.
--
def Supp (E : Finset Edge) (w : Edge → ℤ) : Prop := ∀ e, e ∉ E → w e = 0

-- Balance at every lattice point `p`: going from the cell below-left of `p` to the cell
-- above-right of `p` through the cell below-right, or through the cell above-left,
-- accumulates the same weight.
--
def Balanced (w : Edge → ℤ) : Prop := ∀ p, w (eD p) + w (eR p) = w (eL p) + w (eU p)

variable {E : Finset Edge} {w : Edge → ℤ}

lemma pot_eq_sum_ite (c : Pt) :
    pot E w c = ∑ e ∈ E, if RowSel c e then w e else 0 := by
  unfold pot; rw [Finset.sum_filter]

-- Crossing the left side of `c` rightward adds its weight.
--
lemma pot_jump_v (hS : Supp E w) (c : Pt) :
    pot E w c - pot E w (c.1 - 1, c.2) = w ⟨.v, c⟩ := by
  rw [pot_eq_sum_ite, pot_eq_sum_ite, ← Finset.sum_sub_distrib]
  have key : ∀ e ∈ E,
      ((if RowSel c e then w e else 0) - if RowSel (c.1 - 1, c.2) e then w e else 0)
        = if e = ⟨.v, c⟩ then w e else 0 := by
    intro e _
    obtain ⟨d, a, b⟩ := e
    obtain ⟨x, y⟩ := c
    cases d <;> simp only [RowSel, Edge.mk.injEq, Prod.mk.injEq] <;> split_ifs <;>
      simp_all <;> omega
  rw [Finset.sum_congr rfl key, Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · exact (hS _ h).symm

-- Every edge of `E` lies strictly right of some column `B`.
--
lemma exists_left_bound (E : Finset Edge) : ∃ B : ℤ, ∀ e ∈ E, B < e.p.1 := by
  refine ⟨-(∑ e ∈ E, |e.p.1|) - 1, fun e he => ?_⟩
  have h1 : |e.p.1| ≤ ∑ e ∈ E, |e.p.1| :=
    Finset.single_le_sum (f := fun e : Edge => |e.p.1|) (fun _ _ => abs_nonneg _) he
  have h2 := neg_abs_le e.p.1
  linarith

lemma pot_eq_zero_of_left {B : ℤ} (hB : ∀ e ∈ E, B < e.p.1) (c : Pt) (hc : c.1 ≤ B) :
    pot E w c = 0 := by
  unfold pot
  rw [Finset.filter_false_of_mem, Finset.sum_empty]
  intro e he hsel
  have := hB e he
  have := hsel.2.2
  omega

-- Crossing the bottom side of `c` upward adds its weight, given balance.
--
lemma pot_jump_h (hS : Supp E w) (hbal : Balanced w) (c : Pt) :
    pot E w c - pot E w (c.1, c.2 - 1) = w ⟨.h, c⟩ := by
  obtain ⟨B, hB⟩ := exists_left_bound E
  obtain ⟨x, y⟩ := c
  let f : ℤ → ℤ := fun x => pot E w (x, y) - pot E w (x, y - 1) - w ⟨.h, (x, y)⟩
  have base : ∀ x, x ≤ B → f x = 0 := by
    intro x hx
    have h1 := pot_eq_zero_of_left (w := w) hB (x, y) hx
    have h2 := pot_eq_zero_of_left (w := w) hB (x, y - 1) hx
    have h3 : w ⟨.h, (x, y)⟩ = 0 := by
      apply hS
      intro hm
      have := hB _ hm
      simp at this
      omega
    simp only [f, h1, h2, h3]; ring
  have step : ∀ x, f x = f (x - 1) := by
    intro x
    have j1 := pot_jump_v hS (x, y)
    have j2 := pot_jump_v hS (x, y - 1)
    have hb := hbal (x, y)
    simp only [eD, eR, eL, eU] at hb
    simp only at j1 j2
    simp only [f]
    linarith
  have up : ∀ x, B ≤ x → f x = 0 := by
    intro x hx
    induction x, hx using Int.leInduction with
    | base => exact base B le_rfl
    | succ n _ ih =>
      rw [step (n + 1)]
      simp only [add_sub_cancel_right]
      exact ih
  have all : ∀ x, f x = 0 := by
    intro x
    rcases le_total x B with hx | hx
    · exact base x hx
    · exact up x hx
  have := all x
  simp only [f] at this
  simp only
  linarith

-- Crossing any edge from its low cell to its high cell adds its weight.
--
lemma pot_jump (hS : Supp E w) (hbal : Balanced w) (e : Edge) :
    pot E w e.hi - pot E w e.lo = w e := by
  obtain ⟨d, p⟩ := e
  cases d
  · exact pot_jump_h hS hbal p
  · exact pot_jump_v hS p

-- Enlarging the support set does not change the potential.
--
lemma pot_mono_supp {E E' : Finset Edge} (hsub : E ⊆ E') (hS : Supp E w) (c : Pt) :
    pot E w c = pot E' w c := by
  rw [pot_eq_sum_ite, pot_eq_sum_ite]
  apply Finset.sum_subset hsub
  intro e _ he
  rw [hS e he]; simp

-- The potential is additive in the weights.
--
lemma pot_add (E : Finset Edge) (w₁ w₂ : Edge → ℤ) (c : Pt) :
    pot E (fun e => w₁ e + w₂ e) c = pot E w₁ c + pot E w₂ c := by
  unfold pot; rw [Finset.sum_add_distrib]

lemma pot_sub (E : Finset Edge) (w₁ w₂ : Edge → ℤ) (c : Pt) :
    pot E (fun e => w₁ e - w₂ e) c = pot E w₁ c - pot E w₂ c := by
  unfold pot; rw [Finset.sum_sub_distrib]

end ULHC
