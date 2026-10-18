/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
module

public import SolidGridHam.Path.Compat1

@[expose] public section

/-!
# Lemma 4, (C1) for the half bridge (docs/S4_UNDO.md §II.1)

The half bridge's row (branches (b), (c)) avoids every bridge square: its start and inner squares
by `rowAvoid`; its alternating, uncut last square can only be some `A`, and then the square before
it is a bridge square (b) or has a dark lateral at an even index (c).
-/

namespace SolidGridHam

namespace HP

open Finset Classical

section c1half

variable {V : Finset Pt} {H : Finset Edge}

lemma rowAt_move {BS : List Bridge} {g : Bridge} (mf : MoveFacts V H BS g) :
    RowAt V H BS g.q g.a g.r :=
  ⟨mf.2.2.2.2.1, mf.2.2.2.2.2.1, mf.2.1, mf.2.2.1,
    fun b hb j hj he => mf.2.2.2.1 ⟨b, hb, j, hj, he⟩, mf.2.2.2.2.2.2.1, mf.2.2.2.2.2.2.2.1⟩

lemma perp_or {a a' : Side} : (a' = a ∨ a' = a.opp) ∨ (a' = latA a ∨ a' = latB a) := by
  rcases side_cases a a' with h | h | h | h
  · exact Or.inl (Or.inl h)
  · exact Or.inl (Or.inr h)
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)

lemma lat_of_perp {Y : Pt} {a g : Side} (h : g = latA a ∨ g = latB a) :
    sideEdge Y g = lat1 Y a ∨ sideEdge Y g = lat2 Y a := by
  rcases h with rfl | rfl
  · exact Or.inl (lat1_eq Y a).symm
  · exact Or.inr (lat2_eq Y a).symm

lemma perp_symm {a g : Side} (h : g = latA a ∨ g = latB a) : a = latA g ∨ a = latB g := by
  cases a <;> cases g <;> simp_all [latA, latB]

-- The last square of a half-bridge row is alternating: back and front dark (odd row), or
-- laterals dark (even row).
--
lemma last_alt {BS : List Bridge} {g : Bridge} (mf : MoveFacts V H BS g)
    (hdegc : ∀ f, IsCell V f → ∀ z, IsCorner z f → deg H z = 2) :
    (g.r % 2 = 1 → back g.E g.a ∈ H ∧ front g.E g.a ∈ H ∧ lat1 g.E g.a ∉ H ∧ lat2 g.E g.a ∉ H) ∧
    (g.r % 2 = 0 → lat1 g.E g.a ∈ H ∧ lat2 g.E g.a ∈ H ∧ back g.E g.a ∉ H ∧
      front g.E g.a ∉ H) := by
  have two := mf.2.2.2.2.1
  have hb : back g.E g.a = front (cellJ g.q g.a (g.r - 2)) g.a := by
    unfold Bridge.E Bridge.cell; rw [show g.r - 1 = g.r - 2 + 1 by omega, back_cellJ_succ]
  refine ⟨fun ho => ?_, fun he => ?_⟩
  · obtain ⟨⟨_, hl, hf⟩, _⟩ := oddRow_pat mf ho hdegc
    have f1 := hf (g.r - 1) (by omega)
    have f2 := hf (g.r - 2) (by omega)
    obtain ⟨l1, l2⟩ := hl (g.r - 1) (by omega)
    rw [hb]
    unfold Bridge.E Bridge.cell
    exact ⟨f2.2 (by omega), f1.2 (by omega), fun h => by have := l1.1 h; omega,
      fun h => by have := l2.1 h; omega⟩
  · obtain ⟨⟨_, _, hf⟩, lE1, lE2⟩ := evenRow_pat mf he hdegc
    have f1 := hf (g.r - 1) (by omega)
    have f2 := hf (g.r - 2) (by omega)
    refine ⟨lE1, lE2, ?_, ?_⟩
    · rw [hb]; intro h; have := f2.1 h; omega
    · unfold Bridge.E Bridge.cell; intro h; have := f1.1 h; omega

theorem c1_half {BS : List Bridge} {g : Bridge} (mf : MoveFacts V H BS g)
    (hdegc : ∀ f, IsCell V f → ∀ z, IsCorner z f → deg H z = 2)
    (hreg : ∀ b ∈ BS, RegionOK H b ∧ 2 ≤ b.r ∧ b.r % 2 = 0) {b : Bridge} (hb : b ∈ BS)
    {j : ℕ} (hj : j < g.r) {l : ℕ} (hl : l < b.r) : cellJ g.q g.a j ≠ b.cell l := by
  have hrow := rowAt_move mf
  obtain ⟨hR, htwo, hev⟩ := hreg b hb
  rcases (show j ≤ g.r - 2 ∨ j = g.r - 1 by omega) with hj' | rfl
  · exact rowAvoid hrow hdegc hb hR htwo hev hj' hl
  intro he
  have two := hrow.two
  have hun := hrow.uncut (g.r - 1) (by omega) (by omega)
  have hprev : nb (cellJ g.q g.a (g.r - 1)) g.a.opp = cellJ g.q g.a (g.r - 2) := by
    rw [show g.r - 1 = g.r - 2 + 1 by omega, nb_cellJ_opp]
  have prevAvoid := fun l' (hl' : l' < b.r) => rowAvoid hrow hdegc hb hR htwo hev le_rfl hl'
  obtain ⟨lastO, lastE⟩ := last_alt mf hdegc
  have hgE : g.E = cellJ g.q g.a (g.r - 1) := rfl
  rw [hgE, he] at lastO lastE
  rw [he] at hun hprev
  have galt : Alt H (b.cell l) := by
    rcases Nat.mod_two_eq_zero_or_one g.r with h | h
    · obtain ⟨a1, a2, a3, a4⟩ := lastE h; exact alt_of_lats a1 a2 a3 a4
    · obtain ⟨a1, a2, a3, a4⟩ := lastO h; exact alt_of_bf a1 a2 a3 a4
  rcases (show l = 0 ∨ (1 ≤ l ∧ l + 3 ≤ b.r) ∨ l = b.r - 2 ∨ l = b.r - 1 by omega) with
    h | ⟨h1, h2⟩ | h | h
  · subst h; unfold Bridge.cell at hun; rw [cellJ_zero] at hun; exact hun (cutSq_q hR)
  · exact (region_inner hR h1 h2).not_alt galt
  · -- `A` of `b` (`b.r ≥ 4`)
    subst h
    have r4 : 4 ≤ b.r := by
      by_contra hlt
      have : b.r = 2 := by omega
      rw [this] at hun; unfold Bridge.cell at hun; simp only [Nat.sub_self, cellJ_zero] at hun
      exact hun (cutSq_q hR)
    obtain ⟨la1, la2⟩ := hR.lat (b.r - 2) (by omega) (by omega)
    have lA1 : lat1 (b.cell (b.r - 2)) b.a ∉ H := fun h => by have := la1.1 h; omega
    have lA2 : lat2 (b.cell (b.r - 2)) b.a ∉ H := fun h => by have := la2.1 h; omega
    rcases Nat.mod_two_eq_zero_or_one g.r with hpar | hpar
    · -- even row: dark laterals
      obtain ⟨d1, d2, _, _⟩ := lastE hpar
      rcases perp_or (a := b.a) (a' := g.a) with (hga | hga) | hperp
      · rw [hga] at d1; exact lA1 d1
      · rw [hga, lat1_sopp] at d1; exact lA1 d1
      · -- the square before is a side square of `A`, with a dark lateral
        have hrun := (hrow.run hdegc (g.r - 2) le_rfl)
        have hS : g.a.opp = latA b.a ∨ g.a.opp = latB b.a := by
          rcases hperp with h | h <;> rw [h]
          · right; exact latA_opp' b.a
          · left; exact latB_opp' b.a
        have hdark : sideEdge (nb (b.cell (b.r - 2)) g.a.opp) b.a ∈ H := by
          have ho := hR.outer (b.r - 2) (by omega)
          rcases hS with h | h <;> rw [h]
          · have := side_front (b.cell (b.r - 2)) b.a
            unfold front at this; rw [this]; exact ho.1.2 (by omega)
          · have := sideB_front (b.cell (b.r - 2)) b.a
            unfold front at this; rw [this]; exact ho.2.2 (by omega)
        rw [hprev] at hdark
        rcases lat_of_perp (Y := cellJ g.q g.a (g.r - 2)) (perp_symm hperp) with h | h <;>
          rw [h] at hdark
        · have := hrun.1.1 hdark; omega
        · have := hrun.2.1.1 hdark; omega
    · -- odd row: dark back and front
      obtain ⟨_, d2, _, _⟩ := lastO hpar
      rcases perp_or (a := b.a) (a' := g.a) with (hga | hga) | hperp
      · -- same direction: the square before is the bridge square before `A`
        have ho : g.a.opp = b.a.opp := by rw [hga]
        rw [ho] at hprev
        have : nb (b.cell (b.r - 2)) b.a.opp = b.cell (b.r - 3) := by
          unfold Bridge.cell; rw [show b.r - 2 = b.r - 3 + 1 by omega, nb_cellJ_opp]
        rw [this] at hprev
        exact prevAvoid (b.r - 3) (by omega) hprev.symm
      · -- opposite direction: the square before is `E`
        have ho : g.a.opp = b.a := by rw [hga, opp_opp]
        rw [ho] at hprev
        have : nb (b.cell (b.r - 2)) b.a = b.cell (b.r - 1) := by
          unfold Bridge.cell; rw [nb_cellJ, show b.r - 2 + 1 = b.r - 1 by omega]
        rw [this] at hprev
        exact prevAvoid (b.r - 1) (by omega) hprev.symm
      · -- perpendicular: the dark front is a light lateral of `A`
        unfold front at d2
        rcases lat_of_perp (Y := b.cell (b.r - 2)) hperp with h | h <;> rw [h] at d2
        · exact lA1 d2
        · exact lA2 d2
  · subst h; exact hun (cutSq_E hR)

-- **(C1) for a merging cell.** A non-pair alternating cell is no bridge square.
--
theorem c1_merge {BS : List Bridge} {X : Pt} (ha : Alt H X)
    (hnp : ¬ ∃ b ∈ BS, X = b.cell (b.r - 2) ∨ X = b.E)
    (hreg : ∀ b ∈ BS, RegionOK H b ∧ 2 ≤ b.r ∧ b.r % 2 = 0) {b : Bridge} (hb : b ∈ BS)
    {l : ℕ} (hl : l < b.r) : X ≠ b.cell l := by
  intro he
  obtain ⟨hR, htwo, hev⟩ := hreg b hb
  rcases (show (l = 0 ∧ 4 ≤ b.r) ∨ (1 ≤ l ∧ l + 3 ≤ b.r) ∨ l = b.r - 2 ∨ l = b.r - 1 by omega) with
    ⟨h, r4⟩ | ⟨h1, h2⟩ | h | h
  · subst h
    apply not_alt_of_ne (s' := b.a) _ (he ▸ ha)
    have hf : front (b.cell 0) b.a ∉ H := fun h' => by have := (hR.fr 0 (by omega)).1 h'; omega
    unfold Bridge.cell at hf ⊢; rw [cellJ_zero] at hf ⊢
    have hbk := hR.bk
    unfold front at hf; unfold back at hbk
    tauto
  · exact (region_inner hR h1 h2).not_alt (he ▸ ha)
  · exact hnp ⟨b, hb, Or.inl (h ▸ he)⟩
  · exact hnp ⟨b, hb, Or.inr (by rw [he, h]; rfl)⟩

end c1half

end HP

end SolidGridHam
