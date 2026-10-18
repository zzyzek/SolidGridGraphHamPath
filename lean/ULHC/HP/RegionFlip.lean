/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
import ULHC.HP.Stuck

/-!
# Flipping a region of cells (notes P15)

For a finite set `R` of cells, `bnd R` is the set of edges with exactly one of their two cells
in `R`, and `rflip F R = F ⊕ bnd R`. `OutR F R`: every arc across `bnd R` points out of `R`.

`deg_rflip`: under `OutR`, flipping `R` keeps every degree (a local check at each vertex,
by `decide`).
-/

namespace ULHC

open Finset Classical

namespace HP

-- Edges with exactly one of their two cells in `R`.
--
noncomputable def bnd (R : Finset Pt) : Finset Edge :=
  (R.biUnion cellE).filter (fun e => (decide (e.lo ∈ R) != decide (e.hi ∈ R)) = true)

lemma mem_bnd {R : Finset Pt} {e : Edge} :
    e ∈ bnd R ↔ (decide (e.lo ∈ R) != decide (e.hi ∈ R)) = true := by
  unfold bnd
  rw [Finset.mem_filter]
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨?_, h⟩
    rw [Finset.mem_biUnion]
    obtain ⟨d, p⟩ := e
    by_cases hhi : (⟨d, p⟩ : Edge).hi ∈ R
    · refine ⟨p, hhi, ?_⟩
      cases d <;> simp [cellE, bot, lft]
    · have hlo : (⟨d, p⟩ : Edge).lo ∈ R := by
        by_contra hlo
        have h1 : decide ((⟨d, p⟩ : Edge).lo ∈ R) = false := decide_eq_false hlo
        have h2 : decide ((⟨d, p⟩ : Edge).hi ∈ R) = false := decide_eq_false hhi
        rw [h1, h2] at h; simp at h
      refine ⟨_, hlo, ?_⟩
      cases d <;> simp [cellE, top, rgt, Edge.lo]

noncomputable def rflip (F : Finset Edge) (R : Finset Pt) : Finset Edge := symmDiff F (bnd R)

def OutR (F : Finset Edge) (R : Finset Pt) : Prop :=
  ∀ e ∈ bnd R, up F e = decide (e.lo ∈ R)

-- The local check at a vertex: `P` the colour of its NE cell, `m*` its four edges in `F`,
-- `r**` its four cells in `R` (`r11` NE, `r10` SE, `r01` NW, `r00` SW).
--
theorem vertex_check : ∀ P mR mL mU mD r00 r01 r10 r11 : Bool,
    ((r10 != r11) = true → ((!P) == mR) = r10) →
    ((r00 != r01) = true → (P == mL) = r00) →
    ((r01 != r11) = true → ((!P) == !mU) = r01) →
    ((r00 != r10) = true → (P == !mD) = r00) →
    (mR ^^ (r10 != r11)).toNat + (mL ^^ (r00 != r01)).toNat + (mU ^^ (r01 != r11)).toNat +
      (mD ^^ (r00 != r10)).toNat = mR.toNat + mL.toNat + mU.toNat + mD.toNat := by
  decide

lemma ind_eq_toNat (F : Finset Edge) (e : Edge) : ind F e = (decide (e ∈ F)).toNat := by
  unfold ind; by_cases h : e ∈ F <;> simp [h]

lemma ind_symmDiff_toNat (F B : Finset Edge) (e : Edge) :
    ind (symmDiff F B) e = (decide (e ∈ F) ^^ decide (e ∈ B)).toNat := by
  unfold ind; by_cases h1 : e ∈ F <;> by_cases h2 : e ∈ B <;> simp [Finset.mem_symmDiff, h1, h2]

lemma dec_bnd (R : Finset Pt) (e : Edge) :
    decide (e ∈ bnd R) = (decide (e.lo ∈ R) != decide (e.hi ∈ R)) := by
  rw [Bool.eq_iff_iff, decide_eq_true_iff]; exact mem_bnd

-- **Flipping a region whose boundary arcs all point out keeps every degree.**
--
theorem deg_rflip {F : Finset Edge} {R : Finset Pt} (hO : OutR F R) (v : Pt) :
    deg (rflip F R) v = deg F v := by
  obtain ⟨x, y⟩ := v
  unfold deg rflip
  rw [ind_symmDiff_toNat, ind_symmDiff_toNat, ind_symmDiff_toNat, ind_symmDiff_toNat,
    ind_eq_toNat, ind_eq_toNat, ind_eq_toNat, ind_eq_toNat]
  rw [dec_bnd, dec_bnd, dec_bnd, dec_bnd]
  have pR : par (x, y - 1) = !par (x, y) := par_sub_snd (x, y)
  have pL : par (x - 1, y - 1) = par (x, y) := par_sub_sub (x, y)
  have pU : par (x - 1, y) = !par (x, y) := par_sub_fst (x, y)
  have uR : up F (eR (x, y)) = (par (x, y - 1) == decide (eR (x, y) ∈ F)) := rfl
  have uL : up F (eL (x, y)) = (par (x - 1, y - 1) == decide (eL (x, y) ∈ F)) := rfl
  have uU : up F (eU (x, y)) = (par (x - 1, y) == !decide (eU (x, y) ∈ F)) := rfl
  have uD : up F (eD (x, y)) = (par (x - 1, y - 1) == !decide (eD (x, y) ∈ F)) := rfl
  have oR : (decide ((x, y - 1) ∈ R) != decide ((x, y) ∈ R)) = true →
      ((!par (x, y)) == decide (eR (x, y) ∈ F)) = decide ((x, y - 1) ∈ R) := by
    intro h
    have := hO (eR (x, y)) (mem_bnd.2 h)
    rw [uR, pR] at this; exact this
  have oL : (decide ((x - 1, y - 1) ∈ R) != decide ((x - 1, y) ∈ R)) = true →
      (par (x, y) == decide (eL (x, y) ∈ F)) = decide ((x - 1, y - 1) ∈ R) := by
    intro h
    have := hO (eL (x, y)) (mem_bnd.2 h)
    rw [uL, pL] at this; exact this
  have oU : (decide ((x - 1, y) ∈ R) != decide ((x, y) ∈ R)) = true →
      ((!par (x, y)) == !decide (eU (x, y) ∈ F)) = decide ((x - 1, y) ∈ R) := by
    intro h
    have := hO (eU (x, y)) (mem_bnd.2 h)
    rw [uU, pU] at this; exact this
  have oD : (decide ((x - 1, y - 1) ∈ R) != decide ((x, y - 1) ∈ R)) = true →
      (par (x, y) == !decide (eD (x, y) ∈ F)) = decide ((x - 1, y - 1) ∈ R) := by
    intro h
    have := hO (eD (x, y)) (mem_bnd.2 h)
    rw [uD, pL] at this; exact this
  exact vertex_check _ _ _ _ _ _ _ _ _ oR oL oU oD

/-! ## The potential after a region flip -/

-- Indicator of a cell in `R`.
--
def rin (R : Finset Pt) (c : Pt) : ℤ := if c ∈ R then 1 else 0

-- The change of every edge weight under the flip.
--
def gR (R : Finset Pt) (e : Edge) : ℤ := 2 * (rin R e.hi - rin R e.lo)

lemma wD_rflip {F H : Finset Edge} {R : Finset Pt} (hO : OutR F R) (e : Edge) :
    wD (rflip F R) H e - wD F H e = gR R e := by
  by_cases hb : e ∈ bnd R
  · have hm : e ∈ rflip F R ↔ e ∉ F := by simp [rflip, Finset.mem_symmDiff, hb]
    have hu : up (rflip F R) e = ! up F e := by
      unfold up inE1
      cases e.d <;> cases par e.lo <;> by_cases h : e ∈ F <;> simp [hm, h]
    have ho := hO e hb
    have hx := mem_bnd.1 hb
    unfold wD gR rin; rw [hu, ho]
    by_cases hl : e.lo ∈ R <;> by_cases hh : e.hi ∈ R <;> simp [hl, hh] at hx ⊢ <;>
      by_cases h1 : e ∈ F <;> by_cases h2 : e ∈ H <;> simp [hm, h1, h2, wb]
  · have hm : e ∈ rflip F R ↔ e ∈ F := by simp [rflip, Finset.mem_symmDiff, hb]
    have hx : ¬ (decide (e.lo ∈ R) != decide (e.hi ∈ R)) = true := fun h => hb (mem_bnd.2 h)
    unfold wD gR rin; rw [up_congr hm]
    by_cases hl : e.lo ∈ R <;> by_cases hh : e.hi ∈ R <;> simp [hl, hh] at hx ⊢ <;> simp [hm]

lemma gR_supp (R : Finset Pt) : Supp (bnd R) (gR R) := by
  intro e he
  have hx : ¬ (decide (e.lo ∈ R) != decide (e.hi ∈ R)) = true := fun h => he (mem_bnd.2 h)
  unfold gR rin
  by_cases hl : e.lo ∈ R <;> by_cases hh : e.hi ∈ R <;> simp [hl, hh] at hx ⊢

lemma gR_balanced (R : Finset Pt) : Balanced (gR R) := by
  intro p
  obtain ⟨x, y⟩ := p
  show 2 * (rin R (x, y - 1) - rin R (x - 1, y - 1)) + 2 * (rin R (x, y) - rin R (x, y - 1)) =
    2 * (rin R (x - 1, y) - rin R (x - 1, y - 1)) + 2 * (rin R (x, y) - rin R (x - 1, y))
  ring

lemma exists_left_of_cells (R : Finset Pt) : ∃ B : ℤ, ∀ c ∈ R, B < c.1 := by
  refine ⟨-(∑ c ∈ R, |c.1|) - 1, fun c hc => ?_⟩
  have h1 : |c.1| ≤ ∑ c ∈ R, |c.1| :=
    Finset.single_le_sum (f := fun c : Pt => |c.1|) (fun _ _ => abs_nonneg _) hc
  have h2 := neg_abs_le c.1
  omega

-- Two functions on cells with the same jumps along rows that agree far left agree.
--
lemma row_ind (f h : Pt → ℤ) (B : ℤ) (h0 : ∀ c : Pt, c.1 ≤ B → f c = h c)
    (hs : ∀ c : Pt, f c - f (c.1 - 1, c.2) = h c - h (c.1 - 1, c.2)) : ∀ c, f c = h c := by
  intro c
  obtain ⟨x, y⟩ := c
  suffices key : ∀ n : ℕ, ∀ x : ℤ, x ≤ B + n → f (x, y) = h (x, y) from
    key (x - B).toNat x (by omega)
  intro n
  induction n with
  | zero => intro x hx; exact h0 (x, y) (by simp only; omega)
  | succ n ih =>
    intro x hx
    by_cases hx' : x ≤ B + n
    · exact ih x hx'
    · have e1 := hs (x, y)
      have e2 := ih (x - 1) (by omega)
      simp only at e1
      omega

-- **The potential after a region flip**: `D` goes up by 2 on `R` and stays elsewhere.
--
theorem D_rflip {F H : Finset Edge} {R : Finset Pt} (hO : OutR F R) (x : Pt) :
    D (rflip F R) H x = D F H x + 2 * rin R x := by
  let E := symmDiff F H ∪ symmDiff (rflip F R) H ∪ bnd R
  have s1 : symmDiff (rflip F R) H ⊆ E := by
    intro e he; simp only [E, Finset.mem_union]; tauto
  have s2 : symmDiff F H ⊆ E := by
    intro e he; simp only [E, Finset.mem_union]; tauto
  have s3 : bnd R ⊆ E := by
    intro e he; simp only [E, Finset.mem_union]; tauto
  have hdiff : D (rflip F R) H x - D F H x = pot E (gR R) x := by
    unfold D
    rw [pot_mono_supp s1 (wD_supp _ _), pot_mono_supp s2 (wD_supp _ _), ← pot_sub]
    congr 1
    funext e
    exact wD_rflip hO e
  have hS : Supp E (gR R) := fun e he => gR_supp R e (fun h => he (s3 h))
  obtain ⟨B1, hB1⟩ := exists_left_bound E
  obtain ⟨B2, hB2⟩ := exists_left_of_cells R
  have hrow := row_ind (pot E (gR R)) (fun c => 2 * rin R c) (min B1 B2)
    (fun c hc => by
      rw [pot_eq_zero_of_left hB1 c (by omega)]
      have : c ∉ R := fun h => by have := hB2 c h; omega
      simp [rin, this])
    (fun c => by
      have := pot_jump hS (gR_balanced R) ⟨.v, c⟩
      simp only [Edge.hi, Edge.lo] at this
      rw [this]; unfold gR; simp only [Edge.hi, Edge.lo]; ring)
  have h3 : pot E (gR R) x = 2 * rin R x := hrow x
  omega


end HP

end ULHC
