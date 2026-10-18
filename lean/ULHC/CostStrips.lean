/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
import ULHC.CostConn
import ULHC.AlgComplete

/-!
# Running time, part 2: strips, links and the link graph's nodes

* `stripScanCost`, `stripLenCost`, `allStripsCost ≤ 100 N²` (any edge set).
* `len_le_card`: a strip with all cells in `V` has at most `|V|` cells.
* `cr2BCost`, `gedgeCost ≤ 300 N²` and `gsrcCost ≤ 140 N²` on link-graph nodes of a factor.
* `candNCost ≤ 300 N³`.
-/

namespace ULHC

open Finset

/-! ## Strip enumeration -/

-- Each scanned cell: `IsCell` (four membership tests), `LatOK` and the front test.
--
def stripScanCost (V : Finset Pt) (F : Finset Edge) (c : Pt) (s : Side) : ℕ → ℕ → ℕ
  | 0, _ => 1
  | k + 1, j =>
    20 + (if IsCell V (cellJ c s j) ∧ LatOK F c s j then
      (if (front (cellJ c s j) s ∈ F ↔ j % 2 = 0) then 0 else stripScanCost V F c s k (j + 1))
      else 0)

def stripLenCost (V : Finset Pt) (F : Finset Edge) (c : Pt) (s : Side) : ℕ :=
  V.card + 3 + stripScanCost V F c s V.card 0

-- `allStrips`: the cell test on each point, four scans per cell, and the produced strips.
--
def allStripsCost (V : Finset Pt) (F : Finset Edge) : ℕ :=
  ∑ _c ∈ V, 8 + ∑ c ∈ V.filter (IsCell V), (∑ s ∈ sidesF, (stripLenCost V F c s + 2) + 5)

lemma stripScanCost_le (V : Finset Pt) (F : Finset Edge) (c : Pt) (s : Side) :
    ∀ k j, stripScanCost V F c s k j ≤ 20 * (k + 1) := by
  intro k
  induction k with
  | zero => intro j; simp [stripScanCost]
  | succ k ih =>
    intro j
    simp only [stripScanCost]
    have := ih (j + 1)
    split_ifs <;> omega

lemma allStripsCost_le (V : Finset Pt) (F : Finset Edge) :
    allStripsCost V F ≤ 120 * (V.card + 1) ^ 2 := by
  unfold allStripsCost
  have hf : (V.filter (IsCell V)).card ≤ V.card := card_filter_le _ _
  have hs : sidesF.card = 4 := by decide
  have h1 : ∑ c ∈ V.filter (IsCell V), (∑ s ∈ sidesF, (stripLenCost V F c s + 2) + 5) ≤
      V.card * (4 * (21 * (V.card + 1) + 4) + 5) := by
    have := Finset.sum_le_card_nsmul (V.filter (IsCell V))
      (fun c => ∑ s ∈ sidesF, (stripLenCost V F c s + 2) + 5) (4 * (21 * (V.card + 1) + 4) + 5)
      (fun c _ => by
        have := Finset.sum_le_card_nsmul sidesF (fun s => stripLenCost V F c s + 2)
          (21 * (V.card + 1) + 4) (fun s _ => by
            have := stripScanCost_le V F c s V.card 0; unfold stripLenCost; omega)
        simp only [hs, smul_eq_mul] at this
        omega)
    simp only [smul_eq_mul] at this
    exact this.trans (Nat.mul_le_mul_right _ hf)
  simp only [sum_const, smul_eq_mul]
  nlinarith

-- A strip with all cells in `V` has at most `|V|` cells (the cells are distinct points of `V`).
--
lemma len_le_card {V : Finset Pt} {c : Pt} {s : Side} {n : ℕ}
    (hc : ∀ j < n, IsCell V (cellJ c s j)) : n ≤ V.card := by
  have hsub : (range n).image (cellJ c s) ⊆ V := by
    intro z hz
    simp only [mem_image, mem_range] at hz
    obtain ⟨j, hj, rfl⟩ := hz
    exact (hc j hj).1
  have := card_le_card hsub
  rwa [card_image_of_injective _ (fun i j h => cellJ_inj c s h), card_range] at this

/-! ## Links -/

def flipCost : ℕ := 8

def sideOffBCost (b c : StripSpec) : ℕ := c.n * (20 * b.n + 2) + b.n + 2

def midBCost (b : StripSpec) : ℕ := 10 * b.n + 1

def notEndBCost (c : StripSpec) : ℕ := 5 * c.n + 1

def endOffBCost : ℕ := 30

-- `cr2B b c`, all operands charged; `flip G (endCell b)` is built twice.
--
def cr2BCost (V : Finset Pt) (G : Finset Edge) (b c : StripSpec) : ℕ :=
  13 + 2 * flipCost + allStripsCost V (flip G (endCell b)) + sideOffBCost b c + notEndBCost c +
    endOffBCost + 2 * midBCost b + connBCost V G (back1 c.c c.s) +
    connBCost V (flip G (endCell b)) (back1 c.c c.s)

def chainOKBCost (c : StripSpec) : ℕ := 30 * c.n + 1

def validBCost (V : Finset Pt) (F : Finset Edge) (σ : StripSpec) : ℕ :=
  allStripsCost V F + connBCost V F (back1 σ.c σ.s) + 5

def gedgeCost (V : Finset Pt) (G : Finset Edge) (x y : Node) : ℕ :=
  3 + cr2BCost V G x.σ y.σ + chainOKBCost y.σ

def gsrcCost (V : Finset Pt) (G : Finset Edge) (x : Node) : ℕ := 2 + validBCost V G x.σ

/-! ## Candidate nodes -/

def candCost (V : Finset Pt) (G : Finset Edge) : ℕ :=
  allStripsCost V G +
    ∑ u ∈ V.filter (IsCell V), (flipCost + allStripsCost V (flip G u) + (allStrips V (flip G u)).card + 1) +
    9 * V.card + 2 * (cand V G).card

def candNCost (V : Finset Pt) (G : Finset Edge) : ℕ :=
  candCost V G + 10 * (cand V G).card + (candN V G).card

/-! ## Bounds -/

section bounds

variable {V : Finset Pt} {G : Finset Edge}

lemma node_len (x : Node) (hx : x ∈ candN V G) : 1 ≤ x.σ.n ∧ x.σ.n ≤ V.card ∧
    ∀ j < x.σ.n, IsCell V (cellJ x.σ.c x.σ.s j) := by
  obtain ⟨h1, hc⟩ := cells_of_cand (mem_candN.1 hx).1
  exact ⟨h1, len_le_card hc, hc⟩

lemma cr2BCost_le (hGV : Inside V G) {b c : StripSpec} (hb1 : 1 ≤ b.n) (hbn : b.n ≤ V.card)
    (hb : ∀ j < b.n, IsCell V (cellJ b.c b.s j)) (hcn : c.n ≤ V.card) :
    cr2BCost V G b c ≤ 270 * (V.card + 1) ^ 2 := by
  have hu := endCell_isCell hb1 hb
  have h1 := allStripsCost_le V (flip G (endCell b))
  have h2 := connBCost_le hGV (back1 c.c c.s)
  have h3 := connBCost_le (inside_flip hGV hu) (back1 c.c c.s)
  unfold cr2BCost sideOffBCost notEndBCost endOffBCost midBCost flipCost
  nlinarith

lemma gedgeCost_le (hGV : Inside V G) {x y : Node} (hx : x ∈ candN V G) (hy : y ∈ candN V G) :
    gedgeCost V G x y ≤ 300 * (V.card + 1) ^ 2 := by
  obtain ⟨hx1, hxn, hxc⟩ := node_len x hx
  obtain ⟨_, hyn, _⟩ := node_len y hy
  have := cr2BCost_le hGV hx1 hxn hxc hyn
  unfold gedgeCost chainOKBCost
  nlinarith

lemma gsrcCost_le (hGV : Inside V G) (x : Node) : gsrcCost V G x ≤ 160 * (V.card + 1) ^ 2 := by
  have h1 := allStripsCost_le V G
  have h2 := connBCost_le hGV (back1 x.σ.c x.σ.s)
  have hN1 : 1 ≤ (V.card + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  unfold gsrcCost validBCost
  nlinarith

lemma candNCost_le (G : Finset Edge) : candNCost V G ≤ 300 * (V.card + 1) ^ 3 := by
  have hc := card_cand_le (V := V) G
  have hN := card_candN_le (V := V) G
  have h0 := allStripsCost_le V G
  have hf : (V.filter (IsCell V)).card ≤ V.card := card_filter_le _ _
  have h1 : ∑ u ∈ V.filter (IsCell V),
      (flipCost + allStripsCost V (flip G u) + (allStrips V (flip G u)).card + 1) ≤
      V.card * (9 + 120 * (V.card + 1) ^ 2 + 4 * V.card) := by
    have := Finset.sum_le_card_nsmul (V.filter (IsCell V))
      (fun u => flipCost + allStripsCost V (flip G u) + (allStrips V (flip G u)).card + 1)
      (9 + 120 * (V.card + 1) ^ 2 + 4 * V.card) (fun u _ => by
        have := allStripsCost_le V (flip G u)
        have := card_allStrips (V := V) (F := flip G u)
        unfold flipCost; omega)
    simp only [smul_eq_mul] at this
    exact this.trans (Nat.mul_le_mul_right _ hf)
  unfold candNCost candCost Bd at *
  nlinarith

end bounds

end ULHC
