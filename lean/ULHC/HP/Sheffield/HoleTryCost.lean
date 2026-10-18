/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
import ULHC.HP.Sheffield.HoleTry

/-!
# Hole classes: running time of `classSearchOne` (B-3, docs/HOLE_CLASSES.md §3.4)

Costs in the style of `CostPF`/`SheffCost`: explicit cost functions mirroring the computation of
`classSearch`, one step per membership test and per cell read. The potential is an array indexed by box
position (`relaxA`), so a lookup is a constant number of steps; the relaxation is charged for every
round it runs. With `s = |boxSquares V|` and `N = |W| + 1`:

* one relaxation round with its stop test: `≤ 100 (s + 1)` (`relaxCost_le`);
* `classSearchCost ≤ 500 (|as| + 1) N⁴` when the box of `V` is narrow, i.e. its width and height are
  below `|V|` (`classSearchCost_le`), hence `classSearchOneCost ≤ 1000 N⁴` (`classSearchOneCost_le`); the relaxation runs `|boxSquares V| + 1` rounds (`relax_bf`);
* a box is narrow as soon as some edge set inside `V` has one component on `V`
  (`narrow_of_ncomp`).
-/

namespace ULHC

namespace HP

open Finset

lemma hlsum_const {α : Type*} (l : List α) (c : ℕ) : (l.map fun _ => c).sum = l.length * c := by
  induction l with
  | nil => simp
  | cons a l ih => simp only [List.map_cons, List.sum_cons, List.length_cons, ih]; ring

/-! ## Cost functions -/

-- The four box bounds: one pass over `V` each.
--
def boxCost (V : Finset Pt) : ℕ := 4 * V.card + 4

def boxSquaresCost (V : Finset Pt) : ℕ := (bx1 V - bx0 V).toNat + (boxSquares V).length + 1

def kFuelCost (V : Finset Pt) : ℕ := (boxSquares V).length + 5

-- One array lookup: the box test, the index, the read.
--
def lookCost : ℕ := 8

-- `IsEdge` (two membership tests), `up` (one), and the interval.
--
def ivlCost : ℕ := 4

def lowerBoundCost : ℕ := 4 * lookCost + 4 * ivlCost + 1

-- One round: for every box position, its cell, two lookups and the lower bound.
--
def roundCost (V : Finset Pt) : ℕ := (kWn V * kHn V) * (2 * lookCost + lowerBoundCost + 4) + 1

-- The stop test: two lookups per box cell.
--
def allCost (V : Finset Pt) : ℕ := (boxSquares V).length * (2 * lookCost + 2) + 1

def relaxCost (V : Finset Pt) (F : Finset Edge) : ℕ → Array ℤ → ℕ
  | 0, _ => 1
  | n + 1, A =>
    roundCost V + allCost V + 1 +
      (if (boxSquares V).all (fun c => toFA V (roundA V F A) c == toFA V A c) then 0
        else relaxCost V F n (roundA V F A))

-- One lookup in `as.zip hs` per box position.
--
def kInitCost (V : Finset Pt) (as : List Pt) : ℕ := (kWn V * kHn V) * (as.length + 4) + 1

def sideOKCost : ℕ := 2 * lookCost + 6

def isAdmissibleCost (S : List Pt) (as : List Pt) : ℕ :=
  (S.map fun _ => 4 * sideOKCost + 1).sum + as.length * (lookCost + 1) + 1

-- The `4 s` sides, each filtered by two lookups and an `IsEdge` test, then deduplicated.
--
def jumpEdgesCost (S : List Pt) : ℕ :=
  4 * S.length + 4 * S.length * (2 * lookCost + 3) + (4 * S.length) ^ 2 + 1

def symmDiffCost (F X : Finset Edge) : ℕ := (F.card + X.card) ^ 2 + 1

def classSearchCost (V : Finset Pt) (F : Finset Edge) (as : List Pt) (hs : List ℤ) : ℕ :=
  boxCost V + boxSquaresCost V + kFuelCost V + kInitCost V as +
    relaxCost V F (kFuel V) (kInitA V as hs) +
    isAdmissibleCost (boxSquares V) as + 1 +
    (if isAdmissible V F as hs (classPotential V F as hs) then
      jumpEdgesCost (boxSquares V) + symmDiffCost F (jumpEdges V (classPotential V F as hs))
    else 0)

def classSearchOneCost (V : Finset Pt) (F : Finset Edge) (t : Pt) (h : ℤ) : ℕ := classSearchCost V F [t] [h]

/-! ## Sizes -/

lemma length_kSq (V : Finset Pt) :
    (boxSquares V).length = (bx1 V - bx0 V).toNat * (by1 V - by0 V).toNat := by
  unfold boxSquares
  rw [List.length_flatMap]
  simp only [List.length_map, List.length_range]
  rw [List.map_const', List.sum_replicate, List.length_range, smul_eq_mul]

lemma card_kX_le (V : Finset Pt) (f : Pt → ℤ) : (jumpEdges V f).card ≤ 4 * (boxSquares V).length := by
  unfold jumpEdges
  refine (List.toFinset_card_le _).trans ((List.length_filter_le _ _).trans ?_)
  rw [List.length_flatMap]
  simp only [sides, List.length_cons, List.length_nil]
  rw [hlsum_const]
  omega

lemma card_inside_le {W : Finset Pt} {F : Finset Edge} (hF : Inside W F) :
    F.card ≤ 2 * W.card := by
  have hsub : F ⊆ W.biUnion (fun v => ({eR v, eU v} : Finset Edge)) := by
    intro e he
    have hp := (hF e he).1
    rw [Finset.mem_biUnion]
    refine ⟨e.p, hp, ?_⟩
    obtain ⟨d, p⟩ := e
    cases d <;> simp [eR, eU]
  refine (Finset.card_le_card hsub).trans ((Finset.card_biUnion_le).trans ?_)
  calc ∑ v ∈ W, ({eR v, eU v} : Finset Edge).card ≤ ∑ _v ∈ W, 2 :=
        Finset.sum_le_sum (fun v _ => Finset.card_le_two)
    _ = 2 * W.card := by rw [Finset.sum_const, smul_eq_mul]; ring

/-! ## Bounds -/

lemma kWn_kHn (V : Finset Pt) : kWn V * kHn V = (boxSquares V).length := by
  rw [length_kSq]; rfl

lemma relaxCost_le (V : Finset Pt) (F : Finset Edge) :
    ∀ n (A : Array ℤ), relaxCost V F n A ≤ (n + 1) * (100 * ((boxSquares V).length + 1)) := by
  have hround : roundCost V + allCost V + 1 ≤ 100 * ((boxSquares V).length + 1) := by
    unfold roundCost allCost lowerBoundCost lookCost ivlCost
    rw [kWn_kHn]
    omega
  intro n
  induction n with
  | zero => intro A; simp only [relaxCost]; omega
  | succ n ih =>
    intro A
    simp only [relaxCost]
    have h2 := ih (roundA V F A)
    split_ifs
    · nlinarith
    · nlinarith

lemma hcost_ar1 (s a : ℕ) :
    s * (4 * (2 * (s + 1) + 6) + 1) + a * (s + 1 + 1) + 1 ≤ 40 * (a + 1) * (s + 1) ^ 2 := by
  ring_nf
  nlinarith [Nat.zero_le (a * s ^ 2), Nat.zero_le (a * s), Nat.zero_le (s ^ 2)]

lemma hcost_ar2 (s : ℕ) : 4 * s + 4 * s * (2 * (s + 1) + 3) + (4 * s) ^ 2 + 1 ≤ 41 * (s + 1) ^ 2 := by
  nlinarith

lemma hcost_ar3 (s a : ℕ) : s * (a + 2) + 1 ≤ 3 * (a + 1) * (s + 1) := by
  nlinarith

section narrow

variable {V W : Finset Pt} {F : Finset Edge}

/-- **Cost of `classSearch`.** With a narrow box (width and height below `|V|`), `V ⊆ W` and `F` inside
`W`: `classSearchCost ≤ 500 (|as| + 1) (|W| + 1)⁴`. -/
theorem classSearchCost_le (hVW : V ⊆ W) (hF : Inside W F) (hw : bx1 V - bx0 V < V.card)
    (hh : by1 V - by0 V < V.card) (as : List Pt) (hs : List ℤ) :
    classSearchCost V F as hs ≤ 500 * (as.length + 1) * (W.card + 1) ^ 4 := by
  set s := (boxSquares V).length with hsdef
  set n := V.card
  set N := W.card + 1 with hNdef
  have hnW : n ≤ W.card := Finset.card_le_card hVW
  have hn : n < N := by omega
  have hwn : (bx1 V - bx0 V).toNat ≤ n := by omega
  have hhn : (by1 V - by0 V).toNat ≤ n := by omega
  have hsn : s ≤ n * n := by
    rw [hsdef, length_kSq]; exact Nat.mul_le_mul hwn hhn
  have hkW : (boxWidth V).toNat ≤ n := by unfold boxWidth; omega
  have hM : s + 1 ≤ N ^ 2 := by nlinarith
  have hN1 : 1 ≤ N := by omega
  have hM2 : (s + 1) ^ 2 ≤ N ^ 4 := by
    calc (s + 1) ^ 2 ≤ (N ^ 2) ^ 2 := Nat.pow_le_pow_left hM 2
      _ = N ^ 4 := by ring
  have hN25 : N ^ 2 ≤ N ^ 4 := Nat.pow_le_pow_right hN1 (by omega)
  -- The relaxation: `kFuel + 1` rounds of `100 (s + 1)` steps.
  --
  have hfuel' : kFuel V + 1 ≤ 2 * (s + 1) := by unfold kFuel; rw [← hsdef]; omega
  have hR' : relaxCost V F (kFuel V) (kInitA V as hs) ≤ 200 * N ^ 4 := by
    calc relaxCost V F (kFuel V) (kInitA V as hs)
        ≤ (kFuel V + 1) * (100 * (s + 1)) := relaxCost_le V F _ _
      _ ≤ 2 * (s + 1) * (100 * (s + 1)) := Nat.mul_le_mul_right _ hfuel'
      _ = 200 * (s + 1) ^ 2 := by ring
      _ ≤ 200 * N ^ 4 := Nat.mul_le_mul_left _ hM2
  -- The check, the jump set and the symmetric difference.
  --
  have hC : isAdmissibleCost (boxSquares V) as ≤ 100 * (as.length + 1) * N ^ 2 := by
    unfold isAdmissibleCost sideOKCost lookCost
    rw [hlsum_const, ← hsdef]
    have : 100 * (as.length + 1) * (s + 1) ≤ 100 * (as.length + 1) * N ^ 2 :=
      Nat.mul_le_mul_left _ hM
    nlinarith
  have hX : jumpEdgesCost (boxSquares V) ≤ 100 * N ^ 4 := by
    unfold jumpEdgesCost lookCost
    rw [← hsdef]
    have : 100 * (s + 1) ^ 2 ≤ 100 * N ^ 4 := Nat.mul_le_mul_left _ hM2
    nlinarith
  have hSD : symmDiffCost F (jumpEdges V (classPotential V F as hs)) ≤ 37 * N ^ 4 := by
    unfold symmDiffCost
    have h1 := card_inside_le hF
    have h2 := card_kX_le V (classPotential V F as hs)
    rw [← hsdef] at h2
    have hN2 : N ≤ N ^ 2 := Nat.le_self_pow (by omega) _
    have h3 : F.card + (jumpEdges V (classPotential V F as hs)).card ≤ 6 * N ^ 2 := by omega
    have : (F.card + (jumpEdges V (classPotential V F as hs)).card) ^ 2 ≤ (6 * N ^ 2) ^ 2 :=
      Nat.pow_le_pow_left h3 2
    have e : (6 * N ^ 2) ^ 2 = 36 * N ^ 4 := by ring
    have : 1 ≤ N ^ 4 := Nat.one_le_pow _ _ (by omega)
    omega
  -- The cheap parts.
  --
  have hB : boxCost V ≤ 4 * N := by unfold boxCost; omega
  have hN2 : N ≤ N ^ 2 := Nat.le_self_pow (by omega) _
  have hQ : boxSquaresCost V ≤ 2 * N ^ 2 := by unfold boxSquaresCost; rw [← hsdef]; omega
  have hFu : kFuelCost V ≤ 6 * N ^ 2 := by unfold kFuelCost; rw [← hsdef]; omega
  have hI : kInitCost V as ≤ 5 * (as.length + 1) * N ^ 2 := by
    unfold kInitCost; rw [kWn_kHn, ← hsdef]
    have : 5 * (as.length + 1) * (s + 1) ≤ 5 * (as.length + 1) * N ^ 2 := Nat.mul_le_mul_left _ hM
    nlinarith
  have hif : (if isAdmissible V F as hs (classPotential V F as hs) then
      jumpEdgesCost (boxSquares V) + symmDiffCost F (jumpEdges V (classPotential V F as hs)) else 0) ≤ 137 * N ^ 4 := by
    split_ifs <;> omega
  unfold classSearchCost
  have t1 : 100 * (as.length + 1) * N ^ 2 ≤ 100 * (as.length + 1) * N ^ 4 :=
    Nat.mul_le_mul_left _ hN25
  have t2 : 5 * (as.length + 1) * N ^ 2 ≤ 5 * (as.length + 1) * N ^ 4 := Nat.mul_le_mul_left _ hN25
  have t3 : (as.length + 1) * N ^ 4 ≥ N ^ 4 := Nat.le_mul_of_pos_left _ (by omega)
  have e1 : 500 * (as.length + 1) * N ^ 4 = 500 * ((as.length + 1) * N ^ 4) := by ring
  have e2 : 100 * (as.length + 1) * N ^ 4 = 100 * ((as.length + 1) * N ^ 4) := by ring
  have e3 : 5 * (as.length + 1) * N ^ 4 = 5 * ((as.length + 1) * N ^ 4) := by ring
  omega

/-- **Cost of `classSearchOne`.** With a narrow box, `V ⊆ W` and `F` inside `W`:
`classSearchOneCost ≤ 1000 (|W| + 1)⁴`. -/
theorem classSearchOneCost_le (hVW : V ⊆ W) (hF : Inside W F) (hw : bx1 V - bx0 V < V.card)
    (hh : by1 V - by0 V < V.card) (t : Pt) (h : ℤ) :
    classSearchOneCost V F t h ≤ 1000 * (W.card + 1) ^ 4 := by
  have := classSearchCost_le hVW hF hw hh [t] [h]
  simp only [List.length_cons, List.length_nil] at this
  unfold classSearchOneCost
  omega

-- A box spanned by one component of an edge set inside `V` is narrow.
--
theorem narrow_of_ncomp {H : Finset Edge} (hH : Inside V H) (hHam : ncomp V H = 1) :
    bx1 V - bx0 V < V.card ∧ by1 V - by0 V < V.card := by
  have hV : V.Nonempty := by
    by_contra hV
    rw [Finset.not_nonempty_iff_eq_empty] at hV
    subst hV
    unfold ncomp at hHam
    simp at hHam
  obtain ⟨⟨p0, hp0, e0⟩, ⟨p1, hp1, e1⟩, ⟨q0, hq0, f0⟩, ⟨q1, hq1, f1⟩⟩ := box_attain hV
  have w1 := width_lt_card' hH hHam hp0 hp1
  have w2 := height_lt_card' hH hHam hq0 hq1
  omega

end narrow

end HP

end ULHC
