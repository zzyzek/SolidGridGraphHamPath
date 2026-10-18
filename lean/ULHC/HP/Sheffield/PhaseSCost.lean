/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
import ULHC.HP.Sheffield.ReduceS

/-!
# Running time of the fast loop

Costs in the style of `SheffCost`. With `N = |W| + 1`:
* `connectedPairsCost ≤ 100 N²`: each component's class is computed once (`connectedPairsCost_le`);
* one step of `runPhase` costs `O(N²)`, the phase `O(N³)` (`runPhaseCost_le`);
* `reducePieces` costs `O(N³)` (`reducePiecesCost_le`);
* one round of `twoPhantomLoop` costs `O(N³)`, the loop `O(N⁴)` (`twoPhantomLoopCost_le`).
-/

namespace ULHC

namespace HP

open Finset Classical

/-! ## The connection set -/

def compsAuxCost (W : Finset Pt) (H : Finset Edge) : List Pt → Finset Pt → ℕ
  | [], _ => 1
  | x :: xs, cov =>
    if x ∈ cov then 1 + compsAuxCost W H xs cov
    else cclsCost W H x + cov.card + (ccls W H x).card + 2 +
      compsAuxCost W H xs (cov ∪ ccls W H x)

def ptListCost (W : Finset Pt) : ℕ := 10 * W.card + W.card ^ 2 + 1

def connectedPairsCost (W : Finset Pt) (H : Finset Edge) : ℕ :=
  ptListCost W + compsAuxCost W H (ptList W) ∅ + ((comps W H).map fun C => C.card ^ 2 + 1).sum + 1

section connCost

variable {W : Finset Pt} {H : Finset Edge}

lemma length_ptList (W : Finset Pt) : (ptList W).length = W.card := by
  unfold ptList; simp

-- One class costs about `|W|` rounds over its own points.
--
lemma cclsCost_le' (_hHW : Inside W H) (x : Pt) :
    cclsCost W H x ≤ 30 * (W.card + 1) * ((ccls W H x).card + 1) := by
  set C := ccls W H x with hC
  have key : ∀ k, k ≤ W.card → creachCost H x k ≤ 1 + 26 * C.card * k := by
    intro k
    induction k with
    | zero => intro _; simp [creachCost]
    | succ k ih =>
      intro hk
      have h1 := ih (by omega)
      have hs : creach H x k ⊆ C := creach_mono (by omega)
      have hs' : creach H x (k + 1) ⊆ C := creach_mono hk
      have hb : ((creach H x k).biUnion (fnbr H)).card ≤ C.card := by
        refine Finset.card_le_card (Finset.Subset.trans ?_ hs')
        rw [creach_succ]; exact Finset.subset_union_right
      have hsum : ∑ u ∈ creach H x k, (fnbrCost + (fnbr H u).card) ≤ 24 * C.card := by
        calc ∑ u ∈ creach H x k, (fnbrCost + (fnbr H u).card)
            ≤ ∑ _u ∈ creach H x k, 24 :=
              Finset.sum_le_sum (fun u _ => by have := card_fnbr_le H u; unfold fnbrCost; omega)
          _ = 24 * (creach H x k).card := by rw [Finset.sum_const, smul_eq_mul]; ring
          _ ≤ 24 * C.card := Nat.mul_le_mul_left _ (Finset.card_le_card hs)
      have hck := Finset.card_le_card hs
      simp only [creachCost]
      nlinarith
  unfold cclsCost
  have := key W.card le_rfl
  nlinarith

lemma ccls_disj (hHW : Inside W H) {cov : Finset Pt} (hcl : ∀ x ∈ cov, ccls W H x ⊆ cov)
    {x : Pt} (hxW : x ∈ W) (hx : x ∉ cov) : Disjoint (ccls W H x) cov := by
  rw [Finset.disjoint_left]
  intro a ha hac
  have := hcl a hac
  rw [ccls_eq_of_mem hHW hxW ha] at this
  exact hx (this (mem_ccls_self x))

lemma card_sdiff_step (hHW : Inside W H) {cov : Finset Pt} (_hcov : cov ⊆ W)
    (hcl : ∀ x ∈ cov, ccls W H x ⊆ cov) {x : Pt} (hxW : x ∈ W) (hx : x ∉ cov) :
    (W \ (cov ∪ ccls W H x)).card + (ccls W H x).card = (W \ cov).card := by
  have hsub : ccls W H x ⊆ W \ cov := by
    intro a ha
    rw [Finset.mem_sdiff]
    refine ⟨ccls_sub hHW hxW ha, fun h => ?_⟩
    exact Finset.disjoint_left.1 (ccls_disj hHW hcl hxW hx) ha h
  rw [show W \ (cov ∪ ccls W H x) = (W \ cov) \ (ccls W H x) from (sdiff_sdiff_left).symm,
    Finset.card_sdiff_of_subset hsub]
  have := Finset.card_le_card hsub
  omega

lemma compsAuxCost_le (hHW : Inside W H) :
    ∀ (l : List Pt) (cov : Finset Pt), (∀ x ∈ l, x ∈ W) → cov ⊆ W →
      (∀ x ∈ cov, ccls W H x ⊆ cov) →
      compsAuxCost W H l cov ≤ 40 * (W.card + 1) * (l.length + (W \ cov).card) + 1 ∧
      ((compsAux W H l cov).map fun C => C.card ^ 2 + 1).sum ≤ (W \ cov).card ^ 2 + l.length := by
  intro l
  induction l with
  | nil => intro _ _ _ _; simp [compsAuxCost, compsAux]
  | cons y ys ih =>
    intro cov hl hcov hcl
    have hyW := hl y (by simp)
    have hys : ∀ x ∈ ys, x ∈ W := fun x hx => hl x (by simp [hx])
    simp only [compsAuxCost, compsAux, List.length_cons]
    by_cases hy : y ∈ cov
    · rw [ite_eq_left hy, ite_eq_left hy]
      obtain ⟨a, b⟩ := ih cov hys hcov hcl
      constructor
      · nlinarith
      · omega
    · rw [ite_eq_right hy, ite_eq_right hy]
      have hcov' : cov ∪ ccls W H y ⊆ W := Finset.union_subset hcov (ccls_sub hHW hyW)
      have hcl' : ∀ x ∈ cov ∪ ccls W H y, ccls W H x ⊆ cov ∪ ccls W H y := by
        intro x hx
        rcases Finset.mem_union.1 hx with hx | hx
        · exact (hcl x hx).trans Finset.subset_union_left
        · rw [ccls_eq_of_mem hHW hyW hx]; exact Finset.subset_union_right
      obtain ⟨a, b⟩ := ih _ hys hcov' hcl'
      have hd := card_sdiff_step hHW hcov hcl hyW hy
      have hcc := cclsCost_le' hHW y
      have hcovW : cov.card ≤ W.card := Finset.card_le_card hcov
      set c := (ccls W H y).card
      set d := (W \ (cov ∪ ccls W H y)).card
      constructor
      · rw [← hd]
        nlinarith
      · simp only [List.map_cons, List.sum_cons]
        rw [← hd]
        nlinarith

-- **The connection set costs `O(|W|²)`.**
--
theorem connectedPairsCost_le (hHW : Inside W H) : connectedPairsCost W H ≤ 100 * (W.card + 1) ^ 2 := by
  obtain ⟨a, b⟩ := compsAuxCost_le hHW (ptList W) ∅ (fun x hx => mem_ptList.1 hx)
    (Finset.empty_subset _) (by simp)
  rw [length_ptList, Finset.sdiff_empty] at a b
  unfold connectedPairsCost ptListCost comps
  nlinarith

end connCost

/-! ## The phase -/

def isCutCellCost : ℕ := 7
def isCriticalCost : ℕ := 10

def findMergingCellCost (V : Finset Pt) (BS : List Bridge) : ℕ :=
  cellListCost V + ((cellList V).map fun _ => altCost + isCutCellCost + pairSqBCost BS + 1).sum + 1

def bridgeSquaresCost (BS : List Bridge) : ℕ := (BS.map fun b => b.r + 1).sum + 1

def scanRowCost (V : Finset Pt) : ℕ :=
  (V.card + 1) * (2 * outArcCost + isCellCost + isCutCellCost + 1) + outArcCost + 1

def findRowCost (V : Finset Pt) (BS : List Bridge) : ℕ :=
  bridgeSquaresCost BS + 4 * (cellList V).length * (isCriticalCost + scanRowCost V + 4) + cellListCost V +
    5 * (cellList V).length + 1

def runPhaseCost (V W : Finset Pt) : ℕ → Finset Edge → List Bridge → ℕ
  | 0, _, _ => 1
  | n + 1, H, BS =>
    connectedPairsCost W H + findMergingCellCost V BS + 1 +
      match findMergingCell V (connectedPairs W H) H BS with
      | some _ => 0
      | none =>
        findRowCost V BS + 1 +
          match findRow V (connectedPairs W H) H BS with
          | none => 0
          | some b =>
            if b.r % 2 = 1 then 1
            else flipSplitsCost W H b + 1 +
              (if flipSplits W H b then flipCost + runPhaseCost V W n (flip H b.E) (b :: BS) else 0)

section phaseCost

variable {V W : Finset Pt} {H : Finset Edge} {BS : List Bridge}

lemma length_cellList_le (hVW : V ⊆ W) : (cellList V).length ≤ W.card := by
  have h1 : (cellList V).length ≤ V.card := by
    unfold cellList; simp only [List.length_map, Finset.length_sort, Finset.card_map]
    exact Finset.card_filter_le _ _
  exact h1.trans (Finset.card_le_card hVW)

lemma findMergingCellCost_le (hVW : V ⊆ W) (hBS : BS.length ≤ W.card + 1) :
    findMergingCellCost V BS ≤ 20 * (W.card + 1) ^ 2 := by
  have hc := cellListCost_le' hVW
  have hl := length_cellList_le hVW
  unfold findMergingCellCost altCost isCutCellCost pairSqBCost
  rw [List.map_const', List.sum_replicate, smul_eq_mul]
  nlinarith

lemma bridgeSquaresCost_le (hBS : BS.length ≤ W.card + 1) (hr : ∀ b ∈ BS, b.r ≤ W.card + 1) :
    bridgeSquaresCost BS ≤ 3 * (W.card + 1) ^ 2 + 1 := by
  unfold bridgeSquaresCost
  have := lsum_le BS (fun b => b.r + 1) (W.card + 2) (fun b hb => by have := hr b hb; omega)
  nlinarith

lemma findRowCost_le (hVW : V ⊆ W) (hBS : BS.length ≤ W.card + 1)
    (hr : ∀ b ∈ BS, b.r ≤ W.card + 1) : findRowCost V BS ≤ 150 * (W.card + 1) ^ 2 := by
  have hb := bridgeSquaresCost_le hBS hr
  have hc := cellListCost_le' hVW
  have hl := length_cellList_le hVW
  have hV := Finset.card_le_card hVW
  unfold findRowCost scanRowCost isCriticalCost outArcCost isCellCost isCutCellCost
  nlinarith

-- **The fast phase.** With `n` steps of fuel left and `|BS| + n ≤ |W| + 1`, each step `O(|W|²)`.
--
theorem runPhaseCost_le (hVW : V ⊆ W) :
    ∀ n (H : Finset Edge) (BS : List Bridge), PhI V W H BS → BS.length + n ≤ W.card + 1 →
      runPhaseCost V W n H BS ≤ (n + 1) * (400 * (W.card + 1) ^ 2) := by
  intro n
  induction n with
  | zero =>
    intro H BS _ _
    simp only [runPhaseCost]
    have : 1 ≤ (W.card + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
    omega
  | succ n ih =>
    intro H BS hI hlen
    have hfc : flipCost = 8 := rfl
    have hBS : BS.length ≤ W.card + 1 := by omega
    have hV := Finset.card_le_card hVW
    have hr : ∀ b ∈ BS, b.r ≤ W.card + 1 := fun b hb => by have := (hI.2 b hb).1; omega
    have c0 := connectedPairsCost_le hI.1 (W := W)
    have c1 := findMergingCellCost_le hVW hBS
    have c2 := findRowCost_le hVW hBS hr
    have a0 : 1 ≤ (W.card + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
    have e : (n + 1 + 1) * (400 * (W.card + 1) ^ 2) =
        (n + 1) * (400 * (W.card + 1) ^ 2) + 400 * (W.card + 1) ^ 2 := Nat.succ_mul _ _
    have hX : 400 * (W.card + 1) ^ 2 ≤ (n + 1) * (400 * (W.card + 1) ^ 2) :=
      Nat.le_mul_of_pos_left _ (by omega)
    rw [e]
    simp only [runPhaseCost]
    rw [findMergingCell_eq hVW hI.1, findRow_eq hVW hI.1]
    rcases hm : findMerge V W H BS with _ | c
    · simp only
      rcases hmv : findMove V W H BS with _ | b
      · simp only; omega
      · simp only
        have mf := findMove_some hVW hI.1 hmv
        have hE : IsCell V b.E := mf.2.2.2.2.2.1 _ (by have := mf.2.2.2.2.1; omega)
        have c3 := flipSplitsCost_le hVW hI.1 hE
        split_ifs with h1 h2
        · omega
        · have := ih _ _ (phI_step hVW hI hmv) (by simp; omega)
          omega
        · omega
    · simp only; omega

end phaseCost

/-! ## The undo -/

def bridgeStatesConnCost (W : Finset Pt) : Finset Edge → List Bridge → ℕ
  | _, [] => 1
  | H, b :: BS => flipCost + connectedPairsCost W (flip H b.E) + 1 + bridgeStatesConnCost W (flip H b.E) BS

def undoPlanStepsCost (BS : List Bridge) : ℕ := 3 * BS.length + 1

-- The cut test, the pair test, one plan, and one indexed read per bridge.
--
def isGoodMergingCellCost (W : Finset Pt) (H : Finset Edge) (BS : List Bridge) (X : Pt) : ℕ :=
  altCost + cutBCost W H X + pairSqBCost BS + undoPlanStepsCost BS + BS.length * (BS.length + 8) + 5

def undoPlanCost (BS : List Bridge) : ℕ := undoPlanStepsCost BS + 2 * BS.length + 1

def reducePiecesCost (V W : Finset Pt) (H : Finset Edge) (BS : List Bridge) : POut → ℕ
  | .merge c =>
    bridgeStatesConnCost W H BS + cellListCost V +
      ((cellList V).map fun X => isGoodMergingCellCost W H BS X + 1).sum + 1 +
      (flipCost + 4 + undoPlanCost BS +
        applyAllCost (undoPlan (bridgeStatesConn W H BS) BS
          (mergePair H (((cellList V).find? (isGoodMergingCell W H BS (bridgeStatesConn W H BS))).getD c))))
  | .odd b => bridgeStatesConnCost W H BS + flipCost * b.r + undoPlanCost BS +
      applyAllCost (undoPlan (bridgeStatesConn W H BS) BS (rowStartPair b)) + 2
  | .twist b => bridgeStatesConnCost W H BS + flipCost * b.r + undoPlanCost BS +
      applyAllCost (undoPlan (bridgeStatesConn W H BS) BS (rowStartPair b)) + 2
  | _ => 1

section undoCost

variable {V W : Finset Pt} {H : Finset Edge} {BS : List Bridge}

lemma bridgeStatesConnCost_le : ∀ (BS : List Bridge) (H : Finset Edge), Inside W H →
    (∀ b ∈ BS, IsCell W b.E) → bridgeStatesConnCost W H BS ≤ (BS.length + 1) * (110 * (W.card + 1) ^ 2)
  | [], _, _, _ => by
    simp only [bridgeStatesConnCost, List.length_nil, zero_add, one_mul]
    have : 1 ≤ (W.card + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
    omega
  | b :: BS, H, hH, hE => by
    have hH' : Inside W (flip H b.E) := inside_flip hH (hE b List.mem_cons_self)
    have ih := bridgeStatesConnCost_le BS (flip H b.E) hH' (fun b' hb' => hE b' (List.mem_cons_of_mem _ hb'))
    have hc := connectedPairsCost_le hH' (W := W)
    have : 1 ≤ (W.card + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
    simp only [bridgeStatesConnCost, List.length_cons]
    unfold flipCost
    nlinarith

lemma mem_planBS {Ss : List (Finset (Pt × Pt))} {BS : List Bridge} {uv : Pt × Pt} {o : Join}
    (ho : o ∈ undoPlan Ss BS uv) : ∃ b ∈ BS, o = lowJ b ∨ o = undoJ b := by
  unfold undoPlan at ho
  generalize undoPlanSteps Ss BS uv = L at ho
  induction BS generalizing L with
  | nil => simp at ho
  | cons b BS ih =>
    cases L with
    | nil => simp at ho
    | cons e L =>
      simp only [List.zipWith_cons_cons, List.mem_cons] at ho
      rcases ho with h | h
      · refine ⟨b, List.mem_cons_self, ?_⟩
        split_ifs at h
        · exact Or.inl h
        · exact Or.inr h
      · obtain ⟨b', hb', h'⟩ := ih L h
        exact ⟨b', List.mem_cons_of_mem _ hb', h'⟩

lemma applyAllCost_planBS_le (hVW : V ⊆ W) (hBS : BS.length ≤ W.card + 1)
    (hr : ∀ b ∈ BS, b.r ≤ V.card + 1) (Ss : List (Finset (Pt × Pt))) (uv : Pt × Pt) :
    applyAllCost (undoPlan Ss BS uv) ≤ 10 * (W.card + 1) ^ 2 := by
  unfold applyAllCost
  have hV := Finset.card_le_card hVW
  have hlen : (undoPlan Ss BS uv).length ≤ W.card + 1 := by
    unfold undoPlan; rw [List.length_zipWith]; omega
  have hs := lsum_le (undoPlan Ss BS uv) (fun o => flipCost * o.n + 1) (8 * (W.card + 1) + 1)
    (fun o ho => by
      obtain ⟨b, hb, h⟩ := mem_planBS ho
      have := hr b hb
      unfold flipCost
      rcases h with rfl | rfl
      · simp only [lowJ]; omega
      · simp only [undoJ]; omega)
  have h1 : (undoPlan Ss BS uv).length * (8 * (W.card + 1) + 1) ≤
      (W.card + 1) * (8 * (W.card + 1) + 1) := Nat.mul_le_mul_right _ hlen
  nlinarith

lemma isGoodMergingCellCost_le (hHW : Inside W H) (hBS : BS.length ≤ W.card + 1) (X : Pt) :
    isGoodMergingCellCost W H BS X ≤ 130 * (W.card + 1) ^ 2 := by
  have hc := cutBCost_le hHW X
  have hm : BS.length * (BS.length + 8) ≤ (W.card + 1) * (W.card + 9) := Nat.mul_le_mul hBS (by omega)
  unfold isGoodMergingCellCost altCost pairSqBCost undoPlanStepsCost
  nlinarith

-- **The fast undo costs `O(|W|³)`.**
--
theorem reducePiecesCost_le (hVW : V ⊆ W) (hI : PhI V W H BS) (hBS : BS.length ≤ W.card + 1)
    {out : POut} (hg : ∀ g, (out = .odd g ∨ out = .twist g) → g.r ≤ V.card + 1) :
    reducePiecesCost V W H BS out ≤ 600 * (W.card + 1) ^ 3 := by
  have hV := Finset.card_le_card hVW
  have hr : ∀ b ∈ BS, b.r ≤ V.card + 1 := fun b hb => (hI.2 b hb).1
  have hE : ∀ b ∈ BS, IsCell W b.E := fun b hb => isCell_mono (hI.2 b hb).2 hVW
  have a2 : 1 ≤ (W.card + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  have a3 : (W.card + 1) ^ 2 ≤ (W.card + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
  have e3 : (W.card + 1) * (W.card + 1) ^ 2 = (W.card + 1) ^ 3 := by ring
  have hcl := cellListCost_le' hVW
  have hsc := bridgeStatesConnCost_le BS H hI.1 hE
  have hsc' : bridgeStatesConnCost W H BS ≤ 220 * (W.card + 1) ^ 3 := by
    have : (BS.length + 1) * (110 * (W.card + 1) ^ 2) ≤ (2 * (W.card + 1)) * (110 * (W.card + 1) ^ 2) :=
      Nat.mul_le_mul_right _ (by omega)
    nlinarith
  cases out with
  | merge c =>
    simp only [reducePiecesCost]
    have hl := length_cellList_le hVW
    have hs := lsum_le (cellList V) (fun X => isGoodMergingCellCost W H BS X + 1) (131 * (W.card + 1) ^ 2)
      (fun x _ => by have := isGoodMergingCellCost_le hI.1 hBS x; omega)
    have h1 : (cellList V).length * (131 * (W.card + 1) ^ 2) ≤
        (W.card + 1) * (131 * (W.card + 1) ^ 2) := Nat.mul_le_mul_right _ (by omega)
    have := applyAllCost_planBS_le hVW hBS hr (bridgeStatesConn W H BS)
      (mergePair H (((cellList V).find? (isGoodMergingCell W H BS (bridgeStatesConn W H BS))).getD c))
    unfold flipCost undoPlanCost undoPlanStepsCost
    nlinarith
  | odd g =>
    simp only [reducePiecesCost]
    have := hg g (Or.inl rfl)
    have := applyAllCost_planBS_le hVW hBS hr (bridgeStatesConn W H BS) (rowStartPair g)
    unfold flipCost undoPlanCost undoPlanStepsCost
    nlinarith
  | twist g =>
    simp only [reducePiecesCost]
    have := hg g (Or.inr rfl)
    have := applyAllCost_planBS_le hVW hBS hr (bridgeStatesConn W H BS) (rowStartPair g)
    unfold flipCost undoPlanCost undoPlanStepsCost
    nlinarith
  | stuck => simp only [reducePiecesCost]; nlinarith
  | fuel => simp only [reducePiecesCost]; nlinarith

end undoCost

end HP

end ULHC
