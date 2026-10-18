/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
module

public import SolidGridHam.Cycle.CostConn

@[expose] public section

/-!
# Running time, part 4: the starting 2-factor

Costs of the augmenting-path search `twoFactor`: `|V| + 1` augmentations, each building at
most `|V| + 1` alternating layers (subsets of `V`) and walking back down them.
`twoFactorCost_le : twoFactorCost V ≤ 200 N³`.
-/

namespace SolidGridHam

open Finset TF

-- Four forward-step tests (two membership tests in `V`, a colour test, one in `F`), the
-- four `other`s and a set of at most four points.
--
def nbrCost : ℕ := 45

def degCost : ℕ := 8

-- Four backward-step tests (also a membership test in the layer).
--
def predCost : ℕ := 40

def layerAccCost (V : Finset Pt) (F : Finset Edge) : ℕ → ℕ
  | 0 => 13 * V.card
  | k + 1 =>
    layerAccCost V F k +
      match layerAcc V F k with
      | [] => 1
      | L :: _ => ∑ u ∈ L, (nbrCost + (nbr V F u).card) + L.card + (L.biUnion (nbr V F)).card + 1

def walkCost (V : Finset Pt) (F0 : Finset Edge) : List (Finset Pt) → Pt → Finset Edge → ℕ
  | [], _, _ => 1
  | L :: Ls, v, F =>
    2 + if v ∈ L then walkCost V F0 Ls v F
    else predCost +
      match pred V F0 L v with
      | none => 0
      | some e => 2 + walkCost V F0 Ls (other e v) (if Black v then F.erase e else insert e F)

def pickCost (S : Finset Pt) : ℕ := 2 * S.card + 2

def augStepCost (V : Finset Pt) (F : Finset Edge) : ℕ :=
  V.card + 1 + layerAccCost V F V.card +
    match layerAcc V F V.card with
    | [] => 1
    | L :: Ls =>
      ∑ _w ∈ L, (degCost + 3) + pickCost (L.filter (fun w => ¬ Black w ∧ deg F w < 2)) +
        match pick (L.filter (fun w => ¬ Black w ∧ deg F w < 2)) with
        | none => 0
        | some w => walkCost V F Ls w F

def augLoopCost (V : Finset Pt) : ℕ → Finset Edge → ℕ
  | 0, _ => 1
  | n + 1, F =>
    augStepCost V F + 1 +
      match augStep V F with
      | none => 0
      | some F' => augLoopCost V n F'

def twoFactorCost (V : Finset Pt) : ℕ :=
  V.card + 1 + augLoopCost V (V.card + 1) ∅ + V.card * (degCost + 3) + 1

/-! ## Bounds -/

lemma card_nbr_le (V : Finset Pt) (F : Finset Edge) (u : Pt) : (nbr V F u).card ≤ 4 := by
  unfold nbr
  refine (List.toFinset_card_le _).trans ?_
  rw [List.length_map]
  exact (List.length_filter_le _ _).trans (by simp [inc4])

lemma length_layersBelow (V : Finset Pt) (F : Finset Edge) :
    ∀ k, (layersBelow V F k).length = k
  | 0 => rfl
  | k + 1 => by simp [layersBelow, length_layersBelow V F k]

lemma walkCost_le (V : Finset Pt) (F0 : Finset Edge) :
    ∀ (Ls : List (Finset Pt)) (v : Pt) (F : Finset Edge), walkCost V F0 Ls v F ≤ 45 * (Ls.length + 1)
  | [], _, _ => by simp [walkCost]
  | L :: Ls, v, F => by
    simp only [walkCost, List.length_cons]
    by_cases hv : v ∈ L
    · rw [ite_eq_left hv]; have := walkCost_le V F0 Ls v F; omega
    · rw [ite_eq_right hv]
      rcases pred V F0 L v with _ | e
      · simp only; unfold predCost; omega
      · simp only
        have := walkCost_le V F0 Ls (other e v) (if Black v then F.erase e else insert e F)
        unfold predCost; omega

lemma layerAccCost_le (V : Finset Pt) (F : Finset Edge) :
    ∀ k, layerAccCost V F k ≤ 13 * V.card + 55 * (V.card + 1) * k := by
  intro k
  induction k with
  | zero => simp [layerAccCost]
  | succ k ih =>
    simp only [layerAccCost]
    rw [layerAcc_eq]
    simp only
    set L := layer V F k
    have hL : L.card ≤ V.card := card_le_card (layer_sub k)
    have h1 : ∑ u ∈ L, (nbrCost + (nbr V F u).card) ≤ L.card * 49 := by
      have := Finset.sum_le_card_nsmul L (fun u => nbrCost + (nbr V F u).card) 49
        (fun u _ => by have := card_nbr_le V F u; unfold nbrCost; omega)
      simpa using this
    have h2 : (L.biUnion (nbr V F)).card ≤ L.card * 4 := by
      refine card_biUnion_le.trans ?_
      have := Finset.sum_le_card_nsmul L (fun u => (nbr V F u).card) 4
        (fun u _ => card_nbr_le V F u)
      simpa using this
    nlinarith

lemma augStepCost_le (V : Finset Pt) (F : Finset Edge) :
    augStepCost V F ≤ 130 * (V.card + 1) ^ 2 := by
  have h0 := layerAccCost_le V F V.card
  unfold augStepCost
  rw [layerAcc_eq]
  simp only
  set L := layer V F V.card
  have hL : L.card ≤ V.card := card_le_card (layer_sub _)
  have hfl : (L.filter (fun w => ¬ Black w ∧ deg F w < 2)).card ≤ V.card :=
    (card_filter_le _ _).trans hL
  have hw : ∀ w, walkCost V F (layersBelow V F V.card) w F ≤ 45 * (V.card + 1) := fun w => by
    have := walkCost_le V F (layersBelow V F V.card) w F
    rwa [length_layersBelow] at this
  have h3 : (match pick (L.filter (fun w => ¬ Black w ∧ deg F w < 2)) with
      | none => 0
      | some w => walkCost V F (layersBelow V F V.card) w F) ≤ 45 * (V.card + 1) := by
    split
    · omega
    · exact hw _
  simp only [sum_const, smul_eq_mul]
  unfold pickCost degCost
  nlinarith

lemma augLoopCost_le (V : Finset Pt) :
    ∀ n F, augLoopCost V n F ≤ 1 + n * (130 * (V.card + 1) ^ 2 + 1) := by
  intro n
  induction n with
  | zero => intro F; simp [augLoopCost]
  | succ n ih =>
    intro F
    simp only [augLoopCost]
    have h1 := augStepCost_le V F
    split
    · nlinarith
    · rename_i F' _
      have := ih F'
      nlinarith

theorem twoFactorCost_le (V : Finset Pt) : twoFactorCost V ≤ 200 * (V.card + 1) ^ 3 := by
  have := augLoopCost_le V (V.card + 1) ∅
  unfold twoFactorCost degCost
  nlinarith

end SolidGridHam
