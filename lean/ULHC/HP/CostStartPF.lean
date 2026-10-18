/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
import ULHC.HP.StartPF
import ULHC.CostDFactor

/-!
# Running time of the whole s–t path algorithm `hpPF`

In the style of ULHC's `CostAlg`: each step charged by an explicit cost function, with
`N = |V| + 1`:

* `D F R b`: `≤ 10 (|F| + |R| + 1)²` (a symmetric difference, a row filter, a sum);
* a fence region (`regionC`, `|cells V| + 1` breadth-first rounds): the `k`-th stage lies in the
  box of radius `k` around the start, so it has at most `(2k + 1)²` points;
* the guided chain: `16 |V| + 1` steps;
* `hpPF`: the d-factor search, then `16 (8 |V| + 1)²` guesses, each a guided chain and a run
  of `fuelPF V` rounds (`runPFCost_fuel_le`).

**`hpPFCost_le : hpPFCost V s t ≤ 10¹² (|V| + 1)²⁴`.**
-/

namespace ULHC

namespace HP

open Finset

def DCost (F R : Finset Edge) : ℕ := 10 * (F.card + R.card + 1) ^ 2

-- `k` breadth-first rounds: each scans the current stage (four neighbours per point) and
-- forms the union.
--
def iterGCost (next : Pt → Finset Pt) (b : Pt) : ℕ → ℕ
  | 0 => 1
  | k + 1 => iterGCost next b k + 40 * (iterG next b k).card + 10

def regionCost (next : Pt → Finset Pt) (V : Finset Pt) (b : Pt) : ℕ :=
  iterGCost next b ((cells V).card + 1) + 20 * (regionC next V b).card + 10

def rflipCost (F : Finset Edge) (R : Finset Pt) : ℕ := 10 * (F.card + 4 * R.card + 1) ^ 2

def stepAtCost (V : Finset Pt) (R : Finset Edge) (F : Finset Edge) (b : Pt) : ℕ :=
  DCost F R + regionCost (ancNext F) V b + regionCost (desNext F) V b +
    rflipCost F (regionC (ancNext F) V b) + rflipCost F (regionC (desNext F) V b) + 10

def guidedStepCost (V : Finset Pt) (s t : Pt) (R : Finset Edge) (F : Finset Edge) : ℕ :=
  8 * (DCost F R + 2) + ∑ b ∈ (epCells s t).toFinset, stepAtCost V R F b + 2

def guidedChainCost (V : Finset Pt) (s t : Pt) (R : Finset Edge) (τ : Pt → ℤ) :
    ℕ → Finset Edge → ℕ
  | 0, F => 8 * (DCost F R + 2) + 2
  | k + 1, F =>
    8 * (DCost F R + 2) + 2 +
      if allMatch s t R τ F then 0
      else guidedStepCost V s t R F +
        match guidedStepC V s t R τ F with
        | some F' => guidedChainCost V s t R τ k F'
        | none => 0

def tauCost : ℕ := 100

def hpPFCost (V : Finset Pt) (s t : Pt) : ℕ :=
  DFC.findFactorCost V (dST s t) + 2 +
    match findFactor V (dST s t) with
    | none => 0
    | some R => ((guessList V s t).map fun g =>
        tauCost + guidedChainCost V s t R (tauOf R s t g) (16 * V.card + 1) R + 2 +
          match guidedChainC V s t R (tauOf R s t g) (16 * V.card + 1) R with
          | some F1 => runPFCost V s t (fuelPF V) F1
          | none => 0).sum

/-! ## Bounds -/

section bounds

variable {V : Finset Pt} {s t : Pt}

def box (b : Pt) (k : ℕ) : Finset Pt := (Icc (b.1 - k) (b.1 + k)) ×ˢ (Icc (b.2 - k) (b.2 + k))

lemma card_box (b : Pt) (k : ℕ) : (box b k).card = (2 * k + 1) ^ 2 := by
  unfold box
  rw [card_product, Int.card_Icc, Int.card_Icc]
  have : (b.1 + k + 1 - (b.1 - k)).toNat = 2 * k + 1 := by omega
  have h2 : (b.2 + k + 1 - (b.2 - k)).toNat = 2 * k + 1 := by omega
  rw [this, h2]; ring

-- Stages of a neighbour-step closure stay in the box of radius `k`.
--
lemma iterG_box {next : Pt → Finset Pt} (hn : ∀ y, ∀ x ∈ next y, ∃ sd, x = nb y sd) (b : Pt) :
    ∀ k, iterG next b k ⊆ box b k := by
  intro k
  induction k with
  | zero =>
    intro x hx; simp only [iterG, mem_singleton] at hx; subst hx
    simp [box]
  | succ k ih =>
    intro x hx
    simp only [iterG, growF, mem_union, mem_biUnion] at hx
    have mono : box b k ⊆ box b (k + 1) := by
      intro y hy; simp only [box, mem_product, mem_Icc] at hy ⊢; push_cast; omega
    rcases hx with hx | ⟨y, hy, hxy⟩
    · exact mono (ih hx)
    · obtain ⟨sd, rfl⟩ := hn y x hxy
      have hy' := ih hy
      simp only [box, mem_product, mem_Icc] at hy' ⊢
      push_cast
      cases sd <;> simp only [nb] <;> omega

lemma ancNext_nb (F : Finset Edge) : ∀ y, ∀ x ∈ ancNext F y, ∃ sd, x = nb y sd := by
  intro y x hx
  unfold ancNext at hx
  obtain ⟨sd, _, rfl⟩ := mem_image.1 hx
  exact ⟨sd, rfl⟩

lemma desNext_nb (F : Finset Edge) : ∀ y, ∀ x ∈ desNext F y, ∃ sd, x = nb y sd := by
  intro y x hx
  unfold desNext at hx
  obtain ⟨sd, _, rfl⟩ := mem_image.1 hx
  exact ⟨sd, rfl⟩

lemma card_iterG_le {next : Pt → Finset Pt} (hn : ∀ y, ∀ x ∈ next y, ∃ sd, x = nb y sd) (b : Pt)
    (k : ℕ) : (iterG next b k).card ≤ (2 * k + 1) ^ 2 := by
  rw [← card_box b k]; exact card_le_card (iterG_box hn b k)

lemma iterGCost_le {next : Pt → Finset Pt} (hn : ∀ y, ∀ x ∈ next y, ∃ sd, x = nb y sd) (b : Pt) :
    ∀ k, iterGCost next b k ≤ 1 + k * (40 * (2 * k + 1) ^ 2 + 10) := by
  intro k
  induction k with
  | zero => simp [iterGCost]
  | succ k ih =>
    simp only [iterGCost]
    have h1 := card_iterG_le hn b k
    have h2 : (2 * k + 1) ^ 2 ≤ (2 * (k + 1) + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
    have h3 : k * (40 * (2 * k + 1) ^ 2 + 10) ≤ k * (40 * (2 * (k + 1) + 1) ^ 2 + 10) :=
      Nat.mul_le_mul_left _ (by omega)
    have e : (k + 1) * (40 * (2 * (k + 1) + 1) ^ 2 + 10) =
        k * (40 * (2 * (k + 1) + 1) ^ 2 + 10) + (40 * (2 * (k + 1) + 1) ^ 2 + 10) := by ring
    rw [e]
    omega

lemma card_cells_le (V : Finset Pt) : (cells V).card ≤ V.card := card_filter_le _ _

lemma regionCost_le {next : Pt → Finset Pt} (hn : ∀ y, ∀ x ∈ next y, ∃ sd, x = nb y sd) (b : Pt) :
    regionCost next V b ≤ 1000 * (V.card + 1) ^ 3 := by
  have hc := card_cells_le V
  unfold regionCost regionC
  set k := (cells V).card + 1
  have h1 := iterGCost_le hn b k
  have h2 := card_iterG_le hn b k
  have hk : k ≤ V.card + 1 := by omega
  have hk2 : 2 * k + 1 ≤ 3 * (V.card + 1) := by omega
  have hsq : (2 * k + 1) ^ 2 ≤ 9 * (V.card + 1) ^ 2 := by
    have := Nat.pow_le_pow_left hk2 2; nlinarith
  have hN : 1 ≤ V.card + 1 := by omega
  have h3 : k * (40 * (2 * k + 1) ^ 2 + 10) ≤ (V.card + 1) * (400 * (V.card + 1) ^ 2) := by
    have : 40 * (2 * k + 1) ^ 2 + 10 ≤ 400 * (V.card + 1) ^ 2 := by
      have : 1 ≤ (V.card + 1) ^ 2 := Nat.one_le_pow _ _ hN
      omega
    exact Nat.mul_le_mul hk this
  have e : (V.card + 1) * (400 * (V.card + 1) ^ 2) = 400 * (V.card + 1) ^ 3 := by ring
  have h4 : 20 * (iterG next b k).card ≤ 180 * (V.card + 1) ^ 2 := by omega
  have h5 : (V.card + 1) ^ 2 ≤ (V.card + 1) ^ 3 := Nat.pow_le_pow_right hN (by omega)
  have h6 : 1 ≤ (V.card + 1) ^ 3 := Nat.one_le_pow _ _ hN
  omega

end bounds

section bounds2

variable {V : Finset Pt} {s t : Pt}

lemma DCost_le {F R : Finset Edge} (hF : F.card ≤ V.card) (hR : R.card ≤ V.card) :
    DCost F R ≤ 40 * (V.card + 1) ^ 2 := by
  unfold DCost
  have : (F.card + R.card + 1) ^ 2 ≤ (2 * (V.card + 1)) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  nlinarith

lemma regionC_card_le {next : Pt → Finset Pt} (hn : ∀ y, ∀ x ∈ next y, ∃ sd, x = nb y sd) (b : Pt) :
    (regionC next V b).card ≤ 9 * (V.card + 1) ^ 2 := by
  have h := card_iterG_le hn b ((cells V).card + 1)
  have hc := card_cells_le V
  have : (2 * ((cells V).card + 1) + 1) ^ 2 ≤ (3 * (V.card + 1)) ^ 2 :=
    Nat.pow_le_pow_left (by omega) 2
  unfold regionC; nlinarith

lemma rflipCost_le {F : Finset Edge} {S : Finset Pt} (hF : F.card ≤ V.card)
    (hS : S.card ≤ 9 * (V.card + 1) ^ 2) : rflipCost F S ≤ 14440 * (V.card + 1) ^ 4 := by
  unfold rflipCost
  have hN : 1 ≤ V.card + 1 := by omega
  have a2 : V.card + 1 ≤ (V.card + 1) ^ 2 := Nat.le_self_pow (by omega) _
  have h1 : F.card + 4 * S.card + 1 ≤ 38 * (V.card + 1) ^ 2 := by
    have : 1 ≤ (V.card + 1) ^ 2 := Nat.one_le_pow _ _ hN
    omega
  have h2 := Nat.pow_le_pow_left h1 2
  have e : (38 * (V.card + 1) ^ 2) ^ 2 = 1444 * (V.card + 1) ^ 4 := by ring
  rw [e] at h2
  omega

lemma stepAtCost_le {R F : Finset Edge} (hF : F.card ≤ V.card) (hR : R.card ≤ V.card) (b : Pt) :
    stepAtCost V R F b ≤ 32000 * (V.card + 1) ^ 4 := by
  have hN : 1 ≤ V.card + 1 := by omega
  have h1 := DCost_le hF hR
  have h2 := regionCost_le (V := V) (ancNext_nb F) b
  have h3 := regionCost_le (V := V) (desNext_nb F) b
  have h4 := rflipCost_le hF (regionC_card_le (V := V) (ancNext_nb F) b)
  have h5 := rflipCost_le hF (regionC_card_le (V := V) (desNext_nb F) b)
  have a2 : (V.card + 1) ^ 2 ≤ (V.card + 1) ^ 4 := Nat.pow_le_pow_right hN (by omega)
  have a3 : (V.card + 1) ^ 3 ≤ (V.card + 1) ^ 4 := Nat.pow_le_pow_right hN (by omega)
  have a0 : 1 ≤ (V.card + 1) ^ 4 := Nat.one_le_pow _ _ hN
  unfold stepAtCost
  omega

lemma guidedStepCost_le {R F : Finset Edge} (hF : F.card ≤ V.card) (hR : R.card ≤ V.card) :
    guidedStepCost V s t R F ≤ 260000 * (V.card + 1) ^ 4 := by
  have hN : 1 ≤ V.card + 1 := by omega
  have h1 := DCost_le hF hR
  have hc : (epCells s t).toFinset.card ≤ 8 :=
    (List.toFinset_card_le _).trans (by simp [epCells])
  have hs : ∑ b ∈ (epCells s t).toFinset, stepAtCost V R F b ≤
      (epCells s t).toFinset.card * (32000 * (V.card + 1) ^ 4) := by
    have := Finset.sum_le_card_nsmul (epCells s t).toFinset (fun b => stepAtCost V R F b) (32000 * (V.card + 1) ^ 4)
      (fun b _ => stepAtCost_le hF hR b)
    simpa using this
  have hs' : (epCells s t).toFinset.card * (32000 * (V.card + 1) ^ 4) ≤
      8 * (32000 * (V.card + 1) ^ 4) := Nat.mul_le_mul_right _ hc
  have a2 : (V.card + 1) ^ 2 ≤ (V.card + 1) ^ 4 := Nat.pow_le_pow_right hN (by omega)
  have a0 : 1 ≤ (V.card + 1) ^ 4 := Nat.one_le_pow _ _ hN
  unfold guidedStepCost
  omega

theorem guidedChainCost_le {R : Finset Edge} {τ : Pt → ℤ} (hR : IsFactor V (dST s t) R) :
    ∀ k (F : Finset Edge), IsFactor V (dST s t) F →
      guidedChainCost V s t R τ k F ≤ (k + 1) * (261000 * (V.card + 1) ^ 4) := by
  have hN : 1 ≤ V.card + 1 := by omega
  have hRc := card_le_factor (dST_le s t) hR
  have a2 : (V.card + 1) ^ 2 ≤ (V.card + 1) ^ 4 := Nat.pow_le_pow_right hN (by omega)
  have a0 : 1 ≤ (V.card + 1) ^ 4 := Nat.one_le_pow _ _ hN
  intro k
  induction k with
  | zero =>
    intro F hF
    have := DCost_le (card_le_factor (dST_le s t) hF) hRc
    simp only [guidedChainCost]
    omega
  | succ k ih =>
    intro F hF
    have hFc := card_le_factor (dST_le s t) hF
    have hd := DCost_le hFc hRc
    have hg := guidedStepCost_le (s := s) (t := t) hFc hRc
    have e : (k + 1 + 1) * (261000 * (V.card + 1) ^ 4) =
        (k + 1) * (261000 * (V.card + 1) ^ 4) + 261000 * (V.card + 1) ^ 4 := by ring
    rw [e]
    simp only [guidedChainCost]
    split
    · omega
    · rcases hs : guidedStepC V s t R τ F with _ | F'
      · simp only; omega
      · simp only
        have := ih F' (guided_factor hF (guidedStepC_guided hs))
        omega

lemma length_guessList : (guessList V s t).length = 16 * (8 * V.card + 1) ^ 2 := by
  unfold guessList
  simp only [List.length_flatMap, List.length_map, edgesAt, vals, List.length_range,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.map_const', List.sum_replicate,
    smul_eq_mul]
  ring

-- **Running time of the whole s–t path algorithm.**
--
theorem hpPFCost_le (hsV : s ∈ V) :
    hpPFCost V s t ≤ 1000000000000 * (V.card + 1) ^ 24 := by
  have hN : 1 ≤ V.card + 1 := by omega
  have hd : ∀ z, z ≠ s → z ≠ t → dST s t z = 2 := fun z h1 h2 => by unfold dST; simp [h1, h2]
  have hds : dST s t s = 1 := by unfold dST; simp
  have h0 := DFC.findFactorCost_le V (dST s t)
  have a3 : (V.card + 1) ^ 3 ≤ (V.card + 1) ^ 24 := Nat.pow_le_pow_right hN (by omega)
  have a0 : 1 ≤ (V.card + 1) ^ 24 := Nat.one_le_pow _ _ hN
  unfold hpPFCost
  split
  · omega
  · rename_i R hR
    have hRf := findFactor_some (dST_le s t) hR
    -- each guess costs at most `5·10⁸ N²²`
    have hper : ∀ g ∈ guessList V s t,
        tauCost + guidedChainCost V s t R (tauOf R s t g) (16 * V.card + 1) R + 2 +
          (match guidedChainC V s t R (tauOf R s t g) (16 * V.card + 1) R with
          | some F1 => runPFCost V s t (fuelPF V) F1
          | none => 0) ≤ 500000000 * (V.card + 1) ^ 22 := by
      intro g _
      have hc := guidedChainCost_le (τ := tauOf R s t g) hRf (16 * V.card + 1) R hRf
      have hk : (16 * V.card + 1 + 1) * (261000 * (V.card + 1) ^ 4) ≤
          (17 * (V.card + 1)) * (261000 * (V.card + 1) ^ 4) := Nat.mul_le_mul_right _ (by omega)
      have e5 : (17 * (V.card + 1)) * (261000 * (V.card + 1) ^ 4) = 4437000 * (V.card + 1) ^ 5 := by
        ring
      have a5 : (V.card + 1) ^ 5 ≤ (V.card + 1) ^ 22 := Nat.pow_le_pow_right hN (by omega)
      have a22 : 1 ≤ (V.card + 1) ^ 22 := Nat.one_le_pow _ _ hN
      split
      · rename_i F1 hF1
        have := runPFCost_fuel_le hd hds hsV F1 (guidedChainC_factor _ R F1 hRf hF1)
        unfold tauCost; omega
      · unfold tauCost; omega
    have hsum := List.sum_le_length_nsmul _ (500000000 * (V.card + 1) ^ 22) (by
      intro x hx
      obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hx
      exact hper g hg)
    rw [List.length_map, length_guessList, smul_eq_mul] at hsum
    have hg2 : 16 * (8 * V.card + 1) ^ 2 ≤ 1024 * (V.card + 1) ^ 2 := by
      have : (8 * V.card + 1) ^ 2 ≤ (8 * (V.card + 1)) ^ 2 := Nat.pow_le_pow_left (by omega) 2
      nlinarith
    have e24 : (V.card + 1) ^ 2 * (V.card + 1) ^ 22 = (V.card + 1) ^ 24 := by rw [← pow_add]
    have hm : 16 * (8 * V.card + 1) ^ 2 * (500000000 * (V.card + 1) ^ 22) ≤
        1024 * (V.card + 1) ^ 2 * (500000000 * (V.card + 1) ^ 22) := Nat.mul_le_mul_right _ hg2
    have e2 : 1024 * (V.card + 1) ^ 2 * (500000000 * (V.card + 1) ^ 22) =
        512000000000 * ((V.card + 1) ^ 2 * (V.card + 1) ^ 22) := by ring
    rw [e2, e24] at hm
    omega

end bounds2

end HP

end ULHC
