/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
module

public import SolidGridHam.Path.Taut
public import SolidGridHam.Path.Prelim.ZeroPF

@[expose] public section

/-!
# Columns and the generalized move (repaired §4.8)

A **column** of length `k + 1` from a critical square `c` in direction `s` is a strip in the
thesis sense, `StripPat F c s (k + 1)`: its squares `c_0 = c, …, c_k` may be strips of one piece or
critical squares between pieces; the edge pattern is the same (docs/STUCK_MINIMAL.md §6). The top
square `c_k` is alternating; with `k` even it is the bottom square of a fixed pair.

The **generalized move** lowers `c_1 … c_k` and keeps `c_0`: `lowerCol F c s k`. Flipping the
whole column is the move followed by flipping `c_0` (`flipCol_eq_flip_lowerCol`).

**Strand pairing** (`lowerCol_count`): the move keeps the number of pieces, and two points that are
not interior column vertices of even height (`IsMid`) are joined after the move iff they were
before. It is the pair step of the odd-strip count, without the final merge at `c_0`.
-/

namespace SolidGridHam

namespace HP

open Finset Classical

-- Flip `c_n, c_(n−1), …, c_1` (not `c_0`).
--
def lowerCol (F : Finset Edge) (c : Pt) (s : Side) : ℕ → Finset Edge
  | 0 => F
  | n + 1 => lowerCol (flip F (cellJ c s (n + 1))) c s n

section column

variable {V : Finset Pt} {c : Pt} {s : Side} {s0 t0 : Pt}

lemma lowerCol_succ (F : Finset Edge) (n : ℕ) :
    lowerCol F c s (n + 1) = lowerCol (flip F (cellJ c s (n + 1))) c s n := rfl

-- Flipping the whole column is the move, then `c_0`.
--
lemma flipCol_eq_flip_lowerCol : ∀ (n : ℕ) (F : Finset Edge),
    flipCol F c s (n + 1) = flip (lowerCol F c s n) c
  | 0, F => by rw [flipCol_succ, cellJ_zero]; rfl
  | n + 1, F => by
    rw [flipCol_succ, flipCol_eq_flip_lowerCol n, lowerCol_succ]

-- **Strand pairing.** Lowering `c_1 … c_k` (`k` even) of a column keeps the number of pieces and
-- every connection between points that are not even-height interior column vertices.
--
theorem lowerCol_count : ∀ k : ℕ, k % 2 = 0 → ∀ F : Finset Edge, Deg2Off V F s0 t0 →
    (∀ j ≤ k, IsCell V (cellJ c s j)) →
    (∀ j ≤ k, ¬ IsCorner s0 (cellJ c s j) ∧ ¬ IsCorner t0 (cellJ c s j)) →
    StripPat F c s (k + 1) →
    ncomp V (lowerCol F c s k) = ncomp V F ∧
      Deg2Off V (lowerCol F c s k) s0 t0 ∧
      ∀ x y, ¬ IsMid c s k x → ¬ IsMid c s k y → (Conn (lowerCol F c s k) x y ↔ Conn F x y) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro hk F hF hcell hcor hpat
  rcases (show k = 0 ∨ 2 ≤ k by omega) with rfl | hk2
  · exact ⟨rfl, hF, fun x y _ _ => Iff.rfl⟩
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 2 := ⟨k - 2, by omega⟩
  have hm : m % 2 = 0 := by omega
  rw [lowerCol_succ, lowerCol_succ]
  set u := cellJ c s (m + 1)
  have hnb : nb u s = cellJ c s (m + 2) := nb_cellJ c s (m + 1)
  obtain ⟨hb, hl, hf⟩ := hpat
  have uL1 : lat1 u s ∈ F := (hl (m + 1) (by omega)).1.2 (by omega)
  have uL2 : lat2 u s ∈ F := (hl (m + 1) (by omega)).2.2 (by omega)
  have uF : front u s ∈ F := (hf (m + 1) (by omega)).2 (by omega)
  have uB : back u s ∉ F := by
    rw [back_cellJ_succ]
    intro h; have := (hf m (by omega)).1 h; omega
  have wL1 : lat1 (nb u s) s ∉ F := by
    rw [hnb]; intro h; have := (hl (m + 2) (by omega)).1.1 h; omega
  have wL2 : lat2 (nb u s) s ∉ F := by
    rw [hnb]; intro h; have := (hl (m + 2) (by omega)).2.1 h; omega
  have wF : front (nb u s) s ∈ F := by
    rw [hnb]; exact (hf (m + 2) (by omega)).2 (by omega)
  have hdouble : flip (flip F (cellJ c s (m + 2))) (cellJ c s (m + 1)) = (mkPair u s).res F := by
    rw [← hnb]; exact pair_flip_eq u s uL1 uL2 wF uB wL1 wL2
  have hcu : IsCell V u := hcell (m + 1) (by omega)
  have hcw : IsCell V (nb u s) := by rw [hnb]; exact hcell (m + 2) (by omega)
  obtain ⟨ub1, ub2, uf1, uf2⟩ := isCell_corners hcu s
  obtain ⟨_, _, wf1, wf2⟩ := isCell_corners hcw s
  obtain ⟨cu1, cu2⟩ := hcor (m + 1) (by omega)
  have nf1s : front1 u s ≠ s0 := fun h => cu1 (h ▸ isCorner_front1 u s)
  have nf1t : front1 u s ≠ t0 := fun h => cu2 (h ▸ isCorner_front1 u s)
  have nf2s : front2 u s ≠ s0 := fun h => cu1 (h ▸ isCorner_front2 u s)
  have nf2t : front2 u s ≠ t0 := fun h => cu2 (h ▸ isCorner_front2 u s)
  obtain ⟨hcount, hrel⟩ := (mkPair u s).flip ub2 uf1 uf2 wf1 uL1 uL2 uF wF
    (hF.2 _ uf1 nf1s nf1t) (hF.2 _ uf2 nf2s nf2t)
  rw [hdouble]
  have hF2' : Deg2Off V ((mkPair u s).res F) s0 t0 := by
    rw [← hdouble]
    have hw : cellJ c s (m + 2) = nb u s := hnb.symm
    have d1 : Deg2Off V (flip F (cellJ c s (m + 2))) s0 t0 := by
      rw [hw]
      exact hF.flip (mkBF (nb u s) s) hcw (mkBF_cellE _ s)
        (by show back (nb u s) s ∈ F; rw [back_nb]; exact uF) wF wL1 wL2
    have m1 : lat1 u s ∈ flip F (cellJ c s (m + 2)) := by
      rw [mem_flip_iff]; have := lat1_not_mem c s (j := m + 1) (m := m + 2) (by omega); tauto
    have m2 : lat2 u s ∈ flip F (cellJ c s (m + 2)) := by
      rw [mem_flip_iff]; have := lat2_not_mem c s (j := m + 1) (m := m + 2) (by omega); tauto
    have m3 : back u s ∉ flip F (cellJ c s (m + 2)) := by
      rw [mem_flip_iff, back_cellJ_succ]
      have := front_not_mem c s (j := m) (m := m + 2) (by omega) (by omega)
      rw [back_cellJ_succ] at uB; tauto
    have m4 : front u s ∉ flip F (cellJ c s (m + 2)) := by
      rw [mem_flip_iff]; have := front_mem_next c s (m + 1); tauto
    exact d1.flip (mkLat u s) hcu (mkLat_cellE u s) m1 m2 m3 m4
  have hpat2 : StripPat ((mkPair u s).res F) c s (m + 1) := by
    rw [← hdouble]; exact pat_flip_pair hm ⟨hb, hl, hf⟩
  obtain ⟨ihc, ihd, ihr⟩ := ih m (by omega) hm _ hF2' (fun j hj => hcell j (by omega))
    (fun j hj => hcor j (by omega)) hpat2
  refine ⟨ihc.trans hcount, ihd, fun x y hx hy => ?_⟩
  have mono : ∀ z, ¬ IsMid c s (m + 2) z → ¬ IsMid c s m z := fun z hz ⟨j, hj1, hj2, hj3⟩ =>
    hz ⟨j, hj1, by omega, hj3⟩
  have off : ∀ z, ¬ IsMid c s (m + 2) z → z ≠ front1 u s ∧ z ≠ front2 u s := fun z hz =>
    ⟨fun h => hz ⟨m + 1, by omega, by omega, Or.inl h⟩,
      fun h => hz ⟨m + 1, by omega, by omega, Or.inr h⟩⟩
  rw [ihr x y (mono x hx) (mono y hy)]
  exact hrel x y (off x hx).1 (off x hx).2 (off y hy).1 (off y hy).2

/-! ## Arcs along a column

Across a side, `H`'s arc depends on the side's membership and the cell's parity (`outArc_eq`);
along a column both alternate, so the arcs repeat: every front arc but the last points the same
way as at `c`, and every lateral arc the opposite way. So the column climbs (or descends) one step
per square, and each square but the last is higher (lower) than its side neighbours. -/

lemma front_arc {F : Finset Edge} {n : ℕ} (hp : StripPat F c s n) {j : ℕ} (hj : j + 1 < n) :
    outArc F (cellJ c s j) s = outArc F c s := by
  obtain ⟨_, _, hf⟩ := hp
  have h0 := hf 0 (by omega)
  have hj' := hf j (by omega)
  rw [cellJ_zero] at h0
  have m0 : decide (sideEdge c s ∈ F) = false := by
    simp only [front] at h0; simp [h0]; omega
  have mj : decide (sideEdge (cellJ c s j) s ∈ F) = decide (j % 2 = 1) := by
    simp only [front] at hj'; simp only [hj', decide_eq_decide]; omega
  rw [outArc_eq, outArc_eq, par_cellJ, mj, m0]
  cases par c <;> cases h : decide (j % 2 = 1) <;> cases s.horiz <;> simp

lemma lat_arcA {F : Finset Edge} {n : ℕ} (hp : StripPat F c s n) {j : ℕ} (hj : j < n) :
    outArc F (cellJ c s j) (latA s) = outArc F c (latA s) := by
  obtain ⟨_, hl, _⟩ := hp
  have h0 := (hl 0 (by omega)).1
  have hj' := (hl j hj).1
  rw [cellJ_zero, lat1_eq] at h0
  rw [lat1_eq] at hj'
  have m0 : decide (sideEdge c (latA s) ∈ F) = false := by simp [h0]
  have mj : decide (sideEdge (cellJ c s j) (latA s) ∈ F) = decide (j % 2 = 1) := by
    simp only [hj']
  rw [outArc_eq, outArc_eq, par_cellJ, mj, m0]
  cases par c <;> cases h : decide (j % 2 = 1) <;> cases (latA s).horiz <;> simp

lemma lat_arcB {F : Finset Edge} {n : ℕ} (hp : StripPat F c s n) {j : ℕ} (hj : j < n) :
    outArc F (cellJ c s j) (latB s) = outArc F c (latB s) := by
  obtain ⟨_, hl, _⟩ := hp
  have h0 := (hl 0 (by omega)).2
  have hj' := (hl j hj).2
  rw [cellJ_zero, lat2_eq] at h0
  rw [lat2_eq] at hj'
  have m0 : decide (sideEdge c (latB s) ∈ F) = false := by simp [h0]
  have mj : decide (sideEdge (cellJ c s j) (latB s) ∈ F) = decide (j % 2 = 1) := by
    simp only [hj']
  rw [outArc_eq, outArc_eq, par_cellJ, mj, m0]
  cases par c <;> cases h : decide (j % 2 = 1) <;> cases (latB s).horiz <;> simp

-- At the first square the lateral arcs point opposite to the front arc.
--
lemma lat_arc_first {F : Finset Edge} {n : ℕ} (hp : StripPat F c s n) (hn : 2 ≤ n) :
    outArc F c (latA s) = !outArc F c s ∧ outArc F c (latB s) = !outArc F c s := by
  obtain ⟨_, hl, hf⟩ := hp
  have h1 := (hl 0 (by omega)).1
  have h2 := (hl 0 (by omega)).2
  have h3 := hf 0 (by omega)
  rw [cellJ_zero, lat1_eq] at h1
  rw [cellJ_zero, lat2_eq] at h2
  rw [cellJ_zero] at h3
  simp only [front] at h3
  have n1 : sideEdge c (latA s) ∉ F := by simp [h1]
  have n2 : sideEdge c (latB s) ∉ F := by simp [h2]
  have n3 : sideEdge c s ∉ F := by simp [h3]; omega
  rw [outArc_eq, outArc_eq, outArc_eq]
  simp only [n1, n2, n3, decide_false]
  cases s <;> cases par c <;> simp [latA, latB, Side.horiz]

/-! ## The move lowers `μ` -/

lemma outArc_congr {F F' : Finset Edge} {c : Pt} {s : Side}
    (h : sideEdge c s ∈ F ↔ sideEdge c s ∈ F') : outArc F c s = outArc F' c s := by
  rw [outArc_eq, outArc_eq]; simp only [h]

lemma sink_of_alt {F : Finset Edge} {c : Pt} {s : Side} (h : Alt F c) (ha : outArc F c s = false) :
    Sink F c := by
  rcases alt_sink_or_source h with hs | hs
  · exact hs
  · have := hs s; rw [ha] at this; exact absurd this (by simp)

-- **The move lowers `μ` by `2k`**: each lowered square is a local maximum with `D > 0` when it is
-- flipped.
--
theorem lowerCol_mu (H' : Finset Edge) : ∀ k : ℕ, k % 2 = 0 → ∀ F : Finset Edge,
    (∀ j ≤ k, IsCell V (cellJ c s j)) → StripPat F c s (k + 1) →
    (∀ j, 1 ≤ j → j ≤ k → 0 < D F H' (cellJ c s j)) →
    (∀ j ≤ k, outArc F (cellJ c s j) (latA s) = false) →
    mu V (lowerCol F c s k) H' + 2 * k = mu V F H' := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro hk F hcell hpat hD harc
  rcases (show k = 0 ∨ 2 ≤ k by omega) with rfl | hk2
  · rfl
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 2 := ⟨k - 2, by omega⟩
  have hm : m % 2 = 0 := by omega
  rw [lowerCol_succ, lowerCol_succ]
  set u := cellJ c s (m + 1)
  set w := cellJ c s (m + 2)
  have hnb : nb u s = w := nb_cellJ c s (m + 1)
  obtain ⟨hb, hl, hf⟩ := hpat
  have uL1 : lat1 u s ∈ F := (hl (m + 1) (by omega)).1.2 (by omega)
  have uL2 : lat2 u s ∈ F := (hl (m + 1) (by omega)).2.2 (by omega)
  have uF : front u s ∈ F := (hf (m + 1) (by omega)).2 (by omega)
  have uB : back u s ∉ F := by
    rw [back_cellJ_succ]
    intro h; have := (hf m (by omega)).1 h; omega
  have wL1 : lat1 w s ∉ F := by
    intro h; have := (hl (m + 2) (by omega)).1.1 h; omega
  have wL2 : lat2 w s ∉ F := by
    intro h; have := (hl (m + 2) (by omega)).2.1 h; omega
  have wF : front w s ∈ F := (hf (m + 2) (by omega)).2 (by omega)
  have wB : back w s ∈ F := by rw [← hnb, back_nb]; exact uF
  have hcu : IsCell V u := hcell (m + 1) (by omega)
  have hcw : IsCell V w := hcell (m + 2) (by omega)
  -- First flip: `w`, a sink with `D > 0`.
  --
  have altw : Alt F w := alt_of_bf wB wF wL1 wL2
  have sinkw : Sink F w := sink_of_alt altw (harc (m + 2) le_rfl)
  have mu1 := mu_flip_sink (V := V) (H := H') hcw sinkw (hD (m + 2) (by omega) le_rfl)
  set F1 := flip F w
  -- Second flip: `u`, a sink with `D > 0` in `F1`.
  --
  have m1 : lat1 u s ∈ F1 := by
    rw [mem_flip_iff]; have := lat1_not_mem c s (j := m + 1) (m := m + 2) (by omega); tauto
  have m2 : lat2 u s ∈ F1 := by
    rw [mem_flip_iff]; have := lat2_not_mem c s (j := m + 1) (m := m + 2) (by omega); tauto
  have m3 : back u s ∉ F1 := by
    rw [mem_flip_iff, back_cellJ_succ]
    have := front_not_mem c s (j := m) (m := m + 2) (by omega) (by omega)
    rw [back_cellJ_succ] at uB; tauto
  have m4 : front u s ∉ F1 := by
    rw [mem_flip_iff]; have := front_mem_next c s (m + 1); tauto
  have altu : Alt F1 u := alt_of_lat m3 m4 m1 m2
  have arcu : outArc F1 u (latA s) = false := by
    rw [← harc (m + 1) (by omega)]
    apply outArc_congr
    rw [← lat1_eq, mem_flip_iff]
    have := lat1_not_mem c s (j := m + 1) (m := m + 2) (by omega); tauto
  have sinku : Sink F1 u := sink_of_alt altu arcu
  have huw : u ≠ w := by
    intro h
    have := congrArg (fun z => z) h
    simp only [u, w] at this
    obtain ⟨x, y⟩ := c
    cases s <;> simp [cellJ] at this
  have hDu : 0 < D F1 H' u := by
    rw [D_flip_alt altw huw]; exact hD (m + 1) (by omega) (by omega)
  have mu2 := mu_flip_sink (V := V) (H := H') hcu sinku hDu
  set F2 := flip F1 u
  -- The rest of the column.
  --
  have hpat2 : StripPat F2 c s (m + 1) := pat_flip_pair hm ⟨hb, hl, hf⟩
  have hne : ∀ j ≤ m, cellJ c s j ≠ u ∧ cellJ c s j ≠ w := by
    intro j hj
    obtain ⟨x, y⟩ := c
    constructor <;> intro h <;> simp only [u, w] at h <;> cases s <;> simp [cellJ] at h <;> omega
  have hD2 : ∀ j, 1 ≤ j → j ≤ m → 0 < D F2 H' (cellJ c s j) := by
    intro j h1 h2
    rw [D_flip_alt altu (hne j h2).1, D_flip_alt altw (hne j h2).2]
    exact hD j h1 (by omega)
  have harc2 : ∀ j ≤ m, outArc F2 (cellJ c s j) (latA s) = false := by
    intro j hj
    rw [← harc j (by omega)]
    apply outArc_congr
    rw [← lat1_eq, mem_flip_iff, mem_flip_iff]
    have a1 := lat1_not_mem c s (j := j) (m := m + 1) (by omega)
    have a2 := lat1_not_mem c s (j := j) (m := m + 2) (by omega)
    tauto
  have := ih m (by omega) hm F2 (fun j hj => hcell j (by omega)) hpat2 hD2 harc2
  omega

lemma source_of_alt {F : Finset Edge} {c : Pt} {s : Side} (h : Alt F c)
    (ha : outArc F c s = true) : Source F c := by
  rcases alt_sink_or_source h with hs | hs
  · have := hs s; rw [ha] at this; exact absurd this (by simp)
  · exact hs

-- **The move (raising a descending column) lowers `μ` by `2k`**: each raised square is a local
-- minimum with `D < 0` when it is flipped.
--
theorem lowerCol_mu_src (H' : Finset Edge) : ∀ k : ℕ, k % 2 = 0 → ∀ F : Finset Edge,
    (∀ j ≤ k, IsCell V (cellJ c s j)) → StripPat F c s (k + 1) →
    (∀ j, 1 ≤ j → j ≤ k → D F H' (cellJ c s j) < 0) →
    (∀ j ≤ k, outArc F (cellJ c s j) (latA s) = true) →
    mu V (lowerCol F c s k) H' + 2 * k = mu V F H' := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro hk F hcell hpat hD harc
  rcases (show k = 0 ∨ 2 ≤ k by omega) with rfl | hk2
  · rfl
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 2 := ⟨k - 2, by omega⟩
  have hm : m % 2 = 0 := by omega
  rw [lowerCol_succ, lowerCol_succ]
  set u := cellJ c s (m + 1)
  set w := cellJ c s (m + 2)
  have hnb : nb u s = w := nb_cellJ c s (m + 1)
  obtain ⟨hb, hl, hf⟩ := hpat
  have uL1 : lat1 u s ∈ F := (hl (m + 1) (by omega)).1.2 (by omega)
  have uL2 : lat2 u s ∈ F := (hl (m + 1) (by omega)).2.2 (by omega)
  have uF : front u s ∈ F := (hf (m + 1) (by omega)).2 (by omega)
  have uB : back u s ∉ F := by
    rw [back_cellJ_succ]
    intro h; have := (hf m (by omega)).1 h; omega
  have wL1 : lat1 w s ∉ F := by
    intro h; have := (hl (m + 2) (by omega)).1.1 h; omega
  have wL2 : lat2 w s ∉ F := by
    intro h; have := (hl (m + 2) (by omega)).2.1 h; omega
  have wF : front w s ∈ F := (hf (m + 2) (by omega)).2 (by omega)
  have wB : back w s ∈ F := by rw [← hnb, back_nb]; exact uF
  have hcu : IsCell V u := hcell (m + 1) (by omega)
  have hcw : IsCell V w := hcell (m + 2) (by omega)
  -- First flip: `w`, a sink with `D > 0`.
  --
  have altw : Alt F w := alt_of_bf wB wF wL1 wL2
  have srcw : Source F w := source_of_alt altw (harc (m + 2) le_rfl)
  have mu1 := mu_flip_source (V := V) (H := H') hcw srcw (hD (m + 2) (by omega) le_rfl)
  set F1 := flip F w
  -- Second flip: `u`, a sink with `D > 0` in `F1`.
  --
  have m1 : lat1 u s ∈ F1 := by
    rw [mem_flip_iff]; have := lat1_not_mem c s (j := m + 1) (m := m + 2) (by omega); tauto
  have m2 : lat2 u s ∈ F1 := by
    rw [mem_flip_iff]; have := lat2_not_mem c s (j := m + 1) (m := m + 2) (by omega); tauto
  have m3 : back u s ∉ F1 := by
    rw [mem_flip_iff, back_cellJ_succ]
    have := front_not_mem c s (j := m) (m := m + 2) (by omega) (by omega)
    rw [back_cellJ_succ] at uB; tauto
  have m4 : front u s ∉ F1 := by
    rw [mem_flip_iff]; have := front_mem_next c s (m + 1); tauto
  have altu : Alt F1 u := alt_of_lat m3 m4 m1 m2
  have arcu : outArc F1 u (latA s) = true := by
    rw [← harc (m + 1) (by omega)]
    apply outArc_congr
    rw [← lat1_eq, mem_flip_iff]
    have := lat1_not_mem c s (j := m + 1) (m := m + 2) (by omega); tauto
  have srcu : Source F1 u := source_of_alt altu arcu
  have huw : u ≠ w := by
    intro h
    have := congrArg (fun z => z) h
    simp only [u, w] at this
    obtain ⟨x, y⟩ := c
    cases s <;> simp [cellJ] at this
  have hDu : D F1 H' u < 0 := by
    rw [D_flip_alt altw huw]; exact hD (m + 1) (by omega) (by omega)
  have mu2 := mu_flip_source (V := V) (H := H') hcu srcu hDu
  set F2 := flip F1 u
  -- The rest of the column.
  --
  have hpat2 : StripPat F2 c s (m + 1) := pat_flip_pair hm ⟨hb, hl, hf⟩
  have hne : ∀ j ≤ m, cellJ c s j ≠ u ∧ cellJ c s j ≠ w := by
    intro j hj
    obtain ⟨x, y⟩ := c
    constructor <;> intro h <;> simp only [u, w] at h <;> cases s <;> simp [cellJ] at h <;> omega
  have hD2 : ∀ j, 1 ≤ j → j ≤ m → D F2 H' (cellJ c s j) < 0 := by
    intro j h1 h2
    rw [D_flip_alt altu (hne j h2).1, D_flip_alt altw (hne j h2).2]
    exact hD j h1 (by omega)
  have harc2 : ∀ j ≤ m, outArc F2 (cellJ c s j) (latA s) = true := by
    intro j hj
    rw [← harc j (by omega)]
    apply outArc_congr
    rw [← lat1_eq, mem_flip_iff, mem_flip_iff]
    have a1 := lat1_not_mem c s (j := j) (m := m + 1) (by omega)
    have a2 := lat1_not_mem c s (j := j) (m := m + 2) (by omega)
    tauto
  have := ih m (by omega) hm F2 (fun j hj => hcell j (by omega)) hpat2 hD2 harc2
  omega

-- **`D` after the move** (climbing column): each lowered square loses 2, nothing else changes.
--
theorem lowerCol_D (H' : Finset Edge) : ∀ k : ℕ, k % 2 = 0 → ∀ F : Finset Edge,
    StripPat F c s (k + 1) → (∀ j ≤ k, outArc F (cellJ c s j) (latA s) = false) →
    ∀ x, D (lowerCol F c s k) H' x =
      D F H' x - (if ∃ j, 1 ≤ j ∧ j ≤ k ∧ x = cellJ c s j then 2 else 0) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro hk F hpat harc x
  rcases (show k = 0 ∨ 2 ≤ k by omega) with rfl | hk2
  · simp [lowerCol]
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 2 := ⟨k - 2, by omega⟩
  have hm : m % 2 = 0 := by omega
  rw [lowerCol_succ, lowerCol_succ]
  set u := cellJ c s (m + 1)
  set w := cellJ c s (m + 2)
  have hnb : nb u s = w := nb_cellJ c s (m + 1)
  obtain ⟨hb, hl, hf⟩ := hpat
  have uL1 : lat1 u s ∈ F := (hl (m + 1) (by omega)).1.2 (by omega)
  have uL2 : lat2 u s ∈ F := (hl (m + 1) (by omega)).2.2 (by omega)
  have uF : front u s ∈ F := (hf (m + 1) (by omega)).2 (by omega)
  have uB : back u s ∉ F := by
    rw [back_cellJ_succ]
    intro h; have := (hf m (by omega)).1 h; omega
  have wL1 : lat1 w s ∉ F := by
    intro h; have := (hl (m + 2) (by omega)).1.1 h; omega
  have wL2 : lat2 w s ∉ F := by
    intro h; have := (hl (m + 2) (by omega)).2.1 h; omega
  have wF : front w s ∈ F := (hf (m + 2) (by omega)).2 (by omega)
  have wB : back w s ∈ F := by rw [← hnb, back_nb]; exact uF
  have altw : Alt F w := alt_of_bf wB wF wL1 wL2
  have sinkw : Sink F w := sink_of_alt altw (harc (m + 2) le_rfl)
  set F1 := flip F w
  have m1 : lat1 u s ∈ F1 := by
    rw [mem_flip_iff]; have := lat1_not_mem c s (j := m + 1) (m := m + 2) (by omega); tauto
  have m2 : lat2 u s ∈ F1 := by
    rw [mem_flip_iff]; have := lat2_not_mem c s (j := m + 1) (m := m + 2) (by omega); tauto
  have m3 : back u s ∉ F1 := by
    rw [mem_flip_iff, back_cellJ_succ]
    have := front_not_mem c s (j := m) (m := m + 2) (by omega) (by omega)
    rw [back_cellJ_succ] at uB; tauto
  have m4 : front u s ∉ F1 := by
    rw [mem_flip_iff]; have := front_mem_next c s (m + 1); tauto
  have altu : Alt F1 u := alt_of_lat m3 m4 m1 m2
  have arcu : outArc F1 u (latA s) = false := by
    rw [← harc (m + 1) (by omega)]
    apply outArc_congr
    rw [← lat1_eq, mem_flip_iff]
    have := lat1_not_mem c s (j := m + 1) (m := m + 2) (by omega); tauto
  have sinku : Sink F1 u := sink_of_alt altu arcu
  set F2 := flip F1 u
  have hpat2 : StripPat F2 c s (m + 1) := pat_flip_pair hm ⟨hb, hl, hf⟩
  have harc2 : ∀ j ≤ m, outArc F2 (cellJ c s j) (latA s) = false := by
    intro j hj
    rw [← harc j (by omega)]
    apply outArc_congr
    rw [← lat1_eq, mem_flip_iff, mem_flip_iff]
    have a1 := lat1_not_mem c s (j := j) (m := m + 1) (by omega)
    have a2 := lat1_not_mem c s (j := j) (m := m + 2) (by omega)
    tauto
  rw [ih m (by omega) hm F2 hpat2 harc2 x, D_flip_sink sinku x, D_flip_sink sinkw x]
  have inj : ∀ {a b : ℕ}, cellJ c s a = cellJ c s b → a = b := by
    intro a b h
    obtain ⟨x0, y0⟩ := c
    cases s <;> simp [cellJ] at h <;> omega
  have key : (∃ j, 1 ≤ j ∧ j ≤ m + 2 ∧ x = cellJ c s j) ↔
      ((∃ j, 1 ≤ j ∧ j ≤ m ∧ x = cellJ c s j) ∨ x = u ∨ x = w) := by
    constructor
    · rintro ⟨j, h3, h4, h5⟩
      rcases (show j ≤ m ∨ j = m + 1 ∨ j = m + 2 by omega) with h | rfl | rfl
      · exact Or.inl ⟨j, h3, h, h5⟩
      · exact Or.inr (Or.inl h5)
      · exact Or.inr (Or.inr h5)
    · rintro (⟨j, h3, h4, h5⟩ | h | h)
      · exact ⟨j, h3, by omega, h5⟩
      · exact ⟨m + 1, by omega, by omega, h⟩
      · exact ⟨m + 2, by omega, le_rfl, h⟩
  have ex : ¬ ((∃ j, 1 ≤ j ∧ j ≤ m ∧ x = cellJ c s j) ∧ (x = u ∨ x = w)) := by
    rintro ⟨⟨j, _, h4, h5⟩, h | h⟩ <;> rw [h5] at h <;> have := inj h <;> omega
  have uw : ¬ (x = u ∧ x = w) := by
    rintro ⟨h1, h2⟩; rw [h1] at h2; have := inj h2; omega
  have e1 : (if ∃ j, 1 ≤ j ∧ j ≤ m + 2 ∧ x = cellJ c s j then (2 : ℤ) else 0) =
      (if ∃ j, 1 ≤ j ∧ j ≤ m ∧ x = cellJ c s j then 2 else 0) + (if x = u then 2 else 0) +
        (if x = w then 2 else 0) := by
    by_cases hA : ∃ j, 1 ≤ j ∧ j ≤ m ∧ x = cellJ c s j
    · rw [ite_eq_left (key.2 (Or.inl hA)), ite_eq_left hA,
        ite_eq_right (fun h => ex ⟨hA, Or.inl h⟩), ite_eq_right (fun h => ex ⟨hA, Or.inr h⟩)]; norm_num
    · rw [ite_eq_right hA]
      by_cases hu : x = u
      · rw [ite_eq_left (key.2 (Or.inr (Or.inl hu))), ite_eq_left hu, ite_eq_right (fun h => uw ⟨hu, h⟩)]
        norm_num
      · rw [ite_eq_right hu]
        by_cases hw : x = w
        · rw [ite_eq_left (key.2 (Or.inr (Or.inr hw))), ite_eq_left hw]; norm_num
        · rw [ite_eq_right hw, ite_eq_right (fun h => by rcases key.1 h with h | h | h <;> contradiction)]
          norm_num
  rw [e1]; ring

-- **`D` after the move** (descending column): each raised square gains 2, nothing else changes.
--
theorem lowerCol_D_src (H' : Finset Edge) : ∀ k : ℕ, k % 2 = 0 → ∀ F : Finset Edge,
    StripPat F c s (k + 1) → (∀ j ≤ k, outArc F (cellJ c s j) (latA s) = true) →
    ∀ x, D (lowerCol F c s k) H' x =
      D F H' x + (if ∃ j, 1 ≤ j ∧ j ≤ k ∧ x = cellJ c s j then 2 else 0) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro hk F hpat harc x
  rcases (show k = 0 ∨ 2 ≤ k by omega) with rfl | hk2
  · simp [lowerCol]
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 2 := ⟨k - 2, by omega⟩
  have hm : m % 2 = 0 := by omega
  rw [lowerCol_succ, lowerCol_succ]
  set u := cellJ c s (m + 1)
  set w := cellJ c s (m + 2)
  have hnb : nb u s = w := nb_cellJ c s (m + 1)
  obtain ⟨hb, hl, hf⟩ := hpat
  have uL1 : lat1 u s ∈ F := (hl (m + 1) (by omega)).1.2 (by omega)
  have uL2 : lat2 u s ∈ F := (hl (m + 1) (by omega)).2.2 (by omega)
  have uF : front u s ∈ F := (hf (m + 1) (by omega)).2 (by omega)
  have uB : back u s ∉ F := by
    rw [back_cellJ_succ]
    intro h; have := (hf m (by omega)).1 h; omega
  have wL1 : lat1 w s ∉ F := by
    intro h; have := (hl (m + 2) (by omega)).1.1 h; omega
  have wL2 : lat2 w s ∉ F := by
    intro h; have := (hl (m + 2) (by omega)).2.1 h; omega
  have wF : front w s ∈ F := (hf (m + 2) (by omega)).2 (by omega)
  have wB : back w s ∈ F := by rw [← hnb, back_nb]; exact uF
  have altw : Alt F w := alt_of_bf wB wF wL1 wL2
  have sinkw : Source F w := source_of_alt altw (harc (m + 2) le_rfl)
  set F1 := flip F w
  have m1 : lat1 u s ∈ F1 := by
    rw [mem_flip_iff]; have := lat1_not_mem c s (j := m + 1) (m := m + 2) (by omega); tauto
  have m2 : lat2 u s ∈ F1 := by
    rw [mem_flip_iff]; have := lat2_not_mem c s (j := m + 1) (m := m + 2) (by omega); tauto
  have m3 : back u s ∉ F1 := by
    rw [mem_flip_iff, back_cellJ_succ]
    have := front_not_mem c s (j := m) (m := m + 2) (by omega) (by omega)
    rw [back_cellJ_succ] at uB; tauto
  have m4 : front u s ∉ F1 := by
    rw [mem_flip_iff]; have := front_mem_next c s (m + 1); tauto
  have altu : Alt F1 u := alt_of_lat m3 m4 m1 m2
  have arcu : outArc F1 u (latA s) = true := by
    rw [← harc (m + 1) (by omega)]
    apply outArc_congr
    rw [← lat1_eq, mem_flip_iff]
    have := lat1_not_mem c s (j := m + 1) (m := m + 2) (by omega); tauto
  have sinku : Source F1 u := source_of_alt altu arcu
  set F2 := flip F1 u
  have hpat2 : StripPat F2 c s (m + 1) := pat_flip_pair hm ⟨hb, hl, hf⟩
  have harc2 : ∀ j ≤ m, outArc F2 (cellJ c s j) (latA s) = true := by
    intro j hj
    rw [← harc j (by omega)]
    apply outArc_congr
    rw [← lat1_eq, mem_flip_iff, mem_flip_iff]
    have a1 := lat1_not_mem c s (j := j) (m := m + 1) (by omega)
    have a2 := lat1_not_mem c s (j := j) (m := m + 2) (by omega)
    tauto
  rw [ih m (by omega) hm F2 hpat2 harc2 x, D_flip_source sinku x, D_flip_source sinkw x]
  have inj : ∀ {a b : ℕ}, cellJ c s a = cellJ c s b → a = b := by
    intro a b h
    obtain ⟨x0, y0⟩ := c
    cases s <;> simp [cellJ] at h <;> omega
  have key : (∃ j, 1 ≤ j ∧ j ≤ m + 2 ∧ x = cellJ c s j) ↔
      ((∃ j, 1 ≤ j ∧ j ≤ m ∧ x = cellJ c s j) ∨ x = u ∨ x = w) := by
    constructor
    · rintro ⟨j, h3, h4, h5⟩
      rcases (show j ≤ m ∨ j = m + 1 ∨ j = m + 2 by omega) with h | rfl | rfl
      · exact Or.inl ⟨j, h3, h, h5⟩
      · exact Or.inr (Or.inl h5)
      · exact Or.inr (Or.inr h5)
    · rintro (⟨j, h3, h4, h5⟩ | h | h)
      · exact ⟨j, h3, by omega, h5⟩
      · exact ⟨m + 1, by omega, by omega, h⟩
      · exact ⟨m + 2, by omega, le_rfl, h⟩
  have ex : ¬ ((∃ j, 1 ≤ j ∧ j ≤ m ∧ x = cellJ c s j) ∧ (x = u ∨ x = w)) := by
    rintro ⟨⟨j, _, h4, h5⟩, h | h⟩ <;> rw [h5] at h <;> have := inj h <;> omega
  have uw : ¬ (x = u ∧ x = w) := by
    rintro ⟨h1, h2⟩; rw [h1] at h2; have := inj h2; omega
  have e1 : (if ∃ j, 1 ≤ j ∧ j ≤ m + 2 ∧ x = cellJ c s j then (2 : ℤ) else 0) =
      (if ∃ j, 1 ≤ j ∧ j ≤ m ∧ x = cellJ c s j then 2 else 0) + (if x = u then 2 else 0) +
        (if x = w then 2 else 0) := by
    by_cases hA : ∃ j, 1 ≤ j ∧ j ≤ m ∧ x = cellJ c s j
    · rw [ite_eq_left (key.2 (Or.inl hA)), ite_eq_left hA,
        ite_eq_right (fun h => ex ⟨hA, Or.inl h⟩), ite_eq_right (fun h => ex ⟨hA, Or.inr h⟩)]; norm_num
    · rw [ite_eq_right hA]
      by_cases hu : x = u
      · rw [ite_eq_left (key.2 (Or.inr (Or.inl hu))), ite_eq_left hu, ite_eq_right (fun h => uw ⟨hu, h⟩)]
        norm_num
      · rw [ite_eq_right hu]
        by_cases hw : x = w
        · rw [ite_eq_left (key.2 (Or.inr (Or.inr hw))), ite_eq_left hw]; norm_num
        · rw [ite_eq_right hw, ite_eq_right (fun h => by rcases key.1 h with h | h | h <;> contradiction)]
          norm_num
  rw [e1]; ring

end column

end HP

end SolidGridHam
