/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
import SolidGridHam.Path.CaseB

/-!
# SideRun (docs/S4_UNDO.md §II.4, B3)

The side line of a frozen bridge: squares `S 0 … S (r−1)` beside the bridge squares, their sides
toward `a` being outer edges `O t` (dark iff `t` even), and `S 0`, `S (r−1)` cut. A row running
along this line (direction `a` or `a.opp`) whose arcs turn after `n` squares contains one of the cut
end squares as a non-start square: its start is `S t`, the run's fronts follow the outer edges, so
the arcs agree until the end square.
-/

namespace SolidGridHam

namespace HP

open Finset Classical

lemma cellJ_back' (c : Pt) (a : Side) {j k : ℕ} (h : k ≤ j) :
    cellJ (cellJ c a.opp j) a k = cellJ c a.opp (j - k) := by
  have := cellJ_back c a.opp h
  rwa [opp_opp] at this

section siderun

variable {V : Finset Pt} {F : Finset Edge} {BS : List Bridge}

-- **SideRun**, along the side line in direction `a` (upward).
--
theorem sideRun_up {S : ℕ → Pt} {O : ℕ → Edge} {a : Side} {r : ℕ} (hr : 2 ≤ r)
    (hup : ∀ t u, cellJ (S t) a u = S (t + u))
    (hfront : ∀ t, t + 2 ≤ r → sideEdge (S t) a = O t)
    (hback : ∀ t, 1 ≤ t → t + 2 ≤ r → sideEdge (S t) a.opp = O (t - 1))
    (hO : ∀ t, t + 2 ≤ r → (O t ∈ F ↔ t % 2 = 0))
    (_hcut0 : CutSq F (S 0)) (hcutE : CutSq F (S (r - 1)))
    {q : Pt} {n : ℕ} (hrow : RowAt V F BS q a n)
    (hlast : outArc F (cellJ q a (n - 1)) a ≠ outArc F q a)
    {t : ℕ} (ht : t + 2 ≤ r) (hq : q = S t) : False := by
  have two := hrow.two
  subst hq
  rcases Nat.eq_zero_or_pos t with h0 | hpos
  · -- `S 0` going up: its front `O 0` is dark, but a start's front is light
    subst h0
    have hf : front (S 0) a ∈ F := by unfold front; rw [hfront 0 (by omega)]; exact (hO 0 (by omega)).2 rfl
    rcases hrow.crit.2.2.2 with ⟨_, h2⟩ | ⟨_, h1⟩
    · exact h2 hf
    · exact h1 hrow.bk
  -- the start's back `O (t − 1)` is dark, so `t` is odd
  have hb : O (t - 1) ∈ F := by rw [← hback t hpos ht]; exact hrow.bk
  have todd : t % 2 = 1 := by have := (hO (t - 1) (by omega)).1 hb; omega
  -- the run's fronts follow the outer edges
  have hf0 : front (S t) a ∉ F := by
    unfold front; rw [hfront t ht]; intro h; have := (hO t ht).1 h; omega
  have harc : ∀ u, t + u + 2 ≤ r → outArc F (cellJ (S t) a u) a = outArc F (S t) a := by
    intro u hu
    apply run_front' hf0
    unfold front; rw [hup, hfront (t + u) hu, hO (t + u) hu]; omega
  -- so the row reaches `S (r − 1)`
  have hn : r - 1 - t ≤ n - 1 := by
    by_contra hlt
    exact hlast (harc (n - 1) (by omega))
  have hcell := hrow.uncut (r - 1 - t) (by omega) (by omega)
  rw [hup, show t + (r - 1 - t) = r - 1 by omega] at hcell
  exact hcell hcutE

-- **SideRun**, along the side line in direction `a.opp` (downward).
--
theorem sideRun_down {S : ℕ → Pt} {O : ℕ → Edge} {a : Side} {r : ℕ} (hr : 2 ≤ r)
    (hdown : ∀ t u, u ≤ t → cellJ (S t) a.opp u = S (t - u))
    (hfront : ∀ t, t + 2 ≤ r → sideEdge (S t) a = O t)
    (hback : ∀ t, 1 ≤ t → t + 2 ≤ r → sideEdge (S t) a.opp = O (t - 1))
    (hO : ∀ t, t + 2 ≤ r → (O t ∈ F ↔ t % 2 = 0))
    (hcut0 : CutSq F (S 0)) (hEfront : sideEdge (S (r - 1)) a.opp ∈ F)
    {q : Pt} {n : ℕ} (hrow : RowAt V F BS q a.opp n)
    (hlast : outArc F (cellJ q a.opp (n - 1)) a.opp ≠ outArc F q a.opp)
    {t : ℕ} (ht : 1 ≤ t) (ht' : t ≤ r - 1) (hq : q = S t) : False := by
  have two := hrow.two
  subst hq
  rcases (show t = r - 1 ∨ t + 2 ≤ r by omega) with htE | ht2
  · -- `S (r − 1)` going down: its front is dark
    subst htE
    rcases hrow.crit.2.2.2 with ⟨_, h2⟩ | ⟨_, h1⟩
    · exact h2 hEfront
    · exact h1 hrow.bk
  -- the start's back `O t` is dark, so `t` is even
  have hb : O t ∈ F := by
    rw [← hfront t ht2]; have := hrow.bk; unfold back at this; rwa [opp_opp] at this
  have tev : t % 2 = 0 := (hO t ht2).1 hb
  have hf0 : front (S t) a.opp ∉ F := by
    unfold front; rw [hback t ht ht2]; intro h; have := (hO (t - 1) (by omega)).1 h; omega
  have harc : ∀ u, u + 1 ≤ t → outArc F (cellJ (S t) a.opp u) a.opp = outArc F (S t) a.opp := by
    intro u hu
    apply run_front' hf0
    unfold front; rw [hdown t u (by omega), hback (t - u) (by omega) (by omega),
      hO (t - u - 1) (by omega)]; omega
  have hn : t ≤ n - 1 := by
    by_contra hlt
    exact hlast (harc (n - 1) (by omega))
  have hcell := hrow.uncut t (by omega) (by omega)
  rw [hdown t t le_rfl, Nat.sub_self] at hcell
  exact hcell hcut0

-- The side line of a frozen bridge, on side `ℓ`, with its facts.
--
structure SideLine (F : Finset Edge) (b : Bridge) (ℓ : Side) (S : ℕ → Pt) (O : ℕ → Edge) : Prop where
  hS : ∀ t, S t = nb (b.cell t) ℓ
  up : ∀ t u, cellJ (S t) b.a u = S (t + u)
  down : ∀ t u, u ≤ t → cellJ (S t) b.a.opp u = S (t - u)
  front : ∀ t, t + 2 ≤ b.r → sideEdge (S t) b.a = O t
  back : ∀ t, 1 ≤ t → t + 2 ≤ b.r → sideEdge (S t) b.a.opp = O (t - 1)
  hO : ∀ t, t + 2 ≤ b.r → (O t ∈ F ↔ t % 2 = 0)
  cut0 : CutSq F (S 0)
  cutE : CutSq F (S (b.r - 1))
  efront : sideEdge (S (b.r - 1)) b.a.opp ∈ F
  near : ∀ t, sideEdge (S t) ℓ.opp = sideEdge (b.cell t) ℓ

lemma sideLine_A {F : Finset Edge} {b : Bridge} (hR : RegionOK F b) (htwo : 2 ≤ b.r)
    (hev : b.r % 2 = 0) :
    SideLine F b (latA b.a) (fun t => nb (b.cell t) (latA b.a))
      (fun t => outer1 (b.cell t) b.a) := by
  have hE : b.E = b.cell (b.r - 1) := rfl
  refine ⟨fun _ => rfl, fun t u => ?_, fun t u hu => ?_, fun t _ => ?_, fun t h1 _ => ?_,
    fun t ht => (hR.outer t ht).1, ?_, ?_, ?_, fun t => ?_⟩
  · simp only [Bridge.cell]; rw [cellJ_nb_any, cellJ_add]
  · simp only [Bridge.cell]; rw [cellJ_nb_any, cellJ_back _ _ hu]
  · rw [← front, side_front]
  · simp only [Bridge.cell]; exact side_backA b.q b.a h1
  · refine cutSq_of_corners (isCorner_back2 _ b.a) (isCorner_front2 _ b.a) ?_
    show ¬ Conn F (back2 (nb (b.cell 0) (latA b.a)) b.a) (front2 (nb (b.cell 0) (latA b.a)) b.a)
    rw [sideA_back2, sideA_front2]
    unfold Bridge.cell; rw [cellJ_zero]; exact hR.cut0
  · refine cutSq_of_corners (isCorner_back2 _ b.a) (isCorner_front2 _ b.a) ?_
    show ¬ Conn F (back2 (nb (b.cell (b.r - 1)) (latA b.a)) b.a)
      (front2 (nb (b.cell (b.r - 1)) (latA b.a)) b.a)
    rw [sideA_back2, sideA_front2, ← hE]; exact hR.cutE
  · simp only [Bridge.cell]
    rw [side_backA b.q b.a (by omega), show b.r - 1 - 1 = b.r - 2 by omega]
    have := (hR.outer (b.r - 2) (by omega)).1.2 (by omega); unfold Bridge.cell at this; exact this
  · show sideEdge (nb (b.cell t) _) _ = _; rw [sideEdge_nb_opp]

lemma sideLine_B {F : Finset Edge} {b : Bridge} (hR : RegionOK F b) (htwo : 2 ≤ b.r)
    (hev : b.r % 2 = 0) :
    SideLine F b (latB b.a) (fun t => nb (b.cell t) (latB b.a))
      (fun t => outer2 (b.cell t) b.a) := by
  have hE : b.E = b.cell (b.r - 1) := rfl
  obtain ⟨_, c2⟩ := cutE_both hR htwo
  refine ⟨fun _ => rfl, fun t u => ?_, fun t u hu => ?_, fun t _ => ?_, fun t h1 _ => ?_,
    fun t ht => (hR.outer t ht).2, ?_, ?_, ?_, fun t => ?_⟩
  · simp only [Bridge.cell]; rw [cellJ_nb_any, cellJ_add]
  · simp only [Bridge.cell]; rw [cellJ_nb_any, cellJ_back _ _ hu]
  · rw [← front, sideB_front]
  · simp only [Bridge.cell]; exact side_backB b.q b.a h1
  · refine cutSq_of_corners (isCorner_back1 _ b.a) (isCorner_front1 _ b.a) ?_
    show ¬ Conn F (back1 (nb (b.cell 0) (latB b.a)) b.a) (front1 (nb (b.cell 0) (latB b.a)) b.a)
    rw [sideB_back1, sideB_front1]
    unfold Bridge.cell; rw [cellJ_zero]; exact hR.cut0'
  · refine cutSq_of_corners (isCorner_back1 _ b.a) (isCorner_front1 _ b.a) ?_
    show ¬ Conn F (back1 (nb (b.cell (b.r - 1)) (latB b.a)) b.a)
      (front1 (nb (b.cell (b.r - 1)) (latB b.a)) b.a)
    rw [sideB_back1, sideB_front1, ← hE]; exact c2
  · simp only [Bridge.cell]
    rw [side_backB b.q b.a (by omega), show b.r - 1 - 1 = b.r - 2 by omega]
    have := (hR.outer (b.r - 2) (by omega)).2.2 (by omega); unfold Bridge.cell at this; exact this
  · show sideEdge (nb (b.cell t) _) _ = _; rw [sideEdge_nb_opp]

lemma par_of_lat {a ℓ c : Side} (hℓ : ℓ = latA c ∨ ℓ = latB c)
    (h : latA a = ℓ.opp ∨ latB a = ℓ.opp) : a = c ∨ a = c.opp := by
  cases a <;> cases c <;> cases ℓ <;> simp_all [latA, latB, Side.opp]

-- In a frame perpendicular to `c`, the laterals of a cell are its sides toward `c` and `c.opp`.
--
lemma lats_perp' {Y : Pt} {a c : Side}
    (h : a = latA c ∨ a = latB c ∨ a = (latA c).opp ∨ a = (latB c).opp) :
    (lat1 Y a = sideEdge Y c ∧ lat2 Y a = sideEdge Y c.opp) ∨
      (lat1 Y a = sideEdge Y c.opp ∧ lat2 Y a = sideEdge Y c) := by
  rw [lat1_eq, lat2_eq]
  cases a <;> cases c <;> simp_all [latA, latB, Side.opp]

lemma cellJ_start (q : Pt) (a : Side) (j : ℕ) : cellJ (cellJ q a j) a.opp j = q := by
  rw [cellJ_back _ _ le_rfl, Nat.sub_self, cellJ_zero]

-- **Case B3.**
--
theorem caseB3 {F : Finset Edge} {b : Bridge} {ℓ : Side} {S : ℕ → Pt} {O : ℕ → Edge}
    (hsl : SideLine F b ℓ S O) (hℓ : ℓ = latA b.a ∨ ℓ = latB b.a) (htwo : 2 ≤ b.r)
    {q : Pt} {a : Side} {n : ℕ} (hrow : RowAt V F BS q a n)
    (hlastArc : outArc F (cellJ q a (n - 1)) a ≠ outArc F q a) {nO : ℕ}
    (hnO : nO + 1 = n ∨ nO = n) (hEavoid : nO < n → ∀ l < b.r, cellJ q a (n - 1) ≠ b.cell l)
    (hlast : nO = n →
      (lat1 (cellJ q a (n - 1)) a ∉ F ∧ lat2 (cellJ q a (n - 1)) a ∉ F) ∨
      (lat1 (cellJ q a (n - 1)) a ∈ F ∧ lat2 (cellJ q a (n - 1)) a ∈ F))
    {j : ℕ} (hj : j < nO) {m : ℕ} (hm1 : 1 ≤ m) (hm2 : m + 2 ≤ b.r) (hX : cellJ q a j = S m)
    (hrole : sideEdge (b.cell m) ℓ = lat1 (cellJ q a j) a ∨
      sideEdge (b.cell m) ℓ = lat2 (cellJ q a j) a ∨
      (j = 0 ∧ sideEdge (b.cell m) ℓ = back q a) ∨
      (j + 1 = nO ∧ sideEdge (b.cell m) ℓ = front (cellJ q a j) a)) : False := by
  have two := hrow.two
  have he : sideEdge (b.cell m) ℓ = sideEdge (cellJ q a j) ℓ.opp := by rw [hX, hsl.near]
  have hfr := hsl.front m (by omega)
  have hbk := hsl.back m hm1 (by omega)
  have o1 := hsl.hO m (by omega)
  have o2 := hsl.hO (m - 1) (by omega)
  have opp : ¬ (sideEdge (S m) b.a ∈ F ↔ sideEdge (S m) b.a.opp ∈ F) := by
    rw [hfr, hbk, o1, o2]; omega
  have hperp_of : a = ℓ ∨ a = ℓ.opp →
      a = latA b.a ∨ a = latB b.a ∨ a = (latA b.a).opp ∨ a = (latB b.a).opp := by
    rintro (rfl | rfl) <;> rcases hℓ with rfl | rfl <;> simp
  have mixed : a = ℓ ∨ a = ℓ.opp →
      ¬ (lat1 (S m) a ∉ F ∧ lat2 (S m) a ∉ F) ∧ ¬ (lat1 (S m) a ∈ F ∧ lat2 (S m) a ∈ F) := by
    intro ha
    rcases lats_perp' (Y := S m) (hperp_of ha) with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> rw [e1, e2] <;>
      refine ⟨fun ⟨h1, h2⟩ => opp ⟨fun h => ?_, fun h => ?_⟩,
        fun ⟨h1, h2⟩ => opp ⟨fun _ => ?_, fun _ => ?_⟩⟩ <;> tauto
  have hq : q = cellJ (S m) a.opp j := by rw [← hX, cellJ_start]
  rcases hrole with hl | hl | ⟨hj0, hl⟩ | ⟨hjl, hl⟩
  rotate_right 2
  · -- the start's back: the row runs away from the bridge, its laterals are mixed
    subst hj0
    rw [cellJ_zero] at hX he
    have ha : a = ℓ := by
      have : sideEdge q a.opp = sideEdge q ℓ.opp := by unfold back at hl; rw [← hl, he]
      exact opp_inj (sideEdge_inj this)
    have l1q : lat1 q a ∉ F := fun h => hrow.crit.2.2.1 ((ends_lat1 (c := q) (s := a)).conn h)
    have l2q : lat2 q a ∉ F := fun h => hrow.crit.2.2.1
      (hrow.crit.1.trans (((ends_lat2 (c := q) (s := a)).conn h).trans hrow.crit.2.1.symm))
    rw [hX] at l1q l2q
    exact (mixed (Or.inl ha)).1 ⟨l1q, l2q⟩
  · -- the front of the last square faces the bridge
    have ha : a = ℓ.opp := by
      have : sideEdge (cellJ q a j) a = sideEdge (cellJ q a j) ℓ.opp := by
        unfold front at hl; rw [← hl, he]
      exact sideEdge_inj this
    rcases hnO with hn1 | hn1
    · apply hEavoid (by omega) m (by omega)
      rw [show n - 1 = j + 1 by omega, ← nb_cellJ, hX, ha, hsl.hS m, nb_nb_opp]
    · subst hn1
      have hj1 : j = nO - 1 := by omega
      rw [hj1] at hX
      rw [hX] at hlast
      rcases hlast rfl with h | h
      · exact (mixed (Or.inr ha)).1 h
      · exact (mixed (Or.inr ha)).2 h
  all_goals
    -- a lateral of a row square: the row runs along the side line
    have hpar : a = b.a ∨ a = b.a.opp := by
      apply par_of_lat hℓ
      first
        | (left; rw [lat1_eq, he] at hl; exact (sideEdge_inj hl).symm)
        | (right; rw [lat2_eq, he] at hl; exact (sideEdge_inj hl).symm)
    rcases hpar with rfl | rfl
    · rcases (show j ≤ m ∨ m < j by omega) with hjm | hjm
      · exact sideRun_up htwo hsl.up hsl.front hsl.back hsl.hO hsl.cut0 hsl.cutE hrow hlastArc
          (t := m - j) (by omega) (by rw [hq, hsl.down m j hjm])
      · have hc := hrow.uncut (j - m) (by omega) (by omega)
        rw [hq, cellJ_back' _ _ (by omega), show j - (j - m) = m by omega, hsl.down m m le_rfl,
          Nat.sub_self] at hc
        exact hc hsl.cut0
    · rw [opp_opp] at hq
      rw [hsl.up] at hq
      rcases (show m + j ≤ b.r - 1 ∨ b.r - 1 < m + j by omega) with hle | hgt
      · exact sideRun_down htwo hsl.down hsl.front hsl.back hsl.hO hsl.cut0 hsl.efront hrow
          hlastArc (t := m + j) (by omega) hle hq
      · have hc := hrow.uncut (m + j - (b.r - 1)) (by omega) (by omega)
        rw [hq, hsl.down _ _ (by omega), show m + j - (m + j - (b.r - 1)) = b.r - 1 by omega] at hc
        exact hc hsl.cutE

end siderun

end HP

end SolidGridHam
