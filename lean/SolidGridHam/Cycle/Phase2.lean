/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
module

public import SolidGridHam.Cycle.Phase

@[expose] public section

/-!
# Phase II: the strip from a stop cell, and its effect on `μ`

From a stop cell `w` (dark `back`, the walk entered through a lateral side), cells continue
in direction `s` while forced by degree 2. Along them the arcs keep the walk's
orientation, so `D` keeps its sign and the cells stay in the graph. The first alternating
cell ends the strip. It is a sink (`o = true`) or a source (`o = false`) with `D` of the
right sign, so flipping it lowers `μ` by 2. The next cell is then in the same position.
-/

namespace SolidGridHam

open Finset Classical

-- Parity of the first cell, as forced by entering through a lateral side.
--
def ParOK (c : Pt) (s : Side) (o : Bool) : Prop := par c = if s.horiz then !o else o

lemma par_nb (c : Pt) (s : Side) : par (nb c s) = !par c := by
  obtain ⟨x, y⟩ := c
  cases s
  · exact par_sub_snd (x, y)
  · exact par_add_snd (x, y)
  · exact par_sub_fst (x, y)
  · exact par_add_fst (x, y)

lemma par_cellJ (c : Pt) (s : Side) (j : ℕ) :
    par (cellJ c s j) = (par c ^^ decide (j % 2 = 1)) := by
  induction j with
  | zero => simp [cellJ_zero]
  | succ j ih =>
    rw [← nb_cellJ, par_nb, ih]
    rcases Nat.mod_two_eq_zero_or_one j with h | h
    · have : (j + 1) % 2 = 1 := by omega
      simp [h, this]
    · have : (j + 1) % 2 = 0 := by omega
      simp [h, this]

lemma horiz_opp (s : Side) : s.opp.horiz = s.horiz := by cases s <;> rfl
lemma horiz_latA (s : Side) : (latA s).horiz = !s.horiz := by cases s <;> rfl
lemma horiz_latB (s : Side) : (latB s).horiz = !s.horiz := by cases s <;> rfl

-- Every side of a cell is the front, back or a lateral side for direction `s`.
--
lemma side_cases (s s' : Side) : s' = s ∨ s' = s.opp ∨ s' = latA s ∨ s' = latB s := by
  cases s <;> cases s' <;> simp [Side.opp, latA, latB]

/-! ## The arcs of a strip -/

section arcs

variable {F : Finset Edge} {c : Pt} {s : Side} {o : Bool}

-- In a continuing cell, the front arc points the walk's way.
--
lemma front_out (hp : ParOK c s o) (j : ℕ)
    (hf : front (cellJ c s j) s ∈ F ↔ j % 2 = 1) : outArc F (cellJ c s j) s = o := by
  rw [outArc_eq, par_cellJ, hp]
  have : decide (sideEdge (cellJ c s j) s ∈ F) = decide (j % 2 = 1) := by
    simp only [front] at hf; simp [hf]
  rw [this]
  cases hs : s.horiz <;> cases o <;> rcases Nat.mod_two_eq_zero_or_one j with h | h <;>
    simp [h]

-- The last cell of a strip has all four arcs pointing against the walk's way.
--
lemma end_arcs {n : ℕ} (hp : ParOK c s o) (hpat : StripPat F c s (n + 1)) (s' : Side) :
    outArc F (cellJ c s n) s' = !o := by
  obtain ⟨hb, hl, hf⟩ := hpat
  have mF : front (cellJ c s n) s ∈ F ↔ n % 2 = 0 := by
    have := hf n (by omega); simp only [lt_self_iff_false, iff_false] at this; rw [this]; omega
  have mB : back (cellJ c s n) s ∈ F ↔ n % 2 = 0 := by
    rcases n with _ | n
    · simp only [cellJ_zero]; simp [hb]
    · rw [back_cellJ_succ]
      have := hf n (by omega)
      have q : n + 1 < n + 1 + 1 := by omega
      simp only [q, iff_true] at this
      rw [this]; omega
  have mL1 : lat1 (cellJ c s n) s ∈ F ↔ n % 2 = 1 := (hl n (by omega)).1
  have mL2 : lat2 (cellJ c s n) s ∈ F ↔ n % 2 = 1 := (hl n (by omega)).2
  rw [outArc_eq, par_cellJ, hp]
  rcases side_cases s s' with h | h | h | h <;> rw [h]
  · have : decide (sideEdge (cellJ c s n) s ∈ F) = decide (n % 2 = 0) := by
      simp only [front] at mF; simp [mF]
    rw [this]
    cases hs : s.horiz <;> cases o <;> rcases Nat.mod_two_eq_zero_or_one n with h | h <;>
      simp [h]
  · have : decide (sideEdge (cellJ c s n) s.opp ∈ F) = decide (n % 2 = 0) := by
      simp only [back] at mB; simp [mB]
    rw [this, horiz_opp]
    cases hs : s.horiz <;> cases o <;> rcases Nat.mod_two_eq_zero_or_one n with h | h <;>
      simp [h]
  · have : decide (sideEdge (cellJ c s n) (latA s) ∈ F) = decide (n % 2 = 1) := by
      rw [lat1_eq] at mL1; simp [mL1]
    rw [this, horiz_latA]
    cases hs : s.horiz <;> cases o <;> rcases Nat.mod_two_eq_zero_or_one n with h | h <;>
      simp [h]
  · have : decide (sideEdge (cellJ c s n) (latB s) ∈ F) = decide (n % 2 = 1) := by
      rw [lat2_eq] at mL2; simp [mL2]
    rw [this, horiz_latB]
    cases hs : s.horiz <;> cases o <;> rcases Nat.mod_two_eq_zero_or_one n with h | h <;>
      simp [h]

end arcs

/-! ## Flipping a strip lowers `μ` by twice its length -/

-- Flipping the last cell leaves a strip one shorter (either parity).
--
lemma pat_flip_end {F : Finset Edge} {c : Pt} {s : Side} {k : ℕ} (h : StripPat F c s (k + 2)) :
    StripPat (flip F (cellJ c s (k + 1))) c s (k + 1) := by
  obtain ⟨hb, hl, hf⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · rw [mem_flip_iff]; have := back_not_mem c s (m := k + 1) (by omega); tauto
  · intro j hj
    have e1 := lat1_not_mem c s (j := j) (m := k + 1) (by omega)
    have e2 := lat2_not_mem c s (j := j) (m := k + 1) (by omega)
    rw [mem_flip_iff, mem_flip_iff]
    have := hl j (by omega)
    tauto
  · intro j hj
    rw [mem_flip_iff]
    rcases (show j < k ∨ j = k by omega) with hjk | rfl
    · have e := front_not_mem c s (j := j) (m := k + 1) (by omega) (by omega)
      have := hf j (by omega)
      have q1 : j + 1 < k + 2 := by omega
      have q2 : j + 1 < k + 1 := by omega
      simp only [q1, q2, iff_true] at this ⊢
      tauto
    · have e := front_mem_next c s j
      have := hf j (by omega)
      have q1 : j + 1 < j + 2 := by omega
      simp only [q1, iff_true, lt_self_iff_false, iff_false] at this ⊢
      tauto

theorem strip_mu {V : Finset Pt} {F H : Finset Edge} {c : Pt} {s : Side} {o : Bool}
    (hp : ParOK c s o) :
    ∀ n, StripPat F c s n → (∀ j < n, IsCell V (cellJ c s j)) →
      (∀ j < n, Good o (D F H (cellJ c s j))) →
      mu V (flipCol F c s n) H + 2 * n = mu V F H := by
  intro n
  induction n generalizing F with
  | zero => intro _ _ _; simp [flipCol]
  | succ n ih =>
    intro hpat hcell hgood
    rw [flipCol_succ]
    have hce : IsCell V (cellJ c s n) := hcell n (by omega)
    have arcs := end_arcs hp hpat
    have hge : Good o (D F H (cellJ c s n)) := hgood n (by omega)
    -- The last cell is improving.
    have hstep : mu V (flip F (cellJ c s n)) H + 2 = mu V F H := by
      cases o
      · exact mu_flip_source hce (fun s' => by simpa using arcs s')
          (by unfold Good at hge; simp at hge; omega)
      · exact mu_flip_sink hce (fun s' => by simpa using arcs s')
          (by unfold Good at hge; simp at hge; omega)
    have hD : ∀ j < n, D (flip F (cellJ c s n)) H (cellJ c s j) = D F H (cellJ c s j) := by
      intro j hj
      have hne : cellJ c s j ≠ cellJ c s n := by
        obtain ⟨x, y⟩ := c; cases s <;> simp [cellJ] <;> omega
      cases o
      · rw [D_flip_source (fun s' => by simpa using arcs s')]; simp [hne]
      · rw [D_flip_sink (fun s' => by simpa using arcs s')]; simp [hne]
    rcases n with _ | n
    · simp [flipCol]; omega
    · have := ih (pat_flip_end hpat) (fun j hj => hcell j (by omega))
        (fun j hj => by rw [hD j hj]; exact hgood j (by omega))
      omega

/-! ## Phase II: the strip exists -/

lemma cellJ_inj (c : Pt) (s : Side) {i j : ℕ} (h : cellJ c s i = cellJ c s j) : i = j := by
  obtain ⟨x, y⟩ := c
  cases s <;> simp [cellJ] at h <;> omega

lemma exists_not_cell (V : Finset Pt) (c : Pt) (s : Side) : ∃ J, ¬ IsCell V (cellJ c s J) := by
  by_contra h
  push Not at h
  have hmaps : ∀ k ∈ Finset.range (V.card + 1), cellJ c s k ∈ V := fun k _ => (h k).1
  have hinj : Set.InjOn (cellJ c s) (Finset.range (V.card + 1)) :=
    fun i _ j _ hij => cellJ_inj c s hij
  have := Finset.card_le_card_of_injOn _ hmaps hinj
  simp at this

section phase2

variable {V : Finset Pt} {F H : Finset Edge} {P : Finset Pt}
  (hF : Deg2 V F) (hH : Deg2 V H) (hs : Solid V) (hB : Border V F P)

include hF hH hs in
-- Along continuing cells, the lateral sides follow the pattern and `D` stays good.
--
lemma column {w : Pt} {s : Side} {o : Bool} (hp : ParOK w s o)
    (_hb : back w s ∈ F) (hl1 : lat1 w s ∉ F) (hl2 : lat2 w s ∉ F) (hg : Good o (D F H w)) :
    ∀ J, (∀ j < J, front (cellJ w s j) s ∈ F ↔ j % 2 = 1) →
      (∀ j ≤ J, (lat1 (cellJ w s j) s ∈ F ↔ j % 2 = 1) ∧
        (lat2 (cellJ w s j) s ∈ F ↔ j % 2 = 1)) ∧
      ∀ j ≤ J, Good o (D F H (cellJ w s j)) := by
  intro J
  induction J with
  | zero =>
    intro _
    refine ⟨fun j hj => ?_, fun j hj => ?_⟩
    · obtain rfl : j = 0 := by omega
      rw [cellJ_zero]; simp [hl1, hl2]
    · obtain rfl : j = 0 := by omega
      rw [cellJ_zero]; exact hg
  | succ J ih =>
    intro hc
    obtain ⟨hlat, hgood⟩ := ih (fun j hj => hc j (by omega))
    have hfJ := hc J (by omega)
    have hgJ := hgood J le_rfl
    have hcJ : IsCell V (cellJ w s J) := Good.isCell hF hH hs hgJ
    obtain ⟨_, _, f1V, f2V⟩ := isCell_corners hcJ s
    have d1 := deg_front1 (cellJ w s J) s F
    have d2 := deg_front2 (cellJ w s J) s F
    rw [hF.2 _ f1V] at d1
    rw [hF.2 _ f2V] at d2
    rw [nb_cellJ] at d1 d2
    have mem1 : ∀ e, ind F e = 1 → e ∈ F := by
      intro e h; unfold ind at h; split_ifs at h with h'; exact h'
    have nmem : ∀ e, ind F e = 0 → e ∉ F := by
      intro e h he; simp [ind, he] at h
    have i_of : ∀ e, ∀ p : Prop, (e ∈ F ↔ p) → p → ind F e = 1 := by
      intro e p h hp; unfold ind; rw [ite_eq_left (h.2 hp)]
    have i_of' : ∀ e, ∀ p : Prop, (e ∈ F ↔ p) → ¬ p → ind F e = 0 := by
      intro e p h hp; unfold ind; rw [ite_eq_right (fun h' => hp (h.1 h'))]
    have b1 := ind_le_one F (lat1 (cellJ w s (J + 1)) s)
    have b2 := ind_le_one F (lat2 (cellJ w s (J + 1)) s)
    have b3 := ind_le_one F (outer1 (cellJ w s J) s)
    have b4 := ind_le_one F (outer2 (cellJ w s J) s)
    have newlat : (lat1 (cellJ w s (J + 1)) s ∈ F ↔ (J + 1) % 2 = 1) ∧
        (lat2 (cellJ w s (J + 1)) s ∈ F ↔ (J + 1) % 2 = 1) := by
      rcases Nat.mod_two_eq_zero_or_one J with h | h
      · have a1 := i_of' _ _ (hlat J le_rfl).1 (by omega)
        have a2 := i_of' _ _ (hlat J le_rfl).2 (by omega)
        have a3 := i_of' _ _ hfJ (by omega)
        rw [a1, a3] at d1
        rw [a2, a3] at d2
        have q : (J + 1) % 2 = 1 := by omega
        exact ⟨⟨fun _ => q, fun _ => mem1 _ (by omega)⟩, ⟨fun _ => q, fun _ => mem1 _ (by omega)⟩⟩
      · have a1 := i_of _ _ (hlat J le_rfl).1 (by omega)
        have a2 := i_of _ _ (hlat J le_rfl).2 (by omega)
        have a3 := i_of _ _ hfJ (by omega)
        rw [a1, a3] at d1
        rw [a2, a3] at d2
        have q : ¬ (J + 1) % 2 = 1 := by omega
        exact ⟨⟨fun h' => absurd h' (nmem _ (by omega)), fun h' => absurd h' q⟩,
          ⟨fun h' => absurd h' (nmem _ (by omega)), fun h' => absurd h' q⟩⟩
    refine ⟨fun j hj => ?_, fun j hj => ?_⟩
    · rcases (show j ≤ J ∨ j = J + 1 by omega) with h | rfl
      · exact hlat j h
      · exact newlat
    · rcases (show j ≤ J ∨ j = J + 1 by omega) with h | rfl
      · exact hgood j h
      · rw [← nb_cellJ]
        exact Good.step hF hH (front_out hp J hfJ) hgJ

include hF hH hs hB in
-- **Phase II.** A stop cell starts a strip of length at least 2, all of whose cells are in
-- the graph with `D` of the walk's sign, and whose first back and front corners lie on
-- opposite sides of the border.
--
theorem phase2 {w : Pt} {o : Bool} (hg : Good o (D F H w)) (hst : Stop F P o w) :
    ∃ s n, 2 ≤ n ∧ StripPat F w s n ∧ (∀ j < n, IsCell V (cellJ w s j)) ∧
      (∀ j < n, Good o (D F H (cellJ w s j))) ∧ ParOK w s o ∧
      ¬ Conn F (back1 w s) (front1 w s) := by
  obtain ⟨d, hd, hdo, hla, hlb, ⟨si, hsi, hcut, hin⟩, hnc, hout⟩ := hst
  set s := d.opp
  have hb : back w s ∈ F := by simp only [back, s, opp_opp]; exact hd
  have hf0 : front w s ∉ F := hdo
  have hl1 : lat1 w s ∉ F := by rw [lat1_eq, latA_opp]; exact hla
  have hl2 : lat2 w s ∉ F := by rw [lat2_eq, latB_opp]; exact hlb
  -- Parity from the entry side.
  have hp : ParOK w s o := by
    unfold ParOK
    rw [outArc_eq] at hin
    have hsiF : sideEdge w si ∉ F := by rcases hsi with rfl | rfl <;> assumption
    have hh : si.horiz = !s.horiz := by
      rcases hsi with rfl | rfl
      · rw [← horiz_latA, latA_opp]
      · rw [← horiz_latB, latB_opp]
    rw [hh] at hin
    simp only [hsiF, decide_false] at hin
    cases hs' : s.horiz <;> cases o <;> cases hq : par w <;> simp_all
  -- Opposite sides of the border.
  have hsep : ¬ Conn F (back1 w s) (front1 w s) := by
    intro hc
    have e1 := hB.same_side hc
    have e2 := hB.same_side ((ends_back w s).conn hb)
    have hfc : ¬ Cut P (front w s) := hnc
    have ef := ends_front w s
    unfold Cut at hfc
    have e3 : front1 w s ∈ P ↔ front2 w s ∈ P := by
      rcases ef with ⟨q1, q2⟩ | ⟨q1, q2⟩ <;> rw [q1, q2] at hfc <;> tauto
    rcases hsi with rfl | rfl
    · have := ends_lat1 w s
      rw [lat1_eq, latA_opp] at this
      unfold Cut at hcut
      rcases this with ⟨q1, q2⟩ | ⟨q1, q2⟩ <;> rw [q1, q2] at hcut <;> tauto
    · have := ends_lat2 w s
      rw [lat2_eq, latB_opp] at this
      unfold Cut at hcut
      rcases this with ⟨q1, q2⟩ | ⟨q1, q2⟩ <;> rw [q1, q2] at hcut <;> tauto
  -- The first cell where the pattern stops continuing.
  obtain ⟨J0, hJ0⟩ := exists_not_cell V w s
  have hex : ∃ J, ¬ (front (cellJ w s J) s ∈ F ↔ J % 2 = 1) := by
    by_contra hall
    push Not at hall
    obtain ⟨_, hgd⟩ := column hF hH hs hp hb hl1 hl2 hg (J0 + 1) (fun j _ => hall j)
    exact hJ0 (Good.isCell hF hH hs (hgd J0 (by omega)))
  set J := Nat.find hex
  have hJ : ¬ (front (cellJ w s J) s ∈ F ↔ J % 2 = 1) := Nat.find_spec hex
  have hbefore : ∀ j < J, front (cellJ w s j) s ∈ F ↔ j % 2 = 1 := fun j hj => by
    have := Nat.find_min hex hj; push Not at this; exact this
  have hJpos : J ≠ 0 := by
    intro h0
    apply hJ; rw [h0, cellJ_zero]; simp [hf0]
  obtain ⟨hlat, hgd⟩ := column hF hH hs hp hb hl1 hl2 hg J hbefore
  refine ⟨s, J + 1, by omega, ⟨hb, fun j hj => hlat j (by omega), fun j hj => ?_⟩,
    fun j hj => Good.isCell hF hH hs (hgd j (by omega)), fun j hj => hgd j (by omega), hp, hsep⟩
  rcases (show j < J ∨ j = J by omega) with h | rfl
  · have q : j + 1 < J + 1 := by omega
    simp only [q, iff_true]; exact hbefore j h
  · simp only [lt_self_iff_false, iff_false]
    tauto

end phase2

end SolidGridHam
