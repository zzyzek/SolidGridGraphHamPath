/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
import ULHC.HP.Sheffield.ColProof

/-!
# The side field `side` at the end of a phase (docs/COL_SIDE.md §5)

For a pair from bridge `β` (frame `a`, squares `A = c_(r−2)`, `E = c_(r−1)`):
* beside `E`, Lemma C applies at once;
* beside `A`, the side column runs from `S_(r−2)` toward `f_0` with arcs forced by the frozen
  region, and Lemma C applies at `S_0`, or a non-cell ends it.

Pair separation (B5): two side squares beside `A` and `E` are never one pair, by `PInv.sep`.
-/

namespace ULHC

namespace HP

open Finset Classical

lemma pairwise_or {α : Type*} {R : α → α → Prop} :
    ∀ {l : List α}, l.Pairwise R → ∀ {x y : α}, x ∈ l → y ∈ l → x ≠ y → R x y ∨ R y x
  | [], _, _, _, hx, _, _ => absurd hx List.not_mem_nil
  | z :: l, hp, x, y, hx, hy, hxy => by
    rw [List.pairwise_cons] at hp
    rcases List.mem_cons.1 hx with h1 | h1 <;> rcases List.mem_cons.1 hy with h2 | h2
    · exact absurd (h1.trans h2.symm) hxy
    · rw [h1]; exact Or.inl (hp.1 y h2)
    · rw [h2]; exact Or.inr (hp.1 x h1)
    · exact pairwise_or hp.2 h1 h2 hxy

section geo2

lemma nb_inj_dir {X : Pt} {d1 d2 : Side} (h : nb X d1 = nb X d2) : d1 = d2 := by
  obtain ⟨x, y⟩ := X
  cases d1 <;> cases d2 <;> simp [nb, Prod.ext_iff] at h ⊢ <;> omega

lemma side_ne_col (q : Pt) (a : Side) {ℓ : Side} (hℓ : ℓ = latA a ∨ ℓ = latB a) (i k : ℕ) :
    nb (cellJ q a i) ℓ ≠ cellJ q a k := by
  obtain ⟨x, y⟩ := q
  rcases hℓ with rfl | rfl <;> cases a <;>
    simp [nb, cellJ, latA, latB, Prod.ext_iff]

lemma perp_opp {a g ℓ : Side} (hℓ : ℓ = latA a ∨ ℓ = latB a) (hg : g = a ∨ g = a.opp) :
    ℓ.opp = latA g ∨ ℓ.opp = latB g := by
  cases a <;> cases g <;> cases ℓ <;> simp_all [latA, latB, Side.opp]

end geo2

section b5

variable {V W : Finset Pt} {d : Pt → ℕ} {H : Finset Edge} {t0 u0 : Pt}

lemma side_comm (c : Pt) (a : Side) {ℓ : Side} (hℓ : ℓ = latA a ∨ ℓ = latB a) :
    nb (nb c ℓ) a = nb (nb c a) ℓ := by
  rcases hℓ with rfl | rfl
  · exact nb_side_comm c a
  · exact nb_sideB_comm c a

-- **Pair separation (B5).** The side squares beside `A` and `E` (one side) are not the two
-- squares of one bridge's pair.
--
theorem b5 {BS : List Bridge} (hinv : PInv V W d H BS t0 u0) {β : Bridge} (hβ : β ∈ BS)
    {ℓ : Side} (hℓ : ℓ = latA β.a ∨ ℓ = latB β.a) :
    ∀ γ ∈ BS, ¬ ((γ.cell (γ.r - 2) = nb (β.cell (β.r - 2)) ℓ ∧ γ.E = nb β.E ℓ) ∨
      (γ.cell (γ.r - 2) = nb β.E ℓ ∧ γ.E = nb (β.cell (β.r - 2)) ℓ)) := by
  intro γ hγ h
  obtain ⟨_, tβ, _, _⟩ := hinv.reg β hβ
  obtain ⟨_, tγ, _, _⟩ := hinv.reg γ hγ
  set P0 := nb (β.cell (β.r - 2)) ℓ with hP0
  set P1 := nb β.E ℓ with hP1
  have S1 : P1 = nb P0 β.a := by
    rw [hP1, hP0, side_comm _ _ hℓ]
    unfold Bridge.E Bridge.cell; rw [nb_cellJ, show β.r - 2 + 1 = β.r - 1 by omega]
  have Eγ : γ.E = nb (γ.cell (γ.r - 2)) γ.a := by
    unfold Bridge.E Bridge.cell; rw [nb_cellJ, show γ.r - 2 + 1 = γ.r - 1 by omega]
  have Eβ : β.E = nb P1 ℓ.opp := (nb_nb_opp _ _).symm
  by_cases hgb : γ = β
  · rw [hgb] at h
    have hc : β.E = cellJ β.q β.a (β.r - 1) := rfl
    rcases h with ⟨_, h⟩ | ⟨_, h⟩
    · exact side_ne_col β.q β.a hℓ (β.r - 1) (β.r - 1) (by rw [← hc]; exact h.symm)
    · exact side_ne_col β.q β.a hℓ (β.r - 2) (β.r - 1) (by rw [← hc]; exact h.symm)
  rcases pairwise_or hinv.sep hγ hβ hgb with hz | hz
  · obtain ⟨_, _, hs⟩ := hz
    have k1 := hs (β.r - 2) (by omega)
    have k2 := hs (β.r - 1) (by omega)
    have hE' : β.cell (β.r - 1) = β.E := rfl
    rw [hE'] at k2
    rcases hℓ with rfl | rfl <;> rcases h with ⟨_, h⟩ | ⟨_, h⟩
    · exact k2.1 h
    · exact k1.1 h
    · exact k2.2 h
    · exact k1.2 h
  · obtain ⟨_, _, hs⟩ := hz
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have hg : γ.a = β.a := by
        rw [Eγ, h1, S1] at h2; exact nb_inj_dir h2
      have hp := perp_opp (g := γ.a) hℓ (Or.inl hg)
      have k := hs (γ.r - 1) (by omega)
      have hEc : P1 = γ.cell (γ.r - 1) := h2.symm
      rw [hEc] at Eβ
      rcases hp with hp | hp <;> rw [hp] at Eβ
      · exact k.1 Eβ
      · exact k.2 Eβ
    · have hg : γ.a = β.a.opp := by
        have e : nb P1 γ.a = nb P1 β.a.opp := by
          calc nb P1 γ.a = γ.E := by rw [← h1, Eγ]
            _ = P0 := h2
            _ = nb P1 β.a.opp := by rw [S1, nb_nb_opp]
        exact nb_inj_dir e
      have hp := perp_opp (g := γ.a) hℓ (Or.inr hg)
      have k := hs (γ.r - 2) (by omega)
      rw [← h1] at Eβ
      rcases hp with hp | hp <;> rw [hp] at Eβ
      · exact k.1 Eβ
      · exact k.2 Eβ

end b5

section atE

variable {V W : Finset Pt} {d : Pt → ℕ} {H : Finset Edge} {t0 u0 : Pt}

-- B5 for the fixed pairs.
--
theorem no_pair_P {BS : List Bridge} (hinv : PInv V W d H BS t0 u0) {β : Bridge} (hβ : β ∈ BS)
    {ℓ : Side} (hℓ : ℓ = latA β.a ∨ ℓ = latB β.a) :
    ∀ i ∈ BS.map (Bridge.pairOf H),
      ¬ ((i.top = nb (β.cell (β.r - 2)) ℓ ∧ i.bot = nb β.E ℓ) ∨
        (i.top = nb β.E ℓ ∧ i.bot = nb (β.cell (β.r - 2)) ℓ)) := by
  intro i hi h
  obtain ⟨γ, hγ, rfl⟩ := List.mem_map.1 hi
  obtain ⟨hR, t2, e2, _⟩ := hinv.reg γ hγ
  apply b5 hinv hβ hℓ γ hγ
  rcases pair_squares hR t2 e2 with ⟨x, y⟩ | ⟨x, y⟩ <;> rw [x, y] at h <;>
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl ⟨h1, h2⟩
  · exact Or.inr ⟨h1, h2⟩
  · exact Or.inr ⟨h2, h1⟩
  · exact Or.inl ⟨h2, h1⟩

lemma latAB_opp {a ℓ : Side} (hℓ : ℓ = latA a ∨ ℓ = latB a) : ℓ = latA a.opp ∨ ℓ = latB a.opp := by
  rw [latA_opp, latB_opp]; exact hℓ

-- The cut facts of `E` on both sides.
--
lemma cutE_both {b : Bridge} (hR : RegionOK H b) (htwo : 2 ≤ b.r) :
    ¬ Conn H (back1 b.E b.a) (front1 b.E b.a) ∧ ¬ Conn H (back2 b.E b.a) (front2 b.E b.a) := by
  refine ⟨hR.cutE, fun h => hR.cutE ?_⟩
  have bE : back b.E b.a ∈ H := by
    have := hR.frA
    unfold Bridge.E Bridge.cell at *
    rw [show b.r - 1 = b.r - 2 + 1 by omega, back_cellJ_succ]; exact this
  exact ((ends_back (c := b.E) (s := b.a)).conn bE).trans
    (h.trans ((ends_front (c := b.E) (s := b.a)).conn hR.frE).symm)

-- **`side` beside `E`.**
--
theorem side_atE (hVW : V ⊆ W) (hdc : ∀ q, IsCell V q → ∀ z, IsCorner z q → d z = 2)
    {BS : List Bridge} (hinv : PInv V W d H BS t0 u0) (hmerge : MergeOK V H BS)
    (hstuck : Stuck V H BS) {β : Bridge} (hβ : β ∈ BS) {ℓ : Side}
    (hℓ : ℓ = latA β.a ∨ ℓ = latB β.a) {o : Bool} (hS : IsCell V (nb β.E ℓ))
    (hb : back (nb β.E ℓ) β.a ∈ H) (hl1 : lat1 (nb β.E ℓ) β.a ∉ H)
    (hl2 : lat2 (nb β.E ℓ) β.a ∉ H) (harc : outArc H (nb β.E ℓ) β.a.opp = !o) :
    ColEnds V H (BS.map (Bridge.pairOf H)) (nb β.E ℓ) β.a o ∨ ColOut V H (nb β.E ℓ) β.a o := by
  have hdegc := degc_of hVW hdc hinv.fac
  obtain ⟨hf2, hpok, hpalt, hpdark, hpcell⟩ := phase_fp hVW hdc hinv hmerge
  obtain ⟨hR, htwo, _, _⟩ := hinv.reg β hβ
  obtain ⟨c1, c2⟩ := cutE_both hR htwo
  have hcut : CutSq H (nb β.E ℓ) := by
    rcases hℓ with rfl | rfl
    · refine cutSq_of_corners (isCorner_back2 _ β.a) (isCorner_front2 _ β.a) ?_
      rw [sideA_back2, sideA_front2]; exact c1
    · refine cutSq_of_corners (isCorner_back1 _ β.a) (isCorner_front1 _ β.a) ?_
      rw [sideB_back1, sideB_front1]; exact c2
  have hbehind : nb (nb β.E ℓ) β.a.opp = nb (β.cell (β.r - 2)) ℓ := by
    rw [side_comm _ _ (latAB_opp hℓ)]
    unfold Bridge.E Bridge.cell
    rw [show β.r - 1 = β.r - 2 + 1 by omega, nb_cellJ_opp]
  have hHb : ∀ i ∈ BS.map (Bridge.pairOf H), ¬ ((nb β.E ℓ = i.top ∧
      nb (nb β.E ℓ) β.a.opp = i.bot) ∨ (nb β.E ℓ = i.bot ∧ nb (nb β.E ℓ) β.a.opp = i.top)) := by
    intro i hi h
    rw [hbehind] at h
    apply no_pair_P hinv hβ hℓ i hi
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inr ⟨h1.symm, h2.symm⟩
    · exact Or.inl ⟨h2.symm, h1.symm⟩
  exact lemmaC hdegc hf2 hpok hpalt hpdark hpcell hS hb hl1 hl2 hcut harc hHb
    (fun hcr hnp => col_of_stuck hVW hdc hinv hmerge hstuck _ _ hS hcr hb hnp)

end atE

section atN

variable {V W : Finset Pt} {d : Pt → ℕ} {H : Finset Edge} {t0 u0 : Pt}

lemma cellJ_nb_any (c : Pt) (s ℓ : Side) (j : ℕ) : cellJ (nb c ℓ) s j = nb (cellJ c s j) ℓ := by
  obtain ⟨x, y⟩ := c
  cases s <;> cases ℓ <;> simp [cellJ, nb] <;> ring_nf

lemma back1_sopp (q : Pt) (s : Side) : back1 q s.opp = front1 q s := by
  have := front1_sopp q s.opp; rw [opp_opp] at this; exact this.symm

lemma back2_sopp (q : Pt) (s : Side) : back2 q s.opp = front2 q s := by
  have := front2_sopp q s.opp; rw [opp_opp] at this; exact this.symm

lemma side_backA (q : Pt) (a : Side) {i : ℕ} (hi : 1 ≤ i) :
    sideEdge (nb (cellJ q a i) (latA a)) a.opp = outer1 (cellJ q a (i - 1)) a := by
  obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
  rw [show i' + 1 - 1 = i' by omega, ← nb_cellJ, ← nb_side_comm, sideEdge_nb_opp]
  exact side_front _ _

lemma side_backB (q : Pt) (a : Side) {i : ℕ} (hi : 1 ≤ i) :
    sideEdge (nb (cellJ q a i) (latB a)) a.opp = outer2 (cellJ q a (i - 1)) a := by
  obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
  rw [show i' + 1 - 1 = i' by omega, ← nb_cellJ, ← nb_sideB_comm, sideEdge_nb_opp]
  exact sideB_front _ _

-- Degree 2 forces the laterals of a run whose fronts alternate from light.
--
theorem run_lats {F : Finset Edge} {q : Pt} {a : Side} {n : ℕ}
    (hl0 : lat1 q a ∉ F ∧ lat2 q a ∉ F)
    (hfr : ∀ j < n, front (cellJ q a j) a ∈ F ↔ j % 2 = 1)
    (hdeg : ∀ j < n, deg F (front1 (cellJ q a j) a) = 2 ∧ deg F (front2 (cellJ q a j) a) = 2) :
    ∀ j ≤ n, (lat1 (cellJ q a j) a ∈ F ↔ j % 2 = 1) ∧ (lat2 (cellJ q a j) a ∈ F ↔ j % 2 = 1) := by
  intro j
  induction j with
  | zero =>
    intro _; rw [cellJ_zero]
    exact ⟨⟨fun h => absurd h hl0.1, fun h => by omega⟩, ⟨fun h => absurd h hl0.2, fun h => by omega⟩⟩
  | succ j ih =>
    intro hj
    obtain ⟨l1, l2⟩ := ih (by omega)
    have f1 := hfr j (by omega)
    obtain ⟨d1, d2⟩ := hdeg j (by omega)
    rw [deg_front1, nb_cellJ] at d1
    rw [deg_front2, nb_cellJ] at d2
    refine ⟨?_, ?_⟩
    · rcases Nat.mod_two_eq_zero_or_one j with h | h
      · rw [ind_of_not_mem (fun h' => by have := l1.1 h'; omega),
          ind_of_not_mem (fun h' => by have := f1.1 h'; omega)] at d1
        have := ind_le_one F (lat1 (cellJ q a (j + 1)) a)
        have := ind_le_one F (outer1 (cellJ q a j) a)
        have hi : ind F (lat1 (cellJ q a (j + 1)) a) = 1 := by omega
        constructor
        · intro _; omega
        · intro _; unfold ind at hi; split_ifs at hi with hh; exact hh
      · rw [ind_of_mem (l1.2 h), ind_of_mem (f1.2 h)] at d1
        constructor
        · intro hh; rw [ind_of_mem hh] at d1; omega
        · intro hh; omega
    · rcases Nat.mod_two_eq_zero_or_one j with h | h
      · rw [ind_of_not_mem (fun h' => by have := l2.1 h'; omega),
          ind_of_not_mem (fun h' => by have := f1.1 h'; omega)] at d2
        have := ind_le_one F (lat2 (cellJ q a (j + 1)) a)
        have := ind_le_one F (outer2 (cellJ q a j) a)
        have hi : ind F (lat2 (cellJ q a (j + 1)) a) = 1 := by omega
        constructor
        · intro _; omega
        · intro _; unfold ind at hi; split_ifs at hi with hh; exact hh
      · rw [ind_of_mem (l2.2 h), ind_of_mem (f1.2 h)] at d2
        constructor
        · intro hh; rw [ind_of_mem hh] at d2; omega
        · intro hh; omega

-- **`side` beside `A`.** The side column runs from `S_(r−2)` toward `f_0` (frame `a.opp`).
--
theorem side_atN (hVW : V ⊆ W) (hdc : ∀ q, IsCell V q → ∀ z, IsCorner z q → d z = 2)
    {BS : List Bridge} (hinv : PInv V W d H BS t0 u0) (hmerge : MergeOK V H BS)
    (hstuck : Stuck V H BS) {β : Bridge} (hβ : β ∈ BS) {ℓ : Side}
    (hℓ : ℓ = latA β.a ∨ ℓ = latB β.a) {o : Bool}
    (hS : IsCell V (nb (β.cell (β.r - 2)) ℓ))
    (hb : back (nb (β.cell (β.r - 2)) ℓ) β.a.opp ∈ H)
    (hl1 : lat1 (nb (β.cell (β.r - 2)) ℓ) β.a.opp ∉ H)
    (hl2 : lat2 (nb (β.cell (β.r - 2)) ℓ) β.a.opp ∉ H)
    (harc : outArc H (nb (β.cell (β.r - 2)) ℓ) β.a.opp.opp = !o) :
    ColEnds V H (BS.map (Bridge.pairOf H)) (nb (β.cell (β.r - 2)) ℓ) β.a.opp o ∨
      ColOut V H (nb (β.cell (β.r - 2)) ℓ) β.a.opp o := by
  have hdegc := degc_of hVW hdc hinv.fac
  obtain ⟨hf2, hpok, hpalt, hpdark, hpcell⟩ := phase_fp hVW hdc hinv hmerge
  have hnoP := no_pair_P hinv hβ hℓ
  have hcol := col_of_stuck hVW hdc hinv hmerge hstuck
  obtain ⟨hR, htwo, hev, _⟩ := hinv.reg β hβ
  revert hnoP hS hb hl1 hl2 harc
  obtain ⟨q, a, r⟩ := β
  obtain ⟨m, rfl⟩ : ∃ m, r = m + 2 := ⟨r - 2, by simp only at htwo; omega⟩
  obtain ⟨bk, lat, lat0, latE, fr, frA, frE, outer, cut0, cut0', cutE⟩ := hR
  simp only [Bridge.cell, Bridge.E, show m + 2 - 1 = m + 1 by omega,
    show m + 2 - 2 = m by omega] at *
  intro hS hb hl1 hl2 harc hnoP
  have meven : m % 2 = 0 := by omega
  set S := nb (cellJ q a m) ℓ with hSdef
  have dj : ∀ j ≤ m, cellJ S a.opp j = nb (cellJ q a (m - j)) ℓ := fun j hj => by
    rw [hSdef, cellJ_nb_any, cellJ_back _ _ hj]
  -- Fronts of the walk (frame `a.opp`): outer edges of the bridge.
  --
  have frd : ∀ j < m, (front (cellJ S a.opp j) a.opp ∈ H ↔ j % 2 = 1) := by
    intro j hj
    rw [dj j (by omega)]
    unfold front
    have o' := outer (m - j - 1) (by omega)
    rcases hℓ with rfl | rfl
    · rw [side_backA q a (by omega : 1 ≤ m - j), o'.1]; omega
    · rw [side_backB q a (by omega : 1 ≤ m - j), o'.2]; omega
  -- The last square of the walk, `S_0`, beside `q`.
  --
  have dm : cellJ S a.opp m = nb q ℓ := by rw [dj m le_rfl, Nat.sub_self, cellJ_zero]
  -- If a square of the walk is not a cell, the column leaves `V`.
  --
  by_cases hall : ∀ j ≤ m, IsCell V (cellJ S a.opp j)
  swap
  · push Not at hall
    right
    have hex : ∃ j, j ≤ m ∧ ¬ IsCell V (cellJ S a.opp j) := hall
    let j0 := Nat.find hex
    have hj0 : j0 ≤ m ∧ ¬ IsCell V (cellJ S a.opp j0) := Nat.find_spec hex
    have hmin : ∀ j < j0, IsCell V (cellJ S a.opp j) := fun j hj => by
      have := Nat.find_min hex hj; push Not at this; exact this (by omega)
    have hpos : 1 ≤ j0 := by
      by_contra h0; push Not at h0
      have : j0 = 0 := by omega
      exact hj0.2 (by rw [this, cellJ_zero]; exact hS)
    have harc0 : outArc H S a.opp = o := by
      have hf0 : sideEdge S a.opp ∉ H := by
        have := frd 0 (by omega); rw [cellJ_zero] at this; unfold front at this
        exact fun h => by have := this.1 h; omega
      rw [arc_opp_diff (by unfold back at hb; exact hb) hf0, harc]; simp
    refine ⟨j0 - 1, fun j hj => hmin j (by omega), fun j hj => ?_, ?_⟩
    · have hf0 : front S a.opp ∉ H := by
        have := frd 0 (by omega); rw [cellJ_zero] at this
        exact fun h => by have := this.1 h; omega
      rw [run_front' hf0 (frd j (by omega)), harc0]
    · rw [show j0 - 1 + 1 = j0 by omega]; exact hj0.2
  -- All squares of the walk are cells.
  --
  have hdegd : ∀ j < m, deg H (front1 (cellJ S a.opp j) a.opp) = 2 ∧
      deg H (front2 (cellJ S a.opp j) a.opp) = 2 := fun j hj =>
    ⟨hdegc _ (hall j (by omega)) _ (isCorner_front1 _ _),
      hdegc _ (hall j (by omega)) _ (isCorner_front2 _ _)⟩
  have hS0 : lat1 S a.opp ∉ H ∧ lat2 S a.opp ∉ H := ⟨hl1, hl2⟩
  have hl0' : lat1 (cellJ S a.opp 0) a.opp ∉ H ∧ lat2 (cellJ S a.opp 0) a.opp ∉ H := by
    rw [cellJ_zero]; exact hS0
  have rl := run_lats hS0 frd hdegd
  have hrun : StripRun H S a.opp m := ⟨hb, fun j hj => rl j (by omega), fun j hj => frd j hj⟩
  -- Lemma C at `S_0`.
  --
  have hgm := hall m le_rfl
  have hbg : back (cellJ S a.opp m) a.opp ∈ H := by
    rcases Nat.eq_zero_or_pos m with h0 | hpos
    · rw [h0, cellJ_zero]; exact hb
    · obtain ⟨m', hm'⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
      rw [hm', back_cellJ_succ]; exact (frd m' (by omega)).2 (by omega)
  obtain ⟨lg1, lg2⟩ := rl m le_rfl
  have lg1' : lat1 (cellJ S a.opp m) a.opp ∉ H := fun h => by have := lg1.1 h; omega
  have lg2' : lat2 (cellJ S a.opp m) a.opp ∉ H := fun h => by have := lg2.1 h; omega
  have hcutg : CutSq H (cellJ S a.opp m) := by
    rw [dm]
    rcases hℓ with rfl | rfl
    · refine cutSq_of_corners (isCorner_back2 _ a.opp) (isCorner_front2 _ a.opp) ?_
      rw [← latA_opp, sideA_back2, sideA_front2, back1_sopp, front1_sopp]
      exact fun h => cut0 h.symm
    · refine cutSq_of_corners (isCorner_back1 _ a.opp) (isCorner_front1 _ a.opp) ?_
      rw [← latB_opp, sideB_back1, sideB_front1, back2_sopp, front2_sopp]
      exact fun h => cut0' h.symm
  have harcg : outArc H (cellJ S a.opp m) a.opp.opp = !o := by
    rcases Nat.eq_zero_or_pos m with h0 | hpos
    · rw [h0, cellJ_zero]; exact harc
    · obtain ⟨m', hm'⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
      have hf0 : front S a.opp ∉ H := by
        have := frd 0 (by omega); rw [cellJ_zero] at this
        exact fun h => by have := this.1 h; omega
      have harc0 : outArc H S a.opp = o := by
        unfold front at hf0
        rw [arc_opp_diff (by unfold back at hb; exact hb) hf0, harc]; simp
      rw [hm', ← nb_cellJ, outArc_nb_opp, run_front' hf0 (frd m' (by omega)), harc0]
  have hHbg : ∀ i ∈ BS.map (Bridge.pairOf H), ¬ ((cellJ S a.opp m = i.top ∧
      nb (cellJ S a.opp m) a.opp.opp = i.bot) ∨
      (cellJ S a.opp m = i.bot ∧ nb (cellJ S a.opp m) a.opp.opp = i.top)) := by
    intro i hi h
    rcases Nat.eq_zero_or_pos m with h0 | hpos
    · -- `S_0`, `S_1` are not a pair (B5).
      subst h0
      have e1 : cellJ S a.opp 0 = S := cellJ_zero _ _
      have e2 : nb S a.opp.opp = nb (cellJ q a (0 + 1)) ℓ := by
        rw [opp_opp, hSdef, side_comm _ _ hℓ, nb_cellJ]
      rw [e1, e2] at h
      apply hnoP i hi
      rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl ⟨h1.symm, h2.symm⟩
      · exact Or.inr ⟨h2.symm, h1.symm⟩
    · -- the square behind `S_0` on the walk is not alternating
      obtain ⟨m', hm'⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
      have hprev : nb (cellJ S a.opp m) a.opp.opp = cellJ S a.opp m' := by
        rw [hm', nb_cellJ_opp]
      have f1 : front (cellJ S a.opp m') a.opp ∈ H := (frd m' (by omega)).2 (by omega)
      have l1 : lat1 (cellJ S a.opp m') a.opp ∈ H := (rl m' (by omega)).1.2 (by omega)
      have nAlt : ¬ Alt H (cellJ S a.opp m') := fun ha => by
        have := (alt_lats ha (s' := a.opp) f1).1; rw [← lat1_eq] at this; exact this l1
      rw [hprev] at h
      rcases h with ⟨_, h⟩ | ⟨_, h⟩
      · exact nAlt (h ▸ (hpalt i hi).2)
      · exact nAlt (h ▸ (hpalt i hi).1)
  rcases lemmaC hdegc hf2 hpok hpalt hpdark hpcell hgm hbg lg1' lg2' hcutg harcg hHbg
    (fun hcr hnp => hcol _ _ hgm hcr hbg hnp) with
    ⟨n', cells', pat', i, hi, hpair⟩ | ⟨n', cells', arcs', out'⟩
  · left
    refine ⟨m + n', fun j hj => ?_, ?_, i, hi, ?_⟩
    · rcases Nat.lt_or_ge j m with hlt | hge
      · exact hall j (by omega)
      · have := cells' (j - m) (by omega); rwa [cellJ_add, show m + (j - m) = j by omega] at this
    · have := stripPat_append meven (by omega) hrun pat'
      rwa [show m + (n' + 1) = m + n' + 1 by omega] at this
    · rw [cellJ_add, cellJ_add] at hpair
      rwa [show m + (n' + 1) = m + n' + 1 by omega] at hpair
  · right
    have hf0 : m ≠ 0 → front S a.opp ∉ H := fun hm => by
      have := frd 0 (by omega); rw [cellJ_zero] at this
      exact fun h => by have := this.1 h; omega
    have harcS : ∀ j < m, outArc H (cellJ S a.opp j) a.opp = o := by
      intro j hj
      have hf := hf0 (by omega)
      have harc0 : outArc H S a.opp = o := by
        have hf' := hf; unfold front at hf'
        rw [arc_opp_diff (by unfold back at hb; exact hb) hf', harc]; simp
      rw [run_front' hf (frd j hj), harc0]
    refine ⟨m + n', fun j hj => ?_, fun j hj => ?_, ?_⟩
    · rcases Nat.lt_or_ge j m with hlt | hge
      · exact hall j (by omega)
      · have := cells' (j - m) (by omega); rwa [cellJ_add, show m + (j - m) = j by omega] at this
    · rcases Nat.lt_or_ge j m with hlt | hge
      · exact harcS j hlt
      · have := arcs' (j - m) (by omega); rwa [cellJ_add, show m + (j - m) = j by omega] at this
    · rw [cellJ_add] at out'; rwa [show m + (n' + 1) = m + n' + 1 by omega] at out'

end atN

section sideOf

variable {V W : Finset Pt} {d : Pt → ℕ} {H : Finset Edge} {t0 u0 : Pt}

-- **The side field at the end of a phase.**
--
theorem side_of_stuck (hVW : V ⊆ W) (hdc : ∀ q, IsCell V q → ∀ z, IsCorner z q → d z = 2)
    {BS : List Bridge} (hinv : PInv V W d H BS t0 u0) (hmerge : MergeOK V H BS)
    (hstuck : Stuck V H BS) : SideCert V H (BS.map (Bridge.pairOf H)) := by
  intro p hp ℓ hℓp
  obtain ⟨β, hβ, rfl⟩ := List.mem_map.1 hp
  obtain ⟨_, htwo, _, _⟩ := hinv.reg β hβ
  have hA : nb β.E β.a.opp = β.cell (β.r - 2) := by
    unfold Bridge.E Bridge.cell; rw [show β.r - 1 = β.r - 2 + 1 by omega, nb_cellJ_opp]
  have hE' : nb (β.cell (β.r - 2)) β.a = β.E := by
    unfold Bridge.E Bridge.cell; rw [nb_cellJ, show β.r - 2 + 1 = β.r - 1 by omega]
  have atE := fun {o : Bool} (hℓ : ℓ = latA β.a ∨ ℓ = latB β.a) =>
    side_atE (o := o) hVW hdc hinv hmerge hstuck hβ hℓ
  have atN := fun {o : Bool} (hℓ : ℓ = latA β.a ∨ ℓ = latB β.a) =>
    side_atN (o := o) hVW hdc hinv hmerge hstuck hβ hℓ
  by_cases ho : outArc H (β.cell (β.r - 2)) β.a = false
  · have hpe : β.pairOf H = ⟨β.E, β.a.opp, back1 (β.cell (β.r - 2)) β.a,
        front1 (β.cell (β.r - 2)) β.a, back1 β.E β.a, front1 β.E β.a⟩ := by
      unfold Bridge.pairOf; rw [ite_eq_left ho]
    rw [hpe] at hℓp ⊢
    simp only [FixedPr.top] at hℓp ⊢
    rw [hA]
    have hℓ : ℓ = latA β.a ∨ ℓ = latB β.a := by rw [latA_opp, latB_opp] at hℓp; exact hℓp
    refine ⟨fun hc hb h1 h2 harc => ?_, fun hc hb h1 h2 harc => ?_⟩
    · rw [opp_opp] at hb h1 h2 ⊢
      exact atE hℓ hc hb h1 h2 (by rw [harc]; rfl)
    · exact atN hℓ hc hb h1 h2 (by rw [harc]; rfl)
  · have hpe : β.pairOf H = ⟨β.cell (β.r - 2), β.a, back1 β.E β.a, front1 β.E β.a,
        back1 (β.cell (β.r - 2)) β.a, front1 (β.cell (β.r - 2)) β.a⟩ := by
      unfold Bridge.pairOf; rw [ite_eq_right ho]
    rw [hpe] at hℓp ⊢
    simp only [FixedPr.top] at hℓp ⊢
    rw [hE']
    refine ⟨fun hc hb h1 h2 harc => ?_, fun hc hb h1 h2 harc => ?_⟩
    · exact atN hℓp hc hb h1 h2 (by rw [opp_opp, harc]; rfl)
    · exact atE hℓp hc hb h1 h2 (by rw [harc]; rfl)

end sideOf

end HP

end ULHC
