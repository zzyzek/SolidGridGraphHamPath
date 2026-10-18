/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
import SolidGridHam.Path.WalkGeo

/-!
# Counting the walk's final tests

A state of the hole walk `holeCaseWalk` (`w` fixed with its hole `t`; endpoint `s`, phantom `q`) is
* a base state (`|U| ≤ 2`), a stop state (the final test runs), or
* a ring state (`s` a king neighbour of `w`), or
* an opposed state (`s` at distance 2 along an axis with opposed phantoms; only at the start).

`Lp` counts final tests: `1` at a stop, `outI` of the ring point plus those of the run of ring
points ahead of it at a ring state (at most 11), `13` at an opposed state. `Mp` counts nodes with
weights `1 + outI` (at most 18), `21` at an opposed state. The children of every other state satisfy
`Σ Lp ≤ Lp` and `1 + Σ Mp ≤ Mp` (`pot_step`).
-/

namespace SolidGridHam

namespace HP

open Finset

def bU (w t : Pt) (U : Finset Pt) (k : ℕ) : Bool := decide (ptAt w t k ∈ U)

def stopB (w t s q : Pt) : Bool := isFar w s && !phantomsOpposed w t s q

def ringL (w t : Pt) (U : Finset Pt) (i : ℕ) : ℕ :=
  outI i + upS (bU w t U) outI i + downS (bU w t U) outI i

def ringM (w t : Pt) (U : Finset Pt) (i : ℕ) : ℕ :=
  (1 + outI i) + upS (bU w t U) (fun k => 1 + outI k) i +
    downS (bU w t U) (fun k => 1 + outI k) i

def Lp (w t : Pt) (U : Finset Pt) (s q : Pt) : ℕ :=
  if U.card ≤ 2 then 0 else if stopB w t s q then 1
  else if pidx w t s < 7 then ringL w t U (pidx w t s) else 13

def Mp (w t : Pt) (U : Finset Pt) (s q : Pt) : ℕ :=
  if U.card ≤ 2 then 1 else if stopB w t s q then 1
  else if pidx w t s < 7 then ringM w t U (pidx w t s) else 21

section bounds

variable {w t : Pt}

lemma ringL_le (U : Finset Pt) {i : ℕ} (hi : i < 7) : ringL w t U i ≤ 11 := by
  have h1 := upS_le_true (bU w t U) outI i
  have h2 := downS_le_true (bU w t U) outI i
  have := ring_total_out i hi
  unfold ringL; omega

lemma ringM_le (U : Finset Pt) {i : ℕ} (hi : i < 7) : ringM w t U i ≤ 18 := by
  have h1 := upS_le_true (bU w t U) (fun k => 1 + outI k) i
  have h2 := downS_le_true (bU w t U) (fun k => 1 + outI k) i
  have := ring_total_node i hi
  unfold ringM; omega

lemma Lp_le13 (U : Finset Pt) (s q : Pt) : Lp w t U s q ≤ 13 := by
  unfold Lp
  split_ifs with h1 h2 h3
  · omega
  · omega
  · exact (ringL_le U h3).trans (by omega)
  · omega

lemma Mp_le21 (U : Finset Pt) (s q : Pt) : Mp w t U s q ≤ 21 := by
  unfold Mp
  split_ifs with h1 h2 h3
  · omega
  · omega
  · exact (ringM_le U h3).trans (by omega)
  · omega

lemma Mp_pos (U : Finset Pt) (s q : Pt) : 1 ≤ Mp w t U s q := by
  unfold Mp ringM
  split_ifs <;> omega

-- A point within king distance 1 of `w`, not `w` and not the hole, is a ring point.
--
lemma close1_ring (ha : rel w t ∈ units4) {x : Pt} (hc : Close1 w x) (hxw : x ≠ w) (hxt : x ≠ t) :
    pidx w t x < 7 := by
  have key : ∀ a ∈ units4, ∀ d : ℤ × ℤ, |d.1| ≤ 1 → |d.2| ≤ 1 → d ≠ (0, 0) → d ≠ a →
      ridx (rotE a d) < 7 := by
    intro a ha d h1 h2 h3 h4
    obtain ⟨x, y⟩ := d
    simp only [abs_le] at h1 h2
    have hx : x = -1 ∨ x = 0 ∨ x = 1 := by omega
    have hy : y = -1 ∨ y = 0 ∨ y = 1 := by omega
    simp only [units4, List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl <;> rcases hx with rfl | rfl | rfl <;>
      rcases hy with rfl | rfl | rfl <;> simp_all [rotE, ridx]
  unfold pidx
  unfold Close1 at hc
  apply key _ ha
  · simp only [rel]; rw [abs_sub_comm]; exact hc.1
  · simp only [rel]; rw [abs_sub_comm]; exact hc.2
  · intro h; apply hxw; simp only [rel, Prod.mk.injEq] at h; ext <;> omega
  · intro h; apply hxt; simp only [rel, Prod.mk.injEq] at h; ext <;> omega

lemma ring_close1 (ha : rel w t ∈ units4) {x : Pt} (h : pidx w t x < 7) : Close1 w x := by
  have hx := ptAt_pidx ha h
  have hr := rel_ptAt w t (pidx w t x)
  rw [hx] at hr
  have key : ∀ a ∈ units4, ∀ k < 7,
      |(rotInv a (offI k)).1| ≤ 1 ∧ |(rotInv a (offI k)).2| ≤ 1 := by decide
  obtain ⟨k1, k2⟩ := key _ ha _ h
  rw [← hr] at k1 k2
  unfold Close1
  simp only [rel] at k1 k2
  rw [abs_sub_comm] at k1 k2
  exact ⟨k1, k2⟩

end bounds

section step

variable {w t : Pt}

lemma stop_of_far {q x : Pt} (hq : Close w q) (hx : ¬ Close1 w x) : stopB w t x q = true := by
  unfold stopB
  simp only [Bool.and_eq_true, Bool.not_eq_true', phantomsOpposed, decide_eq_false_iff_not]
  exact ⟨isFar_iff.2 (Or.inr hx), fun hop => opp_far_b hop hq⟩

lemma pot_le_far (U : Finset Pt) {q x : Pt} (hq : Close w q) (hx : ¬ Close1 w x) :
    Lp w t U x q ≤ 1 ∧ Mp w t U x q ≤ 1 := by
  have h := stop_of_far (t := t) hq hx
  constructor
  · unfold Lp; split_ifs <;> simp_all
  · unfold Mp; split_ifs <;> simp_all

lemma pot_le_close (ha : rel w t ∈ units4) (U : Finset Pt) {q x : Pt} (hq : Close w q)
    (hxw : x ≠ w) (hxt : x ≠ t) : Lp w t U x q ≤ 11 ∧ Mp w t U x q ≤ 18 := by
  by_cases hc : Close1 w x
  · have hr := close1_ring ha hc hxw hxt
    constructor
    · unfold Lp; split_ifs <;> first | omega | exact ringL_le U hr
    · unfold Mp; split_ifs <;> first | omega | exact ringM_le U hr
  · have := pot_le_far (t := t) U hq hc
    omega

lemma close_of_close1 {a b : Pt} (h : Close1 a b) : Close a b := by
  unfold Close1 at h; unfold Close; omega

lemma upD_congr7 {b b' : ℕ → Bool} {wt : ℕ → ℕ} :
    ∀ d i, (∀ k, i < k → k ≤ i + d → b k = b' k) → upD b wt d i = upD b' wt d i := by
  intro d
  induction d with
  | zero => intro _ _; rfl
  | succ d ih =>
    intro i h
    simp only [upD]
    rw [h (i + 1) (by omega) (by omega), ih (i + 1) (fun k hk hk' => h k (by omega) (by omega))]

lemma upS_congr7 {b b' : ℕ → Bool} {wt : ℕ → ℕ} {i : ℕ} (h : ∀ k, i < k → k ≤ 6 → b k = b' k) :
    upS b wt i = upS b' wt i :=
  upD_congr7 _ _ (fun k hk hk' => h k hk (by omega))

lemma bU_erase (ha : rel w t ∈ units4) (U : Finset Pt) {i k : ℕ} (hi : i < 7) (hk : k < 7)
    (hki : k ≠ i) : bU w t (U.erase (ptAt w t i)) k = bU w t U k := by
  unfold bU
  have : ptAt w t k ≠ ptAt w t i := fun h => hki (ptAt_inj ha hk hi h)
  simp [Finset.mem_erase, this]

lemma bU_erase_self (U : Finset Pt) (i : ℕ) : bU w t (U.erase (ptAt w t i)) i = false := by
  unfold bU; simp

-- The child two steps along the ring: the run after `i`, in both weightings.
--
lemma child_up (ha : rel w t ∈ units4) (U : Finset Pt) {i : ℕ} (hi : i + 1 < 7)
    (hx : ptAt w t (i + 1) ∈ U) (wt : ℕ → ℕ) :
    wt (i + 1) + upS (bU w t (U.erase (ptAt w t i))) wt (i + 1) +
        downS (bU w t (U.erase (ptAt w t i))) wt (i + 1) = upS (bU w t U) wt i := by
  rw [upS_succ _ _ hi]
  have hb : bU w t U (i + 1) = true := by unfold bU; simp [hx]
  rw [ite_eq_left hb]
  have hd : downS (bU w t (U.erase (ptAt w t i))) wt (i + 1) = 0 := by
    simp only [downS, bU_erase_self, Bool.false_eq_true, ↓reduceIte]
  rw [hd, upS_congr7 (b' := bU w t U) (fun k hk hk' => bU_erase ha U (by omega) (by omega) (by omega))]
  omega

lemma child_down (ha : rel w t ∈ units4) (U : Finset Pt) {i : ℕ} (hi : i < 7) (h0 : 1 ≤ i)
    (hx : ptAt w t (i - 1) ∈ U) (wt : ℕ → ℕ) :
    wt (i - 1) + upS (bU w t (U.erase (ptAt w t i))) wt (i - 1) +
        downS (bU w t (U.erase (ptAt w t i))) wt (i - 1) = downS (bU w t U) wt i := by
  have hu : upS (bU w t (U.erase (ptAt w t i))) wt (i - 1) = 0 := by
    rw [upS_succ _ _ (by omega), show i - 1 + 1 = i by omega, bU_erase_self]; rfl
  have hd : downS (bU w t (U.erase (ptAt w t i))) wt (i - 1) = downS (bU w t U) wt (i - 1) :=
    downS_congr _ (fun k hk => bU_erase ha U hi (by omega) (by omega))
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at hu hd hx ⊢
  have hb : bU w t U j = true := by unfold bU; simp [hx]
  simp only [downS, hb, ↓reduceIte]
  omega

end step

section ringstep

variable {w t : Pt}

lemma cat0 {a : ℤ × ℤ} {k : ℕ} {u : ℤ × ℤ} (h : catOf a k u = 0) :
    ((rotInv a (offI k)).1 + u.1, (rotInv a (offI k)).2 + u.2) = (0, 0) := by
  unfold catOf at h; simp only at h; split_ifs at h with h1; simp_all

lemma cat1 {a : ℤ × ℤ} {k : ℕ} {u : ℤ × ℤ} (h : catOf a k u = 1) :
    ((rotInv a (offI k)).1 + u.1, (rotInv a (offI k)).2 + u.2) = a := by
  unfold catOf at h; simp only at h; split_ifs at h with h1 h2 <;> simp_all

lemma cat2 {a : ℤ × ℤ} {k : ℕ} {u : ℤ × ℤ} (h : catOf a k u = 2) :
    k + 1 < 7 ∧ ridx (rotE a ((rotInv a (offI k)).1 + u.1, (rotInv a (offI k)).2 + u.2)) = k + 1 := by
  unfold catOf at h; simp only at h; split_ifs at h with h1 h2 h3 <;> simp_all

lemma cat3 {a : ℤ × ℤ} {k : ℕ} {u : ℤ × ℤ} (h : catOf a k u = 3) :
    ridx (rotE a ((rotInv a (offI k)).1 + u.1, (rotInv a (offI k)).2 + u.2)) + 1 = k := by
  unfold catOf at h; simp only at h; split_ifs at h with h1 h2 h3 h4 <;> simp_all

lemma cat4 {a : ℤ × ℤ} {k : ℕ} {u : ℤ × ℤ} (h : catOf a k u = 4) :
    kd ((rotInv a (offI k)).1 + u.1, (rotInv a (offI k)).2 + u.2) = 2 := by
  unfold catOf at h; simp only at h; split_ifs at h with h1 h2 h3 h4 h5 <;> simp_all

def catW (A B : ℕ) (c : ℕ) : ℕ := if c = 4 then 1 else if c = 2 then A else if c = 3 then B else 0

lemma ring_sum : ∀ a ∈ units4, ∀ k < 7, ∀ A B : ℕ,
    (units4.map (fun u => catW A B (catOf a k u))).sum ≤ outI k + A + B := by
  intro a ha k hk A B
  simp only [units4, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl <;> interval_cases k <;>
    simp [catW, catOf, rotInv, rotE, ridx, offI, kd, units4, outI] <;> omega

lemma rel_eq_of {w x : Pt} {d : ℤ × ℤ} (h : rel w x = d) : x = (w.1 + d.1, w.2 + d.2) := by
  subst h; simp [rel]

lemma catOf_le (a : ℤ × ℤ) (k : ℕ) (u : ℤ × ℤ) : catOf a k u ≤ 5 := by
  unfold catOf; simp only; split_ifs <;> omega

lemma pidx_self (w t : Pt) : pidx w t w = 7 := by
  unfold pidx rel rotE ridx; simp

lemma stop_ring_false (ha : rel w t ∈ units4) {x q : Pt} (hring : pidx w t x < 7) :
    stopB w t x q = false := by
  have hc1 := ring_close1 ha hring
  have : isFar w x = false := by
    rw [Bool.eq_false_iff]; intro hf
    rcases isFar_iff.1 hf with h' | h'
    · subst h'; rw [pidx_self] at hring; omega
    · exact h' hc1
  unfold stopB; simp [this]

-- **One child of a ring point.**
--
lemma term_ring (ha : rel w t ∈ units4) {U : Finset Pt} (htU : t ∉ U) {i : ℕ} (hi : i < 7)
    {u : ℤ × ℤ} (hu : u ∈ units4) {x : Pt}
    (hx : rel w x = ((rotInv (rel w t) (offI i)).1 + u.1, (rotInv (rel w t) (offI i)).2 + u.2)) :
    (if x ∈ U ∧ x ≠ w then Lp w t (U.erase (ptAt w t i)) x (ptAt w t i) else 0) ≤
      catW (upS (bU w t U) outI i) (downS (bU w t U) outI i) (catOf (rel w t) i u) ∧
    (if x ∈ U ∧ x ≠ w then Mp w t (U.erase (ptAt w t i)) x (ptAt w t i) else 0) ≤
      catW (upS (bU w t U) (fun k => 1 + outI k) i) (downS (bU w t U) (fun k => 1 + outI k) i)
        (catOf (rel w t) i u) := by
  have hne := cat_ne5 _ ha i hi u hu
  have hsc : Close w (ptAt w t i) :=
    close_of_close1 (ring_close1 ha (by rw [pidx_ptAt ha hi]; exact hi))
  have hpx : pidx w t x = ridx (rotE (rel w t)
      ((rotInv (rel w t) (offI i)).1 + u.1, (rotInv (rel w t) (offI i)).2 + u.2)) := by
    unfold pidx; rw [hx]
  set c := catOf (rel w t) i u with hc
  have hc' := hc.symm
  have hcle := catOf_le (rel w t) i u
  rcases (show c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 ∨ c = 4 ∨ c = 5 by omega) with h | h | h | h | h | h
  · -- onto `w`
    have := cat0 (h ▸ hc')
    have hxw : x = w := by
      have e := rel_eq_of hx; rw [this] at e; rw [e]; simp
    simp [hxw]
  · -- onto the hole
    have := cat1 (h ▸ hc')
    have hxt : x = t := by
      have e := rel_eq_of hx; rw [this] at e; rw [e]; simp [rel]
    simp [hxt, htU]
  · -- the next ring point
    obtain ⟨hi1, hr⟩ := cat2 (h ▸ hc')
    have hpi : pidx w t x = i + 1 := by rw [hpx, hr]
    have hxe : x = ptAt w t (i + 1) := by rw [← hpi, ptAt_pidx ha (by omega)]
    have hring : pidx w t x < 7 := by omega
    have hns := stop_ring_false (q := ptAt w t i) ha hring
    simp only [catW, h, show (2 : ℕ) ≠ 4 by omega, ↓reduceIte]
    constructor
    · split_ifs with hxU
      · simp only [Lp, hns, Bool.false_eq_true, ↓reduceIte, hpi, hi1]
        split_ifs
        · omega
        · unfold ringL
          rw [← child_up ha U hi1 (hxe ▸ hxU.1) outI]
      · omega
    · split_ifs with hxU
      · simp only [Mp, hns, Bool.false_eq_true, ↓reduceIte, hpi, hi1]
        split_ifs
        · rw [upS_succ _ _ hi1]
          have hb : bU w t U (i + 1) = true := by unfold bU; simp [← hxe, hxU.1]
          simp [hb]; omega
        · unfold ringM
          rw [← child_up ha U hi1 (hxe ▸ hxU.1) (fun k => 1 + outI k)]
      · omega
  · -- the previous ring point
    have hr := cat3 (h ▸ hc')
    have hpi : pidx w t x + 1 = i := by rw [hpx]; exact hr
    have hxe : x = ptAt w t (i - 1) := by
      rw [show i - 1 = pidx w t x by omega, ptAt_pidx ha (by omega)]
    have hring : pidx w t x < 7 := by omega
    have hpi' : pidx w t x = i - 1 := by omega
    have hns := stop_ring_false (q := ptAt w t i) ha hring
    simp only [catW, h, show (3 : ℕ) ≠ 4 by omega, show (3 : ℕ) ≠ 2 by omega, ↓reduceIte]
    constructor
    · split_ifs with hxU
      · have hlt : i - 1 < 7 := by omega
        simp only [Lp, hns, Bool.false_eq_true, ↓reduceIte, hpi', hlt]
        split_ifs
        · omega
        · unfold ringL
          rw [← child_down ha U hi (by omega) (hxe ▸ hxU.1) outI]
      · omega
    · split_ifs with hxU
      · have hlt : i - 1 < 7 := by omega
        simp only [Mp, hns, Bool.false_eq_true, ↓reduceIte, hpi', hlt]
        split_ifs
        · obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
          have hb : bU w t U j = true := by
            unfold bU; simp only [Nat.add_sub_cancel] at hxe; simp [← hxe, hxU.1]
          simp [downS, hb]; omega
        · unfold ringM
          rw [← child_down ha U hi (by omega) (hxe ▸ hxU.1) (fun k => 1 + outI k)]
      · omega
  · -- outward
    have hk := cat4 (h ▸ hc')
    have hnc : ¬ Close1 w x := by
      unfold Close1; unfold kd at hk; rw [← hx] at hk; simp only [rel] at hk
      rw [abs_sub_comm, abs_sub_comm w.2]; omega
    have := pot_le_far (t := t) (U.erase (ptAt w t i)) hsc hnc
    simp only [catW, h, ↓reduceIte]
    constructor <;> split_ifs <;> omega
  · exact absurd h hne

end ringstep

section steps

variable {w t : Pt}

-- **A ring state's children.**
--
theorem ring_step (ha : rel w t ∈ units4) {U : Finset Pt} (htU : t ∉ U) {i : ℕ} (hi : i < 7) :
    ((nbrsL (ptAt w t i)).map fun x =>
      if x.1 ∈ U ∧ x.1 ≠ w then Lp w t (U.erase (ptAt w t i)) x.1 (ptAt w t i) else 0).sum ≤
        ringL w t U i ∧
    1 + ((nbrsL (ptAt w t i)).map fun x =>
      if x.1 ∈ U ∧ x.1 ≠ w then Mp w t (U.erase (ptAt w t i)) x.1 (ptAt w t i) else 0).sum ≤
        ringM w t U i := by
  set s := ptAt w t i with hs
  have h0 : rel w s = rotInv (rel w t) (offI i) := rel_ptAt w t i
  have hxr : ∀ u : ℤ × ℤ, rel w (s.1 + u.1, s.2 + u.2) =
      ((rotInv (rel w t) (offI i)).1 + u.1, (rotInv (rel w t) (offI i)).2 + u.2) := by
    intro u; rw [← h0]; simp only [rel]; ext <;> simp <;> ring
  have e1 := term_ring ha htU hi (u := (1, 0)) (by simp [units4]) (hxr (1, 0))
  have e2 := term_ring ha htU hi (u := (-1, 0)) (by simp [units4]) (hxr (-1, 0))
  have e3 := term_ring ha htU hi (u := (0, 1)) (by simp [units4]) (hxr (0, 1))
  have e4 := term_ring ha htU hi (u := (0, -1)) (by simp [units4]) (hxr (0, -1))
  have hA := ring_sum _ ha i hi (upS (bU w t U) outI i) (downS (bU w t U) outI i)
  have hB := ring_sum _ ha i hi (upS (bU w t U) (fun k => 1 + outI k) i)
    (downS (bU w t U) (fun k => 1 + outI k) i)
  simp only [units4, List.map_cons, List.sum_cons, List.map_nil, List.sum_nil] at hA hB
  simp only [add_zero, show ∀ z : ℤ, z + -1 = z - 1 from fun z => by ring] at e1 e2 e3 e4
  simp only [nbrsL, List.map_cons, List.sum_cons, List.map_nil, List.sum_nil]
  rw [← hs] at e1 e2 e3 e4
  unfold ringL ringM
  constructor <;> omega

-- **The opposed start state's children.**
--
theorem opp_step (ha : rel w t ∈ units4) {U : Finset Pt} (htU : t ∉ U) {s q : Pt} (hqU : q ∉ U)
    (hop : Opp w t s q) :
    ((nbrsL s).map fun x =>
      if x.1 ∈ U ∧ x.1 ≠ w then Lp w t (U.erase s) x.1 s else 0).sum ≤ 13 ∧
    1 + ((nbrsL s).map fun x =>
      if x.1 ∈ U ∧ x.1 ≠ w then Mp w t (U.erase s) x.1 s else 0).sum ≤ 21 := by
  have hcs : Close w s := opp_close hop
  have gen : ∀ x : Pt, (if x ∈ U ∧ x ≠ w then Lp w t (U.erase s) x s else 0) ≤ 11 ∧
      (if x ∈ U ∧ x ≠ w then Mp w t (U.erase s) x s else 0) ≤ 18 := by
    intro x
    split_ifs with hx
    · exact pot_le_close ha _ hcs hx.2 (fun h => htU (h ▸ hx.1))
    · omega
  have far : ∀ x : Pt, ¬ Close1 w x → (if x ∈ U ∧ x ≠ w then Lp w t (U.erase s) x s else 0) ≤ 1 ∧
      (if x ∈ U ∧ x ≠ w then Mp w t (U.erase s) x s else 0) ≤ 1 := by
    intro x hx
    split_ifs
    · exact pot_le_far _ hcs hx
    · omega
  have hq : ∀ x : Pt, x = q → (if x ∈ U ∧ x ≠ w then Lp w t (U.erase s) x s else 0) = 0 ∧
      (if x ∈ U ∧ x ≠ w then Mp w t (U.erase s) x s else 0) = 0 := by
    rintro x rfl; simp [hqU]
  simp only [nbrsL, List.map_cons, List.sum_cons, List.map_nil, List.sum_nil]
  unfold Opp at hop
  rcases hop with ⟨h1, h2, _, rfl⟩ | ⟨h1, h2, _, rfl⟩ | ⟨h1, h2, _, rfl⟩ | ⟨h1, h2, _, rfl⟩
  · have a1 := hq (s.1 + 1, s.2) rfl
    have a2 := gen (s.1 - 1, s.2)
    have a3 := far (s.1, s.2 + 1) (by unfold Close1; simp only [abs_le]; omega)
    have a4 := far (s.1, s.2 - 1) (by unfold Close1; simp only [abs_le]; omega)
    constructor <;> omega
  · have a1 := gen (s.1 + 1, s.2)
    have a2 := hq (s.1 - 1, s.2) rfl
    have a3 := far (s.1, s.2 + 1) (by unfold Close1; simp only [abs_le]; omega)
    have a4 := far (s.1, s.2 - 1) (by unfold Close1; simp only [abs_le]; omega)
    constructor <;> omega
  · have a1 := far (s.1 + 1, s.2) (by unfold Close1; simp only [abs_le]; omega)
    have a2 := far (s.1 - 1, s.2) (by unfold Close1; simp only [abs_le]; omega)
    have a3 := hq (s.1, s.2 + 1) rfl
    have a4 := gen (s.1, s.2 - 1)
    constructor <;> omega
  · have a1 := far (s.1 + 1, s.2) (by unfold Close1; simp only [abs_le]; omega)
    have a2 := far (s.1 - 1, s.2) (by unfold Close1; simp only [abs_le]; omega)
    have a3 := gen (s.1, s.2 + 1)
    have a4 := hq (s.1, s.2 - 1) rfl
    constructor <;> omega

end steps

end HP

end SolidGridHam
