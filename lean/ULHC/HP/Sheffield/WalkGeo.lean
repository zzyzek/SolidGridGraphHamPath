/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
import ULHC.HP.Sheffield.HoleWalk

/-!
# The ring around a point, with one hole

The 8 king neighbours of `w` with one lattice neighbour `t` removed form a path of 7 points,
indexed `0 … 6` going around `w` (`pidx`, `ptAt`). Lattice steps from a ring point go to `w`, to
`t`, to the next or previous ring point, or out to king distance 2; corners have 2 such outward
steps, edge midpoints 1 (`outI`, `ring_cat`). Everything is checked on the 28 relative positions.
-/

namespace ULHC

namespace HP

open Finset

def rel (w p : Pt) : ℤ × ℤ := (p.1 - w.1, p.2 - w.2)

-- Rotate so that the hole direction `a` becomes `(1, 0)`.
--
def rotE (a d : ℤ × ℤ) : ℤ × ℤ :=
  if a = (1, 0) then d else if a = (0, 1) then (d.2, -d.1)
  else if a = (-1, 0) then (-d.1, -d.2) else (-d.2, d.1)

def rotInv (a d : ℤ × ℤ) : ℤ × ℤ :=
  if a = (1, 0) then d else if a = (0, 1) then (-d.2, d.1)
  else if a = (-1, 0) then (-d.1, -d.2) else (d.2, -d.1)

def ridx (d : ℤ × ℤ) : ℕ :=
  if d = (1, 1) then 0 else if d = (0, 1) then 1 else if d = (-1, 1) then 2
  else if d = (-1, 0) then 3 else if d = (-1, -1) then 4 else if d = (0, -1) then 5
  else if d = (1, -1) then 6 else 7

def offI : ℕ → ℤ × ℤ
  | 0 => (1, 1) | 1 => (0, 1) | 2 => (-1, 1) | 3 => (-1, 0) | 4 => (-1, -1) | 5 => (0, -1)
  | _ => (1, -1)

-- Outward steps: 2 at corners (even index), 1 at edge midpoints.
--
def outI (k : ℕ) : ℕ := if k % 2 = 0 then 2 else 1

def units4 : List (ℤ × ℤ) := [(1, 0), (-1, 0), (0, 1), (0, -1)]

def kd (d : ℤ × ℤ) : ℤ := max |d.1| |d.2|

def pidx (w t p : Pt) : ℕ := ridx (rotE (rel w t) (rel w p))

def ptAt (w t : Pt) (k : ℕ) : Pt :=
  (w.1 + (rotInv (rel w t) (offI k)).1, w.2 + (rotInv (rel w t) (offI k)).2)

/-! ## Finite facts -/

lemma rotInv_rotE {a : ℤ × ℤ} (ha : a ∈ units4) (d : ℤ × ℤ) : rotInv a (rotE a d) = d := by
  simp only [units4, List.mem_cons, List.not_mem_nil, or_false] at ha
  obtain ⟨x, y⟩ := d
  rcases ha with rfl | rfl | rfl | rfl <;> simp [rotInv, rotE]

lemma ridx_lt {v : ℤ × ℤ} (h : ridx v < 7) : v = offI (ridx v) := by
  unfold ridx at *
  split_ifs at * with h1 h2 h3 h4 h5 h6 h7 <;> first | omega | (subst_vars; rfl)

lemma ridx_offI : ∀ k < 7, ridx (offI k) = k := by decide

lemma rotE_rotInv {a : ℤ × ℤ} (ha : a ∈ units4) (d : ℤ × ℤ) : rotE a (rotInv a d) = d := by
  simp only [units4, List.mem_cons, List.not_mem_nil, or_false] at ha
  obtain ⟨x, y⟩ := d
  rcases ha with rfl | rfl | rfl | rfl <;> simp [rotInv, rotE]

lemma rel_ptAt (w t : Pt) (k : ℕ) : rel w (ptAt w t k) = rotInv (rel w t) (offI k) := by
  simp [rel, ptAt]

lemma pidx_ptAt {w t : Pt} (ha : rel w t ∈ units4) {k : ℕ} (hk : k < 7) : pidx w t (ptAt w t k) = k := by
  unfold pidx; rw [rel_ptAt, rotE_rotInv ha, ridx_offI k hk]

lemma ptAt_pidx {w t p : Pt} (ha : rel w t ∈ units4) (h : pidx w t p < 7) : ptAt w t (pidx w t p) = p := by
  have e := ridx_lt h
  unfold pidx at e ⊢
  have : rel w p = rotInv (rel w t) (offI (ridx (rotE (rel w t) (rel w p)))) := by
    rw [← e, rotInv_rotE ha]
  obtain ⟨x, y⟩ := p
  unfold ptAt
  rw [← this]; simp [rel]

lemma ptAt_inj {w t : Pt} (ha : rel w t ∈ units4) {j k : ℕ} (hj : j < 7) (hk : k < 7)
    (h : ptAt w t j = ptAt w t k) : j = k := by
  have := congrArg (pidx w t) h
  rwa [pidx_ptAt ha hj, pidx_ptAt ha hk] at this

-- **The categories of the four lattice steps from ring position `k`.** `0`: onto the centre,
-- `1`: onto the hole, `2`: the next ring point, `3`: the previous one, `4`: outward.
--
def catOf (a : ℤ × ℤ) (k : ℕ) (u : ℤ × ℤ) : ℕ :=
  let d := (( rotInv a (offI k)).1 + u.1, (rotInv a (offI k)).2 + u.2)
  if d = (0, 0) then 0 else if d = a then 1
  else if k + 1 < 7 ∧ ridx (rotE a d) = k + 1 then 2 else if ridx (rotE a d) + 1 = k then 3
  else if kd d = 2 then 4 else 5

lemma cat_ne5 : ∀ a ∈ units4, ∀ k < 7, ∀ u ∈ units4, catOf a k u ≠ 5 := by decide

lemma cat_counts : ∀ a ∈ units4, ∀ k < 7,
    (units4.filter (fun u => catOf a k u = 4)).length ≤ outI k ∧
    (units4.filter (fun u => catOf a k u = 2)).length ≤ 1 ∧
    (units4.filter (fun u => catOf a k u = 3)).length ≤ 1 := by decide

lemma cat_two_lt : ∀ a ∈ units4, ∀ k < 7, ∀ u ∈ units4, catOf a k u = 2 → k + 1 < 7 := by decide

/-! ## Sums along the ring -/

-- `upS b wt i`: the weights of the run of present ring points after position `i`.
--
def upD (b : ℕ → Bool) (wt : ℕ → ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 0
  | d + 1, i => if b (i + 1) then wt (i + 1) + upD b wt d (i + 1) else 0

def upS (b : ℕ → Bool) (wt : ℕ → ℕ) (i : ℕ) : ℕ := upD b wt (6 - i) i

lemma upS_succ (b : ℕ → Bool) (wt : ℕ → ℕ) {i : ℕ} (h : i + 1 < 7) :
    upS b wt i = if b (i + 1) then wt (i + 1) + upS b wt (i + 1) else 0 := by
  unfold upS
  rw [show 6 - i = (6 - (i + 1)) + 1 by omega]
  rfl

lemma upS_last (b : ℕ → Bool) (wt : ℕ → ℕ) {i : ℕ} (h : 6 ≤ i) : upS b wt i = 0 := by
  unfold upS; rw [show 6 - i = 0 by omega]; rfl

def downS (b : ℕ → Bool) (wt : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | i + 1 => if b i then wt i + downS b wt i else 0

lemma upD_congr {b b' : ℕ → Bool} {wt : ℕ → ℕ} :
    ∀ d i, (∀ k, i < k → b k = b' k) → upD b wt d i = upD b' wt d i := by
  intro d
  induction d with
  | zero => intro _ _; rfl
  | succ d ih =>
    intro i h
    simp only [upD]
    rw [h (i + 1) (by omega), ih (i + 1) (fun k hk => h k (by omega))]

lemma upS_congr {b b' : ℕ → Bool} {wt : ℕ → ℕ} (i : ℕ) (h : ∀ k, i < k → b k = b' k) :
    upS b wt i = upS b' wt i := upD_congr _ _ h

lemma downS_congr {b b' : ℕ → Bool} {wt : ℕ → ℕ} :
    ∀ i, (∀ k, k < i → b k = b' k) → downS b wt i = downS b' wt i := by
  intro i
  induction i with
  | zero => intro _; rfl
  | succ i ih =>
    intro h
    simp only [downS]
    rw [h i (by omega), ih (fun k hk => h k (by omega))]

lemma upD_le_true (b : ℕ → Bool) (wt : ℕ → ℕ) :
    ∀ d i, upD b wt d i ≤ upD (fun _ => true) wt d i := by
  intro d
  induction d with
  | zero => intro _; exact le_rfl
  | succ d ih =>
    intro i
    simp only [upD]
    split_ifs
    · have := ih (i + 1); simp; omega
    · simp

lemma upS_le_true (b : ℕ → Bool) (wt : ℕ → ℕ) (i : ℕ) :
    upS b wt i ≤ upS (fun _ => true) wt i := upD_le_true _ _ _ _

lemma downS_le_true (b : ℕ → Bool) (wt : ℕ → ℕ) :
    ∀ i, downS b wt i ≤ downS (fun _ => true) wt i := by
  intro i
  induction i with
  | zero => exact le_rfl
  | succ i ih =>
    simp only [downS]
    split_ifs <;> simp; omega

lemma ring_total_out : ∀ i < 7,
    outI i + upS (fun _ => true) outI i + downS (fun _ => true) outI i = 11 := by decide

lemma ring_total_node : ∀ i < 7,
    (1 + outI i) + upS (fun _ => true) (fun k => 1 + outI k) i +
      downS (fun _ => true) (fun k => 1 + outI k) i = 18 := by decide

end HP

end ULHC
