/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
module

public import SolidGridHam.Cycle.Algorithm

@[expose] public section

/-!
# Step counting: the monad and the counted basic operations

`TimeM α` pairs a result with a step count; `bind` adds the counts. The counted algorithm
(`SolidGridHam/Cycle/Timed/*.lean`) is written with the operations below and constant-time functions on
points, edges, sides, strips, link-graph nodes, numbers and Booleans. Nothing else: the script
`checks/timed_lint.py` rejects any other set or list operation, any membership test and any
call to the uncounted algorithm inside a counted definition.

**The trusted part is this list of costs** (one step per elementary operation, sets as
balanced trees with logarithmic factors dropped):

| operation | cost |
|---|---|
| `tick n` | `n` |
| `memT x s` (membership test) | 1 |
| `insertT`, `eraseT` | 1 |
| `symmDiffT s E` (toggle each element of `E`) | `2 |E|` |
| `unionT A B` | `|A| + |B|` |
| `cardT s` | `|s| + 1` |
| `filterT p s`, `allT p s` | `Σ_{x ∈ s} (cost of p x + 1)` |
| `imageT f s` | `Σ_{x ∈ s} (cost of f x + 1)` |
| `imageSetsT f s` (elements are point sets) | `Σ_{x ∈ s} (cost of f x + |f x|)` |
| `biUnionT f s` | `Σ_{x ∈ s} (cost of f x + |f x| + 1)` |
| `sortT s` | `|s|²` |
| `pickT S` (lexicographic minimum of a point set) | `2 |S| + 2` |
| `lmapT f l`, `lfilterT p l`, `lallT p l`, `lanyT p l`, `lfindT p l` | `Σ_{x ∈ l} (cost + 1)` |
| `lflatMapT f l` | `Σ_{x ∈ l} (cost of f x + |f x| + 1)` |
| `lengthT l` | `|l| + 1` |
| `rangeT n` | `n + 1` |
| `toFinsetT l` | `|l| + 1` |

`lfindT` and the Boolean operations charge every element and operand (an upper bound on
early exit).
-/

namespace SolidGridHam.T

open Finset

structure TimeM (α : Type) where
  ret : α
  time : ℕ

instance : Monad TimeM where
  pure a := ⟨a, 0⟩
  bind m f := let r := f m.ret; ⟨r.ret, m.time + r.time⟩

variable {α β : Type}

@[simp] lemma ret_pure (a : α) : (pure a : TimeM α).ret = a := rfl
@[simp] lemma time_pure (a : α) : (pure a : TimeM α).time = 0 := rfl
@[simp] lemma ret_bind (m : TimeM α) (f : α → TimeM β) : (m >>= f).ret = (f m.ret).ret := rfl
@[simp] lemma time_bind (m : TimeM α) (f : α → TimeM β) :
    (m >>= f).time = m.time + (f m.ret).time := rfl

/-! ## The counted operations -/

def tick (n : ℕ) : TimeM _root_.Unit := ⟨(), n⟩

def memT [DecidableEq α] (x : α) (s : Finset α) : TimeM Bool := ⟨decide (x ∈ s), 1⟩

def insertT [DecidableEq α] (x : α) (s : Finset α) : TimeM (Finset α) := ⟨insert x s, 1⟩

def eraseT [DecidableEq α] (x : α) (s : Finset α) : TimeM (Finset α) := ⟨s.erase x, 1⟩

def symmDiffT [DecidableEq α] (s E : Finset α) : TimeM (Finset α) := ⟨symmDiff s E, 2 * E.card⟩

def unionT [DecidableEq α] (A B : Finset α) : TimeM (Finset α) := ⟨A ∪ B, A.card + B.card⟩

def cardT (s : Finset α) : TimeM ℕ := ⟨s.card, s.card + 1⟩

def filterT (p : α → TimeM Bool) (s : Finset α) : TimeM (Finset α) :=
  ⟨s.filter (fun x => (p x).ret = true), ∑ x ∈ s, ((p x).time + 1)⟩

def allT (p : α → TimeM Bool) (s : Finset α) : TimeM Bool :=
  ⟨decide (∀ x ∈ s, (p x).ret = true), ∑ x ∈ s, ((p x).time + 1)⟩

def imageT [DecidableEq β] (f : α → TimeM β) (s : Finset α) : TimeM (Finset β) :=
  ⟨s.image (fun x => (f x).ret), ∑ x ∈ s, ((f x).time + 1)⟩

-- An image whose elements are point sets: inserting a set costs its size.
--
def imageSetsT (f : α → TimeM (Finset Pt)) (s : Finset α) : TimeM (Finset (Finset Pt)) :=
  ⟨s.image (fun x => (f x).ret), ∑ x ∈ s, (let r := f x; r.time + r.ret.card)⟩

def biUnionT [DecidableEq β] (f : α → TimeM (Finset β)) (s : Finset α) : TimeM (Finset β) :=
  ⟨s.biUnion (fun x => (f x).ret), ∑ x ∈ s, (let r := f x; r.time + r.ret.card + 1)⟩

def sortT [LinearOrder α] (s : Finset α) : TimeM (List α) := ⟨s.sort (· ≤ ·), s.card ^ 2⟩

def pickT (S : Finset Pt) : TimeM (Option Pt) := ⟨TF.pick S, 2 * S.card + 2⟩

def lmapT (f : α → TimeM β) (l : List α) : TimeM (List β) :=
  ⟨l.map (fun x => (f x).ret), (l.map (fun x => (f x).time + 1)).sum⟩

def lfilterT (p : α → TimeM Bool) (l : List α) : TimeM (List α) :=
  ⟨l.filter (fun x => (p x).ret), (l.map (fun x => (p x).time + 1)).sum⟩

def lallT (p : α → TimeM Bool) (l : List α) : TimeM Bool :=
  ⟨l.all (fun x => (p x).ret), (l.map (fun x => (p x).time + 1)).sum⟩

def lanyT (p : α → TimeM Bool) (l : List α) : TimeM Bool :=
  ⟨l.any (fun x => (p x).ret), (l.map (fun x => (p x).time + 1)).sum⟩

def lflatMapT (f : α → TimeM (List β)) (l : List α) : TimeM (List β) :=
  ⟨l.flatMap (fun x => (f x).ret), (l.map (fun x => let r := f x; r.time + r.ret.length + 1)).sum⟩

def lfindT (p : α → TimeM Bool) (l : List α) : TimeM (Option α) :=
  ⟨l.find? (fun x => (p x).ret), (l.map (fun x => (p x).time + 1)).sum⟩

def lengthT (l : List α) : TimeM ℕ := ⟨l.length, l.length + 1⟩

def rangeT (n : ℕ) : TimeM (List ℕ) := ⟨List.range n, n + 1⟩

def toFinsetT [DecidableEq α] (l : List α) : TimeM (Finset α) := ⟨l.toFinset, l.length + 1⟩

/-! ## Constant-time helpers

These touch at most four elements and are charged by `tick` where they are used.
-/

-- Equality tests of points, edges and numbers.
--
def eqP (a b : Pt) : Bool := decide (a = b)
def eqE (a b : Edge) : Bool := decide (a = b)
def eqN (a b : ℕ) : Bool := decide (a = b)

-- The lighter of two weighted candidates (`MP.pick`), extending a weighted tail by one node,
-- and dropping the weight.
--
def pick2 {β : Type} (a b : Option (ℕ × β)) : Option (ℕ × β) := MP.pick a b
def extend (x : α) (wx : ℕ) (tf : Option (ℕ × List α)) : Option (ℕ × List α) :=
  tf.map (fun r => (wx + r.1, x :: r.2))
def dropW {β : Type} (r : Option (ℕ × β)) : Option β := r.map Prod.snd

-- The strip read off an optional length (at most one strip).
--
def optStrips (c : Pt) (s : Side) (o : Option ℕ) : Finset StripSpec :=
  (o.map (fun n => StripSpec.mk c s n)).toFinset

lemma card_cellE_le (c : Pt) : (cellE c).card ≤ 4 := by
  unfold cellE
  exact (card_insert_le _ _).trans (Nat.succ_le_succ ((card_insert_le _ _).trans
    (Nat.succ_le_succ ((card_insert_le _ _).trans (by simp)))))

lemma card_optStrips_le (c : Pt) (s : Side) (o : Option ℕ) : (optStrips c s o).card ≤ 1 := by
  unfold optStrips; cases o <;> simp

/-! ## Simp lemmas -/

@[simp] lemma ret_tick (n : ℕ) : (tick n).ret = () := rfl
@[simp] lemma time_tick (n : ℕ) : (tick n).time = n := rfl

lemma lsum_le {γ : Type} (l : List γ) (g : γ → ℕ) (c : ℕ) (h : ∀ x ∈ l, g x ≤ c) :
    (l.map g).sum ≤ l.length * c := by
  have := List.sum_le_length_nsmul (l.map g) c (by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hy
    exact h x hx)
  simpa using this

lemma fsum_le {γ : Type} (s : Finset γ) (g : γ → ℕ) (c : ℕ) (h : ∀ x ∈ s, g x ≤ c) :
    ∑ x ∈ s, g x ≤ s.card * c := by
  have := Finset.sum_le_card_nsmul s g c h
  simpa using this

lemma lmapT_time_le (f : α → TimeM β) (l : List α) (c : ℕ) (h : ∀ x ∈ l, (f x).time ≤ c) :
    (lmapT f l).time ≤ l.length * (c + 1) :=
  lsum_le l _ _ (fun x hx => by have := h x hx; omega)

lemma lfilterT_time_le (p : α → TimeM Bool) (l : List α) (c : ℕ) (h : ∀ x ∈ l, (p x).time ≤ c) :
    (lfilterT p l).time ≤ l.length * (c + 1) :=
  lsum_le l _ _ (fun x hx => by have := h x hx; omega)

lemma lallT_time_le (p : α → TimeM Bool) (l : List α) (c : ℕ) (h : ∀ x ∈ l, (p x).time ≤ c) :
    (lallT p l).time ≤ l.length * (c + 1) :=
  lsum_le l _ _ (fun x hx => by have := h x hx; omega)

lemma lanyT_time_le (p : α → TimeM Bool) (l : List α) (c : ℕ) (h : ∀ x ∈ l, (p x).time ≤ c) :
    (lanyT p l).time ≤ l.length * (c + 1) :=
  lsum_le l _ _ (fun x hx => by have := h x hx; omega)

lemma lfindT_time_le (p : α → TimeM Bool) (l : List α) (c : ℕ) (h : ∀ x ∈ l, (p x).time ≤ c) :
    (lfindT p l).time ≤ l.length * (c + 1) :=
  lsum_le l _ _ (fun x hx => by have := h x hx; omega)

lemma filterT_time_le (p : α → TimeM Bool) (s : Finset α) (c : ℕ) (h : ∀ x ∈ s, (p x).time ≤ c) :
    (filterT p s).time ≤ s.card * (c + 1) :=
  fsum_le s _ _ (fun x hx => by have := h x hx; omega)

lemma allT_time_le (p : α → TimeM Bool) (s : Finset α) (c : ℕ) (h : ∀ x ∈ s, (p x).time ≤ c) :
    (allT p s).time ≤ s.card * (c + 1) :=
  fsum_le s _ _ (fun x hx => by have := h x hx; omega)

lemma biUnionT_time_le [DecidableEq β] (f : α → TimeM (Finset β)) (s : Finset α) (c d : ℕ)
    (h : ∀ x ∈ s, (f x).time ≤ c) (hd : ∀ x ∈ s, (f x).ret.card ≤ d) :
    (biUnionT f s).time ≤ s.card * (c + d + 1) :=
  fsum_le s _ _ (fun x hx => by have := h x hx; have := hd x hx; dsimp only; omega)

end SolidGridHam.T
