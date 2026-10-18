/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
import ULHC.AFlip

/-!
# Grid symmetries and the planar lemma in every orientation

A grid isomorphism maps lattice points and edges bijectively, respecting ends. It
transports connectivity. The transpose `(x, y) ↦ (y, x)` and the reflection
`(x, y) ↦ (x, −y)` generate the symmetries of the square. They turn `planar_cell` into
the four forms used for the strip directions.
-/

namespace ULHC

open Finset

structure GridIso where
  f : Pt → Pt
  finv : Pt → Pt
  hf : ∀ x, finv (f x) = x
  hf' : ∀ x, f (finv x) = x
  g : Edge → Edge
  ginv : Edge → Edge
  hg : ∀ e, ginv (g e) = e
  hg' : ∀ e, g (ginv e) = e
  ends : ∀ e, Ends (g e) (f e.p) (f e.q)

namespace GridIso

variable (I : GridIso)

lemma adj_map {F : Finset Edge} {u v : Pt} (h : Adj F u v) : Adj (F.image I.g) (I.f u) (I.f v) := by
  obtain ⟨e, he, h⟩ := h
  refine ⟨I.g e, Finset.mem_image_of_mem _ he, ?_⟩
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [← h1, ← h2]
  · exact I.ends e
  · exact (I.ends e).swap

lemma conn_map {F : Finset Edge} {u v : Pt} (h : Conn F u v) :
    Conn (F.image I.g) (I.f u) (I.f v) :=
  ULHC.conn_map I.f (fun _ _ h => Conn.of_adj (I.adj_map h)) h

-- The inverse isomorphism.
--
def inv : GridIso where
  f := I.finv
  finv := I.f
  hf := I.hf'
  hf' := I.hf
  g := I.ginv
  ginv := I.g
  hg := I.hg'
  hg' := I.hg
  ends := by
    intro e
    have h := I.ends (I.ginv e)
    rw [I.hg'] at h
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · left; rw [h1, h2, I.hf, I.hf]; exact ⟨rfl, rfl⟩
    · right; rw [h1, h2, I.hf, I.hf]; exact ⟨rfl, rfl⟩

lemma conn_iff {F : Finset Edge} {u v : Pt} :
    Conn (F.image I.g) (I.f u) (I.f v) ↔ Conn F u v := by
  constructor
  · intro h
    have := I.inv.conn_map h
    simp only [inv, Finset.image_image, I.hf] at this
    have e : (I.ginv ∘ I.g) = id := funext I.hg
    rwa [e, Finset.image_id] at this
  · exact I.conn_map

lemma mem_image_iff {F : Finset Edge} {e : Edge} : I.g e ∈ F.image I.g ↔ e ∈ F := by
  constructor
  · intro h
    obtain ⟨e', he', h'⟩ := Finset.mem_image.1 h
    have : e' = e := by rw [← I.hg e', h', I.hg]
    rwa [← this]
  · exact Finset.mem_image_of_mem _

end GridIso

/-! ## Transpose and reflection -/

def tP (x : Pt) : Pt := (x.2, x.1)

def tE (e : Edge) : Edge :=
  match e.d with
  | .h => ⟨.v, tP e.p⟩
  | .v => ⟨.h, tP e.p⟩

def transposeIso : GridIso where
  f := tP
  finv := tP
  hf := fun _ => rfl
  hf' := fun _ => rfl
  g := tE
  ginv := tE
  hg := by intro e; obtain ⟨d, p⟩ := e; cases d <;> rfl
  hg' := by intro e; obtain ⟨d, p⟩ := e; cases d <;> rfl
  ends := by
    intro e; obtain ⟨d, p1, p2⟩ := e
    left; cases d <;> simp [tE, tP, Edge.q]

def rP (x : Pt) : Pt := (x.1, -x.2)

def rE (e : Edge) : Edge :=
  match e.d with
  | .h => ⟨.h, rP e.p⟩
  | .v => ⟨.v, (e.p.1, -e.p.2 - 1)⟩

def reflectIso : GridIso where
  f := rP
  finv := rP
  hf := fun _ => by simp [rP]
  hf' := fun _ => by simp [rP]
  g := rE
  ginv := rE
  hg := by intro e; obtain ⟨d, p1, p2⟩ := e; cases d <;> simp [rE, rP]
  hg' := by intro e; obtain ⟨d, p1, p2⟩ := e; cases d <;> simp [rE, rP]
  ends := by
    intro e; obtain ⟨d, p1, p2⟩ := e
    cases d
    · left; simp [rE, rP, Edge.q]
    · right; simp [rE, rP, Edge.q]; ring

end ULHC
