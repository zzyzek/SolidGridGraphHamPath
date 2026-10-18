/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
import SolidGridHam.Path.Node

/-!
# The reduction after a successful phase

From a phase state `(H, BS)` with a success outcome, `reduceOut` applies a half bridge and then
the undo plan (`plan`, docs/S4_UNDO.md). In branch (a) the half bridge is the first merging
non-pair cell whose plan passes the compatibility conditions (`candOK`, rule (a*) of
docs/S4_RESIDUAL.md); the S4 theorem shows one passes.

`S4Spec` is the statement the S4 proof establishes: the result is a notch state with one piece fewer
than the start of the phase.
-/

namespace SolidGridHam

namespace HP

open Finset Classical

-- Pair points of a list of joiners.
--
def relPts (ops : List Join) (x : Pt) : Prop :=
  ∃ o ∈ ops, x = back1 o.c o.a ∨ x = front1 o.c o.a

-- The frame of an alternating cell in which its back and front are dark.
--
def altFrame (G : Finset Edge) (X : Pt) : Side := if bot X ∈ G then .t else .r

-- The conditions `undo_count` needs for the half bridge `M` with pair `uv`, applied to `H`
-- giving `G`; `k` bounds the half bridge's interior points.
--
def candOK (W : Finset Pt) (H G : Finset Edge) (BS : List Bridge) (M : Join) (k : ℕ)
    (uv : Pt × Pt) (s0 p0 : Pt) : Prop :=
  OpsOK W G (plan H BS uv) (relPts (M :: plan H BS uv)) s0 p0 ∧
    ∀ x, relPts (M :: plan H BS uv) x → ¬ IsMid M.c M.a k x

noncomputable def mergeJoin (H : Finset Edge) (X : Pt) : Join := ⟨X, altFrame H X, 1⟩

noncomputable def reduceOut (V W : Finset Pt) (s0 p0 : Pt) (H : Finset Edge) (BS : List Bridge) :
    POut → Finset Edge
  | .merge c =>
    let good := fun X => decide (Alt H X ∧ CutSq H X ∧
      ¬ (∃ b ∈ BS, X = b.cell (b.r - 2) ∨ X = b.E) ∧
      candOK W H ((mergeJoin H X).apply H) BS (mergeJoin H X) 0 (rowStartPair' (mergeJoin H X))
        s0 p0)
    let X := ((cellList V).find? good).getD c
    applyAll ((mergeJoin H X).apply H) (plan H BS (rowStartPair' (mergeJoin H X)))
  | .odd b => applyAll (flipCol H b.q b.a b.r) (plan H BS (rowStartPair b))
  | .twist b => applyAll (flipCol H b.q b.a b.r) (plan H BS (rowStartPair b))
  | _ => H
where
  rowStartPair' (M : Join) : Pt × Pt := (back1 M.c M.a, front1 M.c M.a)

-- **The S4 statement.** A success outcome (not `.stuck`, not `.fuel`) of a phase from a notch
-- state `H0` with at least two pieces yields a notch state with one piece fewer.
--
def S4Spec (V : Finset Pt) (s p : Pt) (e0 : Edge) : Prop :=
  ∀ (H0 H : Finset Edge) (BS : List Bridge) (out : POut), NotchF V s p e0 H0 →
    2 ≤ ncomp (insert p V) H0 → POK V H0 H BS out → out ≠ .stuck → out ≠ .fuel →
    NotchF V s p e0 (reduceOut V (insert p V) s p H BS out) ∧
      ncomp (insert p V) (reduceOut V (insert p V) s p H BS out) + 1 = ncomp (insert p V) H0

end HP

end SolidGridHam
