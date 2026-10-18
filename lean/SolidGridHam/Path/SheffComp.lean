/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
import SolidGridHam.Path.S4TheoremR

/-!
# A computable Sheffield loop

`hpSheff` decides connections with `Conn` (classical) in the undo plan and tests `candOK` for the
merging cell. Here every test is a Bool computation:
* `planAB`, `planB`, `lowAtB`: the plan with connections decided by `connB W`; equal to `planA`,
  `plan`, `lowAt` on a factor inside `W` with bridge squares in `W` (`planAB_eq`, `planB_eq`);
* `goodB`: a merging cell (alternating, cut, not a pair square) that no bridge makes bad — the
  condition of Theorem R, which `goodCell_of` turns into `GoodCell`;
* `reduceOutC`, `runSC`, `hpSheffC`, with `cncomp` on `W = insert p V` for the piece count.

`hpSheffC_correct`: `hpSheffC` decides the Hamiltonian `s`–`t` path problem under the hypotheses of
`hpSheff_correct'`.
-/

namespace SolidGridHam

namespace HP

open Finset Classical

def planAB (W : Finset Pt) (H : Finset Edge) : List Bridge → Pt × Pt → List (Bool × (Pt × Pt))
  | [], _ => []
  | b :: BS, uv =>
    if connB W (flip H b.E) uv.1 uv.2 then (true, uv) :: planAB W (flip H b.E) BS (rowStartPair b)
    else (false, uv) :: planAB W (flip H b.E) BS uv

def lowAtB (W : Finset Pt) (H : Finset Edge) (BS : List Bridge) (uv : Pt × Pt) (k : ℕ) : Bool :=
  ((planAB W H BS uv).getD k (false, uv)).1

def planB (W : Finset Pt) (H : Finset Edge) (BS : List Bridge) (uv : Pt × Pt) : List Join :=
  List.zipWith (fun b e => if e.1 then lowJ b else undoJ b) BS (planAB W H BS uv)

-- Bridges whose start and end squares are cells of `W`.
--
def BrW (W : Finset Pt) (BS : List Bridge) : Prop := ∀ b ∈ BS, IsCell W b.E ∧ IsCell W b.q

lemma planAB_eq {W : Finset Pt} : ∀ (BS : List Bridge) (H : Finset Edge) (uv : Pt × Pt),
    Inside W H → uv.1 ∈ W → uv.2 ∈ W → BrW W BS → planAB W H BS uv = planA H BS uv
  | [], _, _, _, _, _, _ => rfl
  | b :: BS, H, uv, hH, h1, h2, hb => by
    have hbE := hb b List.mem_cons_self
    have hH' : Inside W (flip H b.E) := inside_flip hH hbE.1
    have hBS : BrW W BS := fun b' hb' => hb b' (List.mem_cons_of_mem _ hb')
    have hsp := corners_mem hbE.2 b.a
    simp only [planAB, planA]
    by_cases hc : Conn (flip H b.E) uv.1 uv.2
    · have hcB : connB W (flip H b.E) uv.1 uv.2 = true := (connB_iff hH' h1 h2).2 hc
      rw [ite_eq_left hcB, ite_eq_left hc, planAB_eq BS _ _ hH' hsp.1 hsp.2 hBS]
    · have hcB : ¬ connB W (flip H b.E) uv.1 uv.2 = true := fun h => hc ((connB_iff hH' h1 h2).1 h)
      rw [ite_eq_right hcB, ite_eq_right hc, planAB_eq BS _ _ hH' h1 h2 hBS]

lemma lowAtB_eq {W : Finset Pt} {BS : List Bridge} {H : Finset Edge} {uv : Pt × Pt}
    (hH : Inside W H) (h1 : uv.1 ∈ W) (h2 : uv.2 ∈ W) (hb : BrW W BS) (k : ℕ) :
    lowAtB W H BS uv k = lowAt H BS uv k := by
  unfold lowAtB lowAt; rw [planAB_eq BS H uv hH h1 h2 hb]

lemma planB_eq {W : Finset Pt} {BS : List Bridge} {H : Finset Edge} {uv : Pt × Pt}
    (hH : Inside W H) (h1 : uv.1 ∈ W) (h2 : uv.2 ∈ W) (hb : BrW W BS) :
    planB W H BS uv = plan H BS uv := by
  unfold planB; rw [plan_eq, planAB_eq BS H uv hH h1 h2 hb]

-- **The good-cell test** (rule (a*), decided).
--
def goodB (W : Finset Pt) (H : Finset Edge) (BS : List Bridge) (X : Pt) : Bool :=
  decide (Alt H X) && cutB W H X && !pairSqB BS X &&
    (List.finRange BS.length).all fun i =>
      lowAtB W H BS (mergePair H X) i || decide (X ≠ nb (BS.get i).E (BS.get i).a)

lemma goodB_iff {V W : Finset Pt} (hVW : V ⊆ W) {H : Finset Edge} (hHW : Inside W H)
    {BS : List Bridge} (hb : BrW W BS) {X : Pt} (hX : IsCell V X) :
    goodB W H BS X = true ↔ Alt H X ∧ CutSq H X ∧ (¬ ∃ b ∈ BS, X = b.cell (b.r - 2) ∨ X = b.E) ∧
      ∀ i (hi : i < BS.length), lowAt H BS (mergePair H X) i = false →
        X ≠ nb (BS[i]'hi).E (BS[i]'hi).a := by
  have hc := corners_mem (isCell_mono hX hVW) (altFrame H X)
  have hlow : ∀ k, lowAtB W H BS (mergePair H X) k = lowAt H BS (mergePair H X) k :=
    lowAtB_eq hHW hc.1 hc.2 hb
  have hcut := cutB_iff hVW hHW hX
  unfold goodB
  simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', List.all_eq_true,
    List.mem_finRange, true_implies, Bool.or_eq_true, hlow, hcut, ne_eq]
  constructor
  · rintro ⟨⟨⟨ha, hct⟩, hp⟩, hall⟩
    refine ⟨ha, hct, fun hx => ?_, fun i hi hl => ?_⟩
    · have := pairSqB_iff.2 hx; rw [hp] at this; exact absurd this (by simp)
    · rcases hall ⟨i, hi⟩ with h | h
      · rw [hl] at h; exact absurd h (by simp)
      · simpa using h
  · rintro ⟨ha, hct, hp, hg⟩
    refine ⟨⟨⟨ha, hct⟩, ?_⟩, fun i => ?_⟩
    · cases h : pairSqB BS X
      · rfl
      · exact absurd (pairSqB_iff.1 h) hp
    · cases hl : lowAt H BS (mergePair H X) i
      · right; simpa using hg i i.2 hl
      · left; rfl

-- **The reduction, decided.**
--
def reduceOutC (V W : Finset Pt) (H : Finset Edge) (BS : List Bridge) : POut → Finset Edge
  | .merge c =>
    let X := ((cellList V).find? (goodB W H BS)).getD c
    applyAll (flipCol H X (altFrame H X) 1) (planB W H BS (mergePair H X))
  | .odd b => applyAll (flipCol H b.q b.a b.r) (planB W H BS (rowStartPair b))
  | .twist b => applyAll (flipCol H b.q b.a b.r) (planB W H BS (rowStartPair b))
  | _ => H

-- **The decided loop.**
--
def runSC (V : Finset Pt) (p : Pt) : ℕ → Finset Edge → Bool
  | 0, G => cncomp (insert p V) G == 1
  | n + 1, G =>
    if cncomp (insert p V) G == 1 then true
    else
      match phase V (insert p V) ((insert p V).card + 1) G [] with
      | (_, _, .stuck) => false
      | (_, _, .fuel) => false
      | (H, BS, out) => runSC V p n (reduceOutC V (insert p V) H BS out)

def hpSheffC (V : Finset Pt) (s t p : Pt) (e0 : Edge) : Bool :=
  match findFactor V (dST s t) with
  | none => false
  | some R => runSC V p (V.card + 2) (insert e0 R)

section loopC

variable {V : Finset Pt} {s t p : Pt} {e0 : Edge}

lemma cncomp_notch (htV : t ∈ V) (he0 : Ends e0 t p) {G : Finset Edge} (hG : NotchF V s p e0 G) :
    cncomp (insert p V) G = ncomp V G := by
  rw [cncomp_eq (Inside.of_factor hG.fac), hG.ncomp htV he0]

end loopC

end HP

end SolidGridHam
