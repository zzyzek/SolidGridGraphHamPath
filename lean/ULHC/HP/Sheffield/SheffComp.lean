/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
import ULHC.HP.Sheffield.SheffieldMain

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

namespace ULHC

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

section comp

variable {V : Finset Pt} {s t p : Pt} {e0 : Edge}

lemma brW_of_reach (hpV : p ∉ V) (hsD : ∀ c, IsCell V c → ¬ IsCorner s c) (htV : t ∈ V)
    (he0 : Ends e0 t p) {H0 H : Finset Edge} (hN : NotchF V s p e0 H0) {BS : List Bridge}
    (hr : Reach V H0 H BS) : Inside (insert p V) H ∧ BrW (insert p V) BS := by
  have hVW : V ⊆ insert p V := Finset.subset_insert _ _
  have hinv := pinv_reach (t0 := t) (u0 := t) hVW (notch_dc (s := s) hpV hsD) hN.fac (notch_out htV he0 hN) hr
  refine ⟨Inside.of_factor hinv.fac, fun b hb => ?_⟩
  obtain ⟨_, htwo, _, cells⟩ := hinv.reg b hb
  refine ⟨isCell_mono (cells _ (by omega)) hVW, ?_⟩
  have := cells 0 (by omega)
  unfold Bridge.cell at this; rw [cellJ_zero] at this
  exact isCell_mono this hVW

-- **S4 for the decided reduction.**
--
theorem s4C (htV : t ∈ V) (hpV : p ∉ V) (he0 : Ends e0 t p)
    (hsD : ∀ c, IsCell V c → ¬ IsCorner s c) {H0 H : Finset Edge} {BS : List Bridge} {out : POut}
    (hN : NotchF V s p e0 H0) (_h2 : 2 ≤ ncomp (insert p V) H0) (hpok : POK V H0 H BS out)
    (hs : out ≠ .stuck) (hf : out ≠ .fuel) :
    NotchF V s p e0 (reduceOutC V (insert p V) H BS out) ∧
      ncomp (insert p V) (reduceOutC V (insert p V) H BS out) + 1 = ncomp (insert p V) H0 := by
  have hVW : V ⊆ insert p V := Finset.subset_insert _ _
  cases out with
  | stuck => exact absurd rfl hs
  | fuel => exact absurd rfl hf
  | odd g =>
    obtain ⟨hHW, hb⟩ := brW_of_reach hpV hsD htV he0 hN hpok.1
    have hc := corners_mem (isCell_mono hpok.2.2.1.1 hVW) g.a
    have := s4_odd htV hpV he0 hsD hN hpok
    simp only [reduceOut] at this
    simp only [reduceOutC]
    rw [planB_eq hHW hc.1 hc.2 hb]; exact this
  | twist g =>
    obtain ⟨hHW, hb⟩ := brW_of_reach hpV hsD htV he0 hN hpok.1
    have hc := corners_mem (isCell_mono hpok.2.2.1.1 hVW) g.a
    have := s4_twist htV hpV he0 hsD hN hpok
    simp only [reduceOut] at this
    simp only [reduceOutC]
    rw [planB_eq hHW hc.1 hc.2 hb]; exact this
  | merge c =>
    obtain ⟨hr, hc, ha, hcut, hnp⟩ := hpok
    obtain ⟨hHW, hb⟩ := brW_of_reach hpV hsD htV he0 hN hr
    have hdc := notch_dc (s := s) hpV hsD
    have hout0 := notch_out htV he0 hN
    simp only [reduceOutC]
    refine getD_spec (cellList V) _ c (fun X => NotchF V s p e0 (applyAll
        (flipCol H X (altFrame H X) 1) (planB (insert p V) H BS (mergePair H X))) ∧
      ncomp (insert p V) (applyAll (flipCol H X (altFrame H X) 1)
        (planB (insert p V) H BS (mergePair H X))) + 1 = ncomp (insert p V) H0) ?_ ?_
    · intro X hXl hg
      have hX := (mem_cellList.1 hXl).2
      obtain ⟨haX, hcX, hnpX, hgX⟩ := (goodB_iff hVW hHW hb hX).1 hg
      have hgc := goodCell_of hVW hdc hN.fac hout0 (Or.inl rfl) hsD hpV hr hX haX hcX hnpX hgX
      have := s4_good htV hpV he0 hsD hN hr hX hgc
      have hcc := corners_mem (isCell_mono hX hVW) (altFrame H X)
      rw [planB_eq hHW hcc.1 hcc.2 hb]
      exact this
    · obtain ⟨X, hX, haX, hcX, hnpX, hgX⟩ :=
        theoremR (t0 := t) (u0 := t) hVW hdc hN.fac hout0 (Or.inl rfl) (noOpp_same _ _ _) hr hc ha hcut hnp
      exact ⟨X, mem_cellList.2 ⟨by obtain ⟨x, y⟩ := X; exact hX.1, hX⟩,
        (goodB_iff hVW hHW hb hX).2 ⟨haX, hcX, hnpX, hgX⟩⟩

end comp

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

theorem runSC_sound (htV : t ∈ V) (hpV : p ∉ V) (he0 : Ends e0 t p)
    (hsD : ∀ c, IsCell V c → ¬ IsCorner s c) :
    ∀ n G, NotchF V s p e0 G → runSC V p n G = true →
      ∃ G', NotchF V s p e0 G' ∧ ncomp V G' = 1 := by
  intro n
  induction n with
  | zero =>
    intro G hG h
    simp only [runSC, beq_iff_eq] at h
    exact ⟨G, hG, by rw [← cncomp_notch htV he0 hG]; exact h⟩
  | succ n ih =>
    intro G hG h
    by_cases h1 : cncomp (insert p V) G = 1
    · exact ⟨G, hG, by rw [← cncomp_notch htV he0 hG]; exact h1⟩
    have h1' : (cncomp (insert p V) G == 1) = false := by simpa using h1
    simp only [runSC, h1', Bool.false_eq_true, ↓reduceIte] at h
    have hpok := notch_pok htV hpV he0 hsD hG ((insert p V).card + 1)
    have h2 : 2 ≤ ncomp (insert p V) G := by
      have := ncomp_pos (F := G) htV
      rw [hG.ncomp htV he0]; rw [cncomp_notch htV he0 hG] at h1; omega
    rcases hph : phase V (insert p V) ((insert p V).card + 1) G [] with ⟨H, BS, out⟩
    rw [hph] at h hpok
    cases out with
    | stuck => simp at h
    | fuel => simp at h
    | merge c => exact ih _ (s4C htV hpV he0 hsD hG h2 hpok (by simp) (by simp)).1 h
    | odd b => exact ih _ (s4C htV hpV he0 hsD hG h2 hpok (by simp) (by simp)).1 h
    | twist b => exact ih _ (s4C htV hpV he0 hsD hG h2 hpok (by simp) (by simp)).1 h

theorem runSC_complete (hs : Solid V) (hst : s ≠ t) (htV : t ∈ V) (hpV : p ∉ V)
    (he0 : Ends e0 t p) (hsD : ∀ c, IsCell V c → ¬ IsCorner s c)
    (hHP : ∃ H, IsFactor V (dST s t) H ∧ ncomp V H = 1) :
    ∀ n G, NotchF V s p e0 G → ncomp V G ≤ n + 1 → runSC V p n G = true := by
  intro n
  induction n with
  | zero =>
    intro G hG hle
    have := ncomp_pos (F := G) htV
    simp only [runSC, beq_iff_eq, cncomp_notch htV he0 hG]; omega
  | succ n ih =>
    intro G hG hle
    by_cases h1 : ncomp V G = 1
    · simp [runSC, cncomp_notch htV he0 hG, h1]
    have h2 : 2 ≤ ncomp V G := by have := ncomp_pos (F := G) htV; omega
    have h1' : (cncomp (insert p V) G == 1) = false := by
      simpa [cncomp_notch htV he0 hG] using h1
    simp only [runSC, h1', Bool.false_eq_true, ↓reduceIte]
    have hpok := notch_pok htV hpV he0 hsD hG ((insert p V).card + 1)
    have hfuel := phase_fuel (t0 := t) (u0 := t) (Finset.subset_insert _ _) (notch_dc hpV hsD) hG.fac
      (notch_out htV he0 hG) ((insert p V).card + 1) G [] Reach.base (by omega)
    have h2' : 2 ≤ ncomp (insert p V) G := by rw [hG.ncomp htV he0]; exact h2
    rcases hph : phase V (insert p V) ((insert p V).card + 1) G [] with ⟨H, BS, out⟩
    rw [hph] at hpok
    dsimp only at hpok
    have hfuel' := fun H' BS' => hfuel H' BS'
    rw [hph] at hfuel'
    cases out with
    | stuck =>
      obtain ⟨hr, hm, hk'⟩ := hpok
      exact absurd hHP (phase_no_hp hs hst htV hpV he0 hsD hG h2 hr hm hk')
    | fuel => exact absurd rfl (hfuel' H BS)
    | merge c =>
      obtain ⟨hN, hc⟩ := s4C htV hpV he0 hsD hG h2' hpok (by simp) (by simp)
      rw [hN.ncomp htV he0, hG.ncomp htV he0] at hc
      exact ih _ hN (by show ncomp V (reduceOutC V (insert p V) H BS (POut.merge c)) ≤ n + 1; omega)
    | odd b =>
      obtain ⟨hN, hc⟩ := s4C htV hpV he0 hsD hG h2' hpok (by simp) (by simp)
      rw [hN.ncomp htV he0, hG.ncomp htV he0] at hc
      exact ih _ hN (by show ncomp V (reduceOutC V (insert p V) H BS (POut.odd b)) ≤ n + 1; omega)
    | twist b =>
      obtain ⟨hN, hc⟩ := s4C htV hpV he0 hsD hG h2' hpok (by simp) (by simp)
      rw [hN.ncomp htV he0, hG.ncomp htV he0] at hc
      exact ih _ hN (by show ncomp V (reduceOutC V (insert p V) H BS (POut.twist b)) ≤ n + 1; omega)

-- **Correctness of the decided Sheffield loop.**
--
theorem hpSheffC_correct (hs : Solid V) (hst : s ≠ t) (htV : t ∈ V) (hpV : p ∉ V)
    (he0 : Ends e0 t p) (hsD : ∀ c, IsCell V c → ¬ IsCorner s c) :
    hpSheffC V s t p e0 = true ↔ ∃ H, IsFactor V (dST s t) H ∧ ncomp V H = 1 := by
  constructor
  · intro h
    unfold hpSheffC at h
    rcases hR : findFactor V (dST s t) with _ | R
    · rw [hR] at h; simp at h
    rw [hR] at h
    obtain ⟨G, hG, h1⟩ := runSC_sound htV hpV he0 hsD _ _
      (notch_up hst htV hpV he0 (findFactor_some (dST_le s t) hR)) h
    exact ⟨_, notch_down hst htV hpV he0 hG h1⟩
  · intro hHP
    unfold hpSheffC
    rcases hR : findFactor V (dST s t) with _ | R
    · obtain ⟨H, hH, _⟩ := hHP
      exact absurd ⟨H, hH⟩ (findFactor_none (dST_le s t) hR)
    have := ncomp_le_card (X := V) (F := insert e0 R)
    exact runSC_complete hs hst htV hpV he0 hsD hHP _ _
      (notch_up hst htV hpV he0 (findFactor_some (dST_le s t) hR)) (by omega)

end loopC

end HP

end ULHC
