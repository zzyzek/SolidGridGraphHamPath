/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
import ULHC.HP.NearCAPF1
import ULHC.HP.StackedPF
import ULHC.HP.GeoChainLoc
import ULHC.HP.PhantomSide

/-!
# Near lemmas for comp_clean, part 2 (path-factors, rule Tg)

* `link_a_pf`: ULHC `link_a` with degree at most 2.
* `link_end_splits`: the end cell of a linked strip splits (its flip raises the count by one).
* `end_not_twists`, `beyond_not_twists`: a count-neutral strip's end cell, and the cell beyond
  it, do not twist. These close the two cases where ULHC uses parity on a last strip
  (rule Tg allows even last strips with a twisting end cell).
-/

namespace ULHC

namespace HP

open Finset Classical

-- A suffix of a restricted strip is restricted.
--
lemma restr_suf {s0 t0 : Pt} {z : StripSpec} {i : ℕ} (h : Restr s0 t0 z) :
    Restr s0 t0 (suf z i) := by
  intro j hj
  rw [suf_cellJ]
  exact h (i + j) (by simp only [suf] at hj; omega)

-- **`link_a` with degree at most 2.**
--
theorem link_a_pf {V : Finset Pt} {G : Finset Edge} {a : StripSpec} (hle : ∀ z, deg G z ≤ 2)
    (ha : ValidStrip V G a) (hae : a.n % 2 = 0) (ha2 : 2 ≤ a.n)
    {w : StripSpec} (hw1 : 1 ≤ w.n) (hpw : StripPat G w.c w.s w.n)
    (hcw : ∀ j < w.n, IsCell V (cellJ w.c w.s j)) (hnt : ¬ Touches a w)
    (hcg : Conn G (back1 w.c w.s) (front1 w.c w.s))
    (hcu : ¬ Conn (flip G (endCell a)) (back1 w.c w.s) (front1 w.c w.s)) : CR2 V G a w := by
  obtain ⟨k, hk⟩ : ∃ k, a.n = k + 2 := ⟨a.n - 2, by omega⟩
  obtain ⟨_, hpa, hca, _⟩ := ha
  rw [hk] at hpa hca
  have hcell : ∀ j ≤ k + 1, IsCell V (cellJ a.c a.s j) := fun j hj => hca j (by omega)
  have hoff : ∀ j < w.n, ∀ i < a.n, ∀ x ∈ cellE (cellJ w.c w.s j), x ∉ cellE (cellJ a.c a.s i) :=
    fun j hj i hi x hx hx' => hnt ⟨j, hj, i, hi, x, hx, hx'⟩
  have hend : endCell a = cellJ a.c a.s (a.n - 1) := rfl
  have hmid : ∀ p, (∃ j < w.n, ∃ x ∈ G, (x.p = p ∨ x.q = p) ∧ x ∈ cellE (cellJ w.c w.s j)) →
      ¬ IsMid a.c a.s (a.n - 2) p := by
    rintro p ⟨j, hj, x, hx, hxp, hxw⟩ hm
    rw [hk, show k + 2 - 2 = k by omega] at hm
    obtain ⟨i, hi, hxi⟩ := mid_touch_L hle hpa hm hx hxp
    exact hoff j hj i (by omega) x hxw hxi
  obtain ⟨⟨hb, hbp, hb0⟩, hfr⟩ := start_corner_edges hpw hw1
  refine ⟨ha2, hae, hw1, (pat_flip_off hw1 (fun j hj x hx => by
      rw [hend]; exact hoff j hj _ (by omega) x hx)).2 hpw, hcw,
    fun j hj i hi x hx => hoff j hj i (by omega) x hx, ?_, ?_,
    hmid _ ⟨0, by omega, _, hb, hbp, hb0⟩, hmid _ hfr, hcg, hcu⟩
  · intro j hj heq
    have := side_mem_self (cellJ w.c w.s j) .b
    exact hoff j hj (a.n - 1) (by omega) _ this (by rw [← hend, ← heq]; exact this)
  · intro _ x hx
    rw [hend]; exact hoff _ (by omega) _ (by omega) x hx

-- **A linked strip's end cell splits.** Its flip separates the next strip's start pair, which
-- `F` joins; with its lateral sides in one class the flip cannot merge, so it splits.
--
theorem link_end_splits {V : Finset Pt} {F : Finset Edge} {σ τ : StripSpec} (hl : CR2 V F σ τ)
    (hu : IsCell V (endCell σ)) (lu1 : lat1 (endCell σ) σ.s ∈ F) (lu2 : lat2 (endCell σ) σ.s ∈ F)
    (bu : back (endCell σ) σ.s ∉ F) (fu : front (endCell σ) σ.s ∉ F)
    (hsame : Conn F (back1 (endCell σ) σ.s) (back2 (endCell σ) σ.s)) :
    ncomp V (flip F (endCell σ)) = ncomp V F + 1 := by
  obtain ⟨_, _, hτ1, _, hcτ, _, _, _, _, _, hcg, hcu⟩ := hl
  have hE := mkLat_cellE (endCell σ) σ.s
  have hfe := (mkLat (endCell σ) σ.s).flip_eq hE lu1 lu2 bu fu
  obtain ⟨ub1, ub2, uf1, uf2⟩ := isCell_corners hu σ.s
  have hb := flip_same_count (V := V) (mkLat (endCell σ) σ.s) ub1 uf1 ub2 uf2 lu1 lu2 hsame
  have hc0 : IsCell V τ.c := by have := hcτ 0 (by omega); rwa [cellJ_zero] at this
  obtain ⟨tb1, _, tf1, _⟩ := isCell_corners hc0 τ.s
  have hlt := ncomp_lt_of_refine (V := V)
    (fun x _ y _ h => flip_same_conn (mkLat (endCell σ) σ.s) lu1 lu2 hsame x y h) tb1 tf1 hcg
    (by rw [← hfe]; exact hcu)
  rw [hfe]
  omega

section ends

variable {V : Finset Pt} {F : Finset Edge} {c : Pt} {s : Side} {k : ℕ} {s0 t0 : Pt}
  (hF : Deg2Off V F s0 t0) (hs0 : s0 ∈ V) (hds : deg F s0 = 1) (hle : ∀ z, deg F z ≤ 2)
  (hk : k % 2 = 0) (hcell : ∀ j ≤ k + 1, IsCell V (cellJ c s j))
  (hcor : ∀ j ≤ k + 1, ¬ IsCorner s0 (cellJ c s j) ∧ ¬ IsCorner t0 (cellJ c s j))
  (hpat : StripPat F c s (k + 2)) (hsep : ¬ Conn F (back1 c s) (front1 c s))
  (hsame : Conn F (back1 (cellJ c s (k + 1)) s) (back2 (cellJ c s (k + 1)) s))
  (hneut : ncomp V (flipCol F c s (k + 2)) = ncomp V F)
include hF hs0 hds hk hcell hcor hpat hsep hsame hneut

-- The end cell's frame: lateral sides dark, back and front light.
--
omit hF hs0 hds hcell hcor hsep hsame hneut in
lemma end_frame_pf : lat1 (cellJ c s (k + 1)) s ∈ F ∧ lat2 (cellJ c s (k + 1)) s ∈ F ∧
    back (cellJ c s (k + 1)) s ∉ F ∧ front (cellJ c s (k + 1)) s ∉ F := by
  obtain ⟨a1, a2, ab, af⟩ := strip_sig hpat (show k + 1 < k + 2 by omega)
  exact ⟨a1.2 (by omega), a2.2 (by omega), fun h => by have := ab.1 h; omega,
    fun h => by have := (af.1 h).1 (by omega); omega⟩

-- **A count-neutral strip's end cell does not twist** (it splits: `neutral_end_splits`).
--
theorem end_not_twists : ¬ TwistsIn V F (cellJ c s (k + 1)) := by
  rintro ⟨_, heq⟩
  obtain ⟨el1, el2, eb, ef⟩ := end_frame_pf hk hpat
  exact neutral_end_splits k hk F hF hs0 hds hcell hcor hpat hsep hsame hneut
    ((twists_iff_conn (hcell (k + 1) le_rfl) el1 el2 eb ef hsame).1 heq)

-- **The cell beyond a count-neutral strip's end cell does not twist** (case G1): stacked on
-- the end cell, it twists iff the end cell does (`stacked_twist`).
--
include hle in
theorem beyond_not_twists (hu : IsCell V (nb (cellJ c s (k + 1)) s))
    (ul1 : lat1 (nb (cellJ c s (k + 1)) s) s ∈ F) (ul2 : lat2 (nb (cellJ c s (k + 1)) s) s ∈ F)
    (uf : front (nb (cellJ c s (k + 1)) s) s ∉ F) : ¬ TwistsIn V F (nb (cellJ c s (k + 1)) s) := by
  rintro ⟨_, heq⟩
  obtain ⟨el1, el2, eb, ef⟩ := end_frame_pf hk hpat
  have hfr : Conn F (front1 (cellJ c s (k + 1)) s) (front2 (cellJ c s (k + 1)) s) :=
    (((ends_lat1 _ s).conn el1).symm.trans hsame).trans ((ends_lat2 _ s).conn el2)
  have := (stacked_twist hle (hcell (k + 1) le_rfl) hu el1 el2 eb ef ul1 ul2 uf hfr).2 heq
  exact end_not_twists hF hs0 hds hk hcell hcor hpat hsep hsame hneut ⟨alt_of_lats el1 el2 eb ef, this⟩

end ends

-- A corner of a restricted cell has degree 2.
--
lemma deg_corner_restr {V : Finset Pt} {F : Finset Edge} {s0 t0 d z : Pt}
    (hF : Deg2Off V F s0 t0) (hd : IsCell V d) (hr : ¬ IsCorner s0 d ∧ ¬ IsCorner t0 d)
    (hz : IsCorner z d) : deg F z = 2 :=
  hF.2 z (corner_mem hd hz) (fun h => hr.1 (h ▸ hz)) (fun h => hr.2 (h ▸ hz))

-- Paths through `a` (Tg version of ULHC `ViaFree`): none of weight below `W2` whose tail keeps
-- off `a`.
--
def ViaFreeTg (V : Finset Pt) (F : Finset Edge) (s0 t0 : Pt) (a : StripSpec) (W2 : ℕ) : Prop :=
  ∀ w R, RPathTg V F s0 t0 a (w :: R) → (∀ x ∈ R, ¬ Touches a x) →
    (R ≠ [] → ∀ j < a.n, ∀ y ∈ cellE (endCell w), y ∉ cellE (cellJ a.c a.s j)) →
    wt a (w :: R) < W2 → False

-- **NEW MATH (phantom start side, configuration B).** `touch_core_pf` when `t0 ∉ V`. Its proof
-- closes except where the touching chain strip passes sideways through the cell behind `c` at its
-- first patterned index (odd), next to a pseudo-Type III square beside `c`.
--
def Gap_core : Prop :=
  ∀ {V : Finset Pt} {F : Finset Edge} {c : Pt} {s : Side} {k : ℕ} {s0 t0 : Pt} {W : ℕ}
    {σ τ : StripSpec} {i0 : ℕ} {L2 : List StripSpec} {W2 : ℕ} {i j : ℕ} {x : Edge},
    Deg2Off V F s0 t0 → s0 ∈ V → deg F s0 = 1 → (∀ z, deg F z ≤ 2) → NoTypeIIIR V F s0 t0 →
    k % 2 = 0 → (∀ j ≤ k + 1, IsCell V (cellJ c s j)) →
    (∀ j ≤ k + 1, ¬ IsCorner s0 (cellJ c s j) ∧ ¬ IsCorner t0 (cellJ c s j)) →
    StripPat F c s (k + 2) → ¬ Conn F (back1 c s) (front1 c s) →
    NoTypeIIIR V (flipCol F c s (k + 2)) s0 t0 → ncomp V (flipCol F c s (k + 2)) = ncomp V F →
    (∀ tf, (tf = latA s ∨ tf = latB s) → IsCell V (nb c tf) → NotTypeIII V F (nb c tf)) →
    (∀ tf, (tf = latA s ∨ tf = latB s) → IsCell V (nb (cellJ c s (k + 1)) tf) →
      NotTypeIII V (flipCol F c s (k + 2)) (nb (cellJ c s (k + 1)) tf)) →
    (∀ tf, (tf = latA s ∨ tf = latB s) → IsCell V (nb (nb c tf) s.opp) →
      NotTypeIII V F (nb (nb c tf) s.opp)) →
    (∀ σ L', RPathTg V F s0 t0 σ L' → W ≤ wt σ L') →
    CR2 V F σ τ → SigFrom F τ.c τ.s τ.n i0 → i0 ≤ 1 → (i0 = 0 → NoChain σ τ) →
    (i0 = 1 → τ.c ≠ cellJ c s (k + 1)) → EndOK V F σ → σ.n % 2 = 0 → Restr s0 t0 σ →
    CRChainTg V F τ L2 → CATail (τ :: L2) → (∀ x ∈ τ :: L2, Restr s0 t0 x) →
    (∀ w ∈ L2, ¬ Touches ⟨c, s, k + 2⟩ w) → ViaFreeTg V F s0 t0 ⟨c, s, k + 2⟩ W2 →
    wt τ L2 < W → k + 2 + wt τ L2 < W2 → i0 ≤ i → i < τ.n → j < k + 2 →
    x ∈ cellE (cellJ τ.c τ.s i) → x ∈ cellE (cellJ c s j) →
    ¬ PDang V t0 → (¬ ∃ σ' L', RPathTg V (flipCol F c s (k + 2)) s0 t0 σ' L') → t0 ∉ V → False

-- **NEW MATH (phantom start side, behind `c`).** `touch_contra_chain_pf` when `t0 ∉ V`. Its proof
-- closes except where a chain strip starts behind `c` next to a pseudo-Type III square beside `c`.
--
def Gap_chain : Prop :=
  ∀ {V : Finset Pt} {F : Finset Edge} {c : Pt} {s : Side} {k : ℕ} {s0 t0 : Pt} {W : ℕ}
    {σ τ : StripSpec} {L2 : List StripSpec} {W2 : ℕ},
    Deg2Off V F s0 t0 → s0 ∈ V → deg F s0 = 1 → (∀ z, deg F z ≤ 2) → NoTypeIIIR V F s0 t0 →
    k % 2 = 0 → (∀ j ≤ k + 1, IsCell V (cellJ c s j)) →
    (∀ j ≤ k + 1, ¬ IsCorner s0 (cellJ c s j) ∧ ¬ IsCorner t0 (cellJ c s j)) →
    StripPat F c s (k + 2) → ¬ Conn F (back1 c s) (front1 c s) →
    NoTypeIIIR V (flipCol F c s (k + 2)) s0 t0 → ncomp V (flipCol F c s (k + 2)) = ncomp V F →
    (∀ tf, (tf = latA s ∨ tf = latB s) → IsCell V (nb c tf) → NotTypeIII V F (nb c tf)) →
    (∀ tf, (tf = latA s ∨ tf = latB s) → IsCell V (nb (cellJ c s (k + 1)) tf) →
      NotTypeIII V (flipCol F c s (k + 2)) (nb (cellJ c s (k + 1)) tf)) →
    (∀ tf, (tf = latA s ∨ tf = latB s) → IsCell V (nb (nb c tf) s.opp) →
      NotTypeIII V F (nb (nb c tf) s.opp)) →
    (∀ σ L', RPathTg V F s0 t0 σ L' → W ≤ wt σ L') →
    CR2 V F σ τ → ChainOK σ τ → ¬ NoChain σ τ → EndOK V F σ → σ.n % 2 = 0 → Restr s0 t0 σ →
    CRChainTg V F τ L2 → CATail (τ :: L2) → (∀ x ∈ τ :: L2, Restr s0 t0 x) →
    (∀ w ∈ L2, ¬ Touches ⟨c, s, k + 2⟩ w) → ViaFreeTg V F s0 t0 ⟨c, s, k + 2⟩ W2 →
    wt τ L2 < W → k + 2 + wt τ L2 < W2 →
    ¬ PDang V t0 → (¬ ∃ σ' L', RPathTg V (flipCol F c s (k + 2)) s0 t0 σ' L') → t0 ∉ V → ¬ Touches ⟨c, s, k + 2⟩ τ

-- **The near lemma's open sites**, all at phantom endpoints (`t0 ∉ V`).
--
def NearGaps : Prop := Gap_beyond ∧ Gap_start ∧ Gap_core ∧ Gap_chain

-- The endpoint `t0` is in `V` (then the near lemma is proved), or the near lemma's gaps hold.
--
class NearOK (V : Finset Pt) (t0 : Pt) : Prop where
  ok : t0 ∈ V ∨ PDang V t0 ∨ NearGaps

instance NearOK.toNearOK1 {V : Finset Pt} {t0 : Pt} [h : NearOK V t0] : NearOK1 V t0 :=
  ⟨h.ok.imp_right (Or.imp_right (·.1))⟩

instance NearOK.toNearOK2 {V : Finset Pt} {t0 : Pt} [h : NearOK V t0] : NearOK2 V t0 :=
  ⟨h.ok.imp_right (Or.imp_right (·.2.1))⟩

lemma NearOK.of_mem {V : Finset Pt} {t0 : Pt} (h : t0 ∈ V) : NearOK V t0 := ⟨Or.inl h⟩

lemma NearOK.of_pdang {V : Finset Pt} {t0 : Pt} (h : PDang V t0) : NearOK V t0 := ⟨Or.inr (Or.inl h)⟩

section nearpathPF

variable {V : Finset Pt} {F : Finset Edge} {c : Pt} {s : Side} {k : ℕ} {s0 t0 : Pt}
  (hF : Deg2Off V F s0 t0) (hs0 : s0 ∈ V) (hds : deg F s0 = 1) (hle : ∀ z, deg F z ≤ 2)
  (hTR : NoTypeIIIR V F s0 t0) (hk : k % 2 = 0)
  (hcell : ∀ j ≤ k + 1, IsCell V (cellJ c s j))
  (hcor : ∀ j ≤ k + 1, ¬ IsCorner s0 (cellJ c s j) ∧ ¬ IsCorner t0 (cellJ c s j))
  (hpat : StripPat F c s (k + 2))
  (hsep : ¬ Conn F (back1 c s) (front1 c s)) (hT' : NoTypeIIIR V (flipCol F c s (k + 2)) s0 t0)
  (hneut : ncomp V (flipCol F c s (k + 2)) = ncomp V F)
  (hTs : ∀ tf, (tf = latA s ∨ tf = latB s) → IsCell V (nb c tf) → NotTypeIII V F (nb c tf))
  (hTend : ∀ tf, (tf = latA s ∨ tf = latB s) → IsCell V (nb (cellJ c s (k + 1)) tf) →
    NotTypeIII V (flipCol F c s (k + 2)) (nb (cellJ c s (k + 1)) tf))
  (hTd : ∀ tf, (tf = latA s ∨ tf = latB s) → IsCell V (nb (nb c tf) s.opp) →
    NotTypeIII V F (nb (nb c tf) s.opp))
  {W : ℕ} (hmin : ∀ σ L', RPathTg V F s0 t0 σ L' → W ≤ wt σ L')
include hF hs0 hds hle hTR hk hcell hcor hpat hsep hT' hneut hTs hTend hTd hmin

-- **The last touching strip** (ULHC `touch_contra_plain`, rule Tg). In a minimum path, a strip
-- `τ` after the second, all of whose successors keep off `a`, does not touch `a` either. The
-- two endings ULHC excludes by parity are even Tg endings here, excluded because neither the
-- end cell of `a` nor the cell beyond it twists.
--
theorem touch_contra_plain_pf [hg : NearOK V t0] {σ τ : StripSpec} {L2 : List StripSpec} (hl : CR2 V F σ τ)
    (hnc : NoChain σ τ) (hσ : EndOK V F σ) (hσe : σ.n % 2 = 0) (hσR : Restr s0 t0 σ)
    (hch : CRChainTg V F τ L2) (hnct : CATail (τ :: L2)) (hR : ∀ x ∈ τ :: L2, Restr s0 t0 x)
    (hfar2 : ∀ w ∈ L2, ¬ Touches ⟨c, s, k + 2⟩ w)
    {W2 : ℕ} (hvia : ViaFreeTg V F s0 t0 ⟨c, s, k + 2⟩ W2)
    (hnoA : t0 ∉ V → ¬ PDang V t0 → ¬ ∃ σ' L', RPathTg V (flipCol F c s (k + 2)) s0 t0 σ' L') (hW1 : wt τ L2 < W)
    (hW2 : k + 2 + wt τ L2 < W2) :
    ¬ Touches ⟨c, s, k + 2⟩ τ := by
  rintro ⟨i, hi, j, hj, x, hx1, hx2⟩
  have nopath : ∀ σ' L', RPathTg V F s0 t0 σ' L' → wt σ' L' < W → False :=
    fun σ' L' h hlt => by have := hmin σ' L' h; omega
  have hDc := corners_deg2 hF hcell hcor
  have hTe : NotTypeIII V F (cellJ c s (k + 1)) :=
    restr_notT3 hTR (hcell (k + 1) le_rfl) (hcor (k + 1) le_rfl)
  have hsame := end_same_loc hTe hk hcell hpat
  have hca : ∀ j < k + 2, IsCell V (cellJ c s j) := fun j hj => hcell j (by omega)
  have hva : ValidStrip V F ⟨c, s, k + 2⟩ := ⟨by show 1 ≤ k + 2; omega, hpat, hca, hsep⟩
  have hcorR : Restr s0 t0 ⟨c, s, k + 2⟩ := fun j hj => hcor j (by simp only at hj; omega)
  have hτR : Restr s0 t0 τ := hR τ (List.mem_cons_self ..)
  have hl0 := hl
  set e := cellJ c s (k + 1) with he_def
  obtain ⟨h2σ, _, hτ1, hpτu, hcτ, hso, hne, hen, _, _, hcg, hcu⟩ := hl
  have hpτ : StripPat F τ.c τ.s τ.n := (pat_flip_off hτ1 hnc).1 hpτu
  obtain ⟨hu, lu1, lu2, bu, fu⟩ := hσ hσe
  set u' := endCell σ
  have hu'R : ¬ IsCorner s0 u' ∧ ¬ IsCorner t0 u' := hσR (σ.n - 1) (by omega)
  have hsameU : Conn F (back1 u' σ.s) (back2 u' σ.s) :=
    (frame_of_allConn (alt_corners_conn' (restr_notT3 hTR hu hu'R) (alt_of_lats lu1 lu2 bu fu))
      σ.s).1
  have hspw : ncomp V (flip F u') = ncomp V F + 1 := link_end_splits hl0 hu lu1 lu2 bu fu hsameU
  have hae : (⟨c, s, k + 2⟩ : StripSpec).n % 2 = 0 := by show (k + 2) % 2 = 0; omega
  have ha2 : 2 ≤ (⟨c, s, k + 2⟩ : StripSpec).n := by show 2 ≤ k + 2; omega
  -- Shortcut through `a` to the successor `w` of `τ`, once `w`'s start is split by `e`.
  --
  have via_a : ∀ w L3, L2 = w :: L3 → StripPat F w.c w.s w.n →
      ¬ Conn (flip F e) (back1 w.c w.s) (front1 w.c w.s) → False := by
    intro w L3 hL hpw hsplit
    subst hL
    obtain ⟨_, hlw, hrest⟩ := hch
    have hnt := hfar2 w (List.mem_cons_self ..)
    have hw1 : 1 ≤ w.n := hlw.2.2.1
    have hlink : CR2 V F ⟨c, s, k + 2⟩ w := link_a_pf hle hva hae ha2 hw1 hpw hlw.2.2.2.2.1 hnt
      hlw.2.2.2.2.2.2.2.2.2.2.1 hsplit
    refine hvia w L3 ⟨hva, ⟨hae, hlink, hrest⟩,
      ⟨chainOK_of_noChain (fun jw hjw y hy hye => hnt ⟨jw, hjw, k + 1, by show k + 1 < k + 2; omega,
        y, hy, hye⟩), hnct.2⟩, ?_⟩
      (fun x hx => hfar2 x (List.mem_cons_of_mem _ hx))
      (fun _ j hj y hy hy' => hnt ⟨w.n - 1, by omega, j, hj, y, by unfold endCell at hy; exact hy, hy'⟩) ?_
    · intro x hx
      rcases List.mem_cons.1 hx with rfl | hx
      · exact hcorR
      · exact hR x (List.mem_cons_of_mem _ hx)
    · rw [wt_cons]; rw [wt_cons] at hW2; show k + 2 + wt w L3 < W2; omega
  have hτc0 : cellJ τ.c τ.s 0 = τ.c := cellJ_zero τ.c τ.s
  obtain ⟨el1, el2, eb, ef⟩ := end_frame_pf hk hpat
  have hce : IsCell V e := hcell (k + 1) le_rfl
  have hc0 : IsCell V c := by have := hcell 0 (by omega); rwa [cellJ_zero] at this
  -- **Through the end cell.**
  --
  have hR1 : ∀ i' < τ.n, cellJ τ.c τ.s i' = e → False := by
    intro i' hi' hq
    obtain ⟨hend, hdir⟩ := touch_end_L hk hpat (sig_of_pat hpτ) (Nat.zero_le _) hi' hq
    have hendτ : endCell τ = e := by
      unfold endCell; rw [← hq, show τ.n - 1 = i' by omega]
    rcases hdir with ⟨_, hodd⟩ | ⟨hperp, hev⟩
    · cases L2 with
      | nil =>
        rcases (hch : TgEnd V F τ) with h | ⟨_, htw⟩
        · omega
        · rw [hendτ] at htw
          exact end_not_twists hF hs0 hds hk hcell hcor hpat hsep hsame hneut htw
      | cons w L3 =>
        have hlw := hch.2.1
        have hnt := hfar2 w (List.mem_cons_self ..)
        have hpw : StripPat F w.c w.s w.n := by
          have h := hlw.2.2.2.1
          rw [hendτ] at h
          exact (pat_flip_off hlw.2.2.1 (fun jw hjw y hy hy' =>
            hnt ⟨jw, hjw, k + 1, by show k + 1 < k + 2; omega, y, hy, hy'⟩)).1 h
        have hsplit := hlw.2.2.2.2.2.2.2.2.2.2.2
        rw [hendτ] at hsplit
        exact via_a w L3 rfl hpw hsplit
    · by_cases hi0 : i' = 0
      · subst hi0
        rw [hτc0] at hq
        have hwe : u' ≠ e := fun h => hne 0 (by omega) (by rw [hτc0, hq, h])
        have hwu : u' ≠ nb e s := fun h => hnc 0 (by omega) (sideEdge e s)
          (by rw [hτc0, hq]; exact side_mem_self e s)
          (by show sideEdge e s ∈ cellE u'; rw [h]; exact side_mem_nb e s)
        have hoff : ∀ y ∈ cellE e, y ∉ cellE u' := fun y hy =>
          hnc 0 (by omega) y (by rw [hτc0, hq]; exact hy)
        have m1 : lat1 e s ∈ cellE e := by rw [cellE_frame e s]; simp
        have m2 : lat2 e s ∈ cellE e := by rw [cellE_frame e s]; simp
        have hsp := hcu
        rw [hq] at hsp
        exact split_core_pf hF hs0 hds hle hTR hk hcell hcor hpat hsep hT' hneut
          (fun hj _ hx1 hx2 => alt_touch_pfD hF hs0 hTR hk hcell hcor hpat hsep hTs
            hu lu1 lu2 bu fu hj hx1 hx2) hu lu1 lu2
          bu fu hwe hwu hu'R hspw
          (cross_to_back hperp ((mem_flip_off (hoff _ m1)).2 el1)
            ((mem_flip_off (hoff _ m2)).2 el2) hsp)
      · have hp := cell_prev_L (z := τ.c) (tf := τ.s) (i := i') (by omega)
        rw [hq] at hp
        rcases hperp with ht | ht
        · rw [show τ.s.opp = latB s by rw [ht, latA_opp_eq]] at hp
          rcases touch_side2_end_L hDc hk hpat (sig_of_pat hpτ) (i := i' - 1) (Nat.zero_le _)
              (by omega) hp with ⟨ht', _⟩ | ⟨_, hf, hl⟩
          · exact latA_ne_opp s (ht.symm.trans ht')
          · obtain ⟨hcL, hnT⟩ := beside_end2_pf hF hs0 hds hk hcell hcor hpat hsep hsame hneut
              ((outer2_body_L hDc hpat le_rfl).2 hk) hf hl (by rw [← hp]; exact (hR τ (List.mem_cons_self ..) (i' - 1) (by omega)).2)
            exact hnT (hTend _ (Or.inr rfl) hcL)
        · rw [show τ.s.opp = latA s by rw [ht, latB_opp_eq]] at hp
          rcases touch_side1_end_L hDc hk hpat (sig_of_pat hpτ) (i := i' - 1) (Nat.zero_le _)
              (by omega) hp with ⟨ht', _⟩ | ⟨_, hf, hl⟩
          · exact latB_ne_opp s (ht.symm.trans ht')
          · obtain ⟨hcL, hnT⟩ := beside_end1_pf hF hs0 hds hk hcell hcor hpat hsep hsame hneut
              ((outer1_body_L hDc hpat le_rfl).2 hk) hf hl (by rw [← hp]; exact (hR τ (List.mem_cons_self ..) (i' - 1) (by omega)).2)
            exact hnT (hTend _ (Or.inl rfl) hcL)
  -- **Through the cell beyond the end cell.**
  --
  have hR2 : ∀ i' < τ.n, cellJ τ.c τ.s i' = nb e s → False := by
    intro i' hi' hq
    rcases touch_beyond_L hDc hk hpat (sig_of_pat hpτ) (Nat.zero_le _) hi'
        (fun _ _ => Nat.zero_le _) (fun _ => Nat.zero_le _) hq with ⟨ht, hodd, hend⟩ |
        ⟨ht, _, hi1⟩ | ⟨hperp, h0⟩
    · have hendτ : endCell τ = nb e s := by
        unfold endCell; rw [← hq, show τ.n - 1 = i' by omega]
      obtain ⟨g1, g2, gb, _⟩ := strip_sig hpτ hi'
      rw [hq, ht] at g1 g2 gb
      rw [(frame_opp (nb e s) s).1] at g1
      rw [(frame_opp (nb e s) s).2.1] at g2
      rw [(frame_opp (nb e s) s).2.2.1] at gb
      have ul1 := g1.2 hodd
      have ul2 := g2.2 hodd
      have uf : front (nb e s) s ∉ F := fun h => by have := gb.1 h; omega
      have hcu' : IsCell V (nb e s) := by rw [← hq]; exact hcτ i' hi'
      cases L2 with
      | nil =>
        rcases (hch : TgEnd V F τ) with h | ⟨_, htw⟩
        · omega
        · rw [hendτ] at htw
          exact beyond_not_twists hF hs0 hds hle hk hcell hcor hpat hsep hsame hneut hcu' ul1 ul2 uf
            htw
      | cons w L3 =>
        have hlw := hch.2.1
        have hnt := hfar2 w (List.mem_cons_self ..)
        have hsplit := hlw.2.2.2.2.2.2.2.2.2.2.2
        rw [hendτ] at hsplit
        have hncw : NoChain τ w := by
          intro jw hjw y hy hyu
          obtain ⟨rfl, hyl⟩ := hnct.1 jw hjw y hy hyu
          rw [hendτ] at hyu hyl
          exact hnt (e1_chain_L hDc hk hcell hpat hlw (hnct.1) hendτ ht ul1 ul2 hy hyu hyl)
        have hpw : StripPat F w.c w.s w.n := (pat_flip_off hlw.2.2.1 hncw).1 hlw.2.2.2.1
        have hcorner : ∀ y ∈ F, ∀ jw < w.n, y ∈ cellE (cellJ w.c w.s jw) → ∀ r,
            (y.p = r ∨ y.q = r) → r ≠ front1 e s ∧ r ≠ front2 e s := by
          intro y hy jw hjw hyw r hr
          have touchy : y ∈ cellE e → False := fun h =>
            hnt ⟨jw, hjw, k + 1, by show k + 1 < k + 2; omega, y, hyw, h⟩
          have chainy : y ∈ cellE (nb e s) → False := fun h =>
            hncw jw hjw y hyw (by rw [hendτ]; exact h)
          constructor
          · rintro rfl
            have i2 := (ends_lat1 (nb e s) s).inc_iff (front1 e s) |>.2
              (Or.inl (back1_nb e s).symm)
            have hne2 : lat1 e s ≠ lat1 (nb e s) s := (ends_lat1 e s).ne_at
              (by have := ends_lat1 (nb e s) s; rwa [back1_nb] at this)
              (back1_ne_front1_nb e s)
            rcases two_at (hDc (k + 1) le_rfl _ (isCorner_front1 _ _)) el1 ul1
              ((ends_lat1 e s).inc_iff _ |>.2 (Or.inr rfl)) i2 hne2 hy hr with h | h
            · exact touchy (by rw [h, he_def, cellE_frame _ s]; simp)
            · exact chainy (by rw [h, cellE_frame (nb e s) s]; simp)
          · rintro rfl
            have i2 := (ends_lat2 (nb e s) s).inc_iff (front2 e s) |>.2
              (Or.inl (back2_nb e s).symm)
            have hne2 : lat2 e s ≠ lat2 (nb e s) s := (ends_lat2 e s).ne_at
              (by have := ends_lat2 (nb e s) s; rwa [back2_nb] at this)
              (back2_ne_front2_nb e s)
            rcases two_at (hDc (k + 1) le_rfl _ (isCorner_front2 _ _)) el2 ul2
              ((ends_lat2 e s).inc_iff _ |>.2 (Or.inr rfl)) i2 hne2 hy hr with h | h
            · exact touchy (by rw [h, he_def, cellE_frame _ s]; simp)
            · exact chainy (by rw [h, cellE_frame (nb e s) s]; simp)
        have hw1 : 1 ≤ w.n := hlw.2.2.1
        obtain ⟨⟨hb, hbp, hb0⟩, jf, hjf, xf, hxf, hxfp, hxfw⟩ := start_corner_edges hpw hw1
        have cb := hcorner _ hb 0 (by omega) hb0 _ hbp
        have cf := hcorner _ hxf jf hjf hxfw _ hxfp
        have hss := stacked_split_le hle hce hcu' el1 el2 eb ef ul1 ul2 uf cb.1 cb.2 cf.1 cf.2
        exact via_a w L3 rfl hpw (fun h => hsplit (hss.1 h))
    · exact hR1 (i' + 1) hi1 (by rw [← nb_cellJ, hq, ht, nb_nb_opp])
    · subst h0
      rw [hτc0] at hq
      by_cases hm : 2 ≤ τ.n
      · exact beyond_cross_pf hF hs0 hds hle hTR hk hcell hcor hpat hsep hT' hneut hTs hTend hpτ hτR
          hperp hq hm hnoA
      · have hm1 : τ.n = 1 := by omega
        obtain ⟨_, _, gb, gf⟩ := strip_sig hpτ (show 0 < τ.n by omega)
        rw [hτc0, hq] at gb gf
        have hbz := gb.2 rfl
        have hfz := gf.2 ⟨fun h => by omega, fun h => by omega⟩
        have hl12 : lat1 (nb e s) s ∈ F ∧ lat2 (nb e s) s ∈ F := by
          rcases hperp with ht | ht <;> rw [ht] at hbz hfz
          · rw [(frame_latA _ _).1] at hfz; rw [(frame_latA _ _).2.1] at hbz; exact ⟨hfz, hbz⟩
          · rw [(frame_latB _ _).1] at hfz; rw [(frame_latB _ _).2.1] at hbz; exact ⟨hbz, hfz⟩
        have hoffu : ∀ y ∈ cellE (nb e s), y ∉ cellE u' := fun y hy =>
          hnc 0 (by omega) y (by rw [hτc0, hq]; exact hy)
        have hwu : u' ≠ nb e s := fun h => hne 0 (by omega) (by rw [hτc0, hq, h])
        have hwe : u' ≠ e := fun h => hoffu (sideEdge e s) (side_mem_nb e s)
          (by rw [h]; exact side_mem_self e s)
        have hoffe : ∀ y ∈ cellE e, y ∉ cellE u' := by
          intro y hy hy'
          rcases alt_touch_pfD hF hs0 hTR hk hcell hcor hpat hsep hTs hu
            lu1 lu2 bu fu (show k + 1 < k + 2 by omega) hy' hy with h | h
          · exact hwe h
          · exact hwu h
        have m1 : lat1 (nb e s) s ∈ cellE (nb e s) := by rw [cellE_frame _ s]; simp
        have m2 : lat2 (nb e s) s ∈ cellE (nb e s) := by rw [cellE_frame _ s]; simp
        have m1e : lat1 e s ∈ cellE e := by rw [cellE_frame e s]; simp
        have m2e : lat2 e s ∈ cellE e := by rw [cellE_frame e s]; simp
        have hsp := hcu
        rw [hq] at hsp
        have h1 := cross_to_back hperp ((mem_flip_off (hoffu _ m1)).2 hl12.1)
          ((mem_flip_off (hoffu _ m2)).2 hl12.2) hsp
        rw [back1_nb, back2_nb] at h1
        exact split_core_pf hF hs0 hds hle hTR hk hcell hcor hpat hsep hT' hneut
          (fun hj _ hx1 hx2 => alt_touch_pfD hF hs0 hTR hk hcell hcor hpat hsep hTs
            hu lu1 lu2 bu fu hj hx1 hx2) hu lu1 lu2
          bu fu hwe hwu hu'R hspw
          (front_to_back ((mem_flip_off (hoffe _ m1e)).2 el1)
            ((mem_flip_off (hoffe _ m2e)).2 el2) h1)
  -- **Beside the start cell**: the suffix from there is a lighter path.
  --
  have hR3 : τ.s = s.opp → ∀ i0 < τ.n, i0 % 2 = 0 →
      (cellJ τ.c τ.s i0 = nb c (latA s) ∨ cellJ τ.c τ.s i0 = nb c (latB s)) → False := by
    intro ht i0 hi0 hev hq
    have hcR := hτR i0 hi0
    have hcL := hcτ i0 hi0
    have hdc1 : deg F (front1 c s) = 2 := hDc 0 (by omega) _ (by rw [cellJ_zero]; exact isCorner_front1 c s)
    have hdc2 : deg F (front2 c s) = 2 := hDc 0 (by omega) _ (by rw [cellJ_zero]; exact isCorner_front2 c s)
    have hsep' : ¬ Conn F (back1 (cellJ τ.c τ.s i0) τ.s) (front1 (cellJ τ.c τ.s i0) τ.s) := by
      obtain ⟨g1, _, _, _⟩ := strip_sig hpτ hi0
      rcases hq with hq | hq <;> rw [hq] at g1 hcR hcL ⊢ <;> rw [ht] at g1 ⊢ <;> apply conn_lat1_opp
      · have hfar : lat1 (nb c (latA s)) s ∉ F := by
          rw [(frame_opp _ s).1] at g1; exact fun h => by have := g1.1 h; omega
        -- The cell behind the square beside `c` is `τ`'s next cell (restricted), or the square is
        -- `τ`'s last cell, whose dark front (the square's back side) the start forbids.
        --
        have hBR : ¬ IsCorner t0 (nb (nb c (latA s)) s.opp) := by
          by_cases hl : i0 + 1 < τ.n
          · have := (hτR (i0 + 1) hl).2
            rwa [← nb_cellJ, hq, ht] at this
          · exfalso
            obtain ⟨_, _, _, gf⟩ := strip_sig hpτ hi0
            rw [hq, ht, (frame_opp _ s).2.2.2] at gf
            exact back_outer_light_loc hF.1 hpat (by omega) hsep hdc1
              (notT3W hs0 (hTs _ (Or.inl rfl)) (fun h => absurd h hcR.2))
              (gf.2 ⟨fun h => by omega, fun h => by omega⟩)
        exact start_side_sep_loc hF.1 hpat (by omega) (isCell_mono hc0 (sub_insST V s0 t0)) hsep hfar hdc1
          (deg_corner_restr hF hcL hcR (isCorner_front1 _ _))
          (deg_corner_restr hF hcL hcR (isCorner_front2 _ _))
          (notT3W hs0 (hTs _ (Or.inl rfl)) (fun h => absurd h hcR.2))
          (notT3W hs0 (hTd _ (Or.inl rfl)) (fun h => absurd h hBR))
      · rw [side2_back1, side2_front1]
        exact fun h => hsep ((((ends_back c s).conn hpat.1).trans h).trans
          (front_join_loc hF.1 hpat (by omega) (isCell_mono hc0 (sub_insST V s0 t0)) hdc1 hdc2
            (notT3W hs0 (ahead_notT3 hTR hcell hcor hk) (fun ht => absurd
              (show IsCorner t0 (cellJ c s 1) by rw [← nb_cellJ, cellJ_zero]; exact ht)
              (hcor 1 (by omega)).2))).symm)
    have hval := suf_valid hpτ hcτ hev hi0 hsep'
    have hsR : Restr s0 t0 (suf τ i0) := restr_suf hτR
    cases L2 with
    | nil =>
      refine nopath (suf τ i0) [] ⟨hval, tgEnd_suf hev hi0 hch, trivial, ?_⟩ ?_
      · intro x hx; rw [List.mem_singleton.1 hx]; exact hsR
      · simp [wt, suf] at hW1 ⊢; omega
    | cons w L3 =>
      obtain ⟨hτe, hlw, hrest⟩ := hch
      have hcr := suf_cr2 hlw hev (by omega)
      have hok' : ChainOK (suf τ i0) w := by
        have := hnct.1
        unfold ChainOK at this ⊢
        rw [suf_end (by omega)]; exact this
      refine nopath (suf τ i0) (w :: L3) ⟨hval, ⟨by show (τ.n - i0) % 2 = 0; omega, hcr, hrest⟩,
        ⟨hok', hnct.2⟩, ?_⟩ ?_
      · intro x hx
        rcases List.mem_cons.1 hx with rfl | hx
        · exact hsR
        · exact hR x (List.mem_cons_of_mem _ hx)
      · rw [wt_cons]; rw [wt_cons] at hW1; simp only [suf]; omega
  rcases touch_outcome_pfD hF hs0 hds hle hTR hk hcell hcor hpat hsep hT' hneut hTs hpτ hτR hcτ hi hj
      hx1 hx2 with ⟨i', hi', hq⟩ | ⟨i', hi', hq⟩ | ⟨ht, i0, hi0, hev, hq⟩
  · exact hR1 i' hi' hq
  · exact hR2 i' hi' hq
  · exact hR3 ht i0 hi0 hev hq

-- **The last touching strip, core** (ULHC `touch_core`, rule Tg): `τ` known from index `i0 ≤ 1`.
--
theorem touch_core_pf [hg : NearOK V t0] {σ τ : StripSpec} {i0 : ℕ} {L2 : List StripSpec} (hl : CR2 V F σ τ)
    (hzs : SigFrom F τ.c τ.s τ.n i0) (hi01 : i0 ≤ 1) (hz0 : i0 = 0 → NoChain σ τ)
    (hne_e : i0 = 1 → τ.c ≠ cellJ c s (k + 1)) (hσ : EndOK V F σ) (hσe : σ.n % 2 = 0) (hσR : Restr s0 t0 σ)
    (hch : CRChainTg V F τ L2) (hnct : CATail (τ :: L2)) (hR : ∀ x ∈ τ :: L2, Restr s0 t0 x)
    (hfar2 : ∀ w ∈ L2, ¬ Touches ⟨c, s, k + 2⟩ w)
    {W2 : ℕ} (hvia : ViaFreeTg V F s0 t0 ⟨c, s, k + 2⟩ W2)
    (hnoA : t0 ∉ V → ¬ PDang V t0 → ¬ ∃ σ' L', RPathTg V (flipCol F c s (k + 2)) s0 t0 σ' L') (hW1 : wt τ L2 < W)
    (hW2 : k + 2 + wt τ L2 < W2) {i j : ℕ} (hii : i0 ≤ i) (hi : i < τ.n) (hj : j < k + 2)
    {x : Edge} (hx1 : x ∈ cellE (cellJ τ.c τ.s i)) (hx2 : x ∈ cellE (cellJ c s j)) : False := by
  by_cases ht0 : t0 ∈ V ∨ PDang V t0
  swap
  · have h1 : t0 ∉ V := fun h => ht0 (Or.inl h)
    have h2 : ¬ PDang V t0 := fun h => ht0 (Or.inr h)
    exact ((hg.ok.resolve_left h1).resolve_left h2).2.2.1 hF hs0 hds hle hTR hk hcell hcor hpat
      hsep hT' hneut hTs hTend hTd hmin hl hzs hi01 hz0 hne_e hσ hσe hσR hch hnct hR hfar2 hvia hW1
      hW2 hii hi hj hx1 hx2 h2 (hnoA h1 h2) h1
  have nopath : ∀ σ' L', RPathTg V F s0 t0 σ' L' → wt σ' L' < W → False :=
    fun σ' L' h hlt => by have := hmin σ' L' h; omega
  have hDc := corners_deg2 hF hcell hcor
  have hTe : NotTypeIII V F (cellJ c s (k + 1)) :=
    restr_notT3 hTR (hcell (k + 1) le_rfl) (hcor (k + 1) le_rfl)
  have hsame := end_same_loc hTe hk hcell hpat
  have hca : ∀ j < k + 2, IsCell V (cellJ c s j) := fun j hj => hcell j (by omega)
  have hva : ValidStrip V F ⟨c, s, k + 2⟩ := ⟨by show 1 ≤ k + 2; omega, hpat, hca, hsep⟩
  have hcorR : Restr s0 t0 ⟨c, s, k + 2⟩ := fun j hj => hcor j (by simp only at hj; omega)
  have hτR : Restr s0 t0 τ := hR τ (List.mem_cons_self ..)
  have hl0 := hl
  set e := cellJ c s (k + 1) with he_def
  obtain ⟨h2σ, _, hτ1, hpτu, hcτ, hso, hne, hen, _, _, hcg, hcu⟩ := hl
  have hpτ0 : i0 = 0 → StripPat F τ.c τ.s τ.n := fun h => (pat_flip_off hτ1 (hz0 h)).1 hpτu
  obtain ⟨hu, lu1, lu2, bu, fu⟩ := hσ hσe
  set u' := endCell σ
  have hu'R : ¬ IsCorner s0 u' ∧ ¬ IsCorner t0 u' := hσR (σ.n - 1) (by omega)
  have hsameU : Conn F (back1 u' σ.s) (back2 u' σ.s) :=
    (frame_of_allConn (alt_corners_conn' (restr_notT3 hTR hu hu'R) (alt_of_lats lu1 lu2 bu fu))
      σ.s).1
  have hspw : ncomp V (flip F u') = ncomp V F + 1 := link_end_splits hl0 hu lu1 lu2 bu fu hsameU
  have hae : (⟨c, s, k + 2⟩ : StripSpec).n % 2 = 0 := by show (k + 2) % 2 = 0; omega
  have ha2 : 2 ≤ (⟨c, s, k + 2⟩ : StripSpec).n := by show 2 ≤ k + 2; omega
  -- Shortcut through `a` to the successor `w` of `τ`, once `w`'s start is split by `e`.
  --
  have via_a : ∀ w L3, L2 = w :: L3 → StripPat F w.c w.s w.n →
      ¬ Conn (flip F e) (back1 w.c w.s) (front1 w.c w.s) → False := by
    intro w L3 hL hpw hsplit
    subst hL
    obtain ⟨_, hlw, hrest⟩ := hch
    have hnt := hfar2 w (List.mem_cons_self ..)
    have hw1 : 1 ≤ w.n := hlw.2.2.1
    have hlink : CR2 V F ⟨c, s, k + 2⟩ w := link_a_pf hle hva hae ha2 hw1 hpw hlw.2.2.2.2.1 hnt
      hlw.2.2.2.2.2.2.2.2.2.2.1 hsplit
    refine hvia w L3 ⟨hva, ⟨hae, hlink, hrest⟩,
      ⟨chainOK_of_noChain (fun jw hjw y hy hye => hnt ⟨jw, hjw, k + 1, by show k + 1 < k + 2; omega,
        y, hy, hye⟩), hnct.2⟩, ?_⟩
      (fun x hx => hfar2 x (List.mem_cons_of_mem _ hx))
      (fun _ j hj y hy hy' => hnt ⟨w.n - 1, by omega, j, hj, y, by unfold endCell at hy; exact hy, hy'⟩) ?_
    · intro x hx
      rcases List.mem_cons.1 hx with rfl | hx
      · exact hcorR
      · exact hR x (List.mem_cons_of_mem _ hx)
    · rw [wt_cons]; rw [wt_cons] at hW2; show k + 2 + wt w L3 < W2; omega
  have hτc0 : cellJ τ.c τ.s 0 = τ.c := cellJ_zero τ.c τ.s
  obtain ⟨el1, el2, eb, ef⟩ := end_frame_pf hk hpat
  have hce : IsCell V e := hcell (k + 1) le_rfl
  have hc0 : IsCell V c := by have := hcell 0 (by omega); rwa [cellJ_zero] at this
  -- **Through the end cell.**
  --
  have hR1 : ∀ i', i0 ≤ i' → i' < τ.n → cellJ τ.c τ.s i' = e → False := by
    intro i' hi0' hi' hq
    obtain ⟨hend, hdir⟩ := touch_end_L hk hpat hzs hi0' hi' hq
    have hendτ : endCell τ = e := by
      unfold endCell; rw [← hq, show τ.n - 1 = i' by omega]
    rcases hdir with ⟨_, hodd⟩ | ⟨hperp, hev⟩
    · cases L2 with
      | nil =>
        rcases (hch : TgEnd V F τ) with h | ⟨_, htw⟩
        · omega
        · rw [hendτ] at htw
          exact end_not_twists hF hs0 hds hk hcell hcor hpat hsep hsame hneut htw
      | cons w L3 =>
        have hlw := hch.2.1
        have hnt := hfar2 w (List.mem_cons_self ..)
        have hpw : StripPat F w.c w.s w.n := by
          have h := hlw.2.2.2.1
          rw [hendτ] at h
          exact (pat_flip_off hlw.2.2.1 (fun jw hjw y hy hy' =>
            hnt ⟨jw, hjw, k + 1, by show k + 1 < k + 2; omega, y, hy, hy'⟩)).1 h
        have hsplit := hlw.2.2.2.2.2.2.2.2.2.2.2
        rw [hendτ] at hsplit
        exact via_a w L3 rfl hpw hsplit
    · by_cases hi0 : i' = 0
      · subst hi0
        have hz00 : i0 = 0 := by omega
        have hnc := hz0 hz00
        rw [hτc0] at hq
        have hwe : u' ≠ e := fun h => hne 0 (by omega) (by rw [hτc0, hq, h])
        have hwu : u' ≠ nb e s := fun h => hnc 0 (by omega) (sideEdge e s)
          (by rw [hτc0, hq]; exact side_mem_self e s)
          (by show sideEdge e s ∈ cellE u'; rw [h]; exact side_mem_nb e s)
        have hoff : ∀ y ∈ cellE e, y ∉ cellE u' := fun y hy =>
          hnc 0 (by omega) y (by rw [hτc0, hq]; exact hy)
        have m1 : lat1 e s ∈ cellE e := by rw [cellE_frame e s]; simp
        have m2 : lat2 e s ∈ cellE e := by rw [cellE_frame e s]; simp
        have hsp := hcu
        rw [hq] at hsp
        exact split_core_pf hF hs0 hds hle hTR hk hcell hcor hpat hsep hT' hneut
          (fun hj _ hx1 hx2 => alt_touch_pfD hF hs0 hTR hk hcell hcor hpat hsep hTs
            hu lu1 lu2 bu fu hj hx1 hx2) hu lu1 lu2
          bu fu hwe hwu hu'R hspw
          (cross_to_back hperp ((mem_flip_off (hoff _ m1)).2 el1)
            ((mem_flip_off (hoff _ m2)).2 el2) hsp)
      · have hp := cell_prev_L (z := τ.c) (tf := τ.s) (i := i') (by omega)
        rw [hq] at hp
        rcases hperp with ht | ht
        · rw [show τ.s.opp = latB s by rw [ht, latA_opp_eq]] at hp
          rcases touch_side2_end_L hDc hk hpat hzs (i := i' - 1) (by omega)
              (by omega) hp with ⟨ht', _⟩ | ⟨_, hf, hl⟩
          · exact latA_ne_opp s (ht.symm.trans ht')
          · obtain ⟨hcL, hnT⟩ := beside_end2_pf hF hs0 hds hk hcell hcor hpat hsep hsame hneut
              ((outer2_body_L hDc hpat le_rfl).2 hk) hf hl (by rw [← hp]; exact (hR τ (List.mem_cons_self ..) (i' - 1) (by omega)).2)
            exact hnT (hTend _ (Or.inr rfl) hcL)
        · rw [show τ.s.opp = latA s by rw [ht, latB_opp_eq]] at hp
          rcases touch_side1_end_L hDc hk hpat hzs (i := i' - 1) (by omega)
              (by omega) hp with ⟨ht', _⟩ | ⟨_, hf, hl⟩
          · exact latB_ne_opp s (ht.symm.trans ht')
          · obtain ⟨hcL, hnT⟩ := beside_end1_pf hF hs0 hds hk hcell hcor hpat hsep hsame hneut
              ((outer1_body_L hDc hpat le_rfl).2 hk) hf hl (by rw [← hp]; exact (hR τ (List.mem_cons_self ..) (i' - 1) (by omega)).2)
            exact hnT (hTend _ (Or.inl rfl) hcL)
  -- **Through the cell beyond the end cell.**
  --
  have hR2 : ∀ i', i0 ≤ i' → i' < τ.n → cellJ τ.c τ.s i' = nb e s → False := by
    intro i' hi0' hi' hq
    have hpvs : τ.s = s → 1 ≤ i' → i0 ≤ i' - 1 := by
      intro ht hi1
      by_contra hc
      have hi1' : i' = 1 := by omega
      have hz1 : i0 = 1 := by omega
      have hp := cell_prev_L (z := τ.c) (tf := τ.s) (i := i') (by omega)
      rw [hq, ht, nb_nb_opp, hi1', show 1 - 1 = 0 from rfl, cellJ_zero] at hp
      exact hne_e hz1 hp
    rcases touch_beyond_L hDc hk hpat hzs hi0' hi' hpvs (fun _ => by omega) hq with ⟨ht, hodd, hend⟩ |
        ⟨ht, _, hi1⟩ | ⟨hperp, h0⟩
    · have hendτ : endCell τ = nb e s := by
        unfold endCell; rw [← hq, show τ.n - 1 = i' by omega]
      obtain ⟨g1, g2, gb, _⟩ := hzs i' hi0' hi'
      rw [hq, ht] at g1 g2 gb
      rw [(frame_opp (nb e s) s).1] at g1
      rw [(frame_opp (nb e s) s).2.1] at g2
      rw [(frame_opp (nb e s) s).2.2.1] at gb
      have ul1 := g1.2 hodd
      have ul2 := g2.2 hodd
      have uf : front (nb e s) s ∉ F := fun h => by have := gb.1 h; omega
      have hcu' : IsCell V (nb e s) := by rw [← hq]; exact hcτ i' hi'
      cases L2 with
      | nil =>
        rcases (hch : TgEnd V F τ) with h | ⟨_, htw⟩
        · omega
        · rw [hendτ] at htw
          exact beyond_not_twists hF hs0 hds hle hk hcell hcor hpat hsep hsame hneut hcu' ul1 ul2 uf
            htw
      | cons w L3 =>
        have hlw := hch.2.1
        have hnt := hfar2 w (List.mem_cons_self ..)
        have hsplit := hlw.2.2.2.2.2.2.2.2.2.2.2
        rw [hendτ] at hsplit
        have hncw : NoChain τ w := by
          intro jw hjw y hy hyu
          obtain ⟨rfl, hyl⟩ := hnct.1 jw hjw y hy hyu
          rw [hendτ] at hyu hyl
          exact hnt (e1_chain_L hDc hk hcell hpat hlw (hnct.1) hendτ ht ul1 ul2 hy hyu hyl)
        have hpw : StripPat F w.c w.s w.n := (pat_flip_off hlw.2.2.1 hncw).1 hlw.2.2.2.1
        have hcorner : ∀ y ∈ F, ∀ jw < w.n, y ∈ cellE (cellJ w.c w.s jw) → ∀ r,
            (y.p = r ∨ y.q = r) → r ≠ front1 e s ∧ r ≠ front2 e s := by
          intro y hy jw hjw hyw r hr
          have touchy : y ∈ cellE e → False := fun h =>
            hnt ⟨jw, hjw, k + 1, by show k + 1 < k + 2; omega, y, hyw, h⟩
          have chainy : y ∈ cellE (nb e s) → False := fun h =>
            hncw jw hjw y hyw (by rw [hendτ]; exact h)
          constructor
          · rintro rfl
            have i2 := (ends_lat1 (nb e s) s).inc_iff (front1 e s) |>.2
              (Or.inl (back1_nb e s).symm)
            have hne2 : lat1 e s ≠ lat1 (nb e s) s := (ends_lat1 e s).ne_at
              (by have := ends_lat1 (nb e s) s; rwa [back1_nb] at this)
              (back1_ne_front1_nb e s)
            rcases two_at (hDc (k + 1) le_rfl _ (isCorner_front1 _ _)) el1 ul1
              ((ends_lat1 e s).inc_iff _ |>.2 (Or.inr rfl)) i2 hne2 hy hr with h | h
            · exact touchy (by rw [h, he_def, cellE_frame _ s]; simp)
            · exact chainy (by rw [h, cellE_frame (nb e s) s]; simp)
          · rintro rfl
            have i2 := (ends_lat2 (nb e s) s).inc_iff (front2 e s) |>.2
              (Or.inl (back2_nb e s).symm)
            have hne2 : lat2 e s ≠ lat2 (nb e s) s := (ends_lat2 e s).ne_at
              (by have := ends_lat2 (nb e s) s; rwa [back2_nb] at this)
              (back2_ne_front2_nb e s)
            rcases two_at (hDc (k + 1) le_rfl _ (isCorner_front2 _ _)) el2 ul2
              ((ends_lat2 e s).inc_iff _ |>.2 (Or.inr rfl)) i2 hne2 hy hr with h | h
            · exact touchy (by rw [h, he_def, cellE_frame _ s]; simp)
            · exact chainy (by rw [h, cellE_frame (nb e s) s]; simp)
        have hw1 : 1 ≤ w.n := hlw.2.2.1
        obtain ⟨⟨hb, hbp, hb0⟩, jf, hjf, xf, hxf, hxfp, hxfw⟩ := start_corner_edges hpw hw1
        have cb := hcorner _ hb 0 (by omega) hb0 _ hbp
        have cf := hcorner _ hxf jf hjf hxfw _ hxfp
        have hss := stacked_split_le hle hce hcu' el1 el2 eb ef ul1 ul2 uf cb.1 cb.2 cf.1 cf.2
        exact via_a w L3 rfl hpw (fun h => hsplit (hss.1 h))
    · exact hR1 (i' + 1) (by omega) hi1 (by rw [← nb_cellJ, hq, ht, nb_nb_opp])
    · subst h0
      have hz00 : i0 = 0 := by omega
      have hnc := hz0 hz00
      have hpτ := hpτ0 hz00
      rw [hτc0] at hq
      by_cases hm : 2 ≤ τ.n
      · exact beyond_cross_pf hF hs0 hds hle hTR hk hcell hcor hpat hsep hT' hneut hTs hTend hpτ hτR
          hperp hq hm hnoA
      · have hm1 : τ.n = 1 := by omega
        obtain ⟨_, _, gb, gf⟩ := strip_sig hpτ (show 0 < τ.n by omega)
        rw [hτc0, hq] at gb gf
        have hbz := gb.2 rfl
        have hfz := gf.2 ⟨fun h => by omega, fun h => by omega⟩
        have hl12 : lat1 (nb e s) s ∈ F ∧ lat2 (nb e s) s ∈ F := by
          rcases hperp with ht | ht <;> rw [ht] at hbz hfz
          · rw [(frame_latA _ _).1] at hfz; rw [(frame_latA _ _).2.1] at hbz; exact ⟨hfz, hbz⟩
          · rw [(frame_latB _ _).1] at hfz; rw [(frame_latB _ _).2.1] at hbz; exact ⟨hbz, hfz⟩
        have hoffu : ∀ y ∈ cellE (nb e s), y ∉ cellE u' := fun y hy =>
          hnc 0 (by omega) y (by rw [hτc0, hq]; exact hy)
        have hwu : u' ≠ nb e s := fun h => hne 0 (by omega) (by rw [hτc0, hq, h])
        have hwe : u' ≠ e := fun h => hoffu (sideEdge e s) (side_mem_nb e s)
          (by rw [h]; exact side_mem_self e s)
        have hoffe : ∀ y ∈ cellE e, y ∉ cellE u' := by
          intro y hy hy'
          rcases alt_touch_pfD hF hs0 hTR hk hcell hcor hpat hsep hTs hu
            lu1 lu2 bu fu (show k + 1 < k + 2 by omega) hy' hy with h | h
          · exact hwe h
          · exact hwu h
        have m1 : lat1 (nb e s) s ∈ cellE (nb e s) := by rw [cellE_frame _ s]; simp
        have m2 : lat2 (nb e s) s ∈ cellE (nb e s) := by rw [cellE_frame _ s]; simp
        have m1e : lat1 e s ∈ cellE e := by rw [cellE_frame e s]; simp
        have m2e : lat2 e s ∈ cellE e := by rw [cellE_frame e s]; simp
        have hsp := hcu
        rw [hq] at hsp
        have h1 := cross_to_back hperp ((mem_flip_off (hoffu _ m1)).2 hl12.1)
          ((mem_flip_off (hoffu _ m2)).2 hl12.2) hsp
        rw [back1_nb, back2_nb] at h1
        exact split_core_pf hF hs0 hds hle hTR hk hcell hcor hpat hsep hT' hneut
          (fun hj _ hx1 hx2 => alt_touch_pfD hF hs0 hTR hk hcell hcor hpat hsep hTs
            hu lu1 lu2 bu fu hj hx1 hx2) hu lu1 lu2
          bu fu hwe hwu hu'R hspw
          (front_to_back ((mem_flip_off (hoffe _ m1e)).2 el1)
            ((mem_flip_off (hoffe _ m2e)).2 el2) h1)
  -- **Beside the start cell**: the suffix from there is a lighter path.
  --
  have hR3 : τ.s = s.opp → ∀ ie, i0 ≤ ie → ie < τ.n → ie % 2 = 0 →
      (cellJ τ.c τ.s ie = nb c (latA s) ∨ cellJ τ.c τ.s ie = nb c (latB s)) → False := by
    intro ht ie hie hi0 hev hq
    have hcR := hτR ie hi0
    have hcL := hcτ ie hi0
    have hdc1 : deg F (front1 c s) = 2 := hDc 0 (by omega) _ (by rw [cellJ_zero]; exact isCorner_front1 c s)
    have hdc2 : deg F (front2 c s) = 2 := hDc 0 (by omega) _ (by rw [cellJ_zero]; exact isCorner_front2 c s)
    have hsep' : ¬ Conn F (back1 (cellJ τ.c τ.s ie) τ.s) (front1 (cellJ τ.c τ.s ie) τ.s) := by
      obtain ⟨g1, _, _, _⟩ := hzs ie hie hi0
      rcases hq with hq | hq <;> rw [hq] at g1 hcR hcL ⊢ <;> rw [ht] at g1 ⊢ <;> apply conn_lat1_opp
      · have hfar : lat1 (nb c (latA s)) s ∉ F := by
          rw [(frame_opp _ s).1] at g1; exact fun h => by have := g1.1 h; omega
        -- The cell behind the square beside `c` is `τ`'s next cell (restricted), or the square is
        -- `τ`'s last cell, whose dark front (the square's back side) the start forbids.
        --
        have hBR : ¬ IsCorner t0 (nb (nb c (latA s)) s.opp) := by
          by_cases hl : ie + 1 < τ.n
          · have := (hτR (ie + 1) hl).2
            rwa [← nb_cellJ, hq, ht] at this
          · exfalso
            obtain ⟨_, _, _, gf⟩ := hzs ie hie hi0
            rw [hq, ht, (frame_opp _ s).2.2.2] at gf
            exact back_outer_light_loc hF.1 hpat (by omega) hsep hdc1
              (notT3W hs0 (hTs _ (Or.inl rfl)) (fun h => absurd h hcR.2))
              (gf.2 ⟨fun h => by omega, fun h => by omega⟩)
        exact start_side_sep_loc hF.1 hpat (by omega) (isCell_mono hc0 (sub_insST V s0 t0)) hsep hfar hdc1
          (deg_corner_restr hF hcL hcR (isCorner_front1 _ _))
          (deg_corner_restr hF hcL hcR (isCorner_front2 _ _))
          (notT3W hs0 (hTs _ (Or.inl rfl)) (fun h => absurd h hcR.2))
          (notT3W hs0 (hTd _ (Or.inl rfl)) (fun h => absurd h hBR))
      · rw [side2_back1, side2_front1]
        exact fun h => hsep ((((ends_back c s).conn hpat.1).trans h).trans
          (front_join_loc hF.1 hpat (by omega) (isCell_mono hc0 (sub_insST V s0 t0)) hdc1 hdc2
            (notT3W hs0 (ahead_notT3 hTR hcell hcor hk) (fun ht => absurd
              (show IsCorner t0 (cellJ c s 1) by rw [← nb_cellJ, cellJ_zero]; exact ht)
              (hcor 1 (by omega)).2))).symm)
    have hval := suf_validW hzs hcτ hie hev hi0 hsep'
    have hsR : Restr s0 t0 (suf τ ie) := restr_suf hτR
    cases L2 with
    | nil =>
      refine nopath (suf τ ie) [] ⟨hval, tgEnd_suf hev hi0 hch, trivial, ?_⟩ ?_
      · intro x hx; rw [List.mem_singleton.1 hx]; exact hsR
      · simp [wt, suf] at hW1 ⊢; omega
    | cons w L3 =>
      obtain ⟨hτe, hlw, hrest⟩ := hch
      have hcr := suf_cr2 hlw hev (by omega)
      have hok' : ChainOK (suf τ ie) w := by
        have := hnct.1
        unfold ChainOK at this ⊢
        rw [suf_end (by omega)]; exact this
      refine nopath (suf τ ie) (w :: L3) ⟨hval, ⟨by show (τ.n - ie) % 2 = 0; omega, hcr, hrest⟩,
        ⟨hok', hnct.2⟩, ?_⟩ ?_
      · intro x hx
        rcases List.mem_cons.1 hx with rfl | hx
        · exact hsR
        · exact hR x (List.mem_cons_of_mem _ hx)
      · rw [wt_cons]; rw [wt_cons] at hW1; simp only [suf]; omega
  rcases touch_outcomeW_pfD hF hs0 hds hTR hk hcell hcor hpat hsep hT' hneut hTs hzs hτR hcτ
      (fun ht0V hnp _ _ _ => by rcases ht0 with h | h; exacts [absurd h ht0V, absurd h hnp])
      hii hi hj
      hx1 hx2 with ⟨i', hle', hi', hq⟩ | ⟨i', hle', hi', hq⟩ | ⟨ht, ie, hle', hi0, hev, hq⟩
  · exact hR1 i' (by omega) hi' hq
  · exact hR2 i' (by omega) hi' hq
  · exact hR3 ht ie (by omega) hi0 hev hq


-- **The last touching strip, chain case** (ULHC `touch_contra_chain`, rule Tg).
--
theorem touch_contra_chain_pf [hg : NearOK V t0] {σ τ : StripSpec} {L2 : List StripSpec} (hl : CR2 V F σ τ)
    (hok : ChainOK σ τ) (hch' : ¬ NoChain σ τ) (hσ : EndOK V F σ) (hσe : σ.n % 2 = 0)
    (hσR : Restr s0 t0 σ)
    (hch : CRChainTg V F τ L2) (hnct : CATail (τ :: L2)) (hR : ∀ x ∈ τ :: L2, Restr s0 t0 x)
    (hfar2 : ∀ w ∈ L2, ¬ Touches ⟨c, s, k + 2⟩ w)
    {W2 : ℕ} (hvia : ViaFreeTg V F s0 t0 ⟨c, s, k + 2⟩ W2)
    (hnoA : t0 ∉ V → ¬ PDang V t0 → ¬ ∃ σ' L', RPathTg V (flipCol F c s (k + 2)) s0 t0 σ' L') (hW1 : wt τ L2 < W)
    (hW2 : k + 2 + wt τ L2 < W2) :
    ¬ Touches ⟨c, s, k + 2⟩ τ := by
  by_cases ht0 : t0 ∈ V ∨ PDang V t0
  swap
  · have h1 : t0 ∉ V := fun h => ht0 (Or.inl h)
    have h2 : ¬ PDang V t0 := fun h => ht0 (Or.inr h)
    exact ((hg.ok.resolve_left h1).resolve_left h2).2.2.2 hF hs0 hds hle hTR hk hcell hcor hpat
      hsep hT' hneut hTs hTend hTd hmin hl hok hch' hσ hσe hσR hch hnct hR hfar2 hvia hW1 hW2 h2
      (hnoA h1 h2) h1
  rintro ⟨i, hi, j, hj, x, hx1, hx2⟩
  have hzs := chain_sig hl hok
  have hj' : j < k + 2 := hj
  change x ∈ cellE (cellJ c s j) at hx2
  have core : ∀ {i j : ℕ} {x : Edge}, τ.c ≠ cellJ c s (k + 1) → 1 ≤ i → i < τ.n → j < k + 2 →
      x ∈ cellE (cellJ τ.c τ.s i) → x ∈ cellE (cellJ c s j) → False :=
    fun hne hii hi hj hx1 hx2 => touch_core_pf hF hs0 hds hle hTR hk hcell hcor hpat hsep hT' hneut hTs hTend hTd hmin hl hzs le_rfl
      (fun h => absurd h (by omega)) (fun _ => hne) hσ hσe hσR hch hnct hR hfar2 hvia hnoA hW1 hW2 hii hi
      hj hx1 hx2
  obtain ⟨hu, lu1, lu2, bu, fu⟩ := hσ hσe
  obtain ⟨jy, hjy, y, hy, hyu⟩ : ∃ jy < τ.n, ∃ y ∈ cellE (cellJ τ.c τ.s jy),
      y ∈ cellE (endCell σ) := by
    by_contra hn; push Not at hn; exact hch' hn
  obtain ⟨rfl, -⟩ := hok jy hjy y hy hyu
  rw [cellJ_zero] at hy
  obtain ⟨hyG, hylat, hbG, hfr, hyl⟩ := chain_start hl hok ⟨lu1, lu2⟩ hy hyu
  have hdu : τ.c ≠ endCell σ := by
    have := hl.2.2.2.2.2.2.1 0 hl.2.2.1; rwa [cellJ_zero] at this
  have hτ1 : 1 ≤ τ.n := hl.2.2.1
  have hτR : Restr s0 t0 τ := hR τ (List.mem_cons_self ..)
  have hdRt : ¬ IsCorner t0 τ.c := by have := (hτR 0 hτ1).2; rwa [cellJ_zero] at this
  have huRt : ¬ IsCorner t0 (endCell σ) := by
    have := (hσR (σ.n - 1) (by have := hl.1; omega)).2; unfold endCell; exact this
  have hDc := corners_deg2 hF hcell hcor
  have hTr := ahead_notT3 hTR hcell hcor hk
  have hcellW : ∀ j ≤ k + 1, IsCell (insert s0 (insert t0 V)) (cellJ c s j) :=
    fun j hj => isCell_mono (hcell j hj) (sub_insST V s0 t0)
  have hTrW := notT3W (t0 := t0) hs0 hTr (fun ht => absurd
    (show IsCorner t0 (cellJ c s 1) by rw [← nb_cellJ, cellJ_zero]; exact ht) (hcor 1 (by omega)).2)
  have hca : ∀ j < k + 2, IsCell V (cellJ c s j) := fun j hj => hcell j (by omega)
  have hva : ValidStrip V F ⟨c, s, k + 2⟩ := ⟨by show 1 ≤ k + 2; omega, hpat, hca, hsep⟩
  have hcorR : Restr s0 t0 ⟨c, s, k + 2⟩ := fun j hj => hcor j (by simp only at hj; omega)
  have hae : (⟨c, s, k + 2⟩ : StripSpec).n % 2 = 0 := by show (k + 2) % 2 = 0; omega
  -- A link from `a` straight to `τ`, when `τ` is a chain strip of `a`'s end cell.
  --
  have via_end : endCell σ = cellJ c s (k + 1) → CR2 V F ⟨c, s, k + 2⟩ τ →
      (L2 ≠ [] → ∀ j < k + 2, ∀ y ∈ cellE (endCell τ), y ∉ cellE (cellJ c s j)) → False := by
    intro hue hlink hfe
    have hokA : ChainOK ⟨c, s, k + 2⟩ τ := by
      intro jj hjj z hz hze
      obtain ⟨hj0, hzl⟩ := hok jj hjj z hz (by rw [hue]; exact hze)
      refine ⟨hj0, ?_⟩
      have hzG : z ∈ F := by rcases hzl with rfl | rfl; exacts [lu1, lu2]
      obtain ⟨_, _, eb, ef⟩ := end_frame_pf hk hpat
      change z ∈ cellE (cellJ c s (k + 1)) at hze
      rw [cellE_frame _ s] at hze
      simp only [Finset.mem_insert, Finset.mem_singleton] at hze
      rcases hze with rfl | rfl | rfl | rfl
      · exact absurd hzG eb
      · exact absurd hzG ef
      · exact Or.inl rfl
      · exact Or.inr rfl
    refine hvia τ L2 ⟨hva, ⟨hae, hlink, hch⟩, ⟨hokA, hnct⟩, ?_⟩ hfar2 hfe ?_
    · intro x hx
      rcases List.mem_cons.1 hx with rfl | hx
      · exact hcorR
      · exact hR x hx
    · rw [wt_cons]; show k + 2 + wt τ L2 < W2; omega
  have hce : τ.c ≠ cellJ c s (k + 1) := fun h =>
    start_not_body_pf hk hpat hbG hyG hylat hyl lu1 lu2 bu fu hyu hdu (le_refl (k + 1)) h
  rcases Nat.eq_zero_or_pos i with rfl | hi1
  swap
  · exact core hce hi1 hi hj' hx1 hx2
  rw [cellJ_zero] at hx1
  rcases touch_cases s hx1 hx2 with h | h | h | h | h
  · exact start_not_body_pf hk hpat hbG hyG hylat hyl lu1 lu2 bu fu hyu hdu (by omega) h
  · by_cases hjk : j ≤ k
    · exact start_not_body_pf hk hpat hbG hyG hylat hyl lu1 lu2 bu fu hyu hdu
        (show j + 1 ≤ k + 1 by omega) (h.trans (nb_cellJ c s j))
    obtain rfl : j = k + 1 := by omega
    rcases start_beyond_pf hF hs0 hds hle hTR hk hcell hcor hpat hsep hT' hneut hTs hTend hbG hyG hylat hyl hyu hdu hfr h
        (fun hm1 => by
          have := (hR τ (List.mem_cons_self ..) 1 (by omega)).2
          rwa [show cellJ τ.c τ.s 1 = nb τ.c τ.s by rw [← nb_cellJ, cellJ_zero]] at this) hnoA with
      ⟨ht, hfn⟩ | ⟨hm1, hud, hd1, hd2, hdf⟩
    · -- `τ` runs into the end cell.
      --
      have hn2 : 2 ≤ τ.n := by
        by_contra hn; exact hfn (hfr.2 (by omega))
      have h1 : cellJ τ.c τ.s 1 = cellJ c s (k + 1) := by
        rw [← nb_cellJ, cellJ_zero, ht, h, nb_nb_opp]
      have hm : back (cellJ c s (k + 1)) s ∈ cellE (cellJ c s (k + 1)) := by
        rw [cellE_frame _ s]; simp
      exact core hce le_rfl hn2 (show k + 1 < k + 2 by omega) (by rw [h1]; exact hm) hm
    · -- `τ` is a single cell with three dark sides: a shortcut to `u`.
      --
      have hd' : τ.c = cellJ c s (k + 2) := h.trans (nb_cellJ c s (k + 1))
      have hu' : endCell σ = cellJ c s (k + 3) := hud.trans (by rw [hd', nb_cellJ])
      have hcd : IsCell V (cellJ c s (k + 2)) := by
        rw [← hd']; have := hl.2.2.2.2.1 0 hτ1; rwa [cellJ_zero] at this
      have huR : ¬ IsCorner s0 (cellJ c s (k + 3)) ∧ ¬ IsCorner t0 (cellJ c s (k + 3)) := by
        rw [← hu']; exact hσR (σ.n - 1) (by have := hl.1; omega)
      rw [hd'] at hd1 hd2 hdf
      rw [hu'] at hu lu1 lu2 bu fu
      have hlink := single3_link_pf hle hk hcell hpat hd1 hd2 hdf hu lu1 lu2 bu fu hcd
        (restr_notT3 hTR hu huR)
      have hL2 : L2 = [] := by
        cases L2 with
        | nil => rfl
        | cons w L3 => have := hch.1; omega
      subst hL2
      have hokA : ChainOK ⟨c, s, k + 2⟩ ⟨cellJ c s (k + 3), s, 1⟩ := by
        intro jj hjj z hz hze
        exfalso
        obtain rfl : jj = 0 := by simp only at hjj; omega
        rw [cellJ_zero] at hz
        exact along_not_mem c s (show k + 1 + 2 ≤ k + 3 by omega) hz hze
      refine hvia _ [] ⟨hva, ⟨hae, hlink, Or.inl rfl⟩, ⟨hokA, trivial⟩, ?_⟩ (by simp)
        (fun h => absurd rfl h) ?_
      · intro x hx
        rcases List.mem_cons.1 hx with rfl | hx
        · exact hcorR
        · rw [List.mem_singleton.1 hx]
          intro jj hjj
          obtain rfl : jj = 0 := by simp only at hjj; omega
          rw [cellJ_zero]; exact huR
      · simp only [wt, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at hW2 ⊢
        omega
  · rcases j with _ | j
    · rw [cellJ_zero] at h
      by_cases hPh : (IsCorner t0 (nb c (latA s)) ∧ ¬ NotTypeIII V F (nb c (latA s))) ∨
          (IsCorner t0 (nb c (latB s)) ∧ ¬ NotTypeIII V F (nb c (latB s)))
      · -- With `t0 ∈ V` a square beside `c` is a cell (`hTs`) or not Type III.
        --
        exfalso
        rcases ht0 with ht0 | hpd
        swap
        · rcases hPh with ⟨hc, hn⟩ | ⟨hc, hn⟩
          · exact hn (notT3_pdang hF hs0 hpd hc)
          · exact hn (notT3_pdang hF hs0 hpd hc)
        have hIn : Inside V F := by
          have h1 := hF.1
          unfold InsideST at h1
          rwa [Finset.insert_eq_of_mem (Finset.mem_insert_of_mem hs0),
            Finset.insert_eq_of_mem ht0] at h1
        have key : ∀ tf, (tf = latA s ∨ tf = latB s) → NotTypeIII V F (nb c tf) := fun tf htf => by
          by_cases hc : IsCell V (nb c tf)
          · exact hTs tf htf hc
          · exact notTypeIII_of_not_cell hIn hc
        rcases hPh with ⟨_, hn⟩ | ⟨_, hn⟩
        · exact hn (key _ (Or.inl rfl))
        · exact hn (key _ (Or.inr rfl))
      · exact start_not_behind_pf hF hs0 hTR hk hcell hcor hpat hsep hTs
          (by
            rintro tf (rfl | rfl) hc
            · by_contra hn; exact hPh (Or.inl ⟨hc, hn⟩)
            · by_contra hn; exact hPh (Or.inr ⟨hc, hn⟩))
          hbG hyG hylat hyl lu1 lu2 bu fu hyu hdu h
    · exact start_not_body_pf hk hpat hbG hyG hylat hyl lu1 lu2 bu fu hyu hdu
        (show j ≤ k + 1 by omega) (by rw [h, ← nb_cellJ, nb_nb_opp])
  · by_cases hjk : j ≤ k
    · obtain ⟨ht, hje, hyf⟩ := start_beside1_pf hF hs0 hTR hk hcell hcor hpat hsep hT' hneut hTs hTend hbG hyG hylat hyl lu1 lu2 bu fu hyu hdu hjk h hdRt huRt
      have hfn : front τ.c τ.s ∉ F := by
        rw [ht, (frame_opp _ s).2.2.2, h]
        intro hb'
        have := (side1_facts_R hF.1 hDc hcell hpat hsep hjk (fun h0 => notT3W (t0 := t0) hs0
          (hTs _ (Or.inl rfl)) (fun ht => absurd (by rw [h, h0, cellJ_zero]; exact ht) hdRt))).2.1.1 hb'; omega
      have hn2 : 2 ≤ τ.n := by
        by_contra hn; exact hfn (hfr.2 (by omega))
      rcases j with _ | j
      · rw [cellJ_zero] at h
        exact start_L0_pf hF hs0 hTR hk hcell hcor hpat hsep hTs (by rw [← h, ← ht]; exact hzs) hn2
          (by rw [← h, ← ht]; exact hl.2.2.2.2.1 1 hn2) (by rw [← h, ← ht]; exact hτR 1 hn2)
          (by rw [← h, ← hyf]; exact hyG) (by rw [← h]; exact hdRt)
      · have h1 : cellJ τ.c τ.s 1 = nb (cellJ c s j) (latA s) := by
          rw [← nb_cellJ, cellJ_zero, ht, h, side1_down]
        exact core hce le_rfl hn2 (show j < k + 2 by omega) (by rw [h1]; exact side_mem_nb _ _)
          (side_mem_self _ _)
    · obtain rfl : j = k + 1 := by omega
      obtain ⟨hue, ht⟩ := start_beside_end1_pf hF hs0 hTR hk hcell hcor hpat hsep hT' hneut hTs hTend hbG hyG hylat hyl lu1 lu2 bu fu hyu hdu h huRt
      have hfe : L2 ≠ [] → ∀ j < k + 2, ∀ y ∈ cellE (endCell τ), y ∉ cellE (cellJ c s j) := by
        intro hL2 j hj y hy
        have hev : τ.n % 2 = 0 := by
          cases L2 with
          | nil => exact absurd rfl hL2
          | cons _ _ => exact hch.1
        have hτs : τ.s = s := ht.resolve_right (fun h' => by have := hfr.1 h'.2; omega)
        unfold endCell at hy
        rw [hτs, h] at hy
        exact beside_end_farA c s k (show 2 ≤ τ.n by omega) hy j (by omega)
      exact via_end hue (direct_link1 hk hl hue h (ht.imp_right fun h' => ⟨h'.1, hfr.1 h'.2⟩)) hfe
  · by_cases hjk : j ≤ k
    · obtain ⟨ht, hje, hyf⟩ := start_beside2_pf hF hs0 hTR hk hcell hcor hpat hsep hT' hneut hTs hTend hbG hyG hylat hyl lu1 lu2 bu fu hyu hdu hjk h hdRt huRt
      have hfn : front τ.c τ.s ∉ F := by
        rw [ht, (frame_opp _ s).2.2.2, h]
        intro hb'
        have := (side2_facts_R hF.1 hDc hcell hpat hsep hTrW hjk (fun h0 => notT3W (t0 := t0) hs0
          (hTs _ (Or.inr rfl)) (fun ht => absurd (by rw [h, h0, cellJ_zero]; exact ht) hdRt))).2.1.1 hb'; omega
      have hn2 : 2 ≤ τ.n := by
        by_contra hn; exact hfn (hfr.2 (by omega))
      rcases j with _ | j
      · rw [cellJ_zero] at h
        exact start_R0_pf hF hs0 hTR hk hcell hcor hpat hsep hTs (by rw [← h, ← ht]; exact hzs) hn2
          (by rw [← h, ← ht]; exact hl.2.2.2.2.1 1 hn2) (by rw [← h, ← ht]; exact hτR 1 hn2)
          (by rw [← h, ← hyf]; exact hyG) (by rw [← h]; exact hdRt)
      · have h1 : cellJ τ.c τ.s 1 = nb (cellJ c s j) (latB s) := by
          rw [← nb_cellJ, cellJ_zero, ht, h, side2_down]
        exact core hce le_rfl hn2 (show j < k + 2 by omega) (by rw [h1]; exact side_mem_nb _ _)
          (side_mem_self _ _)
    · obtain rfl : j = k + 1 := by omega
      obtain ⟨hue, ht⟩ := start_beside_end2_pf hF hs0 hTR hk hcell hcor hpat hsep hT' hneut hTs hTend hbG hyG hylat hyl lu1 lu2 bu fu hyu hdu h huRt
      have hfe : L2 ≠ [] → ∀ j < k + 2, ∀ y ∈ cellE (endCell τ), y ∉ cellE (cellJ c s j) := by
        intro hL2 j hj y hy
        have hev : τ.n % 2 = 0 := by
          cases L2 with
          | nil => exact absurd rfl hL2
          | cons _ _ => exact hch.1
        have hτs : τ.s = s := ht.resolve_right (fun h' => by have := hfr.1 h'.2; omega)
        unfold endCell at hy
        rw [hτs, h] at hy
        exact beside_end_farB c s k (show 2 ≤ τ.n by omega) hy j (by omega)
      exact via_end hue (direct_link2 hk hl hue h (ht.imp_right fun h' => ⟨h'.1, hfr.1 h'.2⟩)) hfe

-- **No later strip touches `a`** (ULHC `notouch_CA`, rule Tg).
--
theorem notouch_pf [hg : NearOK V t0] {W2 : ℕ} (hvia : ViaFreeTg V F s0 t0 ⟨c, s, k + 2⟩ W2)
    (hnoA : t0 ∉ V → ¬ PDang V t0 → ¬ ∃ σ' L', RPathTg V (flipCol F c s (k + 2)) s0 t0 σ' L') :
    ∀ (L : List StripSpec) (σ : StripSpec), CRChainTg V F σ L → CATail (σ :: L) → EndOK V F σ →
    (∀ x ∈ σ :: L, Restr s0 t0 x) → wt σ L ≤ W → k + 2 + wt σ L ≤ W2 →
    ∀ τ ∈ L, ¬ Touches ⟨c, s, k + 2⟩ τ := by
  intro L
  induction L with
  | nil => intro _ _ _ _ _ _ _ τ h; simp at h
  | cons τ L' ih =>
    intro σ hch hnct hσ hR hW hW2
    obtain ⟨hσe, hl, hrest⟩ := hch
    have hR' : ∀ x ∈ τ :: L', Restr s0 t0 x := fun x hx => hR x (List.mem_cons_of_mem _ hx)
    have hfar2 := ih τ hrest hnct.2 (endOK_of_link hl) hR' (by rw [wt_cons] at hW; omega)
      (by rw [wt_cons] at hW2; omega)
    have hW1' : wt τ L' < W := by rw [wt_cons] at hW; have := hl.1; omega
    have hW2' : k + 2 + wt τ L' < W2 := by rw [wt_cons] at hW2; have := hl.1; omega
    have hσR := hR σ (List.mem_cons_self ..)
    intro w hw
    rcases List.mem_cons.1 hw with rfl | hw'
    · by_cases hnc : NoChain σ w
      · exact touch_contra_plain_pf hF hs0 hds hle hTR hk hcell hcor hpat hsep hT' hneut hTs hTend hTd hmin hl hnc hσ hσe hσR hrest hnct.2 hR' hfar2 hvia hnoA
          hW1' hW2'
      · exact touch_contra_chain_pf hF hs0 hds hle hTR hk hcell hcor hpat hsep hT' hneut hTs hTend hTd hmin hl hnct.1 hnc hσ hσe hσR hrest hnct.2 hR' hfar2
          hvia hnoA hW1' hW2'
    · exact hfar2 w hw'

-- **Later links are far from `a`** (ULHC `farchain_CA`, rule Tg).
--
omit hF hs0 hds hTR hT' hneut hTs hTend hTd hmin in
theorem farchain_pf {W2 : ℕ} (hvia : ViaFreeTg V F s0 t0 ⟨c, s, k + 2⟩ W2) :
    ∀ (L : List StripSpec) (σ : StripSpec), CRChainTg V F σ L → CATail (σ :: L) → EndOK V F σ →
    (∀ x ∈ σ :: L, Restr s0 t0 x) →
    (∀ j < k + 2, ∀ y ∈ cellE (endCell σ), y ∉ cellE (cellJ c s j)) →
    (∀ τ ∈ L, ¬ Touches ⟨c, s, k + 2⟩ τ) → k + 2 + wt σ L ≤ W2 →
    FarChainCA F ⟨c, s, k + 2⟩ σ L := by
  have hca : ∀ j < k + 2, IsCell V (cellJ c s j) := fun j hj => hcell j (by omega)
  have hva : ValidStrip V F ⟨c, s, k + 2⟩ := ⟨by show 1 ≤ k + 2; omega, hpat, hca, hsep⟩
  have hcorR : Restr s0 t0 ⟨c, s, k + 2⟩ := fun j hj => hcor j (by simp only at hj; omega)
  have hae : (⟨c, s, k + 2⟩ : StripSpec).n % 2 = 0 := by show (k + 2) % 2 = 0; omega
  have ha2 : 2 ≤ (⟨c, s, k + 2⟩ : StripSpec).n := by show 2 ≤ k + 2; omega
  intro L
  induction L with
  | nil => intro _ _ _ _ _ _ _ _; trivial
  | cons τ L' ih =>
    intro σ hch hnct hσ hR hσfar hnt hW
    obtain ⟨hσe, hl, hrest⟩ := hch
    have hR' : ∀ x ∈ τ :: L', Restr s0 t0 x := fun x hx => hR x (List.mem_cons_of_mem _ hx)
    have hnτ := hnt τ (List.mem_cons_self ..)
    have hτ1 : 1 ≤ τ.n := hl.2.2.1
    obtain ⟨hu, lu1, lu2, _, _⟩ := hσ hσe
    have hmidτ : ∀ p, (∃ j < τ.n, ∃ x ∈ F, (x.p = p ∨ x.q = p) ∧ x ∈ cellE (cellJ τ.c τ.s j)) →
        ¬ IsMid c s (k + 2 - 2) p := by
      rintro p ⟨j, hj, x, hx, hxp, hxw⟩ hm
      rw [show k + 2 - 2 = k by omega] at hm
      obtain ⟨i, hi, hxi⟩ := mid_touch_L hle hpat hm hx hxp
      exact hnτ ⟨j, hj, i, hi, x, hxw, hxi⟩
    have hmidσ : ∀ p (x : Edge), x ∈ F → (x.p = p ∨ x.q = p) → x ∈ cellE (endCell σ) →
        ¬ IsMid c s (k + 2 - 2) p := by
      intro p x hx hxp hxw hm
      rw [show k + 2 - 2 = k by omega] at hm
      obtain ⟨i, hi, hxi⟩ := mid_touch_L hle hpat hm hx hxp
      exact hσfar i hi x hxw hxi
    -- The start corners of `τ` carry dark edges of `τ`, chain strip or not.
    --
    have hcorn : (back τ.c τ.s ∈ F ∧
        ((back τ.c τ.s).p = back1 τ.c τ.s ∨ (back τ.c τ.s).q = back1 τ.c τ.s) ∧
        back τ.c τ.s ∈ cellE (cellJ τ.c τ.s 0)) ∧
        ∃ j < τ.n, ∃ x ∈ F, (x.p = front1 τ.c τ.s ∨ x.q = front1 τ.c τ.s) ∧
          x ∈ cellE (cellJ τ.c τ.s j) := by
      by_cases hnc : NoChain σ τ
      · exact start_corner_edges ((pat_flip_off hτ1 hnc).1 hl.2.2.2.1) hτ1
      · obtain ⟨jy, hjy, y, hy, hyu⟩ : ∃ jy < τ.n, ∃ y ∈ cellE (cellJ τ.c τ.s jy),
            y ∈ cellE (endCell σ) := by
          by_contra hn; push Not at hn; exact hnc hn
        obtain ⟨rfl, -⟩ := hnct.1 jy hjy y hy hyu
        rw [cellJ_zero] at hy
        obtain ⟨_, _, hbG, hfr, _⟩ := chain_start hl hnct.1 ⟨lu1, lu2⟩ hy hyu
        exact chain_corner_edges hτ1 hbG hfr (chain_sig hl hnct.1)
    obtain ⟨⟨hb, hbp, hb0⟩, hfr⟩ := hcorn
    have mσ1 : lat1 (endCell σ) σ.s ∈ cellE (endCell σ) := by rw [cellE_frame _ σ.s]; simp
    have mσ2 : lat2 (endCell σ) σ.s ∈ cellE (endCell σ) := by rw [cellE_frame _ σ.s]; simp
    refine ⟨⟨hσfar, hmidσ _ _ lu1 ((ends_lat1 _ _).inc_iff _ |>.2 (Or.inl rfl)) mσ1,
      hmidσ _ _ lu2 ((ends_lat2 _ _).inc_iff _ |>.2 (Or.inl rfl)) mσ2,
      fun i hi j hj y hy hy' => hnτ ⟨i, hi, j, hj, y, hy, hy'⟩,
      hmidτ _ ⟨0, by omega, _, hb, hbp, hb0⟩, hmidτ _ hfr, ?_⟩, ?_⟩
    · rintro hnc ⟨hcg, hcu⟩
      have hpτ : StripPat F τ.c τ.s τ.n := (pat_flip_off hτ1 hnc).1 hl.2.2.2.1
      have hlink : CR2 V F ⟨c, s, k + 2⟩ τ := link_a_pf hle hva hae ha2 hτ1 hpτ hl.2.2.2.2.1 hnτ hcg hcu
      have hokA : ChainOK ⟨c, s, k + 2⟩ τ := chainOK_of_noChain (fun j hj y hy hye =>
        hnτ ⟨j, hj, k + 1, by show k + 1 < k + 2; omega, y, hy, hye⟩)
      refine hvia τ L' ⟨hva, ⟨hae, hlink, hrest⟩, ⟨hokA, hnct.2⟩, ?_⟩
        (fun x hx => hnt x (List.mem_cons_of_mem _ hx))
        (fun _ j hj y hy hy' => hnτ ⟨τ.n - 1, by omega, j, hj, y, by unfold endCell at hy; exact hy,
          hy'⟩) ?_
      · intro x hx
        rcases List.mem_cons.1 hx with rfl | hx
        · exact hcorR
        · exact hR' x hx
      · rw [wt_cons]; rw [wt_cons] at hW; have := hl.1; show k + 2 + wt τ L' < W2; omega
    · refine ih τ hrest hnct.2 (endOK_of_link hl) hR' (fun j hj y hy hy' => hnτ ⟨τ.n - 1, by omega,
        j, hj, y, hy, hy'⟩) (fun w hw => hnt w (List.mem_cons_of_mem _ hw))
        (by rw [wt_cons] at hW; omega)

end nearpathPF

end HP

end ULHC
