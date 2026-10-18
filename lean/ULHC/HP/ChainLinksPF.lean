/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
import ULHC.HP.NearCAPF2

/-!
# Link transfer for path-factors (rule Tg)

ULHC's `chain_transfer_CA`: a chain of `F` whose links are far from `a` stays a chain of
`F ⊕ a`. For path-factors with `a` count-neutral:

* `osi_split_pf`: a linked end cell `u` (which splits) still splits the next start pair after `a`.
* `twist_transfer`: a twisting end cell still twists after `a`. Counting from both sides: flipping
  `u` first keeps the classes, so `a` is still a strip with the same end rule, and its flip
  can lower the count by at most one less than it raised `u`'s; and `u` cannot merge after `a`
  because it is not Type III there.
* `chain_transfer_pf`, `progress_step_pf`.
-/

namespace ULHC

namespace HP

open Finset Classical

-- **`chain_conn` with a local Type III hypothesis** (at the second cell only).
--
theorem chain_conn_loc {V : Finset Pt} {S : Finset Edge} {d : Pt} {tf : Side} {m : ℕ}
    (hm : 1 ≤ m) (hsig : SigFrom S d tf m 1) (hcell : 2 ≤ m → IsCell V (cellJ d tf 1))
    (hT1 : 2 ≤ m → NotTypeIII V S (cellJ d tf 1))
    (hb : back d tf ∈ S) (hf : front d tf ∈ S ↔ m = 1)
    (hx : lat1 d tf ∈ S ∨ lat2 d tf ∈ S) :
    Conn S (back1 d tf) (front1 d tf) := by
  by_cases h1 : lat1 d tf ∈ S
  · exact (ends_lat1 d tf).conn h1
  have h2 : lat2 d tf ∈ S := hx.resolve_left h1
  have p1 : Conn S (back1 d tf) (front2 d tf) :=
    ((ends_back d tf).conn hb).trans ((ends_lat2 d tf).conn h2)
  suffices hff : Conn S (front2 d tf) (front1 d tf) from p1.trans hff
  by_cases hm1 : m = 1
  · exact ((ends_front d tf).conn (hf.2 hm1)).symm
  have c1 : nb d tf = cellJ d tf 1 := by
    have := nb_cellJ d tf 0; rwa [cellJ_zero] at this
  obtain ⟨g1, g2, _, gf⟩ := hsig 1 le_rfl (by omega)
  have l1 : lat1 (cellJ d tf 1) tf ∈ S := g1.2 rfl
  have l2 : lat2 (cellJ d tf 1) tf ∈ S := g2.2 rfl
  have e1 := ends_lat1 (cellJ d tf 1) tf
  have e2 := ends_lat2 (cellJ d tf 1) tf
  rw [← c1, back1_nb] at e1
  rw [← c1, back2_nb] at e2
  by_cases hm2 : m = 2
  · -- The second cell is alternating and not Type III, so its corners are joined.
    --
    have hc := hcell (by omega)
    have bF : back (cellJ d tf 1) tf ∉ S := by
      rw [← c1, back_nb]; exact fun h => hm1 (hf.1 h)
    have fF : front (cellJ d tf 1) tf ∉ S := fun h => by have := (gf.1 h).1 rfl; omega
    have hall := alt_corners_conn' (hT1 (by omega)) (alt_of_lats l1 l2 bF fF)
    have hbb := (frame_of_allConn hall tf).1
    rw [← c1, back1_nb, back2_nb] at hbb
    exact hbb.symm
  · have fr : front (cellJ d tf 1) tf ∈ S := gf.2 ⟨fun _ => by omega, fun _ => rfl⟩
    rw [← c1] at l1 l2 fr
    exact (((e2.conn l2).trans ((ends_front _ tf).conn fr).symm).trans (e1.conn l1).symm)

-- **A twist keeps the classes.**
--
lemma twist_rel {V : Finset Pt} {F : Finset Edge} {u : Pt} {s : Side} (hu : IsCell V u)
    (l1 : lat1 u s ∈ F) (l2 : lat2 u s ∈ F) (bu : back u s ∉ F) (fu : front u s ∉ F)
    (hsame : Conn F (back1 u s) (back2 u s)) (heq : ncomp V (flip F u) = ncomp V F) :
    ∀ x y, Conn F x y ↔ Conn (flip F u) x y := by
  have hj := (twists_iff_conn hu l1 l2 bu fu hsame).1 heq
  have hfe := (mkLat u s).flip_eq (mkLat_cellE u s) l1 l2 bu fu
  have hrel := split_rel_pf (mkLat u s) l1 l2 hsame
  have hconn := flip_same_conn (mkLat u s) l1 l2 hsame
  rw [hfe] at hj ⊢
  intro x y
  constructor
  · intro h
    rcases (hrel x y).1 h with h | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact h
    · exact (h1.trans hj).trans h2
    · exact (h1.trans hj.symm).trans h2
  · exact hconn x y

-- Flipping an alternating cell inside one class: the count goes up by one exactly when the
-- flip separates two joined corners.
--
lemma split_count_of_sep {V : Finset Pt} {F : Finset Edge} {u : Pt} {s : Side} (hu : IsCell V u)
    (l1 : lat1 u s ∈ F) (l2 : lat2 u s ∈ F) (bu : back u s ∉ F) (fu : front u s ∉ F)
    (hsame : Conn F (back1 u s) (back2 u s)) {p q : Pt} (hp : p ∈ V) (hq : q ∈ V)
    (hpq : Conn F p q) (hn : ¬ Conn (flip F u) p q) : ncomp V (flip F u) = ncomp V F + 1 := by
  have hfe := (mkLat u s).flip_eq (mkLat_cellE u s) l1 l2 bu fu
  obtain ⟨ub1, ub2, uf1, uf2⟩ := isCell_corners hu s
  have hb := flip_same_count (V := V) (mkLat u s) ub1 uf1 ub2 uf2 l1 l2 hsame
  have hlt := ncomp_lt_of_refine (V := V)
    (fun x _ y _ h => flip_same_conn (mkLat u s) l1 l2 hsame x y h) hp hq hpq
    (by rw [← hfe]; exact hn)
  rw [hfe]
  omega

section osiPF

variable {V : Finset Pt} {F : Finset Edge} {c : Pt} {s : Side} {k : ℕ} {s0 t0 : Pt}
  (hF : Deg2Off V F s0 t0) (hs0 : s0 ∈ V) (hds : deg F s0 = 1) (hTR : NoTypeIIIR V F s0 t0)
  (hk : k % 2 = 0) (hcell : ∀ j ≤ k + 1, IsCell V (cellJ c s j))
  (hcor : ∀ j ≤ k + 1, ¬ IsCorner s0 (cellJ c s j) ∧ ¬ IsCorner t0 (cellJ c s j))
  (hpat : StripPat F c s (k + 2)) (hsep : ¬ Conn F (back1 c s) (front1 c s))
  (hneut : ncomp V (flipCol F c s (k + 2)) = ncomp V F)
  (hT' : NoTypeIIIR V (flipCol F c s (k + 2)) s0 t0)
  {u : Pt} {tf : Side} (hu : IsCell V u) (huR : ¬ IsCorner s0 u ∧ ¬ IsCorner t0 u)
  (lu1 : lat1 u tf ∈ F) (lu2 : lat2 u tf ∈ F) (bu : back u tf ∉ F) (fu : front u tf ∉ F)
  (hfar : ∀ j ≤ k + 1, ∀ e ∈ cellE u, e ∉ cellE (cellJ c s j))
include hF hs0 hds hTR hk hcell hcor hpat hsep hneut hT' hu huR lu1 lu2 bu fu hfar

-- `u` keeps its sides after `a`.
--
omit hF hs0 hds hTR hk hcell hcor hpat hsep hneut hT' hu huR in
lemma far_frame : lat1 u tf ∈ flipCol F c s (k + 2) ∧ lat2 u tf ∈ flipCol F c s (k + 2) ∧
    back u tf ∉ flipCol F c s (k + 2) ∧ front u tf ∉ flipCol F c s (k + 2) := by
  have hc' : ∀ e ∈ cellE u, (e ∈ flipCol F c s (k + 2) ↔ e ∈ F) := by
    intro e he
    rw [mem_flipCol, nOn_zero c s (fun j hj => hfar j (by omega) e he)]
    simp
  have mem : ∀ e, e = lat1 u tf ∨ e = lat2 u tf ∨ e = back u tf ∨ e = front u tf →
      e ∈ cellE u := by
    intro e he; rw [cellE_frame u tf]; rcases he with rfl | rfl | rfl | rfl <;> simp
  exact ⟨(hc' _ (mem _ (Or.inl rfl))).2 lu1, (hc' _ (mem _ (Or.inr (Or.inl rfl)))).2 lu2,
    fun h => bu ((hc' _ (mem _ (Or.inr (Or.inr (Or.inl rfl))))).1 h),
    fun h => fu ((hc' _ (mem _ (Or.inr (Or.inr (Or.inr rfl))))).1 h)⟩

-- `u`'s flip keeps `a` a strip of the same shape, with its classes refined.
--
omit hs0 hcell hcor hsep hTR hneut hT' huR in
lemma flip_far_strip (hsu : Conn F (back1 u tf) (back2 u tf)) :
    Deg2Off V (flip F u) s0 t0 ∧ deg (flip F u) s0 = 1 ∧ StripPat (flip F u) c s (k + 2) ∧
      (∀ x y, Conn (flip F u) x y → Conn F x y) := by
  have hfe := (mkLat u tf).flip_eq (mkLat_cellE u tf) lu1 lu2 bu fu
  have hcong : ∀ j < k + 2, ∀ e ∈ cellE (cellJ c s j), (e ∈ flip F u ↔ e ∈ F) :=
    fun j hj e he => mem_flip_off (fun h => hfar j (by omega) e h he)
  refine ⟨hF.flip (mkLat u tf) hu (mkLat_cellE u tf) lu1 lu2 bu fu, ?_,
    (stripPat_congr hcong).2 hpat, ?_⟩
  · rw [hfe, (mkLat u tf).deg_res lu1 lu2 bu fu]; exact hds
  · rw [hfe]; exact flip_same_conn (mkLat u tf) lu1 lu2 hsu

-- **A twisting end cell far from `a` still twists after `a`.**
--
theorem twist_transfer (htw : ncomp V (flip F u) = ncomp V F) :
    TwistsIn V (flipCol F c s (k + 2)) u := by
  obtain ⟨l1', l2', b', f'⟩ := far_frame (c := c) (s := s) (k := k) lu1 lu2 bu fu hfar
  set G' := flipCol F c s (k + 2) with hG'
  have hsu' : Conn G' (back1 u tf) (back2 u tf) :=
    (frame_of_allConn (alt_corners_conn' (hT' u hu huR.1 huR.2) (alt_of_lats l1' l2' b' f')) tf).1
  have hsuF : Conn F (back1 u tf) (back2 u tf) :=
    (frame_of_allConn (alt_corners_conn' (hTR u hu huR.1 huR.2) (alt_of_lats lu1 lu2 bu fu)) tf).1
  refine ⟨alt_of_lats l1' l2' b' f', ?_⟩
  obtain ⟨ub1, ub2, uf1, uf2⟩ := isCell_corners hu tf
  have hlo := (flip_same_count (V := V) (mkLat u tf) ub1 uf1 ub2 uf2 l1' l2' hsu').1
  rw [← (mkLat u tf).flip_eq (mkLat_cellE u tf) l1' l2' b' f'] at hlo
  have hrelH := twist_rel hu lu1 lu2 bu fu hsuF htw
  obtain ⟨hH, hdsH, hpatH, _⟩ := flip_far_strip hF hds hk hpat hu lu1 lu2 bu fu
    hfar hsuF
  have hTe : NotTypeIII V F (cellJ c s (k + 1)) :=
    restr_notT3 hTR (hcell (k + 1) le_rfl) (hcor (k + 1) le_rfl)
  have hsame := end_same_loc hTe hk hcell hpat
  have hsepH : ¬ Conn (flip F u) (back1 c s) (front1 c s) := fun h => hsep ((hrelH _ _).2 h)
  have hsameH := (hrelH _ _).1 hsame
  obtain ⟨H1, hH1, _, _, _, _, hcntH, _⟩ :=
    strip_even_rel_pf k hk (flip F u) hH hs0 hdsH hcell hcor hpatH hsepH hsameH
  obtain ⟨el1, el2, eb, ef⟩ := end_frame_pf hk hpatH
  obtain ⟨ab1, ab2, af1, af2⟩ := isCell_corners (hcell (k + 1) le_rfl) s
  have hup := (flip_same_count (V := V) (mkLat (cellJ c s (k + 1)) s) ab1 af1 ab2 af2 el1 el2
    hsameH).2
  rw [← (mkLat (cellJ c s (k + 1)) s).flip_eq (mkLat_cellE _ s) el1 el2 eb ef, ← hH1] at hup
  have hcomm : flip G' u = flipCol (flip F u) c s (k + 2) := flipCol_flip_comm F c s u (k + 2)
  rw [hcomm] at hlo ⊢
  omega

-- **A count-neutral strip's end cell splits** (count form).
--
omit hTR hT' hu huR lu1 lu2 bu fu hfar in
lemma end_splits_count (hsame : Conn F (back1 (cellJ c s (k + 1)) s) (back2 (cellJ c s (k + 1)) s)) :
    ncomp V (flip F (cellJ c s (k + 1))) = ncomp V F + 1 := by
  obtain ⟨el1, el2, eb, ef⟩ := end_frame_pf hk hpat
  obtain ⟨ab1, _, af1, _⟩ := isCell_corners (hcell (k + 1) le_rfl) s
  exact split_count_of_sep (hcell (k + 1) le_rfl) el1 el2 eb ef hsame ab1 af1
    ((ends_lat1 _ s).conn el1) (neutral_end_splits k hk F hF hs0 hds hcell hcor hpat hsep hsame hneut)

-- **`osi_split` for path-factors**: a splitting `u` still splits `x, y` after `a`.
--
theorem osi_split_pf (hspu : ncomp V (flip F u) = ncomp V F + 1)
    (hmu1 : ¬ IsMid c s k (back1 u tf)) (hmu2 : ¬ IsMid c s k (back2 u tf))
    {x y : Pt} (hxy : Conn F x y) (hsplit : ¬ Conn (flip F u) x y)
    (hx : ¬ IsMid c s k x) (hy : ¬ IsMid c s k y) :
    ¬ Conn (flip (flipCol F c s (k + 2)) u) x y := by
  have hsu : Conn F (back1 u tf) (back2 u tf) :=
    (frame_of_allConn (alt_corners_conn' (hTR u hu huR.1 huR.2) (alt_of_lats lu1 lu2 bu fu)) tf).1
  have hTe : NotTypeIII V F (cellJ c s (k + 1)) :=
    restr_notT3 hTR (hcell (k + 1) le_rfl) (hcor (k + 1) le_rfl)
  have hsame := end_same_loc hTe hk hcell hpat
  obtain ⟨F1, hF1, _, hconn, _, hodd, _, _⟩ :=
    strip_even_rel_pf k hk F hF hs0 hds hcell hcor hpat hsep hsame
  rw [flipCol_flip_comm]
  obtain ⟨hH, hdsH, hpatH, hHG⟩ := flip_far_strip hF hds hk hpat hu lu1 lu2 bu
    fu hfar hsu
  have hsepH : ¬ Conn (flip F u) (back1 c s) (front1 c s) := fun h => hsep (hHG _ _ h)
  set ua := cellJ c s (k + 1)
  by_cases hsameH : Conn (flip F u) (back1 ua s) (back2 ua s)
  · obtain ⟨F2, _, _, hconn2, _, hodd2, _, _⟩ :=
      strip_even_rel_pf k hk (flip F u) hH hs0 hdsH hcell hcor hpatH hsepH hsameH
    rw [hodd2 x y hx hy]
    rintro (h | ⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact hsplit (hconn2 _ _ h)
    · exact hsep (((hHG _ _ (hconn2 _ _ h1)).symm.trans hxy).trans (hHG _ _ (hconn2 _ _ h2)).symm)
    · exact hsep (((hHG _ _ (hconn2 _ _ h2)).trans hxy.symm).trans (hHG _ _ (hconn2 _ _ h1)))
  · -- `a`'s end cell is split by `u`: then `u` is split by `a`'s end cell (both split), and `u`
    -- would be a Type III cell of `F ⊕ a`.
    --
    exfalso
    have hcua := hcell (k + 1) le_rfl
    obtain ⟨la1, la2, ba, fa⟩ := end_frame_pf hk hpat
    have hspv := end_splits_count hF hs0 hds hk hcell hcor hpat hsep hneut hsame
    have hsym := split_symm_pf hF hs0 hds hu hcua lu1 lu2 bu fu la1 la2 ba fa
      (fun e h1 h2 => hfar (k + 1) le_rfl e h1 h2) hspu hspv
    have hn : ¬ Conn (flip F ua) (back1 u tf) (back2 u tf) := fun h => hsameH (hsym.2 h)
    have hn' : ¬ Conn (flipCol F c s (k + 2)) (back1 u tf) (back2 u tf) := by
      rw [hodd _ _ hmu1 hmu2]
      rintro (h | ⟨h1, h2⟩ | ⟨h1, h2⟩)
      · exact hn (hF1 ▸ h)
      · exact hsep (((hconn _ _ h1).symm.trans hsu).trans (hconn _ _ h2).symm)
      · exact hsep (((hconn _ _ h2).trans hsu.symm).trans (hconn _ _ h1))
    obtain ⟨l1', l2', b', f'⟩ := far_frame (c := c) (s := s) (k := k) lu1 lu2 bu fu hfar
    exact hn' (frame_of_allConn (alt_corners_conn' (hT' u hu huR.1 huR.2)
      (alt_of_lats l1' l2' b' f')) tf).1

-- **`osi_far` for path-factors.**
--
theorem osi_far_pf (hspu : ncomp V (flip F u) = ncomp V F + 1)
    (hmu1 : ¬ IsMid c s k (back1 u tf)) (hmu2 : ¬ IsMid c s k (back2 u tf))
    {x y : Pt} (hxy : Conn F x y) (hsplit : ¬ Conn (flip F u) x y)
    (hx : ¬ IsMid c s k x) (hy : ¬ IsMid c s k y) :
    (Conn (flipCol F c s (k + 2)) x y ∧ ¬ Conn (flip (flipCol F c s (k + 2)) u) x y) ∨
      ¬ Conn (flip F (cellJ c s (k + 1))) x y := by
  have hTe : NotTypeIII V F (cellJ c s (k + 1)) :=
    restr_notT3 hTR (hcell (k + 1) le_rfl) (hcor (k + 1) le_rfl)
  have hsame := end_same_loc hTe hk hcell hpat
  obtain ⟨F1, hF1, _, _, _, hodd, _, _⟩ :=
    strip_even_rel_pf k hk F hF hs0 hds hcell hcor hpat hsep hsame
  by_cases hC : Conn (flipCol F c s (k + 2)) x y
  · exact Or.inl ⟨hC, osi_split_pf hF hs0 hds hTR hk hcell hcor hpat hsep hneut hT' hu huR lu1 lu2
      bu fu hfar hspu hmu1 hmu2 hxy hsplit hx hy⟩
  · right
    intro h; exact hC ((hodd x y hx hy).2 (Or.inl (hF1 ▸ h)))

end osiPF

section transferPF

variable {V : Finset Pt} {F : Finset Edge} {c : Pt} {s : Side} {k : ℕ} {s0 t0 : Pt}
  (hF : Deg2Off V F s0 t0) (hs0 : s0 ∈ V) (hds : deg F s0 = 1) (hTR : NoTypeIIIR V F s0 t0)
  (hk : k % 2 = 0) (hcell : ∀ j ≤ k + 1, IsCell V (cellJ c s j))
  (hcor : ∀ j ≤ k + 1, ¬ IsCorner s0 (cellJ c s j) ∧ ¬ IsCorner t0 (cellJ c s j))
  (hpat : StripPat F c s (k + 2)) (hsep : ¬ Conn F (back1 c s) (front1 c s))
  (hneut : ncomp V (flipCol F c s (k + 2)) = ncomp V F)
  (hT' : NoTypeIIIR V (flipCol F c s (k + 2)) s0 t0)
include hF hs0 hds hTR hk hcell hcor hpat hsep hneut hT'

-- **One link after `a` survives `a`'s flip** (ULHC `link_transfer_CA`).
--
theorem link_transfer_pf {σ τ : StripSpec} (hσ : EndOK V F σ) (hev : σ.n % 2 = 0)
    (hσR : Restr s0 t0 σ) (hτR : Restr s0 t0 τ)
    (hl : CR2 V F σ τ) (hok : ChainOK σ τ) (hfl : FarLinkCA F ⟨c, s, k + 2⟩ σ τ) :
    CR2 V (flipCol F c s (k + 2)) σ τ := by
  have hl0 := hl
  obtain ⟨f1, f2, f3, f4, f5, f6, f7⟩ := hfl
  obtain ⟨h2, hev', hc1, hpatc, hcellc, hoff, hne, hendc, hm1, hm2, hxy, hsplit⟩ := hl
  obtain ⟨hu, lu1, lu2, bu, fu⟩ := hσ hev
  have huR : ¬ IsCorner s0 (endCell σ) ∧ ¬ IsCorner t0 (endCell σ) := hσR (σ.n - 1) (by omega)
  have hsu : Conn F (back1 (endCell σ) σ.s) (back2 (endCell σ) σ.s) :=
    (frame_of_allConn (alt_corners_conn' (hTR _ hu huR.1 huR.2) (alt_of_lats lu1 lu2 bu fu)) σ.s).1
  have hspu := link_end_splits hl0 hu lu1 lu2 bu fu hsu
  have hm2' : ¬ IsMid c s k (back1 (endCell σ) σ.s) := by simpa using f2
  have hm3' : ¬ IsMid c s k (back2 (endCell σ) σ.s) := by simpa using f3
  have hx' : ¬ IsMid c s k (back1 τ.c τ.s) := by simpa using f5
  have hy' : ¬ IsMid c s k (front1 τ.c τ.s) := by simpa using f6
  have hfar' : ∀ j ≤ k + 1, ∀ e ∈ cellE (endCell σ), e ∉ cellE (cellJ c s j) :=
    fun j hj e he => f1 j (by show j < k + 2; omega) e he
  -- Sides of `τ` are not sides of `a`'s cells.
  --
  have hkeepτ : ∀ i < τ.n, ∀ e ∈ cellE (cellJ τ.c τ.s i),
      (e ∈ flipCol F c s (k + 2) ↔ e ∈ F) := by
    intro i hi e he
    rw [mem_flipCol, nOn_zero c s (fun j hj => f4 i hi j (by show j < k + 2; omega) e he)]
    simp
  have hpat' : StripPat (flip (flipCol F c s (k + 2)) (endCell σ)) τ.c τ.s τ.n := by
    obtain ⟨n, hn⟩ : ∃ n, τ.n = n + 1 := ⟨τ.n - 1, by omega⟩
    rw [hn] at hpatc ⊢
    refine (stripPat_congr (fun i hi e he => ?_)).2 hpatc
    rw [mem_flip_iff, mem_flip_iff, hkeepτ i (by omega) e he]
  have hsplit' : ¬ Conn (flip (flipCol F c s (k + 2)) (endCell σ)) (back1 τ.c τ.s)
      (front1 τ.c τ.s) :=
    osi_split_pf hF hs0 hds hTR hk hcell hcor hpat hsep hneut hT' hu huR lu1 lu2 bu fu hfar' hspu hm2' hm3' hxy hsplit hx' hy'
  have hconn' : Conn (flipCol F c s (k + 2)) (back1 τ.c τ.s) (front1 τ.c τ.s) := by
    by_cases hnc : NoChain σ τ
    · rcases osi_far_pf hF hs0 hds hTR hk hcell hcor hpat hsep hneut hT' hu huR lu1 lu2 bu fu hfar' hspu hm2' hm3' hxy hsplit hx' hy' with h | h
      · exact h.1
      · exact absurd ⟨hxy, h⟩ (f7 hnc)
    · -- A chain link: the start pair is joined through the shared side.
      --
      unfold NoChain at hnc
      push Not at hnc
      obtain ⟨j, hj, x, hx, hxu⟩ := hnc
      obtain ⟨rfl, hxl⟩ := hok j hj x hx hxu
      rw [cellJ_zero] at hx
      have hxlat := chain_lat hl0 hok ⟨lu1, lu2⟩ hx hxu
      have hxG : x ∈ F := by rcases hxl with rfl | rfl; exacts [lu1, lu2]
      have hsig := chain_sig hl0 hok
      have hc0 : ∀ e ∈ cellE τ.c, (e ∈ flipCol F c s (k + 2) ↔ e ∈ F) := fun e he =>
        hkeepτ 0 hc1 e (by rw [cellJ_zero]; exact he)
      have hsig' : SigFrom (flipCol F c s (k + 2)) τ.c τ.s τ.n 1 := by
        intro i hi hin
        have mem : ∀ y, y = lat1 (cellJ τ.c τ.s i) τ.s ∨ y = lat2 (cellJ τ.c τ.s i) τ.s ∨
            y = back (cellJ τ.c τ.s i) τ.s ∨ y = front (cellJ τ.c τ.s i) τ.s →
            y ∈ cellE (cellJ τ.c τ.s i) := by
          intro y hy; rw [cellE_frame _ τ.s]; rcases hy with rfl | rfl | rfl | rfl <;> simp
        obtain ⟨g1, g2, gb, gf⟩ := hsig i hi hin
        rw [← hkeepτ i hin _ (mem _ (Or.inl rfl))] at g1
        rw [← hkeepτ i hin _ (mem _ (Or.inr (Or.inl rfl)))] at g2
        rw [← hkeepτ i hin _ (mem _ (Or.inr (Or.inr (Or.inl rfl))))] at gb
        rw [← hkeepτ i hin _ (mem _ (Or.inr (Or.inr (Or.inr rfl))))] at gf
        exact ⟨g1, g2, gb, gf⟩
      have memc : ∀ y, y = lat1 τ.c τ.s ∨ y = lat2 τ.c τ.s ∨ y = back τ.c τ.s ∨
          y = front τ.c τ.s → y ∈ cellE τ.c := by
        intro y hy; rw [cellE_frame _ τ.s]; rcases hy with rfl | rfl | rfl | rfl <;> simp
      have hne0 : τ.c ≠ endCell σ := by
        have := hne 0 hc1; rwa [cellJ_zero] at this
      have hother : ∀ y ∈ cellE τ.c, y ≠ x → (y ∈ flip F (endCell σ) ↔ y ∈ F) :=
        fun y hy hyx => mem_flip_off (fun hyu => hyx (inter_unique hne0 hy hyu hx hxu))
      obtain ⟨n1, n2, n3, n4, _, _⟩ := frame_ne τ.c τ.s
      have hbx : back τ.c τ.s ≠ x := by rcases hxlat with rfl | rfl; exacts [n1, n2]
      have hfx : front τ.c τ.s ≠ x := by rcases hxlat with rfl | rfl; exacts [n3, n4]
      have hb0 : back τ.c τ.s ∈ flipCol F c s (k + 2) := by
        rw [hc0 _ (memc _ (Or.inr (Or.inr (Or.inl rfl)))),
          ← hother _ (memc _ (Or.inr (Or.inr (Or.inl rfl)))) hbx]
        exact hpatc.1
      have hf0 : front τ.c τ.s ∈ flipCol F c s (k + 2) ↔ τ.n = 1 := by
        rw [hc0 _ (memc _ (Or.inr (Or.inr (Or.inr rfl)))),
          ← hother _ (memc _ (Or.inr (Or.inr (Or.inr rfl)))) hfx]
        have := hpatc.2.2 0 hc1
        rw [cellJ_zero] at this
        rw [this]; omega
      have hx0 : lat1 τ.c τ.s ∈ flipCol F c s (k + 2) ∨ lat2 τ.c τ.s ∈ flipCol F c s (k + 2) := by
        rcases hxlat with h | h
        · left; rw [← h, hc0 _ hx]; exact hxG
        · right; rw [← h, hc0 _ hx]; exact hxG
      exact chain_conn_loc hc1 hsig' (fun _ => hcellc 1 (by omega))
        (fun h => hT' _ (hcellc 1 (by omega)) (hτR 1 (by omega)).1 (hτR 1 (by omega)).2) hb0 hf0 hx0
  exact ⟨h2, hev', hc1, hpat', hcellc, hoff, hne, hendc, hm1, hm2, hconn', hsplit'⟩

-- **Tg chains far from `a` survive `a`'s flip** (ULHC `chain_transfer_CA`). The last strip's
-- end cell keeps twisting (`twist_transfer`).
--
theorem chain_transfer_pf : ∀ (L : List StripSpec) (σ : StripSpec), 1 ≤ σ.n →
    EndOK V F σ → CRChainTg V F σ L → CATail (σ :: L) → (∀ x ∈ σ :: L, Restr s0 t0 x) →
    FarChainCA F ⟨c, s, k + 2⟩ σ L →
    (L = [] → σ.n % 2 = 0 → ∀ j ≤ k + 1, ∀ e ∈ cellE (endCell σ), e ∉ cellE (cellJ c s j)) →
    CRChainTg V (flipCol F c s (k + 2)) σ L := by
  intro L
  induction L with
  | nil =>
    intro σ h1 hσ hch _ hR _ hlast
    rcases (hch : TgEnd V F σ) with h | ⟨hev, htw⟩
    · exact Or.inl h
    · obtain ⟨hu, lu1, lu2, bu, fu⟩ := hσ hev
      exact Or.inr ⟨hev, twist_transfer hF hs0 hds hTR hk hcell hcor hpat hsep hneut hT' hu (hR σ (by simp) (σ.n - 1) (by omega)) lu1 lu2 bu fu
        (hlast rfl hev) htw.2⟩
  | cons τ L ih =>
    intro σ _ hσ hch hcat hR hfar _
    obtain ⟨hev, hl, hrest⟩ := hch
    have hR' : ∀ x ∈ τ :: L, Restr s0 t0 x := fun x hx => hR x (List.mem_cons_of_mem _ hx)
    exact ⟨hev, link_transfer_pf hF hs0 hds hTR hk hcell hcor hpat hsep hneut hT' hσ hev (hR σ (List.mem_cons_self ..))
      (hR' τ (List.mem_cons_self ..)) hl hcat.1 hfar.1,
      ih τ hl.2.2.1 (endOK_of_link hl) hrest hcat.2 hR' hfar.2
        (fun _ _ j hj e he => hfar.1.2.2.2.1 (τ.n - 1) (by have := hl.2.2.1; omega) j
          (by show j < k + 2; omega) e he)⟩

-- **`created_step` for path-factors.**
--
omit hTR hneut hT' in
theorem created_step_pf
    (hsame : Conn F (back1 (cellJ c s (k + 1)) s) (back2 (cellJ c s (k + 1)) s))
    {x y : Pt} (hxy : Conn F x y) (hsplit : ¬ Conn (flip F (cellJ c s (k + 1))) x y)
    (hx : ¬ IsMid c s k x) (hy : ¬ IsMid c s k y) :
    ¬ Conn (flipCol F c s (k + 2)) x y := by
  obtain ⟨F1, hF1, _, hconn, _, hodd, _, _⟩ :=
    strip_even_rel_pf k hk F hF hs0 hds hcell hcor hpat hsep hsame
  rw [hodd x y hx hy]
  subst hF1
  rintro (h | ⟨h1, h2⟩ | ⟨h1, h2⟩)
  · exact hsplit h
  · exact hsep (((hconn _ _ h1).symm.trans hxy).trans (hconn _ _ h2).symm)
  · exact hsep (((hconn _ _ h2).trans hxy.symm).trans (hconn _ _ h1))

-- **The first link becomes a valid strip** (ULHC `link_step`).
--
omit hneut hT' in
theorem link_step_pf {b : StripSpec} (hl : CR2 V F ⟨c, s, k + 2⟩ b) :
    ValidStrip V (flipCol F c s (k + 2)) b := by
  obtain ⟨_, _, hc1, hpatc, hcellc, hoff, _, _, hm1, hm2, hxy, hsplit⟩ := hl
  have hTe : NotTypeIII V F (cellJ c s (k + 1)) :=
    restr_notT3 hTR (hcell (k + 1) le_rfl) (hcor (k + 1) le_rfl)
  have hsame := end_same_loc hTe hk hcell hpat
  have hm1' : ¬ IsMid c s k (back1 b.c b.s) := by simpa using hm1
  have hm2' : ¬ IsMid c s k (front1 b.c b.s) := by simpa using hm2
  refine ⟨hc1, ?_, hcellc, created_step_pf hF hs0 hds hk hcell hcor hpat hsep hsame hxy hsplit hm1'
    hm2'⟩
  obtain ⟨n, hn⟩ : ∃ n, b.n = n + 1 := ⟨b.n - 1, by omega⟩
  rw [hn] at hpatc ⊢
  refine (stripPat_congr (fun j hj e he => ?_)).2 hpatc
  exact flipCol_off F c s (k + 1) (fun i hi => hoff j (by omega) i (by show i + 1 < k + 2; omega) e he)

-- **One round** (ULHC `progress_step_CA`): after `a`, the rest of a far path through `a` is a
-- path of `F ⊕ a`.
--
theorem progress_step_pf {b : StripSpec} {L : List StripSpec}
    (hch : CRChainTg V F ⟨c, s, k + 2⟩ (b :: L)) (hcat : CATail (⟨c, s, k + 2⟩ :: b :: L))
    (hR : ∀ x ∈ b :: L, Restr s0 t0 x) (hfar : FarChainCA F ⟨c, s, k + 2⟩ b L) :
    RPathTg V (flipCol F c s (k + 2)) s0 t0 b L ∧ wt b L + (k + 2) = wt ⟨c, s, k + 2⟩ (b :: L) := by
  obtain ⟨_, hl, hrest⟩ := hch
  have hlast : L = [] → b.n % 2 = 0 → ∀ j ≤ k + 1, ∀ e ∈ cellE (endCell b),
      e ∉ cellE (cellJ c s j) := by
    intro _ hev j hj e he
    rcases Nat.lt_or_ge j (k + 1) with hjk | hjk
    · exact hl.2.2.2.2.2.1 (b.n - 1) (by have := hl.2.2.1; omega) j (by show j + 1 < k + 2; omega)
        e he
    · obtain rfl : j = k + 1 := by omega
      exact hl.2.2.2.2.2.2.2.1 hev e he
  refine ⟨⟨link_step_pf hF hs0 hds hTR hk hcell hcor hpat hsep hl,
    chain_transfer_pf hF hs0 hds hTR hk hcell hcor hpat hsep hneut hT' L b hl.2.2.1 (endOK_of_link hl) hrest hcat.2 hR hfar hlast, hcat.2, hR⟩, ?_⟩
  rw [wt_cons]; show wt b L + (k + 2) = k + 2 + wt b L; omega

end transferPF

end HP

end ULHC
