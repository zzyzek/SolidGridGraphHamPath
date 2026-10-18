/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
import ULHC.HP.ChainLinksPF

/-!
# `comp_clean` for path-factors with rule Tg

ULHC's `PathComplete` source/via lemmas and `comp_clean`, for path-factors, restricted strips,
count-neutral strips and Tg chains (`RPathTg`). The cells next to the strip where ULHC uses
"not Type III" and which may be endpoint cells are hypotheses E1, E2, E3.
-/

namespace ULHC

namespace HP

open Finset Classical

-- **A strip flip keeps every degree.**
--
lemma degs_flipCol {V : Finset Pt} {c : Pt} {s : Side} :
    ∀ n (F : Finset Edge), Inside V F → StripPat F c s n → (∀ j < n, IsCell V (cellJ c s j)) →
      Inside V (flipCol F c s n) ∧ ∀ z, deg (flipCol F c s n) z = deg F z := by
  intro n
  induction n with
  | zero => intro F hF _ _; exact ⟨hF, fun _ => rfl⟩
  | succ n ih =>
    intro F hF hpat hcell
    rw [flipCol_succ]
    have hce := hcell n (by omega)
    obtain ⟨hb, hl, hf⟩ := hpat
    have mF : front (cellJ c s n) s ∈ F ↔ n % 2 = 0 := by
      have := hf n (by omega); simp only [lt_self_iff_false, iff_false] at this; rw [this]; omega
    have mB : back (cellJ c s n) s ∈ F ↔ n % 2 = 0 := by
      rcases n with _ | n
      · simp only [cellJ_zero]; simp [hb]
      · rw [back_cellJ_succ]
        have := hf n (by omega)
        have q : n + 1 < n + 1 + 1 := by omega
        simp only [q, iff_true] at this
        rw [this]; omega
    have mL1 := (hl n (by omega)).1
    have mL2 := (hl n (by omega)).2
    have hF' : Inside V (ULHC.flip F (cellJ c s n)) ∧
        ∀ z, deg (ULHC.flip F (cellJ c s n)) z = deg F z := by
      refine ⟨inside_flip hF hce, fun z => ?_⟩
      rcases Nat.mod_two_eq_zero_or_one n with h | h
      · have n1 : lat1 (cellJ c s n) s ∉ F := fun h' => by have := mL1.1 h'; omega
        have n2 : lat2 (cellJ c s n) s ∉ F := fun h' => by have := mL2.1 h'; omega
        rw [(mkBF _ s).flip_eq (mkBF_cellE _ s) (mB.2 h) (mF.2 h) n1 n2,
          (mkBF _ s).deg_res (mB.2 h) (mF.2 h) n1 n2]
      · have n1 : back (cellJ c s n) s ∉ F := fun h' => by have := mB.1 h'; omega
        have n2 : front (cellJ c s n) s ∉ F := fun h' => by have := mF.1 h'; omega
        rw [(mkLat _ s).flip_eq (mkLat_cellE _ s) (mL1.2 h) (mL2.2 h) n1 n2,
          (mkLat _ s).deg_res (mL1.2 h) (mL2.2 h) n1 n2]
    rcases n with _ | n
    · simpa [flipCol] using hF'
    · obtain ⟨h1, h2⟩ := ih _ hF'.1 (pat_flip_end ⟨hb, hl, hf⟩) (fun j hj => hcell j (by omega))
      exact ⟨h1, fun z => (h2 z).trans (hF'.2 z)⟩

-- A valid restricted strip in a factor without restricted Type III cells has two cells or more.
--
lemma valid_two_pf {V : Finset Pt} {F : Finset Edge} {s0 t0 : Pt} {q : StripSpec}
    (hv : ValidStrip V F q) (hqR : Restr s0 t0 q) (hT : NoTypeIIIR V F s0 t0) : 2 ≤ q.n := by
  by_contra hn
  obtain ⟨h1, hp, hc, hsep⟩ := hv
  have h1' : q.n = 1 := by omega
  have hc0 : IsCell V q.c := by have := hc 0 (by omega); rwa [cellJ_zero] at this
  have hr := hqR 0 (by omega)
  rw [cellJ_zero] at hr
  obtain ⟨g1, g2, gb, gf⟩ := strip_sig hp (show 0 < q.n by omega)
  rw [cellJ_zero] at g1 g2 gb gf
  exact hsep (hT q.c hc0 hr.1 hr.2 q.s (gb.2 rfl) (gf.2 ⟨fun h => by omega, fun h => by omega⟩)
    (fun h => by have := g1.1 h; omega) (fun h => by have := g2.1 h; omega))

section via

variable {V : Finset Pt} {F : Finset Edge} {c : Pt} {s : Side} {k : ℕ} {s0 t0 : Pt}
  (hF : Deg2Off V F s0 t0) (hs0 : s0 ∈ V) (hds : deg F s0 = 1) (hle : ∀ z, deg F z ≤ 2)
  (hTR : NoTypeIIIR V F s0 t0) (hk : k % 2 = 0)
  (hcell : ∀ j ≤ k + 1, IsCell V (cellJ c s j))
  (hcor : ∀ j ≤ k + 1, ¬ IsCorner s0 (cellJ c s j) ∧ ¬ IsCorner t0 (cellJ c s j))
  (hpat : StripPat F c s (k + 2))
  (hsep : ¬ Conn F (back1 c s) (front1 c s)) (hT' : NoTypeIIIR V (flipCol F c s (k + 2)) s0 t0)
  (hneut : ncomp V (flipCol F c s (k + 2)) = ncomp V F)
include hF hs0 hds hle hTR hk hcell hcor hpat hsep hT' hneut

-- **Shortcut paths** (ULHC `via_path`). A path through `a` whose tail keeps off `a` gives a path
-- of `F ⊕ a`.
--
theorem via_path_tg : ∀ (n : ℕ) (w : StripSpec) (R : List StripSpec),
    RPathTg V F s0 t0 ⟨c, s, k + 2⟩ (w :: R) → wt ⟨c, s, k + 2⟩ (w :: R) = n →
    (∀ x ∈ R, ¬ Touches ⟨c, s, k + 2⟩ x) →
    (R ≠ [] → ∀ j < k + 2, ∀ y ∈ cellE (endCell w), y ∉ cellE (cellJ c s j)) →
    ∃ σ L, RPathTg V (flipCol F c s (k + 2)) s0 t0 σ L := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro w R hP hwt hnt hfe
  by_contra hno
  have hvia : ViaFreeTg V F s0 t0 ⟨c, s, k + 2⟩ n := fun w' R' hP' hnt' hfe' hlt =>
    hno (ih _ hlt w' R' hP' rfl hnt' hfe')
  obtain ⟨_, hch, hcat, hR⟩ := hP
  have hRw : ∀ x ∈ w :: R, Restr s0 t0 x := fun x hx => hR x (List.mem_cons_of_mem _ hx)
  have hfar : FarChainCA F ⟨c, s, k + 2⟩ w R := by
    cases R with
    | nil => trivial
    | cons τ R' =>
      exact farchain_pf hle hk hcell hcor hpat hsep hvia (τ :: R') w hch.2.2 hcat.2
        (endOK_of_link hch.2.1) hRw (hfe (by simp)) hnt (by rw [← hwt, wt_cons]; exact le_rfl)
  exact hno ⟨w, R, (progress_step_pf hF hs0 hds hTR hk hcell hcor hpat hsep hneut hT' hch hcat hRw
    hfar).1⟩

end via

section source

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

-- In a minimum path, when `F ⊕ a` has no path, the strips after the first keep off `a`.
--
theorem src_notouch_tg [NearOK V t0] {q : StripSpec} {L : List StripSpec} (hP : RPathTg V F s0 t0 q L)
    (hWq : W = wt q L) (hno : ¬ ∃ σ L', RPathTg V (flipCol F c s (k + 2)) s0 t0 σ L') :
    ∀ τ ∈ L, ¬ Touches ⟨c, s, k + 2⟩ τ :=
  notouch_pf hF hs0 hds hle hTR hk hcell hcor hpat hsep hT' hneut hTs hTend hTd hmin (W2 := k + 2 + wt q L)
    (fun w R hP' hnt hfe _ => hno (via_path_tg hF hs0 hds hle hTR hk hcell hcor hpat hsep hT' hneut _ w R hP' rfl hnt hfe))
    (fun _ _ => hno) L q hP.2.1 hP.2.2.1 (endOK_of_valid hP.1) hP.2.2.2 (le_of_eq hWq.symm) le_rfl

-- **The first strip** (ULHC `src_touch`). In a minimum path, when `F ⊕ a` has no path, a first
-- strip touching `a` starts beside `a`'s start cell and runs against `a`.
--
theorem src_touch_tg [NearOK V t0] {q : StripSpec} {L : List StripSpec} (hP : RPathTg V F s0 t0 q L)
    (hWq : W = wt q L) (hno : ¬ ∃ σ L', RPathTg V (flipCol F c s (k + 2)) s0 t0 σ L')
    (htq : Touches ⟨c, s, k + 2⟩ q) :
    q.s = s.opp ∧ (q.c = nb c (latA s) ∨ q.c = nb c (latB s)) := by
  obtain ⟨i, hi, j, hj, x, hx1, hx2⟩ := htq
  have hntL := src_notouch_tg hF hs0 hds hle hTR hk hcell hcor hpat hsep hT' hneut hTs hTend hTd hmin hP hWq hno
  have nopath : ∀ σ' L', RPathTg V F s0 t0 σ' L' → wt σ' L' < W → False :=
    fun σ' L' h hlt => by have := hmin σ' L' h; omega
  have hW1 : wt q L ≤ W := le_of_eq hWq.symm
  obtain ⟨hv, hch, hnct, hR⟩ := hP
  have hpq : StripPat F q.c q.s q.n := hv.2.1
  have hcq : ∀ j < q.n, IsCell V (cellJ q.c q.s j) := hv.2.2.1
  have hqR : Restr s0 t0 q := hR q (List.mem_cons_self ..)
  have hq2 := valid_two_pf hv hqR hTR
  have hvia : ViaFreeTg V F s0 t0 ⟨c, s, k + 2⟩ (k + 2 + wt q L) := fun w R hP' hnt hfe _ =>
    hno (via_path_tg hF hs0 hds hle hTR hk hcell hcor hpat hsep hT' hneut _ w R hP' rfl hnt hfe)
  have hDc := corners_deg2 hF hcell hcor
  have hTe : NotTypeIII V F (cellJ c s (k + 1)) :=
    restr_notT3 hTR (hcell (k + 1) le_rfl) (hcor (k + 1) le_rfl)
  have hsame := end_same_loc hTe hk hcell hpat
  have hca : ∀ j < k + 2, IsCell V (cellJ c s j) := fun j hj => hcell j (by omega)
  have hva : ValidStrip V F ⟨c, s, k + 2⟩ := ⟨by show 1 ≤ k + 2; omega, hpat, hca, hsep⟩
  have hcorR : Restr s0 t0 ⟨c, s, k + 2⟩ := fun j hj => hcor j (by simp only at hj; omega)
  set e := cellJ c s (k + 1) with he_def
  have hae : (⟨c, s, k + 2⟩ : StripSpec).n % 2 = 0 := by show (k + 2) % 2 = 0; omega
  have ha2 : 2 ≤ (⟨c, s, k + 2⟩ : StripSpec).n := by show 2 ≤ k + 2; omega
  have hcorR' := hcorR
  have via_a : ∀ w L3, L = w :: L3 → StripPat F w.c w.s w.n →
      ¬ Conn (flip F e) (back1 w.c w.s) (front1 w.c w.s) → False := by
    intro w L3 hL hpw hsplit
    subst hL
    obtain ⟨_, hlw, hrest⟩ := hch
    have hnt := hntL w (List.mem_cons_self ..)
    have hw1 : 1 ≤ w.n := hlw.2.2.1
    have hlink : CR2 V F ⟨c, s, k + 2⟩ w := link_a_pf hle hva hae ha2 hw1 hpw hlw.2.2.2.2.1 hnt
      hlw.2.2.2.2.2.2.2.2.2.2.1 hsplit
    refine hvia w L3 ⟨hva, ⟨hae, hlink, hrest⟩,
      ⟨chainOK_of_noChain (fun jw hjw y hy hye => hnt ⟨jw, hjw, k + 1, by show k + 1 < k + 2; omega,
        y, hy, hye⟩), hnct.2⟩, ?_⟩
      (fun x hx => hntL x (List.mem_cons_of_mem _ hx))
      (fun _ j hj y hy hy' => hnt ⟨w.n - 1, by omega, j, hj, y, by unfold endCell at hy; exact hy, hy'⟩) ?_
    · intro x hx
      rcases List.mem_cons.1 hx with rfl | hx
      · exact hcorR
      · exact hR x (List.mem_cons_of_mem _ hx)
    · rw [wt_cons, wt_cons]; show k + 2 + wt w L3 < k + 2 + (q.n + wt w L3); have := hv.1; omega
  have hqc0 : cellJ q.c q.s 0 = q.c := cellJ_zero q.c q.s
  obtain ⟨el1, el2, eb, ef⟩ := end_frame_pf hk hpat
  have hce : IsCell V e := hcell (k + 1) le_rfl
  have hc0 : IsCell V c := by have := hcell 0 (by omega); rwa [cellJ_zero] at this
  -- **Through the end cell.**
  --
  have hR1 : ∀ i' < q.n, cellJ q.c q.s i' = e → False := by
    intro i' hi' hq
    obtain ⟨hend, hdir⟩ := touch_end_L hk hpat (sig_of_pat hpq) (Nat.zero_le _) hi' hq
    have hendq : endCell q = e := by
      unfold endCell; rw [← hq, show q.n - 1 = i' by omega]
    rcases hdir with ⟨_, hodd⟩ | ⟨hperp, hev⟩
    · cases L with
      | nil =>
        rcases (hch : TgEnd V F q) with h | ⟨_, htw⟩
        · omega
        · rw [hendq] at htw
          exact end_not_twists hF hs0 hds hk hcell hcor hpat hsep hsame hneut htw
      | cons w L3 =>
        have hlw := hch.2.1
        have hnt := hntL w (List.mem_cons_self ..)
        have hpw : StripPat F w.c w.s w.n := by
          have h := hlw.2.2.2.1
          rw [hendq] at h
          exact (pat_flip_off hlw.2.2.1 (fun jw hjw y hy hy' =>
            hnt ⟨jw, hjw, k + 1, by show k + 1 < k + 2; omega, y, hy, hy'⟩)).1 h
        have hsplit := hlw.2.2.2.2.2.2.2.2.2.2.2
        rw [hendq] at hsplit
        exact via_a w L3 rfl hpw hsplit
    · by_cases hi0 : i' = 0
      · omega
      · have hp := cell_prev_L (z := q.c) (tf := q.s) (i := i') (by omega)
        rw [hq] at hp
        rcases hperp with ht | ht
        · rw [show q.s.opp = latB s by rw [ht, latA_opp_eq]] at hp
          rcases touch_side2_end_L hDc hk hpat (sig_of_pat hpq) (i := i' - 1) (Nat.zero_le _)
              (by omega) hp with ⟨ht', _⟩ | ⟨_, hf, hl⟩
          · exact latA_ne_opp s (ht.symm.trans ht')
          · obtain ⟨hcL, hnT⟩ := beside_end2_pf hF hs0 hds hk hcell hcor hpat hsep hsame hneut
              ((outer2_body_L hDc hpat le_rfl).2 hk) hf hl (by rw [← hp]; exact (hqR (i' - 1) (by omega)).2)
            exact hnT (hTend _ (Or.inr rfl) hcL)
        · rw [show q.s.opp = latA s by rw [ht, latB_opp_eq]] at hp
          rcases touch_side1_end_L hDc hk hpat (sig_of_pat hpq) (i := i' - 1) (Nat.zero_le _)
              (by omega) hp with ⟨ht', _⟩ | ⟨_, hf, hl⟩
          · exact latB_ne_opp s (ht.symm.trans ht')
          · obtain ⟨hcL, hnT⟩ := beside_end1_pf hF hs0 hds hk hcell hcor hpat hsep hsame hneut
              ((outer1_body_L hDc hpat le_rfl).2 hk) hf hl (by rw [← hp]; exact (hqR (i' - 1) (by omega)).2)
            exact hnT (hTend _ (Or.inl rfl) hcL)
  -- **Through the cell beyond the end cell.**
  --
  have hR2 : ∀ i' < q.n, cellJ q.c q.s i' = nb e s → False := by
    intro i' hi' hq
    rcases touch_beyond_L hDc hk hpat (sig_of_pat hpq) (Nat.zero_le _) hi'
        (fun _ _ => Nat.zero_le _) (fun _ => Nat.zero_le _) hq with ⟨ht, hodd, hend⟩ |
        ⟨ht, _, hi1⟩ | ⟨hperp, h0⟩
    · have hendq : endCell q = nb e s := by
        unfold endCell; rw [← hq, show q.n - 1 = i' by omega]
      obtain ⟨g1, g2, gb, _⟩ := strip_sig hpq hi'
      rw [hq, ht] at g1 g2 gb
      rw [(frame_opp (nb e s) s).1] at g1
      rw [(frame_opp (nb e s) s).2.1] at g2
      rw [(frame_opp (nb e s) s).2.2.1] at gb
      have ul1 := g1.2 hodd
      have ul2 := g2.2 hodd
      have uf : front (nb e s) s ∉ F := fun h => by have := gb.1 h; omega
      have hcu' : IsCell V (nb e s) := by rw [← hq]; exact hcq i' hi'
      cases L with
      | nil =>
        rcases (hch : TgEnd V F q) with h | ⟨_, htw⟩
        · omega
        · rw [hendq] at htw
          exact beyond_not_twists hF hs0 hds hle hk hcell hcor hpat hsep hsame hneut hcu' ul1 ul2 uf
            htw
      | cons w L3 =>
        have hlw := hch.2.1
        have hnt := hntL w (List.mem_cons_self ..)
        have hsplit := hlw.2.2.2.2.2.2.2.2.2.2.2
        rw [hendq] at hsplit
        have hncw : NoChain q w := by
          intro jw hjw y hy hyu
          obtain ⟨rfl, hyl⟩ := hnct.1 jw hjw y hy hyu
          rw [hendq] at hyu hyl
          exact hnt (e1_chain_L hDc hk hcell hpat hlw (hnct.1) hendq ht ul1 ul2 hy hyu hyl)
        have hpw : StripPat F w.c w.s w.n := (pat_flip_off hlw.2.2.1 hncw).1 hlw.2.2.2.1
        have hcorner : ∀ y ∈ F, ∀ jw < w.n, y ∈ cellE (cellJ w.c w.s jw) → ∀ r,
            (y.p = r ∨ y.q = r) → r ≠ front1 e s ∧ r ≠ front2 e s := by
          intro y hy jw hjw hyw r hr
          have touchy : y ∈ cellE e → False := fun h =>
            hnt ⟨jw, hjw, k + 1, by show k + 1 < k + 2; omega, y, hyw, h⟩
          have chainy : y ∈ cellE (nb e s) → False := fun h =>
            hncw jw hjw y hyw (by rw [hendq]; exact h)
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
      rw [hqc0] at hq
      by_cases hm : 2 ≤ q.n
      · exact beyond_cross_pf hF hs0 hds hle hTR hk hcell hcor hpat hsep hT' hneut hTs hTend hpq hqR
          hperp hq hm (fun _ _ => hno)
      · omega
  -- **Beside the start cell**: the suffix from there is a lighter path.
  --
  have hR3 : q.s = s.opp → ∀ i0 < q.n, i0 % 2 = 0 → i0 ≠ 0 →
      (cellJ q.c q.s i0 = nb c (latA s) ∨ cellJ q.c q.s i0 = nb c (latB s)) → False := by
    intro ht i0 hi0 hev hi00 hq
    have hcR := hqR i0 hi0
    have hcL := hcq i0 hi0
    have hdc1 : deg F (front1 c s) = 2 := hDc 0 (by omega) _ (by rw [cellJ_zero]; exact isCorner_front1 c s)
    have hdc2 : deg F (front2 c s) = 2 := hDc 0 (by omega) _ (by rw [cellJ_zero]; exact isCorner_front2 c s)
    have hsep' : ¬ Conn F (back1 (cellJ q.c q.s i0) q.s) (front1 (cellJ q.c q.s i0) q.s) := by
      obtain ⟨g1, _, _, _⟩ := strip_sig hpq hi0
      rcases hq with hq | hq <;> rw [hq] at g1 hcR hcL ⊢ <;> rw [ht] at g1 ⊢ <;> apply conn_lat1_opp
      · have hfar : lat1 (nb c (latA s)) s ∉ F := by
          rw [(frame_opp _ s).1] at g1; exact fun h => by have := g1.1 h; omega
        -- The cell behind the square beside `c` is `q`'s next cell (restricted), or the square is
        -- `q`'s last cell, whose dark front (the square's back side) the start forbids.
        --
        have hBR : ¬ IsCorner t0 (nb (nb c (latA s)) s.opp) := by
          by_cases hl : i0 + 1 < q.n
          · have := (hqR (i0 + 1) hl).2
            rwa [← nb_cellJ, hq, ht] at this
          · exfalso
            obtain ⟨_, _, _, gf⟩ := strip_sig hpq hi0
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
    have hval := suf_valid hpq hcq hev hi0 hsep'
    have hsR : Restr s0 t0 (suf q i0) := restr_suf hqR
    cases L with
    | nil =>
      refine nopath (suf q i0) [] ⟨hval, tgEnd_suf hev hi0 hch, trivial, ?_⟩ ?_
      · intro x hx; rw [List.mem_singleton.1 hx]; exact hsR
      · simp [wt, suf] at hW1 ⊢; omega
    | cons w L3 =>
      obtain ⟨hqe, hlw, hrest⟩ := hch
      have hcr := suf_cr2 hlw hev (by omega)
      have hok' : ChainOK (suf q i0) w := by
        have := hnct.1
        unfold ChainOK at this ⊢
        rw [suf_end (by omega)]; exact this
      refine nopath (suf q i0) (w :: L3) ⟨hval, ⟨by show (q.n - i0) % 2 = 0; omega, hcr, hrest⟩,
        ⟨hok', hnct.2⟩, ?_⟩ ?_
      · intro x hx
        rcases List.mem_cons.1 hx with rfl | hx
        · exact hsR
        · exact hR x (List.mem_cons_of_mem _ hx)
      · rw [wt_cons]; rw [wt_cons] at hW1; simp only [suf]; omega
  rcases touch_outcome_pfD hF hs0 hds hle hTR hk hcell hcor hpat hsep hT' hneut hTs hpq hqR hcq hi hj
      hx1 hx2 with ⟨i', hi', hq⟩ | ⟨i', hi', hq⟩ | ⟨ht, i0, hi0, hev, hq⟩
  · exact (hR1 i' hi' hq).elim
  · exact (hR2 i' hi' hq).elim
  · by_cases h0 : i0 = 0
    · subst h0; rw [hqc0] at hq; exact ⟨ht, hq⟩
    · exact (hR3 ht i0 hi0 hev h0 hq).elim


end source

-- Neighbours commute.
--
lemma nb_nb_comm (z : Pt) (s s' : Side) : nb (nb z s) s' = nb (nb z s') s := by
  obtain ⟨x, y⟩ := z
  cases s <;> cases s' <;> simp only [nb] <;> ring_nf

section gside

variable {V : Finset Pt} {G : Finset Edge} {c : Pt} {d : Side} {k : ℕ} {s0 t0 : Pt}
  (hG : Deg2Off V G s0 t0) (hs0 : s0 ∈ V) (hds : deg G s0 = 1) (hT : NoTypeIIIR V G s0 t0)
  (hk : k % 2 = 0) (hcell : ∀ j ≤ k + 1, IsCell V (cellJ c d j))
  (hcor : ∀ j ≤ k + 1, ¬ IsCorner s0 (cellJ c d j) ∧ ¬ IsCorner t0 (cellJ c d j))
  (hpat : StripPat G c d (k + 2)) (hsep : ¬ Conn G (back1 c d) (front1 c d))
include hG hs0 hds hT hk hcell hcor hpat hsep

-- **Links from `σ` read off `F = G ⊕ σ`** (ULHC `link_of_F`).
--
theorem link_of_F_pf {q : StripSpec} (hq1 : 1 ≤ q.n)
    (hpatF : StripPat (flipCol G c d (k + 2)) q.c q.s q.n)
    (hcq : ∀ j < q.n, IsCell V (cellJ q.c q.s j)) (hso : SideOff ⟨c, d, k + 2⟩ q)
    (hne : ∀ j < q.n, cellJ q.c q.s j ≠ cellJ c d (k + 1))
    (hen : q.n % 2 = 0 → ∀ x ∈ cellE (endCell q), x ∉ cellE (cellJ c d (k + 1)))
    (hm1 : ¬ IsMid c d k (back1 q.c q.s)) (hm2 : ¬ IsMid c d k (front1 q.c q.s))
    (hcg : Conn G (back1 q.c q.s) (front1 q.c q.s))
    (hsepF : ¬ Conn (flipCol G c d (k + 2)) (back1 q.c q.s) (front1 q.c q.s)) :
    CR2 V G ⟨c, d, k + 2⟩ q := by
  have hTe : NotTypeIII V G (cellJ c d (k + 1)) :=
    restr_notT3 hT (hcell (k + 1) le_rfl) (hcor (k + 1) le_rfl)
  have hsame := end_same_loc hTe hk hcell hpat
  obtain ⟨F1, hF1, _, _, _, hodd, _, _⟩ :=
    strip_even_rel_pf k hk G hG hs0 hds hcell hcor hpat hsep hsame
  obtain ⟨m, hm⟩ : ∃ m, q.n = m + 1 := ⟨q.n - 1, by omega⟩
  have hpat' : StripPat (flip G (cellJ c d (k + 1))) q.c q.s q.n := by
    rw [hm] at hpatF ⊢
    refine (stripPat_congr (fun j hj y hy => ?_)).2 hpatF
    exact (flipCol_off G c d (k + 1) (fun i hi => hso j (by omega) i hi y hy)).symm
  refine ⟨by show 2 ≤ k + 2; omega, by show (k + 2) % 2 = 0; omega, hq1, hpat', hcq, hso, hne,
    hen, hm1, hm2, hcg, fun h => hsepF ((hodd _ _ hm1 hm2).2 (Or.inl (hF1 ▸ h)))⟩

end gside

section comp

variable {V : Finset Pt} {G : Finset Edge} {c : Pt} {d : Side} {k : ℕ} {s0 t0 : Pt}
  (hG : Deg2Off V G s0 t0) (hs0 : s0 ∈ V) (hds : deg G s0 = 1) (hleG : ∀ z, deg G z ≤ 2)
  (hT : NoTypeIIIR V G s0 t0) (hk : k % 2 = 0)
  (hcell : ∀ j ≤ k + 1, IsCell V (cellJ c d j))
  (hcor : ∀ j ≤ k + 1, ¬ IsCorner s0 (cellJ c d j) ∧ ¬ IsCorner t0 (cellJ c d j))
  (hpat : StripPat G c d (k + 2)) (hsep : ¬ Conn G (back1 c d) (front1 c d))
  (hneut : ncomp V (flipCol G c d (k + 2)) = ncomp V G)
  (hT' : NoTypeIIIR V (flipCol G c d (k + 2)) s0 t0)
  -- E2: the cells beside the strip's start cell are not Type III in `G`.
  (hE2 : ∀ tf, tf = latA d ∨ tf = latB d → IsCell V (nb c tf) → NotTypeIII V G (nb c tf))
  -- E1: the cells beside the strip's end cell are not Type III after the strip.
  (hE1 : ∀ tf, tf = latA d ∨ tf = latB d → IsCell V (nb (cellJ c d (k + 1)) tf) →
    NotTypeIII V (flipCol G c d (k + 2)) (nb (cellJ c d (k + 1)) tf))
  -- E3: the cells diagonally beyond the strip's end are not Type III after the strip.
  (hE3 : ∀ tf, tf = latA d ∨ tf = latB d → IsCell V (nb (cellJ c d (k + 2)) tf) →
    NotTypeIII V (flipCol G c d (k + 2)) (nb (cellJ c d (k + 2)) tf))
include hG hs0 hds hleG hT hk hcell hcor hpat hsep hneut hT' hE2 hE1 hE3

-- **Completeness step for path-factors, rule Tg** (ULHC `comp_clean`). A minimum restricted Tg
-- path of `F = G ⊕ σ`, for a count-neutral even strip `σ`, gives one of `G`.
--
theorem comp_clean_tg [NearOK V t0] {q : StripSpec} {L : List StripSpec}
    (hP : RPathTg V (flipCol G c d (k + 2)) s0 t0 q L)
    (hmin : ∀ σ L', RPathTg V (flipCol G c d (k + 2)) s0 t0 σ L' → wt q L ≤ wt σ L') :
    ∃ σ L', RPathTg V G s0 t0 σ L' := by
  by_contra hno'
  set F := flipCol G c d (k + 2) with hFdef
  set a : StripSpec := ⟨cellJ c d (k + 1), d.opp, k + 2⟩ with hadef
  have hcellS : ∀ j < k + 2, IsCell V (cellJ c d j) := fun j hj => hcell j (by omega)
  obtain ⟨hFin, hFdeg⟩ := degs_flipCol (k + 2) G hG.1 hpat
    (fun j hj => isCell_mono (hcellS j hj) (sub_insST V s0 t0))
  have hF : Deg2Off V F s0 t0 := ⟨hFin, fun z hz h1 h2 => (hFdeg z).trans (hG.2 z hz h1 h2)⟩
  have hdsF : deg F s0 = 1 := (hFdeg s0).trans hds
  have hleF : ∀ z, deg F z ≤ 2 := fun z => (hFdeg z).symm ▸ hleG z
  have hTe : NotTypeIII V G (cellJ c d (k + 1)) :=
    restr_notT3 hT (hcell (k + 1) le_rfl) (hcor (k + 1) le_rfl)
  have hsameG := end_same_loc hTe hk hcell hpat
  have haF : ValidStrip V F a := ⟨by show 1 ≤ k + 2; omega, rev_pat hk hpat,
    fun i hi => by
      change i < k + 2 at hi
      show IsCell V (cellJ (cellJ c d (k + 1)) d.opp i)
      rw [rev_cellJ c d (by omega)]; exact hcell _ (by omega),
    conn_lat1_opp (end_corners_pf hG hs0 hds hk hcell hcor hpat hsep hsameG hneut).2.2⟩
  have hFa : flipCol F (cellJ c d (k + 1)) d.opp (k + 2) = G := rev_flip G c d k
  have hacell : ∀ j < k + 2, cellJ a.c a.s j = cellJ c d (k + 1 - j) := fun j hj =>
    rev_cellJ c d (show j ≤ k + 1 by omega)
  have hcell' : ∀ j ≤ k + 1, IsCell V (cellJ (cellJ c d (k + 1)) d.opp j) := fun j hj => by
    rw [rev_cellJ c d hj]; exact hcell _ (by omega)
  have hcor' : ∀ j ≤ k + 1, ¬ IsCorner s0 (cellJ (cellJ c d (k + 1)) d.opp j) ∧
      ¬ IsCorner t0 (cellJ (cellJ c d (k + 1)) d.opp j) := fun j hj => by
    rw [rev_cellJ c d hj]; exact hcor _ (by omega)
  have hpat' : StripPat F (cellJ c d (k + 1)) d.opp (k + 2) := haF.2.1
  have hsep' : ¬ Conn F (back1 (cellJ c d (k + 1)) d.opp) (front1 (cellJ c d (k + 1)) d.opp) :=
    haF.2.2.2
  have hTa : NoTypeIIIR V (flipCol F (cellJ c d (k + 1)) d.opp (k + 2)) s0 t0 := by
    rw [hFa]; exact hT
  have hneut' : ncomp V (flipCol F (cellJ c d (k + 1)) d.opp (k + 2)) = ncomp V F := by
    rw [hFa]; exact hneut.symm
  have hlat : ∀ tf, (tf = latA d.opp ∨ tf = latB d.opp) → (tf = latA d ∨ tf = latB d) := by
    intro tf h; rwa [latA_opp, latB_opp] at h
  have hTs' : ∀ tf, (tf = latA d.opp ∨ tf = latB d.opp) → IsCell V (nb (cellJ c d (k + 1)) tf) →
      NotTypeIII V F (nb (cellJ c d (k + 1)) tf) := fun tf h hc => hE1 tf (hlat tf h) hc
  have hend' : cellJ (cellJ c d (k + 1)) d.opp (k + 1) = c := by
    rw [rev_cellJ c d le_rfl, Nat.sub_self, cellJ_zero]
  have hTend' : ∀ tf, (tf = latA d.opp ∨ tf = latB d.opp) →
      IsCell V (nb (cellJ (cellJ c d (k + 1)) d.opp (k + 1)) tf) →
      NotTypeIII V (flipCol F (cellJ c d (k + 1)) d.opp (k + 2))
        (nb (cellJ (cellJ c d (k + 1)) d.opp (k + 1)) tf) := by
    intro tf h hc
    rw [hFa, hend']; rw [hend'] at hc; exact hE2 tf (hlat tf h) hc
  have hTd' : ∀ tf, (tf = latA d.opp ∨ tf = latB d.opp) →
      IsCell V (nb (nb (cellJ c d (k + 1)) tf) d.opp.opp) →
      NotTypeIII V F (nb (nb (cellJ c d (k + 1)) tf) d.opp.opp) := by
    intro tf h hc
    have he : nb (nb (cellJ c d (k + 1)) tf) d.opp.opp = nb (cellJ c d (k + 2)) tf := by
      rw [opp_opp, nb_nb_comm, nb_cellJ]
    rw [he] at hc ⊢
    exact hE3 tf (hlat tf h) hc
  have hno : ¬ ∃ σ L', RPathTg V (flipCol F (cellJ c d (k + 1)) d.opp (k + 2)) s0 t0 σ L' := by
    rw [hFa]; exact hno'
  have hntL := src_notouch_tg hF hs0 hdsF hleF hT' hk hcell' hcor' hpat' hsep' hTa hneut' hTs' hTend' hTd' hmin hP rfl hno
  -- The tail of `Q` is a chain of `G` once `q`'s end keeps off `σ`.
  --
  have hfarQ : (∀ y ∈ cellE (endCell q), ∀ i ≤ k + 1, y ∉ cellE (cellJ c d i)) →
      CRChainTg V G q L := by
    intro hfe
    have hfe' : ∀ j < k + 2, ∀ y ∈ cellE (endCell q), y ∉ cellE (cellJ a.c a.s j) :=
      fun j hj y hy hy' => hfe y hy (k + 1 - j) (by omega) (by rw [← hacell j hj]; exact hy')
    have hfar : FarChainCA F a q L := by
      cases L with
      | nil => trivial
      | cons τ L' =>
        exact farchain_pf hleF hk hcell' hcor' hpat' hsep' (W2 := k + 2 + wt q (τ :: L'))
          (fun w R hP' hnt hfe'' _ => hno (via_path_tg hF hs0 hdsF hleF hT' hk hcell' hcor' hpat' hsep' hTa hneut' _ w R hP' rfl hnt hfe''))
          (τ :: L') q hP.2.1 hP.2.2.1 (endOK_of_valid hP.1) hP.2.2.2 hfe' hntL le_rfl
    have := chain_transfer_pf hF hs0 hdsF hT' hk hcell' hcor' hpat' hsep' hneut' hTa L q hP.1.1
      (endOK_of_valid hP.1) hP.2.1 hP.2.2.1 hP.2.2.2 hfar (fun _ _ j hj y hy => hfe' j (by omega) y hy)
    rwa [hFa] at this
  have hv := hP.1
  have hqR : Restr s0 t0 q := hP.2.2.2 q (List.mem_cons_self ..)
  have hq1 : 1 ≤ q.n := hv.1
  have hq2 := valid_two_pf hv hqR hT'
  have hpqF : StripPat F q.c q.s q.n := hv.2.1
  have hcq := hv.2.2.1
  have hsepF := hv.2.2.2
  have hvs : ValidStrip V G ⟨c, d, k + 2⟩ := ⟨by show 1 ≤ k + 2; omega, hpat, hcellS, hsep⟩
  have hRall : ∀ x ∈ (⟨c, d, k + 2⟩ : StripSpec) :: q :: L, Restr s0 t0 x := by
    intro x hx
    rcases List.mem_cons.1 hx with rfl | hx
    · exact fun j hj => hcor j (by simp only at hj; omega)
    · exact hP.2.2.2 x hx
  by_cases htq : Touches a q
  · obtain ⟨hqs, hqc⟩ := src_touch_tg hF hs0 hdsF hleF hT' hk hcell' hcor' hpat' hsep' hTa hneut' hTs' hTend' hTd' hmin hP rfl hno htq
    simp only [opp_opp, latA_opp, latB_opp] at hqs hqc
    rcases hqc with hqc | hqc
    · -- `q` starts beside the end cell across `latA`.
      --
      have hzq : ∀ j, cellJ q.c q.s j = cellJ (nb (cellJ c d (k + 1)) (latA d)) d j :=
        fun j => by rw [hqs, hqc]
      have hoff1 : ∀ j, 1 ≤ j → ∀ y ∈ cellE (cellJ q.c q.s j), ∀ i ≤ k + 1,
          y ∉ cellE (cellJ c d i) := fun j hj1 y hy => besideE_offA c d k hj1 (by rw [← hzq]; exact hy)
      have hx0 : lat2 q.c q.s = lat1 (cellJ c d (k + 1)) d := by rw [hqs, hqc, side_lat2]
      have hoff0 : ∀ y ∈ cellE q.c, y ≠ lat2 q.c q.s → ∀ i ≤ k + 1, y ∉ cellE (cellJ c d i) :=
        fun y hy hne => besideE_cell0A c d k (by rw [← hqc]; exact hy) (by rw [← hx0]; exact hne)
      obtain ⟨ea1, ea2, _, _⟩ := strip_sig hpat (show k + 1 < k + 2 by omega)
      have elx : lat1 (cellJ c d (k + 1)) d ∈ G := ea1.2 (by omega)
      have fne := frame_ne q.c q.s
      have hsigF := sig_of_pat hpqF
      have hsigG : SigFrom G q.c q.s q.n 1 := by
        intro i hi1 hin
        have hs' : ∀ y ∈ cellE (cellJ q.c q.s i), (y ∈ F ↔ y ∈ G) := fun y hy =>
          mem_flipCol_out (fun i' hi' => hoff1 i hi1 y hy i' (by omega))
        obtain ⟨g1, g2, gb, gf⟩ := hsigF i (Nat.zero_le _) hin
        refine ⟨?_, ?_, ?_, ?_⟩
        · rw [← hs' _ (mem_frame _ q.s (Or.inl rfl))]; exact g1
        · rw [← hs' _ (mem_frame _ q.s (Or.inr (Or.inl rfl)))]; exact g2
        · rw [← hs' _ (mem_frame _ q.s (Or.inr (Or.inr (Or.inl rfl))))]; exact gb
        · rw [← hs' _ (mem_frame _ q.s (Or.inr (Or.inr (Or.inr rfl))))]; exact gf
      have hbG : back q.c q.s ∈ G := by
        have hb := hpqF.1
        rwa [mem_flipCol_out (fun i hi => hoff0 _ (mem_frame _ q.s (Or.inr (Or.inr (Or.inl rfl))))
          fne.2.1 i (by omega))] at hb
      have hfG : front q.c q.s ∉ G := by
        have hf0 := (hsigF 0 (Nat.zero_le _) (by omega)).2.2.2
        rw [cellJ_zero] at hf0
        intro h
        rw [← mem_flipCol_out (F := G) (c := c) (s := d) (n := k + 2) (fun i hi => hoff0 _ (mem_frame _ q.s (Or.inr (Or.inr (Or.inr rfl))))
          fne.2.2.2.1 i (by omega))] at h
        have := (hf0.1 h).2 (by omega); omega
      have hcg : Conn G (back1 q.c q.s) (front1 q.c q.s) :=
        chain_conn_loc hq1 hsigG (fun _ => hcq 1 (by omega))
          (fun _ => hT _ (hcq 1 (by omega)) (hqR 1 (by omega)).1 (hqR 1 (by omega)).2) hbG
          ⟨fun h => absurd h hfG, fun h => by omega⟩ (Or.inr (by rw [hx0]; exact elx))
      have hlink := link_of_F_pf hG hs0 hds hT hk hcell hcor hpat hsep hq1 hpqF hcq
        (fun j hj i hi y hy => by
          have hi' : i + 1 < k + 2 := hi
          rw [hzq, cellJ_nb_comm, cellJ_add] at hy
          exact besideA_not_mem c d (j := 0) (show i < k + 1 + j by omega)
            (by rw [cellJ_zero]; exact hy))
        (fun j _ => by rw [hzq]; exact besideA_ne c d (k + 1) j (k + 1))
        (fun _ y hy => beside_end_farA c d k (show 2 ≤ q.n by omega)
          (by unfold endCell at hy; rw [hzq] at hy; exact hy) (k + 1) (by omega))
        (by rw [hqs, hqc]; exact (besideA_not_mid c d k (Or.inl rfl)).1)
        (by rw [hqs, hqc]; exact (besideA_not_mid c d k (Or.inl rfl)).2) hcg hsepF
      have hok : ChainOK ⟨c, d, k + 2⟩ q := by
        intro j hj y hy hye
        rw [endCell_mk] at hye ⊢
        rcases Nat.eq_zero_or_pos j with rfl | hj1
        · rw [cellJ_zero] at hy
          exact ⟨rfl, Or.inl (by rw [shared_unique hqc hye hy, lat1_eq])⟩
        · exact absurd hye (hoff1 j hj1 y hy (k + 1) le_rfl)
      have hchG := hfarQ (fun y hy i hi =>
        hoff1 (q.n - 1) (by omega) y (by unfold endCell at hy; exact hy) i hi)
      exact hno' ⟨_, q :: L, ⟨hvs, ⟨by show (k + 2) % 2 = 0; omega, hlink, hchG⟩, ⟨hok, hP.2.2.1⟩,
        hRall⟩⟩
    · -- `q` starts beside the end cell across `latB`.
      --
      have hzq : ∀ j, cellJ q.c q.s j = cellJ (nb (cellJ c d (k + 1)) (latB d)) d j :=
        fun j => by rw [hqs, hqc]
      have hoff1 : ∀ j, 1 ≤ j → ∀ y ∈ cellE (cellJ q.c q.s j), ∀ i ≤ k + 1,
          y ∉ cellE (cellJ c d i) := fun j hj1 y hy => besideE_offB c d k hj1 (by rw [← hzq]; exact hy)
      have hx0 : lat1 q.c q.s = lat2 (cellJ c d (k + 1)) d := by rw [hqs, hqc, side2_lat1]
      have hoff0 : ∀ y ∈ cellE q.c, y ≠ lat1 q.c q.s → ∀ i ≤ k + 1, y ∉ cellE (cellJ c d i) :=
        fun y hy hne => besideE_cell0B c d k (by rw [← hqc]; exact hy) (by rw [← hx0]; exact hne)
      obtain ⟨ea1, ea2, _, _⟩ := strip_sig hpat (show k + 1 < k + 2 by omega)
      have elx : lat2 (cellJ c d (k + 1)) d ∈ G := ea2.2 (by omega)
      have fne := frame_ne q.c q.s
      have hsigF := sig_of_pat hpqF
      have hsigG : SigFrom G q.c q.s q.n 1 := by
        intro i hi1 hin
        have hs' : ∀ y ∈ cellE (cellJ q.c q.s i), (y ∈ F ↔ y ∈ G) := fun y hy =>
          mem_flipCol_out (fun i' hi' => hoff1 i hi1 y hy i' (by omega))
        obtain ⟨g1, g2, gb, gf⟩ := hsigF i (Nat.zero_le _) hin
        refine ⟨?_, ?_, ?_, ?_⟩
        · rw [← hs' _ (mem_frame _ q.s (Or.inl rfl))]; exact g1
        · rw [← hs' _ (mem_frame _ q.s (Or.inr (Or.inl rfl)))]; exact g2
        · rw [← hs' _ (mem_frame _ q.s (Or.inr (Or.inr (Or.inl rfl))))]; exact gb
        · rw [← hs' _ (mem_frame _ q.s (Or.inr (Or.inr (Or.inr rfl))))]; exact gf
      have hbG : back q.c q.s ∈ G := by
        have hb := hpqF.1
        rwa [mem_flipCol_out (fun i hi => hoff0 _ (mem_frame _ q.s (Or.inr (Or.inr (Or.inl rfl))))
          fne.1 i (by omega))] at hb
      have hfG : front q.c q.s ∉ G := by
        have hf0 := (hsigF 0 (Nat.zero_le _) (by omega)).2.2.2
        rw [cellJ_zero] at hf0
        intro h
        rw [← mem_flipCol_out (F := G) (c := c) (s := d) (n := k + 2) (fun i hi => hoff0 _ (mem_frame _ q.s (Or.inr (Or.inr (Or.inr rfl))))
          fne.2.2.1 i (by omega))] at h
        have := (hf0.1 h).2 (by omega); omega
      have hcg : Conn G (back1 q.c q.s) (front1 q.c q.s) :=
        chain_conn_loc hq1 hsigG (fun _ => hcq 1 (by omega))
          (fun _ => hT _ (hcq 1 (by omega)) (hqR 1 (by omega)).1 (hqR 1 (by omega)).2) hbG
          ⟨fun h => absurd h hfG, fun h => by omega⟩ (Or.inl (by rw [hx0]; exact elx))
      have hlink := link_of_F_pf hG hs0 hds hT hk hcell hcor hpat hsep hq1 hpqF hcq
        (fun j hj i hi y hy => by
          have hi' : i + 1 < k + 2 := hi
          rw [hzq, cellJ_nb_comm, cellJ_add] at hy
          exact besideB_not_mem c d (j := 0) (show i < k + 1 + j by omega)
            (by rw [cellJ_zero]; exact hy))
        (fun j _ => by rw [hzq]; exact besideB_ne c d (k + 1) j (k + 1))
        (fun _ y hy => beside_end_farB c d k (show 2 ≤ q.n by omega)
          (by unfold endCell at hy; rw [hzq] at hy; exact hy) (k + 1) (by omega))
        (by rw [hqs, hqc]; exact (besideB_not_mid c d k (Or.inl rfl)).1)
        (by rw [hqs, hqc]; exact (besideB_not_mid c d k (Or.inl rfl)).2) hcg hsepF
      have hok : ChainOK ⟨c, d, k + 2⟩ q := by
        intro j hj y hy hye
        rw [endCell_mk] at hye ⊢
        rcases Nat.eq_zero_or_pos j with rfl | hj1
        · rw [cellJ_zero] at hy
          exact ⟨rfl, Or.inr (by rw [shared_unique hqc hye hy, lat2_eq])⟩
        · exact absurd hye (hoff1 j hj1 y hy (k + 1) le_rfl)
      have hchG := hfarQ (fun y hy i hi =>
        hoff1 (q.n - 1) (by omega) y (by unfold endCell at hy; exact hy) i hi)
      exact hno' ⟨_, q :: L, ⟨hvs, ⟨by show (k + 2) % 2 = 0; omega, hlink, hchG⟩, ⟨hok, hP.2.2.1⟩,
        hRall⟩⟩
  · -- `q` keeps off `s`.
    --
    have hoff : ∀ j < q.n, ∀ y ∈ cellE (cellJ q.c q.s j), ∀ i ≤ k + 1,
        y ∉ cellE (cellJ c d i) := by
      intro j hj y hy i hi hyi
      exact htq ⟨j, hj, k + 1 - i, by show k + 1 - i < k + 2; omega, y, hy, by
        rw [hacell _ (by omega), show k + 1 - (k + 1 - i) = i by omega]; exact hyi⟩
    have hsame : ∀ j < q.n, ∀ y ∈ cellE (cellJ q.c q.s j), (y ∈ F ↔ y ∈ G) := fun j hj y hy =>
      mem_flipCol_out (fun i hi => hoff j hj y hy i (by omega))
    have hpqG : StripPat G q.c q.s q.n := by
      obtain ⟨m, hm⟩ : ∃ m, q.n = m + 1 := ⟨q.n - 1, by omega⟩
      rw [hm] at hpqF hsame ⊢
      exact (stripPat_congr hsame).1 hpqF
    have hchG := hfarQ (fun y hy i hi =>
      hoff (q.n - 1) (by omega) y (by unfold endCell at hy; exact hy) i hi)
    by_cases hcg : Conn G (back1 q.c q.s) (front1 q.c q.s)
    · have hmid : ∀ p, (∃ j < q.n, ∃ x ∈ G, (x.p = p ∨ x.q = p) ∧ x ∈ cellE (cellJ q.c q.s j)) →
          ¬ IsMid c d k p := by
        rintro p ⟨j, hj, x, hx, hxp, hxw⟩ hm
        obtain ⟨i, hi, hxi⟩ := mid_touch_L hleG hpat hm hx hxp
        exact hoff j hj x hxw i (by omega) hxi
      obtain ⟨⟨hb, hbp, hb0⟩, jf, hjf, xf, hxf, hxfp, hxfw⟩ := start_corner_edges hpqG hq1
      have hlink := link_of_F_pf hG hs0 hds hT hk hcell hcor hpat hsep hq1 hpqF hcq
        (fun j hj i hi y hy => by
          have hi' : i + 1 < k + 2 := hi
          exact hoff j hj y hy i (by omega))
        (fun j hj h => hoff j hj _ (by rw [h]; exact mem_frame _ d (Or.inr (Or.inr (Or.inl rfl))))
          (k + 1) le_rfl (mem_frame _ d (Or.inr (Or.inr (Or.inl rfl)))))
        (fun _ y hy => hoff (q.n - 1) (by omega) y (by unfold endCell at hy; exact hy) (k + 1) le_rfl)
        (hmid _ ⟨0, by omega, _, hb, hbp, hb0⟩) (hmid _ ⟨jf, hjf, xf, hxf, hxfp, hxfw⟩) hcg hsepF
      have hok : ChainOK ⟨c, d, k + 2⟩ q := chainOK_of_noChain (fun j hj y hy hye =>
        hoff j hj y hy (k + 1) le_rfl (by rwa [endCell_mk] at hye))
      exact hno' ⟨_, q :: L, ⟨hvs, ⟨by show (k + 2) % 2 = 0; omega, hlink, hchG⟩, ⟨hok, hP.2.2.1⟩,
        hRall⟩⟩
    · exact hno' ⟨q, L, ⟨⟨hq1, hpqG, hcq, hcg⟩, hchG, hP.2.2.1, hP.2.2.2⟩⟩

end comp

end HP

end ULHC
