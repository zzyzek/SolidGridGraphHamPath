/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
import ULHC.NearCA
import ULHC.LinkGraph
import ULHC.AlgComplete

/-!
# Completeness of the path search

`G` is a clean 2-factor with at least two components of a solid Hamiltonian `V`. Then `G` has
a CA path (`CRPathCA`). Induction on `μ`: the strip `s` that lowers `μ` (`one_strip`) is odd
(a path by itself), or even with a Type III cell after it (`t3_link`), or even with a clean
`F = G ⊕ s`. In the last case a minimum CA path `Q` of `F` gives a path of `G`, with
`a = rev s` (`F ⊕ a = G`):
* `via_path`: a path `a :: w :: R` of `F` whose tail keeps off `a` gives a path of `G`, by
  induction on its weight (no minimality needed).
-/

namespace ULHC

open Finset

-- A proper single-cell strip is a Type III cell, so clean factors have none.
--
lemma valid_two {V : Finset Pt} {G : Finset Edge} {q : StripSpec} (hv : ValidStrip V G q)
    (hT : NoTypeIII V G) : 2 ≤ q.n := by
  by_contra hn
  obtain ⟨h1, hp, hc, hsep⟩ := hv
  have h1' : q.n = 1 := by omega
  have hc0 : IsCell V q.c := by have := hc 0 (by omega); rwa [cellJ_zero] at this
  obtain ⟨g1, g2, gb, gf⟩ := strip_sig hp (show 0 < q.n by omega)
  rw [cellJ_zero] at g1 g2 gb gf
  exact hsep (hT q.c hc0 q.s (gb.2 rfl) (gf.2 ⟨fun h => by omega, fun h => by omega⟩)
    (fun h => by have := g1.1 h; omega) (fun h => by have := g2.1 h; omega))

lemma endOK_of_valid {V : Finset Pt} {G : Finset Edge} {q : StripSpec} (hv : ValidStrip V G q) :
    EndOK V G q := by
  intro hev
  obtain ⟨h1, hp, hc, _⟩ := hv
  obtain ⟨l1, l2, b, f⟩ := end_alt (show 2 ≤ q.n by omega) hev hp
  exact ⟨endCell_isCell h1 hc, l1, l2, b, f⟩

section via

variable {V : Finset Pt} {G : Finset Edge} {a : StripSpec}
  (hs : Solid V) (x0 : Pt) (hconn : ∀ z ∈ V, Conn (GE V) x0 z)
  (hG : Deg2 V G) (hT : NoTypeIII V G) (ha : ValidStrip V G a) (hae : a.n % 2 = 0)
  (ha2 : 2 ≤ a.n) (hT' : NoTypeIII V (applyS G a))
include hs x0 hconn hG hT ha hae ha2 hT'

-- **Shortcut paths.** A path of `G` through `a` whose tail keeps off `a` gives a path of
-- `G ⊕ a`: its links are far from `a` (`farchain_CA`), unless a later strip is created by
-- `a`'s end, which gives a lighter path of the same kind.
--
omit hs x0 hconn in
theorem via_path : ∀ (n : ℕ) (w : StripSpec) (R : List StripSpec), CRPathCA V G a (w :: R) →
    wt a (w :: R) = n → (∀ x ∈ R, ¬ Touches a x) →
    (R ≠ [] → ∀ j < a.n, ∀ y ∈ cellE (endCell w), y ∉ cellE (cellJ a.c a.s j)) →
    ∃ σ L, CRPathCA V (applyS G a) σ L := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro w R hP hwt hnt hfe
  by_contra hno
  have hvia : ViaFree V G a n := fun w' R' hP' hnt' hfe' hlt =>
    hno (ih _ hlt w' R' hP' rfl hnt' hfe')
  obtain ⟨⟨_, hch⟩, hcat⟩ := hP
  have hfar : FarChainCA G a w R := by
    cases R with
    | nil => trivial
    | cons τ R' =>
      exact farchain_CA hG ha hae ha2
        hvia (τ :: R') w hch.2.2 hcat.2 (endOK_of_link hch.2.1) (hfe (by simp)) hnt
        (by rw [← hwt, wt_cons a])
  exact hno ⟨w, R, (progress_step_CA hG hT ha hae ha2 hT' hch hcat hfar).1⟩

-- A strip `w` keeping off `a` and created by `a`'s end, followed by a tail keeping off `a`,
-- gives a path of `G ⊕ a`.
--
omit hs x0 hconn in
theorem via_head {q w : StripSpec} {L3 : List StripSpec} (hch : CRChain V G q (w :: L3))
    (hcat : CATail (q :: w :: L3)) (hntL : ∀ τ ∈ w :: L3, ¬ Touches a τ)
    (hpw : StripPat G w.c w.s w.n)
    (hsplit : ¬ Conn (flip G (endCell a)) (back1 w.c w.s) (front1 w.c w.s)) :
    ∃ σ L, CRPathCA V (applyS G a) σ L := by
  have hlw := hch.2.1
  have hnt := hntL w (List.mem_cons_self ..)
  have hw1 : 1 ≤ w.n := hlw.2.2.1
  have hlink : CR2 V G a w := link_a hG ha hae ha2 hw1 hpw hlw.2.2.2.2.1 hnt
    hlw.2.2.2.2.2.2.2.2.2.2.1 hsplit
  refine via_path hG hT ha hae ha2 hT' _ w L3
    ⟨⟨ha, hae, hlink, hch.2.2⟩, chainOK_of_noChain (fun jw hjw y hy hye => hnt ⟨jw, hjw,
      a.n - 1, by omega, y, hy, by unfold endCell at hye; exact hye⟩), hcat.2⟩ rfl
    (fun x hx => hntL x (List.mem_cons_of_mem _ hx))
    (fun _ j hj y hy hy' => hnt ⟨w.n - 1, by omega, j, hj, y, by unfold endCell at hy; exact hy,
      hy'⟩)

end via

section source

variable {V : Finset Pt} {G : Finset Edge} {a : StripSpec}
  (hs : Solid V) (x0 : Pt) (hconn : ∀ z ∈ V, Conn (GE V) x0 z)
  (hG : Deg2 V G) (hT : NoTypeIII V G) (ha : ValidStrip V G a) (hae : a.n % 2 = 0)
  (ha2 : 2 ≤ a.n) (hT' : NoTypeIII V (applyS G a))
  {W : ℕ} (hmin : ∀ σ L', CRPathCA V G σ L' → W ≤ wt σ L')
include hs x0 hconn hG hT ha hae ha2 hT' hmin

-- In a minimum path, when `G ⊕ a` has no path, the strips after the first keep off `a`.
--
theorem src_notouch {q : StripSpec} {L : List StripSpec} (hP : CRPathCA V G q L)
    (hWq : W = wt q L) (hno : ¬ ∃ σ L', CRPathCA V (applyS G a) σ L') : ∀ τ ∈ L, ¬ Touches a τ :=
  notouch_CA hs x0 hconn hG hT ha hae ha2 hT' hmin (W2 := a.n + wt q L)
    (fun w R hP' hnt hfe _ => hno (via_path hG hT ha hae ha2 hT' _ w R hP' rfl hnt hfe))
    L q hP.1.2 hP.2 (endOK_of_valid hP.1.1) (le_of_eq hWq.symm) le_rfl

-- **The first strip.** In a minimum path, when `G ⊕ a` has no path, a first strip touching `a`
-- starts beside `a`'s start cell and runs against `a`.
--
theorem src_touch {q : StripSpec} {L : List StripSpec} (hP : CRPathCA V G q L)
    (hWq : W = wt q L) (hno : ¬ ∃ σ L', CRPathCA V (applyS G a) σ L') (htq : Touches a q) :
    q.s = a.s.opp ∧ (q.c = nb a.c (latA a.s) ∨ q.c = nb a.c (latB a.s)) := by
  obtain ⟨i, hi, j, hj, x, hx1, hx2⟩ := htq
  have hntL := src_notouch hs x0 hconn hG hT ha hae ha2 hT' hmin hP hWq hno
  have nopath : ∀ σ' L', CRPathCA V G σ' L' → wt σ' L' < W → False :=
    fun σ' L' h hlt => by have := hmin σ' L' h; omega
  have hW1 : wt q L ≤ W := le_of_eq hWq.symm
  obtain ⟨⟨hv, hchq⟩, hcat⟩ := hP
  have hpq : StripPat G q.c q.s q.n := hv.2.1
  have hcq : ∀ j < q.n, IsCell V (cellJ q.c q.s j) := hv.2.2.1
  have hq2 := valid_two hv hT
  obtain ⟨k, hk⟩ : ∃ k, a.n = k + 2 := ⟨a.n - 2, by omega⟩
  have hk2 : k % 2 = 0 := by omega
  have ha' := ha
  obtain ⟨_, hpa, hca, hsep⟩ := ha'
  rw [hk] at hpa hca hj
  have hcell : ∀ j ≤ k + 1, IsCell V (cellJ a.c a.s j) := fun j hj => hca j (by omega)
  have hT'' : NoTypeIII V (flipCol G a.c a.s (k + 2)) := by unfold applyS at hT'; rwa [hk] at hT'
  have hendA : endCell a = cellJ a.c a.s (k + 1) := by unfold endCell; rw [hk]; rfl
  set e := cellJ a.c a.s (k + 1) with he_def
  have via_a : ∀ w L3, L = w :: L3 → StripPat G w.c w.s w.n →
      ¬ Conn (flip G e) (back1 w.c w.s) (front1 w.c w.s) → False := by
    intro w L3 hL hpw hsplit
    subst hL
    exact hno (via_head hG hT ha hae ha2 hT' hchq hcat hntL hpw
      (by rw [hendA]; exact hsplit))
  have hqc0 : cellJ q.c q.s 0 = q.c := cellJ_zero q.c q.s
  obtain ⟨ea1, ea2, eab, eaf⟩ := strip_sig hpa (show k + 1 < k + 2 by omega)
  have el1 : lat1 e a.s ∈ G := ea1.2 (by omega)
  have el2 : lat2 e a.s ∈ G := ea2.2 (by omega)
  have eb : back e a.s ∉ G := fun h => by have := eab.1 h; omega
  have ef : front e a.s ∉ G := fun h => by have := (eaf.1 h).1 (by omega); omega
  have hce : IsCell V e := hcell (k + 1) le_rfl
  have hc0 : IsCell V a.c := by have := hcell 0 (by omega); rwa [cellJ_zero] at this
  -- **Through the end cell.**
  --
  have hR1 : ∀ i' < q.n, cellJ q.c q.s i' = e → False := by
    intro i' hi' hq
    obtain ⟨hend, hdir⟩ := touch_end hk2 hpa (sig_of_pat hpq) (Nat.zero_le _) hi' hq
    have hendq : endCell q = e := by
      unfold endCell; rw [← hq, show q.n - 1 = i' by omega]
    rcases hdir with ⟨_, hodd⟩ | ⟨hperp, hev⟩
    · cases L with
      | nil => have : q.n % 2 = 1 := hchq; omega
      | cons w L3 =>
        have hlw := hchq.2.1
        have hnt := hntL w (List.mem_cons_self ..)
        have hpw : StripPat G w.c w.s w.n := by
          have h := hlw.2.2.2.1
          rw [hendq] at h
          exact (pat_flip_off hlw.2.2.1 (fun jw hjw y hy hy' =>
            hnt ⟨jw, hjw, k + 1, by omega, y, hy, hy'⟩)).1 h
        have hsplit := hlw.2.2.2.2.2.2.2.2.2.2.2
        rw [hendq] at hsplit
        exact via_a w L3 rfl hpw hsplit
    · by_cases hi0 : i' = 0
      · omega
      · have hp := cell_prev (z := q.c) (tf := q.s) (i := i') (by omega)
        rw [hq] at hp
        rcases hperp with ht | ht
        · rw [show q.s.opp = latB a.s by rw [ht, latA_opp_eq]] at hp
          rcases touch_side2_end hG hk2 hcell hpa (sig_of_pat hpq) (i := i' - 1) (Nat.zero_le _) (by omega) hp with
            ⟨ht', _⟩ | ⟨_, hf, hl⟩
          · exact latA_ne_opp a.s (ht.symm.trans ht')
          · exact beside_end2 hG hT hk2 hcell hpa hsep
              ((outer2_body hG hcell hpa le_rfl).2 hk2) hf hl hT''
        · rw [show q.s.opp = latA a.s by rw [ht, latB_opp_eq]] at hp
          rcases touch_side1_end hG hk2 hcell hpa (sig_of_pat hpq) (i := i' - 1) (Nat.zero_le _) (by omega) hp with
            ⟨ht', _⟩ | ⟨_, hf, hl⟩
          · exact latB_ne_opp a.s (ht.symm.trans ht')
          · exact beside_end1 hG hT hk2 hcell hpa hsep
              ((outer1_body hG hcell hpa le_rfl).2 hk2) hf hl hT''
  -- **Through the cell beyond the end cell.**
  --
  have hR2 : ∀ i' < q.n, cellJ q.c q.s i' = nb e a.s → False := by
    intro i' hi' hq
    rcases touch_beyond hG hk2 hcell hpa (sig_of_pat hpq) (Nat.zero_le _) hi' (fun _ _ => Nat.zero_le _) (fun _ => Nat.zero_le _) hq with ⟨ht, hodd, hend⟩ | ⟨ht, _, hi1⟩ |
      ⟨hperp, h0⟩
    · have hendq : endCell q = nb e a.s := by
        unfold endCell; rw [← hq, show q.n - 1 = i' by omega]
      cases L with
      | nil => have : q.n % 2 = 1 := hchq; omega
      | cons w L3 =>
        have hlw := hchq.2.1
        have hnt := hntL w (List.mem_cons_self ..)
        have hsplit := hlw.2.2.2.2.2.2.2.2.2.2.2
        rw [hendq] at hsplit
        obtain ⟨g1, g2, gb, _⟩ := strip_sig hpq hi'
        rw [hq, ht] at g1 g2 gb
        rw [(frame_opp (nb e a.s) a.s).1] at g1
        rw [(frame_opp (nb e a.s) a.s).2.1] at g2
        rw [(frame_opp (nb e a.s) a.s).2.2.1] at gb
        have ul1 := g1.2 hodd
        have ul2 := g2.2 hodd
        have hncw : NoChain q w := by
          intro jw hjw y hy hyu
          obtain ⟨rfl, hyl⟩ := hcat.1 jw hjw y hy hyu
          rw [hendq] at hyu hyl
          obtain ⟨i1, hi1, j1, hj1, x1, h1, h2⟩ := e1_chain hG hk2 hcell hpa hlw (hcat.1) hendq ht ul1 ul2 hy hyu hyl
          exact hnt ⟨i1, hi1, j1, by rw [hk]; exact hj1, x1, h1, h2⟩
        have hpw : StripPat G w.c w.s w.n := (pat_flip_off hlw.2.2.1 hncw).1 hlw.2.2.2.1
        have uf : front (nb e a.s) a.s ∉ G := fun h => by have := gb.1 h; omega
        have hcu' : IsCell V (nb e a.s) := by rw [← hq]; exact hcq i' hi'
        have hcorner : ∀ y ∈ G, ∀ jw < w.n, y ∈ cellE (cellJ w.c w.s jw) → ∀ r,
            (y.p = r ∨ y.q = r) → r ≠ front1 e a.s ∧ r ≠ front2 e a.s := by
          intro y hy jw hjw hyw r hr
          have touchy : y ∈ cellE e → False := fun h => hnt ⟨jw, hjw, k + 1, by omega, y, hyw, h⟩
          have chainy : y ∈ cellE (nb e a.s) → False := fun h =>
            hncw jw hjw y hyw (by rw [hendq]; exact h)
          constructor
          · rintro rfl
            have i2 := (ends_lat1 (nb e a.s) a.s).inc_iff (front1 e a.s) |>.2
              (Or.inl (back1_nb e a.s).symm)
            have hne2 : lat1 e a.s ≠ lat1 (nb e a.s) a.s := (ends_lat1 e a.s).ne_at
              (by have := ends_lat1 (nb e a.s) a.s; rwa [back1_nb] at this)
              (back1_ne_front1_nb e a.s)
            rcases two_at (hG.2 _ (corners4 hce a.s).2.2.1) el1 ul1
              ((ends_lat1 e a.s).inc_iff _ |>.2 (Or.inr rfl)) i2 hne2 hy hr with h | h
            · exact touchy (by rw [h, cellE_frame e a.s]; simp)
            · exact chainy (by rw [h, cellE_frame (nb e a.s) a.s]; simp)
          · rintro rfl
            have i2 := (ends_lat2 (nb e a.s) a.s).inc_iff (front2 e a.s) |>.2
              (Or.inl (back2_nb e a.s).symm)
            have hne2 : lat2 e a.s ≠ lat2 (nb e a.s) a.s := (ends_lat2 e a.s).ne_at
              (by have := ends_lat2 (nb e a.s) a.s; rwa [back2_nb] at this)
              (back2_ne_front2_nb e a.s)
            rcases two_at (hG.2 _ (corners4 hce a.s).2.2.2) el2 ul2
              ((ends_lat2 e a.s).inc_iff _ |>.2 (Or.inr rfl)) i2 hne2 hy hr with h | h
            · exact touchy (by rw [h, cellE_frame e a.s]; simp)
            · exact chainy (by rw [h, cellE_frame (nb e a.s) a.s]; simp)
        have hw1 : 1 ≤ w.n := hlw.2.2.1
        obtain ⟨⟨hb, hbp, hb0⟩, jf, hjf, xf, hxf, hxfp, hxfw⟩ := start_corner_edges hpw hw1
        have cb := hcorner _ hb 0 (by omega) hb0 _ hbp
        have cf := hcorner _ hxf jf hjf hxfw _ hxfp
        have hss := stacked_split hG hce hcu' el1 el2 eb ef ul1 ul2 uf cb.1 cb.2 cf.1 cf.2
        exact via_a w L3 rfl hpw (fun h => hsplit (hss.1 h))
    · exact hR1 (i' + 1) hi1 (by rw [← nb_cellJ, hq, ht, nb_nb_opp])
    · subst h0
      rw [hqc0] at hq
      by_cases hm : 2 ≤ q.n
      · exact beyond_cross hG hT hk2 hcell hpa hsep hT'' hpq hperp hq hm
      · omega
  -- **Beside the start cell**: the suffix from there is a lighter path.
  --
  have hR3 : q.s = a.s.opp → ∀ i0 < q.n, i0 % 2 = 0 → i0 ≠ 0 →
      (cellJ q.c q.s i0 = nb a.c (latA a.s) ∨ cellJ q.c q.s i0 = nb a.c (latB a.s)) → False := by
    intro ht i0 hi0 hev hi00 hq
    have hsep' : ¬ Conn G (back1 (cellJ q.c q.s i0) q.s) (front1 (cellJ q.c q.s i0) q.s) := by
      obtain ⟨g1, _, _, _⟩ := strip_sig hpq hi0
      rcases hq with hq | hq <;> rw [hq] at g1 ⊢ <;> rw [ht] at g1 ⊢ <;> apply conn_lat1_opp
      · have hfar : lat1 (nb a.c (latA a.s)) a.s ∉ G := by
          rw [(frame_opp _ a.s).1] at g1; exact fun h => by have := g1.1 h; omega
        exact start_side_sep hG hT hpa (by omega) hc0 hsep hfar
      · rw [side2_back1, side2_front1]
        exact fun h => hsep ((((ends_back a.c a.s).conn hpa.1).trans h).trans
          (front_join hG hT hpa (by omega) hc0).symm)
    have hval := suf_valid hpq hcq hev hi0 hsep'
    cases L with
    | nil =>
      have hodd : q.n % 2 = 1 := hchq
      refine nopath (suf q i0) [] ⟨⟨hval, ?_⟩, trivial⟩ ?_
      · show (q.n - i0) % 2 = 1; omega
      · simp [wt, suf] at hW1 ⊢; omega
    | cons w L3 =>
      obtain ⟨hqe, hlw, hrest⟩ := hchq
      have hcr := suf_cr2 hlw hev (by omega)
      have hok' : ChainOK (suf q i0) w := by
        have := hcat.1
        unfold ChainOK at this ⊢
        rw [suf_end (by omega)]; exact this
      refine nopath (suf q i0) (w :: L3) ⟨⟨hval, ⟨by show (q.n - i0) % 2 = 0; omega, hcr, hrest⟩⟩,
        ⟨hok', hcat.2⟩⟩ ?_
      rw [wt_cons]; rw [wt_cons] at hW1; simp only [suf]; omega
  rcases touch_outcome hG hT hk2 hcell hpa hsep hT'' hpq hi hj hx1 hx2 with
    ⟨i', hi', hq⟩ | ⟨i', hi', hq⟩ | ⟨ht, i0, hi0, hev, hq⟩
  · exact (hR1 i' hi' hq).elim
  · exact (hR2 i' hi' hq).elim
  · by_cases h0 : i0 = 0
    · subst h0; rw [hqc0] at hq; exact ⟨ht, hq⟩
    · exact (hR3 ht i0 hi0 hev h0 hq).elim

end source


-- Cells of a strip starting beside the end cell `e = c_{k+1}` and running along `d`: after the
-- first, they share no side with the strip; the first shares only the side toward `e`.
--
lemma besideE_offA (c : Pt) (d : Side) (k : ℕ) {j : ℕ} (hj : 1 ≤ j) {y : Edge}
    (hy : y ∈ cellE (cellJ (nb (cellJ c d (k + 1)) (latA d)) d j)) :
    ∀ i ≤ k + 1, y ∉ cellE (cellJ c d i) := by
  intro i hi
  rw [cellJ_nb_comm, cellJ_add] at hy
  exact besideA_not_mem c d (j := 0) (show i < k + 1 + j by omega) (by rw [cellJ_zero]; exact hy)

lemma besideE_offB (c : Pt) (d : Side) (k : ℕ) {j : ℕ} (hj : 1 ≤ j) {y : Edge}
    (hy : y ∈ cellE (cellJ (nb (cellJ c d (k + 1)) (latB d)) d j)) :
    ∀ i ≤ k + 1, y ∉ cellE (cellJ c d i) := by
  intro i hi
  rw [cellJ_nb_comm, cellJ_add] at hy
  exact besideB_not_mem c d (j := 0) (show i < k + 1 + j by omega) (by rw [cellJ_zero]; exact hy)

lemma besideE_cell0A (c : Pt) (d : Side) (k : ℕ) {y : Edge}
    (hy : y ∈ cellE (nb (cellJ c d (k + 1)) (latA d))) (hne : y ≠ lat1 (cellJ c d (k + 1)) d) :
    ∀ i ≤ k + 1, y ∉ cellE (cellJ c d i) := by
  intro i hi hyi
  by_cases hik : i ≤ k
  · exact besideA_not_mem c d (j := 0) (show i < k + 1 by omega) (by rw [cellJ_zero]; exact hy) hyi
  · obtain rfl : i = k + 1 := by omega
    exact hne ((shared_unique rfl hyi hy).trans (lat1_eq _ _).symm)

lemma besideE_cell0B (c : Pt) (d : Side) (k : ℕ) {y : Edge}
    (hy : y ∈ cellE (nb (cellJ c d (k + 1)) (latB d))) (hne : y ≠ lat2 (cellJ c d (k + 1)) d) :
    ∀ i ≤ k + 1, y ∉ cellE (cellJ c d i) := by
  intro i hi hyi
  by_cases hik : i ≤ k
  · exact besideB_not_mem c d (j := 0) (show i < k + 1 by omega) (by rw [cellJ_zero]; exact hy) hyi
  · obtain rfl : i = k + 1 := by omega
    exact hne ((shared_unique rfl hyi hy).trans (lat2_eq _ _).symm)

lemma mem_frame (z : Pt) (tf : Side) {y : Edge}
    (hy : y = lat1 z tf ∨ y = lat2 z tf ∨ y = back z tf ∨ y = front z tf) : y ∈ cellE z := by
  rw [cellE_frame z tf]; rcases hy with rfl | rfl | rfl | rfl <;> simp

section gside

variable {V : Finset Pt} {G : Finset Edge} {c : Pt} {d : Side} {k : ℕ}
  (hG : Deg2 V G) (hT : NoTypeIII V G) (hk : k % 2 = 0)
  (hcell : ∀ j ≤ k + 1, IsCell V (cellJ c d j)) (hpat : StripPat G c d (k + 2))
  (hsep : ¬ Conn G (back1 c d) (front1 c d))
include hG hT hk hcell hpat hsep

-- **Links from `s` read off `F = G ⊕ s`.** A strip of `F` keeping off `s` before its end cell,
-- whose start pair is joined in `G` and split in `F`, is a link from `s`: away from the body,
-- `F` agrees with `G ⊕ e_s`, and a pair split in `F` is split by `e_s` (`strip_even_rel`).
--
theorem link_of_F {q : StripSpec} (hq1 : 1 ≤ q.n)
    (hpatF : StripPat (flipCol G c d (k + 2)) q.c q.s q.n)
    (hcq : ∀ j < q.n, IsCell V (cellJ q.c q.s j)) (hso : SideOff ⟨c, d, k + 2⟩ q)
    (hne : ∀ j < q.n, cellJ q.c q.s j ≠ cellJ c d (k + 1))
    (hen : q.n % 2 = 0 → ∀ x ∈ cellE (endCell q), x ∉ cellE (cellJ c d (k + 1)))
    (hm1 : ¬ IsMid c d k (back1 q.c q.s)) (hm2 : ¬ IsMid c d k (front1 q.c q.s))
    (hcg : Conn G (back1 q.c q.s) (front1 q.c q.s))
    (hsepF : ¬ Conn (flipCol G c d (k + 2)) (back1 q.c q.s) (front1 q.c q.s)) :
    CR2 V G ⟨c, d, k + 2⟩ q := by
  obtain ⟨F1, hF1, _, _, _, _, hodd⟩ :=
    strip_even_rel k hk G hG hcell hpat hsep (end_same hT hk hcell hpat)
  obtain ⟨m, hm⟩ : ∃ m, q.n = m + 1 := ⟨q.n - 1, by omega⟩
  have hpat' : StripPat (flip G (cellJ c d (k + 1))) q.c q.s q.n := by
    rw [hm] at hpatF ⊢
    refine (stripPat_congr (fun j hj y hy => ?_)).2 hpatF
    exact (flipCol_off G c d (k + 1) (fun i hi => hso j (by omega) i hi y hy)).symm
  refine ⟨by show 2 ≤ k + 2; omega, by show (k + 2) % 2 = 0; omega, hq1, hpat', hcq, hso, hne,
    hen, hm1, hm2, hcg, fun h => hsepF ((hodd _ _ hm1 hm2).2 (Or.inl (hF1 ▸ h)))⟩

end gside


section comp

variable {V : Finset Pt} {G : Finset Edge} {c : Pt} {d : Side} {k : ℕ}
  (hs : Solid V) (x0 : Pt) (hconn : ∀ z ∈ V, Conn (GE V) x0 z)
  (hG : Deg2 V G) (hT : NoTypeIII V G) (hk : k % 2 = 0)
  (hcell : ∀ j ≤ k + 1, IsCell V (cellJ c d j)) (hpat : StripPat G c d (k + 2))
  (hsep : ¬ Conn G (back1 c d) (front1 c d)) (hT' : NoTypeIII V (flipCol G c d (k + 2)))
include hs x0 hconn hG hT hk hcell hpat hsep hT'

-- **Completeness step, clean case.** A minimum CA path of `F = G ⊕ s` gives a CA path of `G`.
--
theorem comp_clean {q : StripSpec} {L : List StripSpec}
    (hP : CRPathCA V (flipCol G c d (k + 2)) q L)
    (hmin : ∀ σ L', CRPathCA V (flipCol G c d (k + 2)) σ L' → wt q L ≤ wt σ L') :
    ∃ σ L', CRPathCA V G σ L' := by
  by_contra hno'
  set F := flipCol G c d (k + 2) with hFdef
  set a : StripSpec := ⟨cellJ c d (k + 1), d.opp, k + 2⟩ with hadef
  have hcellS : ∀ j < k + 2, IsCell V (cellJ c d j) := fun j hj => hcell j (by omega)
  have hF : Deg2 V F := deg2_flipCol (k + 2) G hG hpat hcellS
  have haF : ValidStrip V F a := rev_valid hG hT hk hcell hpat hsep 
  have hFa : applyS F a = G := rev_flip G c d k
  have hTa : NoTypeIII V (applyS F a) := by rw [hFa]; exact hT
  have hae : a.n % 2 = 0 := by show (k + 2) % 2 = 0; omega
  have ha2 : 2 ≤ a.n := by show 2 ≤ k + 2; omega
  have hno : ¬ ∃ σ L', CRPathCA V (applyS F a) σ L' := by rw [hFa]; exact hno'
  have hacell : ∀ j < k + 2, cellJ a.c a.s j = cellJ c d (k + 1 - j) := fun j hj =>
    rev_cellJ c d (show j ≤ k + 1 by omega)
  have hntL := src_notouch hs x0 hconn hF hT' haF hae ha2 hTa hmin hP rfl hno
  -- The tail of `Q` is a chain of `G` once `q`'s end keeps off `s`.
  --
  have hfarQ : (L ≠ [] → ∀ y ∈ cellE (endCell q), ∀ i ≤ k + 1, y ∉ cellE (cellJ c d i)) →
      CRChain V G q L := by
    intro hfe
    have hfar : FarChainCA F a q L := by
      cases L with
      | nil => trivial
      | cons τ L' =>
        exact farchain_CA hF haF hae ha2 (W2 := a.n + wt q (τ :: L'))
          (fun w R hP' hnt hfe' _ =>
            hno (via_path hF hT' haF hae ha2 hTa _ w R hP' rfl hnt hfe'))
          (τ :: L') q hP.1.2 hP.2 (endOK_of_valid hP.1.1)
          (fun j hj y hy hy' => hfe (by simp) y hy (k + 1 - j) (by omega)
            (by rw [← hacell j hj]; exact hy'))
          hntL le_rfl
    have := chain_transfer_CA hF hT' haF hae ha2 hTa L q (endOK_of_valid hP.1.1) hP.1.2 hP.2 hfar
    rwa [hFa] at this
  have hv := hP.1.1
  have hq1 : 1 ≤ q.n := hv.1
  have hq2 := valid_two hv hT'
  have hpqF : StripPat F q.c q.s q.n := hv.2.1
  have hcq := hv.2.2.1
  have hsepF := hv.2.2.2
  have hvs : ValidStrip V G ⟨c, d, k + 2⟩ := ⟨by show 1 ≤ k + 2; omega, hpat, hcellS, hsep⟩
  by_cases htq : Touches a q
  · obtain ⟨hqs, hqc⟩ := src_touch hs x0 hconn hF hT' haF hae ha2 hTa hmin hP rfl hno htq
    simp only [hadef, opp_opp, latA_opp, latB_opp] at hqs hqc
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
        chain_conn hG hT hq1 hsigG (fun _ => hcq 1 (by omega)) hbG
          ⟨fun h => absurd h hfG, fun h => by omega⟩ (Or.inr (by rw [hx0]; exact elx))
      have hlink := link_of_F hG hT hk hcell hpat hsep hq1 hpqF hcq
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
      have hchG := hfarQ (fun _ y hy i hi =>
        hoff1 (q.n - 1) (by omega) y (by unfold endCell at hy; exact hy) i hi)
      exact hno' ⟨_, q :: L, ⟨⟨hvs, by show (k + 2) % 2 = 0; omega, hlink, hchG⟩, hok, hP.2⟩⟩
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
        chain_conn hG hT hq1 hsigG (fun _ => hcq 1 (by omega)) hbG
          ⟨fun h => absurd h hfG, fun h => by omega⟩ (Or.inl (by rw [hx0]; exact elx))
      have hlink := link_of_F hG hT hk hcell hpat hsep hq1 hpqF hcq
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
      have hchG := hfarQ (fun _ y hy i hi =>
        hoff1 (q.n - 1) (by omega) y (by unfold endCell at hy; exact hy) i hi)
      exact hno' ⟨_, q :: L, ⟨⟨hvs, by show (k + 2) % 2 = 0; omega, hlink, hchG⟩, hok, hP.2⟩⟩
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
    have hchG := hfarQ (fun _ y hy i hi =>
      hoff (q.n - 1) (by omega) y (by unfold endCell at hy; exact hy) i hi)
    by_cases hcg : Conn G (back1 q.c q.s) (front1 q.c q.s)
    · have hmid : ∀ p, (∃ j < q.n, ∃ x ∈ G, (x.p = p ∨ x.q = p) ∧ x ∈ cellE (cellJ q.c q.s j)) →
          ¬ IsMid c d k p := by
        rintro p ⟨j, hj, x, hx, hxp, hxw⟩ hm
        obtain ⟨i, hi, hxi⟩ := mid_touch hG hpat hcell hm hx hxp
        exact hoff j hj x hxw i (by omega) hxi
      obtain ⟨⟨hb, hbp, hb0⟩, jf, hjf, xf, hxf, hxfp, hxfw⟩ := start_corner_edges hpqG hq1
      have hlink := link_of_F hG hT hk hcell hpat hsep hq1 hpqF hcq
        (fun j hj i hi y hy => by
          have hi' : i + 1 < k + 2 := hi
          exact hoff j hj y hy i (by omega))
        (fun j hj h => hoff j hj _ (by rw [h]; exact mem_frame _ d (Or.inr (Or.inr (Or.inl rfl))))
          (k + 1) le_rfl (mem_frame _ d (Or.inr (Or.inr (Or.inl rfl)))))
        (fun _ y hy => hoff (q.n - 1) (by omega) y (by unfold endCell at hy; exact hy) (k + 1) le_rfl)
        (hmid _ ⟨0, by omega, _, hb, hbp, hb0⟩) (hmid _ ⟨jf, hjf, xf, hxf, hxfp, hxfw⟩) hcg hsepF
      have hok : ChainOK ⟨c, d, k + 2⟩ q := chainOK_of_noChain (fun j hj y hy hye =>
        hoff j hj y hy (k + 1) le_rfl (by rwa [endCell_mk] at hye))
      exact hno' ⟨_, q :: L, ⟨⟨hvs, by show (k + 2) % 2 = 0; omega, hlink, hchG⟩, hok, hP.2⟩⟩
    · exact hno' ⟨q, L, ⟨⟨⟨hq1, hpqG, hcq, hcg⟩, hchG⟩, hP.2⟩⟩

end comp


/-- **Completeness of the path search.** In a solid grid graph with a Hamiltonian cycle, every
clean 2-factor with at least two components has a CA path. -/
theorem pathComplete {V : Finset Pt} {H : Finset Edge} (hs : Solid V) (hH : Deg2 V H)
    (hHam : ncomp V H = 1) : PathComplete V := by
  suffices h : ∀ m (G : Finset Edge), mu V G H = m → Deg2 V G → NoTypeIII V G → 2 ≤ ncomp V G →
      ∃ σ L, CRPathCA V G σ L from fun G hG hT h2 => h _ G rfl hG hT h2
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro G hm hG hT h2
  obtain ⟨x0, hx0, _, _, _⟩ := exists_not_conn h2
  have hconn : ∀ z ∈ V, Conn (GE V) x0 z := fun z hz =>
    (conn_of_ncomp_one hHam hx0 hz).mono (fun e he => mem_GE.2 (hH.1 e he))
  obtain ⟨σ, hv, hn, hmu⟩ := one_strip hs hH hHam hG hT h2
  rcases Nat.mod_two_eq_zero_or_one σ.n with hev | hodd
  swap
  · exact ⟨σ, [], ⟨hv, hodd⟩, trivial⟩
  obtain ⟨c, d, n⟩ := σ
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by simp only at hn; omega⟩
  have hk : k % 2 = 0 := by simp only at hev; omega
  obtain ⟨_, hpat, hcellS, hsep⟩ := hv
  have hcell : ∀ j ≤ k + 1, IsCell V (cellJ c d j) := fun j hj => hcellS j (by simp only; omega)
  by_cases hT' : NoTypeIII V (flipCol G c d (k + 2))
  · have hF : Deg2 V (flipCol G c d (k + 2)) := deg2_flipCol (k + 2) G hG hpat hcellS
    have hcnt := even_strip_count hG hT ⟨by simp only; omega, hpat, hcellS, hsep⟩ hev
    change ncomp V (flipCol G c d (k + 2)) = ncomp V G at hcnt
    change mu V (flipCol G c d (k + 2)) H + 2 * (k + 2) = mu V G H at hmu
    have hex := ih _ (by omega) _ rfl hF hT' (by omega)
    classical
    have hP : ∃ w, ∃ σ' L', CRPathCA V (flipCol G c d (k + 2)) σ' L' ∧ wt σ' L' = w := by
      obtain ⟨σ', L', h⟩ := hex; exact ⟨_, σ', L', h, rfl⟩
    obtain ⟨q, L, hQ, hw⟩ := Nat.find_spec hP
    exact comp_clean hs x0 hconn hG hT hk hcell hpat hsep hT' hQ (fun σ' L' h' => by
      rw [hw]; exact Nat.find_min' hP ⟨σ', L', h', rfl⟩)
  · obtain ⟨τ, hτ1, hl, hok⟩ := t3_link hG hT hk hcell hpat hsep hT'
    exact ⟨_, [τ], ⟨⟨by simp only; omega, hpat, hcellS, hsep⟩, hev, hl, show τ.n % 2 = 1 by rw [hτ1]⟩, hok, trivial⟩

/-- **Umans–Lenhart.** For a solid grid graph `V`, the algorithm `ulhc` answers `true` exactly
when `V` has a Hamiltonian cycle (a 2-factor with one component). -/
theorem ulhc_correct {V : Finset Pt} (hs : Solid V) :
    ulhc V = true ↔ ∃ H, Deg2 V H ∧ ncomp V H = 1 := by
  constructor
  · exact ulhc_sound
  · rintro ⟨H, hH, hHam⟩
    exact ulhc_complete hs hH hHam (pathComplete hs hH hHam)

end ULHC
