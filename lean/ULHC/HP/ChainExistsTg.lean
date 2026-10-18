/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
import ULHC.HP.CompCleanTg
import ULHC.HP.T3LinkPF
import ULHC.HP.ZeroPF
import ULHC.HP.TheoremAT2
import ULHC.HP.CompW

/-!
# Restricted Tg chains exist, and are paths of the algorithm's graph

* `rpath_to_ppath`: a restricted Tg chain of `G` is a path of the graph searched by `findChainPF`
  (nodes `pnodes`, end test `ptgt` with rule Tg).
* `rpath_exists`: every reached state without a Type III cell to flip and with two components or
  more has a restricted Tg chain, by induction on `μ` around `comp_clean_tg`, from two named
  hypotheses (the choice lemma and a restricted `t3_link`).
-/

namespace ULHC

namespace HP

open Finset Classical

lemma cornerB_eq_true_iff {z c : Pt} : cornerB z c = true ↔ IsCorner z c := by
  unfold cornerB IsCorner
  simp only [Bool.or_eq_true, beq_iff_eq]
  constructor
  · rintro (((h | h) | h) | h) <;> simp [← h]
  · rintro (h | h | h | h) <;> simp [h]

lemma avoidB_iff {s t : Pt} {σ : StripSpec} : avoidB s t σ = true ↔ Restr s t σ := by
  unfold avoidB Restr
  simp only [List.all_eq_true, List.mem_range, Bool.and_eq_true, Bool.not_eq_true']
  constructor
  · intro h j hj
    obtain ⟨h1, h2⟩ := h j hj
    exact ⟨fun hc => by rw [cornerB_eq_true_iff.2 hc] at h1; simp at h1,
      fun hc => by rw [cornerB_eq_true_iff.2 hc] at h2; simp at h2⟩
  · intro h j hj
    obtain ⟨h1, h2⟩ := h j hj
    exact ⟨Bool.eq_false_iff.2 (fun hc => h1 (cornerB_eq_true_iff.1 hc)),
      Bool.eq_false_iff.2 (fun hc => h2 (cornerB_eq_true_iff.1 hc))⟩

lemma twistB_iff {V W : Finset Pt} {G : Finset Edge} {u : Pt} (hGV : Inside W G)
    (hW : W.card ≤ V.card + 1) (hVW : V ⊆ W) (hu : IsCell V u) :
    twistB V G u = true ↔ TwistsIn V G u := by
  unfold twistB TwistsIn
  rw [Bool.and_eq_true, altB_iff, beq_iff_eq, cncomp_eqW (inside_flip hGV (isCell_mono hu hVW)) hW hVW,
    cncomp_eqW hGV hW hVW]

section count

variable {V : Finset Pt} {G : Finset Edge} {s t : Pt}

-- **A Tg ending by itself lowers the count**: an odd strip merges; an even strip whose end cell
-- twists merges at its end (`strip_even_rel_pf`).
--
theorem tgEnd_count (hG : Deg2Off V G s t) (hs0 : s ∈ V) (hds : deg G s = 1) {σ : StripSpec}
    (hv : ValidStrip V G σ) (hR : Restr s t σ) (htg : TgEnd V G σ) :
    ncomp V (applyS G σ) + 1 = ncomp V G := by
  obtain ⟨c, d, n⟩ := σ
  obtain ⟨h1, hpat, hcellS, hsep⟩ := hv
  simp only at h1 hpat hcellS hsep
  have hst := conn_st hG hs0 hds
  rcases htg with hodd | ⟨hev, htw⟩
  · change n % 2 = 1 at hodd
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    exact (strip_odd_pf k (by omega) G hG hst (fun j hj => hcellS j (by omega))
      (fun j hj => hR j (by simp only; omega)) hpat hsep).1
  · change n % 2 = 0 at hev
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
    have hk : k % 2 = 0 := by omega
    have hcell : ∀ j ≤ k + 1, IsCell V (cellJ c d j) := fun j hj => hcellS j (by omega)
    have hcor : ∀ j ≤ k + 1, ¬ IsCorner s (cellJ c d j) ∧ ¬ IsCorner t (cellJ c d j) :=
      fun j hj => hR j (by simp only; omega)
    obtain ⟨el1, el2, eb, ef⟩ := end_frame_pf hk hpat
    have htw2 : ncomp V (flip G (cellJ c d (k + 1))) = ncomp V G := htw.2
    have hsame : Conn G (back1 (cellJ c d (k + 1)) d) (back2 (cellJ c d (k + 1)) d) := by
      by_contra hn
      have := (lat_count hG hst (hcell (k + 1) le_rfl) el1 el2 eb ef).2 hn
      omega
    obtain ⟨F1, hF1, _, _, _, _, hcnt, _⟩ :=
      strip_even_rel_pf k hk G hG hs0 hds hcell hcor hpat hsep hsame
    rw [hF1, htw2] at hcnt
    exact hcnt

-- A Tg ending by itself lowers the measure.
--
theorem tgEnd_lowers (hG : Deg2Off V G s t) (hs0 : s ∈ V) (hds : deg G s = 1) {σ : StripSpec}
    (hv : ValidStrip V G σ) (hR : Restr s t σ) (htg : TgEnd V G σ) :
    Mc V (applyS G σ) s t < Mc V G s t := by
  have hcnt := tgEnd_count hG hs0 hds hv hR htg
  have hin : Inside (insert s (insert t V)) (applyS G σ) := (degs_flipCol σ.n G hG.1 hv.2.1
    (fun j hj => isCell_mono (hv.2.2.1 j hj) (sub_insST V s t))).1
  unfold Mc
  rw [cncomp_eqW hin (card_insST hs0) (sub_insST V s t), cncomp_eqW hG.1 (card_insST hs0) (sub_insST V s t)]
  split_ifs <;> omega

end count

section bridge

variable {V : Finset Pt} {G : Finset Edge} {s t : Pt}

def mk3 (w : StripSpec) : PNode := ⟨w, 3, w⟩

lemma chain_cand_tg : ∀ (L : List StripSpec) (b : StripSpec), 1 ≤ b.n →
    (∀ j < b.n, IsCell V (cellJ b.c b.s j)) → CRChainTg V G b L → ∀ c ∈ L, c ∈ cand V G
  | [], _, _, _, _, c, hc => by simp at hc
  | τ :: L, b, h1, hb, hch, c, hc => by
    obtain ⟨_, hl, hrest⟩ := hch
    obtain ⟨hτ1, hτc⟩ := link_cells hl
    rcases List.mem_cons.1 hc with rfl | hc
    · exact cand_of_link h1 hb hl
    · exact chain_cand_tg L τ hτ1 hτc hrest c hc

-- A Tg chain from a node at position 2 or 3 is a tail of the graph.
--
theorem tail_tg {W : Finset Pt} (hGV : Inside W G) (hW : W.card ≤ V.card + 1) (hVW : V ⊆ W) : ∀ (L : List StripSpec) (x : PNode), (x.pos = 2 ∨ x.pos = 3) →
    1 ≤ x.σ.n → (∀ j < x.σ.n, IsCell V (cellJ x.σ.c x.σ.s j)) → CRChainTg V G x.σ L →
    CATail (x.σ :: L) → MP.IsTail pmid (ptgt V G s t) (pedge V G) x (L.map mk3) := by
  intro L
  induction L with
  | nil =>
    intro x hpos h1 hc hch _
    have htg : tgB V G x = true := by
      unfold tgB
      rcases (hch : TgEnd V G x.σ) with h | ⟨h, htw⟩
      · simp [h]
      · simp only [h, Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, true_and]
        right
        exact (twistB_iff hGV hW hVW (endCell_isCell h1 hc)).2 htw
    show ptgt V G s t x = true
    rcases hpos with h | h <;> simp [ptgt, h, htg]
  | cons w L ih =>
    intro x hpos h1 hc hch hcat
    obtain ⟨hev, hl, hrest⟩ := hch
    obtain ⟨hw1, hwc⟩ := link_cells hl
    rw [List.map_cons, MP.isTail_cons]
    refine ⟨by simp [pmid, hev], ?_, ih (mk3 w) (Or.inr rfl) hw1 hwc hrest hcat.2⟩
    have hp : min (x.pos + 1) 3 = 3 := by omega
    simp only [pedge, mk3, hp, (cr2B_iffW hGV hW hVW (endCell_isCell h1 hc)).2 hl, chainOKB_iff.2 hcat.1]
    simp

-- **A restricted Tg chain is a path of the algorithm's graph.**
--
theorem rpath_to_ppath (hG : Deg2Off V G s t) (hs0 : s ∈ V) (hds : deg G s = 1)
    {σ : StripSpec} {L : List StripSpec} (h : RPathTg V G s t σ L) :
    ∃ p : List PNode, MP.IsPath (psrc V G) pmid (ptgt V G s t) (pedge V G) p ∧
      (∀ x ∈ p, x ∈ pnodes V G s t) ∧ MP.pw pw p = wt σ L := by
  obtain ⟨hv, hch, hcat, hR⟩ := h
  have hGV := hG.1
  have hW := card_insST (t := t) hs0
  have hVW := sub_insST V s t
  obtain ⟨h1, hc⟩ := valid_cells hv
  have hσR : Restr s t σ := hR σ (List.mem_cons_self ..)
  have hσc : σ ∈ candR V G s t := Finset.mem_filter.2 ⟨cand_of_valid hv, avoidB_iff.2 hσR⟩
  have hsrc : psrc V G ⟨σ, 1, σ⟩ = true := by
    simp [psrc, (validB_iffW hGV hW hVW).2 hv]
  have hcand : ∀ w ∈ L, w ∈ candR V G s t := fun w hw =>
    Finset.mem_filter.2 ⟨chain_cand_tg L σ h1 hc hch w hw,
      avoidB_iff.2 (hR w (List.mem_cons_of_mem _ hw))⟩
  have hn1 : PNode.mk σ 1 σ ∈ pnodes V G s t :=
    Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_image.2 ⟨σ, hσc, rfl⟩))
  cases L with
  | nil =>
    refine ⟨[⟨σ, 1, σ⟩], ⟨hsrc, ?_⟩, by simpa using hn1, by simp [MP.pw, wt, pw]⟩
    show ptgt V G s t ⟨σ, 1, σ⟩ = true
    simp only [ptgt, beq_self_eq_true, ite_true, decide_eq_true_eq]
    exact tgEnd_lowers hG hs0 hds hv hσR hch
  | cons τ L' =>
    obtain ⟨hev, hl, hrest⟩ := hch
    obtain ⟨hτ1, hτc⟩ := link_cells hl
    refine ⟨⟨σ, 1, σ⟩ :: ⟨τ, 2, σ⟩ :: L'.map mk3, ⟨hsrc, ?_⟩, ?_, ?_⟩
    · rw [MP.isTail_cons]
      refine ⟨by simp [pmid, hev], ?_, tail_tg hGV hW hVW L' ⟨τ, 2, σ⟩ (Or.inl rfl) hτ1 hτc hrest hcat.2⟩
      simp only [pedge, (cr2B_iffW hGV hW hVW (endCell_isCell h1 hc)).2 hl, chainOKB_iff.2 hcat.1]
      simp
    · intro x hx
      simp only [List.mem_cons, List.mem_map] at hx
      rcases hx with rfl | rfl | ⟨w, hw, rfl⟩
      · exact hn1
      · exact Finset.mem_union_right _ (Finset.mem_image.2 ⟨(τ, σ),
          Finset.mem_product.2 ⟨hcand τ (by simp), hσc⟩, rfl⟩)
      · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_image.2
          ⟨w, hcand w (by simp [hw]), rfl⟩))
    · simp [MP.pw, wt, pw, mk3, List.map_map, Function.comp_def]

-- A valid restricted strip that lowers `Mc` is a one-node path of the search.
--
theorem single_ppath (hG : Deg2Off V G s t) (hs0 : s ∈ V) {σ : StripSpec} (hv : ValidStrip V G σ)
    (hσR : Restr s t σ) (hlow : Mc V (applyS G σ) s t < Mc V G s t) :
    ∃ p : List PNode, MP.IsPath (psrc V G) pmid (ptgt V G s t) (pedge V G) p ∧
      ∀ x ∈ p, x ∈ pnodes V G s t := by
  have hGV := hG.1
  have hW := card_insST (t := t) hs0
  have hVW := sub_insST V s t
  have hσc : σ ∈ candR V G s t := Finset.mem_filter.2 ⟨cand_of_valid hv, avoidB_iff.2 hσR⟩
  have hsrc : psrc V G ⟨σ, 1, σ⟩ = true := by
    simp [psrc, (validB_iffW hGV hW hVW).2 hv]
  have hn1 : PNode.mk σ 1 σ ∈ pnodes V G s t :=
    Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_image.2 ⟨σ, hσc, rfl⟩))
  refine ⟨[⟨σ, 1, σ⟩], ⟨hsrc, ?_⟩, by simpa using hn1⟩
  show ptgt V G s t ⟨σ, 1, σ⟩ = true
  simp only [ptgt, beq_self_eq_true, ite_true, decide_eq_true_eq]
  exact hlow

lemma mem_pnodes_cand {G : Finset Edge} {x : PNode} (hx : x ∈ pnodes V G s t) :
    x.σ ∈ cand V G ∧ Restr s t x.σ := by
  unfold pnodes candR at hx
  simp only [Finset.mem_union, Finset.mem_image, Finset.mem_product, Finset.mem_filter] at hx
  rcases hx with (⟨σ, ⟨h1, h⟩, rfl⟩ | ⟨σ, ⟨h1, h⟩, rfl⟩) | ⟨⟨a, b⟩, ⟨⟨h1, h⟩, _⟩, rfl⟩ <;>
    exact ⟨h1, avoidB_iff.1 h⟩

-- A tail of the graph from a node at position 2 or more is a Tg chain.
--
theorem tg_of_tail {W : Finset Pt} (hGV : Inside W G) (hW : W.card ≤ V.card + 1) (hVW : V ⊆ W) : ∀ (L : List PNode) (x : PNode), 2 ≤ x.pos →
    x ∈ pnodes V G s t → (∀ z ∈ L, z ∈ pnodes V G s t) →
    MP.IsTail pmid (ptgt V G s t) (pedge V G) x L →
    CRChainTg V G x.σ (L.map PNode.σ) ∧ CATail (x.σ :: L.map PNode.σ) := by
  intro L
  induction L with
  | nil =>
    intro x hpos hx _ ht
    obtain ⟨h1, hc⟩ := cells_of_cand (mem_pnodes_cand hx).1
    have hne : (x.pos == 1) = false := by simp; omega
    have htg : tgB V G x = true := by
      have := (MP.isTail_nil.1 ht); simpa [ptgt, hne] using this
    refine ⟨?_, trivial⟩
    unfold tgB at htg
    simp only [Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true] at htg
    rcases htg with h | ⟨h, htw⟩
    · exact Or.inl h
    · exact Or.inr ⟨h, (twistB_iff hGV hW hVW (endCell_isCell h1 hc)).1 htw⟩
  | cons y L ih =>
    intro x hpos hx hL ht
    obtain ⟨hm, he, ht'⟩ := MP.isTail_cons.1 ht
    obtain ⟨h1, hc⟩ := cells_of_cand (mem_pnodes_cand hx).1
    simp only [pedge, Bool.and_eq_true, beq_iff_eq] at he
    obtain ⟨⟨⟨hypos, hcr⟩, hok⟩, _⟩ := he
    have hy : 2 ≤ y.pos := by omega
    obtain ⟨ih1, ih2⟩ := ih y hy (hL y (List.mem_cons_self ..)) (fun z hz => hL z (List.mem_cons_of_mem _ hz)) ht'
    refine ⟨⟨by simpa [pmid] using hm, (cr2B_iffW hGV hW hVW (endCell_isCell h1 hc)).1 hcr, ih1⟩,
      chainOKB_iff.1 hok, ih2⟩

-- **A path of the graph with two nodes or more is a restricted Tg chain of the same weight.**
--
theorem ppath_to_rpath {W : Finset Pt} (hGV : Inside W G) (hW : W.card ≤ V.card + 1) (hVW : V ⊆ W) {x y : PNode} {rest : List PNode}
    (hp : MP.IsPath (psrc V G) pmid (ptgt V G s t) (pedge V G) (x :: y :: rest))
    (hN : ∀ z ∈ x :: y :: rest, z ∈ pnodes V G s t) :
    RPathTg V G s t x.σ (y.σ :: rest.map PNode.σ) ∧
      MP.pw pw (x :: y :: rest) = wt x.σ (y.σ :: rest.map PNode.σ) := by
  obtain ⟨hsrc, hm, he, ht⟩ := MP.isPath_cons_cons.1 hp
  simp only [psrc, Bool.and_eq_true, beq_iff_eq] at hsrc
  obtain ⟨⟨hpos, _⟩, hval⟩ := hsrc
  have hv := (validB_iffW hGV hW hVW).1 hval
  obtain ⟨h1, hc⟩ := valid_cells hv
  simp only [pedge, Bool.and_eq_true, beq_iff_eq, hpos] at he
  obtain ⟨⟨⟨hypos, hcr⟩, hok⟩, _⟩ := he
  have hy : 2 ≤ y.pos := by omega
  have hyN := hN y (by simp)
  obtain ⟨hch, hcat⟩ := tg_of_tail hGV hW hVW rest y hy hyN (fun z hz => hN z (by simp [hz])) ht
  refine ⟨⟨hv, ⟨by simpa [pmid] using hm, (cr2B_iffW hGV hW hVW (endCell_isCell h1 hc)).1 hcr, hch⟩,
    ⟨chainOKB_iff.1 hok, hcat⟩, ?_⟩, ?_⟩
  · intro z hz
    simp only [List.mem_cons, List.mem_map] at hz
    rcases hz with rfl | rfl | ⟨w, hw, rfl⟩
    · exact (mem_pnodes_cand (hN x (by simp))).2
    · exact (mem_pnodes_cand hyN).2
    · exact (mem_pnodes_cand (hN w (by simp [hw]))).2
  · simp [MP.pw, wt, pw, List.map_map, Function.comp_def]
    rfl

end bridge

section induction

variable {V : Finset Pt} {d : Pt → ℕ} {s t : Pt}

-- No Type III cell for the next round to flip: none away from the endpoints, and none at all
-- when there are two components.
--
def CleanR (V : Finset Pt) (X : Finset Edge) (s t : Pt) : Prop :=
  NoTypeIIIR V X s t ∧ ¬ (ncomp V X = 2 ∧ ∃ c, IsCell V c ∧ ¬ NotTypeIII V X c)

-- The properties of the strip found by the walk (`lemmaB_t2`).
--
def WalkStrip (V : Finset Pt) (G H : Finset Edge) (s t : Pt) (σ : StripSpec) : Prop :=
  ValidStrip V G σ ∧ 2 ≤ σ.n ∧ mu V (applyS G σ) H + 2 * σ.n = mu V G H ∧ Restr s t σ ∧
    ncomp V (applyS G σ) ≤ ncomp V G ∧ ncomp V G ≤ ncomp V (applyS G σ) + 1 ∧
    (σ.n % 2 = 1 → ncomp V (applyS G σ) + 1 = ncomp V G)

-- E1, E2, E3 for a strip `σ` of `G`: the cells beside `σ`'s start (in `G`), beside its end
-- (after `σ`), and diagonally beyond its end (after `σ`) are not Type III.
--
def E2Of (V : Finset Pt) (G : Finset Edge) (σ : StripSpec) : Prop :=
  ∀ tf, tf = latA σ.s ∨ tf = latB σ.s → IsCell V (nb σ.c tf) → NotTypeIII V G (nb σ.c tf)

def EFree (V : Finset Pt) (G : Finset Edge) (σ : StripSpec) : Prop :=
  E2Of V G σ ∧
  (∀ tf, tf = latA σ.s ∨ tf = latB σ.s → IsCell V (nb (endCell σ) tf) →
    NotTypeIII V (applyS G σ) (nb (endCell σ) tf)) ∧
  (∀ tf, tf = latA σ.s ∨ tf = latB σ.s → IsCell V (nb (cellJ σ.c σ.s σ.n) tf) →
    NotTypeIII V (applyS G σ) (nb (cellJ σ.c σ.s σ.n) tf))

-- A walk strip that keeps the count and leaves a restricted Type III cell: it lowers `M` by
-- itself, so the search accepts it as a one-strip chain (Umans–Lenhart progress).
--
def T3Walk (V : Finset Pt) (G H : Finset Edge) (s t : Pt) : Prop :=
  ∃ τ, WalkStrip V G H s t τ ∧ τ.n % 2 = 0 ∧ ncomp V (applyS G τ) = ncomp V G ∧
    ¬ NoTypeIIIR V (applyS G τ) s t

-- No cell has `s` or `t` as a corner (both endpoints dangle off the body of the graph).
--
def Dang (V : Finset Pt) (s t : Pt) : Prop := ∀ c, IsCell V c → ¬ IsCorner s c ∧ ¬ IsCorner t c

lemma noT3_of_dang {V : Finset Pt} {s t : Pt} {F : Finset Edge} (hD : Dang V s t)
    (h : NoTypeIIIR V F s t) : ∀ c, IsCell V c → NotTypeIII V F c :=
  fun c hc => h c hc (hD c hc).1 (hD c hc).2

-- **The open lemmas of the chain-existence induction**, as one hypothesis: H1 (the walk's choice
-- with three components or more), H2a (endpoint Type III cells after a walk strip) and N (one
-- level of the induction when the state after the walk strip has only a Type-III walk strip).
--
structure GapsCE (V : Finset Pt) (d : Pt → ℕ) (s t : Pt) : Prop where
  h1 : ∀ {G H : Finset Edge}, Solid V → IsFactor V d G → IsFactor V d H → ncomp V H = 1 →
    (∀ z, z ≠ s → z ≠ t → d z = 2) → d s = 1 → d t = 1 → s ∈ V → t ∈ V → ZeroAt G H s t →
    CleanR V G s t → 3 ≤ ncomp V G →
    ∃ σ, WalkStrip V G H s t σ ∧ (σ.n % 2 = 1 ∨ ncomp V (applyS G σ) + 1 = ncomp V G ∨
      ¬ NoTypeIIIR V (applyS G σ) s t ∨
      (¬ CleanR V (applyS G σ) s t ∧ NoTypeIIIR V (applyS G σ) s t) ∨
      (CleanR V (applyS G σ) s t ∧ EFree V G σ))
  h2a : ∀ {G H : Finset Edge}, Solid V → IsFactor V d G → IsFactor V d H → ncomp V H = 1 →
    (∀ z, z ≠ s → z ≠ t → d z = 2) → d s = 1 → d t = 1 → s ∈ V → t ∈ V → ZeroAt G H s t →
    CleanR V G s t → 2 ≤ ncomp V G → ∀ {σ : StripSpec}, WalkStrip V G H s t σ →
    σ.n % 2 = 0 → ncomp V (applyS G σ) = ncomp V G → ¬ CleanR V (applyS G σ) s t →
    NoTypeIIIR V (applyS G σ) s t → ∃ L, RPathTg V G s t σ L
  hN : ∀ {G H : Finset Edge}, Solid V → IsFactor V d G → IsFactor V d H → ncomp V H = 1 →
    (∀ z, z ≠ s → z ≠ t → d z = 2) → d s = 1 → d t = 1 → s ∈ V → t ∈ V → ZeroAt G H s t →
    CleanR V G s t → 2 ≤ ncomp V G → ∀ {σ : StripSpec}, WalkStrip V G H s t σ →
    σ.n % 2 = 0 → ncomp V (applyS G σ) = ncomp V G → CleanR V (applyS G σ) s t →
    EFree V G σ → T3Walk V (applyS G σ) H s t → (¬ ∃ q L, RPathTg V (applyS G σ) s t q L) →
    (∃ q L, RPathTg V G s t q L) ∨ T3Walk V G H s t

-- **NEW MATH (H1, three components or more; the choice lemma).** In a reached state without a Type III cell to flip and
-- with two components or more, some walk strip is odd, lowers the count, leaves a restricted
-- Type III cell, leaves only endpoint Type III cells (two components), or leaves a clean state
-- and has no E-configuration. (E2 was dropped 2026-10-13: a Type-III walk strip is progress.)
--
-- (Open; not proved. Its statement is the corresponding field of `GapsCE`.)
--

-- **The choice lemma.** With two components it follows from `lemmaB_t2`: no E-site can be a
-- Type III cell. With three or more it is H1 (`walk_choice3`).
--
theorem walk_choice {G H : Finset Edge} (hs : Solid V) (hG : IsFactor V d G)
    (hH : IsFactor V d H) (hHam : ncomp V H = 1) (hd : ∀ z, z ≠ s → z ≠ t → d z = 2)
    (hds : d s = 1) (hdt : d t = 1) (hsV : s ∈ V) (htV : t ∈ V) (hz : ZeroAt G H s t)
    (hcl : CleanR V G s t) (h2 : 2 ≤ ncomp V G) (hg : GapsCE V d s t) :
    ∃ σ, WalkStrip V G H s t σ ∧ (σ.n % 2 = 1 ∨ ncomp V (applyS G σ) + 1 = ncomp V G ∨
      ¬ NoTypeIIIR V (applyS G σ) s t ∨
      (¬ CleanR V (applyS G σ) s t ∧ NoTypeIIIR V (applyS G σ) s t) ∨
      (CleanR V (applyS G σ) s t ∧ EFree V G σ)) := by
  by_cases h3 : ncomp V G = 2
  swap
  · exact hg.h1 hs hG hH hHam hd hds hdt hsV htV hz hcl (by omega)
  -- Two components: neither `G` nor a clean state after a count-neutral strip has any Type III
  -- cell, so every E-site is free.
  have hnoG : ∀ c, IsCell V c → NotTypeIII V G c := fun c hc => by
    by_contra hn; exact hcl.2 ⟨h3, c, hc, hn⟩
  rcases lemmaB_t2 (SolidFor.of_solid hG hH hs) hG hH hHam hd hds hsV hz hdt htV hcl.1 h2 with
    ⟨σ, hv, hn2, hmu, hR, hc1, hc2, hodd, _⟩ | ⟨_, c, hc, hn⟩
  swap
  · exact absurd (hnoG c hc) hn
  refine ⟨σ, ⟨hv, hn2, hmu, hR, hc1, hc2, hodd⟩, ?_⟩
  rcases Nat.mod_two_eq_zero_or_one σ.n with hev | hodd'
  swap
  · exact Or.inl hodd'
  by_cases hdrop : ncomp V (applyS G σ) + 1 = ncomp V G
  · exact Or.inr (Or.inl hdrop)
  have hneut : ncomp V (applyS G σ) = 2 := by omega
  have hE2 : E2Of V G σ := fun tf _ hc => hnoG _ hc
  by_cases hcl' : CleanR V (applyS G σ) s t
  · have hnoA : ∀ c, IsCell V c → NotTypeIII V (applyS G σ) c := fun c hc => by
      by_contra hn; exact hcl'.2 ⟨hneut, c, hc, hn⟩
    exact Or.inr (Or.inr (Or.inr (Or.inr ⟨hcl', hE2, fun tf _ hc => hnoA _ hc,
      fun tf _ hc => hnoA _ hc⟩)))
  · by_cases hR' : NoTypeIIIR V (applyS G σ) s t
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hcl', hR'⟩)))
    · exact Or.inr (Or.inr (Or.inl hR'))

-- **NEW MATH (H2a).** A count-neutral even walk strip after which the only Type III cells are
-- endpoint cells (two components) starts a restricted Tg chain. (Tested: 20/20; the second strip
-- is an ordinary strip, not a one-cell link.)
--
-- (Open; not proved. Its statement is the corresponding field of `GapsCE`.)
--

-- The H2b condition for a strip `σ` of `G`: some restricted Type III cell after `σ` is not the
-- cell beyond `σ`'s end, or one of the two cells beside the end cell is restricted. (Stated as a
-- lemma before 2026-10-13; it is false: notes, H2b counterexample. It is now a case split.)
--
def H2bCond (V : Finset Pt) (G : Finset Edge) (s t : Pt) (σ : StripSpec) : Prop :=
  ∃ c tf, IsCell V c ∧ (¬ IsCorner s c ∧ ¬ IsCorner t c) ∧ back c tf ∈ applyS G σ ∧
    front c tf ∈ applyS G σ ∧ lat1 c tf ∉ applyS G σ ∧ lat2 c tf ∉ applyS G σ ∧
    ¬ Conn (applyS G σ) (back1 c tf) (front1 c tf) ∧
    (c = nb (endCell σ) σ.s →
      (IsCell V (nb (endCell σ) (latA σ.s)) →
        ¬ IsCorner s (nb (endCell σ) (latA σ.s)) ∧ ¬ IsCorner t (nb (endCell σ) (latA σ.s))) ∨
      (IsCell V (nb (endCell σ) (latB σ.s)) →
        ¬ IsCorner s (nb (endCell σ) (latB σ.s)) ∧ ¬ IsCorner t (nb (endCell σ) (latB σ.s))))

-- **Restricted `t3_link`**, from `t3_link_pf`, E2 and H2b.
--
theorem t3_link_tg {G H : Finset Edge} (_hs : Solid V) (hG : IsFactor V d G)
    (_hH : IsFactor V d H) (_hHam : ncomp V H = 1) (hd : ∀ z, z ≠ s → z ≠ t → d z = 2)
    (hds : d s = 1) (hdt : d t = 1) (hsV : s ∈ V) (htV : t ∈ V) (_hz : ZeroAt G H s t)
    (hcl : CleanR V G s t) (_h2 : 2 ≤ ncomp V G) {σ : StripSpec} (hw : WalkStrip V G H s t σ)
    (hev : σ.n % 2 = 0) (hneut : ncomp V (applyS G σ) = ncomp V G)
    (hE2 : E2Of V G σ) (hch : H2bCond V G s t σ) :
    ∃ τ, RPathTg V G s t σ [τ] := by
  obtain ⟨c1, tf, hc1, hc1R, hb, hf, hl1, hl2, hn, hLR⟩ := hch
  obtain ⟨hv, hn2, _, hR, _, _, _⟩ := hw
  have hD : Deg2Off V G s t :=
    ⟨InsideST.of_inside (Inside.of_factor hG), fun z hz hzs hzt => by rw [hG.2 z hz]; exact hd z hzs hzt⟩
  have hdsG : deg G s = 1 := by rw [hG.2 s hsV]; exact hds
  have hleG : ∀ z, deg G z ≤ 2 := by
    intro z
    by_cases hzV : z ∈ V
    · rw [hG.2 z hzV]
      by_cases h1 : z = s
      · rw [h1, hds]; omega
      by_cases h1' : z = t
      · rw [h1', hdt]; omega
      rw [hd z h1 h1']
    · rw [deg_zero_of_inside (Inside.of_factor hG) hzV]; omega
  have hv0 := hv
  obtain ⟨c0, sd, n⟩ := σ
  obtain ⟨_, hpat, hcellS, hsep⟩ := hv
  change n % 2 = 0 at hev
  change 2 ≤ n at hn2
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
  have hk : k % 2 = 0 := by omega
  have hcell : ∀ j ≤ k + 1, IsCell V (cellJ c0 sd j) := fun j hj => hcellS j (by simp only; omega)
  have hcor : ∀ j ≤ k + 1, ¬ IsCorner s (cellJ c0 sd j) ∧ ¬ IsCorner t (cellJ c0 sd j) :=
    fun j hj => hR j (by simp only; omega)
  obtain ⟨τ, hτ1, hl, hok, hτR⟩ := t3_link_pf hD hsV hdsG hleG hcl.1 hk hcell hcor hpat hsep hneut
    hE2 hc1 hc1R hb hf hl1 hl2 hn
    (by rw [Finset.insert_eq_of_mem (Finset.mem_insert_of_mem hsV),
      Finset.insert_eq_of_mem htV]; exact hLR)
  refine ⟨τ, hv0, ⟨by show (k + 2) % 2 = 0; omega, hl, Or.inl (by rw [hτ1])⟩, ⟨hok, trivial⟩, ?_⟩
  intro x hx
  rcases List.mem_cons.1 hx with rfl | hx
  · exact hR
  · rw [List.mem_singleton.1 hx]; exact hτR

-- An even restricted strip that lowers the count twists at its end cell.
--
lemma drop_twists {G : Finset Edge} (hD : Deg2Off V G s t) (hs0 : s ∈ V) (hds : deg G s = 1)
    (hT : NoTypeIIIR V G s t) {σ : StripSpec} (hv : ValidStrip V G σ) (hR : Restr s t σ)
    (hev : σ.n % 2 = 0) (hdrop : ncomp V (applyS G σ) + 1 = ncomp V G) :
    TwistsIn V G (endCell σ) := by
  obtain ⟨c, sd, n⟩ := σ
  obtain ⟨h1, hpat, hcellS, hsep⟩ := hv
  change n % 2 = 0 at hev
  change 1 ≤ n at h1
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
  have hk : k % 2 = 0 := by omega
  have hcell : ∀ j ≤ k + 1, IsCell V (cellJ c sd j) := fun j hj => hcellS j (by simp only; omega)
  have hcor : ∀ j ≤ k + 1, ¬ IsCorner s (cellJ c sd j) ∧ ¬ IsCorner t (cellJ c sd j) :=
    fun j hj => hR j (by simp only; omega)
  obtain ⟨el1, el2, eb, ef⟩ := end_frame_pf hk hpat
  have hsame := end_same_loc (restr_notT3 hT (hcell (k + 1) le_rfl) (hcor (k + 1) le_rfl)) hk
    hcell hpat
  obtain ⟨F1, hF1, _, _, _, _, hcnt, _⟩ :=
    strip_even_rel_pf k hk G hD hs0 hds hcell hcor hpat hsep hsame
  refine ⟨alt_of_lats el1 el2 eb ef, ?_⟩
  change ncomp V (flip G (cellJ c sd (k + 1))) = ncomp V G
  rw [← hF1]
  change ncomp V (flipCol G c sd (k + 2)) + 1 = ncomp V G at hdrop
  omega

-- **NEW MATH (N, 2026-10-13; replaces the false H2b).** One level of the induction: `σ` a walk
-- strip of `G` that keeps the count and leaves a clean state with the E-sites free, and the state
-- after `σ` has no restricted Tg chain but has a Type-III walk strip. Then `G` has a restricted Tg
-- chain or a Type-III walk strip of its own.
--
-- (Open; not proved. Its statement is the corresponding field of `GapsCE`.)
--

-- **Proved: the open lemmas hold when no cell has `s` or `t` as a corner.** A clean state then
-- has no Type III cell at all, as in Umans–Lenhart, so every E-site is free, H2a's case cannot
-- arise, and a Type-III walk strip always gives a Tg chain through `t3_link`.
--
theorem gapsCE_dang (hD : Dang V s t) : GapsCE V d s t := by
  refine ⟨?_, ?_, ?_⟩
  · intro G H hs hG hH hHam hd hds hdt hsV htV hz hcl h3
    have hnoG := noT3_of_dang hD hcl.1
    rcases lemmaB_t2 (SolidFor.of_solid hG hH hs) hG hH hHam hd hds hsV hz hdt htV hcl.1 (by omega) with
      ⟨σ, hv, hn2, hmu, hR, hc1, hc2, hodd, _⟩ | ⟨_, c, hc, hn⟩
    swap
    · exact absurd (hnoG c hc) hn
    refine ⟨σ, ⟨hv, hn2, hmu, hR, hc1, hc2, hodd⟩, ?_⟩
    rcases Nat.mod_two_eq_zero_or_one σ.n with hev | hodd'
    swap
    · exact Or.inl hodd'
    by_cases hdrop : ncomp V (applyS G σ) + 1 = ncomp V G
    · exact Or.inr (Or.inl hdrop)
    by_cases hcl' : CleanR V (applyS G σ) s t
    · have hnoA := noT3_of_dang hD hcl'.1
      exact Or.inr (Or.inr (Or.inr (Or.inr ⟨hcl', fun tf _ hc => hnoG _ hc,
        fun tf _ hc => hnoA _ hc, fun tf _ hc => hnoA _ hc⟩)))
    · by_cases hR' : NoTypeIIIR V (applyS G σ) s t
      · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hcl', hR'⟩)))
      · exact Or.inr (Or.inr (Or.inl hR'))
  · intro G H hs hG hH hHam hd hds hdt hsV htV hz hcl h2 σ hw hev hneut hnc hR'
    exact absurd ⟨hR', fun ⟨_, c, hc, hn⟩ => hn (noT3_of_dang hD hR' c hc)⟩ hnc
  · intro G H hs hG hH hHam hd hds hdt hsV htV hz hcl h2 σ hw hev hneut hcl' hE hT hno
    exfalso
    apply hno
    obtain ⟨τ, hwτ, hevτ, hneutτ, hRτ⟩ := hT
    obtain ⟨⟨_, hpat, hcellS, _⟩, _, _, hR, _, _, _⟩ := hw
    have hF : IsFactor V d (applyS G σ) := factor_flipCol σ.n G hG hpat hcellS
    have hzF : ZeroAt (applyS G σ) H s t := zero_flipCol σ.n hpat hR hz
    have hE2 : E2Of V (applyS G σ) τ := fun tf _ hc => noT3_of_dang hD hcl'.1 _ hc
    have hch : H2bCond V (applyS G σ) s t τ := by
      unfold NoTypeIIIR at hRτ
      push Not at hRτ
      obtain ⟨c, hc, hcs, hct, hn⟩ := hRτ
      unfold NotTypeIII at hn
      push Not at hn
      obtain ⟨tf, hb, hf, hl1, hl2, hnc⟩ := hn
      exact ⟨c, tf, hc, ⟨hcs, hct⟩, hb, hf, hl1, hl2, hnc, fun _ => Or.inl (fun hcA => hD _ hcA)⟩
    obtain ⟨τ', h⟩ := t3_link_tg hs hF hH hHam hd hds hdt hsV htV hzF hcl' (by omega) hwτ hevτ
      hneutτ hE2 hch
    exact ⟨τ, [τ'], h⟩

-- **Restricted Tg chains exist** in every reached state without a Type III cell to flip and
-- with two components or more (ULHC `pathComplete`), from H1 and H2.
--
theorem rpath_exists {H : Finset Edge} (hs : Solid V) (hH : IsFactor V d H)
    (hHam : ncomp V H = 1) (hd : ∀ z, z ≠ s → z ≠ t → d z = 2) (hds : d s = 1) (hdt : d t = 1)
    (hsV : s ∈ V) (htV : t ∈ V) (hg : GapsCE V d s t) :
    ∀ (m : ℕ) (G : Finset Edge), mu V G H = m →
    IsFactor V d G → ZeroAt G H s t → CleanR V G s t → 2 ≤ ncomp V G →
    (∃ σ L, RPathTg V G s t σ L) ∨ T3Walk V G H s t := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro G hm hG hz hcl h2
  have := NearOK.of_mem htV
  have hD : Deg2Off V G s t :=
    ⟨InsideST.of_inside (Inside.of_factor hG), fun z hz hzs hzt => by rw [hG.2 z hz]; exact hd z hzs hzt⟩
  have hdsG : deg G s = 1 := by rw [hG.2 s hsV]; exact hds
  have hleG : ∀ z, deg G z ≤ 2 := by
    intro z
    by_cases hzV : z ∈ V
    · rw [hG.2 z hzV]
      by_cases h1 : z = s
      · rw [h1, hds]; omega
      by_cases h1' : z = t
      · rw [h1', hdt]; omega
      rw [hd z h1 h1']
    · rw [deg_zero_of_inside (Inside.of_factor hG) hzV]; omega
  obtain ⟨σ, hw0, hcase⟩ := walk_choice hs hG hH hHam hd hds hdt hsV htV hz hcl h2 hg
  have hwσ := hw0
  obtain ⟨hv, hn2, hmu, hR, hc1, hc2, _⟩ := hw0
  have hRall : ∀ x ∈ [σ], Restr s t x := by
    intro x hx; rw [List.mem_singleton.1 hx]; exact hR
  rcases Nat.mod_two_eq_zero_or_one σ.n with hev | hodd
  swap
  · exact Or.inl ⟨σ, [], hv, Or.inl hodd, trivial, hRall⟩
  by_cases hdrop : ncomp V (applyS G σ) + 1 = ncomp V G
  · exact Or.inl ⟨σ, [], hv, Or.inr ⟨hev, drop_twists hD hsV hdsG hcl.1 hv hR hev hdrop⟩, trivial, hRall⟩
  have hneut : ncomp V (applyS G σ) = ncomp V G := by omega
  by_cases hcl' : CleanR V (applyS G σ) s t
  swap
  · by_cases hR' : NoTypeIIIR V (applyS G σ) s t
    · obtain ⟨L, h⟩ := hg.h2a hs hG hH hHam hd hds hdt hsV htV hz hcl h2
        ⟨hv, hn2, hmu, hR, hc1, hc2, fun h => by omega⟩ hev hneut hcl' hR'
      exact Or.inl ⟨σ, L, h⟩
    by_cases hch : E2Of V G σ ∧ H2bCond V G s t σ
    · obtain ⟨hE2, hch⟩ := hch
      obtain ⟨τ, h⟩ := t3_link_tg hs hG hH hHam hd hds hdt hsV htV hz hcl h2
        ⟨hv, hn2, hmu, hR, hc1, hc2, fun h => by omega⟩ hev hneut hE2 hch
      exact Or.inl ⟨σ, [τ], h⟩
    · exact Or.inr ⟨σ, ⟨hv, hn2, hmu, hR, hc1, hc2, fun h => by omega⟩, hev, hneut, hR'⟩
  have hE : EFree V G σ := by
    rcases hcase with h | h | h | h | h
    · omega
    · exact absurd h hdrop
    · exact absurd hcl'.1 h
    · exact absurd hcl' h.1
    · exact h.2
  obtain ⟨c0, sd, n⟩ := σ
  obtain ⟨h1, hpat, hcellS, hsep⟩ := hv
  change n % 2 = 0 at hev
  change 2 ≤ n at hn2
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
  have hk : k % 2 = 0 := by omega
  have hcell : ∀ j ≤ k + 1, IsCell V (cellJ c0 sd j) := fun j hj => hcellS j (by simp only; omega)
  have hcor : ∀ j ≤ k + 1, ¬ IsCorner s (cellJ c0 sd j) ∧ ¬ IsCorner t (cellJ c0 sd j) :=
    fun j hj => hR j (by simp only; omega)
  have hG' : IsFactor V d (flipCol G c0 sd (k + 2)) := factor_flipCol (k + 2) G hG hpat hcellS
  have hz' : ZeroAt (flipCol G c0 sd (k + 2)) H s t := zero_flipCol (k + 2) hpat hR hz
  have hmu' : mu V (flipCol G c0 sd (k + 2)) H < m := by
    have h' : mu V (flipCol G c0 sd (k + 2)) H + 2 * (k + 2) = mu V G H := hmu
    rw [← hm]; omega
  have hex := ih _ hmu' _ rfl hG' hz' hcl' (by have h3 : ncomp V (flipCol G c0 sd (k + 2)) = ncomp V G := hneut; omega)
  by_cases hP0 : ∃ q L, RPathTg V (flipCol G c0 sd (k + 2)) s t q L
  swap
  · exact hg.hN hs hG hH hHam hd hds hdt hsV htV hz hcl h2 hwσ hev hneut hcl' hE
      (hex.resolve_left hP0) hP0
  have hP : ∃ w, ∃ q L, RPathTg V (flipCol G c0 sd (k + 2)) s t q L ∧ wt q L = w := by
    obtain ⟨q, L, h⟩ := hP0; exact ⟨_, q, L, h, rfl⟩
  obtain ⟨q, L, hQ, hw⟩ := Nat.find_spec hP
  refine Or.inl ?_
  exact comp_clean_tg hD hsV hdsG hleG hcl.1 hk hcell hcor hpat hsep hneut hcl'.1 hE.1 hE.2.1 hE.2.2
    hQ (fun σ' L' h' => by rw [hw]; exact Nat.find_min' hP ⟨σ', L', h', rfl⟩)

end induction

end HP

end ULHC
