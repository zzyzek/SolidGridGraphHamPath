/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
import ULHC.HP.ZeroPF
import ULHC.HP.ChainExistsTg
import ULHC.HP.RoundTg

/-!
# Completeness of the path-factor algorithm: skeleton

The invariant along a run, for a fixed Hamiltonian s–t path `H`: the state is a path-factor and
`D · H` vanishes on the endpoints' cells (`ZeroAt`).  Moves that avoid the endpoints' cells keep
it, since flipping an alternating cell changes `D` only at that cell (`alt_sink_or_source`).

The measure: `M G = 2 · ncomp G + e`, with `e = 0` when the next round has a Type III cell to
flip (away from the endpoints, or anywhere with two components) and `e = 1` otherwise.

Gaps, each marked in the source:
* **NEW MATH** `chain_exists`: a reached state with no such Type III cell and at least two
  components has a path in the restricted link graph.  Route: induction on μ with `lemmaB_t2`;
  the neutral-strip case needs a path-factor `comp_clean`.
* **NEW MATH** `chain_applies`: a minimum chain applies strip by strip and lowers the measure.
  For one or two strips the end test is judged in the actual state, so this is local; from three
  strips on it is ULHC's static-sequence validity (`round_ca`), whose proof uses `split_symm`,
  false for path-factors.
* ROUTINE: `zero_strip` (strip flips are flips of alternating cells, end first).
-/

namespace ULHC

namespace HP

open Finset Classical

variable {V : Finset Pt} {d : Pt → ℕ} {s t : Pt}

/-! ## The measure -/

noncomputable def M (V : Finset Pt) (G : Finset Edge) (s t : Pt) : ℕ :=
  2 * ncomp V G + (if (findT3R V G s t).isSome ∨ (ncomp V G = 2 ∧ (findT3 V G).isSome) then 0 else 1)

/-! ## The two gaps -/

-- No restricted Type III cell when the search finds none.
--
lemma findT3R_none {G : Finset Edge} (hGV : Inside V G) (h : findT3R V G s t = none) :
    NoTypeIIIR V G s t := by
  intro c hc hcs hct tf hb hf hl1 hl2
  by_contra hn
  unfold findT3R at h
  have := List.find?_eq_none.1 h (c, tf) (by
    simp only [List.mem_flatMap, List.mem_map]
    exact ⟨c, mem_cellList.2 ⟨hc.1, hc⟩, tf, mem_sidesL tf, rfl⟩)
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at this
  exact this ⟨⟨Bool.eq_false_iff.2 (fun h' => hcs (cornerB_eq_true_iff.1 h')),
    Bool.eq_false_iff.2 (fun h' => hct (cornerB_eq_true_iff.1 h'))⟩,
    (t3B_iff hGV hc).2 ⟨hb, hf, hl1, hl2, hn⟩⟩

lemma M_eq_Mc {G : Finset Edge} (hGV : Inside V G) : M V G s t = Mc V G s t := by
  unfold M Mc
  rw [cncomp_eq hGV]
  congr 1
  by_cases h1 : (findT3R V G s t).isSome = true <;> by_cases h2 : ncomp V G = 2 <;>
    by_cases h3 : (findT3 V G).isSome = true <;> simp [h1, h2, h3]

lemma mem_pnodes_avoid {G : Finset Edge} {x : PNode} (hx : x ∈ pnodes V G s t) : avoidB s t x.σ = true := by
  unfold pnodes candR at hx
  simp only [Finset.mem_union, Finset.mem_image, Finset.mem_product, Finset.mem_filter] at hx
  rcases hx with (⟨σ, ⟨_, h⟩, rfl⟩ | ⟨σ, ⟨_, h⟩, rfl⟩) | ⟨⟨a, b⟩, ⟨⟨_, h⟩, _⟩, rfl⟩ <;> exact h

lemma applyS_factor_zero {G H : Finset Edge} (hG : IsFactor V d G) (hz : ZeroAt G H s t) {σ : StripSpec}
    (hσ : σ ∈ allStrips V G) (hav : avoidB s t σ = true) :
    IsFactor V d (applyS G σ) ∧ ZeroAt (applyS G σ) H s t := by
  obtain ⟨_, hpat, hcell⟩ := mem_allStrips.1 hσ
  exact ⟨factor_flipCol σ.n G hG hpat hcell, zero_strip hσ hav hz⟩

-- Chains of one or two strips: every property is checked by the end test in the actual state.
--
/-! ## Assembly -/

lemma findChainPF_some_of_path {G : Finset Edge}
    (h : ∃ p : List PNode, MP.IsPath (psrc V G) pmid (ptgt V G s t) (pedge V G) p ∧
      ∀ x ∈ p, x ∈ pnodes V G s t) : ∃ L, findChainPF V G s t = some L := by
  obtain ⟨p, hp, hpN⟩ := h
  unfold findChainPF
  rcases hm : MP.minPath (pnodes V G s t) (psrc V G) pmid (ptgt V G s t) (pedge V G) pw with _ | q
  · exact absurd (MP.minPath_none _ _ _ _ _ _ hm p hp hpN) id
  · exact ⟨_, rfl⟩

lemma findT3R_avoid {G : Finset Edge} {c : Pt} {tf : Side} (h : findT3R V G s t = some (c, tf)) :
    ¬ IsCorner s c ∧ ¬ IsCorner t c := by
  unfold findT3R at h
  have hp := List.find?_some h
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hp
  exact ⟨fun h => by rw [cornerB_of h] at hp; simp at hp, fun h => by rw [cornerB_of h] at hp; simp at hp⟩

-- `CleanR` is exactly "no Type III cell for the next round to flip", as the search sees it.
--
lemma cleanR_iff {X : Finset Edge} (hXV : Inside V X) :
    CleanR V X s t ↔ ¬ ((findT3R V X s t).isSome = true ∨
      (ncomp V X = 2 ∧ (findT3 V X).isSome = true)) := by
  constructor
  · rintro ⟨hR, h2⟩ (h | ⟨h2', h⟩)
    · rcases hf : findT3R V X s t with _ | ⟨c, tf⟩
      · rw [hf] at h; simp at h
      · obtain ⟨hc, hb, hff, hl1, hl2, hn⟩ := findT3R_some hXV hf
        obtain ⟨hcs, hct⟩ := findT3R_avoid hf
        exact hn (hR c hc hcs hct tf hb hff hl1 hl2)
    · rcases hf : findT3 V X with _ | ⟨c, tf⟩
      · rw [hf] at h; simp at h
      · obtain ⟨hc, hb, hff, hl1, hl2, hn⟩ := findT3_some hXV hf
        exact h2 ⟨h2', c, hc, fun hT => hn (hT tf hb hff hl1 hl2)⟩
  · intro h
    refine ⟨fun c hc hcs hct => ?_, fun ⟨h2', c, hc, hn⟩ => ?_⟩
    · by_contra hn
      apply h; left
      rcases hf : findT3R V X s t with _ | p
      · exact absurd (fun tf => findT3R_none hXV hf c hc hcs hct tf) hn
      · rfl
    · apply h; right
      refine ⟨h2', ?_⟩
      rcases hf : findT3 V X with _ | p
      · exact absurd (fun tf => findT3_none hXV hf c hc tf) hn
      · rfl

lemma M_clean {X : Finset Edge} (hXV : Inside V X) (h : CleanR V X s t) :
    M V X s t = 2 * ncomp V X + 1 := by
  unfold M; rw [ite_eq_right ((cleanR_iff hXV).1 h)]

lemma M_not_clean {X : Finset Edge} (hXV : Inside V X) (h : ¬ CleanR V X s t) :
    M V X s t = 2 * ncomp V X := by
  unfold M; rw [ite_eq_left (by by_contra h'; exact h ((cleanR_iff hXV).2 h'))]; rfl

-- A path in the restricted link graph exists (from `rpath_exists`, which rests on the named
-- gaps `walk_choice` (H1) and `t3_link_tg` (H2)).
--
theorem chain_exists {G H : Finset Edge} (hs : Solid V) (hG : IsFactor V d G) (hH : IsFactor V d H)
    (hHam : ncomp V H = 1) (hd : ∀ z, z ≠ s → z ≠ t → d z = 2) (hds : d s = 1) (hdt : d t = 1)
    (hsV : s ∈ V) (htV : t ∈ V) (hz : ZeroAt G H s t) (hr : findT3R V G s t = none)
    (h2c : ¬ (ncomp V G = 2 ∧ (findT3 V G).isSome)) (h2 : 2 ≤ ncomp V G) (hg : GapsCE V d s t) :
    ∃ p : List PNode, MP.IsPath (psrc V G) pmid (ptgt V G s t) (pedge V G) p ∧
      ∀ x ∈ p, x ∈ pnodes V G s t := by
  have hGV := Inside.of_factor hG
  have hcl : CleanR V G s t := by
    refine ⟨findT3R_none hGV hr, fun ⟨h2', c, hc, hn⟩ => h2c ⟨h2', ?_⟩⟩
    rcases hf : findT3 V G with _ | p
    · exact absurd (fun tf => findT3_none hGV hf c hc tf) hn
    · rfl
  have hD : Deg2Off V G s t :=
    ⟨InsideST.of_inside hGV, fun z hz hzs hzt => by rw [hG.2 z hz]; exact hd z hzs hzt⟩
  have hdsG : deg G s = 1 := by rw [hG.2 s hsV]; exact hds
  rcases rpath_exists hs hH hHam hd hds hdt hsV htV hg _ G rfl hG hz hcl h2 with ⟨σ, L, h⟩ | hT
  · obtain ⟨p, hp, hN, _⟩ := rpath_to_ppath hD hsV hdsG h
    exact ⟨p, hp, hN⟩
  -- A Type-III walk strip lowers `M` by itself: a one-strip chain.
  --
  obtain ⟨τ, ⟨hv, _, _, hR, _, _, _⟩, _, hneut, hR'⟩ := hT
  have hin : Inside V (applyS G τ) := (degs_flipCol τ.n G hGV hv.2.1 hv.2.2.1).1
  refine single_ppath hD hsV hv hR ?_
  rw [← M_eq_Mc hin, ← M_eq_Mc hGV, M_not_clean hin (fun h => hR' h.1), M_clean hGV hcl, hneut]
  omega

-- The weight of the minimum chain found by the search (0 when there is none).
--
noncomputable def wmin (V : Finset Pt) (G : Finset Edge) (s t : Pt) : ℕ :=
  match MP.minPath (pnodes V G s t) (psrc V G) pmid (ptgt V G s t) (pedge V G) pw with
  | some p => MP.pw pw p
  | none => 0

lemma wmin_le {G : Finset Edge} {p : List PNode}
    (hp : MP.IsPath (psrc V G) pmid (ptgt V G s t) (pedge V G) p)
    (hN : ∀ x ∈ p, x ∈ pnodes V G s t) : wmin V G s t ≤ MP.pw pw p := by
  unfold wmin
  rcases hm : MP.minPath (pnodes V G s t) (psrc V G) pmid (ptgt V G s t) (pedge V G) pw with _ | q
  · simp
  · exact MP.minPath_min _ _ _ _ _ _ hm p hp hN

-- The first strip of a chain with two strips or more keeps the count (its end cell splits).
--
lemma first_neutral {G : Finset Edge} (hD : Deg2Off V G s t) (hs0 : s ∈ V) (hds : deg G s = 1)
    (hT : NoTypeIIIR V G s t) {a b : StripSpec} {L : List StripSpec}
    (hP : RPathTg V G s t a (b :: L)) : ncomp V (applyS G a) = ncomp V G := by
  obtain ⟨hv, ⟨hev, hab, _⟩, _, hR⟩ := hP
  have hR0 : Restr s t a := hR a (List.mem_cons_self ..)
  obtain ⟨c, sd, n⟩ := a
  obtain ⟨h1, hpat, hcellS, hsep⟩ := hv
  change n % 2 = 0 at hev
  change 1 ≤ n at h1
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
  have hk : k % 2 = 0 := by omega
  have hcell : ∀ j ≤ k + 1, IsCell V (cellJ c sd j) := fun j hj => hcellS j (by simp only; omega)
  have hcor : ∀ j ≤ k + 1, ¬ IsCorner s (cellJ c sd j) ∧ ¬ IsCorner t (cellJ c sd j) :=
    fun j hj => hR0 j (by simp only; omega)
  obtain ⟨el1, el2, eb, ef⟩ := end_frame_pf hk hpat
  have hsame := end_same_loc (restr_notT3 hT (hcell (k + 1) le_rfl) (hcor (k + 1) le_rfl)) hk
    hcell hpat
  have hsp := link_end_splits hab (hcell (k + 1) le_rfl) el1 el2 eb ef hsame
  obtain ⟨F1, hF1, _, _, _, _, hcnt, _⟩ :=
    strip_even_rel_pf k hk G hD hs0 hds hcell hcor hpat hsep hsame
  change ncomp V (flip G (cellJ c sd (k + 1))) = ncomp V G + 1 at hsp
  rw [← hF1] at hsp
  change ncomp V (flipCol G c sd (k + 2)) = ncomp V G
  omega

-- E-sites for one round at a strip `a` of `G`: the cells beside `a`'s start and diagonally behind
-- it (in `G`), and beside its end (after `a`), are not Type III.
--
def ERound (V : Finset Pt) (G : Finset Edge) (a : StripSpec) : Prop :=
  E2Of V G a ∧
  (∀ tf, tf = latA a.s ∨ tf = latB a.s → IsCell V (nb (endCell a) tf) →
    NotTypeIII V (applyS G a) (nb (endCell a) tf)) ∧
  (∀ tf, tf = latA a.s ∨ tf = latB a.s → IsCell V (nb (nb a.c tf) a.s.opp) →
    NotTypeIII V G (nb (nb a.c tf) a.s.opp))

-- **NEW MATH (H3, three components or more).** In a reached state without a Type III cell to flip, the first strip of a
-- minimum chain of two strips or more, when it leaves a clean state, has no E-configuration
-- for the round.
--
-- (Open; not proved. Its statement is the field `h3` of `GapsPF`.)
--

-- **E-sites for the round.** With two components no E-site can be a Type III cell; with three
-- or more it is H3 (`first_eround3`).
--
-- **The open lemmas of the completeness proof**: those of chain existence and H3.
--
structure GapsPF (V : Finset Pt) (d : Pt → ℕ) (s t : Pt) : Prop where
  ce : GapsCE V d s t
  h3 : ∀ {G H : Finset Edge}, Solid V → IsFactor V d G → IsFactor V d H → ncomp V H = 1 →
    (∀ z, z ≠ s → z ≠ t → d z = 2) → d s = 1 → d t = 1 → s ∈ V → t ∈ V → ZeroAt G H s t →
    CleanR V G s t → 3 ≤ ncomp V G → ∀ {a b : StripSpec} {L : List StripSpec},
    RPathTg V G s t a (b :: L) → (∀ σ L', RPathTg V G s t σ L' → wt a (b :: L) ≤ wt σ L') →
    CleanR V (applyS G a) s t → ERound V G a

-- **Proved: no open lemma is needed when no cell has `s` or `t` as a corner.**
--
theorem gapsPF_dang (hD : Dang V s t) : GapsPF V d s t :=
  ⟨gapsCE_dang hD, fun {_ _} _ _ _ _ _ _ _ _ _ _ hcl _ {_ _ _} _ _ hcl' =>
    ⟨fun _ _ hc => noT3_of_dang hD hcl.1 _ hc, fun _ _ hc => noT3_of_dang hD hcl'.1 _ hc,
      fun _ _ hc => noT3_of_dang hD hcl.1 _ hc⟩⟩

theorem first_eround {G H : Finset Edge} (hs : Solid V) (hG : IsFactor V d G)
    (hH : IsFactor V d H) (hHam : ncomp V H = 1) (hd : ∀ z, z ≠ s → z ≠ t → d z = 2)
    (hds : d s = 1) (hdt : d t = 1) (hsV : s ∈ V) (htV : t ∈ V) (hz : ZeroAt G H s t)
    (hcl : CleanR V G s t) (h2 : 2 ≤ ncomp V G) {a b : StripSpec} {L : List StripSpec}
    (hP : RPathTg V G s t a (b :: L))
    (hmin : ∀ σ L', RPathTg V G s t σ L' → wt a (b :: L) ≤ wt σ L')
    (hcl' : CleanR V (applyS G a) s t) (hg : GapsPF V d s t) : ERound V G a := by
  by_cases h3 : ncomp V G = 2
  swap
  · exact hg.h3 hs hG hH hHam hd hds hdt hsV htV hz hcl (by omega) hP hmin hcl'
  have hGV := Inside.of_factor hG
  have hD : Deg2Off V G s t := ⟨InsideST.of_inside hGV, fun z hz hzs hzt => by rw [hG.2 z hz]; exact hd z hzs hzt⟩
  have hdsG : deg G s = 1 := by rw [hG.2 s hsV]; exact hds
  have hneut := first_neutral hD hsV hdsG hcl.1 hP
  have hnoG : ∀ c, IsCell V c → NotTypeIII V G c := fun c hc => by
    by_contra hn; exact hcl.2 ⟨h3, c, hc, hn⟩
  have hnoA : ∀ c, IsCell V c → NotTypeIII V (applyS G a) c := fun c hc => by
    by_contra hn; exact hcl'.2 ⟨by omega, c, hc, hn⟩
  exact ⟨fun tf _ hc => hnoG _ hc, fun tf _ hc => hnoA _ hc, fun tf _ hc => hnoG _ hc⟩

-- One round from a reached state with at least two components makes a move, keeps the
-- invariant (zeros at the endpoints, or a single component), and lowers the measure `M`, or keeps
-- it and lowers the weight of the minimum chain.
--
theorem step_progress {G H : Finset Edge} (hs : Solid V) (hG : IsFactor V d G) (hH : IsFactor V d H)
    (hHam : ncomp V H = 1) (hd : ∀ z, z ≠ s → z ≠ t → d z = 2) (hds : d s = 1) (hdt : d t = 1)
    (hsV : s ∈ V) (htV : t ∈ V) (hz : ZeroAt G H s t) (h2 : 2 ≤ ncomp V G) (hg : GapsPF V d s t) :
    ∃ G', stepPF V G s t = some G' ∧ IsFactor V d G' ∧ (ZeroAt G' H s t ∨ ncomp V G' = 1) ∧
      (M V G' s t < M V G s t ∨ (M V G' s t = M V G s t ∧ wmin V G' s t < wmin V G s t)) := by
  have := RoundOK.of_mem htV
  have hGV := Inside.of_factor hG
  have hcn : cncomp V G = ncomp V G := cncomp_eq hGV
  have hD : Deg2Off V G s t := ⟨InsideST.of_inside hGV, fun z hz hzs hzt => by rw [hG.2 z hz]; exact hd z hzs hzt⟩
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
    · rw [deg_zero_of_inside hGV hzV]; omega
  -- The chain branch, used when no Type III cell is to be flipped.
  have chain : findT3R V G s t = none → ¬ (ncomp V G = 2 ∧ (findT3 V G).isSome) →
      ∃ G', (match findChainPF V G s t with
              | some L => applyChainChecked V G (L.take 1)
              | none => none) = some G' ∧ IsFactor V d G' ∧ (ZeroAt G' H s t ∨ ncomp V G' = 1) ∧
        (M V G' s t < M V G s t ∨ (M V G' s t = M V G s t ∧ wmin V G' s t < wmin V G s t)) := by
    intro hr h2c
    have hcl : CleanR V G s t := by
      refine ⟨findT3R_none hGV hr, fun ⟨h2', c, hc, hn⟩ => h2c ⟨h2', ?_⟩⟩
      rcases hf : findT3 V G with _ | p
      · exact absurd (fun tf => findT3_none hGV hf c hc tf) hn
      · rfl
    have hMG := M_clean hGV hcl
    obtain ⟨p0, hp0, hN0⟩ := chain_exists hs hG hH hHam hd hds hdt hsV htV hz hr h2c h2 hg.ce
    rcases hm : MP.minPath (pnodes V G s t) (psrc V G) pmid (ptgt V G s t) (pedge V G) pw with _ | p
    · exact absurd (MP.minPath_none _ _ _ _ _ _ hm p0 hp0 hN0) id
    obtain ⟨hp, hpN⟩ := MP.minPath_some _ _ _ _ _ _ hm
    have hfc : findChainPF V G s t = some (p.map PNode.σ) := by unfold findChainPF; rw [hm]; rfl
    have hwG : wmin V G s t = MP.pw pw p := by unfold wmin; rw [hm]
    rw [hfc]
    rcases p with _ | ⟨x, rest⟩
    · exact absurd hp id
    obtain ⟨hsrc, htail⟩ := MP.isPath_cons.1 hp
    have hsrc' := hsrc
    simp only [psrc, Bool.and_eq_true, beq_iff_eq] at hsrc'
    obtain ⟨⟨hpos, _⟩, hval⟩ := hsrc'
    have hv := (validB_iff hGV).1 hval
    have hσ : x.σ ∈ allStrips V G := mem_allStrips.2 ⟨hv.1, hv.2.1, hv.2.2.1⟩
    have hav : avoidB s t x.σ = true := mem_pnodes_avoid (hpN x (by simp))
    obtain ⟨hF', hz'⟩ := applyS_factor_zero hG hz hσ hav
    have hF'V := Inside.of_factor hF'
    refine ⟨applyS G x.σ, by simp [applyChainChecked, hσ], hF', Or.inl hz', ?_⟩
    rcases rest with _ | ⟨y, rest'⟩
    · -- One strip: the end test at position 1 is "the measure drops".
      left
      have htg := MP.isTail_nil.1 htail
      simp only [ptgt, hpos, beq_self_eq_true, ite_true, decide_eq_true_eq] at htg
      rw [M_eq_Mc hF'V, M_eq_Mc hGV]; exact htg
    · obtain ⟨hRP, hpw⟩ := ppath_to_rpath hGV (Nat.le_succ _) (Finset.Subset.refl _) hp hpN
      have hmin : ∀ σ L', RPathTg V G s t σ L' →
          wt x.σ (y.σ :: rest'.map PNode.σ) ≤ wt σ L' := fun σ L' h => by
        obtain ⟨q, hq, hqN, hqw⟩ := rpath_to_ppath hD hsV hdsG h
        have := MP.minPath_min _ _ _ _ _ _ hm q hq hqN
        omega
      have hneut := first_neutral hD hsV hdsG hcl.1 hRP
      by_cases hcl' : CleanR V (applyS G x.σ) s t
      · right
        have hE := first_eround hs hG hH hHam hd hds hdt hsV htV hz hcl h2 hRP hmin hcl' hg
        refine ⟨by rw [M_clean hF'V hcl', hMG, hneut], ?_⟩
        have hR0 : Restr s t x.σ := hRP.2.2.2 x.σ (List.mem_cons_self ..)
        generalize hxs : x.σ = a at hRP hmin hneut hcl' hE hR0 hv hpw hF'V hF' hz' ⊢
        obtain ⟨c0, sd, n⟩ := a
        obtain ⟨h1, hpat, hcellS, hsep⟩ := hv
        have hev : n % 2 = 0 := hRP.2.1.1
        change 1 ≤ n at h1
        obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
        have hk : k % 2 = 0 := by omega
        have hcell : ∀ j ≤ k + 1, IsCell V (cellJ c0 sd j) :=
          fun j hj => hcellS j (by simp only; omega)
        have hcor : ∀ j ≤ k + 1, ¬ IsCorner s (cellJ c0 sd j) ∧ ¬ IsCorner t (cellJ c0 sd j) :=
          fun j hj => hR0 j (by simp only; omega)
        obtain ⟨hR', hwt⟩ := round_tg hD hsV hdsG hleG hcl.1 hk hcell hcor hpat hsep hcl'.1 hneut
          hE.1 hE.2.1 hE.2.2 hRP hmin
        obtain ⟨q, hq, hqN, hqw⟩ := rpath_to_ppath (Inside.of_factor hF' |> fun hin =>
          (⟨InsideST.of_inside hin, fun z hz hzs hzt => by rw [hF'.2 z hz]; exact hd z hzs hzt⟩ : Deg2Off V _ s t))
          hsV (by rw [hF'.2 s hsV]; exact hds) hR'
        have hle' := wmin_le hq hqN
        change wmin V (flipCol G c0 sd (k + 2)) s t < wmin V G s t
        rw [hwG, hpw]
        change wmin V (flipCol G c0 sd (k + 2)) s t ≤ MP.pw pw q at hle'
        omega
      · left
        rw [M_not_clean hF'V hcl', hMG, hneut]; omega
  unfold stepPF
  rcases hr : findT3R V G s t with _ | ⟨c, tf⟩
  · simp only
    by_cases hc2 : cncomp V G = 2
    · rw [ite_eq_left (by simpa using hc2)]
      rcases ht : findT3 V G with _ | ⟨c, tf⟩
      · simp only
        exact chain hr (by rw [ht]; simp)
      · simp only [Option.some.injEq, exists_eq_left']
        have data := findT3_some hGV ht
        obtain ⟨hc, hb, hf, hl1, hl2, hn⟩ := data
        obtain ⟨hF', hcnt, _⟩ := typeIII_flip (H := H) hG hd hds hsV hc (fun hT => hn (hT tf hb hf hl1 hl2))
        have h2' : ncomp V G = 2 := by rw [← hcn]; exact hc2
        refine ⟨hF', Or.inr (by omega), Or.inl ?_⟩
        unfold M
        have : (findT3R V G s t).isSome = true ∨ (ncomp V G = 2 ∧ (findT3 V G).isSome = true) :=
          Or.inr ⟨h2', by rw [ht]; rfl⟩
        rw [ite_eq_left this]
        split_ifs <;> omega
    · rw [ite_eq_right (by simpa using hc2)]
      exact chain hr (fun h => hc2 (by rw [hcn]; exact h.1))
  · simp only [Option.some.injEq, exists_eq_left']
    have data := findT3R_some hGV hr
    have hav := findT3R_avoid hr
    obtain ⟨hc, hb, hf, hl1, hl2, hn⟩ := data
    obtain ⟨hF', hcnt, _⟩ := typeIII_flip (H := H) hG hd hds hsV hc (fun hT => hn (hT tf hb hf hl1 hl2))
    refine ⟨hF', Or.inl (zero_flip (alt_of_bf hb hf hl1 hl2) hav.1 hav.2 hz), Or.inl ?_⟩
    unfold M
    have : (findT3R V G s t).isSome = true ∨ (ncomp V G = 2 ∧ (findT3 V G).isSome = true) :=
      Or.inl (by rw [hr]; rfl)
    rw [ite_eq_left this]
    split_ifs <;> omega

-- A strip with all its cells in `V` has at most `|V|` cells.
--
lemma len_le_card_pf {c : Pt} {sd : Side} {n : ℕ} (hc : ∀ j < n, IsCell V (cellJ c sd j)) :
    n ≤ V.card := by
  have hsub : (Finset.range n).image (cellJ c sd) ⊆ V := by
    intro z hz
    simp only [Finset.mem_image, Finset.mem_range] at hz
    obtain ⟨j, hj, rfl⟩ := hz
    exact (hc j hj).1
  have := Finset.card_le_card hsub
  rwa [Finset.card_image_of_injective _ (fun i j h => cellJ_inj c sd h), Finset.card_range] at this

-- Bounds: candidate strips, nodes, and the weight of a minimum chain.
--
def CandB (V : Finset Pt) : ℕ := 4 * V.card + V.card * (4 * V.card)

def Wb (V : Finset Pt) : ℕ := (2 * CandB V + CandB V * CandB V) * V.card

lemma card_pnodes_le (G : Finset Edge) :
    (pnodes V G s t).card ≤ 2 * CandB V + CandB V * CandB V := by
  have hc : (candR V G s t).card ≤ CandB V :=
    (Finset.card_filter_le _ _).trans (card_cand_le (V := V) G)
  unfold pnodes
  have h1 := Finset.card_union_le
    ((candR V G s t).image (fun σ => PNode.mk σ 1 σ) ∪ (candR V G s t).image (fun σ => PNode.mk σ 3 σ))
    (((candR V G s t) ×ˢ (candR V G s t)).image (fun p => PNode.mk p.1 2 p.2))
  have h2 := Finset.card_union_le ((candR V G s t).image (fun σ => PNode.mk σ 1 σ))
    ((candR V G s t).image (fun σ => PNode.mk σ 3 σ))
  have h3 : ((candR V G s t).image (fun σ => PNode.mk σ 1 σ)).card ≤ CandB V :=
    Finset.card_image_le.trans hc
  have h4 : ((candR V G s t).image (fun σ => PNode.mk σ 3 σ)).card ≤ CandB V :=
    Finset.card_image_le.trans hc
  have h5 : (((candR V G s t) ×ˢ (candR V G s t)).image (fun p => PNode.mk p.1 2 p.2)).card ≤
      CandB V * CandB V := by
    refine Finset.card_image_le.trans ?_
    rw [Finset.card_product]
    exact Nat.mul_le_mul hc hc
  omega

-- **The weight of a minimum chain is at most `Wb V`**: a repetition-free path is no lighter
-- than the minimum, has at most as many nodes as the graph, and each strip has at most `|V|`
-- cells.
--
lemma wmin_le_Wb (G : Finset Edge) : wmin V G s t ≤ Wb V := by
  unfold wmin
  rcases hm : MP.minPath (pnodes V G s t) (psrc V G) pmid (ptgt V G s t) (pedge V G) pw with _ | p
  · simp
  simp only
  obtain ⟨hp, hpN⟩ := MP.minPath_some _ _ _ _ _ _ hm
  rcases p with _ | ⟨x, L⟩
  · exact absurd hp id
  obtain ⟨hsrc, ht⟩ := MP.isPath_cons.1 hp
  obtain ⟨L', ht', hnd, hsub⟩ := MP.shortcut ht
  have hq : MP.IsPath (psrc V G) pmid (ptgt V G s t) (pedge V G) (x :: L') := ⟨hsrc, ht'⟩
  have hqN : ∀ z ∈ x :: L', z ∈ pnodes V G s t := fun z hz => hpN z (hsub.subset hz)
  have hle := MP.minPath_min _ _ _ _ _ _ hm (x :: L') hq hqN
  have hlen : (x :: L').length ≤ (pnodes V G s t).card := by
    have := MP.length_le_card (NL := (pnodes V G s t).toList) hnd
      (fun z hz => Finset.mem_toList.2 (hqN z hz))
    rwa [Finset.length_toList] at this
  have hw : ∀ z ∈ x :: L', pw z ≤ V.card := fun z hz =>
    len_le_card_pf (cells_of_cand (mem_pnodes_cand (hqN z hz)).1).2
  have hsum : MP.pw pw (x :: L') ≤ (x :: L').length * V.card := by
    unfold MP.pw
    have := List.sum_le_length_nsmul ((x :: L').map pw) V.card (fun y hy => by
      obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hy; exact hw z hz)
    simpa using this
  have hc := card_pnodes_le (V := V) (s := s) (t := t) G
  calc MP.pw pw (x :: L) ≤ MP.pw pw (x :: L') := hle
    _ ≤ (x :: L').length * V.card := hsum
    _ ≤ (2 * CandB V + CandB V * CandB V) * V.card := Nat.mul_le_mul_right _ (hlen.trans hc)

lemma M_le (G : Finset Edge) : M V G s t ≤ 2 * V.card + 1 := by
  have h2 : ncomp V G ≤ V.card := Finset.card_image_le
  unfold M; split_ifs <;> omega

-- The fuel that suffices from any reached state: rounds lower `M · (Wb + 1) + wmin`.
--
def fuelPF (V : Finset Pt) : ℕ := (2 * V.card + 2) * (Wb V + 1)

-- **Completeness from a reached state**, with an explicit number of rounds.
--
theorem runPF_complete {H : Finset Edge} (hs : Solid V) (hH : IsFactor V d H) (hHam : ncomp V H = 1)
    (hd : ∀ z, z ≠ s → z ≠ t → d z = 2) (hds : d s = 1) (hdt : d t = 1) (hsV : s ∈ V) (htV : t ∈ V)
    (hg : GapsPF V d s t) :
    ∀ k (G : Finset Edge), IsFactor V d G → (ZeroAt G H s t ∨ ncomp V G = 1) →
      M V G s t * (Wb V + 1) + wmin V G s t ≤ k → runPF V s t (k + 1) G = true := by
  intro k
  induction k with
  | zero =>
    intro G hG _ hM
    have := ncomp_pos (F := G) hsV
    have hM1 : 1 ≤ M V G s t := by unfold M; split_ifs <;> omega
    have : Wb V + 1 ≤ M V G s t * (Wb V + 1) := Nat.le_mul_of_pos_left _ hM1
    omega
  | succ k ih =>
    intro G hG hz hM
    simp only [runPF]
    by_cases h1 : cncomp V G = 1
    · simp [h1]
    · have h1' : ncomp V G ≠ 1 := by rw [← cncomp_eq (Inside.of_factor hG)]; exact h1
      have hn : 2 ≤ ncomp V G := by have := ncomp_pos (F := G) hsV; omega
      have hz0 : ZeroAt G H s t := hz.resolve_right h1'
      obtain ⟨G', hst, hG', hz', hlt⟩ := step_progress hs hG hH hHam hd hds hdt hsV htV hz0 hn hg
      rw [ite_eq_right_iff.2 (fun h => absurd (by simpa using h) h1), hst]
      refine ih G' hG' hz' ?_
      have hw' := wmin_le_Wb (V := V) (s := s) (t := t) G'
      rcases hlt with hlt | ⟨heq, hlt⟩
      · have : M V G' s t * (Wb V + 1) + (Wb V + 1) ≤ M V G s t * (Wb V + 1) := by
          rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ hlt
        omega
      · rw [heq]; omega

-- **Completeness with `fuelPF` rounds.**
--
theorem runPF_complete_fuel {H : Finset Edge} (hs : Solid V) (hH : IsFactor V d H)
    (hHam : ncomp V H = 1) (hd : ∀ z, z ≠ s → z ≠ t → d z = 2) (hds : d s = 1) (hdt : d t = 1)
    (hsV : s ∈ V) (htV : t ∈ V) (hg : GapsPF V d s t) (G : Finset Edge) (hG : IsFactor V d G)
    (hz : ZeroAt G H s t ∨ ncomp V G = 1) : runPF V s t (fuelPF V) G = true := by
  have hle : M V G s t * (Wb V + 1) + wmin V G s t + 1 ≤ fuelPF V := by
    have h1 := M_le (V := V) (s := s) (t := t) G
    have h2 := wmin_le_Wb (V := V) (s := s) (t := t) G
    unfold fuelPF
    have : M V G s t * (Wb V + 1) ≤ (2 * V.card + 1) * (Wb V + 1) := Nat.mul_le_mul_right _ h1
    nlinarith
  obtain ⟨j, hj⟩ : ∃ j, fuelPF V = (M V G s t * (Wb V + 1) + wmin V G s t + j) + 1 :=
    ⟨fuelPF V - (M V G s t * (Wb V + 1) + wmin V G s t + 1), by omega⟩
  rw [hj]
  exact runPF_complete hs hH hHam hd hds hdt hsV htV hg _ G hG hz (by omega)

end HP

end ULHC
