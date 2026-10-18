/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
import ULHC.HP.AfterFence

/-!
# Theorem A for path-factors (notes: the existence half)

`theoremA_pf`: let `H` be a Hamiltonian s–t path and `F` a path-factor with `D F H = 0` on every
cell with an endpoint as a corner. Then moves that keep away from the endpoints' cells (UL
strips avoiding `s` and `t`, and Type III merges at cells without an endpoint as a corner)
lead from `F` either to a Hamiltonian path or to a state with a Type III cell that has an
endpoint as a corner. Every move keeps the zeros; each strip lowers `μ` and keeps or lowers the
count, each merge lowers the count.

Tools: `factor_flipCol` (strips keep the degrees), `strip_D_off` (a strip changes `D` only on
its cells), `typeIII_flip` (a Type III flip merges, keeps degrees, changes `D` only there).
-/

namespace ULHC

open Finset Classical

namespace HP

lemma factor_flip {V : Finset Pt} {d : Pt → ℕ} {F : Finset Edge} (h : IsFactor V d F)
    (C : ACell) {c : Pt} (hc : IsCell V c) (hE : cellE c = {C.e1, C.e2, C.l1, C.l2})
    (h1 : C.e1 ∈ F) (h2 : C.e2 ∈ F) (h3 : C.l1 ∉ F) (h4 : C.l2 ∉ F) :
    IsFactor V d (ULHC.flip F c) := by
  refine ⟨fun e he => ?_, fun z hz => ?_⟩
  · unfold ULHC.flip at he
    rcases Finset.mem_symmDiff.1 he with ⟨h', _⟩ | ⟨h', _⟩
    · exact h.1 e h'
    · exact isEdge_of_cellE hc h'
  · rw [C.flip_eq hE h1 h2 h3 h4, C.deg_res h1 h2 h3 h4]; exact h.2 z hz

lemma factor_flipCol {V : Finset Pt} {d : Pt → ℕ} {c : Pt} {s : Side} :
    ∀ n (F : Finset Edge), IsFactor V d F → StripPat F c s n → (∀ j < n, IsCell V (cellJ c s j)) →
      IsFactor V d (flipCol F c s n) := by
  intro n
  induction n with
  | zero => intro F hF _ _; exact hF
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
    have hF' : IsFactor V d (ULHC.flip F (cellJ c s n)) := by
      rcases Nat.mod_two_eq_zero_or_one n with h | h
      · exact factor_flip hF (mkBF _ s) hce (mkBF_cellE _ s) (mB.2 h) (mF.2 h)
          (fun h' => by have := mL1.1 h'; omega) (fun h' => by have := mL2.1 h'; omega)
      · exact factor_flip hF (mkLat _ s) hce (mkLat_cellE _ s) (mL1.2 h) (mL2.2 h)
          (fun h' => by have := mB.1 h'; omega) (fun h' => by have := mF.1 h'; omega)
    rcases n with _ | n
    · simpa [flipCol] using hF'
    · exact ih _ hF' (pat_flip_end ⟨hb, hl, hf⟩) (fun j hj => hcell j (by omega))

-- A strip changes `D` only on its own cells.
--
theorem strip_D_off {F H : Finset Edge} {c : Pt} {s : Side} {o : Bool} (hp : ParOK c s o) :
    ∀ n, StripPat F c s n → (∀ j < n, Good o (D F H (cellJ c s j))) →
      ∀ x, (∀ j < n, x ≠ cellJ c s j) → D (flipCol F c s n) H x = D F H x := by
  intro n
  induction n generalizing F with
  | zero => intro _ _ x _; simp [flipCol]
  | succ n ih =>
    intro hpat hgood x hx
    rw [flipCol_succ]
    have arcs := end_arcs hp hpat
    have hD : ∀ y, y ≠ cellJ c s n → D (ULHC.flip F (cellJ c s n)) H y = D F H y := by
      intro y hy
      cases o
      · rw [D_flip_source (fun s' => by simpa using arcs s')]; simp [hy]
      · rw [D_flip_sink (fun s' => by simpa using arcs s')]; simp [hy]
    rcases n with _ | n
    · simp only [flipCol]; exact hD x (hx 0 (by omega))
    · have hne : ∀ j < n + 1, cellJ c s j ≠ cellJ c s (n + 1) := by
        intro j hj h; have := cellJ_inj c s h; omega
      rw [ih (pat_flip_end hpat) (fun j hj => by rw [hD _ (hne j hj)]; exact hgood j (by omega)) x
        (fun j hj => hx j (by omega))]
      exact hD x (hx (n + 1) (by omega))

-- A Type III flip merges, keeps the degrees, and changes `D` only at the flipped cell.
--
theorem typeIII_flip {V : Finset Pt} {d : Pt → ℕ} {F H : Finset Edge} (hF : IsFactor V d F)
    {s t : Pt} (hd : ∀ z, z ≠ s → z ≠ t → d z = 2) (hds : d s = 1) (hsV : s ∈ V)
    {c : Pt} (hc : IsCell V c) (hT3 : ¬ NotTypeIII V F c) :
    IsFactor V d (ULHC.flip F c) ∧ ncomp V (ULHC.flip F c) + 1 = ncomp V F ∧
      ∀ x, x ≠ c → D (ULHC.flip F c) H x = D F H x := by
  unfold NotTypeIII at hT3
  push Not at hT3
  obtain ⟨s', hb, hf, hl1, hl2, hn⟩ := hT3
  have hE := mkBF_cellE c s'
  have hfe := (mkBF c s').flip_eq hE hb hf hl1 hl2
  have hD2 : Deg2Off V F s t :=
    ⟨InsideST.of_inside (Inside.of_factor hF), fun z hz hzs hzt => by rw [hF.2 z hz]; exact hd z hzs hzt⟩
  have hdsF : deg F s = 1 := by rw [hF.2 s hsV]; exact hds
  have hst := conn_st hD2 hsV hdsF
  obtain ⟨cb1, cb2, cf1, cf2⟩ := isCell_corners hc s'
  have hcyc : (∀ z, Conn F (mkBF c s').d z → deg F z = 2) ∨
      (∀ z, Conn F (mkBF c s').a z → deg F z = 2) := by
    by_cases hd' : Conn F (front1 c s') s
    · right; exact class_deg2 hD2 hst cb1 (fun h => hn (h.trans hd'.symm))
    · left; exact class_deg2 hD2 hst cf1 hd'
  have hcount := merge_count (mkBF c s') hD2.1 cb1 cb2 cf1 cf2 hb hf hcyc hn
  have ha : Alt F c := by
    rw [lat1_eq] at hl1
    rw [lat2_eq] at hl2
    simp only [back, front] at hb hf
    obtain ⟨x, y⟩ := c
    cases s' <;> simp only [latA, latB, sideEdge, Side.opp] at hl1 hl2 hb hf <;> unfold Alt <;> tauto
  refine ⟨factor_flip hF (mkBF c s') hc hE hb hf hl1 hl2, by rw [hfe]; exact hcount, fun x hx => ?_⟩
  rcases (alt_iff_uniform F c).1 ha with hso | hsi
  · rw [D_flip_source hso]; simp [hx]
  · rw [D_flip_sink hsi]; simp [hx]

def MovePF (V : Finset Pt) (s t : Pt) (F F' : Finset Edge) : Prop :=
  (∃ σ : StripSpec, ValidStrip V F σ ∧
      (∀ j < σ.n, ¬ IsCorner s (cellJ σ.c σ.s j) ∧ ¬ IsCorner t (cellJ σ.c σ.s j)) ∧
      F' = applyS F σ ∧ ncomp V F' ≤ ncomp V F) ∨
  (∃ c, IsCell V c ∧ ¬ IsCorner s c ∧ ¬ IsCorner t c ∧ ¬ NotTypeIII V F c ∧ F' = ULHC.flip F c)

lemma ncomp_pos {V : Finset Pt} {F : Finset Edge} {s : Pt} (hs : s ∈ V) : 1 ≤ ncomp V F := by
  unfold ncomp
  exact Finset.card_pos.2 ⟨_, Finset.mem_image_of_mem _ hs⟩

-- **Theorem A for path-factors.**
--
theorem theoremA_pf {V : Finset Pt} {d : Pt → ℕ} {H : Finset Edge} (hs : Solid V)
    (hH : IsFactor V d H) (hHam : ncomp V H = 1) {s t : Pt}
    (hd : ∀ z, z ≠ s → z ≠ t → d z = 2) (hds : d s = 1) (hsV : s ∈ V) :
    ∀ F, IsFactor V d F → (∀ w, IsCorner s w ∨ IsCorner t w → D F H w = 0) →
      ∃ F', Relation.ReflTransGen (MovePF V s t) F F' ∧ IsFactor V d F' ∧
        (ncomp V F' = 1 ∨
          ∃ c, IsCell V c ∧ (IsCorner s c ∨ IsCorner t c) ∧ ¬ NotTypeIII V F' c) := by
  suffices key : ∀ n m (F : Finset Edge), ncomp V F = n → mu V F H = m → IsFactor V d F →
      (∀ w, IsCorner s w ∨ IsCorner t w → D F H w = 0) →
      ∃ F', Relation.ReflTransGen (MovePF V s t) F F' ∧ IsFactor V d F' ∧
        (ncomp V F' = 1 ∨
          ∃ c, IsCell V c ∧ (IsCorner s c ∨ IsCorner t c) ∧ ¬ NotTypeIII V F' c) from
    fun F hF hz => key _ _ F rfl rfl hF hz
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ihn =>
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ihm =>
  intro F hn hm hF hz
  by_cases h1 : ncomp V F ≤ 1
  · exact ⟨F, Relation.ReflTransGen.refl, hF, Or.inl (by have := ncomp_pos (F := F) hsV; omega)⟩
  by_cases hA : ∃ c, IsCell V c ∧ ¬ IsCorner s c ∧ ¬ IsCorner t c ∧ ¬ NotTypeIII V F c
  · obtain ⟨c, hc, hcs, hct, hc3⟩ := hA
    obtain ⟨hF', hcnt, hDoff⟩ := typeIII_flip (H := H) hF hd hds hsV hc hc3
    have hz' : ∀ w, IsCorner s w ∨ IsCorner t w → D (ULHC.flip F c) H w = 0 := by
      intro w hw
      have hwc : w ≠ c := by
        rintro rfl; rcases hw with h | h
        · exact hcs h
        · exact hct h
      rw [hDoff w hwc]; exact hz w hw
    obtain ⟨F', hr, hF'', hfin⟩ :=
      ihn (ncomp V (ULHC.flip F c)) (by omega) _ _ rfl rfl hF' hz'
    exact ⟨F', Relation.ReflTransGen.head (Or.inr ⟨c, hc, hcs, hct, hc3, rfl⟩) hr, hF'', hfin⟩
  by_cases hB : ∃ c, IsCell V c ∧ (IsCorner s c ∨ IsCorner t c) ∧ ¬ NotTypeIII V F c
  · exact ⟨F, Relation.ReflTransGen.refl, hF, Or.inr hB⟩
  have hT : NoTypeIII V F := by
    intro c hc
    by_contra h
    by_cases hcor : IsCorner s c ∨ IsCorner t c
    · exact hB ⟨c, hc, hcor, h⟩
    · push Not at hcor; exact hA ⟨c, hc, hcor.1, hcor.2, h⟩
  obtain ⟨σ, hv, hn2, hmu, hcor, hle, _, _, o, hp, hg⟩ :=
    lemmaB hs hF hH hHam hd hds hsV hz hT (by omega)
  have hF' : IsFactor V d (applyS F σ) := factor_flipCol σ.n F hF hv.2.1 hv.2.2.1
  have hz' : ∀ w, IsCorner s w ∨ IsCorner t w → D (applyS F σ) H w = 0 := by
    intro w hw
    unfold applyS
    rw [strip_D_off hp σ.n hv.2.1 hg w (fun j hj heq => by
      rcases hw with h | h
      · exact (hcor j hj).1 (heq ▸ h)
      · exact (hcor j hj).2 (heq ▸ h))]
    exact hz w hw
  have hmove : MovePF V s t F (applyS F σ) := Or.inl ⟨σ, hv, hcor, rfl, hle⟩
  by_cases hlt : ncomp V (applyS F σ) < ncomp V F
  · obtain ⟨F', hr, hF'', hfin⟩ := ihn _ (by omega) _ _ rfl rfl hF' hz'
    exact ⟨F', Relation.ReflTransGen.head hmove hr, hF'', hfin⟩
  · obtain ⟨F', hr, hF'', hfin⟩ := ihm (mu V (applyS F σ) H) (by omega) _ (by omega) rfl hF' hz'
    exact ⟨F', Relation.ReflTransGen.head hmove hr, hF'', hfin⟩

end HP

end ULHC

namespace ULHC

open Finset Classical

namespace HP

-- **From a stuck state to a Hamiltonian path.** If the fence at a cell `b` around `t` meets the
-- two conditions of `after_fence_strip` for some Hamiltonian path `H` (`D F H b = -2`, and `H`
-- uses the flipped factor's edges at `t`), then moves away from the endpoints lead from the
-- flipped factor to a Hamiltonian path, or to a Type III cell at an endpoint.
--
theorem fence_then_finish {V : Finset Pt} {d : Pt → ℕ} {F H : Finset Edge} (hs : Solid V)
    (hF : IsFactor V d F) (hH : IsFactor V d H) (hHam : ncomp V H = 1) {s t b : Pt}
    (hd : ∀ z, z ≠ s → z ≠ t → d z = 2) (hds : d s = 1) (hsV : s ∈ V)
    (hsfree : ∀ w, IsCorner s w → ¬ IsCell V w)
    (hall : ∀ c, AncP F b c → IsCell V c) (hbt : IsCorner t b) (hDb : D F H b = -2)
    (hag : ∀ e, (e = eR t ∨ e = eL t ∨ e = eU t ∨ e = eD t) →
      (e ∈ rflip F ((cells V).filter (AncP F b)) ↔ e ∈ H)) :
    IsFactor V d (rflip F ((cells V).filter (AncP F b))) ∧
    ∃ F', Relation.ReflTransGen (MovePF V s t) (rflip F ((cells V).filter (AncP F b))) F' ∧
      IsFactor V d F' ∧
      (ncomp V F' = 1 ∨ ∃ c, IsCell V c ∧ (IsCorner s c ∨ IsCorner t c) ∧ ¬ NotTypeIII V F' c) := by
  set R := (cells V).filter (AncP F b) with hRdef
  obtain ⟨hF', hbR, hcl, _, _⟩ := smallest_fence hF hall
  have hO := outR_of_closed hcl
  have hb0 : D (rflip F R) H b = 0 := by
    rw [D_rflip hO b]; unfold rin; simp [hbR, hDb]
  obtain ⟨c1, c2, c3⟩ := D_const_at hF' hH hag
  have ht0 : D (rflip F R) H t = 0 := by
    rcases isCorner_cases hbt with rfl | rfl | rfl | rfl
    · exact hb0
    · rw [← c1]; exact hb0
    · rw [← c2]; exact hb0
    · rw [← c3]; exact hb0
  have hz : ∀ w, IsCorner s w ∨ IsCorner t w → D (rflip F R) H w = 0 := by
    intro w hw
    rcases hw with hw | hw
    · exact D_eq_zero_of_not_cell hF' hH hs (hsfree w hw)
    · rcases isCorner_cases hw with rfl | rfl | rfl | rfl
      · exact ht0
      · rw [c1]; exact ht0
      · rw [c2]; exact ht0
      · rw [c3]; exact ht0
  exact ⟨hF', theoremA_pf hs hH hHam hd hds hsV _ hF' hz⟩

end HP

end ULHC
