/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
import SolidGridHam.Cycle.NearLemma

/-!
# Chain links

A link `b → c` is a *chain link* when a cell of `c` shares a side with `b`'s end cell `u`.
`ChainOK b c` allows this only for `c`'s start cell and only along a lateral side of `u`
(the sides that are dark before `u` is flipped). Paths in the class `CRPathCA` have
`ChainOK` links throughout; the class is closed under prepending a strip.

* `chain_lat`: the shared side is a lateral side of the start cell (not its back or front).
* `chain_sig`: the pattern of `c` holds in the factor itself from index 1 on, and at the
  start cell except on the shared side.
* `chain_conn`: in a Type III-free factor, a start cell with dark back and one dark lateral
  side, followed by the strip's pattern, has its `lat1` corners joined (through the shared
  side and the next cell). This gives the joined half of the created condition in every
  clean state, with no condition from the first strip.
-/

namespace SolidGridHam

open Finset

def ChainOK (b c : StripSpec) : Prop :=
  ∀ j < c.n, ∀ x ∈ cellE (cellJ c.c c.s j), x ∈ cellE (endCell b) →
    j = 0 ∧ (x = lat1 (endCell b) b.s ∨ x = lat2 (endCell b) b.s)

def CATail : List StripSpec → Prop
  | [] => True
  | [_] => True
  | b :: c :: L => ChainOK b c ∧ CATail (c :: L)

def CRPathCA (V : Finset Pt) (G : Finset Edge) (σ : StripSpec) (L : List StripSpec) : Prop :=
  CRPath V G σ L ∧ CATail (σ :: L)

lemma chainOK_of_noChain {b c : StripSpec} (h : NoChain b c) : ChainOK b c :=
  fun j hj x hx hx' => absurd hx' (h j hj x hx)

-- A cell and its neighbour across a side share only that side.
--
lemma shared_unique {d u : Pt} {tf : Side} (hu : u = nb d tf) {x : Edge} (hx : x ∈ cellE d)
    (hx' : x ∈ cellE u) : x = sideEdge d tf := by
  subst hu
  obtain ⟨p, q⟩ := d
  rw [cellE_frame (p, q) tf] at hx
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exfalso; revert hx'
    cases tf <;> simp [cellE, back, sideEdge, nb, Side.opp, bot, top, lft, rgt] <;> omega
  · rfl
  · exfalso; revert hx'
    cases tf <;> simp [cellE, lat1, nb, bot, top, lft, rgt] <;> omega
  · exfalso; revert hx'
    cases tf <;> simp [cellE, lat2, nb, bot, top, lft, rgt] <;> omega

lemma frame_ne (d : Pt) (tf : Side) : back d tf ≠ lat1 d tf ∧ back d tf ≠ lat2 d tf ∧
    front d tf ≠ lat1 d tf ∧ front d tf ≠ lat2 d tf ∧ lat1 d tf ≠ lat2 d tf ∧ back d tf ≠ front d tf := by
  obtain ⟨p, q⟩ := d
  cases tf <;> simp [back, front, lat1, lat2, sideEdge, Side.opp, bot, top, lft, rgt]

-- Two distinct cells share at most one side.
--
lemma inter_unique {d u : Pt} (hne : d ≠ u) {x y : Edge} (hx : x ∈ cellE d) (hxu : x ∈ cellE u)
    (hy : y ∈ cellE d) (hyu : y ∈ cellE u) : x = y := by
  have hnb : ∃ t', u = nb d t' := by
    rw [cellE_frame d .t] at hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    have hside : ∀ t', x = sideEdge d t' → ∃ t'', u = nb d t'' := fun t' h =>
      ⟨t', (cell_of_side d (tf := t') (h ▸ hxu)).resolve_left (Ne.symm hne)⟩
    rcases hx with rfl | rfl | rfl | rfl
    · exact hside _ rfl
    · exact hside _ rfl
    · exact hside _ (lat1_eq _ _)
    · exact hside _ (lat2_eq _ _)
  obtain ⟨t', ht'⟩ := hnb
  rw [shared_unique ht' hx hxu, shared_unique ht' hy hyu]

section chain

variable {V : Finset Pt} {G : Finset Edge}

-- In a chain link the shared side is a lateral side of the start cell.
--
theorem chain_lat {b c : StripSpec} (hl : CR2 V G b c) (hok : ChainOK b c)
    (hlu : lat1 (endCell b) b.s ∈ G ∧ lat2 (endCell b) b.s ∈ G) {x : Edge}
    (hx : x ∈ cellE c.c) (hxu : x ∈ cellE (endCell b)) :
    x = lat1 c.c c.s ∨ x = lat2 c.c c.s := by
  have hx0 : x ∈ cellE (cellJ c.c c.s 0) := by rw [cellJ_zero]; exact hx
  obtain ⟨_, hxl⟩ := hok 0 hl.2.2.1 x hx0 hxu
  have hxG : x ∈ G := by rcases hxl with rfl | rfl; exacts [hlu.1, hlu.2]
  have hxF : x ∉ flip G (endCell b) := by
    rw [mem_flip_iff]; intro h; exact (h.1 hxG) hxu
  obtain ⟨hb, hlt, hf⟩ := hl.2.2.2.1
  rw [cellE_frame c.c c.s] at hx
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact absurd hb hxF
  · exfalso
    have hf0 := hf 0 hl.2.2.1
    rw [cellJ_zero] at hf0
    by_cases h1 : 1 < c.n
    · -- The next cell would be `b`'s end cell.
      --
      have hc1 : cellJ c.c c.s 1 = endCell b := by
        rcases cell_of_side c.c (tf := c.s) hxu with h | h
        · exfalso
          have := hl.2.2.2.2.2.2.1 0 hl.2.2.1
          rw [cellJ_zero] at this; exact this h.symm
        · rw [h]
          have := nb_cellJ c.c c.s 0
          rw [cellJ_zero] at this; exact this.symm
      exact hl.2.2.2.2.2.2.1 1 h1 hc1
    · exact hxF (hf0.2 ⟨fun h => by omega, fun h => by omega⟩)
  · exact Or.inl rfl
  · exact Or.inr rfl

-- The pattern of a chain strip in `G` itself, from index 1.
--
theorem chain_sig {b c : StripSpec} (hl : CR2 V G b c) (hok : ChainOK b c) :
    SigFrom G c.c c.s c.n 1 := by
  intro i hi hin
  have hoff : ∀ x ∈ cellE (cellJ c.c c.s i), (x ∈ flip G (endCell b) ↔ x ∈ G) := by
    intro x hx
    refine mem_flip_off (fun hxu => ?_)
    have := (hok i hin x hx hxu).1; omega
  have hsig := strip_sig hl.2.2.2.1 hin
  have mem : ∀ y, y = lat1 (cellJ c.c c.s i) c.s ∨ y = lat2 (cellJ c.c c.s i) c.s ∨
      y = back (cellJ c.c c.s i) c.s ∨ y = front (cellJ c.c c.s i) c.s →
      y ∈ cellE (cellJ c.c c.s i) := by
    intro y hy; rw [cellE_frame _ c.s]; rcases hy with rfl | rfl | rfl | rfl <;> simp
  obtain ⟨g1, g2, gb, gf⟩ := hsig
  rw [hoff _ (mem _ (Or.inl rfl))] at g1
  rw [hoff _ (mem _ (Or.inr (Or.inl rfl)))] at g2
  rw [hoff _ (mem _ (Or.inr (Or.inr (Or.inl rfl))))] at gb
  rw [hoff _ (mem _ (Or.inr (Or.inr (Or.inr rfl))))] at gf
  exact ⟨g1, g2, gb, gf⟩

-- The start cell of a chain strip, read in `G`.
--
theorem chain_start {b c : StripSpec} (hl : CR2 V G b c) (hok : ChainOK b c)
    (hlu : lat1 (endCell b) b.s ∈ G ∧ lat2 (endCell b) b.s ∈ G) {x : Edge}
    (hx : x ∈ cellE c.c) (hxu : x ∈ cellE (endCell b)) :
    x ∈ G ∧ (x = lat1 c.c c.s ∨ x = lat2 c.c c.s) ∧ back c.c c.s ∈ G ∧
      (front c.c c.s ∈ G ↔ c.n = 1) ∧
      ((lat1 c.c c.s ∈ G ∧ lat2 c.c c.s ∉ G) ∨ (lat2 c.c c.s ∈ G ∧ lat1 c.c c.s ∉ G)) := by
  have hx0 : x ∈ cellE (cellJ c.c c.s 0) := by rw [cellJ_zero]; exact hx
  obtain ⟨_, hxl⟩ := hok 0 hl.2.2.1 x hx0 hxu
  have hxG : x ∈ G := by rcases hxl with rfl | rfl; exacts [hlu.1, hlu.2]
  have hxlat := chain_lat hl hok hlu hx hxu
  have hne0 : c.c ≠ endCell b := by have := hl.2.2.2.2.2.2.1 0 hl.2.2.1; rwa [cellJ_zero] at this
  have hother : ∀ y ∈ cellE c.c, y ≠ x → (y ∈ flip G (endCell b) ↔ y ∈ G) :=
    fun y hy hyx => mem_flip_off (fun hyu => hyx (inter_unique hne0 hy hyu hx hxu))
  have memc : ∀ y, y = lat1 c.c c.s ∨ y = lat2 c.c c.s ∨ y = back c.c c.s ∨
      y = front c.c c.s → y ∈ cellE c.c := by
    intro y hy; rw [cellE_frame _ c.s]; rcases hy with rfl | rfl | rfl | rfl <;> simp
  obtain ⟨n1, n2, n3, n4, n5, _⟩ := frame_ne c.c c.s
  have hpat := hl.2.2.2.1
  have hl0 := hpat.2.1 0 hl.2.2.1
  have hf0 := hpat.2.2 0 hl.2.2.1
  rw [cellJ_zero] at hl0 hf0
  have hbx : back c.c c.s ≠ x := by rcases hxlat with rfl | rfl; exacts [n1, n2]
  have hfx : front c.c c.s ≠ x := by rcases hxlat with rfl | rfl; exacts [n3, n4]
  refine ⟨hxG, hxlat, ?_, ?_, ?_⟩
  · rw [← hother _ (memc _ (Or.inr (Or.inr (Or.inl rfl)))) hbx]; exact hpat.1
  · rw [← hother _ (memc _ (Or.inr (Or.inr (Or.inr rfl)))) hfx, hf0]
    have hn1 := hl.2.2.1
    constructor
    · intro h; by_contra hn; have := h.2 (by omega); omega
    · intro h; exact ⟨fun h' => by omega, fun h' => by omega⟩
  · rcases hxlat with h | h
    · left; refine ⟨h ▸ hxG, fun h2 => ?_⟩
      have : lat2 c.c c.s ∈ flip G (endCell b) :=
        (hother _ (memc _ (Or.inr (Or.inl rfl))) (fun he => n5 (h ▸ he.symm))).2 h2
      have := hl0.2.1 this; omega
    · right; refine ⟨h ▸ hxG, fun h1 => ?_⟩
      have : lat1 c.c c.s ∈ flip G (endCell b) :=
        (hother _ (memc _ (Or.inl rfl)) (fun he => n5 (he.trans h))).2 h1
      have := hl0.1.1 this; omega

end chain

section conn

variable {V : Finset Pt} {S : Finset Edge}

-- The start pair of a strip-like run is joined when its start cell has a dark back and a dark
-- lateral side (and the other lateral side light): through the dark side, or through the next
-- cell.
--
theorem chain_conn (_hS : Deg2 V S) (hT : NoTypeIII V S) {d : Pt} {tf : Side} {m : ℕ}
    (hm : 1 ≤ m) (hsig : SigFrom S d tf m 1) (hcell : 2 ≤ m → IsCell V (cellJ d tf 1))
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
    have hall := alt_corners_conn hT hc (alt_of_lats l1 l2 bF fF)
    have hbb := (frame_of_allConn hall tf).1
    rw [← c1, back1_nb, back2_nb] at hbb
    exact hbb.symm
  · have fr : front (cellJ d tf 1) tf ∈ S := gf.2 ⟨fun _ => by omega, fun _ => rfl⟩
    rw [← c1] at l1 l2 fr
    exact (((e2.conn l2).trans ((ends_front _ tf).conn fr).symm).trans (e1.conn l1).symm)

end conn

-- Far conditions for the class CA: the no-split condition is needed only for links without a
-- shared side (chain links are created in every clean state).
--
def FarLinkCA (G : Finset Edge) (a σ τ : StripSpec) : Prop :=
  (∀ j < a.n, ∀ e ∈ cellE (endCell σ), e ∉ cellE (cellJ a.c a.s j)) ∧
    ¬ IsMid a.c a.s (a.n - 2) (back1 (endCell σ) σ.s) ∧
    ¬ IsMid a.c a.s (a.n - 2) (back2 (endCell σ) σ.s) ∧
    (∀ i < τ.n, ∀ j < a.n, ∀ e ∈ cellE (cellJ τ.c τ.s i), e ∉ cellE (cellJ a.c a.s j)) ∧
    ¬ IsMid a.c a.s (a.n - 2) (back1 τ.c τ.s) ∧ ¬ IsMid a.c a.s (a.n - 2) (front1 τ.c τ.s) ∧
    (NoChain σ τ → ¬ (Conn G (back1 τ.c τ.s) (front1 τ.c τ.s) ∧
      ¬ Conn (flip G (endCell a)) (back1 τ.c τ.s) (front1 τ.c τ.s)))

def FarChainCA (G : Finset Edge) (a : StripSpec) : StripSpec → List StripSpec → Prop
  | _, [] => True
  | σ, τ :: L => FarLinkCA G a σ τ ∧ FarChainCA G a τ L

section transfer

variable {V : Finset Pt} {G : Finset Edge} (hG : Deg2 V G) (hT : NoTypeIII V G)
  {a : StripSpec} (ha : ValidStrip V G a) (hae : a.n % 2 = 0) (ha2 : 2 ≤ a.n)
  (hT' : NoTypeIII V (applyS G a))
include hG hT ha hae ha2 hT'

-- One link `σ → τ` after `a`'s own link survives `a`'s flip.
--
theorem link_transfer_CA {σ τ : StripSpec} (hσ : EndOK V G σ) (hev : σ.n % 2 = 0)
    (hl : CR2 V G σ τ) (hok : ChainOK σ τ) (hfl : FarLinkCA G a σ τ) :
    CR2 V (applyS G a) σ τ := by
  obtain ⟨f1, f2, f3, f4, f5, f6, f7⟩ := hfl
  obtain ⟨h2, hev', hc1, hpatc, hcellc, hoff, hne, hendc, hm1, hm2, hxy, hsplit⟩ := hl
  obtain ⟨k, hk⟩ : ∃ k, a.n = k + 2 := ⟨a.n - 2, by omega⟩
  obtain ⟨_, hpata, hcella, hsepa⟩ := ha
  have hpata' := hpata
  have hend : endCell a = cellJ a.c a.s (k + 1) := by unfold endCell; rw [hk]; rfl
  rw [hk] at hpata f1 f2 f3 f4 f5 f6
  have hcellk : ∀ j < k + 2, IsCell V (cellJ a.c a.s j) := by rw [← hk]; exact hcella
  rw [hend] at f7
  have hcella' : ∀ j ≤ k + 1, IsCell V (cellJ a.c a.s j) := fun j hj => hcellk j (by omega)
  have hk2 : k % 2 = 0 := by omega
  have hsame := end_same hT hk2 hcella' hpata
  have hT'' : NoTypeIII V (flipCol G a.c a.s (k + 2)) := by
    unfold applyS at hT'; rwa [hk] at hT'
  obtain ⟨hu, lu1, lu2, bu, fu⟩ := hσ hev
  have hsu : Conn G (back1 (endCell σ) σ.s) (back2 (endCell σ) σ.s) := by
    have hall : AllConn G (endCell σ) := by
      unfold AllConn; exact alt_corners_conn' (V := V) (hT _ hu) (alt_of_lats lu1 lu2 bu fu)
    exact (frame_of_allConn hall σ.s).1
  have hm2' : ¬ IsMid a.c a.s k (back1 (endCell σ) σ.s) := by simpa using f2
  have hm3' : ¬ IsMid a.c a.s k (back2 (endCell σ) σ.s) := by simpa using f3
  have hx' : ¬ IsMid a.c a.s k (back1 τ.c τ.s) := by simpa using f5
  have hy' : ¬ IsMid a.c a.s k (front1 τ.c τ.s) := by simpa using f6
  have hfar' : ∀ j ≤ k + 1, ∀ e ∈ cellE (endCell σ), e ∉ cellE (cellJ a.c a.s j) :=
    fun j hj e he => f1 j (by omega) e he
  -- Sides of `τ` and of `σ`'s end cell are not sides of `a`'s cells.
  --
  have hkeepτ : ∀ i < τ.n, ∀ e ∈ cellE (cellJ τ.c τ.s i), (e ∈ applyS G a ↔ e ∈ G) := by
    intro i hi e he
    unfold applyS; rw [hk, mem_flipCol, nOn_zero a.c a.s (fun j hj => f4 i hi j (by omega) e he)]
    simp
  have hpat' : StripPat (flip (applyS G a) (endCell σ)) τ.c τ.s τ.n := by
    obtain ⟨n, hn⟩ : ∃ n, τ.n = n + 1 := ⟨τ.n - 1, by omega⟩
    rw [hn] at hpatc ⊢
    refine (stripPat_congr (fun i hi e he => ?_)).2 hpatc
    rw [mem_flip_iff, mem_flip_iff, hkeepτ i (by omega) e he]
  have hsplit' : ¬ Conn (flip (applyS G a) (endCell σ)) (back1 τ.c τ.s) (front1 τ.c τ.s) := by
    unfold applyS; rw [hk]
    exact osi_split hG hk2 hcella' hpata hsepa hsame hT'' hu lu1 lu2 bu fu hsu hfar' hm2' hm3'
      hxy hsplit hx' hy'
  have hconn' : Conn (applyS G a) (back1 τ.c τ.s) (front1 τ.c τ.s) := by
    by_cases hnc : NoChain σ τ
    · have hosi := osi_far hG hk2 hcella' hpata hsepa hsame hT'' hu lu1 lu2 bu fu hsu hfar'
        hm2' hm3' hxy hsplit hx' hy'
      unfold applyS; rw [hk]
      rcases hosi with h | h
      · exact h.1
      · exact absurd ⟨hxy, h⟩ (f7 hnc)
    · -- A chain link: the start pair is joined through the shared side.
      --
      unfold NoChain at hnc
      push Not at hnc
      obtain ⟨j, hj, x, hx, hxu⟩ := hnc
      obtain ⟨rfl, hxl⟩ := hok j hj x hx hxu
      rw [cellJ_zero] at hx
      have hxlat := chain_lat ⟨h2, hev', hc1, hpatc, hcellc, hoff, hne, hendc, hm1, hm2, hxy,
        hsplit⟩ hok ⟨lu1, lu2⟩ hx hxu
      have hxG : x ∈ G := by rcases hxl with rfl | rfl; exacts [lu1, lu2]
      have hsig := chain_sig ⟨h2, hev', hc1, hpatc, hcellc, hoff, hne, hendc, hm1, hm2, hxy,
        hsplit⟩ hok
      have hc0 : ∀ e ∈ cellE τ.c, (e ∈ applyS G a ↔ e ∈ G) := fun e he =>
        hkeepτ 0 hc1 e (by rw [cellJ_zero]; exact he)
      have hsig' : SigFrom (applyS G a) τ.c τ.s τ.n 1 := by
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
      -- At the start cell, sides other than `x` keep their pattern value in `G`.
      --
      have hne0 : τ.c ≠ endCell σ := by
        have := hne 0 hc1; rwa [cellJ_zero] at this
      have hother : ∀ y ∈ cellE τ.c, y ≠ x → (y ∈ flip G (endCell σ) ↔ y ∈ G) :=
        fun y hy hyx => mem_flip_off (fun hyu => hyx (inter_unique hne0 hy hyu hx hxu))
      obtain ⟨n1, n2, n3, n4, _, _⟩ := frame_ne τ.c τ.s
      have hbx : back τ.c τ.s ≠ x := by rcases hxlat with rfl | rfl; exacts [n1, n2]
      have hfx : front τ.c τ.s ≠ x := by rcases hxlat with rfl | rfl; exacts [n3, n4]
      have hb0 : back τ.c τ.s ∈ applyS G a := by
        rw [hc0 _ (memc _ (Or.inr (Or.inr (Or.inl rfl)))),
          ← hother _ (memc _ (Or.inr (Or.inr (Or.inl rfl)))) hbx]
        exact hpatc.1
      have hf0 : front τ.c τ.s ∈ applyS G a ↔ τ.n = 1 := by
        rw [hc0 _ (memc _ (Or.inr (Or.inr (Or.inr rfl)))),
          ← hother _ (memc _ (Or.inr (Or.inr (Or.inr rfl)))) hfx]
        have := hpatc.2.2 0 hc1
        rw [cellJ_zero] at this
        rw [this]; omega
      have hx0 : lat1 τ.c τ.s ∈ applyS G a ∨ lat2 τ.c τ.s ∈ applyS G a := by
        rcases hxlat with h | h
        · left; rw [← h, hc0 _ hx]; exact hxG
        · right; rw [← h, hc0 _ hx]; exact hxG
      have hGa : Deg2 V (applyS G a) := by
        unfold applyS; exact deg2_flipCol _ G hG hpata' hcella
      exact chain_conn hGa hT' hc1 hsig' (fun h => hcellc 1 (by omega)) hb0 hf0 hx0
  exact ⟨h2, hev', hc1, hpat', hcellc, hoff, hne, hendc, hm1, hm2, hconn', hsplit'⟩

theorem chain_transfer_CA : ∀ (L : List StripSpec) (σ : StripSpec),
    EndOK V G σ → CRChain V G σ L → CATail (σ :: L) → FarChainCA G a σ L →
      CRChain V (applyS G a) σ L := by
  intro L
  induction L with
  | nil => intro σ _ h _ _; exact h
  | cons τ L ih =>
    intro σ hσ hch hcat hfar
    obtain ⟨hev, hl, hrest⟩ := hch
    exact ⟨hev, link_transfer_CA hG hT ha hae ha2 hT' hσ hev hl hcat.1 hfar.1,
      ih τ (endOK_of_link hl) hrest hcat.2 hfar.2⟩

theorem progress_step_CA {b : StripSpec} {L : List StripSpec} (hch : CRChain V G a (b :: L))
    (hcat : CATail (a :: b :: L)) (hfar : FarChainCA G a b L) :
    CRPathCA V (applyS G a) b L ∧ wt b L + a.n = wt a (b :: L) := by
  obtain ⟨_, hl, hrest⟩ := hch
  refine ⟨⟨⟨link_step hG hT ha hl, chain_transfer_CA hG hT ha hae ha2 hT' L b (endOK_of_link hl)
    hrest hcat.2 hfar⟩, hcat.2⟩, ?_⟩
  simp [wt]; ring

end transfer

end SolidGridHam
