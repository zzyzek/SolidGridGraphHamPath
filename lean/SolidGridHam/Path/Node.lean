/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
module

public import SolidGridHam.Path.HalfBridge
public import SolidGridHam.Algorithm

@[expose] public section

/-!
# Nodes of pairs along a phase (docs/S4_UNDO.md §I.2)

`seqH H0 BS`: the state after the bridges `BS` (newest first). For a pair `x, y` apart at the end,
`node H0 BS x y` is the number of bridges after which they first fall apart (0: apart in `H0`).
* `node_lt`: the node is at most the number of bridges, and the pair is apart from the node on.
* `sameNode`: a pair matched in the last state with the pair `(β, φ)` of the newest bridge's
  flipped square, and apart, has the newest node.
-/

namespace SolidGridHam

namespace HP

open Finset Classical

def seqH (H0 : Finset Edge) : List Bridge → Finset Edge
  | [] => H0
  | b :: BS => flip (seqH H0 BS) b.E

lemma seqH_of_reach {V : Finset Pt} {H0 H : Finset Edge} {BS : List Bridge}
    (hr : Reach V H0 H BS) : H = seqH H0 BS := by
  induction hr with
  | base => rfl
  | step _ _ _ _ ih => simp [seqH, ih]

-- The node of a pair: the number of bridges after which it is first apart.
--
noncomputable def node (H0 : Finset Edge) : List Bridge → Pt → Pt → ℕ
  | [], _, _ => 0
  | _ :: BS, x, y => if Conn (seqH H0 BS) x y then BS.length + 1 else node H0 BS x y

lemma node_le (H0 : Finset Edge) : ∀ (BS : List Bridge) (x y : Pt), node H0 BS x y ≤ BS.length
  | [], _, _ => le_rfl
  | b :: BS, x, y => by
    simp only [node, List.length_cons]
    split_ifs
    · exact le_rfl
    · exact (node_le H0 BS x y).trans (Nat.le_succ _)

-- The node as a bridge (`none`: apart in `H0`).
--
noncomputable def nodeB (H0 : Finset Edge) : List Bridge → Pt → Pt → Option Bridge
  | [], _, _ => none
  | b :: BS, x, y => if Conn (seqH H0 BS) x y then some b else nodeB H0 BS x y

def Matched (R : Pt → Pt → Prop) (x y a b : Pt) : Prop := (R x a ∧ R y b) ∨ (R x b ∧ R y a)

section nodes

variable {V W : Finset Pt} {d : Pt → ℕ} {t0 u0 : Pt} {H0 : Finset Edge}

-- Suffixes of a reachable bridge list are reachable.
--
lemma reach_suffix : ∀ {pre BS : List Bridge} {H : Finset Edge}, Reach V H0 H (pre ++ BS) →
    Reach V H0 (seqH H0 BS) BS
  | [], BS, H, h => by
    rw [List.nil_append] at h; rw [← seqH_of_reach h]; exact h
  | b :: pre, BS, H, h => by
    cases h with
    | step hr _ _ _ => exact reach_suffix hr

variable (hVW : V ⊆ W) (hdc : ∀ q, IsCell V q → ∀ z, IsCorner z q → d z = 2)
  (h0 : IsFactor W d H0) (hout0 : ∀ e ∈ H0, (e.p ∉ V → e.q = t0 ∨ e.q = u0) ∧ (e.q ∉ V → e.p = t0 ∨ e.p = u0))
include hVW hdc h0 hout0

-- The newest step: the state before it is the state after it with `β`, `φ` merged.
--
lemma reach_cons {b : Bridge} {L : List Bridge} {H : Finset Edge} (hr : Reach V H0 H (b :: L)) :
    Reach V H0 (seqH H0 L) L ∧ RowStep V (seqH H0 L) b ∧ H = flip (seqH H0 L) b.E ∧
      (∀ x y, Conn (seqH H0 L) x y ↔ merge (Conn H) (back1 b.E b.a) (front1 b.E b.a) x y) ∧
      ¬ Conn H (back1 b.E b.a) (front1 b.E b.a) := by
  cases hr with
  | step hr' hrs _ _ =>
    rename_i Hp
    have e := seqH_of_reach hr'
    subst e
    have hinv := pinv_reach (t0 := t0) (u0 := u0) hVW hdc h0 hout0 hr'
    exact ⟨hr', hrs, rfl, step_rel hrs (degc_of hVW hdc hinv.fac), hrs.split⟩

-- Later states are finer.
--
lemma conn_suffix : ∀ {pre BS : List Bridge} {H : Finset Edge}, Reach V H0 H (pre ++ BS) →
    ∀ x y, Conn H x y → Conn (seqH H0 BS) x y
  | [], BS, H, h, x, y, hc => by
    rw [List.nil_append] at h; rw [← seqH_of_reach h]; exact hc
  | b :: pre, BS, H, h, x, y, hc => by
    obtain ⟨hr', _, _, hrel, _⟩ := reach_cons hVW hdc h0 hout0 h
    exact conn_suffix hr' x y ((hrel x y).2 (Or.inl hc))

-- **SameNode.** A pair apart at the end and matched there with the flipped-square pair of `b`
-- has node `b`.
--
theorem sameNode {pre post : List Bridge} {b : Bridge} {H : Finset Edge}
    (hr : Reach V H0 H (pre ++ b :: post)) {x y : Pt}
    (hm : Matched (Conn H) x y (back1 b.E b.a) (front1 b.E b.a)) (_hn : ¬ Conn H x y) :
    nodeB H0 (pre ++ b :: post) x y = some b := by
  have hsuf : Reach V H0 (seqH H0 (b :: post)) (b :: post) := reach_suffix hr
  obtain ⟨_, _, _, hrel, hsplit⟩ := reach_cons hVW hdc h0 hout0 hsuf
  have sub := conn_suffix hVW hdc h0 hout0 hr
  have hm' : Matched (Conn (seqH H0 (b :: post))) x y (back1 b.E b.a) (front1 b.E b.a) := by
    rcases hm with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨sub _ _ h1, sub _ _ h2⟩
    · exact Or.inr ⟨sub _ _ h1, sub _ _ h2⟩
  have hnb : ¬ Conn (seqH H0 (b :: post)) x y := by
    intro h
    apply hsplit
    rcases hm' with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact (h1.symm.trans h).trans h2
    · exact ((h2.symm.trans h.symm).trans h1)
  have hbefore : Conn (seqH H0 post) x y := by
    rw [hrel]
    rcases hm' with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inr (Or.inl ⟨h1, h2.symm⟩)
    · exact Or.inr (Or.inr ⟨h1, h2.symm⟩)
  -- Walk down `pre`: every state there is finer than the one after `b`.
  --
  clear hm _hn
  induction pre generalizing H with
  | nil =>
    simp only [List.nil_append, nodeB]
    rw [ite_eq_left hbefore]
  | cons c pre ih =>
    simp only [List.cons_append, nodeB]
    have hr' := (reach_cons hVW hdc h0 hout0 hr).1
    have hc : ¬ Conn (seqH H0 (pre ++ b :: post)) x y := fun h =>
      hnb (conn_suffix (pre := pre) hVW hdc h0 hout0 hr' x y h)
    rw [ite_eq_right hc]
    exact ih hr' (conn_suffix hVW hdc h0 hout0 hr')

-- The newest step, with the start rule.
--
omit hVW hdc h0 hout0 in
lemma reach_cons_nbs {b : Bridge} {L : List Bridge} {H : Finset Edge}
    (hr : Reach V H0 H (b :: L)) : ¬ BridgeSqL L b.q ∧ MergeOK V (seqH H0 L) L := by
  cases hr with
  | step hr' _ hm hnb =>
    have e := seqH_of_reach hr'
    subst e
    exact ⟨hnb, hm⟩

end nodes

-- The node as an index in the newest-first list (the list length: apart in `H0`).
--
noncomputable def nodeI (H0 : Finset Edge) : List Bridge → Pt → Pt → ℕ
  | [], _, _ => 0
  | _ :: BS, x, y => if Conn (seqH H0 BS) x y then 0 else nodeI H0 BS x y + 1

-- The plan with its decisions and pending pairs.
--
noncomputable def planA (H : Finset Edge) : List Bridge → Pt × Pt → List (Bool × (Pt × Pt))
  | [], _ => []
  | b :: BS, uv =>
    if Conn (flip H b.E) uv.1 uv.2 then (true, uv) :: planA (flip H b.E) BS (rowStartPair b)
    else (false, uv) :: planA (flip H b.E) BS uv

-- The node depends only on the connection of the pair in each state.
--
lemma nodeI_congr {H0 : Finset Edge} {x y x' y' : Pt} : ∀ BS : List Bridge,
    (∀ k, (Conn (seqH H0 (BS.drop k)) x y ↔ Conn (seqH H0 (BS.drop k)) x' y')) →
    nodeI H0 BS x y = nodeI H0 BS x' y'
  | [], _ => rfl
  | b :: BS, h => by
    simp only [nodeI]
    have h1 := h 1
    simp only [List.drop_succ_cons, List.drop_zero] at h1
    rw [h1]
    split_ifs
    · rfl
    · congr 1
      exact nodeI_congr BS (fun k => by have := h (k + 1); simpa using this)

lemma planA_length (H : Finset Edge) : ∀ (BS : List Bridge) (uv : Pt × Pt),
    (planA H BS uv).length = BS.length
  | [], _ => rfl
  | b :: BS, uv => by
    simp only [planA]; split_ifs <;> simp [planA_length]

section chain

variable {V W : Finset Pt} {d : Pt → ℕ} {t0 u0 : Pt} {H0 : Finset Edge}
  (hVW : V ⊆ W) (hdc : ∀ q, IsCell V q → ∀ z, IsCorner z q → d z = 2)
  (h0 : IsFactor W d H0) (hout0 : ∀ e ∈ H0, (e.p ∉ V → e.q = t0 ∨ e.q = u0) ∧ (e.q ∉ V → e.p = t0 ∨ e.p = u0))
include hVW hdc h0 hout0

lemma conn_drop {BS : List Bridge} {H : Finset Edge} (hr : Reach V H0 H BS) (k : ℕ) {x y : Pt}
    (h : Conn H x y) : Conn (seqH H0 (BS.drop k)) x y := by
  have e := List.take_append_drop k BS
  have hr2 : Reach V H0 H (BS.take k ++ BS.drop k) := by rw [e]; exact hr
  exact conn_suffix hVW hdc h0 hout0 hr2 x y h

-- A pair apart after the `k` newest bridges are removed has node at least `k`.
--
lemma nodeI_ge : ∀ (BS : List Bridge) (H : Finset Edge), Reach V H0 H BS → ∀ k x y,
    k ≤ BS.length → ¬ Conn (seqH H0 (BS.drop k)) x y → k ≤ nodeI H0 BS x y
  | [], _, _, k, x, y, hk, _ => by simp at hk; omega
  | b :: BS, H, hr, k, x, y, hk, h => by
    rcases k with _ | k
    · exact Nat.zero_le _
    · simp only [List.drop_succ_cons] at h
      have hr' := (reach_cons hVW hdc h0 hout0 hr).1
      have hn : ¬ Conn (seqH H0 BS) x y := fun hc => h (conn_drop hVW hdc h0 hout0 hr' k hc)
      simp only [nodeI, hn, ↓reduceIte]
      have := nodeI_ge BS _ hr' k x y (by simp at hk; omega) h
      omega

-- A pair joined before the bridge at index `k` and apart after it has node `k`.
--
lemma nodeI_eq : ∀ (BS : List Bridge) (H : Finset Edge), Reach V H0 H BS → ∀ k x y,
    k < BS.length → Conn (seqH H0 (BS.drop (k + 1))) x y → ¬ Conn (seqH H0 (BS.drop k)) x y →
    nodeI H0 BS x y = k
  | [], _, _, k, x, y, hk, _, _ => by simp at hk
  | b :: BS, H, hr, k, x, y, hk, hc, hn => by
    have hr' := (reach_cons hVW hdc h0 hout0 hr).1
    rcases k with _ | k
    · simp only [List.drop_succ_cons, List.drop_zero] at hc
      simp [nodeI, hc]
    · simp only [List.drop_succ_cons] at hc hn
      have hn' : ¬ Conn (seqH H0 BS) x y := fun h => hn (conn_drop hVW hdc h0 hout0 hr' k h)
      simp only [nodeI, hn', ↓reduceIte]
      rw [nodeI_eq BS _ hr' k x y (by simp at hk; omega) hc hn]

-- **The plan, entry by entry.** At index `k`, with pending pair `w`: the bridge is lowered iff `w`
-- is joined before it; `w` is apart after it; the next pending pair is the bridge's start pair if
-- lowered, else `w`.
--
theorem planA_get : ∀ (BS : List Bridge) (H : Finset Edge) (uv : Pt × Pt), Reach V H0 H BS →
    ¬ Conn H uv.1 uv.2 → ∀ k (hk : k < BS.length),
      let e := (planA H BS uv)[k]'(by rw [planA_length]; exact hk)
      (e.1 = true ↔ Conn (seqH H0 (BS.drop (k + 1))) e.2.1 e.2.2) ∧
        ¬ Conn (seqH H0 (BS.drop k)) e.2.1 e.2.2 ∧ (k = 0 → e.2 = uv) ∧
        ∀ (hk1 : k + 1 < BS.length), ((planA H BS uv)[k + 1]'(by rw [planA_length]; exact hk1)).2 =
          if e.1 then rowStartPair (BS[k]'hk) else e.2
  | [], _, _, _, _, k, hk => absurd hk (by simp)
  | b :: BS, H, uv, hr, hn, k, hk => by
    obtain ⟨hr', hrs, hH, _, _⟩ := reach_cons hVW hdc h0 hout0 hr
    have hHp : flip H b.E = seqH H0 BS := by rw [hH, flip_flip]
    by_cases hc : Conn (seqH H0 BS) uv.1 uv.2
    · have hp : planA H (b :: BS) uv = (true, uv) :: planA (seqH H0 BS) BS (rowStartPair b) := by
        simp only [planA, hHp, ite_eq_left hc]
      rcases k with _ | k
      · simp only [hp, List.getElem_cons_zero, List.drop_succ_cons, List.drop_zero, true_iff,
          List.getElem_cons_succ, ↓reduceIte]
        refine ⟨hc, by rw [← seqH_of_reach hr]; exact hn, fun _ => by simp, fun hk1 => ?_⟩
        rcases BS with _ | ⟨b', BS'⟩
        · simp at hk1
        · simp only [planA]; split_ifs <;> rfl
      · simp only [hp, List.getElem_cons_succ, List.drop_succ_cons]
        exact (planA_get BS _ (rowStartPair b) hr' hrs.crit.2.2.1 k (by simpa using hk)).imp id
          (fun h => ⟨h.1, fun h' => by omega, fun hk1 => h.2.2 (by simpa using hk1)⟩)
    · have hp : planA H (b :: BS) uv = (false, uv) :: planA (seqH H0 BS) BS uv := by
        simp only [planA, hHp, ite_eq_right hc]
      rcases k with _ | k
      · simp only [hp, List.getElem_cons_zero, List.drop_succ_cons, List.drop_zero,
          Bool.false_eq_true, false_iff, List.getElem_cons_succ, ↓reduceIte]
        refine ⟨hc, by rw [← seqH_of_reach hr]; exact hn, fun _ => by simp, fun hk1 => ?_⟩
        rcases BS with _ | ⟨b', BS'⟩
        · simp at hk1
        · simp only [planA]; split_ifs <;> rfl
      · simp only [hp, List.getElem_cons_succ, List.drop_succ_cons]
        exact (planA_get BS _ uv hr' hc k (by simpa using hk)).imp id
          (fun h => ⟨h.1, fun h' => by omega, fun hk1 => h.2.2 (by simpa using hk1)⟩)

-- The bridge at index `k` steps from the state before it.
--
lemma reach_at {BS : List Bridge} {H : Finset Edge} (hr : Reach V H0 H BS) {k : ℕ}
    (hk : k < BS.length) : Reach V H0 (seqH H0 (BS.drop (k + 1))) (BS.drop (k + 1)) ∧
      RowStep V (seqH H0 (BS.drop (k + 1))) (BS[k]'hk) ∧
      seqH H0 (BS.drop k) = flip (seqH H0 (BS.drop (k + 1))) (BS[k]'hk).E := by
  have e := List.take_append_drop k BS
  have hr2 : Reach V H0 H (BS.take k ++ BS.drop k) := by rw [e]; exact hr
  have hs := reach_suffix hr2
  rw [List.drop_eq_getElem_cons hk] at hs ⊢
  obtain ⟨h1, h2, h3, _⟩ := reach_cons hVW hdc h0 hout0 hs
  exact ⟨h1, h2, h3⟩

-- Decisions and pending pairs of the plan, by index.
--
noncomputable def lowAt (H : Finset Edge) (BS : List Bridge) (uv : Pt × Pt) (k : ℕ) : Bool :=
  ((planA H BS uv).getD k (false, uv)).1

noncomputable def pendAt (H : Finset Edge) (BS : List Bridge) (uv : Pt × Pt) (k : ℕ) : Pt × Pt :=
  ((planA H BS uv).getD k (false, uv)).2

lemma pend_facts {BS : List Bridge} {H : Finset Edge} {uv : Pt × Pt} (hr : Reach V H0 H BS)
    (hn : ¬ Conn H uv.1 uv.2) {k : ℕ} (hk : k < BS.length) :
    (lowAt H BS uv k = true ↔
        Conn (seqH H0 (BS.drop (k + 1))) (pendAt H BS uv k).1 (pendAt H BS uv k).2) ∧
      ¬ Conn (seqH H0 (BS.drop k)) (pendAt H BS uv k).1 (pendAt H BS uv k).2 ∧
      (k = 0 → pendAt H BS uv k = uv) ∧
      (k + 1 < BS.length → pendAt H BS uv (k + 1) =
        if lowAt H BS uv k then rowStartPair (BS[k]'hk) else pendAt H BS uv k) := by
  have hl : k < (planA H BS uv).length := by rw [planA_length]; exact hk
  obtain ⟨g1, g2, g3, g4⟩ := planA_get hVW hdc h0 hout0 BS H uv hr hn k hk
  unfold lowAt pendAt
  rw [List.getD_eq_getElem _ _ hl]
  refine ⟨g1, g2, g3, fun hk1 => ?_⟩
  rw [List.getD_eq_getElem _ _ (by rw [planA_length]; exact hk1)]
  exact g4 hk1

-- **K1/K2.** From index `j` on, the pending pair keeps its node until the first lowered bridge,
-- which is its node: an undone bridge at `i ≥ j` is never the node, and a lowered bridge at
-- `i ≥ j` bounds it.
--
theorem node_pend {BS : List Bridge} {H : Finset Edge} {uv : Pt × Pt} (hr : Reach V H0 H BS)
    (hn : ¬ Conn H uv.1 uv.2) : ∀ n j i, i - j = n → j ≤ i → i < BS.length →
      (lowAt H BS uv i = false → nodeI H0 BS (pendAt H BS uv j).1 (pendAt H BS uv j).2 ≠ i) ∧
      (lowAt H BS uv i = true → nodeI H0 BS (pendAt H BS uv j).1 (pendAt H BS uv j).2 ≤ i) := by
  intro n
  induction n with
  | zero =>
    intro j i hji hj hi
    obtain rfl : j = i := by omega
    obtain ⟨f1, f2, _, _⟩ := pend_facts hVW hdc h0 hout0 hr hn hi
    refine ⟨fun hlow => ?_, fun hlow => ?_⟩
    · have hc : ¬ Conn (seqH H0 (BS.drop (j + 1))) (pendAt H BS uv j).1 (pendAt H BS uv j).2 :=
        fun h => by rw [← f1] at h; rw [h] at hlow; exact absurd hlow (by simp)
      have := nodeI_ge hVW hdc h0 hout0 BS H hr (j + 1) _ _ (by omega) hc
      omega
    · rw [nodeI_eq hVW hdc h0 hout0 BS H hr j _ _ hi (f1.1 hlow) f2]
  | succ n ih =>
    intro j i hji hj hi
    obtain ⟨f1, f2, _, f4⟩ := pend_facts hVW hdc h0 hout0 hr hn (k := j) (by omega)
    by_cases hlj : lowAt H BS uv j = true
    · have he := nodeI_eq hVW hdc h0 hout0 BS H hr j _ _ (by omega) (f1.1 hlj) f2
      refine ⟨fun hlow => ?_, fun _ => by omega⟩
      rw [he]; omega
    · have hj1 : pendAt H BS uv (j + 1) = pendAt H BS uv j := by
        rw [f4 (by omega)]; simp [hlj]
      have := ih (j + 1) i (by omega) (by omega) hi
      rw [hj1] at this
      exact this

-- **SameNode, by index.** A pair apart after the bridge at `k` and matched there with its
-- flipped square's pair `(β, φ)` has node `k`.
--
theorem sameNodeI {BS : List Bridge} {H : Finset Edge} (hr : Reach V H0 H BS) {k : ℕ}
    (hk : k < BS.length) {x y : Pt}
    (hm : Matched (Conn (seqH H0 (BS.drop k))) x y (back1 (BS[k]'hk).E (BS[k]'hk).a)
      (front1 (BS[k]'hk).E (BS[k]'hk).a))
    (hn : ¬ Conn (seqH H0 (BS.drop k)) x y) : nodeI H0 BS x y = k := by
  obtain ⟨hrk, hrs, he⟩ := reach_at hVW hdc h0 hout0 hr hk
  have hinv := pinv_reach (t0 := t0) (u0 := u0) hVW hdc h0 hout0 hrk
  have rel := step_rel hrs (degc_of hVW hdc hinv.fac)
  rw [← he] at rel
  apply nodeI_eq hVW hdc h0 hout0 BS H hr k x y hk _ hn
  rw [rel]
  rcases hm with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inr (Or.inl ⟨h1, h2.symm⟩)
  · exact Or.inr (Or.inr ⟨h1, h2.symm⟩)

-- **Transfer.** A pair matched with `(x', y')`, after the bridge at the node `k` of `(x', y')`,
-- has node `k`.
--
theorem transferI {BS : List Bridge} {H : Finset Edge} (hr : Reach V H0 H BS) {k : ℕ}
    (hk : k < BS.length) {x y x' y' : Pt}
    (hc : Conn (seqH H0 (BS.drop (k + 1))) x' y') (hn : ¬ Conn (seqH H0 (BS.drop k)) x' y')
    (hm : Matched (Conn (seqH H0 (BS.drop k))) x y x' y') : nodeI H0 BS x y = k := by
  obtain ⟨hrk, hrs, he⟩ := reach_at hVW hdc h0 hout0 hr hk
  have hinv := pinv_reach (t0 := t0) (u0 := u0) hVW hdc h0 hout0 hrk
  have rel := step_rel hrs (degc_of hVW hdc hinv.fac)
  rw [← he] at rel
  have sub : ∀ u v, Conn (seqH H0 (BS.drop k)) u v → Conn (seqH H0 (BS.drop (k + 1))) u v :=
    fun u v h => (rel u v).2 (Or.inl h)
  apply nodeI_eq hVW hdc h0 hout0 BS H hr k x y hk
  · rcases hm with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ((sub _ _ h1).trans hc).trans (sub _ _ h2).symm
    · exact ((sub _ _ h1).trans hc.symm).trans (sub _ _ h2).symm
  · intro h
    apply hn
    rcases hm with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact (h1.symm.trans h).trans h2
    · exact ((h2.symm.trans h.symm).trans h1)

-- **SameNode from a finer state.** A pair matched with `(β, φ)` of the bridge at `k` in any state
-- `S m` with `m ≤ k` has node `k`.
--
theorem sameNodeI' {BS : List Bridge} {H : Finset Edge} (hr : Reach V H0 H BS) {k m : ℕ}
    (hk : k < BS.length) (hmk : m ≤ k) {x y : Pt}
    (hm : Matched (Conn (seqH H0 (BS.drop m))) x y (back1 (BS[k]'hk).E (BS[k]'hk).a)
      (front1 (BS[k]'hk).E (BS[k]'hk).a)) : nodeI H0 BS x y = k := by
  -- `S m` is finer than `S k`.
  have hrm : Reach V H0 (seqH H0 (BS.drop m)) (BS.drop m) := by
    have e := List.take_append_drop m BS
    have hr2 : Reach V H0 H (BS.take m ++ BS.drop m) := by rw [e]; exact hr
    exact reach_suffix hr2
  have sub : ∀ u v, Conn (seqH H0 (BS.drop m)) u v → Conn (seqH H0 (BS.drop k)) u v := by
    intro u v h
    have e : List.drop (k - m) (List.drop m BS) = List.drop k BS := by
      rw [List.drop_drop, show m + (k - m) = k by omega]
    rw [← e]
    exact conn_drop hVW hdc h0 hout0 hrm (k - m) h
  have hm' : Matched (Conn (seqH H0 (BS.drop k))) x y (back1 (BS[k]'hk).E (BS[k]'hk).a)
      (front1 (BS[k]'hk).E (BS[k]'hk).a) := by
    rcases hm with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨sub _ _ h1, sub _ _ h2⟩
    · exact Or.inr ⟨sub _ _ h1, sub _ _ h2⟩
  obtain ⟨_, hrs, he⟩ := reach_at hVW hdc h0 hout0 hr hk
  have hsplit := hrs.split
  rw [← he] at hsplit
  apply sameNodeI hVW hdc h0 hout0 hr hk hm'
  intro h
  apply hsplit
  rcases hm' with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact (h1.symm.trans h).trans h2
  · exact (h2.symm.trans h.symm).trans h1

end chain

end HP

end SolidGridHam
