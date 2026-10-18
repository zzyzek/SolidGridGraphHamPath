/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
import SolidGridHam.Path.Overlap

/-!
# Lemma 4, (C1) for the undo operations

Each bridge is a row at its creation time (`rowAt_at`). The squares an undo operation of a newer
bridge uses (its `E`, or its row up to `A`) avoid every square of an older bridge
(`c1_newer`): for `E`, `NotZ`; for the row, `rowAvoid` at the newer bridge's creation time.
-/

namespace SolidGridHam

namespace HP

open Finset Classical

section c1

variable {V W : Finset Pt} {d : Pt → ℕ} {t0 u0 : Pt} {H0 : Finset Edge}
  (hVW : V ⊆ W) (hdc : ∀ q, IsCell V q → ∀ z, IsCorner z q → d z = 2)
  (h0 : IsFactor W d H0) (hout0 : ∀ e ∈ H0, (e.p ∉ V → e.q = t0 ∨ e.q = u0) ∧ (e.q ∉ V → e.p = t0 ∨ e.p = u0))
include hVW hdc h0 hout0

-- The bridge at index `k` is a row at its creation time, against the older bridges.
--
theorem rowAt_at {BS : List Bridge} {H : Finset Edge} (hr : Reach V H0 H BS) {k : ℕ}
    (hk : k < BS.length) :
    RowAt V (seqH H0 (BS.drop (k + 1))) (BS.drop (k + 1)) (BS[k]'hk).q (BS[k]'hk).a
      (BS[k]'hk).r := by
  obtain ⟨_, hrs, _⟩ := reach_at hVW hdc h0 hout0 hr hk
  have e := List.take_append_drop k BS
  have hr2 : Reach V H0 H (BS.take k ++ BS.drop k) := by rw [e]; exact hr
  have hs := reach_suffix hr2
  rw [List.drop_eq_getElem_cons hk] at hs
  obtain ⟨hnb, _⟩ := reach_cons_nbs hs
  exact ⟨hrs.two, hrs.cells, hrs.crit, hrs.bk,
    fun b hb j hj he => hnb ⟨b, hb, j, hj, he⟩, hrs.uncut, hrs.arcs⟩

-- **(C1)** Squares used by an undo operation of the bridge at `k` avoid the squares of an older
-- bridge at `i > k`.
--
theorem c1_newer {BS : List Bridge} {H : Finset Edge} (hr : Reach V H0 H BS) {k i : ℕ}
    (hki : k < i) (hi : i < BS.length) (low : Bool) {j : ℕ}
    (hj : j < (if low then lowJ (BS[k]'(by omega)) else undoJ (BS[k]'(by omega))).n) {l : ℕ}
    (hl : l < (BS[i]'hi).r) :
    cellJ (if low then lowJ (BS[k]'(by omega)) else undoJ (BS[k]'(by omega))).c
      (if low then lowJ (BS[k]'(by omega)) else undoJ (BS[k]'(by omega))).a j ≠
      (BS[i]'hi).cell l := by
  have hk : k < BS.length := by omega
  have hinv := pinv_reach (t0 := t0) (u0 := u0) hVW hdc h0 hout0 hr
  cases low
  · -- re-flip of `E`: `NotZ`
    simp only [Bool.false_eq_true, ↓reduceIte, undoJ] at hj ⊢
    obtain rfl : j = 0 := by omega
    rw [cellJ_zero]
    have hz : NotZ (BS[k]'hk) (BS[i]'hi) :=
      List.pairwise_iff_getElem.1 hinv.sep k i hk hi hki
    exact hz.1 l (by omega)
  · -- lowering: `rowAvoid` at the creation time of bridge `k`
    simp only [↓reduceIte, lowJ] at hj ⊢
    have hrow := rowAt_at hVW hdc h0 hout0 hr hk
    have hrk := (reach_at hVW hdc h0 hout0 hr hk).1
    have hinvk := pinv_reach (t0 := t0) (u0 := u0) hVW hdc h0 hout0 hrk
    have hmem : BS[i]'hi ∈ BS.drop (k + 1) := by
      rw [List.mem_iff_getElem]
      exact ⟨i - (k + 1), by simp; omega, by simp [List.getElem_drop]; congr 1; omega⟩
    obtain ⟨hR, h2, he, _⟩ := hinvk.reg _ hmem
    exact rowAvoid hrow (degc_of hVW hdc hinvk.fac) hmem hR h2 he (by omega) hl

end c1

end HP

end SolidGridHam
