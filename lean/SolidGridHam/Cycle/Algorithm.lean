/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
module

public import SolidGridHam.Cycle.LinkGraph
public import SolidGridHam.Algorithm

@[expose] public section

/-!
# The algorithm

Start from a 2-factor (`twoFactor`). While it has more than one component: flip a Type III
cell if there is one (`findT3`); otherwise flip the first strip of a minimum no-chain path
(`findPath`); if there is no such path, give up. `run` bounds the number of rounds by fuel.

* `step_deg2`, `run_sound`, `ulhc_sound`: every state is a 2-factor, so `ulhc V = true`
  yields a Hamiltonian cycle (a 2-factor with one component).
-/

namespace SolidGridHam

open Finset

lemma mem_cellList {V : Finset Pt} {d : Pt} : d ∈ cellList V ↔ d ∈ V ∧ IsCell V d := by
  unfold cellList
  simp only [List.mem_map, Finset.mem_sort, Finset.mem_map, Finset.mem_filter]
  constructor
  · rintro ⟨y, ⟨x, hx, rfl⟩, rfl⟩; exact hx
  · intro h; exact ⟨toLex d, ⟨d, h, rfl⟩, rfl⟩

lemma mem_sidesL (tf : Side) : tf ∈ sidesL := by cases tf <;> simp [sidesL]

-- A Type III cell in frame `t`, decided.
--
def t3B (V : Finset Pt) (G : Finset Edge) (d : Pt) (tf : Side) : Bool :=
  decide (back d tf ∈ G) && decide (front d tf ∈ G) && decide (lat1 d tf ∉ G) &&
    decide (lat2 d tf ∉ G) && !connB V G (back1 d tf) (front1 d tf)

def findT3 (V : Finset Pt) (G : Finset Edge) : Option (Pt × Side) :=
  ((cellList V).flatMap fun d => sidesL.map fun tf => (d, tf)).find? fun p => t3B V G p.1 p.2

lemma t3B_iff {V : Finset Pt} {G : Finset Edge} (hGV : Inside V G) {d : Pt} (hd : IsCell V d)
    {tf : Side} : t3B V G d tf = true ↔ back d tf ∈ G ∧ front d tf ∈ G ∧ lat1 d tf ∉ G ∧
      lat2 d tf ∉ G ∧ ¬ Conn G (back1 d tf) (front1 d tf) := by
  obtain ⟨hb, _, hf, _⟩ := corners4 hd tf
  unfold t3B
  simp only [Bool.and_eq_true, decide_eq_true_eq, bool_not_iff (connB_iff hGV hb hf)]
  tauto

theorem findT3_some {V : Finset Pt} {G : Finset Edge} (hGV : Inside V G) {d : Pt} {tf : Side}
    (h : findT3 V G = some (d, tf)) : IsCell V d ∧ back d tf ∈ G ∧ front d tf ∈ G ∧
      lat1 d tf ∉ G ∧ lat2 d tf ∉ G ∧ ¬ Conn G (back1 d tf) (front1 d tf) := by
  unfold findT3 at h
  have hm := List.mem_of_find?_eq_some h
  have hp := List.find?_some h
  simp only [List.mem_flatMap, List.mem_map] at hm
  obtain ⟨d', hd', t', _, he⟩ := hm
  cases he
  have hc := (mem_cellList.1 hd').2
  exact ⟨hc, (t3B_iff hGV hc).1 hp⟩

theorem findT3_none {V : Finset Pt} {G : Finset Edge} (hGV : Inside V G) (h : findT3 V G = none) :
    NoTypeIII V G := by
  intro d hd tf hb hf hl1 hl2
  by_contra hn
  unfold findT3 at h
  have := List.find?_eq_none.1 h (d, tf) (by
    simp only [List.mem_flatMap, List.mem_map]
    exact ⟨d, mem_cellList.2 ⟨hd.1, hd⟩, tf, mem_sidesL tf, rfl⟩)
  exact this ((t3B_iff hGV hd).2 ⟨hb, hf, hl1, hl2, hn⟩)

-- One round.
--
def step (V : Finset Pt) (G : Finset Edge) : Option (Finset Edge) :=
  match findT3 V G with
  | some (d, _) => some (flip G d)
  | none =>
    match findPath V G with
    | some (a, _) => some (applyS G a)
    | none => none

theorem step_deg2 {V : Finset Pt} {G G' : Finset Edge} (hG : Deg2 V G)
    (h : step V G = some G') : Deg2 V G' := by
  unfold step at h
  rcases ht : findT3 V G with _ | ⟨d, tf⟩
  · rw [ht] at h
    simp only at h
    rcases hp : findPath V G with _ | ⟨a, L⟩
    · rw [hp] at h; simp at h
    · rw [hp] at h
      simp only [Option.some.injEq] at h
      subst h
      obtain ⟨⟨⟨_, hpa, hca, _⟩, _⟩, _⟩ := (findPath_some hG.1 hp).1
      exact deg2_flipCol _ G hG hpa hca
  · rw [ht] at h
    simp only [Option.some.injEq] at h
    subst h
    obtain ⟨hd, hb, hf, hl1, hl2, _⟩ := findT3_some hG.1 ht
    exact hG.flip (mkBF d tf) hd (mkBF_cellE d tf) hb hf hl1 hl2

def run (V : Finset Pt) : ℕ → Finset Edge → Bool
  | 0, G => cncomp V G == 1
  | k + 1, G =>
    if cncomp V G == 1 then true
    else match step V G with
      | some G' => run V k G'
      | none => false

theorem run_sound {V : Finset Pt} : ∀ (k : ℕ) (G : Finset Edge), Deg2 V G → run V k G = true →
    ∃ H, Deg2 V H ∧ ncomp V H = 1 := by
  intro k
  induction k with
  | zero =>
    intro G hG h
    simp only [run, beq_iff_eq] at h
    exact ⟨G, hG, by rw [← cncomp_eq hG.1]; exact h⟩
  | succ k ih =>
    intro G hG h
    simp only [run] at h
    by_cases h1 : cncomp V G = 1
    · exact ⟨G, hG, by rw [← cncomp_eq hG.1]; exact h1⟩
    · rw [ite_eq_right (by simpa using h1)] at h
      rcases hs : step V G with _ | G'
      · rw [hs] at h; simp at h
      · rw [hs] at h
        exact ih G' (step_deg2 hG hs) h

-- A bound on the number of link-graph nodes, `|candN V G| ≤ Bd V` for every `G`
-- (`card_candN_le` in `AlgComplete`).
--
def Bd (V : Finset Pt) : ℕ := 3 * (4 * V.card + V.card * (4 * V.card))

-- A bound on the weight of a minimum path (`dval_le` in `AlgComplete`).
--
def Dm (V : Finset Pt) : ℕ := Bd V * V.card

-- The number of rounds allowed, `O(|V|⁴)`. It exceeds the potential `Mz` of the starting
-- 2-factor, which every round lowers (`AlgComplete`).
--
def fuel (V : Finset Pt) : ℕ := (V.card + 1) * (2 * Dm V + 4) + 2

def ulhc (V : Finset Pt) : Bool :=
  match twoFactor V with
  | some F => run V (fuel V) F
  | none => false

theorem ulhc_sound {V : Finset Pt} (h : ulhc V = true) : ∃ H, Deg2 V H ∧ ncomp V H = 1 := by
  unfold ulhc at h
  rcases hf : twoFactor V with _ | F
  · rw [hf] at h; simp at h
  · rw [hf] at h
    exact run_sound _ F (twoFactor_some hf) h

end SolidGridHam
