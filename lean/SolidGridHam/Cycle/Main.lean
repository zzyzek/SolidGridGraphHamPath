/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
module

public import SolidGridHam.Cycle.PathComplete
public import SolidGridHam.Cycle.Timed.Alg

@[expose] public section

/-!
# Main theorem

`T.ulhcT V` is the algorithm written with counted operations (`Timed/TimeM.lean` lists them
and their costs; `checks/timed_lint.py` checks that nothing else is used). Its result is `ulhc V`
(`T.ulhcT_ret`), so for a solid grid graph `V` it decides whether `V` has a Hamiltonian cycle,
and it takes at most `5·10⁸ (|V| + 1)¹²` steps.
-/

namespace SolidGridHam

theorem ulhc_main {V : Finset Pt} (hs : Solid V) :
    ((T.ulhcT V).ret = true ↔ ∃ H, Deg2 V H ∧ ncomp V H = 1) ∧
      (T.ulhcT V).time ≤ 500000000 * (V.card + 1) ^ 12 := by
  refine ⟨?_, (T.ulhcT_time_le V).trans (ulhcCost_le V)⟩
  rw [T.ulhcT_ret]
  exact ulhc_correct hs

end SolidGridHam
