/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
import SolidGridHam.Path.HoleOne

/-!
# An inner endpoint, the other dangling: running time

Per branch: the box test, a reference factor, and per class (at most `2|V| + 1`) one `classSearchOne` and
one loop. With `N = |V| + 3`, at most `5·10⁴ N⁸` steps (`hpI1_main`).
-/

namespace SolidGridHam

namespace HP

open Finset Classical

noncomputable def hpI1Cost (V : Finset Pt) (s t : Pt) : ℕ :=
  10 + ((nbrsL t).map fun x => 10 + 8 * V.card +
    if x.1 ∈ V ∧ x.1 ≠ s ∧ isNarrow (V.erase t) = true then
      DFC.findFactorCost (V.erase t) (dST s x.1) + 1 +
        (match findFactor (V.erase t) (dST s x.1) with
          | none => 0
          | some R => ((classRange (V.erase t)).map fun h =>
              2 + classSearchOneCost (V.erase t) (insert x.2 R) t h +
                (match classSearchOne (V.erase t) (insert x.2 R) t h with
                  | some G => runSCCost (V.erase t) t ((V.erase t).card + 2) G
                  | none => 0)).sum)
    else 0).sum

section cost

variable {V : Finset Pt} {s t : Pt}

lemma length_hRange (U : Finset Pt) : (classRange U).length = 2 * U.card + 1 := by
  simp [classRange]

end cost

end HP

end SolidGridHam
