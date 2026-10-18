/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
import ULHC

/-! Axioms of the main results. Each should list only `propext`, `Classical.choice` and
`Quot.sound`. Run with `lake env lean CheckAxioms.lean` from `lean/`. -/

-- Hamiltonian s-t paths in solid grid graphs: correctness and the step bound.
#print axioms ULHC.HP.decideHamPath_main
#print axioms ULHC.HP.boundaryEndpoints_main
#print axioms ULHC.HP.oneHoleCase_main
#print axioms ULHC.HP.twoHoleCase_main
-- The stuck-state count behind the certificate (columns).
#print axioms ULHC.HP.stuck_minimal

-- Hamiltonian cycles (Umans-Lenhart): correctness and the step bound of the counted algorithm.
#print axioms ULHC.ulhc_main
-- Correctness of the plain algorithm.
#print axioms ULHC.ulhc_correct
-- The step bound.
#print axioms ULHC.ulhcCost_le
-- Existence of alternating strip sequences (thesis Lemma 6.7 / paper Theorem 5).
#print axioms ULHC.theoremA
#print axioms ULHC.theoremA2
-- Repeated sequences reach a Hamiltonian cycle (thesis Theorem 6.1).
#print axioms ULHC.theorem61
-- Completeness of the path search.
#print axioms ULHC.pathComplete
