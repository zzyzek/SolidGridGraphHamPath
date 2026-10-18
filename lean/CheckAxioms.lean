/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
import SolidGridHam

/-! Axioms of the main results. Each should list only `propext`, `Classical.choice` and
`Quot.sound`. Run with `lake env lean CheckAxioms.lean` from `lean/`. -/

-- Hamiltonian s-t paths in solid grid graphs: correctness and the step bound.
#print axioms SolidGridHam.HP.decideHamPath_main
#print axioms SolidGridHam.HP.boundaryEndpoints_main
#print axioms SolidGridHam.HP.oneHoleCase_main
#print axioms SolidGridHam.HP.twoHoleCase_main
-- The stuck-state count behind the certificate (columns).
#print axioms SolidGridHam.HP.stuck_minimal

-- Hamiltonian cycles (Umans-Lenhart): correctness and the step bound of the counted algorithm.
#print axioms SolidGridHam.ulhc_main
-- Correctness of the plain algorithm.
#print axioms SolidGridHam.ulhc_correct
-- The step bound.
#print axioms SolidGridHam.ulhcCost_le
-- Existence of alternating strip sequences (thesis Lemma 6.7 / paper Theorem 5).
#print axioms SolidGridHam.theoremA
#print axioms SolidGridHam.theoremA2
-- Repeated sequences reach a Hamiltonian cycle (thesis Theorem 6.1).
#print axioms SolidGridHam.theorem61
-- Completeness of the path search.
#print axioms SolidGridHam.pathComplete
