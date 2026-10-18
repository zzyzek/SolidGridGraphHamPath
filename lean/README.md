# Lean package `solidgridham`

The Lean 4 library `SolidGridHam` (Mathlib, toolchain pinned in `lean-toolchain`). See the
[top-level README](../README.md) for what is proved, how to build and how to check it.

* `SolidGridHam.lean`: imports every module.
* `SolidGridHam/Algorithm.lean`: the algorithm `decideHamPath` and every definition that it and
  the statement of `decideHamPath_main` use, in one module (lattice points, edges, degrees,
  factors, `dST`, `Solid`, `ncomp`, and the algorithm's subroutines). The other files prove
  things about them.
* `SolidGridHam/Basic/` (7 files): lattice points, edges, degrees and factors (`Grid.lean`),
  connectivity (`Conn.lean`, `Graph.lean`), arcs, relative heights and potentials (`Arcs.lean`,
  `D.lean`, `Potential.lean`, `Planar.lean`).
* `SolidGridHam/Cycle/` (49 files): the Umans–Lenhart Hamiltonian cycle formalization,
  `Main.lean` has `SolidGridHam.ulhc_main`. `Timed/` is the algorithm in a step-counting monad.
  The path development reuses its strip and flip library.
* `SolidGridHam/Path/` (87 files): the Hamiltonian s–t path development. `HPFinal.lean` has
  `SolidGridHam.HP.decideHamPath_main`. `FindFactor.lean` is the starting factor (augmenting
  paths). File and definition names follow the paper.
* `SolidGridHam/Path/Prelim/` (11 files): lemmas on path factors, notches and relative strips
  that the path development uses.
* `Challenge.lean`, `Solution.lean`, `comparator.json`, `formalization.yaml`: the Palomar registry
  entry (see the top-level README).
* `CheckAxioms.lean`: `#print axioms` for the main results (`lake env lean CheckAxioms.lean`).
* `build.sh`: `lake build`, optionally with memory and thread limits (`LEAN_MEM`,
  `LEAN_NUM_THREADS`).

Finite case checks use kernel `decide`. There is no `native_decide`.
