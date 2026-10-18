# Checks

* `timed_lint.py`: the cost-model lint. Inside every definition of the counted algorithm
  (`lean/SolidGridHam/Cycle/Timed/*.lean`, except `TimeM.lean`), it allows only the counted operations of
  `TimeM.lean` and constant-time functions. It rejects membership tests, sums, set and list
  operations, `decide`, and calls to the uncounted algorithm.
* `sanity_gen.py`, `sanity_cmp.py`: generate solid point sets, decide Hamiltonicity by
  backtracking, write a Lean file that evaluates `ulhc` and `T.ulhcT` on them, and compare.
  Used by `scripts/sanity.sh`.
* `solid_check.py`, `solid_check_grid.py`: cross-check the Lean definition of `Solid`
  (king-move escape of missing points) against "all interior faces have unit area".
* `probes/`: exploratory scripts from the development, referred to in `BLUEPRINT.md`. Many read
  data files or import helper modules that are not included, so they are a record rather than
  something to run.
