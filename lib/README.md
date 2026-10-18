# Reference implementation of `decideHamPath` (Python)

`lib/python/` holds a Python 3 (standard library only) implementation of the Lean-verified
decision procedure `decideHamPath` (`lean/ULHC/HP/Sheffield/HPFinal.lean`): for a solid grid graph `V`
and distinct `s, t ∈ V`, `decideHamPath V s t = true` iff `V` has a Hamiltonian `s`–`t` path
(`decideHamPath_main`, at most `5 220 000 · (|V|+3)⁶` steps). The Python version also returns the
path. It follows the Lean definitions of commit e25dca0 (branch `faropp`): `Far` is king
distance ≥ 2, and the walks stop only when the two phantoms are not opposed (`Opp`).

| file | content |
|---|---|
| `hpst_ref.py` | faithful port ("ref" mode): one Python function per Lean definition, same name, Lean file cited; the names before the 2026-10-18 rename remain as aliases |
| `hpst_fast.py` | the same algorithm with answer-preserving speedups ("fast" mode); entry point `decideHamPath` (alias `hpAll`, its name before 2026-10-18) |
| `hpst_cli.py` | command line front end |
| `brute.py` | exact brute force (DFS with pruning), for testing |
| `gen.py` | random solid grid graphs with chosen endpoint types |
| `test_hpst.py` | tests against the brute force |


## Names

All implementations use the names of the Lean definitions they follow (`decideHamPath`,
`boundaryEndpointsWalk`, `holeCaseWalk`, `oneHoleFinalTest`, `classSearch`, `twoPhantomLoop`,
`runPhase`, `reducePieces`, `findFactor`, `isFar`, `phantomsOpposed`, …), the same names as the
paper and its pseudocode. Statistics keys and branch labels use them too (`findFactor`,
`classSearch`, `twoHoleCase`, `oneHoleCase-swap`, …), so the four implementations report identical
output. The Lean definitions were renamed on 2026-10-18 from terse names (`hpAll`, `walkT`,
`dFactor`, `kFind`, `phaseS`, …); `hpst_ref.py` keeps the old names as aliases and `hpst_fast.py`
keeps `hpAll`. The mapping is in the commit message of the rename (git log, "Rename Lean
procedures").

## Command line

```
python3 lib/python/hpst_cli.py [FILE] [--mode ref|fast] [--draw] [--json] [--check] [--stats]
                               [--no-heuristic]
```

The input is read from `FILE`, or from stdin. The format is detected: input whose first
non-blank character is `{` is JSON, anything else is an ASCII grid.

**ASCII grid.** One line per row, top row first.
* `.` is a point of `V`; `#` or space is not a point; `s` and `t` are the endpoints (points of `V`).
* Lines starting with `;` are comments. Blank lines before the first and after the last grid line
  are ignored; blank lines inside the grid are empty rows.
* Coordinates: `x` is the column index (0 = leftmost character), `y` is the row index counted
  from the bottom (the last grid line is `y = 0`), so `y` increases upward as in Lean.

```
; a 4x3 block, s bottom left, t bottom right
....
....
s..t
```

**JSON.** `{"points": [[x, y], ...], "s": [x, y], "t": [x, y]}`.

**Output.** The first line is `yes` or `no`. After `yes`, the second line is the path from `s` to
`t` as `x,y` pairs separated by spaces.

| flag | effect |
|---|---|
| `--mode ref\|fast` | faithful port or fast mode (default `fast`) |
| `--draw` | draw the path (box characters; points on even columns and rows, path edges between) |
| `--json` | JSON output: `{"answer": "yes"\|"no", "path": [[x, y], ...] \| null, ...}` |
| `--check` | also run the brute force and print `check: agree` / `check: DISAGREE` (small inputs only) |
| `--stats` | time, the `decideHamPath` branch, counts (walk nodes, final tests, classes tried / found, `runSC2` runs, phases, bridges, reductions, pruned branches, memo hits) and the time in each part (global checks, heuristic, pruning, `findFactor`, class search, loop) |
| `--no-heuristic` | fast mode: skip the heuristic yes-search, so the algorithm itself decides |

Exit codes: 0 answered; 1 `--check` disagreement or an invalid witness; 2 bad input (format,
missing or equal endpoints, endpoint not in `V`, `V` not solid). Non-solid input is rejected with
an error message: `decideHamPath_main` assumes `Solid V`.

Every returned path is checked independently (`verify_path`: starts at `s`, ends at `t`, visits
every point once, consecutive points adjacent).

## Ref mode: faithfulness to Lean

`hpst_ref.py` ports every `Bool`/`Option`-valued definition on the call path of `decideHamPath`:
`decideHamPath`, `isInner` (HPFinal); `boundaryEndpoints`, `boundaryEndpointsWalk`, `isFar`, `phantomsOpposed`, `isUsablePhantom` (TwoPhWalk); `nbrsL` (SheffBoundary);
`holeCase`, `holeCaseWalk`, `oneHoleFinalTest`, `oneHoleCase` (HoleWalk); `twoHoleFinalTest`, `twoHoleCase` (HoleTwoV); `isNarrow` (HoleOne);
`twoPhantomTest` (LoopF); `twoPhantomLoop`, `reducePieces`, `bridgeStatesConn`, `undoPlanSteps`, `undoPlan`, `isGoodMergingCell`
(ReduceS); `runPhase`, `findMergingCell`, `findRow`, `rowOf`, `scanRow`, `scanRowAux`, `isCritical`, `isCutCell`,
`bridgeSquares` (PhaseS); `connectedPairs`, `isConnected`, `comps`, `compsAux`, `ptList` (ConnSet); `flipSplits`
(SPhaseAlg); `cutB`, `pairSqB` (SAlg); `classSearch`, `classSearchOne`, `classRange` (HoleTry); `classPotential`, `relaxA`,
`roundA`, `kInitA`, `toFA`, `idx`, `cellOf`, `inBox`, `kWn`, `kHn`, `lowerBound`, `ivl`, `isAdmissible`,
`sideOK`, `jumpEdges`, `kFuel`, `boxSquares`, `boxWidth`, `bx0..by1`, `sides` (HoleRelax); `sv` (HoleAdm); `findFactor`,
`augLoop`, `augStep`, `walk`, `pick`, `pred`, `layerAcc`, `nbr`, `Fwd`, `Bwd` (DFactor); `connB`
(Enum); `ccls`, `creach`, `cncomp`, `fnbr` (Comp); the geometry of Grid, Arcs, Strip, StripCount,
D, Bridges, Undo, Compat0, UndoCount, Node, Reduce, S4TheoremR.

Same control flow, fuel constants (`12` for `boundaryEndpointsWalk`, `10` for `holeCaseWalk`, `|V|+2` loop iterations,
`|W|+1` phase steps, `|V|+1` scan steps, `|V|+1` augmentations, `|V|` layers and BFS rounds,
`kFuel = |boxSquares V| + 1` relaxation rounds) and iteration orders (`nbrsL`: right, left, up, down; `inc4`: right,
left, up, down; `sidesL`: b, t, l, r; `cellList`, `ptList`: lexicographic; `boxSquares` and the `relaxA`
array: x-major; `classRange`:
`-|V| … |V|`; `pick`: lexicographic least). Lean `Finset`s are used only as sets (membership,
union, symmetric difference); no result depends on a `Finset` iteration order, and every list
order above is Lean's, so ref mode makes the same choices as Lean.

Deviations, all value-identical:
* `creach` stops after a round that adds nothing; `layerAcc` stops once a layer repeats and pads
  with copies (later rounds would return the same set).
* `bx0..by1` and `boxSquares` are memoized per point set; `toFA` reads the box once and inlines `inBox`
  and `idx`.
* Bool results carry witnesses: `twoPhantomLoop` returns the final factor or `None`; the decision
  functions return a path or `None` (`None` exactly when Lean returns `false`).

Witness: the final one-piece factor of `twoPhantomLoop` minus the two phantom edges is the path in the
current set; every deletion on the way back up re-attaches the deleted point (its edge to its
successor is the branch edge), giving the path in the original `V`.

## Fast mode

Same algorithm; every speedup is commented in `hpst_fast.py` with its justification.

* **S1** Integer point ids and flat arrays (`bytearray` for point sets and edge sets), for C/JS ports.
* **S2** Pieces: one component labelling per factor state, recomputed only after a flip;
  `connB`, `cutB`, `critB`, `cncomp` become lookups. Cells scanned in Lean's order.
* **S3** `findFactor`: layers as one BFS (distances), the walk jumps to the first layer not containing
  the point; same factor as Lean.
* **S4** Class search: `classPotential` by a bucket shortest-path (longest-path with weights 0/−1) computation
  instead of `kFuel = |boxSquares|+1` Jacobi rounds (`relaxA`); same potential (Jacobi converges to the
  least fixed point above `kInit` within `|boxSquares|+1` rounds since no cycle has positive weight). Tested equal to the
  faithful `classPotential`/`classSearch`.
* **S5** Classes restricted to `|h| ≤ boxWidth` (`hClass_bound` + `classSearch_sound`), ordered by `|h|`
  (pairs by `|h₁|+|h₂|`), first success returns.
* **S6** Necessary conditions for a Hamiltonian `a`–`b` path, globally and before every walk
  branch: colour balance, every point other than `a`, `b` has 2 neighbours (`a`, `b` one), `V`
  plus the edge `a`–`b` is 2-connected (includes connectivity and the cut-vertex conditions).
  Answer-preserving because every decision call on the path decides "is there a Hamiltonian path
  in this subproblem" (Lean `boundaryEndpointsWalk_correct`, `holeCaseWalk_correct`, `holeCase_branch`, `oneHoleFinalTest_correct`, …).
* **S7** Memo of failed subproblems `(deleted set, a, b)`.
* **S8** Heuristic yes-first: a time-boxed DFS (Warnsdorff order, degree and connectivity pruning);
  a found path is verified before it is returned. `--no-heuristic` turns it off.

With `order='lean'` and `heuristic=False` (Python API), fast mode returns exactly the path of ref
mode (tested).

## Tests

```
cd lib/python
ulimit -v 8000000
python3 test_hpst.py                      # all suites
python3 test_hpst.py hand random --count 400 --nmax 40 --time 900
```

Suites: `hand` (rectangles up to 5×6 with all colour-feasible endpoint pairs, both orders; an L;
a plus), `random` (all shapes × endpoint modes, ref for `|V| ≤ 30`, fast with and without the
heuristic), `same` (fast in Lean order = ref, path for path), `kpot` (shortest-path `classPotential` = faithful
array `classPotential`), `leaf` (every final test compared with the brute force on its own subproblem, tagged by
the king distance of the out-vertices and by whether the loop ran a phase).

Generator (`gen.py`): shapes `blob`, `thin`, `fat`, `rect`, `hpath` (a planted Hamiltonian path,
mixed by backbite moves, so "yes"); endpoint modes `any`, `inner2`, `inner1`, `boundary`, `close`
(king distance ≤ 2), `adjacent`, `plausible` (endpoints passing all necessary conditions of S6:
the hard "no" candidates).

Results and timings: see the end of this file.

## Results (2026-10-17, Lean commit e007d32)

Machine: 4 cores, each run single-threaded under `ulimit -v 6000000`.

**Correctness.** No disagreement with the brute force, no invalid path, in any suite:

| suite | instances | notes |
|---|---|---|
| `hand` | 1,624 runs (ref on ≤ 30 points) + fast with and without heuristic | rectangles 2×2 … 5×6, L, plus; all colour-feasible pairs, both orders |
| `random` | 1,500 (|V| 10–40; ref on ≤ 30) | all four `decideHamPath` branches, yes and no |
| `same` | 400 | fast (Lean order, no heuristic) returns ref's path exactly |
| `kpot` | 900 | shortest-path `classPotential`/`classSearch` equal to the faithful ones |
| `leaf` | 20,000 (|V| 10–46) | 76,179 final tests vs brute on their own subproblem; 4,270 at king distance 2 and 4,114 at ≥ 3 ran the loop |

**Ref mode on the current Lean definitions** (commit e25dca0: `twoPhantomLoop` / `runPhase` /
`reducePieces` loop, array `classPotential` with `kFuel = |boxSquares| + 1`): `hand` (672 ref runs), `random` (244 ref
runs), `same` (150), `kpot` (900) pass; a separate ref vs brute force run on 1,350 instances of
15–45 points (endpoint modes weighted towards one or two inner endpoints: 481 `boundaryEndpoints`, 514 `oneHoleCase`
either way round, 355 `twoHoleCase`; 680 yes, 670 no) agrees on every instance. On 250 of them the
previous ref mode (`runSC2`, list `relax`) returns the same path everywhere; the new ref mode
takes 132 s against 114 s (the class search dominates; worst single instance 373 s, `twoHoleCase` at
|V| = 44).

**Walk size, new rule vs old rule** (full 15×15 grid, the whole walk tree: every final test
forced to fail, no pruning, no memo; worst start over the tested endpoints):

| | old (Far ≥ 3) | new (Far ≥ 2, no `Opp`) |
|---|---|---|
| `holeCase` (inner `t` at the centre), walk nodes / final tests | 73,678 / 35,778 | 74 / 48 |
| `boundaryEndpoints` (both on the bottom row), walk nodes / final tests | 588 / 269 | 12 / 7 |

**Fast mode times** (algorithm only, `--no-heuristic`). "Yes" instances finish in the first branch:
median ≤ 0.03 s up to |V| ≈ 800. The hardest instances are "no" answers whose endpoints pass every
necessary condition (found by searching 31,247 instances of 50–100 points and 8,348 of 200–400):
worst 0.54 s at |V| = 100 (37 walk nodes, 27 final tests, 882 classes tried), worst 0.10 s at
|V| ≈ 400. The same |V| = 100 instance took 41.7 s under the old rule without the `findFactor` warm
start (5,985 walk nodes, 2,837 final tests) and 2.8 s with it.

**Ref mode times.** Yes instances with boundary endpoints: < 0.1 s up to |V| ≈ 100. `twoHoleCase`
(both endpoints inner) is dominated by the class-pair search, `(2|U|+1)²` relaxations: 7 s at
|V| = 49, 35 s at 64, 91 s at 96 (yes instances); "no" instances 56–78 s at |V| = 42–50 and over
240 s at |V| = 100. Ref mode is for auditing, not for use above about 50 points.

## C port (`lib/c/`)

A C99 port of fast mode (libc and libm only): the same algorithm with the same speedups S1–S8,
the same iteration orders and the same command line.

| file | content |
|---|---|
| `hpst.h`, `hpst.c` | solver library: `hpst_solve(V, n, s, t, opts, &path, &np, &stats)` returns 1 (yes, with the path), 0 (no), -1 (bad input), -2 (internal error); also `hpst_verify_path`, `hpst_solid` |
| `main.c` | command line front end (with a built-in brute force for `--check`) |
| `Makefile` | `make` builds `hpst` |
| `compare.py` | C vs Python fast mode vs brute force on `gen.py` instances; CLI output comparison |
| `perf.py` | timings, C vs Python, on yes and hard no instances |

```
cd lib/c && make
./hpst FILE [--draw] [--json] [--check] [--stats] [--no-heuristic]
```

Input formats, flags, output and exit codes are those of `hpst_cli.py` (above); `--mode` accepts
only `fast`. Output is byte-identical to the Python front end except for timings and the wording
of JSON syntax errors.

Port notes. Sets and dicts are id-indexed arrays emptied by epoch stamps; the memo (S7) is an
open-addressing hash table keyed by the sorted deleted set and the two endpoints (the full key
is compared, so collisions cannot change answers); the heuristic DFS (S8) uses an explicit stack.
Two extra value-identical changes: in `oneHoleFinalTest` the `classPotential` constraint weights and outside
sources depend only on the factor and `U`, so they are computed once per factor instead of once
per class; `planAB` flips the bridge squares in place and flips them back instead of copying
the edge set. With the heuristic off, the C solver returns the same path and the same counters
(walk nodes, final tests, `classSearch` calls, phases, …) as Python fast mode; `compare.py` checks
this on every instance.

```
cd lib/c
ulimit -v 8000000
python3 compare.py --cli --sizes 8,16,24,32,40 --count 24     # with brute force up to 40 points
python3 compare.py --sizes 400,800,1600 --count 2 --brute-max 0
python3 perf.py --sizes 100,400,1600
```

C port results (2026-10-17): 10,337 random instances (all shapes × endpoint modes, |V| 8–1600;
8,260 also checked by brute force), no disagreement in answer, path or counters, no invalid
path; 16 CLI cases identical (output and exit code); an ASan/UBSan build is clean on 735 of them.
Algorithm times (no heuristic) are 50–220× below Python fast mode: hardest no instances found
0.7 ms (|V| = 100, 100 `classSearch` calls; Python 0.155 s), 1.2 ms (|V| ≈ 400; Python 0.096 s),
0.2 ms (|V| ≈ 1600; Python 0.026 s); yes instances 0.1–0.7 ms at |V| ≈ 1600 (Python 0.045–0.075 s).

# JavaScript port (fast mode)

`lib/js/` holds a port of the fast mode (`hpst_fast.py`) to plain modern JavaScript (ES2020, no
dependencies, ES module).

| file | content |
|---|---|
| `hpst.js` | the library: `solve`, plus `isSolid`, `verifyPath`, `parseInput`, `checkInput`, `draw` |
| `cli.js` | command line front end (Node) |
| `batch.js` | JSON-lines batch runner (testing and timing; times `solve` only) |
| `compare.py` | correctness driver: JS vs Python fast mode vs brute force on `gen.py` instances |
| `timing.py` | timings JS vs Python fast mode on yes and hard "no" instances |
| `package.json` | `"type": "module"` so that Node loads the `.js` files as ES modules |

## Command line

```
node lib/js/cli.js [FILE] [--draw] [--json] [--stats] [--no-heuristic] [--mode fast]
```

Same input formats (ASCII grid or JSON, from `FILE` or stdin), same output (text and `--json`,
byte for byte the format of `hpst_cli.py`, including the `--stats` lines and `json.dumps`
spacing and `\u` escapes) and the same exit codes (0 answered, 1 invalid witness, 2 bad input
or bad arguments; non-solid input is rejected with exit 2). Only fast mode is ported: `--mode ref`
and `--check` are rejected with exit 2 (use `hpst_cli.py`).

## Library

```js
import { solve, isSolid } from './lib/js/hpst.js';   // Node or <script type="module">
const r = solve([[0,0],[1,0],[0,1],[1,1]], [0,0], [1,0], { heuristic: true });
// r.answer: 'yes' | 'no'; r.path: [[x, y], ...] | null;
// r.stats: { counts, times (seconds), branch, decided_by }
```

Options: `heuristic` (default true), `order` (`'abs'`, or `'lean'` for Lean's class order and
no `findFactor` warm start), `prune`, `memo` (default true), `timeBox` (seconds). `solve` does not
test solidity; call `isSolid(points)` first (the CLI does, through `checkInput`). On Node ≥ 22.12
`require('./lib/js/hpst.js')` also works (require of an ES module).

## Port

Same algorithm, same speedups S1–S8, same iteration orders and fuels. Python dicts and sets of
points are typed arrays indexed by point id (`inU`, edge sets, `dist`, `degA`, component labels,
`cellset`, `classPotential`'s potential, the heuristic's `vis` / `free`); small cell sets (`pairSq`,
`brSq`) and the memo are JS `Set`s. Differences in form only:
* The Tarjan test and the heuristic DFS use explicit stacks (no recursion depth limit).
* `classPotential`'s reverse adjacency is computed on the fly from the four neighbouring cells (same terms).
* Floats in `--stats` / `--json` are printed as Python prints them (`0.0`, `0.0123`).

With the heuristic off the JS port returns exactly the Python fast-mode path (checked on every
instance below). With the heuristic on, the heuristic is time-boxed in both, so which instances
it settles may differ; the answer may not.

## Results (2026-10-17)

`compare.py` (all 5 shapes × 7 endpoint modes of `gen.py`; Python fast mode without heuristic;
JS through `batch.js` with and without heuristic; every k-th instance also through `node cli.js
--json` with and without heuristic), each process under a 5 GB address-space limit:

| sizes | instances | brute force compared | answers differing | invalid JS paths | JS path = Python path (no heuristic) | CLI runs |
|---|---|---|---|---|---|---|
| 8–36 | 7,448 | 7,198 | 0 | 0 | 7,448 / 7,448 | 2 × 298 |
| 40–150 | 5,192 | – | 0 | 0 | 5,192 / 5,192 | 2 × 130 |
| 50–200 | 2,578 | – | 0 | 0 | 2,578 / 2,578 | 2 × 129 |

In the 40–150 run one of three parallel `batch.js` processes (heuristic on, 1,731 instances)
died with SIGSEGV and no message; the same 5,192 instances rerun sequentially (twice) and in
parallel (4 × 5,192) gave no crash and agreed with Python on every answer. `compare.py` now
retries a crashed chunk once and counts the crashes (0 in the 50–200 run).

**Times** (`timing.py`; seconds; algorithm only, no heuristic, in-process for both; JS warm in
one `batch.js` process; hard "no" = the slowest algorithm-decided "no" answers among
candidates from shapes rect / fat / hpath with endpoint modes plausible, inner2, close):

| \|V\| | group | # | Python median / max | JS median / max | median speedup |
|---|---|---|---|---|---|
| ≈ 100 | yes (planted path) | 28 | 0.0023 / 0.288 | 0.0007 / 0.057 | 2.6× |
| ≈ 100 | hard no | 41 | 0.0010 / 1.509 | 0.0002 / 0.104 | 6.2× |
| ≈ 400 | yes (planted path) | 20 | 0.029 / 0.106 | 0.0039 / 0.018 | 8.7× |
| ≈ 400 | hard no (mixed search) | 10 | 0.063 / 0.195 | 0.0041 / 0.027 | 16× |
| ≈ 400 | hard no (rect / fat, inner2 / close) | 12 | 0.115 / 0.190 | 0.0054 / 0.040 | 17× |
| ≈ 1600 | yes (planted path) | 15 | 0.056 / 0.155 | 0.0089 / 0.036 | 6.0× |
| ≈ 1600 | hard no | 6 | 0.157 / 0.234 | 0.0103 / 0.018 | 11× |

The hardest instances seen are `twoHoleCase` "no" answers on rectangles with both endpoints inner,
dominated by the class-pair search: |V| = 137, Python 16.7 s, JS 1.14 s (14.6×); |V| = 89,
Python 1.67 s, JS 0.15 s. A whole `node cli.js` run on a 4-point input takes 37 ms (median of 10; `hpst_cli.py` 55 ms). On a planted
path with |V| = 10,016: Python 2.7 s, JS 0.19 s (no heuristic), JS 0.42 s with the heuristic.

```
cd lib/js
python3 compare.py --sizes 8,12,16,20,24,28,32,36 --count 30 --brute-max 36 --cli-every 25 --seed 11
python3 compare.py --sizes 40,60,100,150 --count 40 --brute-max 0 --cli-every 40 --seed 23
python3 timing.py -n 400 --yes 20 --pl-search 1500 --pl 12 --py-timeout 240
```
