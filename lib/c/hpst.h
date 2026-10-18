// SPDX-License-Identifier: CC0-1.0
//
// Hamiltonian s-t paths in solid grid graphs: C port of the fast mode of the Lean-verified
// decision procedure `decideHamPath` (lean/ULHC/HP/Sheffield/HPFinal.lean), following
// lib/python/hpst_fast.py speedup for speedup (S1-S8). See lib/README.md.
//
#ifndef HPST_H
#define HPST_H

typedef struct { int x, y; } hpst_pt;

// Counters; names (the Python keys) in hpst_count_names.
//
enum {
  HPST_C_WALK_NODES, HPST_C_FINAL_TESTS, HPST_C_DFACTOR, HPST_C_KFIND, HPST_C_KFIND_SOME,
  HPST_C_RUNSC2, HPST_C_RUNS_STUCK, HPST_C_PHASES, HPST_C_BRIDGES, HPST_C_REDUCTIONS,
  HPST_C_PRUNED, HPST_C_MEMO_HITS, HPST_NCOUNT
};

// Timers (seconds); names in hpst_time_names.
//
enum {
  HPST_T_GLOBAL, HPST_T_HEURISTIC, HPST_T_ALGORITHM, HPST_T_PRUNE, HPST_T_DFACTOR,
  HPST_T_CLASSES, HPST_T_LOOP, HPST_T_TOTAL, HPST_NTIME
};

// corder / torder record the first-touch order of the counters and timers, so the CLI can
// print them in the order the Python dicts would have.
//
typedef struct {
  long long c[HPST_NCOUNT];
  double    t[HPST_NTIME];

  int corder[HPST_NCOUNT], nco;
  int torder[HPST_NTIME],  nto;
  int ttouched[HPST_NTIME];

  const char *branch;
  const char *how;
} hpst_stats;

typedef struct {
  int    heuristic;
  int    prune;
  int    memo;
  double time_box;
} hpst_opts;

extern const char *hpst_count_names[HPST_NCOUNT];
extern const char *hpst_time_names[HPST_NTIME];

// heuristic = prune = memo = 1; time_box < 0 means the Python default
// min(2, 0.05 + 0.002 |V|) seconds.
//
void hpst_default_opts(hpst_opts *o);

// Decide whether the grid graph on V (n points, duplicates ignored, assumed solid) has a
// Hamiltonian path from s to t.
// Returns 1 (yes: *path gets a malloc'd array of *np points from s to t, the caller frees it),
// 0 (no), -1 (bad input: s or t not in V, or s == t), -2 (internal error: a final factor that
// is not a path; never expected). `opts` and `stats` may be NULL. Out of memory aborts.
// stats->branch is "boundaryEndpoints", "oneHoleCase", "oneHoleCase-swap" or "twoHoleCase"; stats->how is "global-reject",
// "heuristic" or "algorithm".
//
int hpst_solve(const hpst_pt *V, int n, hpst_pt s, hpst_pt t, const hpst_opts *opts,
               hpst_pt **path, int *np, hpst_stats *stats);

// 1 iff P starts at s, ends at t, visits every point of V once, consecutive points adjacent.
//
int hpst_verify_path(const hpst_pt *V, int n, hpst_pt s, hpst_pt t, const hpst_pt *P, int np);

// 1 iff V is solid: every missing point of the box reaches the outside by king moves through
// missing points.
//
int hpst_solid(const hpst_pt *V, int n);

#endif
