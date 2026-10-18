// SPDX-License-Identifier: CC0-1.0
//
// Fast mode of `decideHamPath` (lean/SolidGridHam/Path/HPFinal.lean) in C99: a port of
// lib/python/hpst_fast.py. Same algorithm, same answer-preserving speedups, same iteration
// orders (with heuristic off, the returned path is the Python fast-mode path):
//
//   S1  integer point ids and flat arrays; sets and dicts become id-indexed arrays, cleared by
//       epoch stamps (`Mark`) instead of being reallocated.
//   S2  pieces: one component labelling per factor state (`labels`), lookups for connB/cutB/critB.
//   S3  findFactor: alternating layers as one BFS (distances), warm start from a greedy edge set.
//   S4  class search: classPotential by a bucket longest-path computation (weights 0 / -1).
//   S5  classes restricted to |h| <= boxWidth, tried by |h| (pairs by |h1| + |h2|).
//   S6  necessary conditions (colour, degrees, 2-connectivity of U plus the edge a-b).
//   S7  memo of failed subproblems (deleted set, a, b) in an open-addressing hash table.
//   S8  heuristic yes-first DFS (Warnsdorff order), node and time boxed, path verified.
//
// Additional C-only changes, all value-identical:
//   * classSearch: the constraint weights (lb_terms) and the outside-cell sources depend only on the
//     factor R and on U, not on the class, so oneHoleFinalTest computes them once per R (`kprep`) and
//     each class only reruns the bucket computation.
//   * planAB flips the bridge end squares in H and flips them back afterwards (flips are
//     involutions) instead of copying H.
// Justifications of S2-S8 are in hpst_fast.py at the corresponding functions.
//
#define _POSIX_C_SOURCE 199309L

#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#include "hpst.h"

typedef unsigned char u8;

const char *hpst_count_names[HPST_NCOUNT] = {
  "walk_nodes", "final_tests", "findFactor", "classSearch", "classSearch_some", "runSC2", "runs_stuck",
  "phases", "bridges", "reductions", "pruned", "memo_hits"
};

const char *hpst_time_names[HPST_NTIME] = {
  "global", "heuristic", "algorithm", "prune", "findFactor", "classes", "loop", "total"
};

// Sides as ints: b, t, l, r (Algorithm.lean `sidesL` order).
//
enum { SB = 0, ST = 1, SL = 2, SR = 3 };
static const int OPPS[4] = { ST, SB, SR, SL };

// ---------------------------------------------------------------------------------------------
// Small utilities.
// ---------------------------------------------------------------------------------------------

static void *xmalloc(size_t n) {
  void *p = malloc( (n == 0) ? 1 : n );
  if (!p) { fprintf(stderr, "hpst: out of memory\n"); abort(); }
  return p;
}

static void *xcalloc(size_t n, size_t k) {
  void *p = calloc( (n == 0) ? 1 : n, (k == 0) ? 1 : k );
  if (!p) { fprintf(stderr, "hpst: out of memory\n"); abort(); }
  return p;
}

static double now(void) {
  struct timespec ts;
  clock_gettime(CLOCK_MONOTONIC, &ts);
  return ((double)ts.tv_sec) + (1e-9 * ((double)ts.tv_nsec));
}

static void cinc(hpst_stats *st, int k) {
  if (st->c[k] == 0) { st->corder[st->nco++] = k; }
  st->c[k]++;
}

static void tadd(hpst_stats *st, int k, double dt) {
  if (!st->ttouched[k]) {
    st->ttouched[k] = 1;
    st->torder[st->nto++] = k;
  }
  st->t[k] += dt;
}

// A set over ids 0..n-1 that is emptied in O(1): an id is in the set iff its stamp equals the
// current epoch.
//
typedef struct {
  unsigned *st;
  unsigned  ep;
  int       n;
} Mark;

static void mark_init(Mark *m, int n) {
  m->st = xcalloc((size_t)n, sizeof(unsigned));
  m->ep = 0;
  m->n  = n;
}

static void mark_new(Mark *m) {
  m->ep++;
  if (m->ep == 0) {
    memset(m->st, 0, ((size_t)m->n) * sizeof(unsigned));
    m->ep = 1;
  }
}

#define MARKED(m, i) ((m)->st[(i)] == (m)->ep)
#define MARK(m, i)   ((m)->st[(i)] = (m)->ep)

static int iabs(int a) { return ( (a < 0) ? -a : a ); }

// A path of point ids with room to prepend and append.
//
typedef struct {
  int  n, cap;
  int *v;
} Path;

static Path *path_new(int cap) {
  Path *P = xmalloc(sizeof(Path));
  P->n   = 0;
  P->cap = cap + 4;
  P->v   = xmalloc(((size_t)P->cap) * sizeof(int));
  return P;
}

static void path_free(Path *P) {
  if (P) {
    free(P->v);
    free(P);
  }
}

static void path_grow(Path *P) {
  if (P->n >= P->cap) {
    P->cap = (2 * P->cap) + 4;
    P->v   = realloc(P->v, ((size_t)P->cap) * sizeof(int));
    if (!P->v) { fprintf(stderr, "hpst: out of memory\n"); abort(); }
  }
}

static void path_append(Path *P, int x) {
  path_grow(P);
  P->v[P->n++] = x;
}

static void path_prepend(Path *P, int x) {
  path_grow(P);
  memmove(P->v + 1, P->v, ((size_t)P->n) * sizeof(int));
  P->v[0] = x;
  P->n++;
}

// ---------------------------------------------------------------------------------------------
// The solver state: grid context (point id = (x - x0) + (y - y0) * Wd over V's box with margin
// 3; edge id = 2 p + d, d = 0 `.h` to p + 1, d = 1 `.v` to p + Wd; cell id = id of its lower-left
// corner), the current set U, the memo, and scratch arrays shared by the (never nested) final
// tests.
// ---------------------------------------------------------------------------------------------

typedef struct { int q, a, k; } Br;

typedef struct {
  uint64_t h;
  int      a, b, off, len, used;
} MemoEnt;

enum { O_FUEL, O_MERGE, O_STUCK, O_ODD, O_TWIST };

typedef struct {
  int x0, y0, Wd, Hd, N;
  u8  *par;
  int *Vids;
  int  nV;
  int  step[4];

  u8  *inU;
  int  cnt;
  int *del;
  int  ndel;

  uint64_t *zob;
  uint64_t  zh;

  int prune, memo;
  int fuelA, fuelG;
  hpst_stats *st;
  int err;

  // Memo (S7).
  //
  MemoEnt *mt;
  size_t   mcap, mcnt;
  int     *mpool;
  size_t   mpn, mpcap;

  // Current U as a list in Lean's order (lexicographic: x-major).
  //
  int *Ul;
  int  nUl;

  // nec / biconnected_plus.
  //
  Mark bim;
  int *disc, *low, *fu, *fpar, *fit;

  // findFactor.
  //
  int *degA, *dist, *fr, *nf, *seen;
  Mark dm;
  u8  *F0;

  // Run (the loop on W = U + {p, q}).
  //
  int *Wl;
  int  nW, nU;
  int *cells;
  int  ncells;
  u8  *isCellR;
  int *lab;
  Mark lm;
  int *stk;
  Mark bfm;
  Mark pairm, brm;
  Br  *bs;
  int  nbs, cbs;
  u8  *plan;
  int *need;

  // classSearch.
  //
  u8          *inS;
  int         *Sl;
  int          nS;
  signed char *wt[4];
  int         *src;
  int         *f;
  u8          *done;
  int         *bhead, *bnext, *bval;
  int          bcap, nbk;

  // The two factor buffers of a final test.
  //
  u8 *R, *G;
} Slv;

static int lex(const Slv *z, int i) {
  return ( ((i % z->Wd) * z->Hd) + (i / z->Wd) );
}

static int eqE(const Slv *z, int e) {
  int p = e >> 1;
  return ( ((e & 1) == 0) ? (p + 1) : (p + z->Wd) );
}

static int otherE(const Slv *z, int e, int y) {
  int p = e >> 1;
  return ( (p == y) ? eqE(z, e) : p );
}

static int loE(const Slv *z, int e) {
  int p = e >> 1;
  return ( ((e & 1) == 0) ? (p - z->Wd) : (p - 1) );
}

// inc4: right, left, up, down edges of p. nbrs4: right, left, up, down neighbours.
//
static void inc4(const Slv *z, int p, int *e) {
  e[0] = 2 * p;
  e[1] = 2 * (p - 1);
  e[2] = (2 * p) + 1;
  e[3] = (2 * (p - z->Wd)) + 1;
}

static void nbrs4(const Slv *z, int p, int *v) {
  v[0] = p + 1;
  v[1] = p - 1;
  v[2] = p + z->Wd;
  v[3] = p - z->Wd;
}

static int sideEdge(const Slv *z, int c, int s) {
  if      (s == SB) { return 2 * c; }
  else if (s == ST) { return 2 * (c + z->Wd); }
  else if (s == SL) { return (2 * c) + 1; }
  else              { return (2 * (c + 1)) + 1; }
}

static int back1(const Slv *z, int c, int s) {
  if      (s == ST) { return c; }
  else if (s == SB) { return c + z->Wd; }
  else if (s == SR) { return c; }
  else              { return c + 1; }
}

static int front1(const Slv *z, int c, int s) {
  if      (s == ST) { return c + z->Wd; }
  else if (s == SB) { return c; }
  else if (s == SR) { return c + 1; }
  else              { return c; }
}

static int back2(const Slv *z, int c, int s) {
  if      (s == ST) { return c + 1; }
  else if (s == SB) { return c + z->Wd + 1; }
  else if (s == SR) { return c + z->Wd; }
  else              { return c + z->Wd + 1; }
}

static int front2(const Slv *z, int c, int s) {
  if      (s == ST) { return c + z->Wd + 1; }
  else if (s == SB) { return c + 1; }
  else if (s == SR) { return c + z->Wd + 1; }
  else              { return c + z->Wd; }
}

static int isCell(const Slv *z, int c) {
  const u8 *u = z->inU;
  return ( u[c] && u[c + 1] && u[c + z->Wd] && u[c + z->Wd + 1] );
}

static int isEdge(const Slv *z, int e) {
  return ( z->inU[e >> 1] && z->inU[eqE(z, e)] );
}

// ---------------------------------------------------------------------------------------------
// Arcs (Arcs.lean) on edge arrays.
// ---------------------------------------------------------------------------------------------

static int up(const Slv *z, const u8 *H, int e) {
  int ine1 = ( ((e & 1) == 0) ? (H[e] != 0) : (H[e] == 0) );
  return ( (z->par[loE(z, e)] != 0) == ine1 );
}

static int outArc(const Slv *z, const u8 *H, int c, int s) {
  int e = sideEdge(z, c, s);
  if ( (s == SB) || (s == SL) ) { return !up(z, H, e); }
  return up(z, H, e);
}

static int alt(const Slv *z, const u8 *H, int c) {
  int b = 2 * c, t = 2 * (c + z->Wd), l = (2 * c) + 1, r = (2 * (c + 1)) + 1;
  return ( ( H[b] && H[t] && (!H[l]) && (!H[r]) ) ||
           ( (!H[b]) && (!H[t]) && H[l] && H[r] ) );
}

static void flip(const Slv *z, u8 *H, int c) {
  H[2 * c]                ^= 1;
  H[2 * (c + z->Wd)]      ^= 1;
  H[(2 * c) + 1]          ^= 1;
  H[(2 * (c + 1)) + 1]    ^= 1;
}

// ---------------------------------------------------------------------------------------------
// U and its list.
// ---------------------------------------------------------------------------------------------

static void fill_Ul(Slv *z) {
  int i, k = 0;
  for (i = 0; i < z->nV; i++) {
    if (z->inU[z->Vids[i]]) { z->Ul[k++] = z->Vids[i]; }
  }
  z->nUl = k;
}

static void sdelete(Slv *z, int p) {
  z->inU[p] = 0;
  z->cnt--;
  z->del[z->ndel++] = p;
  z->zh ^= z->zob[p];
}

static void srestore(Slv *z, int p) {
  z->inU[p] = 1;
  z->cnt++;
  z->ndel--;
  z->zh ^= z->zob[p];
}

// ---------------------------------------------------------------------------------------------
// S6: necessary conditions for a Hamiltonian a-b path in the grid graph on U (hpst_fast.nec).
// Uses z->Ul (the current U).
// ---------------------------------------------------------------------------------------------

// Neighbours of u in the graph U plus the edge a-b, in Python's order (nbrs4, then the extra).
//
static int bnb(const Slv *z, int u, int a, int b, int *out) {
  int v[4], i, k = 0, hasb = 0, hasa = 0;
  nbrs4(z, u, v);
  for (i = 0; i < 4; i++) {
    if (z->inU[v[i]]) {
      out[k++] = v[i];
      if (v[i] == b) { hasb = 1; }
      if (v[i] == a) { hasa = 1; }
    }
  }
  if      ( (u == a) && (!hasb) ) { out[k++] = b; }
  else if ( (u == b) && (!hasa) ) { out[k++] = a; }
  return k;
}

// Iterative Tarjan: is U plus the edge a-b 2-connected?
//
static int biconnected_plus(Slv *z, int a, int b) {
  int root = z->Ul[0], cnt = 1, rootkids = 0, sp = 0;
  int nb[5];

  mark_new(&z->bim);
  MARK(&z->bim, root);
  z->disc[root] = 0;
  z->low[root]  = 0;
  z->fu[0] = root; z->fpar[0] = -1; z->fit[0] = 0;
  sp = 1;
  while (sp > 0) {
    int u = z->fu[sp - 1], par = z->fpar[sp - 1];
    int k = bnb(z, u, a, b, nb), adv = 0;
    while (z->fit[sp - 1] < k) {
      int v = nb[z->fit[sp - 1]++];
      if (!MARKED(&z->bim, v)) {
        MARK(&z->bim, v);
        z->disc[v] = cnt;
        z->low[v]  = cnt;
        cnt++;
        z->fu[sp] = v; z->fpar[sp] = u; z->fit[sp] = 0;
        sp++;
        adv = 1;
        break;
      }
      else if (v != par) {
        if (z->disc[v] < z->low[u]) { z->low[u] = z->disc[v]; }
      }
    }
    if (adv) { continue; }
    sp--;
    if (par >= 0) {
      if (z->low[u] < z->low[par]) { z->low[par] = z->low[u]; }
      if (par == root) {
        rootkids++;
      }
      else if (z->low[u] >= z->disc[par]) {
        return 0;
      }
    }
  }
  if (cnt != z->nUl) { return 0; }
  return ( rootkids <= 1 );
}

static int nec(Slv *z, int a, int b) {
  int n = z->nUl, i, j, blk = 0, wht, ca, cb;
  if ( (!z->inU[a]) || (!z->inU[b]) || (a == b) ) { return 0; }
  if (n == 2) {
    return ( (b == (a + 1)) || (b == (a - 1)) || (b == (a + z->Wd)) || (b == (a - z->Wd)) );
  }
  for (i = 0; i < n; i++) {
    if (!z->par[z->Ul[i]]) { blk++; }
  }
  wht = n - blk;
  ca  = z->par[a];
  cb  = z->par[b];
  if ((n % 2) == 0) {
    if ( (ca == cb) || (blk != wht) ) { return 0; }
  }
  else {
    if (ca != cb) { return 0; }
    if ( (ca == 0) && (blk != (wht + 1)) ) { return 0; }
    if ( (ca == 1) && (wht != (blk + 1)) ) { return 0; }
  }
  for (i = 0; i < n; i++) {
    int p = z->Ul[i], v[4], k = 0;
    nbrs4(z, p, v);
    for (j = 0; j < 4; j++) {
      if (z->inU[v[j]]) { k++; }
    }
    if (k < ( ((p == a) || (p == b)) ? 1 : 2 )) { return 0; }
  }
  return biconnected_plus(z, a, b);
}

// ---------------------------------------------------------------------------------------------
// S3: findFactor (FindFactor.lean), layers as BFS distances, warm start (S3b). Writes F (size 2N);
// returns 1 iff a factor (deg 1 at s, t; 2 elsewhere) exists. Uses z->Ul.
// ---------------------------------------------------------------------------------------------

static int dd(int x, int s, int t) {
  return ( ((x == s) || (x == t)) ? 1 : 2 );
}

static int findFactor(Slv *z, int s, int t, u8 *F) {
  int N2 = 2 * z->N, n = z->nUl, i, it, j;
  int *Ul = z->Ul, *degA = z->degA, *dist = z->dist;
  int e4[4];

  cinc(z->st, HPST_C_DFACTOR);
  memset(F, 0, (size_t)N2);
  for (i = 0; i < n; i++) { degA[Ul[i]] = 0; }

  // S3b warm start: greedy edges with deg <= d.
  //
  for (i = 0; i < n; i++) {
    int x = Ul[i], ee[2];
    ee[0] = 2 * x;
    ee[1] = (2 * x) + 1;
    for (j = 0; j < 2; j++) {
      int e = ee[j];
      if (isEdge(z, e)) {
        int q = eqE(z, e);
        if ( (degA[x] < dd(x, s, t)) && (degA[q] < dd(q, s, t)) ) {
          F[e] = 1;
          degA[x]++;
          degA[q]++;
        }
      }
    }
  }

  for (it = 0; it < (n + 1); it++) {
    int nfr = 0, nseen = 0, k = 0, w = -1, v;
    int *fr = z->fr, *nf = z->nf;

    mark_new(&z->dm);
    for (i = 0; i < n; i++) {
      int x = Ul[i];
      if ( (!z->par[x]) && (degA[x] < dd(x, s, t)) ) {
        MARK(&z->dm, x);
        dist[x] = 0;
        fr[nfr++] = x;
        z->seen[nseen++] = x;
      }
    }
    while ( (nfr > 0) && (k < n) ) {
      int nnf = 0, *tmp;
      for (i = 0; i < nfr; i++) {
        int u = fr[i], blk = !z->par[u];
        inc4(z, u, e4);
        for (j = 0; j < 4; j++) {
          int e = e4[j];
          if ( isEdge(z, e) && ( blk ? (!F[e]) : (F[e] != 0) ) ) {
            int y = otherE(z, e, u);
            if (!MARKED(&z->dm, y)) {
              MARK(&z->dm, y);
              dist[y] = k + 1;
              nf[nnf++] = y;
              z->seen[nseen++] = y;
            }
          }
        }
      }
      tmp = fr; fr = nf; nf = tmp;
      nfr = nnf;
      k++;
    }
    for (i = 0; i < nseen; i++) {
      int x = z->seen[i];
      if ( z->par[x] && (degA[x] < dd(x, s, t)) ) {
        if ( (w < 0) || (lex(z, x) < lex(z, w)) ) { w = x; }
      }
    }
    if (w < 0) { break; }
    memcpy(z->F0, F, (size_t)N2);
    v = w;
    k = n - 1;
    while (k >= 0) {
      int dv = dist[v], blk, ee = -1, want;
      if (dv <= k) {
        k = dv - 1;
        continue;
      }
      blk = !z->par[v];
      inc4(z, v, e4);
      for (j = 0; j < 4; j++) {
        int e = e4[j];
        if (isEdge(z, e)) {
          int o = otherE(z, e, v);
          if ( MARKED(&z->dm, o) && (dist[o] <= k) && ( blk ? (z->F0[e] != 0) : (!z->F0[e]) ) ) {
            ee = e;
            break;
          }
        }
      }
      if (ee < 0) { break; }
      want = ( blk ? 0 : 1 );
      if (F[ee] != want) {
        int dlt = ( want ? 1 : -1 );
        F[ee] = (u8)want;
        degA[ee >> 1]      += dlt;
        degA[eqE(z, ee)]   += dlt;
      }
      v = otherE(z, ee, v);
      k--;
    }
  }
  for (i = 0; i < n; i++) {
    if (degA[Ul[i]] != dd(Ul[i], s, t)) { return 0; }
  }
  return 1;
}

// ---------------------------------------------------------------------------------------------
// The phase and the loop (SAlg.lean, SPhaseAlg.lean, SheffComp.lean, TwoPhS4.lean) on
// W = U + {p, q}. One Run is active at a time; run_setup / run_teardown bracket it.
// ---------------------------------------------------------------------------------------------

static void run_setup(Slv *z, int p, int q) {
  int i;
  z->nU = z->nUl;
  z->nW = 0;
  for (i = 0; i < z->nUl; i++) { z->Wl[z->nW++] = z->Ul[i]; }
  z->Wl[z->nW++] = p;
  z->Wl[z->nW++] = q;
  z->ncells = 0;
  for (i = 0; i < z->nUl; i++) {
    int c = z->Ul[i];
    if (isCell(z, c)) {
      z->cells[z->ncells++] = c;
      z->isCellR[c] = 1;
    }
  }
}

static void run_teardown(Slv *z) {
  int i;
  for (i = 0; i < z->ncells; i++) { z->isCellR[z->cells[i]] = 0; }
  z->ncells = 0;
}

static int labels(Slv *z, const u8 *H) {
  int i, j, k = 0, e4[4];
  mark_new(&z->lm);
  for (i = 0; i < z->nW; i++) {
    int x = z->Wl[i], sp = 0;
    if (MARKED(&z->lm, x)) { continue; }
    MARK(&z->lm, x);
    z->lab[x] = k;
    z->stk[sp++] = x;
    while (sp > 0) {
      int u = z->stk[--sp];
      inc4(z, u, e4);
      for (j = 0; j < 4; j++) {
        if (H[e4[j]]) {
          int v = otherE(z, e4[j], u);
          if (!MARKED(&z->lm, v)) {
            MARK(&z->lm, v);
            z->lab[v] = k;
            z->stk[sp++] = v;
          }
        }
      }
    }
    k++;
  }
  return k;
}

static int conn(const Slv *z, int x, int y) {
  if (x == y) { return 1; }
  return ( MARKED(&z->lm, x) && MARKED(&z->lm, y) && (z->lab[x] == z->lab[y]) );
}

static int cutC(const Slv *z, int c) {
  int Wd = z->Wd;
  return !( conn(z, c, c + 1) && conn(z, c, c + Wd + 1) && conn(z, c, c + Wd) );
}

static int critB(const Slv *z, const u8 *H, int q, int a) {
  int b1 = back1(z, q, a), b2 = back2(z, q, a), f1 = front1(z, q, a), f2 = front2(z, q, a);
  return ( conn(z, b1, b2) && conn(z, f1, f2) && (!conn(z, b1, f1)) &&
           H[sideEdge(z, q, OPPS[a])] && (!H[sideEdge(z, q, a)]) );
}

// Connectivity in a modified state (no labelling): DFS with early exit.
//
static int bfs_conn(Slv *z, const u8 *H, int x, int y) {
  int sp = 0, j, e4[4];
  if (x == y) { return 1; }
  mark_new(&z->bfm);
  MARK(&z->bfm, x);
  z->stk[sp++] = x;
  while (sp > 0) {
    int u = z->stk[--sp];
    inc4(z, u, e4);
    for (j = 0; j < 4; j++) {
      if (H[e4[j]]) {
        int v = otherE(z, e4[j], u);
        if (v == y) { return 1; }
        if (!MARKED(&z->bfm, v)) {
          MARK(&z->bfm, v);
          z->stk[sp++] = v;
        }
      }
    }
  }
  return 0;
}

// scan: 1 = ('row', j), 2 = ('stuck', j), 0 = None.
//
static int scan(const Slv *z, const u8 *H, int q, int a, int *jout) {
  int o = outArc(z, H, q, a), st = z->step[a], j = 1, fuel = z->nU + 1;
  while (fuel > 0) {
    int c;
    if (outArc(z, H, q + ((j - 1) * st), a) != o) {
      *jout = j;
      return 1;
    }
    c = q + (j * st);
    if ( (!z->isCellR[c]) || cutC(z, c) ) {
      *jout = j;
      return 2;
    }
    fuel--;
    j++;
  }
  return 0;
}

static int bcell(const Slv *z, Br b, int j) {
  return ( b.q + (j * z->step[b.a]) );
}

static int bE(const Slv *z, Br b) {
  return bcell(z, b, b.k - 1);
}

static void bs_prepend(Slv *z, Br b) {
  if (z->nbs >= z->cbs) {
    z->cbs = (2 * z->cbs) + 16;
    z->bs  = realloc(z->bs, ((size_t)z->cbs) * sizeof(Br));
    if (!z->bs) { fprintf(stderr, "hpst: out of memory\n"); abort(); }
  }
  memmove(z->bs + 1, z->bs, ((size_t)z->nbs) * sizeof(Br));
  z->bs[0] = b;
  z->nbs++;
}

// SPhaseAlg.lean `phase`. H is modified in place; the bridges go to z->bs (Python BS order);
// returns the outcome kind, with the merge cell or the bridge in *mc / *ob.
//
static int phase(Slv *z, int n, u8 *H, int *mc, Br *ob) {
  int i, a;
  cinc(z->st, HPST_C_PHASES);
  z->nbs = 0;
  mark_new(&z->pairm);
  mark_new(&z->brm);
  labels(z, H);
  for (;;) {
    int found = 0, E;
    Br b = { 0, 0, 0 };
    if (n == 0) { return O_FUEL; }
    for (i = 0; i < z->ncells; i++) {
      int c = z->cells[i];
      if ( alt(z, H, c) && cutC(z, c) && (!MARKED(&z->pairm, c)) ) {
        *mc = c;
        return O_MERGE;
      }
    }
    for (i = 0; ( (i < z->ncells) && (!found) ); i++) {
      int q = z->cells[i];
      if (MARKED(&z->brm, q)) { continue; }
      for (a = 0; a < 4; a++) {
        if (critB(z, H, q, a)) {
          int j, r = scan(z, H, q, a, &j);
          if (r == 1) {
            b.q = q; b.a = a; b.k = j;
            found = 1;
            break;
          }
        }
      }
    }
    if (!found) { return O_STUCK; }
    if ((b.k % 2) == 1) {
      *ob = b;
      return O_ODD;
    }
    E = bE(z, b);
    flip(z, H, E);
    if (!bfs_conn(z, H, back1(z, E, b.a), front1(z, E, b.a))) {
      int j;
      cinc(z->st, HPST_C_BRIDGES);
      bs_prepend(z, b);
      MARK(&z->pairm, bcell(z, b, b.k - 2));
      MARK(&z->pairm, E);
      for (j = 0; j < b.k; j++) { MARK(&z->brm, bcell(z, b, j)); }
      labels(z, H);
      n--;
    }
    else {
      flip(z, H, E);
      *ob = b;
      return O_TWIST;
    }
  }
}

// SheffComp.lean `planAB`: flips the bridge end squares one by one (on H, undone at the end).
//
static void planAB(Slv *z, u8 *H, int u, int v) {
  int i;
  for (i = 0; i < z->nbs; i++) {
    Br b = z->bs[i];
    flip(z, H, bE(z, b));
    if (bfs_conn(z, H, u, v)) {
      z->plan[i] = 1;
      u = back1(z, b.q, b.a);
      v = front1(z, b.q, b.a);
    }
    else {
      z->plan[i] = 0;
    }
  }
  for (i = z->nbs - 1; i >= 0; i--) { flip(z, H, bE(z, z->bs[i])); }
}

static void mergePair(const Slv *z, const u8 *H, int X, int *u, int *v) {
  int a = ( H[2 * X] ? ST : SR );
  *u = back1(z, X, a);
  *v = front1(z, X, a);
}

// SheffComp.lean `goodB` (pairSq in z->pairm); the plan only if some bridge needs it.
//
static int goodB(Slv *z, u8 *H, int X) {
  int i, nn = 0, u, v;
  if ( !( alt(z, H, X) && cutC(z, X) && (!MARKED(&z->pairm, X)) ) ) { return 0; }
  for (i = 0; i < z->nbs; i++) {
    Br b = z->bs[i];
    if (X == (bE(z, b) + z->step[b.a])) { z->need[nn++] = i; }
  }
  if (nn == 0) { return 1; }
  mergePair(z, H, X, &u, &v);
  planAB(z, H, u, v);
  for (i = 0; i < nn; i++) {
    if (!z->plan[z->need[i]]) { return 0; }
  }
  return 1;
}

static void flipRun(const Slv *z, u8 *H, int c, int a, int k) {
  int j, st = z->step[a];
  for (j = 0; j < k; j++) { flip(z, H, c + (j * st)); }
}

// SheffComp.lean `reduceOutC`, in place.
//
static void reduceOutC(Slv *z, u8 *H, int kind, int mc, Br ob) {
  int i, u, v;
  cinc(z->st, HPST_C_REDUCTIONS);
  if (kind == O_MERGE) {
    int X = mc;
    mark_new(&z->pairm);
    for (i = 0; i < z->nbs; i++) {
      MARK(&z->pairm, bcell(z, z->bs[i], z->bs[i].k - 2));
      MARK(&z->pairm, bE(z, z->bs[i]));
    }
    for (i = 0; i < z->ncells; i++) {
      if (goodB(z, H, z->cells[i])) {
        X = z->cells[i];
        break;
      }
    }
    mergePair(z, H, X, &u, &v);
    planAB(z, H, u, v);
    flipRun(z, H, X, SB, 1);
  }
  else {
    u = back1(z, ob.q, ob.a);
    v = front1(z, ob.q, ob.a);
    planAB(z, H, u, v);
    flipRun(z, H, ob.q, ob.a, ob.k);
  }
  for (i = 0; i < z->nbs; i++) {
    Br b = z->bs[i];
    if (z->plan[i]) { flipRun(z, H, b.q, b.a, b.k - 1); }
    else            { flipRun(z, H, bE(z, b), b.a, 1); }
  }
}

// TwoPhS4.lean `runSC2` on H in place; 1 iff it ends with one piece.
//
static int runSC2(Slv *z, int n, u8 *H) {
  cinc(z->st, HPST_C_RUNSC2);
  for (;;) {
    int kind, mc = -1;
    Br ob = { 0, 0, 0 };
    if (labels(z, H) == 1) { return 1; }
    if (n == 0) { return 0; }
    kind = phase(z, z->nW + 1, H, &mc, &ob);
    if ( (kind == O_STUCK) || (kind == O_FUEL) ) {
      cinc(z->st, HPST_C_RUNS_STUCK);
      return 0;
    }
    reduceOutC(z, H, kind, mc, ob);
    n--;
  }
}

static Path *factor_path(Slv *z, u8 *F, int s, int t, int e0, int e1) {
  Path *P = path_new(z->nV);
  int prev = -1, cur = s, e4[4], j;
  F[e0] = 0;
  F[e1] = 0;
  path_append(P, s);
  while (cur != t) {
    int nx = -1, k = 0;
    inc4(z, cur, e4);
    for (j = 0; j < 4; j++) {
      if (F[e4[j]]) {
        int o = otherE(z, e4[j], cur);
        if (o != prev) {
          nx = o;
          k++;
        }
      }
    }
    if ( (k != 1) || (P->n > z->nV) ) {
      z->err = 1;
      path_free(P);
      F[e0] = 1;
      F[e1] = 1;
      return NULL;
    }
    prev = cur;
    cur  = nx;
    path_append(P, cur);
  }
  F[e0] = 1;
  F[e1] = 1;
  return P;
}

// ---------------------------------------------------------------------------------------------
// S4: class search (HoleRelax.lean / HoleTry.lean). kprep computes, for the factor F and the
// current U, the constraint weights wt[i][s] (term i of lowerBound at cell s: 0 below, 1 left, 2 top,
// 3 right) and the sources from cells outside boxSquares (fixed at 0). kpot runs the bucket
// longest-path computation for one class; kcheck and ktoggle are `isAdmissible` and the `jumpEdges` flip.
// ---------------------------------------------------------------------------------------------

static void box(const Slv *z, int *x0, int *x1, int *y0, int *y1) {
  int i;
  *x0 = *y0 = 1 << 30;
  *x1 = *y1 = -(1 << 30);
  for (i = 0; i < z->nUl; i++) {
    int p = z->Ul[i], x = p % z->Wd, y = p / z->Wd;
    if (x < *x0) { *x0 = x; }
    if (x > *x1) { *x1 = x; }
    if (y < *y0) { *y0 = y; }
    if (y > *y1) { *y1 = y; }
  }
}

static int sv(const Slv *z, const u8 *F, int e) {
  return ( up(z, F, e) ? 1 : -1 );
}

static void kprep(Slv *z, const u8 *F) {
  int x0, x1, y0, y1, i, j, Wd = z->Wd;
  box(z, &x0, &x1, &y0, &y1);
  z->nS = 0;
  for (i = 0; i < (x1 - x0); i++) {
    for (j = 0; j < (y1 - y0); j++) {
      int c = (x0 + i) + ((y0 + j) * Wd);
      z->Sl[z->nS++] = c;
      z->inS[c] = 1;
    }
  }
  z->nbk = (2 * (x1 - x0)) + 3;
  for (i = 0; i < z->nS; i++) {
    int s = z->Sl[i], best = -(1 << 30);
    int ee[4], uu[4], below[4];
    ee[0] = 2 * s;              uu[0] = s - Wd;  below[0] = 1;
    ee[1] = (2 * s) + 1;        uu[1] = s - 1;   below[1] = 1;
    ee[2] = 2 * (s + Wd);       uu[2] = s + Wd;  below[2] = 0;
    ee[3] = (2 * (s + 1)) + 1;  uu[3] = s + 1;   below[3] = 0;
    for (j = 0; j < 4; j++) {
      int w = 0;
      if (isEdge(z, ee[j])) {
        int v = sv(z, F, ee[j]);
        w = ( below[j] ? ( (v < 0) ? v : 0 ) : -( (v > 0) ? v : 0 ) );
      }
      z->wt[j][s] = (signed char)w;
      if ( (!z->inS[uu[j]]) && (w > best) ) { best = w; }
    }
    z->src[s] = best;
  }
}

static void kunprep(Slv *z) {
  int i;
  for (i = 0; i < z->nS; i++) { z->inS[z->Sl[i]] = 0; }
  z->nS = 0;
}

static int fval(const Slv *z, int c) {
  return ( z->inS[c] ? z->f[c] : 0 );
}

static void bpush(Slv *z, int s, int v, int W) {
  int b = v + W + 1, k;
  if (z->bcap == 0) { return; }
  k = z->bval[0]++;
  z->bval[k + 1] = s;
  z->bnext[k]    = z->bhead[b];
  z->bhead[b]    = k;
}

// classPotential_fast for the classes (as_[i], hs[i]), i < na. W = boxWidth.
//
static void kpot(Slv *z, const int *as_, const int *hs, int na, int W) {
  int i, j, b, Wd = z->Wd;
  for (i = 0; i < z->nS; i++) {
    int s = z->Sl[i], v = -W;
    for (j = 0; j < na; j++) {
      if (as_[j] == s) {
        v = hs[j];
        break;
      }
    }
    if (z->src[s] > v) { v = z->src[s]; }
    z->f[s]    = v;
    z->done[s] = 0;
  }
  for (b = 0; b < z->nbk; b++) { z->bhead[b] = -1; }
  z->bval[0] = 0;
  for (i = 0; i < z->nS; i++) { bpush(z, z->Sl[i], z->f[z->Sl[i]], W); }
  for (b = z->nbk - 1; b >= 0; b--) {
    while (z->bhead[b] >= 0) {
      int k = z->bhead[b], s = z->bval[k + 1], v = b - W - 1;
      int s2[4], ti[4];
      z->bhead[b] = z->bnext[k];
      if ( z->done[s] || (z->f[s] != v) ) { continue; }
      z->done[s] = 1;
      s2[0] = s + Wd;  ti[0] = 0;
      s2[1] = s + 1;   ti[1] = 1;
      s2[2] = s - Wd;  ti[2] = 2;
      s2[3] = s - 1;   ti[3] = 3;
      for (j = 0; j < 4; j++) {
        int c = s2[j];
        if ( z->inS[c] && (!z->done[c]) ) {
          int nv = v + z->wt[ti[j]][c];
          if (nv > z->f[c]) {
            z->f[c] = nv;
            bpush(z, c, nv, W);
          }
        }
      }
    }
  }
}

static int kcheck(Slv *z, const u8 *F, const int *as_, const int *hs, int na) {
  int i, j, Wd = z->Wd;
  for (i = 0; i < z->nS; i++) {
    int s = z->Sl[i], ee[4];
    ee[0] = 2 * s;
    ee[1] = (2 * s) + 1;
    ee[2] = 2 * (s + Wd);
    ee[3] = (2 * (s + 1)) + 1;
    for (j = 0; j < 4; j++) {
      int e = ee[j], dlt = fval(z, e >> 1) - fval(z, loE(z, e));
      if (dlt != 0) {
        if ( !( isEdge(z, e) && (dlt == sv(z, F, e)) ) ) { return 0; }
      }
    }
  }
  for (j = 0; j < na; j++) {
    if (fval(z, as_[j]) != hs[j]) { return 0; }
  }
  return 1;
}

static void ktoggle(Slv *z, u8 *G) {
  int i, j, Wd = z->Wd;
  for (i = 0; i < z->nS; i++) {
    int s = z->Sl[i], ee[4], ne = 0;
    ee[ne++] = 2 * s;
    ee[ne++] = (2 * s) + 1;
    if (!z->inS[s + Wd]) { ee[ne++] = 2 * (s + Wd); }
    if (!z->inS[s + 1])  { ee[ne++] = (2 * (s + 1)) + 1; }
    for (j = 0; j < ne; j++) {
      int e = ee[j];
      if ( isEdge(z, e) && (fval(z, e >> 1) != fval(z, loE(z, e))) ) { G[e] ^= 1; }
    }
  }
}

// classSearch_fast: G = the factor of class (as_, hs) derived from R, or 0 (none).
//
static int classSearch(Slv *z, const u8 *R, u8 *G, const int *as_, const int *hs, int na, int W) {
  cinc(z->st, HPST_C_KFIND);
  kpot(z, as_, hs, na, W);
  if (!kcheck(z, R, as_, hs, na)) { return 0; }
  cinc(z->st, HPST_C_KFIND_SOME);
  memcpy(G, R, ((size_t)z->N) * 2);
  ktoggle(z, G);
  return 1;
}

// ---------------------------------------------------------------------------------------------
// Memo (S7): failed subproblems keyed by (deleted set, min(a, b), max(a, b)). The key compares
// the full sorted deleted set, so a hash collision never answers wrongly.
// ---------------------------------------------------------------------------------------------

static uint64_t mix64(uint64_t x) {
  x += 0x9e3779b97f4a7c15ULL;
  x  = (x ^ (x >> 30)) * 0xbf58476d1ce4e5b9ULL;
  x  = (x ^ (x >> 27)) * 0x94d049bb133111ebULL;
  return x ^ (x >> 31);
}

static uint64_t mkey(const Slv *z, int a, int b) {
  return mix64( z->zh ^ mix64((((uint64_t)(unsigned)a) << 32) | ((uint64_t)(unsigned)b)) );
}

static int sorted_del(const Slv *z, int *out) {
  int i, j;
  for (i = 0; i < z->ndel; i++) {
    int x = z->del[i];
    for (j = i; ( (j > 0) && (out[j - 1] > x) ); j--) { out[j] = out[j - 1]; }
    out[j] = x;
  }
  return z->ndel;
}

static long memo_find(const Slv *z, int a, int b, const int *sd, int nd, uint64_t h) {
  size_t m = z->mcap - 1, i = (size_t)(h & m);
  if (z->mcap == 0) { return -1; }
  while (z->mt[i].used) {
    const MemoEnt *e = &z->mt[i];
    if ( (e->h == h) && (e->a == a) && (e->b == b) && (e->len == nd) &&
         (memcmp(z->mpool + e->off, sd, ((size_t)nd) * sizeof(int)) == 0) ) {
      return (long)i;
    }
    i = (i + 1) & m;
  }
  return -1;
}

static void memo_insert_raw(Slv *z, MemoEnt e) {
  size_t m = z->mcap - 1, i = (size_t)(e.h & m);
  while (z->mt[i].used) { i = (i + 1) & m; }
  z->mt[i] = e;
}

static void memo_add(Slv *z, int a, int b) {
  int sd[64], *sdp = sd, nd, lo = ( (a < b) ? a : b ), hi = ( (a < b) ? b : a );
  uint64_t h;
  MemoEnt e;
  if (z->ndel > 64) { sdp = xmalloc(((size_t)z->ndel) * sizeof(int)); }
  nd = sorted_del(z, sdp);
  h  = mkey(z, lo, hi);
  if (memo_find(z, lo, hi, sdp, nd, h) >= 0) {
    if (sdp != sd) { free(sdp); }
    return;
  }
  if ((2 * (z->mcnt + 1)) > z->mcap) {
    size_t oc = z->mcap, i;
    MemoEnt *old = z->mt;
    z->mcap = ( (oc == 0) ? 1024 : (2 * oc) );
    z->mt   = xcalloc(z->mcap, sizeof(MemoEnt));
    for (i = 0; i < oc; i++) {
      if (old[i].used) { memo_insert_raw(z, old[i]); }
    }
    free(old);
  }
  if ((z->mpn + (size_t)nd) > z->mpcap) {
    z->mpcap = (2 * z->mpcap) + (size_t)nd + 1024;
    z->mpool = realloc(z->mpool, z->mpcap * sizeof(int));
    if (!z->mpool) { fprintf(stderr, "hpst: out of memory\n"); abort(); }
  }
  memcpy(z->mpool + z->mpn, sdp, ((size_t)nd) * sizeof(int));
  e.h = h; e.a = lo; e.b = hi; e.off = (int)z->mpn; e.len = nd; e.used = 1;
  z->mpn += (size_t)nd;
  memo_insert_raw(z, e);
  z->mcnt++;
  if (sdp != sd) { free(sdp); }
}

static int memo_has(Slv *z, int a, int b) {
  int sd[64], *sdp = sd, nd, lo = ( (a < b) ? a : b ), hi = ( (a < b) ? b : a ), r;
  if (z->mcnt == 0) { return 0; }
  if (z->ndel > 64) { sdp = xmalloc(((size_t)z->ndel) * sizeof(int)); }
  nd = sorted_del(z, sdp);
  r  = ( memo_find(z, lo, hi, sdp, nd, mkey(z, lo, hi)) >= 0 );
  if (sdp != sd) { free(sdp); }
  return r;
}

// S6 + S7: may the subproblem (current U, a, b) have a Hamiltonian path?
//
static int viable(Slv *z, int a, int b) {
  if ( z->memo && memo_has(z, a, b) ) {
    cinc(z->st, HPST_C_MEMO_HITS);
    return 0;
  }
  if (z->prune) {
    double t0 = now();
    int ok;
    fill_Ul(z);
    ok = nec(z, a, b);
    tadd(z->st, HPST_T_PRUNE, now() - t0);
    if (!ok) {
      cinc(z->st, HPST_C_PRUNED);
      return 0;
    }
  }
  return 1;
}

static void failed(Slv *z, int a, int b) {
  if (z->memo) { memo_add(z, a, b); }
}

// ---------------------------------------------------------------------------------------------
// The walks (TwoPhWalk.lean, HoleWalk.lean) and the final tests.
// ---------------------------------------------------------------------------------------------

// TwoPhWalk.lean `isFar`: equal or king distance >= 2.
//
static int isFar(const Slv *z, int t, int s) {
  int dx = iabs((t % z->Wd) - (s % z->Wd)), dy = iabs((t / z->Wd) - (s / z->Wd));
  return ( (t == s) || ( !( (dx <= 1) && (dy <= 1) ) ) );
}

// TwoPhWalk.lean `phantomsOpposed` (StuckL4.lean `Opp`) on ids.
//
static int phantomsOpposed(const Slv *z, int a, int ma, int b, int mb) {
  int Wd = z->Wd, dx = (b % Wd) - (a % Wd), dy = (b / Wd) - (a / Wd);
  return ( ( (dx == 2)  && (iabs(dy) <= 2) && (ma == (a - 1))  && (mb == (b + 1)) ) ||
           ( (dx == -2) && (iabs(dy) <= 2) && (ma == (a + 1))  && (mb == (b - 1)) ) ||
           ( (dy == 2)  && (iabs(dx) <= 2) && (ma == (a - Wd)) && (mb == (b + Wd)) ) ||
           ( (dy == -2) && (iabs(dx) <= 2) && (ma == (a + Wd)) && (mb == (b - Wd)) ) );
}

// SheffBoundary `nbrsL`: (neighbour, edge to it), right, left, up, down.
//
static void nbrsL(const Slv *z, int t, int *p, int *e) {
  p[0] = t + 1;      e[0] = 2 * t;
  p[1] = t - 1;      e[1] = 2 * (t - 1);
  p[2] = t + z->Wd;  e[2] = (2 * t) + 1;
  p[3] = t - z->Wd;  e[3] = (2 * (t - z->Wd)) + 1;
}

static Path *two(Slv *z, int t, int s) {
  int p[4], e[4], i;
  nbrsL(z, t, p, e);
  for (i = 0; i < 4; i++) {
    if (p[i] == s) {
      Path *P = path_new(z->nV);
      path_append(P, s);
      path_append(P, t);
      return P;
    }
  }
  return NULL;
}

// TwoPhWalk.lean `isUsablePhantom`.
//
static int isUsablePhantom(const Slv *z, int s, int q, int t, int x) {
  return ( (!z->inU[x]) && (x != q) && (!phantomsOpposed(z, t, x, s, q)) );
}

// TwoPhS4.lean `hpSheffC2` (final test of boundaryEndpoints).
//
static Path *hpSheffC2(Slv *z, int s, int t, int p, int q, int e0, int e1) {
  Path *res = NULL;
  int ok;
  double t0;
  cinc(z->st, HPST_C_FINAL_TESTS);
  fill_Ul(z);
  t0 = now();
  ok = findFactor(z, s, t, z->R);
  tadd(z->st, HPST_T_DFACTOR, now() - t0);
  if (ok) {
    int g;
    z->R[e0] = 1;
    z->R[e1] = 1;
    t0 = now();
    run_setup(z, p, q);
    g = runSC2(z, z->nUl + 2, z->R);
    run_teardown(z);
    tadd(z->st, HPST_T_LOOP, now() - t0);
    if (g) { res = factor_path(z, z->R, s, t, e0, e1); }
  }
  return res;
}

// HoleWalk.lean `oneHoleFinalTest` / HoleTwoV.lean `twoHoleFinalTest` (r < 0 for one hole). Classes by |h|
// (S5); pairs by |h1| + |h2|, then h1, then h2 (the Python sort key).
//
static Path *oneHoleFinalTest(Slv *z, int s, int w, int t, int r, int q, int e0, int e1) {
  Path *res = NULL;
  int x0, x1, y0, y1, n, narrow;
  cinc(z->st, HPST_C_FINAL_TESTS);
  fill_Ul(z);
  n = z->nUl;
  box(z, &x0, &x1, &y0, &y1);
  narrow = ( ((x1 - x0) < n) && ((y1 - y0) < n) );
  if (narrow) {
    double t0 = now();
    int ok = findFactor(z, s, w, z->R);
    tadd(z->st, HPST_T_DFACTOR, now() - t0);
    if (ok) {
      int kw = x1 - x0, as_[2], hv[2], na, d, done = 0;
      z->R[e0] = 1;
      z->R[e1] = 1;
      run_setup(z, t, q);
      t0 = now();
      kprep(z, z->R);
      tadd(z->st, HPST_T_CLASSES, now() - t0);
      as_[0] = t;
      as_[1] = r;
      na = ( (r < 0) ? 1 : 2 );
      for (d = 0; ( (d <= (na * kw)) && (!done) ); d++) {
        int h1, sg;
        if (na == 1) {
          for (sg = -1; ( (sg <= 1) && (!done) ); sg += 2) {
            int g;
            if ( (d == 0) && (sg == 1) ) { break; }
            hv[0] = sg * d;
            t0 = now();
            g = classSearch(z, z->R, z->G, as_, hv, 1, kw);
            tadd(z->st, HPST_T_CLASSES, now() - t0);
            if (!g) { continue; }
            t0 = now();
            g = runSC2(z, n + 2, z->G);
            tadd(z->st, HPST_T_LOOP, now() - t0);
            if (g) {
              res  = factor_path(z, z->G, s, w, e0, e1);
              done = 1;
            }
          }
          continue;
        }
        for (h1 = -kw; ( (h1 <= kw) && (!done) ); h1++) {
          int rem = d - iabs(h1);
          if ( (rem < 0) || (rem > kw) ) { continue; }
          for (sg = -1; ( (sg <= 1) && (!done) ); sg += 2) {
            int g;
            if ( (rem == 0) && (sg == 1) ) { break; }
            hv[0] = h1;
            hv[1] = sg * rem;
            t0 = now();
            g = classSearch(z, z->R, z->G, as_, hv, 2, kw);
            tadd(z->st, HPST_T_CLASSES, now() - t0);
            if (!g) { continue; }
            t0 = now();
            g = runSC2(z, n + 2, z->G);
            tadd(z->st, HPST_T_LOOP, now() - t0);
            if (g) {
              res  = factor_path(z, z->G, s, w, e0, e1);
              done = 1;
            }
          }
        }
      }
      kunprep(z);
      run_teardown(z);
    }
  }
  return res;
}

// TwoPhWalk.lean `boundaryEndpointsWalk`.
//
static Path *boundaryEndpointsWalk(Slv *z, int s, int q, int e1, int n, int t) {
  int p[4], e[4], i, xi = -1;
  cinc(z->st, HPST_C_WALK_NODES);
  if (n == 0)      { return NULL; }
  if (z->cnt <= 2) { return two(z, t, s); }
  nbrsL(z, t, p, e);
  for (i = 0; i < 4; i++) {
    if (isUsablePhantom(z, s, q, t, p[i])) {
      xi = i;
      break;
    }
  }
  if ( (xi >= 0) && isFar(z, t, s) ) { return hpSheffC2(z, s, t, p[xi], q, e[xi], e1); }
  for (i = 0; i < 4; i++) {
    if ( z->inU[p[i]] && (p[i] != s) ) {
      Path *P = NULL;
      sdelete(z, t);
      if (viable(z, s, p[i])) {
        P = boundaryEndpointsWalk(z, s, q, e1, n - 1, p[i]);
        if (!P) { failed(z, s, p[i]); }
      }
      srestore(z, t);
      if (P) {
        path_append(P, t);
        return P;
      }
      if (z->err) { return NULL; }
    }
  }
  return NULL;
}

// TwoPhWalk.lean `boundaryEndpoints`.
//
static Path *boundaryEndpoints(Slv *z, int s, int t) {
  int p[4], e[4], i;
  if (z->cnt <= 2) { return two(z, t, s); }
  nbrsL(z, s, p, e);
  for (i = 0; i < 4; i++) {
    if (!z->inU[p[i]]) { return boundaryEndpointsWalk(z, s, p[i], e[i], z->fuelA, t); }
  }
  for (i = 0; i < 4; i++) {
    if ( z->inU[p[i]] && (p[i] != t) ) {
      Path *P = NULL;
      sdelete(z, s);
      if (viable(z, p[i], t)) {
        P = boundaryEndpointsWalk(z, p[i], s, e[i], z->fuelA, t);
        if (!P) { failed(z, p[i], t); }
      }
      srestore(z, s);
      if (P) {
        path_prepend(P, s);
        return P;
      }
      if (z->err) { return NULL; }
    }
  }
  return NULL;
}

// HoleWalk.lean `holeCaseWalk` (fin = (t, r, e0); w's phantom pw = t).
//
static Path *holeCaseWalk(Slv *z, int ft, int fr, int fe0, int w, int pw, int n, int s, int q, int e1) {
  int p[4], e[4], i;
  cinc(z->st, HPST_C_WALK_NODES);
  if (n == 0) { return NULL; }
  if (z->cnt <= 2) {
    nbrsL(z, w, p, e);
    for (i = 0; i < 4; i++) {
      if (p[i] == s) {
        Path *P = path_new(z->nV);
        path_append(P, s);
        path_append(P, w);
        return P;
      }
    }
    return NULL;
  }
  if ( isFar(z, w, s) && (!phantomsOpposed(z, w, pw, s, q)) ) { return oneHoleFinalTest(z, s, w, ft, fr, q, fe0, e1); }
  nbrsL(z, s, p, e);
  for (i = 0; i < 4; i++) {
    if ( z->inU[p[i]] && (p[i] != w) ) {
      Path *P = NULL;
      sdelete(z, s);
      if (viable(z, p[i], w)) {
        P = holeCaseWalk(z, ft, fr, fe0, w, pw, n - 1, p[i], s, e[i]);
        if (!P) { failed(z, p[i], w); }
      }
      srestore(z, s);
      if (P) {
        path_prepend(P, s);
        return P;
      }
      if (z->err) { return NULL; }
    }
  }
  return NULL;
}

// HoleWalk.lean `holeCase` with the final test oneHoleFinalTest (r < 0) or twoHoleFinalTest (r = original s).
//
static Path *holeCase(Slv *z, int s, int t, int r) {
  int py[4], ey[4], i, j;
  if (z->cnt <= 2) { return two(z, t, s); }
  nbrsL(z, t, py, ey);
  for (i = 0; i < 4; i++) {
    int y = py[i];
    if ( z->inU[y] && (y != s) ) {
      Path *P = NULL;
      sdelete(z, t);
      if (viable(z, s, y)) {
        if (z->cnt <= 2) {
          int px[4], ex[4];
          nbrsL(z, y, px, ex);
          for (j = 0; j < 4; j++) {
            if (px[j] == s) {
              P = path_new(z->nV);
              path_append(P, s);
              path_append(P, y);
              break;
            }
          }
        }
        else {
          int px[4], ex[4];
          nbrsL(z, s, px, ex);
          for (j = 0; j < 4; j++) {
            int x = px[j];
            if ( z->inU[x] && (x != y) ) {
              Path *P2 = NULL;
              sdelete(z, s);
              if (viable(z, x, y)) {
                P2 = holeCaseWalk(z, t, r, ey[i], y, t, z->fuelG, x, s, ex[j]);
                if (!P2) { failed(z, x, y); }
              }
              srestore(z, s);
              if (P2) {
                path_prepend(P2, s);
                P = P2;
                break;
              }
              if (z->err) { break; }
            }
          }
        }
        if (!P) { failed(z, s, y); }
      }
      srestore(z, t);
      if (P) {
        path_append(P, t);
        return P;
      }
      if (z->err) { return NULL; }
    }
  }
  return NULL;
}

static int isInner(const Slv *z, int p) {
  int Wd = z->Wd;
  return ( isCell(z, p - Wd - 1) && isCell(z, p - Wd) && isCell(z, p - 1) && isCell(z, p) );
}

// HPFinal.lean `decideHamPath` on ids.
//
static Path *hpAllIds(Slv *z, int s, int t) {
  if (isInner(z, s)) {
    Path *P;
    int i;
    if (isInner(z, t)) { return holeCase(z, s, t, s); }
    P = holeCase(z, t, s, -1);
    if (P) {
      for (i = 0; i < (P->n / 2); i++) {
        int x = P->v[i];
        P->v[i] = P->v[P->n - 1 - i];
        P->v[P->n - 1 - i] = x;
      }
    }
    return P;
  }
  if (isInner(z, t)) { return holeCase(z, s, t, -1); }
  return boundaryEndpoints(z, s, t);
}

// ---------------------------------------------------------------------------------------------
// S8: heuristic yes-first, an explicit-stack version of hpst_fast.heuristic_path (same moves in
// the same order: Warnsdorff order, forced moves, connectivity every 4th depth). Returns the
// number of points written to out (n on success) or 0.
// ---------------------------------------------------------------------------------------------

typedef struct {
  int cur, nc, i;
  int cand[4];
} HFrame;

enum { H_CONT, H_FALSE, H_TRUE, H_BUDGET };

typedef struct {
  Slv    *z;
  int     n, s, t, nvis, tx, ty;
  u8     *vis;
  int    *freec, *path, *stk;
  Mark    cm;
  long    nodes, node_box;
  double  t_end;
} Heur;

static int hconnected(Heur *h, int cur) {
  Slv *z = h->z;
  int sp = 0, cntc = 1, j, v[4];
  mark_new(&h->cm);
  MARK(&h->cm, cur);
  h->stk[sp++] = cur;
  while (sp > 0) {
    int u = h->stk[--sp];
    nbrs4(z, u, v);
    for (j = 0; j < 4; j++) {
      int x = v[j];
      if ( z->inU[x] && (!h->vis[x]) && (!MARKED(&h->cm, x)) ) {
        MARK(&h->cm, x);
        cntc++;
        h->stk[sp++] = x;
      }
    }
  }
  return ( cntc == ((h->n - h->nvis) + 1) );
}

static int hexpand(Heur *h, int cur, HFrame *F) {
  Slv *z = h->z;
  int v[4], j, must = -1, nc = 0, cand[4], key1[4], key2[4];
  h->nodes++;
  if ( (h->nodes > h->node_box) || ( ((h->nodes & 255) == 0) && (now() > h->t_end) ) ) {
    return H_BUDGET;
  }
  if (h->nvis == h->n) { return ( (cur == h->t) ? H_TRUE : H_FALSE ); }
  if ( ((h->nvis & 3) == 0) && (!hconnected(h, cur)) ) { return H_FALSE; }
  nbrs4(z, cur, v);
  for (j = 0; j < 4; j++) {
    int x = v[j];
    if ( z->inU[x] && (!h->vis[x]) ) {
      if ( (x == h->t) && (h->nvis < (h->n - 1)) ) { continue; }
      if ( (x != h->t) && (h->freec[x] <= 1) ) {
        if (must >= 0) { return H_FALSE; }
        must = x;
      }
      cand[nc++] = x;
    }
  }
  if (must >= 0) {
    cand[0] = must;
    nc = 1;
  }
  for (j = 0; j < nc; j++) {
    int x = cand[j], k, k1, k2;
    k1 = h->freec[x];
    k2 = iabs((x % z->Wd) - h->tx) + iabs((x / z->Wd) - h->ty);
    for (k = j; ( (k > 0) && ( (key1[k - 1] > k1) || ( (key1[k - 1] == k1) && (key2[k - 1] > k2) ) ) ); k--) {
      key1[k] = key1[k - 1];
      key2[k] = key2[k - 1];
      F->cand[k] = F->cand[k - 1];
    }
    key1[k] = k1;
    key2[k] = k2;
    F->cand[k] = x;
  }
  F->cur = cur;
  F->nc  = nc;
  F->i   = 0;
  return H_CONT;
}

static void hmove(Heur *h, int x, int dlt) {
  Slv *z = h->z;
  int v[4], j;
  nbrs4(z, x, v);
  for (j = 0; j < 4; j++) {
    if (z->inU[v[j]]) { h->freec[v[j]] -= dlt; }
  }
  if (dlt > 0) {
    h->vis[x] = 1;
    h->path[h->nvis++] = x;
  }
  else {
    h->vis[x] = 0;
    h->nvis--;
  }
}

static int heuristic_path(Slv *z, int s, int t, double time_box, long node_box, int *out) {
  Heur h;
  HFrame *fr;
  int i, j, d = 0, r, res = 0, v[4];

  memset(&h, 0, sizeof(h));
  h.z = z; h.n = z->nUl; h.s = s; h.t = t;
  h.tx = t % z->Wd; h.ty = t / z->Wd;
  h.vis   = xcalloc((size_t)z->N, 1);
  h.freec = xcalloc((size_t)z->N, sizeof(int));
  h.path  = out;
  h.stk   = xmalloc(((size_t)z->N) * sizeof(int));
  mark_init(&h.cm, z->N);
  h.node_box = node_box;
  h.t_end    = now() + time_box;
  fr = xmalloc(((size_t)h.n + 2) * sizeof(HFrame));

  for (i = 0; i < z->nUl; i++) {
    int p = z->Ul[i], k = 0;
    nbrs4(z, p, v);
    for (j = 0; j < 4; j++) {
      if (z->inU[v[j]]) { k++; }
    }
    h.freec[p] = k;
  }
  nbrs4(z, s, v);
  for (j = 0; j < 4; j++) {
    if (z->inU[v[j]]) { h.freec[v[j]]--; }
  }
  h.vis[s] = 1;
  h.path[h.nvis++] = s;

  r = hexpand(&h, s, &fr[0]);
  if      (r == H_TRUE)  { res = h.nvis; }
  else if (r == H_CONT) {
    d = 0;
    while (d >= 0) {
      HFrame *F = &fr[d];
      if (F->i < F->nc) {
        int x = F->cand[F->i++], ok = 1;
        hmove(&h, x, 1);
        nbrs4(z, x, v);
        for (j = 0; j < 4; j++) {
          int u = v[j];
          if ( z->inU[u] && (!h.vis[u]) && (u != t) && (h.freec[u] < 1) ) { ok = 0; }
        }
        if (ok) {
          r = hexpand(&h, x, &fr[d + 1]);
          if (r == H_CONT) {
            d++;
            continue;
          }
          if (r == H_TRUE) {
            res = h.nvis;
            break;
          }
          if (r == H_BUDGET) { break; }
        }
        hmove(&h, x, -1);
      }
      else {
        d--;
        if (d >= 0) { hmove(&h, fr[d].cand[fr[d].i - 1], -1); }
      }
    }
  }
  free(h.vis);
  free(h.freec);
  free(h.stk);
  free(h.cm.st);
  free(fr);
  return res;
}

// ---------------------------------------------------------------------------------------------
// Entry points.
// ---------------------------------------------------------------------------------------------

void hpst_default_opts(hpst_opts *o) {
  o->heuristic = 1;
  o->prune     = 1;
  o->memo      = 1;
  o->time_box  = -1.0;
}

static int cmp_pt(const void *a, const void *b) {
  const hpst_pt *p = a, *q = b;
  if (p->x != q->x) { return ( (p->x < q->x) ? -1 : 1 ); }
  if (p->y != q->y) { return ( (p->y < q->y) ? -1 : 1 ); }
  return 0;
}

int hpst_verify_path(const hpst_pt *V, int n, hpst_pt s, hpst_pt t, const hpst_pt *P, int np) {
  hpst_pt *U;
  u8 *used;
  int i, m = 0, ok = 1;
  if ( (np < 1) || (P[0].x != s.x) || (P[0].y != s.y) || (P[np - 1].x != t.x) ||
       (P[np - 1].y != t.y) ) {
    return 0;
  }
  U = xmalloc(((size_t)n + 1) * sizeof(hpst_pt));
  memcpy(U, V, ((size_t)n) * sizeof(hpst_pt));
  qsort(U, (size_t)n, sizeof(hpst_pt), cmp_pt);
  for (i = 0; i < n; i++) {
    if ( (m == 0) || (cmp_pt(&U[m - 1], &U[i]) != 0) ) { U[m++] = U[i]; }
  }
  used = xcalloc((size_t)m + 1, 1);
  if (np != m) { ok = 0; }
  for (i = 0; ( ok && (i < np) ); i++) {
    hpst_pt *f = bsearch(&P[i], U, (size_t)m, sizeof(hpst_pt), cmp_pt);
    if ( (!f) || used[f - U] ) {
      ok = 0;
      break;
    }
    used[f - U] = 1;
    if ( (i > 0) && ((iabs(P[i].x - P[i - 1].x) + iabs(P[i].y - P[i - 1].y)) != 1) ) { ok = 0; }
  }
  free(U);
  free(used);
  return ok;
}

int hpst_solid(const hpst_pt *V, int n) {
  int x0, x1, y0, y1, W, H, i, sp = 0, ok = 1;
  u8 *in, *seen;
  int *stk;
  if (n == 0) { return 1; }
  x0 = x1 = V[0].x;
  y0 = y1 = V[0].y;
  for (i = 1; i < n; i++) {
    if (V[i].x < x0) { x0 = V[i].x; }
    if (V[i].x > x1) { x1 = V[i].x; }
    if (V[i].y < y0) { y0 = V[i].y; }
    if (V[i].y > y1) { y1 = V[i].y; }
  }
  x0--; x1++; y0--; y1++;
  W = x1 - x0 + 1;
  H = y1 - y0 + 1;
  in   = xcalloc((size_t)W * (size_t)H, 1);
  seen = xcalloc((size_t)W * (size_t)H, 1);
  stk  = xmalloc(((size_t)W * (size_t)H) * sizeof(int));
  for (i = 0; i < n; i++) { in[(V[i].x - x0) + ((V[i].y - y0) * W)] = 1; }
  for (i = 0; i < H; i++) {
    int c = i * W;
    if ( (!in[c]) && (!seen[c]) ) {
      seen[c] = 1;
      stk[sp++] = c;
    }
  }
  while (sp > 0) {
    int c = stk[--sp], x = c % W, y = c / W, a, b;
    for (a = -1; a <= 1; a++) {
      for (b = -1; b <= 1; b++) {
        int xx = x + a, yy = y + b, cc;
        if ( (xx < 0) || (xx >= W) || (yy < 0) || (yy >= H) ) { continue; }
        cc = xx + (yy * W);
        if ( (!in[cc]) && (!seen[cc]) ) {
          seen[cc] = 1;
          stk[sp++] = cc;
        }
      }
    }
  }
  for (i = 0; i < (W * H); i++) {
    if ( (!in[i]) && (!seen[i]) ) {
      ok = 0;
      break;
    }
  }
  free(in);
  free(seen);
  free(stk);
  return ok;
}

static void slv_free(Slv *z) {
  int j;
  free(z->par); free(z->Vids); free(z->inU); free(z->del); free(z->zob);
  free(z->mt); free(z->mpool); free(z->Ul);
  free(z->bim.st); free(z->disc); free(z->low); free(z->fu); free(z->fpar); free(z->fit);
  free(z->degA); free(z->dist); free(z->fr); free(z->nf); free(z->seen); free(z->dm.st);
  free(z->F0);
  free(z->Wl); free(z->cells); free(z->isCellR); free(z->lab); free(z->lm.st); free(z->stk);
  free(z->bfm.st); free(z->pairm.st); free(z->brm.st); free(z->bs); free(z->plan);
  free(z->need);
  free(z->inS); free(z->Sl);
  for (j = 0; j < 4; j++) { free(z->wt[j]); }
  free(z->src); free(z->f); free(z->done); free(z->bhead); free(z->bnext); free(z->bval);
  free(z->R); free(z->G);
}

static void slv_init(Slv *z, const hpst_pt *V, int n, const hpst_opts *o, hpst_stats *st) {
  int i, xmin, xmax, ymin, ymax, m = 3, N, x, y, j;
  memset(z, 0, sizeof(*z));
  xmin = xmax = V[0].x;
  ymin = ymax = V[0].y;
  for (i = 1; i < n; i++) {
    if (V[i].x < xmin) { xmin = V[i].x; }
    if (V[i].x > xmax) { xmax = V[i].x; }
    if (V[i].y < ymin) { ymin = V[i].y; }
    if (V[i].y > ymax) { ymax = V[i].y; }
  }
  z->x0 = xmin - m;
  z->y0 = ymin - m;
  z->Wd = (xmax - xmin) + 1 + (2 * m);
  z->Hd = (ymax - ymin) + 1 + (2 * m);
  z->N  = z->Wd * z->Hd;
  N     = z->N;
  z->step[SB] = -z->Wd;
  z->step[ST] = z->Wd;
  z->step[SL] = -1;
  z->step[SR] = 1;
  z->par = xcalloc((size_t)N, 1);
  z->inU = xcalloc((size_t)N, 1);
  z->zob = xmalloc(((size_t)N) * sizeof(uint64_t));
  for (i = 0; i < N; i++) {
    x = i % z->Wd;
    y = i / z->Wd;
    z->par[i] = (u8)((x + z->x0 + y + z->y0) & 1);
    z->zob[i] = mix64(0x5eed0000ULL + (uint64_t)i);
  }
  for (i = 0; i < n; i++) { z->inU[(V[i].x - z->x0) + ((V[i].y - z->y0) * z->Wd)] = 1; }

  // Vids in Lean's (lexicographic, x-major) order.
  //
  z->Vids = xmalloc(((size_t)n + 1) * sizeof(int));
  z->nV   = 0;
  for (x = 0; x < z->Wd; x++) {
    for (y = 0; y < z->Hd; y++) {
      int p = x + (y * z->Wd);
      if (z->inU[p]) { z->Vids[z->nV++] = p; }
    }
  }
  z->cnt   = z->nV;
  z->del   = xmalloc(((size_t)z->nV + 4) * sizeof(int));
  z->prune = ( o ? o->prune : 1 );
  z->memo  = ( o ? o->memo : 1 );
  z->fuelA = 12;
  z->fuelG = 10;
  z->st    = st;

  z->Ul   = xmalloc(((size_t)z->nV + 1) * sizeof(int));
  mark_init(&z->bim, N);
  z->disc = xmalloc(((size_t)N) * sizeof(int));
  z->low  = xmalloc(((size_t)N) * sizeof(int));
  z->fu   = xmalloc(((size_t)N + 1) * sizeof(int));
  z->fpar = xmalloc(((size_t)N + 1) * sizeof(int));
  z->fit  = xmalloc(((size_t)N + 1) * sizeof(int));
  z->degA = xcalloc((size_t)N, sizeof(int));
  z->dist = xmalloc(((size_t)N) * sizeof(int));
  z->fr   = xmalloc(((size_t)N) * sizeof(int));
  z->nf   = xmalloc(((size_t)N) * sizeof(int));
  z->seen = xmalloc(((size_t)N) * sizeof(int));
  mark_init(&z->dm, N);
  z->F0   = xmalloc(((size_t)N) * 2);
  z->Wl      = xmalloc(((size_t)z->nV + 4) * sizeof(int));
  z->cells   = xmalloc(((size_t)z->nV + 1) * sizeof(int));
  z->isCellR = xcalloc((size_t)N, 1);
  z->lab     = xmalloc(((size_t)N) * sizeof(int));
  mark_init(&z->lm, N);
  z->stk     = xmalloc(((size_t)N + 1) * sizeof(int));
  mark_init(&z->bfm, N);
  mark_init(&z->pairm, N);
  mark_init(&z->brm, N);
  z->plan    = xmalloc(((size_t)z->nV + 4) * 2);
  z->need    = xmalloc(((size_t)z->nV + 4) * 2 * sizeof(int));
  z->inS  = xcalloc((size_t)N, 1);
  z->Sl   = xmalloc(((size_t)N) * sizeof(int));
  for (j = 0; j < 4; j++) { z->wt[j] = xcalloc((size_t)N, 1); }
  z->src  = xmalloc(((size_t)N) * sizeof(int));
  z->f    = xmalloc(((size_t)N) * sizeof(int));
  z->done = xcalloc((size_t)N, 1);
  z->bcap  = (5 * N) + 8;
  z->bhead = xmalloc(((size_t)(2 * z->Wd) + 8) * sizeof(int));
  z->bnext = xmalloc(((size_t)z->bcap) * sizeof(int));
  z->bval  = xmalloc(((size_t)z->bcap + 1) * sizeof(int));
  z->R = xmalloc(((size_t)N) * 2);
  z->G = xmalloc(((size_t)N) * 2);
}

int hpst_solve(const hpst_pt *V, int n, hpst_pt s, hpst_pt t, const hpst_opts *opts,
               hpst_pt **path, int *np, hpst_stats *stats) {
  hpst_opts   dopt;
  hpst_stats  dst;
  Slv         z;
  double      T0 = now(), t0;
  int         si = -1, ti = -1, i, res = 0;
  Path       *P = NULL;

  if (!opts) {
    hpst_default_opts(&dopt);
    opts = &dopt;
  }
  if (!stats) { stats = &dst; }
  memset(stats, 0, sizeof(*stats));
  if (path) { *path = NULL; }
  if (np)   { *np = 0; }
  if (n < 1) { return -1; }
  for (i = 0; i < n; i++) {
    if ( (V[i].x == s.x) && (V[i].y == s.y) ) { si = i; }
    if ( (V[i].x == t.x) && (V[i].y == t.y) ) { ti = i; }
  }
  if ( (si < 0) || (ti < 0) || ( (s.x == t.x) && (s.y == t.y) ) ) { return -1; }

  slv_init(&z, V, n, opts, stats);
  si = (s.x - z.x0) + ((s.y - z.y0) * z.Wd);
  ti = (t.x - z.x0) + ((t.y - z.y0) * z.Wd);
  stats->branch = ( isInner(&z, si) ? ( isInner(&z, ti) ? "twoHoleCase" : "oneHoleCase-swap" ) :
                                     ( isInner(&z, ti) ? "oneHoleCase" : "boundaryEndpoints" ) );

  fill_Ul(&z);
  if (opts->prune) {
    int ok;
    t0 = now();
    ok = nec(&z, si, ti);
    tadd(stats, HPST_T_GLOBAL, now() - t0);
    if (!ok) {
      stats->how = "global-reject";
      goto done;
    }
  }
  if (opts->heuristic) {
    double tb = opts->time_box;
    int   *hp = xmalloc(((size_t)z.nV + 1) * sizeof(int)), k;
    if (tb < 0) {
      tb = 0.05 + (0.002 * (double)z.nV);
      if (tb > 2.0) { tb = 2.0; }
    }
    t0 = now();
    fill_Ul(&z);
    k = heuristic_path(&z, si, ti, tb, 2000L + (200L * (long)z.nV), hp);
    tadd(stats, HPST_T_HEURISTIC, now() - t0);
    if (k == z.nV) {
      hpst_pt *Q = xmalloc(((size_t)k) * sizeof(hpst_pt));
      for (i = 0; i < k; i++) {
        Q[i].x = (hp[i] % z.Wd) + z.x0;
        Q[i].y = (hp[i] / z.Wd) + z.y0;
      }
      if (hpst_verify_path(V, n, s, t, Q, k)) {
        free(hp);
        stats->how = "heuristic";
        if (path) { *path = Q; } else { free(Q); }
        if (np)   { *np = k; }
        res = 1;
        goto done;
      }
      free(Q);
    }
    free(hp);
  }
  stats->how = "algorithm";
  t0 = now();
  P  = hpAllIds(&z, si, ti);
  tadd(stats, HPST_T_ALGORITHM, now() - t0);
  if (z.err) {
    path_free(P);
    res = -2;
    goto done;
  }
  if (P) {
    hpst_pt *Q = xmalloc(((size_t)P->n) * sizeof(hpst_pt));
    for (i = 0; i < P->n; i++) {
      Q[i].x = (P->v[i] % z.Wd) + z.x0;
      Q[i].y = (P->v[i] / z.Wd) + z.y0;
    }
    if (path) { *path = Q; } else { free(Q); }
    if (np)   { *np = P->n; }
    path_free(P);
    res = 1;
  }

done:
  slv_free(&z);
  tadd(stats, HPST_T_TOTAL, now() - T0);
  return res;
}
