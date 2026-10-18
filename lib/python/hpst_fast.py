#!/usr/bin/env python3
# SPDX-License-Identifier: CC0-1.0
#
# Fast mode for `decideHamPath` (lean/SolidGridHam/Path/HPFinal.lean). Same algorithm as hpst_ref.py
# (which mirrors Lean line by line), with speedups that never change the yes/no answer. Each
# speedup is marked "SPEEDUP" and justified where it is made. Summary:
#
#   S1  integer point ids and flat arrays (bytearray / list) instead of tuples and frozensets,
#       so the code ports to C / JS; values are the same.
#   S2  pieces: one labelling of the components per factor state, recomputed only after a flip
#       (a bridge flip or a reduction); `connB`, `cutB`, `critB` become O(1) lookups.
#   S3  `findFactor`: the alternating layers by one BFS (distance array) instead of |V| rounds;
#       the walk down the layers jumps to the first layer not containing the point. The result
#       is the same factor as Lean's.
#   S4  class search: `classPotential` (least admissible potential above `kInit`) by a bucket shortest-path
#       computation instead of `kFuel` Jacobi rounds; same potential.
#   S5  classes restricted to |h| <= boxWidth (Lean `hClass_bound`) and tried by |h| ascending.
#   S6  global rejections and walk pruning by necessary conditions for a Hamiltonian a-b path.
#   S7  memoisation of failed subproblems (U, a, b).
#   S8  heuristic yes-first: a time-boxed DFS for a Hamiltonian path; a found path is verified.
#
# Witnesses: with `order='lean'` and `heuristic=False` the returned path is the one ref mode
# returns (S2-S4, S6, S7 only skip calls that return false or compute identical values; S5
# with Lean order only skips classes for which `classSearch` returns none).
#
import sys
import time

sys.setrecursionlimit(1000000)

# Sides as ints: b, t, l, r (Algorithm.lean `sidesL` order).
#
SB, ST, SL, SR = 0, 1, 2, 3
OPP = (ST, SB, SR, SL)


class Stats(object):
  def __init__(self):
    self.c = {}
    self.t = {}

  def inc(self, k, n=1):
    self.c[k] = self.c.get(k, 0) + n

  def add_time(self, k, dt):
    self.t[k] = self.t.get(k, 0.0) + dt


class Timer(object):
  def __init__(self, stats, key):
    self.stats, self.key = stats, key

  def __enter__(self):
    self.t0 = time.perf_counter()
    return self

  def __exit__(self, *a):
    self.stats.add_time(self.key, time.perf_counter() - self.t0)


# ---------------------------------------------------------------------------------------------
# The grid context: point id = (x - x0) + (y - y0) * Wd over V's box with margin 3 (every point,
# cell, phantom and neighbouring cell the algorithm touches lies inside). Edge id = 2 * p + d
# (d = 0: `.h`, to p + 1; d = 1: `.v`, to p + Wd). Cell id = id of its lower-left corner.
# ---------------------------------------------------------------------------------------------

class Ctx(object):
  def __init__(self, V):
    xs = [p[0] for p in V]
    ys = [p[1] for p in V]
    m = 3
    self.x0, self.y0 = min(xs) - m, min(ys) - m
    self.Wd = max(xs) - min(xs) + 1 + (2 * m)
    self.Hd = max(ys) - min(ys) + 1 + (2 * m)
    self.N = self.Wd * self.Hd
    Wd = self.Wd
    self.par = bytearray(self.N)
    self.lexkey = [0] * self.N
    for i in range(self.N):
      x, y = (i % Wd), (i // Wd)
      self.par[i] = ( (x + self.x0 + y + self.y0) & 1 )
      self.lexkey[i] = (x * self.Hd) + y
    self.step = (-Wd, Wd, -1, 1)
    self.Vids = sorted((self.pid(p) for p in V), key=lambda i: self.lexkey[i])

  def pid(self, p):
    return (p[0] - self.x0) + ((p[1] - self.y0) * self.Wd)

  def pt(self, i):
    return ((i % self.Wd) + self.x0, (i // self.Wd) + self.y0)

  # Edges.
  #
  def eR(self, p): return 2 * p
  def eL(self, p): return 2 * (p - 1)
  def eU(self, p): return (2 * p) + 1
  def eD(self, p): return (2 * (p - self.Wd)) + 1

  def inc4(self, p):
    return (2 * p, 2 * (p - 1), (2 * p) + 1, (2 * (p - self.Wd)) + 1)

  def nbrs4(self, p):
    Wd = self.Wd
    return (p + 1, p - 1, p + Wd, p - Wd)

  def eq(self, e):
    p = e >> 1
    return ( (p + 1) if ((e & 1) == 0) else (p + self.Wd) )

  def other(self, e, y):
    p = e >> 1
    return ( self.eq(e) if (p == y) else p )

  def lo(self, e):
    p = e >> 1
    return ( (p - self.Wd) if ((e & 1) == 0) else (p - 1) )

  # Cell sides.
  #
  def sideEdge(self, c, s):
    if   s == SB: return 2 * c
    elif s == ST: return 2 * (c + self.Wd)
    elif s == SL: return (2 * c) + 1
    else:         return (2 * (c + 1)) + 1

  def cellE(self, c):
    Wd = self.Wd
    return (2 * c, 2 * (c + Wd), (2 * c) + 1, (2 * (c + 1)) + 1)

  def back1(self, c, s):
    if   s == ST: return c
    elif s == SB: return c + self.Wd
    elif s == SR: return c
    else:         return c + 1

  def back2(self, c, s):
    if   s == ST: return c + 1
    elif s == SB: return c + self.Wd + 1
    elif s == SR: return c + self.Wd
    else:         return c + self.Wd + 1

  def front1(self, c, s):
    if   s == ST: return c + self.Wd
    elif s == SB: return c
    elif s == SR: return c + 1
    else:         return c

  def front2(self, c, s):
    if   s == ST: return c + self.Wd + 1
    elif s == SB: return c + 1
    elif s == SR: return c + self.Wd + 1
    else:         return c + self.Wd

  def isCell(self, inU, c):
    Wd = self.Wd
    return ( inU[c] and inU[c + 1] and inU[c + Wd] and inU[c + Wd + 1] )


# ---------------------------------------------------------------------------------------------
# Arcs (Arcs.lean) on edge arrays.
# ---------------------------------------------------------------------------------------------

def up(cx, H, e):
  ine1 = ( H[e] if ((e & 1) == 0) else (not H[e]) )
  return ( bool(cx.par[cx.lo(e)]) == bool(ine1) )


def outArc(cx, H, c, s):
  e = cx.sideEdge(c, s)
  if ( (s == SB) or (s == SL) ):
    return (not up(cx, H, e))
  return up(cx, H, e)


def alt(cx, H, c):
  b, t, l, r = cx.cellE(c)
  return ( (H[b] and H[t] and (not H[l]) and (not H[r])) or
           ((not H[b]) and (not H[t]) and H[l] and H[r]) )


def flip(cx, H, c):
  for e in cx.cellE(c):
    H[e] ^= 1


# ---------------------------------------------------------------------------------------------
# S6: necessary conditions for a Hamiltonian a-b path in the grid graph on U.
# SPEEDUP justification: each test is implied by the existence of such a path, so rejecting a
# subproblem that fails one never rejects a subproblem that has a path. Every decision call of
# the algorithm (decideHamPath, boundaryEndpointsWalk, holeCaseWalk, the holeCase branch, the final tests) returns true exactly when
# its subproblem has a Hamiltonian path (Lean: decideHamPath_main, boundaryEndpointsWalk_correct, holeCaseWalk_correct,
# holeCase_branch, hpSheffC2_correct, oneHoleFinalTest_correct, twoHoleFinalTest_correct), so a rejected call would
# have returned false.
#   * |U| = 2: a and b adjacent;
#   * colour balance: the path alternates colours;
#   * every point other than a, b has 2 neighbours in U, and a, b have 1;
#   * U plus the edge a-b is 2-connected (the path plus that edge is a Hamiltonian cycle);
#     this includes connectivity and the cut-vertex conditions.
# ---------------------------------------------------------------------------------------------

def nec(cx, inU, Ul, a, b):
  n = len(Ul)
  if ( (not inU[a]) or (not inU[b]) or (a == b) ):
    return False
  if n == 2:
    return ( b in cx.nbrs4(a) )
  blk = 0
  for p in Ul:
    if not cx.par[p]:
      blk += 1
  wht = n - blk
  ca, cb = cx.par[a], cx.par[b]
  if (n % 2) == 0:
    if ( (ca == cb) or (blk != wht) ):
      return False
  else:
    if ca != cb:
      return False
    if ( (ca == 0) and (blk != (wht + 1)) ):
      return False
    if ( (ca == 1) and (wht != (blk + 1)) ):
      return False
  for p in Ul:
    k = 0
    for v in cx.nbrs4(p):
      if inU[v]:
        k += 1
    if k < ( 1 if ( (p == a) or (p == b) ) else 2 ):
      return False
  return biconnected_plus(cx, inU, Ul, a, b)


# Tarjan (iterative): is the graph on U plus the edge a-b 2-connected?
#
def biconnected_plus(cx, inU, Ul, a, b):
  disc = {}
  low = {}
  root = Ul[0]

  def nb(u):
    out = [v for v in cx.nbrs4(u) if inU[v]]
    if ( (u == a) and (b not in out) ):
      out.append(b)
    elif ( (u == b) and (a not in out) ):
      out.append(a)
    return out

  disc[root] = low[root] = 0
  cnt = 1
  rootkids = 0
  st = [(root, -1, iter(nb(root)))]
  while st:
    u, par, it = st[-1]
    adv = False
    for v in it:
      if v not in disc:
        disc[v] = low[v] = cnt
        cnt += 1
        st.append((v, u, iter(nb(v))))
        adv = True
        break
      elif v != par:
        if disc[v] < low[u]:
          low[u] = disc[v]
    if adv:
      continue
    st.pop()
    if par >= 0:
      if low[u] < low[par]:
        low[par] = low[u]
      if par == root:
        rootkids += 1
      elif low[u] >= disc[par]:
        return False
  if cnt != len(Ul):
    return False
  return ( rootkids <= 1 )


# ---------------------------------------------------------------------------------------------
# S3: findFactor (FindFactor.lean) with the layers as BFS distances.
# SPEEDUP justification: layer k of Lean's `layer` is {z : dist z <= k} for the BFS distance
# from layer 0 along `Fwd` steps (layer k+1 = layer k plus its forward neighbours). Lean's `walk`
# skips the layers containing the point, so jumping to layer dist(v) - 1 is the same walk. The
# `pred` search, the `pick` choice (lexicographic least) and the edge order (`inc4`) are Lean's,
# so the factor is identical.
# ---------------------------------------------------------------------------------------------

# SPEEDUP S3b (`warm`, used when the exact Lean witness is not requested): start the
# augmentation from a greedy edge set (deg <= d) instead of the empty set. Justification: the
# augmentation loop ends at an edge set with no augmenting path, which is maximum (Lean
# `stuck_full` argues from any `Good` set: inside V, deg <= d), and at most |V| + 1 augmentations
# are needed from any start (|F| <= |V|). So the result is a factor iff one exists, as with
# Lean's empty start. The callers use only `IsFactor R` (`findFactor_some`) and "none means no
# factor" (`findFactor_none`), so the answer is unchanged; the start factor, hence possibly the
# path found, may differ.
#
def findFactor(cx, inU, Ul, s, t, stats, warm=False):
  stats.inc('findFactor')
  N2 = 2 * cx.N
  F = bytearray(N2)
  degA = {p: 0 for p in Ul}
  n = len(Ul)

  def dd(z):
    return ( 1 if ( (z == s) or (z == t) ) else 2 )

  def isEdge(e):
    return ( inU[e >> 1] and inU[cx.eq(e)] )

  if warm:
    for z in Ul:
      for e in (cx.eR(z), cx.eU(z)):
        if isEdge(e):
          q = cx.eq(e)
          if ( (degA[z] < dd(z)) and (degA[q] < dd(q)) ):
            F[e] = 1
            degA[z] += 1
            degA[q] += 1

  for _ in range(n + 1):
    dist = {}
    fr = [z for z in Ul if ( (not cx.par[z]) and (degA[z] < dd(z)) )]
    for z in fr:
      dist[z] = 0
    k = 0
    while fr and (k < n):
      nf = []
      for u in fr:
        blk = (not cx.par[u])
        for e in cx.inc4(u):
          if ( isEdge(e) and ( (not F[e]) if blk else F[e] ) ):
            v = cx.other(e, u)
            if v not in dist:
              dist[v] = k + 1
              nf.append(v)
      fr = nf
      k += 1
    w = None
    for z in dist:
      if ( cx.par[z] and (degA[z] < dd(z)) ):
        if ( (w is None) or (cx.lexkey[z] < cx.lexkey[w]) ):
          w = z
    if w is None:
      break
    F0 = bytes(F)
    v = w
    k = n - 1
    while k >= 0:
      dv = dist[v]
      if dv <= k:
        k = dv - 1
        continue
      blk = (not cx.par[v])
      ee = -1
      for e in cx.inc4(v):
        if isEdge(e):
          o = cx.other(e, v)
          do = dist.get(o)
          if ( (do is not None) and (do <= k) and ( F0[e] if blk else (not F0[e]) ) ):
            ee = e
            break
      if ee < 0:
        break
      want = ( 0 if blk else 1 )
      if F[ee] != want:
        F[ee] = want
        dlt = ( 1 if want else -1 )
        degA[ee >> 1] += dlt
        degA[cx.eq(ee)] += dlt
      v = cx.other(ee, v)
      k -= 1
  for z in Ul:
    if degA[z] != dd(z):
      return None
  return F


# ---------------------------------------------------------------------------------------------
# The phase and the loop (SAlg.lean, SPhaseAlg.lean, SheffComp.lean, TwoPhS4.lean).
# SPEEDUP S2 justification: `connB W H x y` (Enum.lean) is "y in the component of x" when H lies
# inside W; one labelling per state answers every query of that state. The labelling is
# recomputed after each flip of the state (a bridge flip), since flips are the only changes.
# `cncomp` is the number of labels. Cells are scanned in Lean's order (lexicographic), so the
# phase makes the same choices as Lean.
# ---------------------------------------------------------------------------------------------

class Run(object):
  def __init__(self, cx, inU, Ul, p, q, stats):
    self.cx = cx
    self.inU = inU
    self.Wl = list(Ul) + [p, q]
    self.inW = set(self.Wl)
    self.nU = len(Ul)
    self.cells = [c for c in Ul if cx.isCell(inU, c)]
    self.cellset = set(self.cells)
    self.stats = stats
    self.lab = {}

  def labels(self, H):
    cx = self.cx
    lab = {}
    k = 0
    for x in self.Wl:
      if x in lab:
        continue
      lab[x] = k
      st = [x]
      while st:
        u = st.pop()
        for e in cx.inc4(u):
          if H[e]:
            v = cx.other(e, u)
            if v not in lab:
              lab[v] = k
              st.append(v)
      k += 1
    self.lab = lab
    return k

  def conn(self, x, y):
    if x == y:
      return True
    a = self.lab.get(x)
    return ( (a is not None) and (a == self.lab.get(y)) )

  def cut(self, c):
    Wd = self.cx.Wd
    return not ( self.conn(c, c + 1) and self.conn(c, c + Wd + 1) and self.conn(c, c + Wd) )

  def critB(self, H, q, a):
    cx = self.cx
    b1, b2, f1, f2 = cx.back1(q, a), cx.back2(q, a), cx.front1(q, a), cx.front2(q, a)
    return ( self.conn(b1, b2) and self.conn(f1, f2) and (not self.conn(b1, f1)) and
             H[cx.sideEdge(q, OPP[a])] and (not H[cx.sideEdge(q, a)]) )

  # Connectivity in a modified state (no labelling): BFS with early exit.
  #
  def bfs_conn(self, H, x, y):
    if x == y:
      return True
    cx = self.cx
    seen = {x}
    st = [x]
    while st:
      u = st.pop()
      for e in cx.inc4(u):
        if H[e]:
          v = cx.other(e, u)
          if v == y:
            return True
          if v not in seen:
            seen.add(v)
            st.append(v)
    return False

  def scan(self, H, q, a):
    cx = self.cx
    o = outArc(cx, H, q, a)
    st = cx.step[a]
    j = 1
    fuel = self.nU + 1
    while fuel > 0:
      if outArc(cx, H, q + ((j - 1) * st), a) != o:
        return ('row', j)
      c = q + (j * st)
      if ( (c not in self.cellset) or self.cut(c) ):
        return ('stuck', j)
      fuel -= 1
      j += 1
    return None

  def bcell(self, b, j):
    return b[0] + (j * self.cx.step[b[1]])

  def bE(self, b):
    return self.bcell(b, b[2] - 1)

  # SPhaseAlg.lean `phase`. H is modified in place; returns (BS, out).
  #
  def phase(self, n, H):
    cx = self.cx
    self.stats.inc('phases')
    BS = []
    pairSq = set()
    brSq = set()
    self.labels(H)
    while True:
      if n == 0:
        return (BS, ('fuel',))
      mc = None
      for c in self.cells:
        if ( alt(cx, H, c) and self.cut(c) and (c not in pairSq) ):
          mc = c
          break
      if mc is not None:
        return (BS, ('merge', mc))
      b = None
      for q in self.cells:
        if q in brSq:
          continue
        for a in (SB, ST, SL, SR):
          if self.critB(H, q, a):
            e = self.scan(H, q, a)
            if ( (e is not None) and (e[0] == 'row') ):
              b = (q, a, e[1])
              break
        if b is not None:
          break
      if b is None:
        return (BS, ('stuck',))
      if (b[2] % 2) == 1:
        return (BS, ('odd', b))
      E = self.bE(b)
      flip(cx, H, E)
      if not self.bfs_conn(H, cx.back1(E, b[1]), cx.front1(E, b[1])):
        self.stats.inc('bridges')
        BS.insert(0, b)
        pairSq.add(self.bcell(b, b[2] - 2))
        pairSq.add(E)
        for j in range(b[2]):
          brSq.add(self.bcell(b, j))
        self.labels(H)
        n -= 1
      else:
        flip(cx, H, E)
        return (BS, ('twist', b))

  # SheffComp.lean `planAB` on a copy of H.
  #
  def planAB(self, H, BS, uv):
    cx = self.cx
    Hc = bytearray(H)
    out = []
    for b in BS:
      flip(cx, Hc, self.bE(b))
      if self.bfs_conn(Hc, uv[0], uv[1]):
        out.append(True)
        uv = (cx.back1(b[0], b[1]), cx.front1(b[0], b[1]))
      else:
        out.append(False)
    return out

  def mergePair(self, H, X):
    a = ( ST if H[2 * X] else SR )
    return (a, (self.cx.back1(X, a), self.cx.front1(X, a)))

  # SheffComp.lean `goodB`. The plan is computed only if some bridge has X beside its end square
  # (otherwise every conjunct is true by its second disjunct); same value.
  #
  def goodB(self, H, BS, pairSq, X):
    cx = self.cx
    if not ( alt(cx, H, X) and self.cut(X) and (X not in pairSq) ):
      return False
    need = [i for i, b in enumerate(BS)
            if X == (self.bE(b) + cx.step[b[1]])]
    if not need:
      return True
    plan = self.planAB(H, BS, self.mergePair(H, X)[1])
    return all(plan[i] for i in need)

  # SheffComp.lean `reduceOutC`; H is consumed.
  #
  def reduceOutC(self, H, BS, out):
    cx = self.cx
    self.stats.inc('reductions')
    kind = out[0]
    if kind == 'merge':
      pairSq = set()
      for b in BS:
        pairSq.add(self.bcell(b, b[2] - 2))
        pairSq.add(self.bE(b))
      X = out[1]
      for Y in self.cells:
        if self.goodB(H, BS, pairSq, Y):
          X = Y
          break
      uv = self.mergePair(H, X)[1]
      first = [(X, 0, 1)]
    else:
      b = out[1]
      uv = (cx.back1(b[0], b[1]), cx.front1(b[0], b[1]))
      first = [(b[0], b[1], b[2])]
    plan = self.planAB(H, BS, uv)
    ops = list(first)
    for b, lw in zip(BS, plan):
      ops.append( (b[0], b[1], b[2] - 1) if lw else (self.bE(b), b[1], 1) )
    for (c, a, k) in ops:
      st = cx.step[a]
      for j in range(k):
        flip(cx, H, c + (j * st))
    return H

  # TwoPhS4.lean `runSC2`. Returns the final factor (bytearray) or None.
  #
  def runSC2(self, n, G):
    self.stats.inc('runSC2')
    H = G
    nW = len(self.Wl)
    while True:
      if self.labels(H) == 1:
        return H
      if n == 0:
        return None
      BS, out = self.phase(nW + 1, H)
      if out[0] in ('stuck', 'fuel'):
        self.stats.inc('runs_stuck')
        return None
      H = self.reduceOutC(H, BS, out)
      n -= 1


def factor_path(cx, F, s, t, drop):
  for e in drop:
    F[e] = 0
  path = [s]
  prev, cur = -1, s
  while cur != t:
    nxt = [cx.other(e, cur) for e in cx.inc4(cur) if F[e]]
    nxt = [v for v in nxt if v != prev]
    if len(nxt) != 1:
      raise RuntimeError("factor_path: not a path")
    prev, cur = cur, nxt[0]
    path.append(cur)
  for e in drop:
    F[e] = 1
  return path


# ---------------------------------------------------------------------------------------------
# S4: class search (HoleRelax.lean / HoleTry.lean).
# SPEEDUP justification: every constraint of `lowerBound` has the form f(s) >= f(u) + w with
# w in {0, -1} (w = min 0 sv or -(max 0 sv), and 0 across non-edges of U); cells outside `boxSquares`
# are fixed at 0. Lean's `relax` iterates f <- max(f, lowerBound f) from `kInit`; with weights <= 0
# there is no positive cycle, so it reaches the least fixed point above `kInit` within
# |boxSquares| + 1 rounds <= `kFuel`, and that is what `classPotential` returns. The least fixed point is the
# longest-path value max(init(u) + path weight); a bucket queue over values (largest first,
# Dial's algorithm, weights 0 / -1) computes it exactly. `isAdmissible` and `jumpEdges` are then Lean's.
# Checked against the faithful classPotential by test_hpst.py (test_kpot).
# ---------------------------------------------------------------------------------------------

def box(cx, Ul):
  xs = [(p % cx.Wd) for p in Ul]
  ys = [(p // cx.Wd) for p in Ul]
  return (min(xs), max(xs), min(ys), max(ys))


def boxSquares(cx, Ul):
  x0, x1, y0, y1 = box(cx, Ul)
  return [ (x0 + i) + ((y0 + j) * cx.Wd) for i in range(x1 - x0) for j in range(y1 - y0) ]


def sv(cx, F, e):
  return ( 1 if up(cx, F, e) else -1 )


# The constraints into cell s: list of (u, w) meaning f(s) >= f(u) + w (lowerBound's four terms).
#
def lb_terms(cx, inU, F, s):
  Wd = cx.Wd
  out = []
  for (e, u, below) in ( (2 * s, s - Wd, True), ((2 * s) + 1, s - 1, True),
                         (2 * (s + Wd), s + Wd, False), ((2 * (s + 1)) + 1, s + 1, False) ):
    if ( inU[e >> 1] and inU[cx.eq(e)] ):
      v = sv(cx, F, e)
      w = ( min(0, v) if below else -max(0, v) )
    else:
      w = 0
    out.append((u, w))
  return out


def classPotential_fast(cx, inU, Ul, F, as_, hs):
  S = boxSquares(cx, Ul)
  x0, x1, y0, y1 = box(cx, Ul)
  W = x1 - x0
  look = {}
  for a, h in zip(as_, hs):
    if a not in look:
      look[a] = h
  inS = set(S)
  f = {s: look.get(s, -W) for s in S}
  # Reverse adjacency: when f(u) is final, push f(u) + w to each s with a term (u, w).
  #
  outs = {}
  for s in S:
    for (u, w) in lb_terms(cx, inU, F, s):
      outs.setdefault(u, []).append((s, w))
  # Cells outside S are fixed at 0 and act as sources.
  #
  for u in list(outs.keys()):
    if u not in inS:
      for (s, w) in outs[u]:
        if (0 + w) > f[s]:
          f[s] = 0 + w
  buckets = {}
  for s in S:
    buckets.setdefault(f[s], []).append(s)
  done = set()
  while buckets:
    v = max(buckets)
    lst = buckets.pop(v)
    for s in lst:
      if ( (s in done) or (f[s] != v) ):
        continue
      done.add(s)
      for (s2, w) in outs.get(s, ()):
        if ( (s2 not in done) and ((v + w) > f[s2]) ):
          f[s2] = v + w
          buckets.setdefault(v + w, []).append(s2)
  return f


def isAdmissible_fast(cx, inU, S, F, f, as_, hs):
  Wd = cx.Wd
  for s in S:
    for e in (2 * s, (2 * s) + 1, 2 * (s + Wd), (2 * (s + 1)) + 1):
      hi = e >> 1
      lo = cx.lo(e)
      dlt = f.get(hi, 0) - f.get(lo, 0)
      if dlt != 0:
        if not ( inU[e >> 1] and inU[cx.eq(e)] and (dlt == sv(cx, F, e)) ):
          return False
  for a, h in zip(as_, hs):
    if f.get(a, 0) != h:
      return False
  return True


def classSearch_fast(cx, inU, Ul, F, as_, hs, stats):
  stats.inc('classSearch')
  f = classPotential_fast(cx, inU, Ul, F, as_, hs)
  S = boxSquares(cx, Ul)
  if not isAdmissible_fast(cx, inU, S, F, f, as_, hs):
    return None
  stats.inc('classSearch_some')
  G = bytearray(F)
  Wd = cx.Wd
  seen = set()
  for s in S:
    for e in (2 * s, (2 * s) + 1, 2 * (s + Wd), (2 * (s + 1)) + 1):
      if e in seen:
        continue
      seen.add(e)
      if ( inU[e >> 1] and inU[cx.eq(e)] and (f.get(e >> 1, 0) != f.get(cx.lo(e), 0)) ):
        G[e] ^= 1
  return G


# ---------------------------------------------------------------------------------------------
# The solver: walks (TwoPhWalk.lean, HoleWalk.lean) and final tests, on a mutable set U.
# ---------------------------------------------------------------------------------------------

class Solver(object):
  def __init__(self, V, order='abs', prune=True, memo=True, leaf_hook=None):
    self.cx = Ctx(V)
    cx = self.cx
    self.inU = bytearray(cx.N)
    for p in cx.Vids:
      self.inU[p] = 1
    self.cnt = len(cx.Vids)
    self.deleted = []
    self.order = order
    # Lean fuels: `boundaryEndpoints` calls `boundaryEndpointsWalk` with 12, `holeCase` calls `holeCaseWalk` with 10.
    #
    self.fuelA, self.fuelG = 12, 10
    self.prune = prune
    self.memo = memo
    self.fail = set()
    self.stats = Stats()
    self.leaf_hook = leaf_hook

  def Ul(self):
    inU = self.inU
    return [p for p in self.cx.Vids if inU[p]]

  def delete(self, p):
    self.inU[p] = 0
    self.cnt -= 1
    self.deleted.append(p)

  def restore(self, p):
    self.inU[p] = 1
    self.cnt += 1
    self.deleted.pop()

  def key(self, a, b):
    return (frozenset(self.deleted), min(a, b), max(a, b))

  # S6 + S7: may the subproblem (current U, a, b) have a Hamiltonian path?
  # SPEEDUP justification: see `nec`; a memoised failure is a subproblem on which a call already
  # returned false, and every call on it returns the same value (it decides the subproblem).
  #
  def viable(self, a, b):
    if ( self.memo and (self.key(a, b) in self.fail) ):
      self.stats.inc('memo_hits')
      return False
    if self.prune:
      with Timer(self.stats, 'prune'):
        ok = nec(self.cx, self.inU, self.Ul(), a, b)
      if not ok:
        self.stats.inc('pruned')
        return False
    return True

  def failed(self, a, b):
    if self.memo:
      self.fail.add(self.key(a, b))

  # TwoPhWalk.lean `isFar`: equal or king distance >= 2.
  #
  def isFar(self, t, s):
    cx = self.cx
    dx = abs((t % cx.Wd) - (s % cx.Wd))
    dy = abs((t // cx.Wd) - (s // cx.Wd))
    return ( (t == s) or (not ( (dx <= 1) and (dy <= 1) )) )

  # TwoPhWalk.lean `phantomsOpposed` (StuckL4.lean `Opp`) on ids.
  #
  def phantomsOpposed(self, a, ma, b, mb):
    Wd = self.cx.Wd
    dx = (b % Wd) - (a % Wd)
    dy = (b // Wd) - (a // Wd)
    return ( ( (dx == 2) and (abs(dy) <= 2) and (ma == (a - 1)) and (mb == (b + 1)) ) or
             ( (dx == -2) and (abs(dy) <= 2) and (ma == (a + 1)) and (mb == (b - 1)) ) or
             ( (dy == 2) and (abs(dx) <= 2) and (ma == (a - Wd)) and (mb == (b + Wd)) ) or
             ( (dy == -2) and (abs(dx) <= 2) and (ma == (a + Wd)) and (mb == (b - Wd)) ) )

  # TwoPhWalk.lean `isUsablePhantom`.
  #
  def isUsablePhantom(self, s, q, t, x):
    return ( (not self.inU[x[0]]) and (x[0] != q) and (not self.phantomsOpposed(t, x[0], s, q)) )

  def nbrsL(self, t):
    cx = self.cx
    return ((t + 1, cx.eR(t)), (t - 1, cx.eL(t)), (t + cx.Wd, cx.eU(t)), (t - cx.Wd, cx.eD(t)))

  def two(self, t, s):
    for x in self.nbrsL(t):
      if x[0] == s:
        return [s, t]
    return None

  # TwoPhS4.lean `hpSheffC2` (final test of boundaryEndpoints).
  #
  def hpSheffC2(self, s, t, p, q, e0, e1):
    st = self.stats
    st.inc('final_tests')
    Ul = self.Ul()
    with Timer(st, 'findFactor'):
      R = findFactor(self.cx, self.inU, Ul, s, t, st, warm=(self.order != 'lean'))
    res = None
    if R is not None:
      R[e0] = 1
      R[e1] = 1
      with Timer(st, 'loop'):
        G = Run(self.cx, self.inU, Ul, p, q, st).runSC2(len(Ul) + 2, R)
      if G is not None:
        res = factor_path(self.cx, G, s, t, (e0, e1))
    if self.leaf_hook:
      self.leaf_hook(self, s, t, res)
    return res

  def classes(self, Ul):
    n = len(Ul)
    x0, x1, y0, y1 = box(self.cx, Ul)
    kw = x1 - x0
    hs = [ (i - n) for i in range(2 * n + 1) ]
    # S5. SPEEDUP justification: Lean `hClass_bound` gives |class| <= boxWidth for every factor
    # agreeing with F off U, and `classSearch_sound` says classSearch returns some only for a class that has
    # such a factor, so classSearch returns none for |h| > boxWidth. Classes are independent (the loop in
    # each class decides "a Hamiltonian path in this class"), so the order only changes which
    # path is found first.
    #
    hs = [h for h in hs if abs(h) <= kw]
    if self.order == 'abs':
      hs.sort(key=lambda h: (abs(h), h))
    return hs

  # HoleWalk.lean `oneHoleFinalTest` / HoleTwoV.lean `twoHoleFinalTest` (r = None for one hole).
  #
  def oneHoleFinalTest(self, s, w, t, r, q, e0, e1):
    cx = self.cx
    st = self.stats
    st.inc('final_tests')
    Ul = self.Ul()
    res = None
    x0, x1, y0, y1 = box(cx, Ul)
    narrow = ( ((x1 - x0) < len(Ul)) and ((y1 - y0) < len(Ul)) )
    if narrow:
      with Timer(st, 'findFactor'):
        R = findFactor(cx, self.inU, Ul, s, w, st, warm=(self.order != 'lean'))
      if R is not None:
        R[e0] = 1
        R[e1] = 1
        hs = self.classes(Ul)
        if r is None:
          cl = [([t], [h]) for h in hs]
        else:
          cl = [([t, r], [h1, h2]) for h1 in hs for h2 in hs]
          if self.order == 'abs':
            cl.sort(key=lambda x: (abs(x[1][0]) + abs(x[1][1]), x[1]))
        for as_, hv in cl:
          with Timer(st, 'classes'):
            G = classSearch_fast(cx, self.inU, Ul, R, as_, hv, st)
          if G is None:
            continue
          with Timer(st, 'loop'):
            G2 = Run(cx, self.inU, Ul, t, q, st).runSC2(len(Ul) + 2, G)
          if G2 is not None:
            res = factor_path(cx, G2, s, w, (e0, e1))
            break
    if self.leaf_hook:
      self.leaf_hook(self, s, w, res)
    return res

  # TwoPhWalk.lean `boundaryEndpointsWalk`.
  #
  def boundaryEndpointsWalk(self, s, q, e1, n, t):
    self.stats.inc('walk_nodes')
    if n == 0:
      return None
    if self.cnt <= 2:
      return self.two(t, s)
    x = None
    for y in self.nbrsL(t):
      if self.isUsablePhantom(s, q, t, y):
        x = y
        break
    if ( (x is not None) and self.isFar(t, s) ):
      return self.hpSheffC2(s, t, x[0], q, x[1], e1)
    for y in self.nbrsL(t):
      if ( self.inU[y[0]] and (y[0] != s) ):
        self.delete(t)
        P = None
        if self.viable(s, y[0]):
          P = self.boundaryEndpointsWalk(s, q, e1, n - 1, y[0])
          if P is None:
            self.failed(s, y[0])
        self.restore(t)
        if P is not None:
          return P + [t]
    return None

  # TwoPhWalk.lean `boundaryEndpoints`.
  #
  def boundaryEndpoints(self, s, t):
    if self.cnt <= 2:
      return self.two(t, s)
    x = None
    for y in self.nbrsL(s):
      if not self.inU[y[0]]:
        x = y
        break
    if x is not None:
      return self.boundaryEndpointsWalk(s, x[0], x[1], self.fuelA, t)
    for y in self.nbrsL(s):
      if ( self.inU[y[0]] and (y[0] != t) ):
        self.delete(s)
        P = None
        if self.viable(y[0], t):
          P = self.boundaryEndpointsWalk(y[0], s, y[1], self.fuelA, t)
          if P is None:
            self.failed(y[0], t)
        self.restore(s)
        if P is not None:
          return [s] + P
    return None

  # HoleWalk.lean `holeCaseWalk` (fin = (t, r, e0); w's phantom pw = t).
  #
  def holeCaseWalk(self, fin, w, pw, n, s, q, e1):
    self.stats.inc('walk_nodes')
    if n == 0:
      return None
    if self.cnt <= 2:
      for x in self.nbrsL(w):
        if x[0] == s:
          return [s, w]
      return None
    if ( self.isFar(w, s) and (not self.phantomsOpposed(w, pw, s, q)) ):
      t, r, e0 = fin
      return self.oneHoleFinalTest(s, w, t, r, q, e0, e1)
    for x in self.nbrsL(s):
      if ( self.inU[x[0]] and (x[0] != w) ):
        self.delete(s)
        P = None
        if self.viable(x[0], w):
          P = self.holeCaseWalk(fin, w, pw, n - 1, x[0], s, x[1])
          if P is None:
            self.failed(x[0], w)
        self.restore(s)
        if P is not None:
          return [s] + P
    return None

  # HoleWalk.lean `holeCase` with the final test oneHoleFinalTest (r = None) or twoHoleFinalTest (r = original s).
  #
  def holeCase(self, s, t, r):
    if self.cnt <= 2:
      return self.two(t, s)
    for y in self.nbrsL(t):
      if ( self.inU[y[0]] and (y[0] != s) ):
        self.delete(t)
        P = None
        if self.viable(s, y[0]):
          if self.cnt <= 2:
            for x in self.nbrsL(y[0]):
              if x[0] == s:
                P = [s, y[0]]
                break
          else:
            for x in self.nbrsL(s):
              if ( self.inU[x[0]] and (x[0] != y[0]) ):
                self.delete(s)
                P2 = None
                if self.viable(x[0], y[0]):
                  P2 = self.holeCaseWalk((t, r, y[1]), y[0], t, self.fuelG, x[0], s, x[1])
                  if P2 is None:
                    self.failed(x[0], y[0])
                self.restore(s)
                if P2 is not None:
                  P = [s] + P2
                  break
          if P is None:
            self.failed(s, y[0])
        self.restore(t)
        if P is not None:
          return P + [t]
    return None

  def isInner(self, p):
    cx = self.cx
    Wd = cx.Wd
    return ( cx.isCell(self.inU, p - Wd - 1) and cx.isCell(self.inU, p - Wd) and
             cx.isCell(self.inU, p - 1) and cx.isCell(self.inU, p) )

  # HPFinal.lean `decideHamPath` on ids.
  #
  def decideHamPath(self, s, t):
    if self.isInner(s):
      if self.isInner(t):
        return self.holeCase(s, t, s)
      P = self.holeCase(t, s, None)
      return ( None if (P is None) else P[::-1] )
    if self.isInner(t):
      return self.holeCase(s, t, None)
    return self.boundaryEndpoints(s, t)


# ---------------------------------------------------------------------------------------------
# S8: heuristic yes-first. DFS from s with Warnsdorff ordering (fewest free neighbours first),
# the degree rule and periodic connectivity checks, within a node budget and a time box.
# SPEEDUP justification: a returned path is checked by `verify_path` before it is used, so a
# "yes" from here is correct; on failure or timeout the full algorithm runs.
# ---------------------------------------------------------------------------------------------

class _Budget(Exception):
  pass


def heuristic_path(cx, inU, Ul, s, t, time_box, node_box):
  n = len(Ul)
  vis = {s}
  free = {}
  for p in Ul:
    free[p] = sum(1 for v in cx.nbrs4(p) if inU[v])
  for v in cx.nbrs4(s):
    if inU[v]:
      free[v] -= 1
  path = [s]
  t_end = time.perf_counter() + time_box
  nodes = [0]
  tx, ty = (t % cx.Wd), (t // cx.Wd)

  def connected(cur):
    seen = {cur}
    st = [cur]
    while st:
      u = st.pop()
      for v in cx.nbrs4(u):
        if ( inU[v] and (v not in vis) and (v not in seen) ):
          seen.add(v)
          st.append(v)
    return ( len(seen) == ((n - len(vis)) + 1) )

  def dfs(cur):
    nodes[0] += 1
    if ( (nodes[0] > node_box) or (((nodes[0] & 255) == 0) and (time.perf_counter() > t_end)) ):
      raise _Budget()
    if len(vis) == n:
      return ( cur == t )
    if ( ((len(vis) & 3) == 0) and (not connected(cur)) ):
      return False
    cand = []
    must = None
    for v in cx.nbrs4(cur):
      if ( inU[v] and (v not in vis) ):
        if ( (v == t) and (len(vis) < (n - 1)) ):
          continue
        if ( (v != t) and (free[v] <= 1) ):
          if must is not None:
            return False
          must = v
        cand.append(v)
    if must is not None:
      cand = [must]
    # A neighbour other than t left with fewer than 2 free neighbours after this step is dead.
    #
    cand.sort(key=lambda v: (free[v], abs((v % cx.Wd) - tx) + abs((v // cx.Wd) - ty)))
    for v in cand:
      vis.add(v)
      path.append(v)
      for u in cx.nbrs4(v):
        if inU[u]:
          free[u] -= 1
      ok = True
      for u in cx.nbrs4(v):
        if ( inU[u] and (u not in vis) and (u != t) and (free[u] < 1) ):
          ok = False
      if ( ok and dfs(v) ):
        return True
      for u in cx.nbrs4(v):
        if inU[u]:
          free[u] += 1
      path.pop()
      vis.discard(v)
    return False

  try:
    if dfs(s):
      return list(path)
  except _Budget:
    return None
  return None


# ---------------------------------------------------------------------------------------------
# Entry point.
# ---------------------------------------------------------------------------------------------

def verify_path(V, s, t, P):
  V = set(V)
  if ( (not P) or (P[0] != s) or (P[-1] != t) or (len(P) != len(V)) or (set(P) != V) ):
    return False
  for a, b in zip(P, P[1:]):
    if ( (abs(a[0] - b[0]) + abs(a[1] - b[1])) != 1 ):
      return False
  return True


LAST = {'stats': None, 'branch': None, 'how': None}


# Returns a Hamiltonian path s..t (list of points) or None. `how` in LAST records whether the
# answer came from the global rejection, the heuristic or the algorithm.
#
def decideHamPath(V, s, t, heuristic=True, order='abs', prune=True, memo=True,
          time_box=None, leaf_hook=None):
  V = frozenset(V)
  T0 = time.perf_counter()
  sv_ = Solver(V, order=order, prune=prune, memo=memo, leaf_hook=leaf_hook)
  cx = sv_.cx
  st = sv_.stats
  LAST['stats'] = st
  si, ti = cx.pid(s), cx.pid(t)
  LAST['branch'] = ( ('twoHoleCase' if sv_.isInner(ti) else 'oneHoleCase-swap') if sv_.isInner(si) else
                     ('oneHoleCase' if sv_.isInner(ti) else 'boundaryEndpoints') )
  res = None
  try:
    # S6 global rejection.
    #
    if prune:
      with Timer(st, 'global'):
        ok = nec(cx, sv_.inU, sv_.Ul(), si, ti)
      if not ok:
        LAST['how'] = 'global-reject'
        return None
    if heuristic:
      n = len(V)
      tb = ( time_box if (time_box is not None) else min(2.0, 0.05 + (0.002 * n)) )
      with Timer(st, 'heuristic'):
        P = heuristic_path(cx, sv_.inU, sv_.Ul(), si, ti, tb, 2000 + (200 * n))
      if P is not None:
        Pp = [cx.pt(i) for i in P]
        if verify_path(V, s, t, Pp):
          LAST['how'] = 'heuristic'
          res = Pp
          return Pp
    LAST['how'] = 'algorithm'
    with Timer(st, 'algorithm'):
      P = sv_.decideHamPath(si, ti)
    res = ( None if (P is None) else [cx.pt(i) for i in P] )
    return res
  finally:
    st.add_time('total', time.perf_counter() - T0)


# Old entry point name (Lean `hpAll` before the 2026-10-18 rename), kept as an alias.
#
hpAll = decideHamPath
