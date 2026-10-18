#!/usr/bin/env python3
# SPDX-License-Identifier: CC0-1.0
#
# Faithful Python port of the Lean decision procedure `decideHamPath` (lean/ULHC/HP/Sheffield/HPFinal.lean)
# for Hamiltonian s-t paths in solid grid graphs.
#
# Every Lean definition on the call path of `decideHamPath` has a Python function of the same name
# (camelCase kept), with the Lean file cited above it. Control flow, fuel constants and
# iteration orders are those of Lean. The two-phantom loop is the one the walks call:
# `twoPhantomTest` / `twoPhantomLoop` (LoopF.lean, ReduceS.lean) with `runPhase` (PhaseS.lean, connection set
# `connectedPairs` built once per step) and `reducePieces`; the class search potential `classPotential` is the
# array relaxation `relaxA` with `kFuel = |boxSquares V| + 1` rounds (HoleRelax.lean).
# The Lean functions return `Bool` / `Option`; here a "true" result carries a witness:
#   * `twoPhantomLoop` returns the final one-piece factor (a frozenset of edges) or None,
#   * the decision functions (`twoPhantomTest`, `boundaryEndpointsWalk`, `boundaryEndpoints`, `oneHoleFinalTest`, `holeCaseWalk`, `holeCase`, ...)
#     return a Hamiltonian path (list of points) or None.
# A witness is returned exactly when the Lean function returns `true`; `None` exactly when it
# returns `false`.
#
# Representations:
#   Pt    = (x, y) tuple of ints,
#   Edge  = (d, x, y) with d = 0 for `.h` (to (x+1, y)) and d = 1 for `.v` (to (x, y+1)),
#   Finset Pt / Finset Edge / Finset (Pt x Pt) = Python frozenset,
#   Array Z = Python list,
#   Side  = one of 'b', 't', 'l', 'r'.
#
# Deviations from Lean that are value-identical (pure functions evaluated in fewer steps):
#   * `creach` stops once a round adds nothing (later rounds return the same set),
#   * `layerAcc` likewise stops once a layer equals the previous one and pads with copies,
#   * the box functions `bx0`, `bx1`, `by0`, `by1` and `boxSquares` are memoized per point set.
#
import functools
import sys
from collections import namedtuple

sys.setrecursionlimit(100000)

# Statistics of the last run (reset by `decideHamPath`).
#
STATS = {}


def _stat(k, n=1):
  STATS[k] = STATS.get(k, 0) + n


# ---------------------------------------------------------------------------------------------
# Grid.lean
# ---------------------------------------------------------------------------------------------

DH, DV = 0, 1


def edge_p(e):
  return (e[1], e[2])


# Grid.lean `Edge.q`: the far endpoint.
#
def edge_q(e):
  return ((e[1] + 1, e[2]) if (e[0] == DH) else (e[1], e[2] + 1))


# Grid.lean `Edge.lo`: the cell below an h edge, left of a v edge.
#
def edge_lo(e):
  return ((e[1], e[2] - 1) if (e[0] == DH) else (e[1] - 1, e[2]))


# Grid.lean `Edge.hi`.
#
def edge_hi(e):
  return (e[1], e[2])


def bot(c): return (DH, c[0], c[1])
def top(c): return (DH, c[0], c[1] + 1)
def lft(c): return (DV, c[0], c[1])
def rgt(c): return (DV, c[0] + 1, c[1])


def eR(p): return (DH, p[0], p[1])
def eL(p): return (DH, p[0] - 1, p[1])
def eU(p): return (DV, p[0], p[1])
def eD(p): return (DV, p[0], p[1] - 1)


# Grid.lean `deg`.
#
def deg(F, p):
  return ( (eR(p) in F) + (eL(p) in F) + (eU(p) in F) + (eD(p) in F) )


# Grid.lean `IsEdge`.
#
def IsEdge(V, e):
  return ( (edge_p(e) in V) and (edge_q(e) in V) )


# Grid.lean `IsCell`: cell named by its lower-left corner.
#
def IsCell(V, c):
  x, y = c
  return ( ((x, y) in V) and ((x + 1, y) in V) and ((x, y + 1) in V) and ((x + 1, y + 1) in V) )


# Grid.lean `Solid`: every missing point reaches, by king moves through missing points, a point
# left of all of V. Equivalent check: flood the complement inside the box with margin 1 from the
# margin; every missing box point must be reached.
#
def Solid(V):
  if not V:
    return True
  xs = [p[0] for p in V]
  ys = [p[1] for p in V]
  x0, x1, y0, y1 = min(xs) - 1, max(xs) + 1, min(ys) - 1, max(ys) + 1
  seen = set()
  st = [(x0, y) for y in range(y0, y1 + 1)]
  while st:
    p = st.pop()
    if ( (p in seen) or (p in V) or
         (not ( (x0 <= p[0] <= x1) and (y0 <= p[1] <= y1) )) ):
      continue
    seen.add(p)
    for a in (-1, 0, 1):
      for b in (-1, 0, 1):
        st.append((p[0] + a, p[1] + b))
  for x in range(x0, x1 + 1):
    for y in range(y0, y1 + 1):
      if ( ((x, y) not in V) and ((x, y) not in seen) ):
        return False
  return True


# ---------------------------------------------------------------------------------------------
# Arcs.lean
# ---------------------------------------------------------------------------------------------

# Arcs.lean `par`: true for odd x + y.
#
def par(c):
  return ( ((c[0] + c[1]) % 2) == 1 )


# Arcs.lean `inE1`.
#
def inE1(F, e):
  return ( (e in F) if (e[0] == DH) else (e not in F) )


# Arcs.lean `up`.
#
def up(F, e):
  return ( par(edge_lo(e)) == inE1(F, e) )


# Arcs.lean `sideEdge`.
#
def sideEdge(c, s):
  if   s == 'b': return bot(c)
  elif s == 't': return top(c)
  elif s == 'l': return lft(c)
  else:          return rgt(c)


# Arcs.lean `nb`: the neighbouring cell across a side.
#
def nb(c, s):
  if   s == 'b': return (c[0], c[1] - 1)
  elif s == 't': return (c[0], c[1] + 1)
  elif s == 'l': return (c[0] - 1, c[1])
  else:          return (c[0] + 1, c[1])


_OPP = {'b': 't', 't': 'b', 'l': 'r', 'r': 'l'}


# Arcs.lean `Side.opp`.
#
def opp(s):
  return _OPP[s]


# Arcs.lean `outArc`.
#
def outArc(F, c, s):
  if   s == 'b': return (not up(F, bot(c)))
  elif s == 't': return up(F, top(c))
  elif s == 'l': return (not up(F, lft(c)))
  else:          return up(F, rgt(c))


# Arcs.lean `Alt`.
#
def Alt(F, c):
  b, t, l, r = (bot(c) in F), (top(c) in F), (lft(c) in F), (rgt(c) in F)
  return ( (b and t and (not l) and (not r)) or
           ((not b) and (not t) and l and r) )


# ---------------------------------------------------------------------------------------------
# Strip.lean
# ---------------------------------------------------------------------------------------------

def front(c, s): return sideEdge(c, s)
def back(c, s):  return sideEdge(c, opp(s))


def back1(c, s):
  x, y = c
  if   s == 't': return (x, y)
  elif s == 'b': return (x, y + 1)
  elif s == 'r': return (x, y)
  else:          return (x + 1, y)


def back2(c, s):
  x, y = c
  if   s == 't': return (x + 1, y)
  elif s == 'b': return (x + 1, y + 1)
  elif s == 'r': return (x, y + 1)
  else:          return (x + 1, y + 1)


def front1(c, s):
  x, y = c
  if   s == 't': return (x, y + 1)
  elif s == 'b': return (x, y)
  elif s == 'r': return (x + 1, y)
  else:          return (x, y)


def front2(c, s):
  x, y = c
  if   s == 't': return (x + 1, y + 1)
  elif s == 'b': return (x + 1, y)
  elif s == 'r': return (x + 1, y + 1)
  else:          return (x, y + 1)


# Strip.lean `cellJ`: the j-th cell of the strip from c in direction s.
#
def cellJ(c, s, j):
  x, y = c
  if   s == 't': return (x, y + j)
  elif s == 'b': return (x, y - j)
  elif s == 'r': return (x + j, y)
  else:          return (x - j, y)


# ---------------------------------------------------------------------------------------------
# D.lean, StripCount.lean
# ---------------------------------------------------------------------------------------------

# D.lean `cellE`.
#
def cellE(c):
  return frozenset((bot(c), top(c), lft(c), rgt(c)))


# D.lean `flip`: toggle the four sides of a cell.
#
def flip(F, c):
  return F ^ cellE(c)


# StripCount.lean `flipCol`: flipCol F c s (n+1) = flipCol (flip F (cellJ c s n)) c s n.
#
def flipCol(F, c, s, n):
  while n > 0:
    F = flip(F, cellJ(c, s, n - 1))
    n -= 1
  return F


# ---------------------------------------------------------------------------------------------
# Algorithm.lean
# ---------------------------------------------------------------------------------------------

# Algorithm.lean `cellList`: the cells of V in lexicographic order (as in Lean).
#
def cellList(V):
  return sorted(c for c in V if IsCell(V, c))


# Algorithm.lean `sidesL`.
#
sidesL = ('b', 't', 'l', 'r')


# ---------------------------------------------------------------------------------------------
# Graph.lean, Comp.lean, Enum.lean
# ---------------------------------------------------------------------------------------------

# Graph.lean `other`.
#
def other(e, y):
  return ( edge_q(e) if (edge_p(e) == y) else edge_p(e) )


# DFactor.lean / TwoFactor.lean `inc4` (searched in this order).
#
def inc4(z):
  return (eR(z), eL(z), eU(z), eD(z))


# Comp.lean `fnbr`.
#
def fnbr(F, u):
  return {other(e, u) for e in inc4(u) if e in F}


# Comp.lean `creach`: points reachable from x in at most k steps. Stops early once a round adds
# nothing (value-identical).
#
def creach(F, x, k):
  C = {x}
  frontier = {x}
  for _ in range(k):
    new = set()
    for u in frontier:
      for v in fnbr(F, u):
        if v not in C:
          new.add(v)
    if not new:
      break
    C |= new
    frontier = new
  return frozenset(C)


# Comp.lean `ccls`.
#
def ccls(V, F, x):
  return creach(F, x, len(V))


# Comp.lean `cncomp`.
#
def cncomp(V, F):
  return len({ccls(V, F, x) for x in V})


# Enum.lean `connB`.
#
def connB(V, F, x, y):
  return ( y in ccls(V, F, x) )


# ---------------------------------------------------------------------------------------------
# DFactor.lean (namespace DF), StartPF.lean `dST`
# ---------------------------------------------------------------------------------------------

# StartPF.lean `dST`.
#
def dST(s, t):
  return (lambda z: (1 if ( (z == s) or (z == t) ) else 2))


def Black(z):
  return ( ((z[0] + z[1]) % 2) == 0 )


# DFactor.lean `Fwd`.
#
def Fwd(V, F, u, e):
  return ( IsEdge(V, e) and ( (e not in F) if Black(u) else (e in F) ) )


# DFactor.lean `nbr`.
#
def nbr(V, F, u):
  return {other(e, u) for e in inc4(u) if Fwd(V, F, u, e)}


# DFactor.lean `layerAcc`: [layer k, ..., layer 0]. Stops once a layer equals the previous one
# and pads with copies (value-identical: equal layers stay equal).
#
def layerAcc(V, d, F, k):
  L = frozenset(z for z in V if ( Black(z) and (deg(F, z) < d(z)) ))
  out = [L]
  i = 0
  while i < k:
    L2 = frozenset(L | {w for u in L for w in nbr(V, F, u)})
    if L2 == L:
      out.extend([L] * (k - i))
      break
    out.append(L2)
    L = L2
    i += 1
  out.reverse()
  return out


# DFactor.lean `Bwd`.
#
def Bwd(V, F, L, v, e):
  return ( IsEdge(V, e) and (other(e, v) in L) and
           ( (e in F) if Black(v) else (e not in F) ) )


# DFactor.lean `pred`.
#
def pred(V, F, L, v):
  for e in inc4(v):
    if Bwd(V, F, L, v, e):
      return e
  return None


# DFactor.lean `walk`: one list entry consumed per step.
#
def walk(V, F0, Ls, v, F):
  for L in Ls:
    if v in L:
      continue
    e = pred(V, F0, L, v)
    if e is None:
      return F
    F = ( (F - {e}) if Black(v) else (F | {e}) )
    v = other(e, v)
  return F


# DFactor.lean `pick`: the lexicographic least point.
#
def pick(S):
  return ( min(S) if S else None )


# DFactor.lean `augStep`.
#
def augStep(V, d, F):
  Ls = layerAcc(V, d, F, len(V))
  if not Ls:
    return None
  L, rest = Ls[0], Ls[1:]
  w = pick([w for w in L if ( (not Black(w)) and (deg(F, w) < d(w)) )])
  if w is None:
    return None
  return walk(V, F, rest, w, F)


# DFactor.lean `augLoop`.
#
def augLoop(V, d, n, F):
  while n > 0:
    F2 = augStep(V, d, F)
    if F2 is None:
      return F
    F = F2
    n -= 1
  return F


# DFactor.lean `findFactor`.
#
def findFactor(V, d):
  _stat('findFactor')
  F = augLoop(V, d, len(V) + 1, frozenset())
  if all(deg(F, z) == d(z) for z in V):
    return frozenset(F)
  return None


# ---------------------------------------------------------------------------------------------
# Bridges.lean, Undo.lean, Compat0.lean, UndoCount.lean, Node.lean
# ---------------------------------------------------------------------------------------------

Bridge = namedtuple('Bridge', 'q a r')
Join = namedtuple('Join', 'c a n')


# Bridges.lean `Bridge.cell`, `Bridge.E`.
#
def bcell(b, j):
  return cellJ(b.q, b.a, j)


def bE(b):
  return bcell(b, b.r - 1)


# Compat0.lean `lowJ`, `undoJ`.
#
def lowJ(b):
  return Join(b.q, b.a, b.r - 1)


def undoJ(b):
  return Join(bE(b), b.a, 1)


# Undo.lean `Join.apply`.
#
def joinApply(G, o):
  return flipCol(G, o.c, o.a, o.n)


# UndoCount.lean `applyAll`.
#
def applyAll(G, os):
  for o in os:
    G = joinApply(G, o)
  return G


# Node.lean `rowStartPair`.
#
def rowStartPair(b):
  return (back1(b.q, b.a), front1(b.q, b.a))


# Reduce.lean `altFrame`.
#
def altFrame(G, X):
  return ( 't' if (bot(X) in G) else 'r' )


# S4TheoremR.lean `mergePair`.
#
def mergePair(H, X):
  a = altFrame(H, X)
  return (back1(X, a), front1(X, a))


# ---------------------------------------------------------------------------------------------
# SAlg.lean, SPhaseAlg.lean (the parts the fast loop still calls)
# ---------------------------------------------------------------------------------------------

# SAlg.lean `cutB`.
#
def cutB(W, H, c):
  return not ( connB(W, H, c, (c[0] + 1, c[1])) and
               connB(W, H, c, (c[0] + 1, c[1] + 1)) and
               connB(W, H, c, (c[0], c[1] + 1)) )


# SAlg.lean `pairSqB`.
#
def pairSqB(BS, c):
  return any( ( (c == bcell(b, b.r - 2)) or (c == bE(b)) ) for b in BS )


# SPhaseAlg.lean `flipSplits`.
#
def flipSplits(W, H, b):
  return not connB(W, flip(H, bE(b)), back1(bE(b), b.a), front1(bE(b), b.a))


# ---------------------------------------------------------------------------------------------
# ConnSet.lean
# ---------------------------------------------------------------------------------------------

# ConnSet.lean `compsAux`: one sweep over `xs`, a class for each point not yet covered.
#
def compsAux(W, H, xs, cov):
  out = []
  for x in xs:
    if x in cov:
      continue
    C = ccls(W, H, x)
    out.append(C)
    cov = cov | C
  return out


# ConnSet.lean `ptList`: the points of W in lexicographic order.
#
def ptList(W):
  return sorted(W)


# ConnSet.lean `comps`.
#
def comps(W, H):
  return compsAux(W, H, ptList(W), frozenset())


# ConnSet.lean `connectedPairs`: the connected pairs, the union of C x C over the components.
#
def connectedPairs(W, H):
  return frozenset( (x, y) for C in comps(W, H) for x in C for y in C )


# ConnSet.lean `isConnected`.
#
def isConnected(S, x, y):
  return ( (x, y) in S )


# ---------------------------------------------------------------------------------------------
# PhaseS.lean
# ---------------------------------------------------------------------------------------------

# PhaseS.lean `isCutCell`.
#
def isCutCell(S, c):
  return not ( isConnected(S, c, (c[0] + 1, c[1])) and
               isConnected(S, c, (c[0] + 1, c[1] + 1)) and
               isConnected(S, c, (c[0], c[1] + 1)) )


# PhaseS.lean `findMergingCell`: `List.find?` over `cellList V`.
#
def findMergingCell(V, S, H, BS):
  for c in cellList(V):
    if ( Alt(H, c) and isCutCell(S, c) and (not pairSqB(BS, c)) ):
      return c
  return None


# PhaseS.lean `isCritical`: critical in frame a with the back dark.
#
def isCritical(S, H, q, a):
  return ( isConnected(S, back1(q, a), back2(q, a)) and
           isConnected(S, front1(q, a), front2(q, a)) and
           (not isConnected(S, back1(q, a), front1(q, a))) and
           (back(q, a) in H) and
           (front(q, a) not in H) )


# PhaseS.lean `scanRowAux`: returns ('row', j), ('stuck', j) or None.
#
def scanRowAux(V, S, H, q, a, o, fuel, j):
  while fuel > 0:
    if outArc(H, cellJ(q, a, j - 1), a) != o:
      return ('row', j)
    c = cellJ(q, a, j)
    if ( (not IsCell(V, c)) or isCutCell(S, c) ):
      return ('stuck', j)
    fuel -= 1
    j += 1
  return None


# PhaseS.lean `scanRow`.
#
def scanRow(V, S, H, q, a):
  return scanRowAux(V, S, H, q, a, outArc(H, q, a), len(V) + 1, 1)


# PhaseS.lean `bridgeSquares`: the squares of the bridges, as one set.
#
def bridgeSquares(BS):
  return frozenset( bcell(b, j) for b in BS for j in range(b.r) )


# PhaseS.lean `rowOf`.
#
def rowOf(V, S, H, B, x):
  q, a = x
  if ( isCritical(S, H, q, a) and (q not in B) ):
    e = scanRow(V, S, H, q, a)
    if ( (e is not None) and (e[0] == 'row') ):
      return Bridge(q, a, e[1])
    return None
  return None


# PhaseS.lean `findRow`: `List.findSome?` over the cells in `cellList` order, sides in `sidesL`
# order.
#
def findRow(V, S, H, BS):
  B = bridgeSquares(BS)
  for q in cellList(V):
    for a in sidesL:
      b = rowOf(V, S, H, B, (q, a))
      if b is not None:
        return b
  return None


# PhaseS.lean `runPhase`: returns (H, BS, out) with out one of ('stuck',), ('merge', c),
# ('odd', b), ('twist', b), ('fuel',). BS is a tuple, most recent bridge first (Lean `b :: BS`).
# The connection set `S` is built once per step.
#
def runPhase(V, W, n, H, BS):
  _stat('phases')
  while True:
    if n == 0:
      return (H, BS, ('fuel',))
    S = connectedPairs(W, H)
    c = findMergingCell(V, S, H, BS)
    if c is not None:
      return (H, BS, ('merge', c))
    b = findRow(V, S, H, BS)
    if b is None:
      return (H, BS, ('stuck',))
    if (b.r % 2) == 1:
      return (H, BS, ('odd', b))
    elif flipSplits(W, H, b):
      _stat('bridges')
      n, H, BS = n - 1, flip(H, bE(b)), (b,) + BS
    else:
      return (H, BS, ('twist', b))


# ---------------------------------------------------------------------------------------------
# ReduceS.lean
# ---------------------------------------------------------------------------------------------

# ReduceS.lean `bridgeStatesConn`: the connection sets of the states reached by flipping the bridge
# ends, in the order of BS.
#
def bridgeStatesConn(W, H, BS):
  out = []
  for b in BS:
    H = flip(H, bE(b))
    out.append(connectedPairs(W, H))
  return out


# ReduceS.lean `undoPlanSteps` (stops at the end of the shorter list).
#
def undoPlanSteps(Ss, BS, uv):
  out = []
  for S, b in zip(Ss, BS):
    if isConnected(S, uv[0], uv[1]):
      out.append((True, uv))
      uv = rowStartPair(b)
    else:
      out.append((False, uv))
  return out


# ReduceS.lean `undoPlan`.
#
def undoPlan(Ss, BS, uv):
  return [ (lowJ(b) if e[0] else undoJ(b)) for b, e in zip(BS, undoPlanSteps(Ss, BS, uv)) ]


# ReduceS.lean `isGoodMergingCell`.
#
def isGoodMergingCell(W, H, BS, Ss, X):
  if not ( Alt(H, X) and cutB(W, H, X) and (not pairSqB(BS, X)) ):
    return False
  uv = mergePair(H, X)
  P = undoPlanSteps(Ss, BS, uv)
  for i in range(len(BS)):
    b = BS[i]
    Pi = ( P[i] if (i < len(P)) else (False, uv) )
    if not ( Pi[0] or (X != nb(bE(b), b.a)) ):
      return False
  return True


# ReduceS.lean `reducePieces`.
#
def reducePieces(V, W, H, BS, out):
  _stat('reductions')
  kind = out[0]
  if kind == 'merge':
    c = out[1]
    Ss = bridgeStatesConn(W, H, BS)
    X = c
    for Y in cellList(V):
      if isGoodMergingCell(W, H, BS, Ss, Y):
        X = Y
        break
    return applyAll(flipCol(H, X, altFrame(H, X), 1), undoPlan(Ss, BS, mergePair(H, X)))
  elif kind in ('odd', 'twist'):
    b = out[1]
    return applyAll(flipCol(H, b.q, b.a, b.r), undoPlan(bridgeStatesConn(W, H, BS), BS, rowStartPair(b)))
  return H


# ReduceS.lean `twoPhantomLoop` (two phantoms p, q). Returns the final one-piece factor or None.
#
def twoPhantomLoop(V, p, q, n, G):
  _stat('twoPhantomLoop')
  W = V | {p, q}
  while True:
    if n == 0:
      return ( G if (cncomp(W, G) == 1) else None )
    if cncomp(W, G) == 1:
      return G
    H, BS, out = runPhase(V, W, len(W) + 1, G, ())
    if out[0] in ('stuck', 'fuel'):
      _stat('runs_stuck')
      return None
    G = reducePieces(V, W, H, BS, out)
    n -= 1


# ---------------------------------------------------------------------------------------------
# LoopF.lean
# ---------------------------------------------------------------------------------------------

# LoopF.lean `twoPhantomTest`. Returns a path s..t in V or None.
#
def twoPhantomTest(V, s, t, p, q, e0, e1):
  _stat('leaf')
  R = findFactor(V, dST(s, t))
  if R is None:
    return None
  G = twoPhantomLoop(V, p, q, len(V) + 2, R | {e0, e1})
  if G is None:
    return None
  return factor_path(G - {e0, e1}, s, t)


# ---------------------------------------------------------------------------------------------
# Witness extraction: the path s..t of a one-piece path factor (phantom edges removed).
# ---------------------------------------------------------------------------------------------

def factor_path(F, s, t):
  adj = {}
  for e in F:
    a, b = edge_p(e), edge_q(e)
    adj.setdefault(a, []).append(b)
    adj.setdefault(b, []).append(a)
  path = [s]
  prev, cur = None, s
  while cur != t:
    nxt = [v for v in adj.get(cur, []) if v != prev]
    if len(nxt) != 1:
      raise RuntimeError("factor_path: not a path at %r" % (cur,))
    prev, cur = cur, nxt[0]
    path.append(cur)
    if len(path) > (len(F) + 1):
      raise RuntimeError("factor_path: cycle")
  return path


# ---------------------------------------------------------------------------------------------
# SheffBoundary.lean, TwoPhWalk.lean
# ---------------------------------------------------------------------------------------------

# SheffBoundary.lean `nbrsL`: (neighbour, edge) in the order right, left, up, down.
#
def nbrsL(t):
  return ( ((t[0] + 1, t[1]), eR(t)), ((t[0] - 1, t[1]), eL(t)),
           ((t[0], t[1] + 1), eU(t)), ((t[0], t[1] - 1), eD(t)) )


# TwoPhWalk.lean `isFar`: equal, or king distance >= 2 (StuckL4.lean `Far`, `Close1`).
#
def isFar(t, s):
  return ( (t == s) or
           (not ( (abs(t[0] - s[0]) <= 1) and (abs(t[1] - s[1]) <= 1) )) )


# TwoPhWalk.lean `phantomsOpposed` (StuckL4.lean `Opp`): the out-vertices a, b differ by exactly 2 along
# one axis (at most 2 along the other) and their phantoms ma, mb point away from each other
# along that axis.
#
def phantomsOpposed(a, ma, b, mb):
  dx, dy = (b[0] - a[0]), (b[1] - a[1])
  return ( ( (dx == 2) and (abs(dy) <= 2) and (ma == (a[0] - 1, a[1])) and
             (mb == (b[0] + 1, b[1])) ) or
           ( (dx == -2) and (abs(dy) <= 2) and (ma == (a[0] + 1, a[1])) and
             (mb == (b[0] - 1, b[1])) ) or
           ( (dy == 2) and (abs(dx) <= 2) and (ma == (a[0], a[1] - 1)) and
             (mb == (b[0], b[1] + 1)) ) or
           ( (dy == -2) and (abs(dx) <= 2) and (ma == (a[0], a[1] + 1)) and
             (mb == (b[0], b[1] - 1)) ) )


# TwoPhWalk.lean `isUsablePhantom`: a missing lattice neighbour of t, not q, not opposed to s's phantom.
#
def isUsablePhantom(V, s, q, t, x):
  return ( (x[0] not in V) and (x[0] != q) and (not phantomsOpposed(t, x[0], s, q)) )


# The `hp_two` test (V = {s, t}): the path [s, t] if adjacent.
#
def _two(t, s):
  for x in nbrsL(t):
    if x[0] == s:
      return [s, t]
  return None


# TwoPhWalk.lean `boundaryEndpointsWalk`: s keeps its phantom q (edge e1); t moves. Returns a path s..t in V.
#
def boundaryEndpointsWalk(s, q, e1, n, V, t):
  _stat('walk_nodes')
  if n == 0:
    return None
  if len(V) <= 2:
    return _two(t, s)
  x = None
  for y in nbrsL(t):
    if isUsablePhantom(V, s, q, t, y):
      x = y
      break
  if ( (x is not None) and isFar(t, s) ):
    return twoPhantomTest(V, s, t, x[0], q, x[1], e1)
  for y in nbrsL(t):
    if ( (y[0] in V) and (y[0] != s) ):
      P = boundaryEndpointsWalk(s, q, e1, n - 1, V - {t}, y[0])
      if P is not None:
        return P + [t]
  return None


# TwoPhWalk.lean `boundaryEndpoints`: two endpoints with a missing king neighbour each.
#
def boundaryEndpoints(V, s, t):
  if len(V) <= 2:
    return _two(t, s)
  x = None
  for y in nbrsL(s):
    if y[0] not in V:
      x = y
      break
  if x is not None:
    return boundaryEndpointsWalk(s, x[0], x[1], 12, V, t)
  for y in nbrsL(s):
    if ( (y[0] in V) and (y[0] != t) ):
      P = boundaryEndpointsWalk(y[0], s, y[1], 12, V - {s}, t)
      if P is not None:
        return [s] + P
  return None


# ---------------------------------------------------------------------------------------------
# HoleAdm.lean, HoleRelax.lean, HoleTry.lean, HoleOne.lean
# ---------------------------------------------------------------------------------------------

# HoleAdm.lean `sv`.
#
def sv(F, e):
  return ( 1 if up(F, e) else -1 )


# HoleRelax.lean `bx0`, `bx1`, `by0`, `by1` (memoized: V is a frozenset).
#
@functools.lru_cache(maxsize=256)
def bx0(V): return ( min(p[0] for p in V) if V else 0 )


@functools.lru_cache(maxsize=256)
def bx1(V): return ( max(p[0] for p in V) if V else 0 )


@functools.lru_cache(maxsize=256)
def by0(V): return ( min(p[1] for p in V) if V else 0 )


@functools.lru_cache(maxsize=256)
def by1(V): return ( max(p[1] for p in V) if V else 0 )


# HoleRelax.lean `boxWidth`.
#
def boxWidth(V):
  return bx1(V) - bx0(V)


# HoleRelax.lean `boxSquares`: cells strictly inside the box, x-major order as in Lean (memoized,
# returned as a tuple).
#
@functools.lru_cache(maxsize=256)
def boxSquares(V):
  x0, y0 = bx0(V), by0(V)
  return tuple( (x0 + i, y0 + j)
                for i in range(max(0, bx1(V) - x0))
                for j in range(max(0, by1(V) - y0)) )


# HoleRelax.lean `ivl`.
#
def ivl(V, F, e):
  if IsEdge(V, e):
    v = sv(F, e)
    return (min(0, v), max(0, v))
  return (0, 0)


# HoleRelax.lean `lowerBound` (f : Pt -> Z).
#
def lowerBound(V, F, f, s):
  return max( max( f(edge_lo(bot(s))) + ivl(V, F, bot(s))[0],
                   f(edge_lo(lft(s))) + ivl(V, F, lft(s))[0] ),
              max( f(edge_hi(top(s))) - ivl(V, F, top(s))[1],
                   f(edge_hi(rgt(s))) - ivl(V, F, rgt(s))[1] ) )


# HoleRelax.lean `sideOK`.
#
def sideOK(V, F, f, e):
  dlt = f(edge_hi(e)) - f(edge_lo(e))
  return ( (dlt == 0) or (IsEdge(V, e) and (dlt == sv(F, e))) )


# HoleRelax.lean `sides`.
#
def sides(s):
  return (bot(s), lft(s), top(s), rgt(s))


# HoleRelax.lean `isAdmissible`.
#
def isAdmissible(V, F, as_, hs, f):
  return ( all( all(sideOK(V, F, f, e) for e in sides(s)) for s in boxSquares(V) ) and
           all( (f(a) == h) for a, h in zip(as_, hs) ) )


# HoleRelax.lean `jumpEdges`: the jump set of f, as edges of V.
#
def jumpEdges(V, f):
  return frozenset( e for s in boxSquares(V) for e in sides(s)
                    if ( IsEdge(V, e) and (f(edge_hi(e)) != f(edge_lo(e))) ) )


# HoleRelax.lean `kFuel`: the Bellman-Ford round bound |boxSquares V| + 1.
#
def kFuel(V):
  return len(boxSquares(V)) + 1


# The box of V as one tuple (x0, x1, y0, y1, kWn, kHn), memoized; the functions below read
# it instead of recomputing `bx0` ... (value-identical).
#
@functools.lru_cache(maxsize=256)
def _box(V):
  x0, x1, y0, y1 = bx0(V), bx1(V), by0(V), by1(V)
  return (x0, x1, y0, y1, max(0, x1 - x0), max(0, y1 - y0))


# HoleRelax.lean `kWn`, `kHn`: the box sides as naturals.
#
def kWn(V):
  return _box(V)[4]


def kHn(V):
  return _box(V)[5]


# HoleRelax.lean `inBox`: c is a cell of `boxSquares V`.
#
def inBox(V, c):
  x0, x1, y0, y1, _, _ = _box(V)
  return ( (x0 <= c[0]) and (c[0] < x1) and (y0 <= c[1]) and (c[1] < y1) )


# HoleRelax.lean `idx`: the array index of a box cell (x-major, as `boxSquares`).
#
def idx(V, c):
  x0, _, y0, _, _, h = _box(V)
  return ( (max(0, c[0] - x0) * h) + max(0, c[1] - y0) )


# HoleRelax.lean `cellOf`: the box cell of an array index (Lean's k / 0 = 0, k % 0 = k).
#
def cellOf(V, k):
  x0, _, y0, _, _, h = _box(V)
  return ( (x0 + (k // h), y0 + (k % h)) if (h > 0) else (x0, y0 + k) )


# HoleRelax.lean `toFA`: the potential stored in A; 0 outside the box. `inBox` and `idx`
# inlined (inside the box both differences are >= 0, so `toNat` is the identity).
#
def toFA(V, A, c):
  x0, x1, y0, y1, _, h = _box(V)
  if ( (x0 <= c[0]) and (c[0] < x1) and (y0 <= c[1]) and (c[1] < y1) ):
    k = ((c[0] - x0) * h) + (c[1] - y0)
    return ( A[k] if (k < len(A)) else 0 )
  return 0


# HoleRelax.lean `roundA`: one simultaneous round, read from the old array.
#
def roundA(V, F, A):
  f = (lambda c: toFA(V, A, c))
  out = []
  for k in range(kWn(V) * kHn(V)):
    c = cellOf(V, k)
    out.append(max(f(c), lowerBound(V, F, f, c)))
  return out


# HoleRelax.lean `relaxA`: stops (returning the old array) once a round changes no cell of `boxSquares`.
#
def relaxA(V, F, n, A):
  while n > 0:
    A2 = roundA(V, F, A)
    if all( (toFA(V, A2, c) == toFA(V, A, c)) for c in boxSquares(V) ):
      return A
    A = A2
    n -= 1
  return A


# HoleRelax.lean `kInitA`: prescribed cells start at their values (first match of `as.zip hs`),
# other box cells at -boxWidth.
#
def kInitA(V, as_, hs):
  def look(c):
    for a, h in zip(as_, hs):
      if a == c:
        return h
    return -boxWidth(V)
  return [ look(cellOf(V, k)) for k in range(kWn(V) * kHn(V)) ]


# HoleRelax.lean `classPotential`: a function Pt -> Z (`toFA` of the relaxed array).
#
def classPotential(V, F, as_, hs):
  A = relaxA(V, F, kFuel(V), kInitA(V, as_, hs))
  return (lambda c: toFA(V, A, c))


# HoleTry.lean `classSearch`.
#
def classSearch(V, F, as_, hs):
  _stat('classSearch')
  f = classPotential(V, F, as_, hs)
  if isAdmissible(V, F, as_, hs, f):
    _stat('classSearch_some')
    return F ^ jumpEdges(V, f)
  return None


# HoleTry.lean `classSearchOne`.
#
def classSearchOne(V, F, t, h):
  return classSearch(V, F, [t], [h])


# HoleTry.lean `classRange`: -|V| .. |V|.
#
def classRange(V):
  n = len(V)
  return [ i - n for i in range(2 * n + 1) ]


# HoleOne.lean `isNarrow`.
#
def isNarrow(U):
  return ( ((bx1(U) - bx0(U)) < len(U)) and ((by1(U) - by0(U)) < len(U)) )


# ---------------------------------------------------------------------------------------------
# HoleWalk.lean, HoleTwoV.lean
# ---------------------------------------------------------------------------------------------

# HoleWalk.lean `holeCaseWalk`: w fixed (its phantom pw), s moves; `fin(U, s, q, e1)` is the final
# test. Returns a path s..w in U or None.
#
def holeCaseWalk(fin, w, pw, n, U, s, q, e1):
  _stat('walk_nodes')
  if n == 0:
    return None
  if len(U) <= 2:
    for x in nbrsL(w):
      if x[0] == s:
        return [s, w]
    return None
  if ( isFar(w, s) and (not phantomsOpposed(w, pw, s, q)) ):
    return fin(U, s, q, e1)
  for x in nbrsL(s):
    if ( (x[0] in U) and (x[0] != w) ):
      P = holeCaseWalk(fin, w, pw, n - 1, U - {s}, x[0], s, x[1])
      if P is not None:
        return [s] + P
  return None


# HoleWalk.lean `holeCase`: delete t (branch over w), delete s (branch over its successor), walk.
# `fin(w, e0, U, s, q, e1)`. Returns a path s..t in V or None.
#
def holeCase(fin, V, s, t):
  if len(V) <= 2:
    return _two(t, s)
  Vt = V - {t}
  for y in nbrsL(t):
    if ( (y[0] in V) and (y[0] != s) ):
      if len(Vt) <= 2:
        P = None
        for x in nbrsL(y[0]):
          if x[0] == s:
            P = [s, y[0]]
            break
      else:
        P = None
        for x in nbrsL(s):
          if ( (x[0] in Vt) and (x[0] != y[0]) ):
            w, e0 = y[0], y[1]
            fw = (lambda U, s2, q, e1, w=w, e0=e0: fin(w, e0, U, s2, q, e1))
            P2 = holeCaseWalk(fw, w, t, 10, Vt - {s}, x[0], s, x[1])
            if P2 is not None:
              P = [s] + P2
              break
      if P is not None:
        return P + [t]
  return None


# HoleWalk.lean `oneHoleFinalTest`: per class the factor `classSearchOne` returns, then the two-phantom loop
# `twoPhantomLoop`.
# Returns a path s..w in U or None.
#
def oneHoleFinalTest(U, s, w, t, q, e0, e1):
  _stat('leaf')
  if not isNarrow(U):
    return None
  R = findFactor(U, dST(s, w))
  if R is None:
    return None
  F = R | {e0, e1}
  for h in classRange(U):
    G = classSearchOne(U, F, t, h)
    if G is not None:
      G2 = twoPhantomLoop(U, t, q, len(U) + 2, G)
      if G2 is not None:
        return factor_path(G2 - {e0, e1}, s, w)
  return None


# HoleWalk.lean `oneHoleCase`: t inner, s with a missing king neighbour.
#
def oneHoleCase(V, s, t):
  return holeCase((lambda w, e0, U, s2, q, e1: oneHoleFinalTest(U, s2, w, t, q, e0, e1)), V, s, t)


# HoleTwoV.lean `twoHoleFinalTest`: class pairs at the holes t and r.
#
def twoHoleFinalTest(U, s, w, t, r, q, e0, e1):
  _stat('leaf')
  if not isNarrow(U):
    return None
  R = findFactor(U, dST(s, w))
  if R is None:
    return None
  F = R | {e0, e1}
  for h1 in classRange(U):
    for h2 in classRange(U):
      G = classSearch(U, F, [t, r], [h1, h2])
      if G is not None:
        G2 = twoPhantomLoop(U, t, q, len(U) + 2, G)
        if G2 is not None:
          return factor_path(G2 - {e0, e1}, s, w)
  return None


# HoleTwoV.lean `twoHoleCase`: both endpoints inner.
#
def twoHoleCase(V, s, t):
  return holeCase((lambda w, e0, U, s2, q, e1: twoHoleFinalTest(U, s2, w, t, s, q, e0, e1)), V, s, t)


# ---------------------------------------------------------------------------------------------
# HPFinal.lean
# ---------------------------------------------------------------------------------------------

# HPFinal.lean `isInner`: the four cells around p are present.
#
def isInner(V, p):
  x, y = p
  return ( IsCell(V, (x - 1, y - 1)) and IsCell(V, (x, y - 1)) and
           IsCell(V, (x - 1, y)) and IsCell(V, p) )


# HPFinal.lean `decideHamPath` branch name (for statistics).
#
def decideHamPath_branch(V, s, t):
  if isInner(V, s):
    return ( 'twoHoleCase' if isInner(V, t) else 'oneHoleCase-swap' )
  return ( 'oneHoleCase' if isInner(V, t) else 'boundaryEndpoints' )


# HPFinal.lean `decideHamPath`. Returns a Hamiltonian path s..t (list of points) or None.
#
def decideHamPath(V, s, t):
  V = frozenset(V)
  STATS.clear()
  if isInner(V, s):
    if isInner(V, t):
      return twoHoleCase(V, s, t)
    P = oneHoleCase(V, t, s)
    return ( None if (P is None) else P[::-1] )
  if isInner(V, t):
    return oneHoleCase(V, s, t)
  return boundaryEndpoints(V, s, t)


# ---------------------------------------------------------------------------------------------
# Independent witness check.
# ---------------------------------------------------------------------------------------------

def verify_path(V, s, t, P):
  V = set(V)
  if ( (not P) or (P[0] != s) or (P[-1] != t) ):
    return False
  if ( (len(P) != len(V)) or (set(P) != V) ):
    return False
  for a, b in zip(P, P[1:]):
    if ( (abs(a[0] - b[0]) + abs(a[1] - b[1])) != 1 ):
      return False
  return True


# Old names (before the 2026-10-18 rename of the Lean definitions), kept as aliases.
#
bridgeSet = bridgeSquares
connS = isConnected
connSet = connectedPairs
critS = isCritical
cutS = isCutCell
dFactor = findFactor
farB = isFar
findMergeS = findMergingCell
findMoveS = findRow
goodPh = isUsablePhantom
goodS = isGoodMergingCell
hRange = classRange
hTry = classSearchOne
hpA = boundaryEndpoints
hpAll = decideHamPath
hpAll_branch = decideHamPath_branch
hpB2 = oneHoleCase
hpB3 = twoHoleCase
hpG = holeCase
hpSheffC2F = twoPhantomTest
innerB = isInner
kCheck = isAdmissible
kFind = classSearch
kPot = classPotential
kSq = boxSquares
kW = boxWidth
kX = jumpEdges
lbAt = lowerBound
moveOfS = rowOf
narrowB = isNarrow
oppB = phantomsOpposed
pairX = mergePair
phaseS = runPhase
planABS = undoPlanSteps
planBS = undoPlan
reduceOutCS = reducePieces
runSC2F = twoPhantomLoop
scanAuxS = scanRowAux
scanS = scanRow
splitB = flipSplits
startPair = rowStartPair
statesConn = bridgeStatesConn
twoHole = oneHoleFinalTest
twoHole2 = twoHoleFinalTest
walkG = holeCaseWalk
walkT = boundaryEndpointsWalk
