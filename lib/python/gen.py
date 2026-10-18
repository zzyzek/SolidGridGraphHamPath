#!/usr/bin/env python3
# SPDX-License-Identifier: CC0-1.0
#
# Random solid grid graphs with chosen endpoints.
#
# Shapes (all made solid by filling holes afterwards, so |V| may exceed n slightly):
#   blob  : random polyomino growth (uniform frontier choice),
#   thin  : growth preferring frontier points with few neighbours in V (snaky, many cut points),
#   fat   : growth preferring frontier points with many neighbours in V (compact, many inner),
#   rect  : a w x h rectangle (area about n) with random boundary points removed,
#   stamp : a union of K template shapes (rectangles, L, T, plus, U, staircase bands, discs) in
#           random orientations, each placed to overlap the previous ones in at least a 2x2 block.
#           Then only points lying in some 2x2 cell are kept (no spurs, no one-wide corridors that
#           force the path), holes are filled, and the colour counts are repaired by removing
#           convex corner points of the majority colour (never arbitrary boundary points).
#           Arms are at least 2 wide.
#   stamp3: as stamp with arms at least 3 wide (no instance with a unique Hamiltonian path was
#           seen at about 44 points, against 9% for hpath).
#   hpath : a planted Hamiltonian path. A random Hamiltonian path of a rectangle (serpentine
#           mixed by backbite moves), trimmed at both ends while V stays solid, then mixed again
#           by backbite moves inside V until its ends fit the endpoint mode. The instance is a
#           "yes" (the ends of the planted path are the endpoints).
#
# Endpoint modes:
#   any       : any two points,
#   inner2    : both endpoints inner (all 8 king neighbours in V),
#   inner1    : exactly one endpoint inner,
#   boundary  : neither endpoint inner,
#   close     : king distance <= 2,
#   adjacent  : lattice neighbours,
#   plausible : any two points that pass the necessary conditions of hpst_fast.nec (colour
#               balance, degrees, 2-connectivity of V plus the edge s-t); the hard "no"
#               candidates, since everything else is rejected before the algorithm runs.
# With `parity=True` (default) the endpoints are chosen so that the colour count allows a
# Hamiltonian path (otherwise almost every instance is a trivial "no").
#
import random
import sys


def nbrs4(p):
  x, y = p
  return ((x + 1, y), (x - 1, y), (x, y + 1), (x, y - 1))


def king(p):
  x, y = p
  return [(x + a, y + b) for a in (-1, 0, 1) for b in (-1, 0, 1) if (a, b) != (0, 0)]


# Add every missing box point that cannot escape by king moves (the holes).
#
def fill_holes(V):
  V = set(V)
  xs = [p[0] for p in V]
  ys = [p[1] for p in V]
  x0, x1, y0, y1 = min(xs) - 1, max(xs) + 1, min(ys) - 1, max(ys) + 1
  seen = set()
  st = [(x0, y) for y in range(y0, y1 + 1)]
  while st:
    p = st.pop()
    if ( (p in seen) or (p in V) or (not ( (x0 <= p[0] <= x1) and (y0 <= p[1] <= y1) )) ):
      continue
    seen.add(p)
    st.extend(king(p))
  for x in range(x0, x1 + 1):
    for y in range(y0, y1 + 1):
      if ( ((x, y) not in V) and ((x, y) not in seen) ):
        V.add((x, y))
  return V


def grow(n, rng, bias):
  V = {(0, 0)}
  front = set(nbrs4((0, 0)))
  while len(V) < n:
    fl = sorted(front)
    if bias == 'blob':
      p = rng.choice(fl)
    else:
      w = []
      for q in fl:
        k = sum(1 for r in nbrs4(q) if r in V)
        w.append( (4.0 ** (1 - k)) if (bias == 'thin') else (4.0 ** (k - 1)) )
      p = rng.choices(fl, weights=w)[0]
    V.add(p)
    front.discard(p)
    for q in nbrs4(p):
      if q not in V:
        front.add(q)
  return fill_holes(V)


def connected(V):
  if not V:
    return True
  s = next(iter(V))
  seen = {s}
  st = [s]
  while st:
    u = st.pop()
    for v in nbrs4(u):
      if ( (v in V) and (v not in seen) ):
        seen.add(v)
        st.append(v)
  return ( len(seen) == len(V) )


def rect(n, rng):
  w = rng.randint(2, max(2, int(n ** 0.5) + 2))
  h = max(2, n // w)
  V = {(x, y) for x in range(w) for y in range(h)}
  k = rng.randint(0, max(0, (w + h) // 2))
  for _ in range(k):
    bd = sorted(p for p in V if any(q not in V for q in king(p)))
    p = rng.choice(bd)
    V2 = V - {p}
    if ( (len(V2) >= 2) and connected(V2) ):
      V = V2
  return fill_holes(V)


# One backbite move on the path P (list) inside V: an end steps to a random lattice neighbour
# and the path is re-routed (the segment before that neighbour is reversed).
#
def backbite(P, V, rng, pos):
  n = len(P)
  if rng.random() < 0.5:
    c = [q for q in nbrs4(P[0]) if q in V]
    i = pos[rng.choice(c)]
    if i == 1:
      return
    P[0:i] = P[0:i][::-1]
    for k in range(i):
      pos[P[k]] = k
  else:
    c = [q for q in nbrs4(P[-1]) if q in V]
    i = pos[rng.choice(c)]
    if i == (n - 2):
      return
    P[i + 1:] = P[i + 1:][::-1]
    for k in range(i + 1, n):
      pos[P[k]] = k


def reindex(P):
  return {p: k for k, p in enumerate(P)}


def endpoint_mode_ok(V, s, t, mode):
  a, b = is_inner(V, s), is_inner(V, t)
  if   mode == 'inner2':   return ( a and b )
  elif mode == 'inner1':   return ( a != b )
  elif mode == 'boundary': return ( (not a) and (not b) )
  elif mode == 'close':    return ( (abs(s[0] - t[0]) <= 2) and (abs(s[1] - t[1]) <= 2) )
  elif mode == 'adjacent': return ( (abs(s[0] - t[0]) + abs(s[1] - t[1])) == 1 )
  return True


def hpath(n, mode, rng):
  w = rng.randint(2, max(2, int(n ** 0.5) + 3))
  h = max(2, (n + w - 1) // w)
  V = {(x, y) for x in range(w) for y in range(h)}
  P = []
  for y in range(h):
    xs = ( range(w) if ((y % 2) == 0) else range(w - 1, -1, -1) )
    P.extend((x, y) for x in xs)
  pos = reindex(P)
  for _ in range(20 * len(P)):
    backbite(P, V, rng, pos)
  k = rng.randint(0, len(P) // 3)
  for _ in range(k):
    if len(P) <= 4:
      break
    end = ( 0 if (rng.random() < 0.5) else (len(P) - 1) )
    p = P[end]
    if is_inner(V, p):
      continue
    V.discard(p)
    P.pop(end)
  pos = reindex(P)
  for _ in range(20 * len(P)):
    backbite(P, V, rng, pos)
  for _ in range(200 * len(P)):
    if endpoint_mode_ok(V, P[0], P[-1], mode):
      return (V, P)
    backbite(P, V, rng, pos)
  return None


# ---------------------------------------------------------------------------------------------
# Stamped shapes.
# ---------------------------------------------------------------------------------------------

def _box(w, h, x0=0, y0=0):
  return {(x, y) for x in range(x0, x0 + w) for y in range(y0, y0 + h)}


# Template shapes, each at least two points wide everywhere.
#
# `m` bounds the longest side, so templates scale with the requested size.
#
def template(rng, m=10, wmin=2):
  m = max(2 * wmin + 1, m)
  k = rng.choice(['rect', 'rect', 'L', 'T', 'plus', 'U', 'stair', 'disc'])
  a = rng.randint(wmin, max(wmin, min(4, (m - 1) // 2)))
  if k == 'rect':
    return _box(rng.randint(max(3, wmin), m), rng.randint(max(3, wmin), m))
  if k == 'L':
    w, h = rng.randint(a + 2, m), rng.randint(a + 2, m)
    return _box(w, a) | _box(a, h)
  if k == 'T':
    w, h = rng.randint(a + 2, m), rng.randint(a + 2, m)
    c = (w - a) // 2
    return _box(w, a, 0, h - a) | _box(a, h, c, 0)
  if k == 'plus':
    mm = rng.randint(a + 2, m)
    c = (mm - a) // 2
    return _box(mm, a, 0, c) | _box(a, mm, c, 0)
  if k == 'U':
    w, h = rng.randint(2 * a + 1, max(2 * a + 1, m)), rng.randint(a + 2, m)
    return _box(w, a) | _box(a, h) | _box(a, h, w - a, 0)
  if k == 'stair':
    n = rng.randint(2, max(2, m // a))
    S = set()
    for i in range(n):
      S |= _box(a + 1, a + 1, i * (a - 1), i * (a - 1))
    return S
  r = rng.randint(2, max(2, min(4, m // 2)))
  return {(x, y) for x in range(-r, r + 1) for y in range(-r, r + 1) if ((x * x) + (y * y)) <= (r * r + r)}


def orient(S, rng):
  k, refl = rng.randrange(4), (rng.random() < 0.5)
  out = set()
  for (x, y) in S:
    if refl:
      x = -x
    for _ in range(k):
      x, y = -y, x
    out.add((x, y))
  mx = min(p[0] for p in out)
  my = min(p[1] for p in out)
  return {(x - mx, y - my) for (x, y) in out}


# A cell (2x2 block) of S, named by its lower-left point.
#
def cells_in(S):
  return {(x, y) for (x, y) in S
          if ( ((x + 1, y) in S) and ((x, y + 1) in S) and ((x + 1, y + 1) in S) )}


# Translate `piece` so that it shares at least one 2x2 cell with S.
#
def place(S, piece, rng):
  if not S:
    return set(piece)
  cs, cp = sorted(cells_in(S)), sorted(cells_in(piece))
  for _ in range(60):
    a, b = rng.choice(cs), rng.choice(cp)
    dx, dy = (a[0] - b[0]), (a[1] - b[1])
    moved = {(x + dx, y + dy) for (x, y) in piece}
    if len(moved & S) < len(moved):
      return S | moved
  return S


# Keep only the points that lie in some 2x2 cell.
#
def open2(S):
  keep = set()
  for (x, y) in cells_in(S):
    keep |= {(x, y), (x + 1, y), (x, y + 1), (x + 1, y + 1)}
  return keep


# A convex corner: exactly two lattice neighbours, at a right angle, and the diagonal point
# between them in S. Removing it keeps every other point in a 2x2 cell when the shape is at least
# three wide there; the caller rechecks.
#
def convex_corner(S, p):
  x, y = p
  n = [q for q in nbrs4(p) if q in S]
  if len(n) != 2:
    return False
  (ax, ay), (bx, by) = n
  if ( (ax == bx) or (ay == by) ):
    return False
  d = ((ax + bx - x), (ay + by - y))
  return d in S


# Make the colour counts differ by at most one, removing convex corners of the majority colour.
#
def balance(S, rng, limit=40):
  S = set(S)
  for _ in range(limit):
    blk = sum(1 for p in S if colour(p) == 0)
    wht = len(S) - blk
    if abs(blk - wht) <= 1:
      return S
    maj = ( 0 if (blk > wht) else 1 )
    cand = sorted(p for p in S if ( (colour(p) == maj) and convex_corner(S, p) ))
    rng.shuffle(cand)
    done = False
    for p in cand:
      S2 = S - {p}
      if ( (open2(S2) == S2) and connected(S2) ):
        S = S2
        done = True
        break
    if not done:
      return None
  return None


def stamp(n, rng, tries=200, slack=0.2, wmin=2):
  m = int(round(1.2 * (n ** 0.5))) + 1
  for _ in range(tries):
    S = set()
    while len(S) < n:
      S2 = place(S, orient(template(rng, m, wmin), rng), rng)
      if S2 == S:
        break
      S = S2
    S = fill_holes(open2(S))
    if not connected(S):
      continue
    S = balance(S, rng)
    if S is None:
      continue
    S = fill_holes(S)
    if ( (open2(S) == S) and connected(S) and (len(S) <= (1 + slack) * n) ):
      return S
  return None


def make_shape(n, shape, rng):
  if shape == 'rect':
    return rect(n, rng)
  if shape == 'stamp':
    return stamp(n, rng)
  if shape == 'stamp3':
    return stamp(n, rng, wmin=3)
  return grow(n, rng, shape)


def is_inner(V, p):
  return all(q in V for q in king(p))


def colour(p):
  return ( (p[0] + p[1]) % 2 )


def parity_ok(V, s, t):
  n = len(V)
  blk = sum(1 for p in V if colour(p) == 0)
  wht = n - blk
  if (n % 2) == 0:
    return ( (colour(s) != colour(t)) and (blk == wht) )
  if colour(s) != colour(t):
    return False
  return ( (blk == (wht + 1)) if (colour(s) == 0) else (wht == (blk + 1)) )


def pick_endpoints(V, mode, rng, parity=True, tries=400):
  P = sorted(V)
  inner = [p for p in P if is_inner(V, p)]
  bdry = [p for p in P if not is_inner(V, p)]
  for _ in range(tries):
    if mode == 'inner2':
      if len(inner) < 2:
        return None
      s, t = rng.sample(inner, 2)
    elif mode == 'inner1':
      if ( (not inner) or (not bdry) ):
        return None
      s, t = rng.choice(inner), rng.choice(bdry)
      if rng.random() < 0.5:
        s, t = t, s
    elif mode == 'boundary':
      if len(bdry) < 2:
        return None
      s, t = rng.sample(bdry, 2)
    elif mode == 'close':
      s = rng.choice(P)
      c = [q for q in P if ( (q != s) and (abs(q[0] - s[0]) <= 2) and (abs(q[1] - s[1]) <= 2) )]
      if not c:
        continue
      t = rng.choice(c)
    elif mode == 'adjacent':
      s = rng.choice(P)
      c = [q for q in nbrs4(s) if q in V]
      if not c:
        continue
      t = rng.choice(c)
    else:
      s, t = rng.sample(P, 2)
    if mode == 'plausible':
      import hpst_fast
      cx = hpst_fast.Ctx(V)
      inU = bytearray(cx.N)
      for p in cx.Vids:
        inU[p] = 1
      if hpst_fast.nec(cx, inU, cx.Vids, cx.pid(s), cx.pid(t)):
        return (s, t)
      continue
    if ( (not parity) or parity_ok(V, s, t) ):
      return (s, t)
  return None


# One random instance: (V, s, t), or None when the mode is impossible for the drawn shape.
#
def gen(n, shape='blob', mode='any', seed=None, parity=True):
  rng = random.Random(seed)
  if ( (shape == 'hpath') and (mode != 'plausible') ):
    r = hpath(n, mode, rng)
    if r is None:
      return None
    V, P = r
    return (frozenset(V), P[0], P[-1])
  if shape == 'hpath':
    r = hpath(n, 'any', rng)
    if r is None:
      return None
    V = r[0]
  else:
    V = make_shape(n, shape, rng)
    if V is None:
      return None
  st = pick_endpoints(V, mode, rng, parity)
  if st is None:
    return None
  return (frozenset(V), st[0], st[1])


def to_ascii(V, s, t):
  xs = [p[0] for p in V]
  ys = [p[1] for p in V]
  rows = []
  for y in range(max(ys), min(ys) - 1, -1):
    r = ''
    for x in range(min(xs), max(xs) + 1):
      p = (x, y)
      r += ( 's' if (p == s) else ('t' if (p == t) else ('.' if (p in V) else '#')) )
    rows.append(r)
  return '\n'.join(rows) + '\n'


if __name__ == "__main__":
  import argparse
  ap = argparse.ArgumentParser(description="random solid grid graph with endpoints (ASCII)")
  ap.add_argument('-n', type=int, default=30)
  ap.add_argument('--shape', default='blob', choices=['blob', 'thin', 'fat', 'rect', 'stamp', 'stamp3', 'hpath'])
  ap.add_argument('--mode', default='any',
                  choices=['any', 'inner2', 'inner1', 'boundary', 'close', 'adjacent', 'plausible'])
  ap.add_argument('--seed', type=int, default=None)
  ap.add_argument('--no-parity', action='store_true')
  a = ap.parse_args()
  r = None
  seed = a.seed
  for i in range(100):
    r = gen(a.n, a.shape, a.mode, (None if (seed is None) else (seed + 1000003 * i)),
            not a.no_parity)
    if r is not None:
      break
  if r is None:
    sys.exit("no instance for this mode")
  sys.stdout.write(to_ascii(*r))
