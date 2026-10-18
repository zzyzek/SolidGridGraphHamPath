# SPDX-License-Identifier: CC0-1.0
# Exact local enumeration around a touch between an even strip a (vertical, upward) and a
# strip z: window of cells within radius R of the contact; edges of the window; constraints:
# degree exactly 2 at every vertex all of whose 4 edges lie in the window, a's pattern on a's
# cells, z's pattern on z's cells. Report, per touch type, whether solutions exist and the
# local connectivity (through dark edges in the window) between z's separating corners and
# a's start/end corners.
#
import itertools, sys
def side(c, d):
  x, y = c
  return {'b': ((x, y), (x + 1, y)), 't': ((x, y + 1), (x + 1, y + 1)),
          'l': ((x, y), (x, y + 1)), 'r': ((x + 1, y), (x + 1, y + 1))}[d]
OPP = {'b': 't', 't': 'b', 'l': 'r', 'r': 'l'}
LATA = {'t': 'l', 'b': 'l', 'r': 'b', 'l': 'b'}; LATB = {'t': 'r', 'b': 'r', 'r': 't', 'l': 't'}
STEP = {'b': (0, -1), 't': (0, 1), 'l': (-1, 0), 'r': (1, 0)}
def cells_of(c, s, n): return [(c[0] + STEP[s][0] * j, c[1] + STEP[s][1] * j) for j in range(n)]
def pattern(c, s, n):
  # required membership of sides: dict edge -> bool
  req = {}
  for j, cj in enumerate(cells_of(c, s, n)):
    lat = j % 2 == 1
    req[side(cj, LATA[s])] = lat; req[side(cj, LATB[s])] = lat
    front = (j % 2 == 1) == (j + 1 < n)
    req[side(cj, s)] = front
  req[side(c, OPP[s])] = True
  return req
def solve(a, z, R=2):
  (ac, asd, an), (zc, zsd, zn) = a, z
  A = cells_of(ac, asd, an); Z = cells_of(zc, zsd, zn)
  if set(A) & set(Z): return None
  req = {}
  for e, v in list(pattern(ac, asd, an).items()) + list(pattern(zc, zsd, zn).items()):
    if e in req and req[e] != v: return None
    req[e] = v
  # window: cells within R of any cell of Z near A
  cont = [w for w in Z if any(abs(w[0] - v[0]) + abs(w[1] - v[1]) == 1 for v in A)]
  if not cont: return None
  W = {(w[0] + dx, w[1] + dy) for w in cont for dx in range(-R, R + 1) for dy in range(-R, R + 1)}
  E = sorted({side(c, d) for c in W for d in 'btlr'})
  free = [e for e in E if e not in req]
  verts = {p for e in E for p in e}
  inc = {v: [e for e in E if v in e] for v in verts}
  interior = [v for v in verts if len(inc[v]) == 4]
  # backtracking over free edges
  sols = []
  assign = dict(req)
  order = free
  def ok_partial():
    for v in interior:
      vals = [assign.get(e) for e in inc[v]]
      d = sum(1 for x in vals if x)
      u = sum(1 for x in vals if x is None)
      if d > 2 or d + u < 2: return False
    return True
  def go(i):
    if len(sols) > 200000: return
    if i == len(order):
      sols.append(dict(assign)); return
    for val in (False, True):
      assign[order[i]] = val
      if ok_partial(): go(i + 1)
      del assign[order[i]]
  if not ok_partial(): return []
  go(0)
  return sols
if __name__ == '__main__':
  # Example: a from (0,0) up, length 4; z starting at the left neighbour of a's start going down.
  a = ((0, 0), 't', 4)
  for zc, zs, zn in [((-1, 0), 'b', 2), ((-1, 0), 'b', 3), ((-1, 0), 'b', 4), ((0, -1), 'b', 2), ((0, 4), 't', 2), ((0, 4), 'l', 1), ((-1, 3), 't', 1)]:
    sols = solve(a, ((zc), zs, zn))
    print((zc, zs, zn), 'solutions' if sols else 'none', len(sols) if sols else 0)
