# SPDX-License-Identifier: CC0-1.0
# Exact touch types for a vertical even strip a = cells (0,j), j = 0..n-1 (direction up).
# Known edges: a's pattern, plus the outer sides forced by degree at a's corners
# (outer sides beside interior cells), unknown elsewhere. A candidate z (start, direction,
# length <= 7, cells disjoint from a, sharing >= 1 side with a) survives if its pattern agrees
# with every known edge. Output: contact types, by z's role at the contact and z's direction.
#
import sys
sys.path.insert(0, '/home/z/claude/ulhc-lean/checks')
from window import side, pattern, cells_of, STEP, OPP
def known_edges(n):
  K = dict(pattern((0, 0), 't', n))
  for j in range(n - 1):
    # outer sides at front corners of c_j (j < n-1): dark iff j even
    K[((-1, j + 1), (0, j + 1))] = (j % 2 == 0)
    K[((1, j + 1), (2, j + 1))] = (j % 2 == 0)
  # proper start: outer back edges light, back-down edges dark
  K[((-1, 0), (0, 0))] = False; K[((1, 0), (2, 0))] = False
  K[((0, -1), (0, 0))] = True; K[((1, -1), (1, 0))] = True
  return K
def role(i, m):
  if m == 1: return 'single'
  if i == 0: return 'start'
  if i == m - 1: return 'end'
  return 'even' if i % 2 == 0 else 'odd'
def arole(j, n):
  if j == 0: return 'start'
  if j == n - 1: return 'end'
  return 'even' if j % 2 == 0 else 'odd'
types = {}
for n in (4, 6, 8):
  K = known_edges(n)
  A = cells_of((0, 0), 't', n)
  aside = {}
  for j, c in enumerate(A):
    for d in 'btlr': aside.setdefault(side(c, d), []).append(j)
  for sx in range(-3, 4):
    for sy in range(-8, n + 8):
      for zs in 'btlr':
        for m in range(1, 8):
          Z = cells_of((sx, sy), zs, m)
          if set(Z) & set(A): continue
          P = pattern((sx, sy), zs, m)
          shared = [(i, e) for i, c in enumerate(Z) for e in [side(c, d) for d in 'btlr'] if e in aside]
          if not shared: continue
          if any(e in K and K[e] != v for e, v in P.items()): continue
          M = dict(K); M.update(P)
          dk = {}; lt = {}
          for e, v in M.items():
            for p in e:
              T = dk if v else lt
              T[p] = T.get(p, 0) + 1
          if any(d > 2 for d in dk.values()) or any(l > 2 for l in lt.values()): continue
          for i, e in shared:
            j = aside[e][0]
            rel = 'up' if zs == 't' else ('down' if zs == 'b' else 'horiz')
            key = (arole(j, n), role(i, m), rel)
            types.setdefault(key, set()).add((n, sx, sy, zs, m))
for k in sorted(types): print(k, len(types[k]), sorted(types[k])[:2])
print(len(types), 'types')
