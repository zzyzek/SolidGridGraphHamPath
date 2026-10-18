# SPDX-License-Identifier: CC0-1.0
# Window feasibility (degree 2 at interior vertices) for an odd strip z ending at a's end
# cell from the side, with a's pattern, forced outer sides and the proper-start facts.
#
import sys, itertools
import numpy as np
from scipy.optimize import milp, LinearConstraint, Bounds
sys.path.insert(0, '/home/z/claude/ulhc-lean/checks')
from window import side, pattern, cells_of
def feasible(n, m, extra={}):
  a = ((0, 0), 't', n)
  z = ((-(m - 1), n - 1), 'r', m)
  req = {}
  for e, v in list(pattern(*a).items()) + list(pattern(*z).items()):
    if e in req and req[e] != v: return 'conflict'
    req[e] = v
  for j in range(n - 1):
    req[((-1, j + 1), (0, j + 1))] = (j % 2 == 0); req[((1, j + 1), (2, j + 1))] = (j % 2 == 0)
  req[((-1, 0), (0, 0))] = False; req[((1, 0), (2, 0))] = False
  req[((0, -1), (0, 0))] = True; req[((1, -1), (1, 0))] = True
  req.update(extra)
  W = {(x, y) for x in range(-m - 1, 3) for y in range(-2, n + 2)}
  E = sorted({side(c, d) for c in W for d in 'btlr'})
  idx = {e: i for i, e in enumerate(E)}
  verts = {p for e in E for p in e}
  inc = {v: [e for e in E if v in e] for v in verts}
  rows = []; lo = []; hi = []
  for v in verts:
    if len(inc[v]) == 4:
      r = np.zeros(len(E)); 
      for e in inc[v]: r[idx[e]] = 1
      rows.append(r); lo.append(2); hi.append(2)
  lb = np.zeros(len(E)); ub = np.ones(len(E))
  for e, v in req.items():
    if e in idx: lb[idx[e]] = ub[idx[e]] = (1 if v else 0)
  res = milp(np.zeros(len(E)), constraints=LinearConstraint(np.array(rows), lo, hi), integrality=np.ones(len(E)), bounds=Bounds(lb, ub))
  return 'feasible' if res.status == 0 else 'infeasible'
for n in (2, 4, 6):
  for m in (3, 5, 7):
    print(n, m, feasible(n, m))
