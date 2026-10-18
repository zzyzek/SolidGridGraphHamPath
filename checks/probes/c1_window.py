# SPDX-License-Identifier: CC0-1.0
# Local feasibility: s vertical up (cells (0,0..n-1)), F = G xor s with G's s-pattern; q =
# [(-1,n-1), (-1,n)] up (pattern in F); z an even strip of flip F M (M = (-1,n)) starting at
# (-2,n) going up (length m). Degrees 2 at all corners of the cells involved, in G and in F
# (F = G xor s on s's sides only). Also the forced facts: G Type III-free is not encoded.
#
import sys, itertools
import numpy as np
from scipy.optimize import milp, LinearConstraint, Bounds
sys.path.insert(0, '/home/z/claude/ulhc-lean/checks')
from window import side, pattern, cells_of
def solve(n, m, extra=None):
  S = cells_of((0, 0), 't', n)
  sides_s = {}
  for c in S:
    for d in 'btlr':
      e = side(c, d); sides_s[e] = sides_s.get(e, 0) + 1
  toggled = {e for e, k in sides_s.items() if k % 2 == 1}
  W = {(x, y) for x in range(-4, 3) for y in range(-2, n + m + 2)}
  E = sorted({side(c, d) for c in W for d in 'btlr'})
  idx = {e: i for i, e in enumerate(E)}
  verts = {p for e in E for p in e}
  inc = {v: [e for e in E if v in e] for v in verts}
  # variables: G edges. F = G xor toggled.
  rows, lo, hi = [], [], []
  def deg_row(v):
    r = np.zeros(len(E)); 
    for e in inc[v]: r[idx[e]] = 1
    return r
  # degree 2 in G at every interior vertex of the window
  interior = [v for v in verts if len(inc[v]) == 4]
  for v in interior:
    rows.append(deg_row(v)); lo.append(2); hi.append(2)
  lb = np.zeros(len(E)); ub = np.ones(len(E))
  def fixG(e, val):
    lb[idx[e]] = ub[idx[e]] = val
  # s's pattern in G
  for e, v in pattern((0, 0), 't', n).items(): fixG(e, 1 if v else 0)
  # q's pattern in F: G value = F value xor toggled
  for e, v in pattern((-1, n - 1), 't', 2).items():
    fixG(e, (1 if v else 0) ^ (1 if e in toggled else 0))
  # z's pattern in flip F M: G value = pattern xor toggled(s) xor side of M
  Mside = {side((-1, n), d) for d in 'btlr'}
  for e, v in pattern((-2, n), 't', m).items():
    val = (1 if v else 0) ^ (1 if e in toggled else 0) ^ (1 if e in Mside else 0)
    if lb[idx[e]] == ub[idx[e]] and lb[idx[e]] != val: return 'conflict'
    fixG(e, val)
  res = milp(np.zeros(len(E)), constraints=LinearConstraint(np.array(rows), lo, hi),
             integrality=np.ones(len(E)), bounds=Bounds(lb, ub))
  return 'feasible' if res.status == 0 else 'infeasible'
for n in (2, 4, 6):
  for m in (2, 4):
    print(n, m, solve(n, m))
