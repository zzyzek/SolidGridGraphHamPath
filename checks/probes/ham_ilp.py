# SPDX-License-Identifier: CC0-1.0
# Exact Hamiltonian-cycle test for small grid graphs: degree-2 ILP with lazily added
# subtour cuts (scipy.optimize.milp). Returns a cycle edge list, or None.
#
import numpy as np
from scipy.optimize import milp, LinearConstraint, Bounds

def ham_cycle(V):
  V = sorted(V); idx = {v: i for i, v in enumerate(V)}
  E = []
  for (x, y) in V:
    for w in ((x + 1, y), (x, y + 1)):
      if w in idx: E.append(((x, y), w))
  m = len(E)
  if m == 0: return None
  rows = []; lo = []; hi = []
  for v in V:
    r = np.zeros(m)
    for k, (a, b) in enumerate(E):
      if a == v or b == v: r[k] = 1
    rows.append(r); lo.append(2); hi.append(2)
  while True:
    res = milp(np.zeros(m), constraints=LinearConstraint(np.array(rows), lo, hi),
               integrality=np.ones(m), bounds=Bounds(0, 1))
    if res.status != 0: return None
    x = np.round(res.x).astype(int)
    chosen = [E[k] for k in range(m) if x[k]]
    par = {v: v for v in V}
    def f(a):
      while par[a] != a:
        par[a] = par[par[a]]; a = par[a]
      return a
    for a, b in chosen: par[f(a)] = f(b)
    comps = {}
    for v in V: comps.setdefault(f(v), set()).add(v)
    if len(comps) == 1: return chosen
    for S in comps.values():
      r = np.zeros(m)
      for k, (a, b) in enumerate(E):
        if (a in S) != (b in S): r[k] = 1
      rows.append(r); lo.append(2); hi.append(np.inf)
