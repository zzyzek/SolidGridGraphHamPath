# SPDX-License-Identifier: CC0-1.0
# Variant search ("pairwise exact"): nodes are strip shapes; a -> b when b is a proper strip
# (pattern and separated start) in F xor a. Shortest path from a proper strip of F to an odd
# strip; then simulate and check that each strip is proper when flipped.
#
import random, sys, heapq
args = sys.argv[1:]
sys.argv = sys.argv[:1] + ['0', '0', '4']
exec(open('/home/z/claude/ulhc-lean/checks/ul_algo.py').read().split("ap = argparse")[0])
sys.path.insert(0, '/home/z/claude/ulhc-lean/checks')
from ham_ilp import ham_cycle

def proper(V, cells, F, cl=None):
  # Proper strips of F: Type I starts with a separated front corner, and Type III cells.
  #
  cl = cl or classes(V, F)
  out = []
  for c in cells:
    D = dark(F, c)
    if len(D) == 1:
      d = next(iter(D)); s = OPP[d]
      run = strip_from(cells, F, c, s)
      if run:
        b = side(c, OPP[s]); f = side(c, s)
        if cl[b[0]] != cl[f[0]] or cl[b[0]] != cl[f[1]]:
          out.append(tuple(run))
    if type3(F, cl, c):
      out.append((c,))
  return out

def px_search(V, cells, F, local=None):
  src = proper(V, cells, F)
  dist = {}; prev = {}; pq = []
  for r in src:
    if len(r) < dist.get(r, 1 << 30):
      dist[r] = len(r); prev[r] = None; heapq.heappush(pq, (len(r), r))
  memo = {}
  while pq:
    d, r = heapq.heappop(pq)
    if d > dist[r]: continue
    if len(r) % 2 == 1:
      seq = [r]
      while prev[seq[-1]] is not None: seq.append(prev[seq[-1]])
      return seq[::-1]
    if r not in memo:
      F2 = apply(F, [list(r)])
      memo[r] = proper(V, cells, F2)
    for r2 in memo[r]:
      if local is not None:
        u = r[-1]; y = r2[0]
        if max(abs(u[0] - y[0]), abs(u[1] - y[1])) > local: continue
      nd = d + len(r2)
      if nd < dist.get(r2, 1 << 30):
        dist[r2] = nd; prev[r2] = r; heapq.heappush(pq, (nd, r2))
  return None

def simulate(V, cells, F, seq):
  # Each strip proper when flipped; return the final factor or None.
  #
  for r in seq:
    if tuple(r) not in proper(V, cells, F): return None
    F = apply(F, [list(r)])
  return F
