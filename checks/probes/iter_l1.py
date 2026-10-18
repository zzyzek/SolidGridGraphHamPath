# SPDX-License-Identifier: CC0-1.0
# Iterative algorithm with the cr2 rule: each round, a minimum-weight path from the current
# state (sources: proper strips of G; links: cr2 relative to G); apply only its first strip;
# stop when the count drops or a Type III cell appears. Checks success and that the minimum
# weight drops each round.
#
import sys, random, json, heapq
args = sys.argv[1:]
exec(open('/home/z/claude/ulhc-lean/checks/clean_var.py').read().split("\nst = {}")[0])
if VARIANT == 'cr2l1':
  def sep_sides(run, tog):
    c = run[0]
    if len(run) > 1:
      s = strip_dir(run)
      return [(c, LATA[s])]
    return [(c, d) for d in SIDES]
  def proper(V, cells, F, cl=None):
    cl = cl or classes(V, F)
    out = []
    for c in cells:
      D = dark(F, c)
      if len(D) == 1:
        d = next(iter(D)); s = OPP[d]
        run = strip_from(cells, F, c, s)
        if run:
          l = side(c, LATA[s])
          if cl[l[0]] != cl[l[1]]: out.append(tuple(run))
      if type3(F, cl, c): out.append((c,))
    return out
sys.path.insert(0, '/home/z/claude/ulhc-lean/checks')
from ham_ilp import ham_cycle
from parse import split_top
def min_path(V, cells, G, anchor):
  cands = candidates(V, cells, G); pr = set(proper(V, cells, G))
  if anchor is not None:
    clG = classes(V, G); clU = classes(V, apply(G, [[anchor]]))
  dist = {}; prev = {}; pq = []
  for x in cands:
    if x[1] is None and x[0] in pr:
      if anchor is not None:
        r = x[0]
        sl = [side(r[0], d) for d in SIDES if side(r[0], d) not in G] if len(r) == 1 else [side(c0, d) for c0, d in sep_sides(r, None)]
        # created by the previous end: separated in G, not after unflipping the end cell
        if not any(clG[e[0]] != clG[e[1]] and clU[e[0]] == clU[e[1]] for e in sl): continue
      dist[x] = len(x[0]); prev[x] = None; heapq.heappush(pq, (len(x[0]), x))
  memo = {}
  while pq:
    dd, x = heapq.heappop(pq)
    if dd > dist[x]: continue
    if len(x[0]) % 2 == 1:
      seq = [x]
      while prev[seq[-1]] is not None: seq.append(prev[seq[-1]])
      return dd, [r for r, _ in seq[::-1]]
    if x not in memo: memo[x] = tl_succ_all(V, cells, G, cands, x)
    for z in memo[x]:
      nd = dd + len(z[0])
      if nd < dist.get(z, 1 << 30):
        dist[z] = nd; prev[z] = x; heapq.heappush(pq, (nd, z))
  return None, None
st = {}
def bump(k): st[k] = st.get(k, 0) + 1
def run_iter(V, F, tag):
  G0 = ph.induced(V); cells = ph.unit_cells(G0)
  n0 = ncomp(V, F); G = F; anchor = None; dprev = None
  for rnd in range(50):
    cl = classes(V, G)
    if any(type3(G, cl, c) for c in cells): bump(tag + '_ok_t3'); return
    d, p = min_path(V, cells, G, anchor)
    if p is None:
      if anchor is None and ham_cycle(V) is None: bump(tag + '_none_nonham'); return
      bump(tag + '_STUCK_r%d' % min(rnd, 3)); print('STUCK', tag, rnd, json.dumps([sorted(V), sorted(F)]), flush=True); return
    if dprev is not None and d > dprev - 2:
      bump(tag + '_NO_DECREASE'); print('NODEC', tag, json.dumps([sorted(V), sorted(F)]), flush=True)
    a = p[0]
    G = apply(G, [list(a)])
    if ncomp(V, G) < n0: bump(tag + '_ok_r%d' % min(rnd, 3)); return
    anchor = None; dprev = d
  bump(tag + '_TOO_LONG')
for fn in ['/home/z/claude/runs/2026-10-09/long_climb.txt', '/home/z/claude/runs/2026-10-09/long_climb_run1.txt']:
  for line in open(fn):
    if line.startswith('LONG'):
      q = split_top(line); run_iter(set(map(tuple, q[4])), {tuple(map(tuple, e)) for e in q[5]}, 'long')
print('long done', st, flush=True)
rng = random.Random(int(args[0]))
for t in range(int(args[1])):
  if t % 2000 == 0: print('progress', t, st, flush=True)
  W = rng.choice([8, 10, 12]); Hh = rng.choice([8, 10, 12])
  V = set(E3['grow_shape'](W, Hh, rng))
  Fs = E3['two_factor'](V, rng)
  if Fs is None: continue
  F = {tuple(sorted(e)) for e in Fs}
  Gr = ph.induced(V); cells = ph.unit_cells(Gr)
  for _ in range(rng.randint(0, 40)):
    alts = [c for c in cells if is_alt(F, c)]
    if not alts: break
    F = apply(F, [[rng.choice(alts)]])
  F = settle(V, cells, F)
  if ncomp(V, F) < 2: continue
  run_iter(V, F, 'rand')
print('final', st)
