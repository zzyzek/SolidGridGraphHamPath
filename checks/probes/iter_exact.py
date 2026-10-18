# SPDX-License-Identifier: CC0-1.0
# Iterative algorithm with the Lean definitions verbatim: sources are `ValidStrip`s of G,
# links are `CR2 V G b c`, the last strip is odd. Each round: a minimum-weight path,
# apply its first strip, stop at a Type III cell or a count drop. With NOCHAIN=1, a link at
# position >= 3 must not share a side with the previous end cell ("chain strips only second").
# Checks success and that the minimum weight drops by at least the first strip's length.
#
# usage: iter_exact.py seed trials NOCHAIN
#
import sys, random, json, heapq
myargs = sys.argv[1:]
args = myargs
sys.argv = [sys.argv[0], args[0], args[1], '0', 'cr2l1']
exec(open('/home/z/claude/ulhc-lean/checks/iter_l1.py').read().split("\nst = {}\ndef bump")[0])
from window import side as wside, STEP as WSTEP, LATA as WLA, LATB as WLB, OPP as WOPP
NOCHAIN = myargs[2] in ('1', '2')
ALLNC = myargs[2] == '2'
args = myargs
def cellj(c, s, j): return (c[0] + WSTEP[s][0] * j, c[1] + WSTEP[s][1] * j)
def csides(c): return [wside(c, d) for d in 'btlr']
def strips_of(F, cells):
  # every StripSpec (c, s, n) with StripPat F c s n and all cells in V; at most one n per (c, s)
  out = []
  for c in cells:
    for s in 'btlr':
      if wside(c, WOPP[s]) not in F: continue
      j = 0
      while True:
        cj = cellj(c, s, j)
        if cj not in cells: break
        lt = (j % 2 == 1)
        if (wside(cj, WLA[s]) in F) != lt or (wside(cj, WLB[s]) in F) != lt: break
        fr = wside(cj, s) in F
        if fr == (j % 2 == 0):
          out.append((c, s, j + 1)); break
        j += 1
  return out
def lat1(x): c, s, n = x; e = wside(c, WLA[s]); return e
def endc(x): c, s, n = x; return cellj(c, s, n - 1)
def mids(b):
  c, s, n = b; M = set()
  for j in range(1, n - 2, 2):
    M |= set(wside(cellj(c, s, j), s))
  return M
def links(V, cells, G, clG, b, cache):
  c0, s0, n0 = b
  if n0 < 2 or n0 % 2: return []
  u = endc(b)
  if u not in cache:
    Gu = apply(G, [[u]]); cache[u] = (strips_of(Gu, cells), classes(V, Gu))
  cand, clu = cache[u]
  body = {e for i in range(n0 - 1) for e in csides(cellj(c0, s0, i))}
  us = set(csides(u)); M = mids(b)
  out = []
  for x in cand:
    cs = [cellj(x[0], x[1], j) for j in range(x[2])]
    if any(e in body for q in cs for e in csides(q)): continue
    if u in cs: continue
    if x[2] % 2 == 0 and any(e in us for e in csides(cs[-1])): continue
    l = lat1(x)
    if l[0] in M or l[1] in M: continue
    if clG[l[0]] != clG[l[1]]: continue
    if clu[l[0]] == clu[l[1]]: continue
    chain = any(e in us for q in cs for e in csides(q))
    out.append((x, chain))
  return out
def min_path_exact(V, cells, G):
  clG = classes(V, G); cache = {}
  dist = {}; prev = {}; pq = []
  for x in strips_of(G, cells):
    l = lat1(x)
    if clG[l[0]] == clG[l[1]]: continue
    k = (x, 1); dist[k] = x[2]; prev[k] = None; heapq.heappush(pq, (x[2], k))
  memo = {}
  while pq:
    dd, k = heapq.heappop(pq)
    if dd > dist[k]: continue
    x, pos = k
    if x[2] % 2 == 1:
      seq = [k]
      while prev[seq[-1]] is not None: seq.append(prev[seq[-1]])
      return dd, [y for y, _ in seq[::-1]]
    if x not in memo: memo[x] = links(V, cells, G, clG, x, cache)
    for z, chain in memo[x]:
      if NOCHAIN and pos >= (1 if ALLNC else 2) and chain: continue
      nk = (z, min(pos + 1, 3)); nd = dd + z[2]
      if nd < dist.get(nk, 1 << 30):
        dist[nk] = nd; prev[nk] = k; heapq.heappush(pq, (nd, nk))
  return None, None
st = {}
def bump(k): st[k] = st.get(k, 0) + 1
def run_iter(V, F, tag):
  G0 = ph.induced(V); cells = set(ph.unit_cells(G0))
  n0 = ncomp(V, F); G = F; dprev = None; aprev = None
  for rnd in range(60):
    cl = classes(V, G)
    if any(type3(G, cl, c) for c in cells): bump(tag + '_ok_t3'); return
    d, p = min_path_exact(V, cells, G)
    if p is None:
      if ham_cycle(V) is None: bump(tag + '_none_nonham'); return
      bump(tag + '_STUCK_r%d' % min(rnd, 3)); print('STUCK', tag, rnd, json.dumps([sorted(V), sorted(F)]), flush=True); return
    if dprev is not None and d > dprev - aprev:
      bump(tag + '_NO_DECREASE'); print('NODEC', tag, rnd, d, dprev, aprev, json.dumps([sorted(V), sorted(F)]), flush=True)
    a = p[0]
    G = apply(G, [[cellj(a[0], a[1], j) for j in range(a[2])]])
    if ncomp(V, G) < n0: bump(tag + '_ok_r%d' % min(rnd, 3)); return
    dprev = d; aprev = a[2]
  bump(tag + '_TOO_LONG')
for fn in ['/home/z/claude/runs/2026-10-09/long_climb.txt', '/home/z/claude/runs/2026-10-09/long_climb_run1.txt']:
  for line in open(fn):
    if line.startswith('LONG'):
      q = split_top(line); run_iter(set(map(tuple, q[4])), {tuple(map(tuple, e)) for e in q[5]}, 'long')
print('long done', st, flush=True)
rng = random.Random(int(args[0]))
for t in range(int(args[1])):
  if t % 500 == 0: print('progress', t, st, flush=True)
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
