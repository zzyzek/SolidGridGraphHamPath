# SPDX-License-Identifier: CC0-1.0
# Conjecture test: a TL path whose execution keeps the count and creates no Type III cell
# before a step is proper at that step (patterns hold, start separated).
# Random stuck instances; all TL paths up to length 4 and weight min + slack.
#
import sys, random, json
args = sys.argv[1:]
exec(open('/home/z/claude/ulhc-lean/checks/tl_algo.py').read())
src = open('/home/z/claude/ulhc-lean/checks/depth2_climb.py').read()
exec("def settle" + src.split("def settle")[1].split("best = None")[0])
E3 = {}
exec(open('/home/z/claude/ulhc-lean/checks/l57_check.py').read().split('def run(')[0], E3)
_e = open('/home/z/claude/ulhc-lean/checks/even_t3.py').read()
exec('import random\nimport networkx as nx\ndef grow_shape' + _e.split('def grow_shape')[1].rsplit('def run(', 1)[0], E3)
VARIANT = args[3]
def cr2_succ(V, cells, F, cands, x):
  run, tog = x
  u = run[-1]
  if len(run) % 2 == 1: return []
  Fu = apply(F, [[u]])
  cl0 = classes(V, F); clu = classes(V, Fu)
  s = strip_dir(run)
  succ = []
  def near(p, q): return abs(p[0] - q[0]) <= 1 and abs(p[1] - q[1]) <= 1
  body = run[:-1]
  bodysides = {e for q in body for e in cell_edges(q)}
  usides = set(cell_edges(u))
  # middle corners of b: front corners of odd cells before the last pair
  mids = set()
  for jj in range(1, len(run) - 2, 2):
    e = side(run[jj], s)
    mids |= {e[0], e[1]}
  for z in cands:
    zr, zt = z
    if set(zr) & set(run): continue
    if any(e in bodysides for q in zr for e in cell_edges(q)): continue
    if any(e in usides for e in cell_edges(zr[-1])) and len(zr) > 1: continue
    if len(zr) == 1 and any(e in usides for e in cell_edges(zr[0])) and zt is None: continue
    if len(zr) > 1:
      zs = strip_dir(zr); lat = side(zr[0], LATA[zs])
      if lat[0] in mids or lat[1] in mids: continue
    if zt is not None:
      if zt in (side(u, LATA[s]), side(u, LATB[s])): succ.append(z)
      continue
    if zr[0] in (nb(u, LATA[s]), nb(u, LATB[s])): continue
    if len(zr) == 1:
      sl = [side(zr[0], d) for d in SIDES if side(zr[0], d) not in F]
    else:
      sl = [side(c0, d) for c0, d in sep_sides(zr, zt)]
    if any(clu[e[0]] != clu[e[1]] and cl0[e[0]] == cl0[e[1]] for e in sl): succ.append(z)
  return succ
def tl_succ_all(V, cells, F, cands, x):
  if VARIANT in ('cr2', 'cr2l1'): return cr2_succ(V, cells, F, cands, x)
  run, tog = x
  u = run[-1]; s = strip_dir(run); y = run[0]
  extra = {side(u, LATA[s]), side(u, LATB[s])}
  banned = set()
  if VARIANT != 'noyban': banned |= {side(y, d) for d in SIDES}
  if VARIANT != 'nouban': banned |= {side(u, s), side(u, OPP[s])}
  if VARIANT == 'px':
    Fa = apply(F, [list(run)])
    prs = set(proper(V, cells, Fa))
  Dg = light_graph(cells, F, extra, banned)
  if VARIANT == 'created':
    D0 = light_graph(cells, F, set(), banned)
  succ = []
  for z in cands:
    zr, zt = z
    if set(zr) & set(run): continue
    if zt is not None and zt not in extra: continue
    if zt is None and zr[0] in (nb(u, LATA[s]), nb(u, LATB[s])): continue
    if zt is not None: succ.append(z); continue
    if VARIANT == 'px':
      if zr in prs: succ.append(z)
      continue
    if len(zr) == 1:
      sl = [(zr[0], d) for d in SIDES if side(zr[0], d) not in F]
    else:
      sl = sep_sides(zr, zt)
    if VARIANT == 'created':
      ok = any(in_cycle(Dg, c0, d) and not in_cycle(D0, c0, d) for c0, d in sl)
    else:
      ok = any(in_cycle(Dg, c0, d) for c0, d in sl)
    if ok: succ.append(z)
  return succ


def var_search(V, cells, F):
  import heapq
  cands = candidates(V, cells, F); pr = set(proper(V, cells, F))
  dist = {}; prev = {}; pq = []
  for x in cands:
    if x[1] is None and x[0] in pr:
      dist[x] = len(x[0]); prev[x] = None; heapq.heappush(pq, (len(x[0]), x))
  memo = {}
  while pq:
    dd, x = heapq.heappop(pq)
    if dd > dist[x]: continue
    if len(x[0]) % 2 == 1:
      seq = [x]
      while prev[seq[-1]] is not None: seq.append(prev[seq[-1]])
      return [r for r, _ in seq[::-1]]
    if x not in memo: memo[x] = tl_succ_all(V, cells, F, cands, x)
    for z in memo[x]:
      nd = dd + len(z[0])
      if nd < dist.get(z, 1 << 30):
        dist[z] = nd; prev[z] = x; heapq.heappush(pq, (nd, z))
  return None

st = {}
def bump(k): st[k] = st.get(k, 0) + 1
rng = random.Random(int(args[0]))
slack = int(args[2])
for t in range(int(args[1])):
  if t % 500 == 0: print('progress', t, st, flush=True)
  W = rng.choice([8, 10, 12]); Hh = rng.choice([8, 10, 12])
  V = set(E3['grow_shape'](W, Hh, rng))
  Fs = E3['two_factor'](V, rng)
  if Fs is None: continue
  F = {tuple(sorted(e)) for e in Fs}
  G = ph.induced(V); cells = ph.unit_cells(G)
  for _ in range(rng.randint(0, 40)):
    alts = [c for c in cells if is_alt(F, c)]
    if not alts: break
    F = apply(F, [[rng.choice(alts)]])
  F = settle(V, cells, F)
  n0 = ncomp(V, F)
  if n0 < 2: continue
  best = tl_search(V, cells, F)
  if best is None: continue
  wmin = sum(len(r) for r in best)
  cands = candidates(V, cells, F)
  pr = set(proper(V, cells, F))
  memo = {}; paths = []
  def go(path, w):
    x = path[-1]
    if len(x[0]) % 2 == 1: paths.append(list(path)); return
    if len(path) >= 4: return
    if x not in memo: memo[x] = tl_succ_all(V, cells, F, cands, x)
    for z in memo[x]:
      if w + len(z[0]) <= wmin + slack:
        path.append(z); go(path, w + len(z[0])); path.pop()
  for x in cands:
    if x[1] is None and x[0] in pr: go([x], len(x[0]))
  for p_ in paths:
    runs = [r for r, _ in p_]
    if len(runs) < 2: continue
    Fi = F; clean = True
    for i, r in enumerate(runs):
      prop = r in set(proper(V, cells, Fi))
      if not prop:
        if clean:
          bump('CLEAN_FAIL'); print('CLEAN_FAIL', json.dumps([sorted(V), sorted(F), [list(map(list, q)) for q in runs], i]), flush=True)
        else: bump('fail_after_unclean')
        break
      Fi = apply(Fi, [list(r)])
      if ncomp(V, Fi) != n0: clean = False
      cl = classes(V, Fi)
      if any(type3(Fi, cl, c) for c in cells): clean = False
    else:
      bump('valid')
print('final', st)
