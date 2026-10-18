# SPDX-License-Identifier: CC0-1.0
# Prepend situation: which first strips q' (valid in F, chain-linked from s in G) start a
# minimum path of F? Record their lengths and whether they have even chain links.
#
import sys, random, json, heapq
myargs = sys.argv[1:]
sys.argv = [sys.argv[0], myargs[0], myargs[1], '1']
exec(open('/home/z/claude/ulhc-lean/checks/chain2_probe.py').read().split("\nrng = random.Random(int(myargs[0]))")[0])
def completion1(V, cells, F, clF, start):
  cache = {}; dist = {(start, 1): start[2]}; pq = [(start[2], (start, 1))]; memo = {}
  while pq:
    dd, k = heapq.heappop(pq)
    if dd > dist[k]: continue
    x, pos = k
    if x[2] % 2 == 1: return dd
    if x not in memo: memo[x] = links(V, cells, F, clF, x, cache)
    for z, ch in memo[x]:
      if pos >= 2 and ch: continue
      nk = (z, min(pos + 1, 3)); nd = dd + z[2]
      if nd < dist.get(nk, 1 << 30): dist[nk] = nd; heapq.heappush(pq, (nd, nk))
  return None
rng = random.Random(int(myargs[0]))
for t in range(int(myargs[1])):
  if t % 100 == 0: print('progress', t, st, flush=True)
  V, G = rng.choice(SEEDS); V = set(V); G = set(G)
  cells = set(ph.unit_cells(ph.induced(V)))
  for _ in range(rng.randint(0, 15)):
    alts = [c for c in cells if is_alt(G, c)]
    if not alts: break
    G = apply(G, [[rng.choice(alts)]])
  G = settle(V, cells, G)
  if ncomp(V, G) < 2: continue
  clG = classes(V, G)
  if any(type3(G, clG, c) for c in cells): continue
  ss = [x for x in strips_of(G, cells) if x[2] % 2 == 0 and clG[lat1(x)[0]] != clG[lat1(x)[1]]]
  rng.shuffle(ss)
  for s in ss[:3]:
    Sc = cells_of_x(s)
    F = apply(G, [Sc]); clF = classes(V, F)
    if any(type3(F, clF, c) for c in cells) or ncomp(V, F) < 2: continue
    dF, Q = min_path_exact(V, cells, F)
    if Q is None: continue
    srcF = [x for x in strips_of(F, cells) if clF[lat1(x)[0]] != clF[lat1(x)[1]]]
    lks = set(z for z, ch in links(V, cells, G, clG, tuple(s), {}))
    for qq in srcF:
      if qq not in lks: continue
      w = completion1(V, cells, F, clF, qq)
      if w == dF:
        bump('minfirst_len%d' % min(qq[2], 6))
        ev = [z for z, ch in links(V, cells, F, clF, qq, {}) if ch and z[2] % 2 == 0]
        if ev: bump('MINFIRST_HAS_EVEN_CHAIN'); print('EVC', qq, ev, flush=True)
print('final', st)
