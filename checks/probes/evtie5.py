# SPDX-License-Identifier: CC0-1.0
# In the completeness situation (F = G xor s, Q a minimum no-chain path of F starting with a
# strip q beside s's end cell), compare Q with the lightest path q, z, ... whose second strip z
# is a chain strip of q. Is the chain version ever as light as Q?
#
import sys, random, json, heapq
myargs = sys.argv[1:]
sys.argv = [sys.argv[0], myargs[0], myargs[1], '1']
exec(open('/home/z/claude/ulhc-lean/checks/comp_step.py').read().split("rng = random.Random(int(myargs[0]))")[0])
def completion(V, cells, F, clF, start):
  # lightest no-chain completion from `start` placed at position 2
  cache = {}; dist = {(start, 2): start[2]}; pq = [(start[2], (start, 2))]; memo = {}
  while pq:
    dd, k = heapq.heappop(pq)
    if dd > dist[k]: continue
    x, pos = k
    if x[2] % 2 == 1: return dd
    if x not in memo: memo[x] = links(V, cells, F, clF, x, cache)
    for z, ch in memo[x]:
      if pos >= 2 and ch: continue
      nk = (z, 3); nd = dd + z[2]
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
    q = Q[0]
    if len(Q) < 2: continue
    ra = (Sc[-1], {'t': 'b', 'b': 't', 'l': 'r', 'r': 'l'}[s[1]], s[2])
    if tuple(q) == ra: bump('q_is_rev'); continue
    lks = links(V, cells, G, clG, tuple(s), {})
    if not any(z == tuple(q) for z, ch in lks): bump('q_not_linked_from_s'); continue
    bump('q_chainstart')
    lkq = links(V, cells, F, clF, q, {})
    ev = [z for z, ch in lkq if ch and z[2] % 2 == 0]
    od = [z for z, ch in lkq if ch and z[2] % 2 == 1]
    bump('q_len%d' % min(q[2], 6))
    bump('even_chain_links_%d' % min(len(ev), 2)); bump('odd_chain_links_%d' % min(len(od), 2))
    if ev: print('EVCHAIN', 'q', q, 'eq', cells_of_x(q)[-1], 'ev', ev, flush=True)
    eqc = cells_of_x(q)[-1]
    Fe = apply(F, [[eqc]]); clFe = classes(V, Fe)
    for x in strips_of(Fe, cells):
      if x[2] % 2 or x[0] == eqc: continue
      if not any(e2 in set(csides(eqc)) for e2 in csides(x[0])): continue
      l = lat1(x)
      cre = clF[l[0]] == clF[l[1]] and clFe[l[0]] != clFe[l[1]]
      shared = l in set(csides(eqc))
      bump('evenpat_at_lateral_' + ('created' if cre else ('notconnF' if clF[l[0]] != clF[l[1]] else 'notsplit')) + ('_shared' if shared else '_far'))
    lk = links(V, cells, F, clF, q, {})
    chains = [z for z, ch in lk if ch]
    if not chains: bump('no_chain_links_of_q'); continue
    best = None; bz = None
    for z in chains:
      w = completion(V, cells, F, clF, z)
      if w is not None and (best is None or w < best): best = w; bz = z
    if best is None: bump('chain_links_no_completion'); continue
    tot = q[2] + best
    bump('chain_path_' + ('LIGHTER' if tot < dF else ('EQUAL' if tot == dF else 'heavier')))
    # lightest even chain strip continuation
    beste = None
    for z in chains:
      if z[2] % 2 == 1: continue
      w = completion(V, cells, F, clF, z)
      if w is not None and (beste is None or w < beste): beste = w
    if beste is not None:
      bump('even_chain_' + ('LIGHTER' if q[2] + beste < dF else ('EQUAL' if q[2] + beste == dF else 'heavier')))
      if q[2] + beste == dF:
        ez = [z for z in chains if z[2] % 2 == 0 and completion(V, cells, F, clF, z) == beste]
        print('EVENTIE q', q, 'eq', cells_of_x(q)[-1], 'evenchain', ez[0], 'lat1', lat1(ez[0]), 'Q', Q, flush=True)
    if tot <= dF:
      eq = cells_of_x(q)[-1]
      print('CHAINEQ', 'q', q, 'Q', Q, 'chainz', bz, 'eq', eq, 's_end', Sc[-1], flush=True)
print('final', st)
