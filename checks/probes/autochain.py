# SPDX-License-Identifier: CC0-1.0
# Chain candidates: strips of flip G u (u an alternating cell with dark lats, the end of some
# even strip) whose start cell shares a side with u. Is the created condition automatic for
# single cells, lat1 = shared side, and length >= 3? Count by type.
#
import sys, random, json
myargs = sys.argv[1:]
sys.argv = [sys.argv[0], myargs[0], myargs[1], '1']
exec(open('/home/z/claude/ulhc-lean/checks/comp_step.py').read().split("\nrng = random.Random(int(myargs[0]))")[0])
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
  for b in strips_of(G, cells):
    if b[2] % 2 or b[2] < 2: continue
    u = cells_of_x(b)[-1]
    Gu = apply(G, [[u]]); clu = classes(V, Gu)
    us = set(csides(u)); body = {e for q in cells_of_x(b)[:-1] for e in csides(q)}
    for z in strips_of(Gu, cells):
      zc = cells_of_x(z)
      if u in zc or any(e in body for q in zc for e in csides(q)): continue
      if not any(e in us for e in csides(zc[0])): continue
      if any(e in us for q in zc[1:] for e in csides(q)): bump('LATER_CELL_TOUCHES_U'); continue
      l = lat1(z); shared = l in us
      xs = [e for e in csides(zc[0]) if e in us]
      ulats = {e for e in us if e in G}
      kind = 'alpha' if all(e in ulats for e in xs) else 'beta'
      typ = 'shared' if shared else ('n1' if z[2] == 1 else ('n2' if z[2] == 2 else 'n3plus'))
      cre = clG[l[0]] == clG[l[1]] and clu[l[0]] != clu[l[1]]
      bump(kind + '_' + typ + ('_created' if cre else '_NOT'))
print('final', st)
