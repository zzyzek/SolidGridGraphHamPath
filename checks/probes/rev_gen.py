# SPDX-License-Identifier: CC0-1.0
# Reverse generator: from a 2-factor M of a block graph (always Hamiltonian), split by
# flipping an alternating cell whose dark sides share a class, then flip random even strips
# (each one's reverse is a strip of the earlier factor). Keep stuck results (no Type III,
# >= 2 cycles) on which px_search finds a sequence of 3 or more strips; check them by
# simulation, and check the thesis-style search too.
#
# Usage: python3 checks/rev_gen.py SEED TRIALS W,H,.. DEPTH
#
import random, sys
args = sys.argv[1:]
exec(open('/home/z/claude/ulhc-lean/checks/px_algo.py').read())
L57 = {}
exec(open('/home/z/claude/ulhc-lean/checks/l57_check.py').read().split('def strips(')[0], L57)

def even_strips_any(V, cells, F):
  out = []
  for c in cells:
    D = dark(F, c)
    if len(D) == 1:
      d = next(iter(D)); s = OPP[d]
      run = strip_from(cells, F, c, s)
      if run and len(run) % 2 == 0: out.append(run)
  return out

seed, trials = int(args[0]), int(args[1])
sizes = [int(x) for x in args[2].split(',')]; depth = int(args[3])
rng = random.Random(seed)
st = dict(gen=0, stuck=0, long=0, px_bad=0, th_bad=0, th_none=0, px_none=0, lens={})
src = open('/home/z/claude/ulhc-lean/checks/depth2_climb.py').read()
exec("def settle" + src.split("def settle")[1].split("best = None")[0])
def stuck(V, cells, F):
  cl = classes(V, F)
  return ncomp(V, F) >= 2 and not any(type3(F, cl, c) for c in cells)
def has_odd(V, cells, F):
  return any(len(r) % 2 for r in proper(V, cells, F))
for t in range(trials):
  W = rng.choice(sizes); Hh = rng.choice(sizes)
  V, Fb = L57['random_2factor'](W, Hh, rng.randint(10, 400), rng)
  F = {tuple(sorted(e)) for e in Fb}
  G = ph.induced(V); cells = ph.unit_cells(G)
  F = settle(V, cells, F)
  if not stuck(V, cells, F): continue
  for _ in range(depth):
    E = even_strips_any(V, cells, F)
    rng.shuffle(E)
    moved = False
    for r in E[:12]:
      F2 = apply(F, [r])
      if is_factor(V, F2) and stuck(V, cells, F2) and not has_odd(V, cells, F2):
        F = F2; moved = True; break
    if not moved: break
  st['gen'] += 1
  if not stuck(V, cells, F): continue
  st['stuck'] += 1
  px = px_search(V, cells, F)
  th = find_seq(V, cells, F)
  if px is None: st['px_none'] += 1; print('PX_NONE', sorted(V), sorted(F), flush=True)
  if th is None: st['th_none'] += 1; print('TH_NONE', sorted(V), sorted(F), flush=True)
  for name, runs in (('px', px), ('th', [s['run'] for s in th] if th else None)):
    if runs is None: continue
    F2 = simulate(V, cells, F, [tuple(r) for r in runs])
    if F2 is None or ncomp(V, F2) >= ncomp(V, F):
      st[name + '_bad'] += 1; print(name.upper() + '_BAD', sorted(V), sorted(F), [list(r) for r in runs], flush=True)
  if px:
    st['lens'][len(px)] = st['lens'].get(len(px), 0) + 1
    if len(px) >= 3:
      st['long'] += 1; print('LONG', len(px), sorted(V), sorted(F), [list(r) for r in px], flush=True)
  if t % 500 == 0: print('progress', t, st, flush=True)
print('final', st)
