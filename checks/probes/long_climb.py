# SPDX-License-Identifier: CC0-1.0
# Hill-climb on stuck 2-factors to make the px_search shortest sequence long. Moves: flip an
# even strip or an alternating cell, then merge Type III cells. Prints instances of length >= 3
# and checks both searches on them by simulation.
#
# Usage: python3 checks/long_climb.py SEED ROUNDS W,H,.. STEPS
#
import random, sys
args = sys.argv[1:]
exec(open('/home/z/claude/ulhc-lean/checks/px_algo.py').read())
src = open('/home/z/claude/ulhc-lean/checks/depth2_climb.py').read()
exec("def settle" + src.split("def settle")[1].split("best = None")[0])
E3 = {}
exec(open('/home/z/claude/ulhc-lean/checks/l57_check.py').read().split('def run(')[0], E3)
_e = open('/home/z/claude/ulhc-lean/checks/even_t3.py').read()
exec('import random\nimport networkx as nx\ndef grow_shape' + _e.split('def grow_shape')[1].rsplit('def run(', 1)[0], E3)
exec(open('/home/z/claude/ulhc-lean/checks/rev_gen.py').read().split('def even_strips_any')[1].join(['def even_strips_any', '']).split('seed, trials')[0])

seed, rounds = int(args[0]), int(args[1])
sizes = [int(x) for x in args[2].split(',')]; steps = int(args[3])
rng = random.Random(seed)
seen = set()
def score(V, cells, F):
  cl = classes(V, F)
  if ncomp(V, F) < 2 or any(type3(F, cl, c) for c in cells): return 0, None
  px = px_search(V, cells, F)
  return (len(px) if px else 0), px
best = 0
import ast
_l = [l for l in open('/home/z/claude/ulhc-lean/checks/even_t3_counterexample.txt') if l.startswith('no_t3_example')][0]
_V, _F, _ = ast.literal_eval(_l[len('no_t3_example '):])
SEEDV = set(map(tuple, _V)); SEEDF = {ph.ekey(tuple(a), tuple(b)) for a, b in _F}
for r in range(rounds):
  V = set(SEEDV); F = set(SEEDF)
  G = ph.induced(V); cells = ph.unit_cells(G)
  # random walk away from the seed (alternating flips), then settle
  for _ in range(rng.randint(0, 6)):
    alts = [c for c in cells if is_alt(F, c)]
    F = apply(F, [[rng.choice(alts)]])
  F = settle(V, cells, F)
  sc, px = score(V, cells, F)
  for it in range(steps):
    moves = [[c] for c in cells if is_alt(F, c)] + even_strips_any(V, cells, F)
    if not moves: break
    F2 = settle(V, cells, apply(F, [rng.choice(moves)]))
    s2, p2 = score(V, cells, F2)
    if s2 >= sc or rng.random() < 0.05:
      F, sc, px = F2, s2, p2
    if sc >= 3:
      key = (frozenset(V), frozenset(F))
      if key not in seen:
        seen.add(key)
        th = find_seq(V, cells, F)
        ok_px = simulate(V, cells, F, px) is not None
        ok_th = th is not None and simulate(V, cells, F, [tuple(s['run']) for s in th]) is not None
        print('LONG', sc, ok_px, ok_th, sorted(V), sorted(F), [list(x) for x in px], flush=True)
  best = max(best, sc)
  if r % 10 == 0: print('round', r, 'best', best, flush=True)
print('done best', best)
