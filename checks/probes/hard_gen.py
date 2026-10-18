# SPDX-License-Identifier: CC0-1.0
# Hill-climb toward stuck 2-factors (no Type III cell, >= 2 cycles) whose sequence found by
# the Ch. 8 algorithm (checks/ul_algo.py) is long. Prints instances with length >= MINLEN.
#
# Usage: python3 checks/hard_gen.py SEED ROUNDS W H MINLEN
#
import random, sys
sys.argv, args = sys.argv[:1] + ['0', '0', '4'], sys.argv[1:]
src = open('/home/z/claude/ulhc-lean/checks/ul_algo.py').read().split("ap = argparse")[0]
exec(src)
L57 = {}
exec(open('/home/z/claude/ulhc-lean/checks/l57_check.py').read().split('def strips(')[0], L57)

seed, rounds, W, Hh, minlen = map(int, args)
rng = random.Random(seed)

def stuck(V, cells, F):
  if ncomp(V, F) < 2: return False
  cl = classes(V, F)
  return not any(type3(F, cl, c) for c in cells)

def settle(V, cells, F):
  while True:
    cl = classes(V, F)
    t3 = [c for c in cells if type3(F, cl, c)]
    if not t3: return F
    F = apply(F, [[t3[0]]])

def fitness(V, cells, F):
  F = settle(V, cells, F)
  if not stuck(V, cells, F): return 0, None
  seq = find_seq(V, cells, F)
  if seq is None: return -1, None
  F2 = apply(F, [s['run'] for s in seq])
  ok = is_factor(V, F2) and ncomp(V, F2) == ncomp(V, F) - 1
  return (len(seq) if ok else 100), seq

best_seen = 0
for r in range(rounds):
  V, Fb = L57['random_2factor'](W, Hh, rng.randint(10, 400), rng)
  F = {tuple(sorted(e)) for e in Fb}
  G = ph.induced(V); cells = ph.unit_cells(G)
  fit, seq = fitness(V, cells, F)
  for it in range(300):
    alts = [c for c in cells if is_alt(F, c)]
    if not alts: break
    F2 = apply(F, [[rng.choice(alts)]])
    f2, s2 = fitness(V, cells, F2)
    if f2 >= fit or rng.random() < 0.05:
      F, fit, seq = F2, f2, s2
    if fit >= minlen or fit < 0:
      break
  if fit >= minlen or fit < 0:
    print('found', fit, sorted(V), sorted(settle(V, cells, F)), [(s['kind'], s['run']) for s in seq] if seq else None)
    sys.stdout.flush()
  best_seen = max(best_seen, fit)
print('best', best_seen)
