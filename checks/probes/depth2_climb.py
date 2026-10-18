# SPDX-License-Identifier: CC0-1.0
# Adversarial test of "two strips suffice": hill-climb over 2-factors of block graphs
# (always Hamiltonian) toward a stuck factor (no Type III, >= 2 cycles, no proper odd strip)
# in which no proper even strip s leaves a Type III cell or a proper odd strip in F xor s.
# The score is the number of such escaping even strips; 0 is a counterexample.
#
# Usage: python3 checks/depth2_climb.py SEED ROUNDS W H
#
import random, sys
args = sys.argv[1:]
sys.argv = sys.argv[:1] + ['0', '0', '4']
exec(open('/home/z/claude/ulhc-lean/checks/ul_algo.py').read().split("ap = argparse")[0])
L57 = {}
exec(open('/home/z/claude/ulhc-lean/checks/l57_check.py').read().split('def strips(')[0], L57)

seed, rounds, W, Hh = map(int, args)
rng = random.Random(seed)

def settle(V, cells, F):
  while True:
    cl = classes(V, F)
    t3 = [c for c in cells if type3(F, cl, c)]
    if not t3: return F
    F = apply(F, [[t3[0]]])

def proper_strips(V, cells, F):
  cl = classes(V, F)
  out = []
  for c in cells:
    D = dark(F, c)
    if len(D) != 1: continue
    d = next(iter(D)); s = OPP[d]
    run = strip_from(cells, F, c, s)
    if not run: continue
    b = side(c, OPP[s]); f = side(c, s)
    if cl[b[0]] != cl[f[0]] or cl[b[0]] != cl[f[1]]:
      out.append(run)
  return out

def escapes(V, cells, F):
  if ncomp(V, F) < 2: return None
  S = proper_strips(V, cells, F)
  if any(len(r) % 2 for r in S): return None
  n = 0
  for r in S:
    F2 = apply(F, [r])
    cl2 = classes(V, F2)
    if any(type3(F2, cl2, c) for c in cells) or any(len(r2) % 2 for r2 in proper_strips(V, cells, F2)):
      n += 1
  return n

best = None
for r in range(rounds):
  V, Fb = L57['random_2factor'](W, Hh, rng.randint(10, 400), rng)
  F = {tuple(sorted(e)) for e in Fb}
  G = ph.induced(V); cells = ph.unit_cells(G)
  Fs = settle(V, cells, F)
  sc = escapes(V, cells, Fs)
  sc = 1000 if sc is None else sc
  for it in range(400):
    alts = [c for c in cells if is_alt(F, c)]
    if not alts: break
    F2 = apply(F, [[rng.choice(alts)]])
    Fs2 = settle(V, cells, F2)
    s2 = escapes(V, cells, Fs2)
    s2 = 1000 if s2 is None else s2
    if s2 <= sc or rng.random() < 0.03:
      F, Fs, sc = F2, Fs2, s2
    if sc == 0: break
  if best is None or sc < best: best = sc
  if sc == 0:
    print('COUNTEREXAMPLE', sorted(V), sorted(Fs), flush=True)
  if r % 10 == 0: print('round', r, 'score', sc, 'best', best, flush=True)
print('best', best)
