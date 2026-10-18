# SPDX-License-Identifier: CC0-1.0
# Markov test: along random clean executions (each next strip proper in the current factor,
# no Type III appears, count constant), compare the proper strips of F_i and of F xor a_i.
#
import sys, random
args = sys.argv[1:]
exec(open('/home/z/claude/ulhc-lean/checks/tl_algo.py').read())
src = open('/home/z/claude/ulhc-lean/checks/depth2_climb.py').read()
exec("def settle" + src.split("def settle")[1].split("best = None")[0])
E3 = {}
exec(open('/home/z/claude/ulhc-lean/checks/l57_check.py').read().split('def run(')[0], E3)
_e = open('/home/z/claude/ulhc-lean/checks/even_t3.py').read()
exec('import random\nimport networkx as nx\ndef grow_shape' + _e.split('def grow_shape')[1].rsplit('def run(', 1)[0], E3)
st = {}
def bump(k): st[k] = st.get(k, 0) + 1
rng = random.Random(int(args[0]))
for t in range(int(args[1])):
  if t % 1000 == 0: print('progress', t, st, flush=True)
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
  Fi = F; seq = []
  for step in range(6):
    pr = [r for r in proper(V, cells, Fi) if len(r) % 2 == 0]
    if not pr: break
    r = rng.choice(pr)
    F2 = apply(Fi, [list(r)])
    cl = classes(V, F2)
    if ncomp(V, F2) != n0 or any(type3(F2, cl, c) for c in cells): break
    seq.append(r); Fi = F2
    if len(seq) >= 2:
      A = set(proper(V, cells, Fi)); B = set(proper(V, cells, apply(F, [list(r)])))
      near = set()
      for q in seq[:-1]:
        for c in q:
          near.add(c)
          for d in SIDES: near.add(nb(c, d))
      dA = {x for x in A - B if not (set(x) & near)}
      dB = {x for x in B - A if not (set(x) & near)}
      bump('cmp')
      if dA: bump('dyn_only_far'); print('DYN_ONLY', sorted(V), sorted(F), seq, sorted(dA), flush=True)
      if dB: bump('static_only_far'); print('STATIC_ONLY', sorted(V), sorted(F), seq, sorted(dB), flush=True)
print('final', st)
