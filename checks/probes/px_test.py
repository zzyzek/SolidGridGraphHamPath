# SPDX-License-Identifier: CC0-1.0
# Compare px_search with Hamiltonicity on long_gen hits and on random block instances.
#
import sys, ast, random
args = sys.argv[1:]
exec(open('/home/z/claude/ulhc-lean/checks/px_algo.py').read())
src = open('/home/z/claude/ulhc-lean/checks/depth2_climb.py').read()
exec("def settle" + src.split("def settle")[1].split("best = None")[0])
st = dict(cases=0, px_ok=0, px_sim_fail=0, px_none_ham=0, px_none_nonham=0, lens={})
def check(V, F):
  G = ph.induced(V); cells = ph.unit_cells(G)
  st['cases'] += 1
  seq = px_search(V, cells, F)
  if seq is None:
    if ham_cycle(V) is not None:
      st['px_none_ham'] += 1; print('PX_NONE_HAM', sorted(V), sorted(F), flush=True)
    else: st['px_none_nonham'] += 1
    return
  F2 = simulate(V, cells, F, seq)
  if F2 is None or not (is_factor(V, F2) and ncomp(V, F2) < ncomp(V, F)):
    st['px_sim_fail'] += 1; print('PX_SIM_FAIL', sorted(V), sorted(F), seq, flush=True); return
  st['px_ok'] += 1; st['lens'][len(seq)] = st['lens'].get(len(seq), 0) + 1
for line in open('/home/z/claude/runs/2026-10-09/long_gen.txt'):
  if not line.startswith('LONG'): continue
  rest = line.split(' ', 2)[2]
  Vl, Fl, sq = ast.literal_eval('(' + rest.strip().replace(')] [(', ')], [(', 2).replace(')]] [(', ')]], [(', 1) + ')')
  check(set(map(tuple, Vl)), {tuple(map(tuple, e)) for e in Fl})
print('long', st, flush=True)
L57 = {}
exec(open('/home/z/claude/ulhc-lean/checks/l57_check.py').read().split('def strips(')[0], L57)
rng = random.Random(int(args[0]))
for t in range(int(args[1])):
  V, Fb = L57['random_2factor'](12, 12, rng.randint(10, 400), rng)
  F = {tuple(sorted(e)) for e in Fb}
  G = ph.induced(V); cells = ph.unit_cells(G)
  F = settle(V, cells, F)
  if ncomp(V, F) < 2: continue
  check(V, F)
print('all', st)
