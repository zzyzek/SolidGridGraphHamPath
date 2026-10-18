# SPDX-License-Identifier: CC0-1.0
# Catalogue how two candidate strips of the same 2-factor F can interact: shared cells
# (where, which roles) and adjacency across a side that one of them changes.
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

def changed(run):
  # sides changed by flipping the run (odd multiplicity)
  cnt = {}
  for c in run:
    for e in cell_edges(c): cnt[e] = cnt.get(e, 0) + 1
  return {e for e, k in cnt.items() if k % 2}

def role(run, c):
  i = run.index(c)
  if i == len(run) - 1: return 'end'
  if i == 0: return 'start'
  return 'even' if i % 2 == 0 else 'odd'

st = {}
def bump(k): st[k] = st.get(k, 0) + 1
rng = random.Random(int(args[0]))
for t in range(int(args[1])):
  W = rng.choice([8, 10, 12]); Hh = rng.choice([8, 10, 12])
  V = set(E3['grow_shape'](W, Hh, rng))
  Fs = E3['two_factor'](V, rng)
  if Fs is None: continue
  F = {tuple(sorted(e)) for e in Fs}
  G = ph.induced(V); cells = ph.unit_cells(G)
  F = settle(V, cells, F)
  if ncomp(V, F) < 2: continue
  cands = candidates(V, cells, F)
  for i, (ra, ta) in enumerate(cands):
    for j, (rb, tb) in enumerate(cands):
      if i == j: continue
      A, B = set(ra), set(rb)
      sa = strip_dir(ra); sb = strip_dir(rb)
      for c in A & B:
        rel = 'same' if sa == sb else ('opp' if sa and sb and OPP[sa] == sb else 'perp')
        bump('share:%s/%s/%s/%s/%s' % (role(ra, c), role(rb, c), rel,
             'chainA' if ta else '', 'chainB' if tb else ''))
      if not (A & B):
        ca = changed(ra)
        for c in rb:
          for d in SIDES:
            e = side(c, d)
            if e in ca and e != ta and e != tb:
              # which cell of a owns e, and its role
              owner = [x for x in ra if e in cell_edges(x)][0]
              bump('adj:a_%s/b_%s/%s' % (role(ra, owner), role(rb, c),
                   'perp' if sa and sb and sa not in (sb, OPP[sb]) else 'par'))
for k, v in sorted(st.items(), key=lambda x: -x[1]): print(v, k)
